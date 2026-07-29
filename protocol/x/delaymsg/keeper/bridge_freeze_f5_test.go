package keeper_test

import (
	"testing"

	sdkmath "cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/dydxprotocol/v4-chain/protocol/testutil/constants"
	keepertest "github.com/dydxprotocol/v4-chain/protocol/testutil/keeper"
	bridgetypes "github.com/dydxprotocol/v4-chain/protocol/x/bridge/types"
	"github.com/dydxprotocol/v4-chain/protocol/x/delaymsg/keeper"
	delaymsgtypes "github.com/dydxprotocol/v4-chain/protocol/x/delaymsg/types"
	"github.com/stretchr/testify/require"
)

// TestF5_BridgingDisabledDuringDelay_PermanentlyFreezesFunds is a regression test
// for finding F5 (see formal-verification/FINDINGS.md and
// formal-verification/tla/BridgeCompletion.tla).
//
// A bridge deposit is acknowledged (which schedules a delayed MsgCompleteBridge
// via x/delaymsg AND advances AcknowledgedEventInfo past the event, so it is
// never re-acknowledged). If bridging is then DISABLED before the delayed
// completion fires:
//   - x/bridge CompleteBridge returns ErrBridgingDisabled (no coins sent), and
//   - x/delaymsg DispatchMessagesForBlock runs the handler in a cached context
//     (rolled back on error, error only logged) and then UNCONDITIONALLY deletes
//     the message.
//
// Net effect: the delayed MsgCompleteBridge is consumed without paying the user
// and is never retried => the user's already-locked (burned on L1) funds are
// permanently frozen. This test demonstrates that end-to-end using the real
// bridge msg server routed through the real delaymsg dispatch, and contrasts it
// with the enabled ("control") path where the funds are delivered.
func TestF5_BridgingDisabledDuringDelay_PermanentlyFreezesFunds(t *testing.T) {
	event := constantsBridgeEvent()
	denom := event.Coin.Denom
	const funded int64 = 1_000

	// run schedules a delayed MsgCompleteBridge (as AcknowledgeBridges does),
	// optionally disables bridging during the delay window, then dispatches the
	// delayed messages for the block. It returns the recipient balance, the
	// bridge module account balance, and whether the delayed message still exists.
	run := func(disableDuringDelay bool) (recipient sdkmath.Int, moduleAcc sdkmath.Int, msgStillExists bool) {
		ctx, delayMsgKeeper, _, bridgeKeeper, bankKeeper, _ := keepertest.DelayMsgKeepers(t)

		// Fund the bridge module account so a successful completion CAN pay out.
		require.NoError(t, bankKeeper.MintCoins(
			ctx,
			bridgetypes.ModuleName,
			sdk.NewCoins(sdk.NewCoin(denom, sdkmath.NewInt(funded))),
		))

		// Bridging is enabled at acknowledgement time.
		require.NoError(t, bridgeKeeper.UpdateSafetyParams(ctx, bridgetypes.SafetyParams{
			IsDisabled:  false,
			DelayBlocks: 0,
		}))

		// Acknowledgement schedules a delayed MsgCompleteBridge (authority is the
		// delaymsg module, which the bridge keeper accepts) to fire this block.
		msg := &bridgetypes.MsgCompleteBridge{
			Authority: delaymsgtypes.ModuleAddress.String(),
			Event:     event,
		}
		id, err := delayMsgKeeper.DelayMessageByBlocks(ctx, msg, 0)
		require.NoError(t, err)

		// Sanity: the message is scheduled for this block.
		ids, found := delayMsgKeeper.GetBlockMessageIds(ctx, uint32(ctx.BlockHeight()))
		require.True(t, found)
		require.Contains(t, ids.Ids, id)

		// Governance disables bridging DURING the delay window (before completion).
		if disableDuringDelay {
			require.NoError(t, bridgeKeeper.UpdateSafetyParams(ctx, bridgetypes.SafetyParams{
				IsDisabled:  true,
				DelayBlocks: 0,
			}))
		}

		// EndBlock: dispatch (and, per the code, delete) delayed messages for this block.
		keeper.DispatchMessagesForBlock(delayMsgKeeper, ctx)

		recipient = bankKeeper.GetBalance(ctx, sdk.MustAccAddressFromBech32(event.Address), denom).Amount
		moduleAcc = bankKeeper.GetBalance(ctx, bridgetypes.ModuleAddress, denom).Amount
		_, msgStillExists = delayMsgKeeper.GetMessage(ctx, id)
		return recipient, moduleAcc, msgStillExists
	}

	// Control: bridging stays enabled -> funds delivered, message consumed.
	rEnabled, modEnabled, existsEnabled := run(false)
	require.Equal(t, event.Coin.Amount, rEnabled,
		"control: recipient should receive the bridged funds when bridging is enabled")
	require.Equal(t, sdkmath.NewInt(funded).Sub(event.Coin.Amount), modEnabled,
		"control: bridge module account should be debited by the bridged amount")
	require.False(t, existsEnabled, "control: delayed message is consumed after successful completion")

	// F5: bridging disabled during the delay window.
	rDisabled, modDisabled, existsDisabled := run(true)
	require.True(t, rDisabled.IsZero(),
		"F5: recipient must NOT receive funds when bridging is disabled at completion time")
	require.Equal(t, sdkmath.NewInt(funded), modDisabled,
		"F5: bridged funds remain stuck in the bridge module account")
	require.False(t, existsDisabled,
		"F5: the delayed MsgCompleteBridge is DELETED despite failing => never retried => funds permanently frozen")
}

// constantsBridgeEvent returns a valid, positive-amount bridge event whose
// recipient is a distinct user account (not the bridge module account).
func constantsBridgeEvent() bridgetypes.BridgeEvent {
	return bridgetypes.BridgeEvent{
		Id:             0,
		Address:        constants.BobAccAddress.String(),
		Coin:           sdk.NewCoin(testDenom, sdkmath.NewInt(888)),
		EthBlockHeight: 3,
	}
}
