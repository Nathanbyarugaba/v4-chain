package keeper_test

import (
	"math/big"
	"testing"

	testapp "github.com/dydxprotocol/v4-chain/protocol/testutil/app"
	"github.com/dydxprotocol/v4-chain/protocol/testutil/constants"
	testutil "github.com/dydxprotocol/v4-chain/protocol/testutil/util"
	perptypes "github.com/dydxprotocol/v4-chain/protocol/x/perpetuals/types"
	satypes "github.com/dydxprotocol/v4-chain/protocol/x/subaccounts/types"
	"github.com/stretchr/testify/require"
)

// TestF1_NegativeTncRearmKeepsWithdrawalsBlocked corroborates the (single-shot
// testable) core mechanism of finding F1 (see formal-verification/FINDINGS.md,
// tla/WithdrawalGating.tla, tla/NegativeTncResolution.tla, and the Lean theorems
// `rearm_always_blocked` / `freeze_is_bounded`).
//
// The withdrawal/transfer breaker blocks a collateral pool for
// WITHDRAWAL_AND_TRANSFERS_BLOCKED_AFTER_NEGATIVE_TNC_SUBACCOUNT_SEEN_BLOCKS (=50)
// blocks after the last block a negative-TNC subaccount was "seen". While such a
// subaccount persists, x/clob EndBlock RE-ARMS the breaker every block
// (SetNegativeTncSubaccountSeenAtBlock(currentBlock)). This test shows:
//
//  1. as long as the breaker is re-armed to the current block, EVERY withdrawal
//     is blocked (WithdrawalsAndTransfersBlocked) -- so if the negative-TNC
//     subaccount can never be resolved (F1b), the freeze is permanent; and
//  2. once re-arming STOPS, the freeze provably lifts after exactly 50 blocks
//     (bounded freeze) -- i.e. the permanence is entirely due to the re-arm.
func TestF1_NegativeTncRearmKeepsWithdrawalsBlocked(t *testing.T) {
	tApp := testapp.NewTestAppBuilder(t).Build()
	ctx := tApp.InitChain()
	sk := tApp.App.SubaccountsKeeper

	// A cross (non-isolated) perpetual -> cross collateral pool.
	var crossPerpId uint32
	found := false
	for _, p := range tApp.App.PerpetualsKeeper.GetAllPerpetuals(ctx) {
		if p.Params.MarketType == perptypes.PerpetualMarketType_PERPETUAL_MARKET_TYPE_CROSS {
			crossPerpId = p.Params.Id
			found = true
			break
		}
	}
	require.True(t, found, "expected at least one cross perpetual in default genesis")

	// A solvent subaccount with USDC and no perpetual positions (cross pool).
	saId := satypes.SubaccountId{Owner: constants.AliceAccAddress.String(), Number: 0}
	sk.SetSubaccount(ctx, satypes.Subaccount{
		Id:             &saId,
		AssetPositions: testutil.CreateUsdcAssetPositions(big.NewInt(1_000)),
	})

	withdraw := []satypes.Update{{
		SubaccountId: saId,
		AssetUpdates: testutil.CreateUsdcAssetUpdates(big.NewInt(-100)),
	}}
	blockedResult := func(ctxAt uint32) satypes.UpdateResult {
		c := ctx.WithBlockHeight(int64(ctxAt))
		_, perUpdate, err := sk.CanUpdateSubaccounts(c, withdraw, satypes.Withdrawal)
		require.NoError(t, err)
		require.Len(t, perUpdate, 1)
		return perUpdate[0]
	}

	const startBlock = uint32(100)

	// (1) Re-arm every block: withdrawals stay blocked across many consecutive
	// blocks (well beyond the 50-block window), demonstrating the permanent-freeze
	// mechanism while a negative-TNC subaccount persists.
	for h := startBlock; h <= startBlock+60; h++ {
		require.NoError(t, sk.SetNegativeTncSubaccountSeenAtBlock(ctx, crossPerpId, h)) // re-arm
		require.Equal(t, satypes.WithdrawalsAndTransfersBlocked, blockedResult(h),
			"F1: while re-armed each block, withdrawals must stay blocked (block %d)", h)
	}

	// After the loop the last "seen" block is startBlock+60.
	lastSeen := startBlock + 60

	// (2) Stop re-arming: within 50 blocks of lastSeen it is still blocked ...
	require.Equal(t, satypes.WithdrawalsAndTransfersBlocked, blockedResult(lastSeen+49),
		"still blocked 49 blocks after the last re-arm")

	// ... and at exactly lastSeen+50 the breaker lifts (bounded freeze), so the
	// withdrawal succeeds. This proves the permanence is due solely to re-arming.
	require.Equal(t, satypes.Success, blockedResult(lastSeen+50),
		"F1: once re-arming stops, the freeze lifts after exactly 50 blocks")
}
