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

// TestF2_BlockHeightRegression_PanicsOnWithdrawal is a regression test for
// finding F2 (see formal-verification/FINDINGS.md and tla/WithdrawalGating.tla,
// lean/WithdrawalGating.lean).
//
// The withdrawal/transfer gating in internalCanUpdateSubaccounts computes the
// uint32 difference `currentBlock - lastBlockNegativeTncSubaccountSeen` and
// PANICS if `currentBlock < lastBlockNegativeTncSubaccountSeen` (guarding against
// uint32 underflow). Under normal operation the "seen" height is set to the
// current block height (monotonic), so the guard never fires. But if the chain
// height ever REGRESSES below a persisted "seen" height (e.g. a restart from an
// older snapshot or a bad upgrade), then EVERY withdrawal/transfer panics — a
// deterministic chain-halt-style freeze of the withdrawal path.
//
// This test reproduces the post-regression state: a negative-TNC "seen" height
// recorded ABOVE the current block height, and shows that a withdrawal then
// panics.
func TestF2_BlockHeightRegression_PanicsOnWithdrawal(t *testing.T) {
	tApp := testapp.NewTestAppBuilder(t).Build()
	ctx := tApp.InitChain()
	sk := tApp.App.SubaccountsKeeper

	// Pick a cross (non-isolated) perpetual so the "seen" record maps to the
	// cross collateral pool (the same pool a position-less subaccount uses).
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

	// A subaccount with USDC and no perpetual positions (=> cross collateral pool).
	saId := satypes.SubaccountId{Owner: constants.AliceAccAddress.String(), Number: 0}
	sk.SetSubaccount(ctx, satypes.Subaccount{
		Id:             &saId,
		AssetPositions: testutil.CreateUsdcAssetPositions(big.NewInt(1_000)),
	})

	// Simulate the POST-REGRESSION state: a negative-TNC subaccount was "seen" at
	// a block far ABOVE the current height (recorded legitimately before the
	// height regressed). The setter is monotonic and has no prior value here.
	const seenAtBlock = uint32(1_000_000)
	require.NoError(t, sk.SetNegativeTncSubaccountSeenAtBlock(ctx, crossPerpId, seenAtBlock))

	// Current height is now BELOW the stored "seen" height.
	ctx = ctx.WithBlockHeight(50)
	require.Less(t, uint32(ctx.BlockHeight()), seenAtBlock)

	// Sanity: with the same (regressed) state a Deposit does NOT hit the gating
	// panic guard (gating only applies to Withdrawal/Transfer).
	require.NotPanics(t, func() {
		_, _, _ = sk.CanUpdateSubaccounts(ctx, []satypes.Update{{
			SubaccountId: saId,
			AssetUpdates: testutil.CreateUsdcAssetUpdates(big.NewInt(100)),
		}}, satypes.Deposit)
	})

	// F2: a Withdrawal now triggers the uint32-underflow panic guard, freezing the
	// entire withdrawal/transfer path for this collateral pool.
	require.Panics(t, func() {
		_, _, _ = sk.CanUpdateSubaccounts(ctx, []satypes.Update{{
			SubaccountId: saId,
			AssetUpdates: testutil.CreateUsdcAssetUpdates(big.NewInt(-100)),
		}}, satypes.Withdrawal)
	})
}
