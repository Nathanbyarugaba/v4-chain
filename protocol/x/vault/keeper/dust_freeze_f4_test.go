package keeper_test

import (
	"math/big"
	"testing"

	testapp "github.com/dydxprotocol/v4-chain/protocol/testutil/app"
	"github.com/dydxprotocol/v4-chain/protocol/testutil/constants"
	testutil "github.com/dydxprotocol/v4-chain/protocol/testutil/util"
	satypes "github.com/dydxprotocol/v4-chain/protocol/x/subaccounts/types"
	vaulttypes "github.com/dydxprotocol/v4-chain/protocol/x/vault/types"
	"github.com/stretchr/testify/require"
)

// TestF4_DustHoldersCannotWithdraw is a regression test for finding F4 (see
// formal-verification/FINDINGS.md and lean/VaultShares.lean `redeem_zero_iff` /
// `dust_freeze`).
//
// Megavault redemption pays `equity * shares / totalShares` (floored) and reverts
// with ErrInsufficientRedeemedQuoteQuantums when that is <= 0. When
// `equity < totalShares` (vault worth < 1 quantum per share), any holder whose
// withdrawable shares `s` satisfy `equity * s < totalShares` gets 0 for `s` and
// for every smaller amount -> those shares can never be converted to a positive
// payout (a permanent dust freeze of that holder's position).
func TestF4_DustHoldersCannotWithdraw(t *testing.T) {
	tApp := testapp.NewTestAppBuilder(t).Build()
	ctx := tApp.InitChain()
	k := tApp.App.VaultKeeper

	// Give the megavault main vault a tiny positive equity (1 quote quantum) by
	// funding its subaccount, so equity > 0 but far below total shares.
	tApp.App.SubaccountsKeeper.SetSubaccount(ctx, satypes.Subaccount{
		Id:             &vaulttypes.MegavaultMainSubaccount,
		AssetPositions: testutil.CreateUsdcAssetPositions(big.NewInt(1)),
	})

	// Precondition: equity is a small positive number.
	equity, err := k.GetMegavaultEquity(ctx)
	require.NoError(t, err)
	require.Equal(t, int64(1), equity.Int64(), "test precondition: megavault equity == 1")

	// A holder owns some shares out of a large total (equity << totalShares).
	owner := constants.AliceAccAddress.String()
	toSubaccount := satypes.SubaccountId{Owner: owner, Number: 0}
	require.NoError(t, k.SetTotalShares(ctx, vaulttypes.BigIntToNumShares(big.NewInt(1_000))))
	require.NoError(t, k.SetOwnerShares(ctx, owner, vaulttypes.BigIntToNumShares(big.NewInt(999))))

	// For every withdrawable amount s in 1..999, redeemed = 1*s/1000 = 0, so the
	// withdrawal reverts. The holder can never extract a positive payout.
	for _, s := range []int64{1, 100, 500, 999} {
		_, err := k.WithdrawFromMegavault(ctx, toSubaccount, big.NewInt(s), big.NewInt(0))
		require.ErrorIs(t, err, vaulttypes.ErrInsufficientRedeemedQuoteQuantums,
			"F4: withdrawing %d shares must revert (equity*shares/total floors to 0)", s)
	}
}
