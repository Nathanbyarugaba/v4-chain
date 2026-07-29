package keeper_test

import (
	"math/big"
	"testing"

	testapp "github.com/dydxprotocol/v4-chain/protocol/testutil/app"
	"github.com/dydxprotocol/v4-chain/protocol/testutil/constants"
	satypes "github.com/dydxprotocol/v4-chain/protocol/x/subaccounts/types"
	vaulttypes "github.com/dydxprotocol/v4-chain/protocol/x/vault/types"
	"github.com/stretchr/testify/require"
)

// TestF3_MegavaultEquityZero_FreezesShareholders is a regression test for finding
// F3 (see formal-verification/FINDINGS.md and tla/MegavaultShares.tla).
//
// If megavault equity reaches 0 (or below) while shares are still outstanding
// (e.g. after catastrophic losses), then for every shareholder:
//   - WithdrawFromMegavault redeems equity*shares/totalShares = 0 and reverts with
//     ErrInsufficientRedeemedQuoteQuantums, and
//   - MintShares (the only user-facing way to add equity) is blocked with
//     ErrNonPositiveEquity.
//
// So outstanding shares cannot be redeemed and equity cannot be topped up through
// the normal deposit path: shareholders are frozen out until equity is restored
// via some out-of-band transfer into the megavault main subaccount.
//
// NOTE: this test also documents a CORRECTION to an earlier draft of F3, which
// claimed MintShares divides by zero and panics. The real code guards equity<=0
// and returns ErrNonPositiveEquity (a clean error, not a panic). This test pins
// the true behavior.
func TestF3_MegavaultEquityZero_FreezesShareholders(t *testing.T) {
	tApp := testapp.NewTestAppBuilder(t).Build()
	ctx := tApp.InitChain()
	k := tApp.App.VaultKeeper

	// Precondition: megavault equity is 0 (empty main vault, no positive sub-vault equity).
	equity, err := k.GetMegavaultEquity(ctx)
	require.NoError(t, err)
	require.Equal(t, 0, equity.Sign(), "test precondition: megavault equity must be 0")

	// But shares are outstanding (as if earlier depositors are still invested).
	owner := constants.AliceAccAddress.String()
	toSubaccount := satypes.SubaccountId{Owner: owner, Number: 0}
	require.NoError(t, k.SetTotalShares(ctx, vaulttypes.BigIntToNumShares(big.NewInt(1_000))))
	require.NoError(t, k.SetOwnerShares(ctx, owner, vaulttypes.BigIntToNumShares(big.NewInt(1_000))))

	// (F3a) Withdrawals are frozen: redeemed = equity*shares/total = 0 -> revert.
	_, err = k.WithdrawFromMegavault(ctx, toSubaccount, big.NewInt(500), big.NewInt(0))
	require.ErrorIs(t, err, vaulttypes.ErrInsufficientRedeemedQuoteQuantums,
		"F3: withdrawals must revert when equity is 0 with shares outstanding")

	// (F3b) Deposits that would raise equity are blocked with a CLEAN error
	// (ErrNonPositiveEquity) -- NOT a divide-by-zero panic. So recovery via the
	// normal deposit path is impossible while equity <= 0.
	_, err = k.MintShares(ctx, owner, big.NewInt(1_000))
	require.ErrorIs(t, err, vaulttypes.ErrNonPositiveEquity,
		"F3: deposits are blocked (clean error, not panic) while equity <= 0")
}
