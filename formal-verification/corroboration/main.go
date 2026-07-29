// Runtime corroboration (Go, stdlib math/big only) of the vault-share
// arithmetic findings proven in ../lean/VaultShares.lean and ../coq/Redemption.v.
//
// It reproduces, in isolation, the exact big.Int operations performed by:
//   protocol/x/vault/keeper/deposit.go  MintShares   (sharesToMint = q*total/equity)
//   protocol/x/vault/keeper/withdraw.go RedeemFromMainAndSubVaults
//                                       (redeemed = equity*shares/total)
//
// These are NOT a substitute for the formal proofs; they are concrete runtime
// evidence that the modelled Go operations behave as the models assume.
package main

import (
	"fmt"
	"math/big"
)

// mirrors deposit.go MintShares share math (existingTotalShares > 0 branch).
func mintShares(quantums, totalShares, equity *big.Int) (mint *big.Int, panicked bool) {
	defer func() {
		if r := recover(); r != nil {
			panicked = true
		}
	}()
	mint = new(big.Int).Set(quantums)
	mint.Mul(mint, totalShares)
	mint.Quo(mint, equity) // <-- panics if equity == 0 (Go big.Int division by zero)
	return mint, false
}

// mirrors withdraw.go redeemed = equity * shares / totalShares (floor).
func redeemed(equity, shares, total *big.Int) *big.Int {
	r := new(big.Int).Set(equity)
	r.Mul(r, shares)
	r.Quo(r, total)
	return r
}

func main() {
	bi := big.NewInt

	fmt.Println("== F3: MintShares divides by equity; equity==0 with shares outstanding ==")
	mint, panicked := mintShares(bi(1000), bi(1000), bi(0))
	fmt.Printf("  mintShares(q=1000, total=1000, equity=0): panicked=%v (mint=%v)\n", panicked, mint)
	if !panicked {
		fmt.Println("  UNEXPECTED: expected a division-by-zero panic")
	}

	fmt.Println("== F3: redemption pays 0 when equity==0 while shares are outstanding ==")
	fmt.Printf("  redeemed(equity=0, shares=5, total=1000) = %v (=> withdrawal reverts)\n",
		redeemed(bi(0), bi(5), bi(1000)))

	fmt.Println("== F4: dust freeze -- equity < total, small holder floors to 0 ==")
	// equity dropped to 100 vs 1000 total shares; a 5-share holder:
	fmt.Printf("  redeemed(equity=100, shares=5, total=1000) = %v (=> reverts; 5 shares unwithdrawable)\n",
		redeemed(bi(100), bi(5), bi(1000)))
	// same holder cannot get a positive payout for ANY amount up to their balance:
	stuck := true
	for s := int64(1); s <= 5; s++ {
		if redeemed(bi(100), bi(s), bi(1000)).Sign() > 0 {
			stuck = false
		}
	}
	fmt.Printf("  no withdrawable amount 1..5 yields a positive payout: %v\n", stuck)

	fmt.Println("== sanity: redeemed <= equity, and positive once equity*shares >= total ==")
	fmt.Printf("  redeemed(equity=100, shares=1000, total=1000) = %v (== equity)\n",
		redeemed(bi(100), bi(1000), bi(1000)))
	fmt.Printf("  redeemed(equity=100, shares=10, total=1000)   = %v (> 0 at threshold)\n",
		redeemed(bi(100), bi(10), bi(1000)))
}
