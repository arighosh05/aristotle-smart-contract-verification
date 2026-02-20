-- evm_model/AMM.lean
-- Constant-product AMM (Uniswap V2 style) state model.
-- Hardcodes the 0.3% fee (997/1000 Uniswap convention) in the swap function.
-- All intermediate arithmetic is done in Nat (arbitrary-precision) via .val
-- extraction; only the final reserve writes require Fin (2^256) bounds proofs.
--
-- Note: parameter names avoid Lean 4.24 reserved words (`from`, `to`).

import evm_model.Basic

/-- AMM pool state: two token reserves + LP accounting. -/
structure AMMState where
  /-- Reserve of token0 (the input token for swap). -/
  reserve0   : UInt256
  /-- Reserve of token1 (the output token for swap). -/
  reserve1   : UInt256
  /-- Total outstanding LP tokens. -/
  totalLP    : UInt256
  /-- LP token balances per address. -/
  lpBalances : Address → UInt256

namespace AMMState

/-- swap(amtIn): exchange `amtIn` units of token0 for token1.
    Fee: 0.3% (Uniswap V2 convention: multiply input by 997, denominator by 1000).
    Returns none (revert) if:
      · amtIn = 0
      · either reserve is 0 (empty / uninitialized pool)
      · amountOut = 0 (input too small, rounds to zero)
      · amountOut ≥ reserve1 (would drain the pool)
      · reserve0 + amtIn overflows UInt256

    Constant-product formula:
      amountInWithFee = amtIn * 997
      amountOut       = ⌊ amountInWithFee * reserve1 / (reserve0 * 1000 + amountInWithFee) ⌋ -/
def swap (state : AMMState) (amtIn : UInt256) : Option AMMState :=
  if h_zero : amtIn.val = 0 then none
  else if h_pool : state.reserve0.val = 0 ∨ state.reserve1.val = 0 then none
  else
    let r0  := state.reserve0.val
    let r1  := state.reserve1.val
    let f   := amtIn.val * 997          -- amountInWithFee  (Nat, no overflow)
    let num := f * r1                   -- numerator
    let den := r0 * 1000 + f            -- denominator (> 0 since r0 > 0)
    let amtOut := num / den             -- Nat.div (floor division)
    if h_drain : amtOut = 0 ∨ amtOut ≥ r1 then none
    else if h_ovf : r0 + amtIn.val ≥ 2^256 then none
    else
      -- newR0: safe because ¬h_ovf gives r0 + amtIn.val < 2^256
      let newR0 : UInt256 := ⟨r0 + amtIn.val, by omega⟩
      -- newR1: r1 - amtOut ≤ r1 (Nat.sub_le, always) and r1 < 2^256 (reserve1.isLt).
      let newR1 : UInt256 := ⟨r1 - amtOut, by
        exact Nat.lt_of_le_of_lt (Nat.sub_le r1 amtOut) state.reserve1.isLt⟩
      some { state with reserve0 := newR0, reserve1 := newR1 }

end AMMState
