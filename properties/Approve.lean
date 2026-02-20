-- properties/Approve.lean
-- Verification conditions for the ERC-20 approve() function.
-- All theorems use `sorry` stubs for Aristotle to fill.

import evm_model.Basic
import evm_model.ERC20


open EVMState ERC20

/-! ## Tier 1 — Arithmetic Safety -/

/-- approve always succeeds (never reverts). -/
theorem approve_never_reverts
    (state : EVMState) (spender : Address) (amt : UInt256) :
    approve state spender amt ≠ none := by sorry

/-- approve sets the allowance for (msg_sender, spender) to exactly amt. -/
theorem approve_sets_allowance
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.allowances state.msg_sender spender = amt := by sorry

/-! ## Tier 2 — State Invariants -/

/-- approve does not change any token balances. -/
theorem approve_preserves_balances
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.balances = state.balances := by sorry

/-- approve does not change totalSupply. -/
theorem approve_preserves_supply
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.totalSupply = state.totalSupply := by sorry

/-- approve does not affect allowances for any other (owner, spender') pair. -/
theorem approve_only_affects_target_allowance
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (a s : Address)
    (ha : a ≠ state.msg_sender ∨ s ≠ spender)
    (h : approve state spender amt = some state') :
    state'.allowances a s = state.allowances a s := by sorry

/-- Calling approve twice overwrites the first approval. -/
theorem approve_overrides_previous
    (state : EVMState) (spender : Address) (amt1 amt2 : UInt256) :
    ∃ state1,
      approve state spender amt1 = some state1 ∧
      ∃ state2,
        approve state1 spender amt2 = some state2 ∧
        state2.allowances state.msg_sender spender = amt2 := by sorry

/-! ## Tier 3 — Access Control -/

/-- approve only changes allowances originating from msg_sender:
    no other owner's allowances change. -/
theorem approve_only_affects_sender_allowances
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (a : Address) (ha : a ≠ state.msg_sender)
    (h : approve state spender amt = some state') :
    ∀ s, state'.allowances a s = state.allowances a s := by sorry
