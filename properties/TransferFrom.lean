-- properties/TransferFrom.lean
-- Verification conditions for the ERC-20 transferFrom() function.
-- All theorems use `sorry` stubs for Aristotle to fill.
--
-- Note: parameter `tgt` (not `to`) avoids a reserved word in Lean 4.24.

import evm_model.Basic
import evm_model.ERC20


open EVMState ERC20

/-! ## Tier 1 — Arithmetic Safety -/

/-- transferFrom reverts when the caller's allowance is insufficient. -/
theorem transferFrom_revert_insufficient_allowance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h : (state.allowances src state.msg_sender).val < amt.val) :
    transferFrom state src tgt amt = none := by sorry

/-- transferFrom reverts when src has insufficient balance
    (even if allowance is sufficient). -/
theorem transferFrom_revert_insufficient_balance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h_allow : amt.val ≤ (state.allowances src state.msg_sender).val)
    (h_bal : (state.balances src).val < amt.val) :
    transferFrom state src tgt amt = none := by sorry

/-- If transferFrom succeeds, src had sufficient balance. -/
theorem transferFrom_success_implies_sufficient_balance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt ≠ none) :
    amt.val ≤ (state.balances src).val := by sorry

/-- If transferFrom succeeds, the allowance was sufficient. -/
theorem transferFrom_success_implies_sufficient_allowance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt ≠ none) :
    amt.val ≤ (state.allowances src state.msg_sender).val := by sorry

/-! ## Tier 2 — State Invariants -/

/-- transferFrom preserves totalSupply. -/
theorem transferFrom_preserves_supply
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt = some state') :
    state'.totalSupply = state.totalSupply := by sorry

/-- transferFrom decrements the (src, msg_sender) allowance by exactly amt. -/
theorem transferFrom_decrements_allowance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt = some state') :
    (state'.allowances src state.msg_sender).val =
      (state.allowances src state.msg_sender).val - amt.val := by sorry

/-- On success with src ≠ tgt, src balance decreases by exactly amt. -/
theorem transferFrom_debits_src
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    (state'.balances src).val = (state.balances src).val - amt.val := by sorry

/-- On success with src ≠ tgt, recipient balance increases by exactly amt. -/
theorem transferFrom_credits_recipient
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    (state'.balances tgt).val = (state.balances tgt).val + amt.val := by sorry

/-- The sum of src + recipient balances is conserved (src ≠ tgt). -/
theorem transferFrom_conserves_pair_balance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    pairSum state' src tgt = pairSum state src tgt := by sorry

/-! ## Tier 3 — Access Control -/

/-- transferFrom only changes balances of src and tgt:
    every other address is unaffected. -/
theorem transferFrom_only_affects_participants
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (a : Address) (ha1 : a ≠ src) (ha2 : a ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    state'.balances a = state.balances a := by sorry

/-- transferFrom only changes the allowance for (src, msg_sender):
    all other allowances are unchanged. -/
theorem transferFrom_only_affects_target_allowance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (a s : Address) (ha : a ≠ src ∨ s ≠ state.msg_sender)
    (h : transferFrom state src tgt amt = some state') :
    state'.allowances a s = state.allowances a s := by sorry
