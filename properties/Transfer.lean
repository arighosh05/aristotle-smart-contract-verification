-- properties/Transfer.lean
-- Verification conditions for the ERC-20 transfer() function.
-- All theorems use `sorry` stubs for Aristotle to fill.
--
-- Tier 1 — Arithmetic safety
-- Tier 2 — State invariants
-- Tier 3 — Access control
--
-- Note: parameter `tgt` (not `to`) avoids a reserved word in Lean 4.24.

import evm_model.Basic
import evm_model.ERC20


open EVMState ERC20

/-! ## Tier 1 — Arithmetic Safety -/

/-- transfer reverts when the sender has insufficient balance. -/
theorem transfer_revert_insufficient_balance
    (state : EVMState) (tgt : Address) (amt : UInt256)
    (h : (state.balances state.msg_sender).val < amt.val) :
    transfer state tgt amt = none := by sorry

/-- If transfer succeeds, the sender had enough balance. -/
theorem transfer_success_implies_sufficient_balance
    (state : EVMState) (tgt : Address) (amt : UInt256)
    (h : transfer state tgt amt ≠ none) :
    amt.val ≤ (state.balances state.msg_sender).val := by sorry

/-- If transfer succeeds, the recipient balance after is < 2^256.
    Trivially true by the Fin type bound. -/
theorem transfer_recipient_bounded
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (h : transfer state tgt amt = some state') :
    (state'.balances tgt).val < 2^256 :=
  (state'.balances tgt).isLt

/-- If transfer succeeds, recipient balance before + amt did not overflow.
    Precondition: sender ≠ tgt (distinct parties). -/
theorem transfer_no_recipient_overflow
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (h_neq : state.msg_sender ≠ tgt)
    (h : transfer state tgt amt = some state') :
    (state.balances tgt).val + amt.val < 2^256 := by sorry

/-! ## Tier 2 — State Invariants -/

/-- transfer preserves totalSupply. -/
theorem transfer_preserves_supply
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (h : transfer state tgt amt = some state') :
    state'.totalSupply = state.totalSupply := by sorry

/-- transfer leaves the allowances mapping unchanged. -/
theorem transfer_preserves_allowances
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (h : transfer state tgt amt = some state') :
    state'.allowances = state.allowances := by sorry

/-- On success with sender ≠ tgt, sender balance decreases by exactly amt. -/
theorem transfer_debits_sender
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (h_neq : state.msg_sender ≠ tgt)
    (h : transfer state tgt amt = some state') :
    (state'.balances state.msg_sender).val =
      (state.balances state.msg_sender).val - amt.val := by sorry

/-- On success with sender ≠ tgt, recipient balance increases by exactly amt. -/
theorem transfer_credits_recipient
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (h_neq : state.msg_sender ≠ tgt)
    (h : transfer state tgt amt = some state') :
    (state'.balances tgt).val = (state.balances tgt).val + amt.val := by sorry

/-- The sum of sender + recipient balances is conserved (sender ≠ tgt). -/
theorem transfer_conserves_pair_balance
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (h_neq : state.msg_sender ≠ tgt)
    (h : transfer state tgt amt = some state') :
    pairSum state' state.msg_sender tgt = pairSum state state.msg_sender tgt := by sorry

/-! ## Tier 3 — Access Control -/

/-- transfer leaves all balances unchanged except those of sender and tgt. -/
theorem transfer_only_affects_participants
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (a : Address) (ha1 : a ≠ state.msg_sender) (ha2 : a ≠ tgt)
    (h : transfer state tgt amt = some state') :
    state'.balances a = state.balances a := by sorry

/-- Universal form: all non-participant balances are frozen. -/
theorem transfer_sender_is_msg_sender
    (state state' : EVMState) (tgt : Address) (amt : UInt256)
    (h : transfer state tgt amt = some state') :
    ∀ a, a ≠ state.msg_sender → a ≠ tgt → state'.balances a = state.balances a := by sorry
