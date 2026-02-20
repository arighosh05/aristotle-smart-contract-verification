/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b24204a2-805e-40e7-ac12-9b819a4e46e2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem transferFrom_revert_insufficient_allowance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h : (state.allowances src state.msg_sender).val < amt.val) :
    transferFrom state src tgt amt = none

- theorem transferFrom_revert_insufficient_balance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h_allow : amt.val ≤ (state.allowances src state.msg_sender).val)
    (h_bal : (state.balances src).val < amt.val) :
    transferFrom state src tgt amt = none

- theorem transferFrom_success_implies_sufficient_balance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt ≠ none) :
    amt.val ≤ (state.balances src).val

- theorem transferFrom_success_implies_sufficient_allowance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt ≠ none) :
    amt.val ≤ (state.allowances src state.msg_sender).val

- theorem transferFrom_preserves_supply
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt = some state') :
    state'.totalSupply = state.totalSupply

- theorem transferFrom_decrements_allowance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt = some state') :
    (state'.allowances src state.msg_sender).val =
      (state.allowances src state.msg_sender).val - amt.val

- theorem transferFrom_debits_src
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    (state'.balances src).val = (state.balances src).val - amt.val

- theorem transferFrom_credits_recipient
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    (state'.balances tgt).val = (state.balances tgt).val + amt.val

- theorem transferFrom_conserves_pair_balance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    pairSum state' src tgt = pairSum state src tgt

- theorem transferFrom_only_affects_participants
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (a : Address) (ha1 : a ≠ src) (ha2 : a ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    state'.balances a = state.balances a

- theorem transferFrom_only_affects_target_allowance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (a s : Address) (ha : a ≠ src ∨ s ≠ state.msg_sender)
    (h : transferFrom state src tgt amt = some state') :
    state'.allowances a s = state.allowances a s
-/

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
    transferFrom state src tgt amt = none := by
  -- By definition of `transferFrom`, if the allowance is insufficient, the function returns `none`.
  simp [ERC20.transferFrom, h]

/-- transferFrom reverts when src has insufficient balance
    (even if allowance is sufficient). -/
theorem transferFrom_revert_insufficient_balance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h_allow : amt.val ≤ (state.allowances src state.msg_sender).val)
    (h_bal : (state.balances src).val < amt.val) :
    transferFrom state src tgt amt = none := by
  unfold ERC20.transferFrom; aesop

/-- If transferFrom succeeds, src had sufficient balance. -/
theorem transferFrom_success_implies_sufficient_balance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt ≠ none) :
    amt.val ≤ (state.balances src).val := by
  contrapose! h;
  unfold ERC20.transferFrom; aesop;

/-- If transferFrom succeeds, the allowance was sufficient. -/
theorem transferFrom_success_implies_sufficient_allowance
    (state : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt ≠ none) :
    amt.val ≤ (state.allowances src state.msg_sender).val := by
  contrapose! h;
  exact?

/-! ## Tier 2 — State Invariants -/

/-- transferFrom preserves totalSupply. -/
theorem transferFrom_preserves_supply
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt = some state') :
    state'.totalSupply = state.totalSupply := by
  unfold ERC20.transferFrom at h ; aesop

/-- transferFrom decrements the (src, msg_sender) allowance by exactly amt. -/
theorem transferFrom_decrements_allowance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h : transferFrom state src tgt amt = some state') :
    (state'.allowances src state.msg_sender).val =
      (state.allowances src state.msg_sender).val - amt.val := by
  unfold ERC20.transferFrom at h ; aesop

/-- On success with src ≠ tgt, src balance decreases by exactly amt. -/
theorem transferFrom_debits_src
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    (state'.balances src).val = (state.balances src).val - amt.val := by
  unfold ERC20.transferFrom at h;
  aesop

/-- On success with src ≠ tgt, recipient balance increases by exactly amt. -/
theorem transferFrom_credits_recipient
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    (state'.balances tgt).val = (state.balances tgt).val + amt.val := by
  unfold ERC20.transferFrom at h ; aesop

/-- The sum of src + recipient balances is conserved (src ≠ tgt). -/
theorem transferFrom_conserves_pair_balance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (h_neq : src ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    pairSum state' src tgt = pairSum state src tgt := by
  unfold EVMState.pairSum at *;
  unfold ERC20.transferFrom at h;
  simp +zetaDelta at *;
  obtain ⟨ h₁, h₂, h₃, rfl ⟩ := h;
  grind

/-! ## Tier 3 — Access Control -/

/-- transferFrom only changes balances of src and tgt:
    every other address is unaffected. -/
theorem transferFrom_only_affects_participants
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (a : Address) (ha1 : a ≠ src) (ha2 : a ≠ tgt)
    (h : transferFrom state src tgt amt = some state') :
    state'.balances a = state.balances a := by
  unfold ERC20.transferFrom at h; aesop;

/-- transferFrom only changes the allowance for (src, msg_sender):
    all other allowances are unchanged. -/
theorem transferFrom_only_affects_target_allowance
    (state state' : EVMState) (src tgt : Address) (amt : UInt256)
    (a s : Address) (ha : a ≠ src ∨ s ≠ state.msg_sender)
    (h : transferFrom state src tgt amt = some state') :
    state'.allowances a s = state.allowances a s := by
  unfold ERC20.transferFrom at h; aesop;