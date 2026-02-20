/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 38d483a6-3240-4873-acaf-c9b85451af19

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem approve_never_reverts
    (state : EVMState) (spender : Address) (amt : UInt256) :
    approve state spender amt ≠ none

- theorem approve_sets_allowance
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.allowances state.msg_sender spender = amt

- theorem approve_preserves_balances
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.balances = state.balances

- theorem approve_preserves_supply
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.totalSupply = state.totalSupply

- theorem approve_only_affects_target_allowance
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (a s : Address)
    (ha : a ≠ state.msg_sender ∨ s ≠ spender)
    (h : approve state spender amt = some state') :
    state'.allowances a s = state.allowances a s

- theorem approve_overrides_previous
    (state : EVMState) (spender : Address) (amt1 amt2 : UInt256) :
    ∃ state1,
      approve state spender amt1 = some state1 ∧
      ∃ state2,
        approve state1 spender amt2 = some state2 ∧
        state2.allowances state.msg_sender spender = amt2

- theorem approve_only_affects_sender_allowances
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (a : Address) (ha : a ≠ state.msg_sender)
    (h : approve state spender amt = some state') :
    ∀ s, state'.allowances a s = state.allowances a s
-/

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
    approve state spender amt ≠ none := by
  tauto

/-- approve sets the allowance for (msg_sender, spender) to exactly amt. -/
theorem approve_sets_allowance
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.allowances state.msg_sender spender = amt := by
  cases h ; aesop

/-! ## Tier 2 — State Invariants -/

/-- approve does not change any token balances. -/
theorem approve_preserves_balances
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.balances = state.balances := by
  cases h;
  rfl

/-- approve does not change totalSupply. -/
theorem approve_preserves_supply
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (h : approve state spender amt = some state') :
    state'.totalSupply = state.totalSupply := by
  cases h ; aesop

/-- approve does not affect allowances for any other (owner, spender') pair. -/
theorem approve_only_affects_target_allowance
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (a s : Address)
    (ha : a ≠ state.msg_sender ∨ s ≠ spender)
    (h : approve state spender amt = some state') :
    state'.allowances a s = state.allowances a s := by
  cases ha <;> rw [ERC20.approve] at h <;> aesop

/-- Calling approve twice overwrites the first approval. -/
theorem approve_overrides_previous
    (state : EVMState) (spender : Address) (amt1 amt2 : UInt256) :
    ∃ state1,
      approve state spender amt1 = some state1 ∧
      ∃ state2,
        approve state1 spender amt2 = some state2 ∧
        state2.allowances state.msg_sender spender = amt2 := by
  unfold ERC20.approve; aesop;

/-! ## Tier 3 — Access Control -/

/-- approve only changes allowances originating from msg_sender:
    no other owner's allowances change. -/
theorem approve_only_affects_sender_allowances
    (state state' : EVMState) (spender : Address) (amt : UInt256)
    (a : Address) (ha : a ≠ state.msg_sender)
    (h : approve state spender amt = some state') :
    ∀ s, state'.allowances a s = state.allowances a s := by
  unfold ERC20.approve at h ; aesop