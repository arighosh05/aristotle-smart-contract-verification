/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aa19b2c0-5e9f-4de8-981f-75c4f7d24a30

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem swap_den_pos (r0 i : Nat) (hr0 : r0 > 0) :
    r0 * 1000 + i * 997 > 0

- theorem amtOut_floor_le (r0 r1 i : Nat) (hr0 : r0 > 0) :
    i * 997 * r1 / (r0 * 1000 + i * 997) * (r0 * 1000 + i * 997) ≤ i * 997 * r1

- theorem fee_arithmetic (r0 i : Nat) :
    (r0 + i) * 1000 ≥ r0 * 1000 + i * 997

- theorem swap_preserves_constant_product
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val * state'.reserve1.val ≥
    state.reserve0.val * state.reserve1.val

- theorem swap_output_bounded
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve1.val < state.reserve1.val

- theorem swap_reserves_nonzero
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val > 0 ∧ state'.reserve1.val > 0

- theorem swap_reserve0_increases
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val > state.reserve0.val

The following was negated by Aristotle:

- theorem swap_no_free_value
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val + state'.reserve1.val ≥
    state.reserve0.val + state.reserve1.val

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

-- properties/AMM.lean
-- Verification conditions for the AMM constant-product invariant.
-- All theorems use `sorry` stubs for Aristotle to fill.
--
-- The key theorem (swap_preserves_constant_product) asks Aristotle to prove
-- that x·y does not decrease after a fee-taking swap — a nonlinear arithmetic
-- property that breaks Z3/Certora but reduces to linear arithmetic via the
-- proof chain in the helper theorems below.
--
-- Proof sketch for swap_preserves_constant_product:
--   Let r0, r1 = reserves, i = amtIn, f = i*997, d = r0*1000 + f,
--       o = ⌊f*r1/d⌋  (the output amount).
--   Goal: (r0 + i)*(r1 - o) ≥ r0*r1
--   Step 1: o ≤ f*r1/d        (floor definition)
--   Step 2: r1 - o ≥ r1*(d-f)/d = r1*r0*1000/d  (since d - f = r0*1000)
--   Step 3: (r0+i)*r1*r0*1000/d ≥ r0*r1  ↔  (r0+i)*1000 ≥ d = r0*1000 + i*997
--   Step 4: i*3 ≥ 0           ✓  (omega closes this)
--
-- fee_arithmetic captures Step 4; amtOut_floor_le captures Step 1.

import evm_model.Basic
import evm_model.AMM


open AMMState

/-! ## Helper Lemmas (proof skeleton for Aristotle) -/

/-- The denominator r0*1000 + i*997 is strictly positive whenever r0 > 0. -/
theorem swap_den_pos (r0 i : Nat) (hr0 : r0 > 0) :
    r0 * 1000 + i * 997 > 0 := by
      positivity

/-- Floor division satisfies: q * d ≤ n  (where q = n / d). -/
theorem amtOut_floor_le (r0 r1 i : Nat) (hr0 : r0 > 0) :
    i * 997 * r1 / (r0 * 1000 + i * 997) * (r0 * 1000 + i * 997) ≤ i * 997 * r1 := by
      exact Nat.div_mul_le_self _ _

/-- Key fee arithmetic: (r0 + i)*1000 ≥ r0*1000 + i*997.
    Equivalently i*3 ≥ 0, which is trivially true. -/
theorem fee_arithmetic (r0 i : Nat) :
    (r0 + i) * 1000 ≥ r0 * 1000 + i * 997 := by
      grind

/-! ## Tier 1 — Core Invariant -/

/-- The constant product x·y does not decrease after a successful swap.
    This is the central correctness property of any AMM:
    the pool's aggregate "value" (measured by the geometric mean) is preserved
    or increases after every trade, guaranteeing LPs are not drained. -/
theorem swap_preserves_constant_product
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val * state'.reserve1.val ≥
    state.reserve0.val * state.reserve1.val := by
      unfold AMMState.swap at h;
      split_ifs at h;
      norm_num +zetaDelta at *;
      rw [ ← h.2.choose_spec ];
      rw [ Nat.mul_sub_left_distrib ];
      exact le_tsub_of_add_le_left ( by nlinarith [ Nat.div_mul_le_self ( ( amtIn : ℕ ) * 997 * ( state.reserve1 : ℕ ) ) ( ( state.reserve0 : ℕ ) * 1000 + ( amtIn : ℕ ) * 997 ) ] )

/-! ## Tier 2 — Reserve Safety -/

/-- After a successful swap, the output token reserve strictly decreases.
    The pool always keeps a positive reserve1 (enforced by the drain guard). -/
theorem swap_output_bounded
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve1.val < state.reserve1.val := by
      -- By definition of swap, we know that reserve1' = reserve1 - amountOut.
      have h_res1 : state'.reserve1.val = state.reserve1.val - (amtIn.val * 997 * state.reserve1.val / (state.reserve0.val * 1000 + amtIn.val * 997)) := by
        unfold AMMState.swap at h;
        grind;
      -- Since the reserves are positive integers, the division result is positive, so the subtraction will make the new value smaller.
      have h_pos : 0 < (amtIn.val * 997 * state.reserve1.val) / (state.reserve0.val * 1000 + amtIn.val * 997) := by
        unfold AMMState.swap at h;
        grind;
      exact h_res1.symm ▸ Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop ) ) h_pos

/-- Both reserves remain strictly positive after a successful swap. -/
theorem swap_reserves_nonzero
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val > 0 ∧ state'.reserve1.val > 0 := by
      unfold AMMState.swap at h;
      split_ifs at h ; simp_all +decide;
      rcases h with ⟨ ⟨ h₁, h₂ ⟩, _, rfl ⟩;
      exact ⟨ Nat.pos_of_ne_zero ( by aesop ), Nat.sub_pos_of_lt h₂ ⟩

/-- After a successful swap, reserve0 strictly increases. -/
theorem swap_reserve0_increases
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val > state.reserve0.val := by
      unfold AMMState.swap at h;
      grind

/-! ## Tier 3 — Value Conservation Conjecture -/

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Conjecture: the raw token sum (reserve0 + reserve1) does not decrease.
    This is NOT guaranteed by the constant-product formula for imbalanced pools —
    include it so Aristotle can either prove it or return a counterexample.
    A counterexample would demonstrate Aristotle's falsification capability.
-/
theorem swap_no_free_value
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val + state'.reserve1.val ≥
    state.reserve0.val + state.reserve1.val := by
      -- Wait, there's a mistake. We can actually prove the opposite.
      negate_state;
      -- Proof starts here:
      fconstructor;
      constructor;
      exact ⟨ 1000, by decide ⟩;
      exact ⟨ 1000000, by decide ⟩;
      exact ⟨ 1000, by decide ⟩;
      exact fun _ => ⟨ 0, by decide ⟩;
      exists ⟨ ⟨ 1000 + 1, by decide ⟩, ⟨ 1000000 - ( 1 * 997 * 1000000 / ( 1000 * 1000 + 1 * 997 ) ), by decide ⟩, ⟨ 1000, by decide ⟩, fun _ => ⟨ 0, by decide ⟩ ⟩, ⟨ 1, by decide ⟩

-/
/-- Conjecture: the raw token sum (reserve0 + reserve1) does not decrease.
    This is NOT guaranteed by the constant-product formula for imbalanced pools —
    include it so Aristotle can either prove it or return a counterexample.
    A counterexample would demonstrate Aristotle's falsification capability. -/
theorem swap_no_free_value
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val + state'.reserve1.val ≥
    state.reserve0.val + state.reserve1.val := by sorry