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
    r0 * 1000 + i * 997 > 0 := by sorry

/-- Floor division satisfies: q * d ≤ n  (where q = n / d). -/
theorem amtOut_floor_le (r0 r1 i : Nat) (hr0 : r0 > 0) :
    i * 997 * r1 / (r0 * 1000 + i * 997) * (r0 * 1000 + i * 997) ≤ i * 997 * r1 := by sorry

/-- Key fee arithmetic: (r0 + i)*1000 ≥ r0*1000 + i*997.
    Equivalently i*3 ≥ 0, which is trivially true. -/
theorem fee_arithmetic (r0 i : Nat) :
    (r0 + i) * 1000 ≥ r0 * 1000 + i * 997 := by sorry

/-! ## Tier 1 — Core Invariant -/

/-- The constant product x·y does not decrease after a successful swap.
    This is the central correctness property of any AMM:
    the pool's aggregate "value" (measured by the geometric mean) is preserved
    or increases after every trade, guaranteeing LPs are not drained. -/
theorem swap_preserves_constant_product
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val * state'.reserve1.val ≥
    state.reserve0.val * state.reserve1.val := by sorry

/-! ## Tier 2 — Reserve Safety -/

/-- After a successful swap, the output token reserve strictly decreases.
    The pool always keeps a positive reserve1 (enforced by the drain guard). -/
theorem swap_output_bounded
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve1.val < state.reserve1.val := by sorry

/-- Both reserves remain strictly positive after a successful swap. -/
theorem swap_reserves_nonzero
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val > 0 ∧ state'.reserve1.val > 0 := by sorry

/-- After a successful swap, reserve0 strictly increases. -/
theorem swap_reserve0_increases
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val > state.reserve0.val := by sorry

/-! ## Tier 3 — Value Conservation Conjecture -/

/-- Conjecture: the raw token sum (reserve0 + reserve1) does not decrease.
    This is NOT guaranteed by the constant-product formula for imbalanced pools —
    include it so Aristotle can either prove it or return a counterexample.
    A counterexample would demonstrate Aristotle's falsification capability. -/
theorem swap_no_free_value
    (state state' : AMMState) (amtIn : UInt256)
    (h : swap state amtIn = some state') :
    state'.reserve0.val + state'.reserve1.val ≥
    state.reserve0.val + state.reserve1.val := by sorry
