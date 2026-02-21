# automated smart contract verification with aristotle

formal verification of ERC-20 tokens and AMM swap invariants using [aristotle](https://harmonic.fun)'s theorem prover. 29 theorems submitted, 28 proved, 1 correctly falsified with a counterexample.

the headline result: aristotle proved the constant product invariant for a uniswap v2-style swap—a property class that SMT-based verifiers require [lossy overapproximations](https://arxiv.org/pdf/2402.10174) to attempt. nonlinear integer arithmetic is [undecidable](https://en.wikipedia.org/wiki/Hilbert%27s_tenth_problem) for SMT solvers; they either time out or fall back to bounded reasoning, which isn't a proof. 

---

## background

smart contract auditing is a multi-billion dollar market. the dominant verification approach uses SMT solvers on EVM bytecode—automated, fast, and limited by what the solver can decide.

every AMM on ethereum depends on the constant product invariant: after a swap, `reserve0 * reserve1` must not decrease. this involves multiplication of two uint256 values, integer division with truncation, and fee arithmetic. no SMT-based tool can formally verify this end-to-end. auditors currently verify it by hand or with bounded model checking.

a separate line of work [extracts solidity's yul IR to lean 4](https://www.nethermind.io/blog/clear-prove-anything-about-your-solidity-smart-contracts) for interactive theorem proving. this gives full mathematical expressiveness but requires human experts to write every proof manually.

aristotle's [VERINA benchmark results](https://harmonic.fun/news)—96.8% success on [189 code verification tasks](https://arxiv.org/abs/2505.23135) in lean—suggested a third path: automated proof generation with full expressiveness. the question was whether that capability extends from functional programs to state machine verification. that's precisely what i wanted to find out.

---

## results

### ERC-20 (baseline)

28 theorems across `transfer`, `approve`, and `transferFrom`—all proved. properties verified include balance conservation, overflow safety, allowance correctness, access control, and non-interference.

aristotle's dominant strategy: `unfold; aesop`. expand the definition, let automation handle the conditional logic. this works because the state-transition functions are pure if-then-else with no recursion or loops. once unfolded, the goals are within reach of standard lean automation.

these results establish that aristotle handles the same property classes that SMT-based tools already handle well. necessary groundwork, but not the interesting part.

### AMM (novel result)

8 theorems on a [uniswap v2-style](https://docs.uniswap.org/contracts/v2/concepts/protocol-overview/how-uniswap-works) swap function—7 proved, 1 correctly negated.

| theorem | result | significance |
|---------|--------|-------------|
| `swap_preserves_constant_product` | **proved** | the core invariant. uses `nlinarith`—beyond SMT decidability. |
| `swap_output_bounded` | proved | output cannot exceed reserves |
| `swap_reserves_nonzero` | proved | positive reserves maintained |
| `swap_reserve0_increases` | proved | input reserve grows |
| `swap_no_free_value` | **negated** | correctly falsified with concrete witness |
| 3 helper lemmas | proved | floor division, denominator positivity, fee bounds |

### the key proof

```lean
theorem swap_preserves_constant_product
    (state state' : AMMState) (amtIn : Fin (2^256))
    (h : swap state amtIn = some state') :
  state'.reserve0.val * state'.reserve1.val ≥ state.reserve0.val * state.reserve1.val
```

aristotle's proof: unfold the swap, destruct the guards, normalize, then close with `nlinarith` using `Nat.div_mul_le_self` as a hint—the floor property that `amountOut * denominator ≤ numerator` bounds output below the level that would violate the invariant.

the proof operates over unbounded `Nat`, not modular `Fin (2^256)`. this is sound because the swap function guards against overflow (returns `none` if reserves would exceed the bound). the guards ensure you never hit the modular boundary, so natural number reasoning suffices.

SMT solvers receive the equivalent goal `(r0+i)*(r1-o) ≥ r0*r1` over 256-bit integers and return "unknown." `nlinarith` in lean closes it in one step given the right hint. this isn't a performance gap—it's a decidability gap. nonlinear integer arithmetic [has been undecidable since 1970](https://en.wikipedia.org/wiki/Matiyasevich%27s_theorem); SMT solvers can only approximate it.

### the counterexample

aristotle negated `swap_no_free_value` (the conjecture that `r0 + r1` is conserved) with a concrete witness:

```
reserve0 = 1,000    reserve1 = 1,000,000    amtIn = 1
amtOut = 996

sum before: 1,001,000
sum after:  1,000,005    ← decreased
```

trading 1 token0 into a pool with a 1:1000 price ratio returns 996 token1. the raw token count extracted far exceeds the deposit, so the arithmetic sum shrinks. the constant-product invariant guarantees `x*y` is preserved, not `x+y`. this is correct AMM behavior—and a demonstration that aristotle's falsification returns checkable witnesses, not just "false."

---

## verification scope

this project verifies **lean 4 models** of ERC-20 and AMM contracts, not EVM bytecode.

the models capture uint256 overflow/underflow semantics (via `Fin (2^256)` with explicit guards), allowance deduction, msg.sender access control, self-transfer correctness, and constant product arithmetic with fee calculation and integer division truncation.

the models do not capture gas accounting, storage layout, ABI encoding, reentrancy, or events. closing this gap requires formally verified extraction from solidity/yul to lean—[existing work](https://www.nethermind.io/blog/clear-prove-anything-about-your-solidity-smart-contracts) takes this approach but requires manual proofs. the contribution here is demonstrating that aristotle's proof search handles state-machine verification patterns automatically, including nonlinear arithmetic that existing tools cannot reach.

---

## repo structure

```
evm_model/
  Basic.lean              core types: address, uint256, EVMState
  ERC20.lean              transfer, approve, transferFrom
  AMM.lean                AMMState, swap (uniswap v2 model)

properties/
  Transfer.lean           11 theorems (sorry stubs as submitted)
  Approve.lean            7 theorems
  TransferFrom.lean       11 theorems
  AMM.lean                8 theorems including helper lemmas

results/
  Transfer_proved.lean    aristotle output with proofs filled
  Approve_proved.lean
  TransferFrom_proved.lean
  AMM_proved.lean
  run_logs/               API responses and metadata

FINDINGS.md               full technical analysis
lakefile.lean             lean 4 project configuration
```

`properties/` is what was submitted (theorems with `sorry`). `results/` is what aristotle returned (proofs filled). diff them to see what the prover generated.

---

## the landscape

|  | SMT-based (bytecode) | interactive (lean 4) | this project |
|---|---|---|---|
| automation | fully automated | manual proof writing | fully automated |
| expressiveness | limited by SMT decidability | full lean expressiveness | full lean expressiveness |
| nonlinear arithmetic | timeout / unknown | provable (if human writes proof) | **proved automatically** |
| verifies bytecode | yes | yes (via extraction) | no (lean model only) |

the gap before aristotle: automated verification was limited by what SMT solvers can decide. expressive verification required human proof engineers. aristotle fills the missing quadrant—automated and expressive.

---

## technical details

see [ANALYSIS.md](ANALYSIS.md) for the full analysis: proof tactics, comparisons, failure modes, version compatibility notes, and counterexample verification.

**built with:** lean 4 · aristotle 0.7.0 · mathlib f897ebcf

**references:**
- [overapproximation of non-linear integer arithmetic for smart contract verification](https://arxiv.org/pdf/2402.10174) — documents the lossy approximations SMT-based tools use to work around nonlinear arithmetic; the exact limitation aristotle sidesteps
- [VERINA: benchmarking verifiable code generation](https://arxiv.org/abs/2505.23135) — the benchmark aristotle [scored 96.8% on](https://harmonic.fun/news)
- [uniswap v2 protocol overview](https://docs.uniswap.org/contracts/v2/concepts/protocol-overview/how-uniswap-works) — the swap model this project verifies
- [matiyasevich's theorem](https://en.wikipedia.org/wiki/Matiyasevich%27s_theorem) — why nonlinear integer arithmetic is undecidable for SMT; resolving [Hilbert's 10th problem](https://en.wikipedia.org/wiki/Hilbert%27s_tenth_problem) negatively
- [clear: yul → lean 4 extraction](https://www.nethermind.io/blog/clear-prove-anything-about-your-solidity-smart-contracts) — existing work on bridging the semantic gap
