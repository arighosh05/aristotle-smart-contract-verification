-- evm_model/Basic.lean
-- Core EVM types and state model for ERC-20 verification.
-- Models Solidity 0.8+ overflow-reverting arithmetic semantics.

/-- 256-bit unsigned integer, represented as Fin (2^256).
    Arithmetic wraps modulo 2^256 by default; overflow checks
    are performed explicitly in function definitions. -/
abbrev UInt256 := Fin (2^256)

/-- Ethereum address: 20-byte value, represented as a UInt256 for simplicity.
    (Valid addresses occupy only the lower 160 bits, but we don't
    enforce this constraint here.) -/
abbrev Address := UInt256

/-- EVM state relevant to an ERC-20 token contract.
    Represents a snapshot of the storage slots used by the token. -/
structure EVMState where
  /-- Token balance for each address. -/
  balances    : Address → UInt256
  /-- Approved spending amounts: allowances[owner][spender] = amount. -/
  allowances  : Address → Address → UInt256
  /-- Total token supply. -/
  totalSupply : UInt256
  /-- Transaction sender (msg.sender). -/
  msg_sender  : Address
  /-- ETH value sent with the transaction (msg.value). -/
  msg_value   : UInt256

namespace EVMState

/-- Helper: total value held by a pair of distinct addresses.
    Used in two-party conservation theorems (e.g. sender + recipient). -/
def pairSum (s : EVMState) (a b : Address) : Nat :=
  (s.balances a).val + (s.balances b).val

end EVMState
