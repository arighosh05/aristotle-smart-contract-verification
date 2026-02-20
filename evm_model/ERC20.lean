-- evm_model/ERC20.lean
-- ERC-20 state-transition functions as pure Lean 4 definitions.
-- All functions return Option EVMState:
--   · some state' = successful execution with new state
--   · none        = revert (e.g. insufficient balance, overflow)
-- Overflow semantics match Solidity 0.8+: addition/subtraction that
-- would wrap reverts instead.
--
-- Note: parameter names avoid Lean 4.24 reserved words (`from`, `to`).
-- `tgt` = transfer recipient, `src` = transferFrom source.

import evm_model.Basic

open EVMState

namespace ERC20

/-! ## Read-only accessors -/

/-- Return the token balance of `addr`. -/
def balanceOf (state : EVMState) (addr : Address) : UInt256 :=
  state.balances addr

/-- Return the spending allowance that `owner` has granted to `spender`. -/
def allowanceOf (state : EVMState) (owner spender : Address) : UInt256 :=
  state.allowances owner spender

/-! ## State-transition functions -/

/-- transfer(tgt, amt): move `amt` tokens from `msg_sender` to `tgt`.
    Reverts (returns none) if:
      · sender balance < amt  (underflow)
      · recipient balance + amt ≥ 2^256 (overflow)
    The two-phase update correctly handles the self-transfer case
    (sender == tgt): first deduct, then credit from the deducted state. -/
def transfer (state : EVMState) (tgt : Address) (amt : UInt256) : Option EVMState :=
  let sender    := state.msg_sender
  let senderBal := state.balances sender
  -- Guard: underflow
  if h_bal : senderBal.val < amt.val then none
  else
    -- Deduct from sender (safe: amt.val ≤ senderBal.val)
    let newSenderBal : UInt256 := ⟨senderBal.val - amt.val, by
      have := senderBal.isLt; omega⟩
    let state1 : EVMState :=
      { state with balances := fun addr =>
          if addr == sender then newSenderBal else state.balances addr }
    -- Credit recipient from intermediate state (handles sender == tgt)
    let recipientBal := state1.balances tgt
    -- Guard: overflow
    if h_ovf : recipientBal.val + amt.val ≥ 2^256 then none
    else
      let newRecipientBal : UInt256 := ⟨recipientBal.val + amt.val, by
        have hlt := recipientBal.isLt
        omega⟩
      some { state1 with balances := fun addr =>
               if addr == tgt then newRecipientBal else state1.balances addr }

/-- approve(spender, amt): grant `spender` the right to spend up to `amt`
    tokens on behalf of `msg_sender`.  Always succeeds. -/
def approve (state : EVMState) (spender : Address) (amt : UInt256) : Option EVMState :=
  let owner := state.msg_sender
  some { state with allowances := fun a s =>
           if a == owner && s == spender then amt
           else state.allowances a s }

/-- transferFrom(src, tgt, amt): move `amt` tokens from `src` to `tgt`,
    deducting from the allowance that `src` has granted to `msg_sender`.
    Reverts if:
      · allowances[src][msg_sender] < amt  (insufficient allowance)
      · balances[src] < amt               (insufficient balance)
      · balances[tgt] + amt ≥ 2^256       (overflow) -/
def transferFrom (state : EVMState) (src tgt : Address) (amt : UInt256) :
    Option EVMState :=
  let spender     := state.msg_sender
  let srcBal      := state.balances src
  let spAllowance := state.allowances src spender
  -- Guard: allowance sufficient
  if h_allow : spAllowance.val < amt.val then none
  -- Guard: source has enough balance
  else if h_bal : srcBal.val < amt.val then none
  else
    -- Deduct allowance
    let newAllowance : UInt256 := ⟨spAllowance.val - amt.val, by
      have := spAllowance.isLt; omega⟩
    let state1 : EVMState :=
      { state with allowances := fun a s =>
          if a == src && s == spender then newAllowance
          else state.allowances a s }
    -- Deduct from src
    let newSrcBal : UInt256 := ⟨srcBal.val - amt.val, by
      have := srcBal.isLt; omega⟩
    let state2 : EVMState :=
      { state1 with balances := fun addr =>
          if addr == src then newSrcBal else state1.balances addr }
    -- Credit tgt (from intermediate state, handles src == tgt)
    let recipientBal := state2.balances tgt
    if h_ovf : recipientBal.val + amt.val ≥ 2^256 then none
    else
      let newRecipientBal : UInt256 := ⟨recipientBal.val + amt.val, by
        have hlt := recipientBal.isLt
        omega⟩
      some { state2 with balances := fun addr =>
               if addr == tgt then newRecipientBal else state2.balances addr }

end ERC20
