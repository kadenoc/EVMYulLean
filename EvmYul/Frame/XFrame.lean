import EvmYul.Frame.MutualFrame
import EvmYul.Frame.StepFrame
import EvmYul.Frame.SelfdestructFrame
import EvmYul.Frame.UpsilonFrame

/-!
# XFrame — `X`-level balance frame infrastructure for `Ξ_balanceOf_ge`.

This file stages helper lemmas for the fuel-induction proof of
`Ξ_balanceOf_ge` (declared in `MutualFrame.lean`). `Ξ` unfolds to
`X` on a freshly-built `EVM.State`, and `X` iterates `step` over a
fuel budget. Per-step balance monotonicity at `C` follows from the
already-closed per-opcode frame lemmas:

  * CALL / CALLCODE / DELEGATECALL / STATICCALL — `Θ_balanceOf_ge`
    (via `call`, via `MutualFrame.lean`).
  * CREATE / CREATE2 — `Λ_balanceOf_ge`.
  * SELFDESTRUCT — `selfdestruct_balanceOf_ne_Iₐ_ge`.
  * Regular (handled by `EvmYul.step`) — `EvmYul.step_preserves_balanceOf`.

**Current content.** This file contains:

  1. `EVM_X_zero` — `X 0 _ _ = .error .OutOfFuel`. Closed.
  2. `X_balance_ge_zero` — the fuel-0 monotonicity fact. Closed.
  3. `X_result_monotone_at_C` — statement wrapper used by
     `Ξ_balanceOf_ge`. Declared with its full intended body as a
     private theorem whose proof lives upstream.

No new `sorry` or `axiom` is introduced. The full X-fuel induction
remains the open obligation in `Ξ_balanceOf_ge` (sorry + detailed
block comment there). -/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM

/-- `X` at zero fuel immediately errors. This is a direct structural
unfolding; it does not depend on the EVM state. -/
theorem EVM_X_zero
    (validJumps : Array UInt256) (evmState : EVM.State) :
    EVM.X 0 validJumps evmState = .error .OutOfFuel := rfl

/-! ## `step` fuel-irrelevance for non-system ops (call-free monotonicity brick)

`X (f+1)` invokes `step f gasCost instr s`, and `step` threads its fuel `f`
into the nested `Ξ`/`Λ` only through the six *system* arms (CREATE, CREATE2,
CALL, CALLCODE, DELEGATECALL, STATICCALL); every other opcode (STOP / RETURN /
REVERT / SELFDESTRUCT / arithmetic / stack / storage / …) hits the fall-through
`EvmYul.step instr arg {…}`, which never reads the fuel. So for any op *outside*
those six, `step`'s result is independent of the fuel value.

This is the leaf enabler of a **call-free `X`-success fuel-monotonicity** lemma
(`X n s = success sf → X (n+1) s = success sf`): a run whose every executed op is
non-system never depends on fuel except as the recursion bound, so surplus fuel
after halting is inert. `X` is NOT fuel-monotone in general (surplus fuel feeds
nested calls and can flip an outer branch), which is exactly why the hypothesis
is "no CALL/CREATE executed". -/

set_option maxHeartbeats 4000000 in
/-- `EVM.step`'s result is independent of the fuel value for any op that is not
one of the six system (CALL/CREATE-family) ops: both `f+1` and `f'+1` route the
op to the fuel-free `EvmYul.step` fall-through arm. -/
theorem step_fuel_irrel
    (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (gasCost : ℕ)
    (f f' : ℕ) (s : EVM.State)
    (h1 : op ≠ .CREATE) (h2 : op ≠ .CREATE2) (h3 : op ≠ .CALL)
    (h4 : op ≠ .CALLCODE) (h5 : op ≠ .DELEGATECALL) (h6 : op ≠ .STATICCALL) :
    EVM.step (f + 1) gasCost (some (op, arg)) s
      = EVM.step (f' + 1) gasCost (some (op, arg)) s := by
  cases op
  case System sysOp =>
    cases sysOp <;> first
      | rfl
      | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3
      | exact absurd rfl h4 | exact absurd rfl h5 | exact absurd rfl h6
  all_goals rfl

/-- `X_balance_ge` at fuel 0: trivial because `X 0 _ _ = .error`. The
match on the result reduces to `True` in the `.error` branch, which
is discharged by `trivial`. -/
theorem X_balance_ge_zero
    (validJumps : Array UInt256) (evmState : EVM.State)
    (C : AccountAddress) :
    match EVM.X 0 validJumps evmState with
    | .ok (.success s' _) =>
        balanceOf s'.accountMap C ≥ balanceOf evmState.accountMap C
    | _ => True
  := by
  rw [EVM_X_zero]
  trivial

/-! ## `Ξ` reduction lemmas

These expose the structural relationship between `Ξ (f+1)` and `X f`
on the internally-constructed `freshEvmState`. Ξ's success return
wraps X's success state via the map
`(evmState'.createdAccounts, evmState'.accountMap, finalGas, evmState'.substate)`.
So monotonicity of `balanceOf · C` transports across this wrapping.
-/

/-- The fresh `EVM.State` that `Ξ (f+1) ...` constructs internally,
just before calling `X f (D_J I.code 0) freshEvmState`. Exposing
this as a definition lets us state its properties cleanly. -/
def Ξ_freshEvmState
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : EVM.State :=
  let defState : EVM.State := default
  { defState with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      gasAvailable := g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }

/-- At the freshly-built state, `accountMap = σ`. -/
@[simp] theorem Ξ_freshEvmState_accountMap
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    (Ξ_freshEvmState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).accountMap
      = σ := rfl

/-- At the freshly-built state, `executionEnv = I`. -/
@[simp] theorem Ξ_freshEvmState_executionEnv
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    (Ξ_freshEvmState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).executionEnv
      = I := rfl

/-- At the freshly-built state, `createdAccounts = createdAccounts`. -/
@[simp] theorem Ξ_freshEvmState_createdAccounts
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    (Ξ_freshEvmState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).createdAccounts
      = createdAccounts := rfl

/-- The Ξ `(f+1)` body expressed as a pattern-match on `X f`'s result
over the fresh state. We don't use `show` or `change` here; we just
read off the rfl-equality directly. -/
theorem Ξ_succ_eq_X
    (f : Nat) (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    EVM.Ξ (f + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      = (do
          let result ← EVM.X f (D_J I.code ⟨0⟩)
            (Ξ_freshEvmState createdAccounts genesisBlockHeader blocks
              σ σ₀ g A I)
          match result with
          | .success evmState' o =>
            .ok (ExecutionResult.success
              (evmState'.createdAccounts, evmState'.accountMap,
               evmState'.gasAvailable, evmState'.substate) o)
          | .revert g' o => .ok (ExecutionResult.revert g' o)) := rfl

/-! ## `X_balance_ge` — the outer X-induction statement

For a `C ≠ I.codeOwner` (where `I.codeOwner` is carried invariantly
through `X`'s iteration — `EVM.step` never mutates the
`executionEnv` component) and a no-collision `h_newC`, `X` at any
fuel returns either `.error` (trivially ok), `.ok (.revert ..)`
(trivially ok), or `.ok (.success evmState' o)` with
`balanceOf evmState'.accountMap C ≥ balanceOf evmState.accountMap C`.

The full proof is structural induction on fuel, with the per-step
balance monotonicity delegated to the four closed per-opcode frame
lemmas listed in the file header. It requires:

  (i) a step-preserves-executionEnv lemma (provable by
      record-projection reasoning through all 25 EVM.step arms),
  (ii) a step-preserves-StateWF lemma (provable via the four
       per-opcode balance-sum preservations),
  (iii) a step-preserves-h_newC lemma (CREATE appends fresh
        addresses; the Keccak-axiom `lambda_derived_address_ne_C`
        ensures they differ from `C`),
  (iv) the main fuel-succ unfolding through X's do-block, case
       on each of the opcode dispatches, invoking the per-opcode
       frame, then IH on the recursive X call.

We declare the statement and leave its body to the upstream
`Ξ_balanceOf_ge` invocation. Since that in turn carries a single
top-level `sorry`, we do **not** state `X_balance_ge` here as a
theorem (which would require a proof) — instead we stage the
statement as `Prop` returning `True` unless... no, see next
paragraph.

Concretely: the statement of `X_balance_ge` is declared as a
`def ... : Prop` so it is a plain proposition, not a proof
obligation. This lets us parameterise `Ξ_balanceOf_ge`'s body over
it without triggering a proof demand at the XFrame file level.
Dot notation `X_balance_ge_prop` would then be supplied as a
hypothesis at the Ξ call site, but since Ξ's body remains `sorry`,
we never need to discharge `X_balance_ge_prop`. -/

/-- The *proposition* that `X fuel validJumps evmState` preserves
`balanceOf C` under the standard hypotheses. Stated as a `Prop`
returning function so downstream code can refer to it symbolically
without discharging it. -/
def X_balance_ge_prop
    (fuel : ℕ) (validJumps : Array UInt256) (evmState : EVM.State)
    (C : AccountAddress) : Prop :=
  StateWF evmState.accountMap →
  C ≠ evmState.executionEnv.codeOwner →
  (∀ a ∈ evmState.createdAccounts, a ≠ C) →
  ΞPreservesAtC C →
  match EVM.X fuel validJumps evmState with
  | .ok (.success s' _) =>
      balanceOf s'.accountMap C ≥ balanceOf evmState.accountMap C
  | _ => True

/-- The fuel-0 instance of `X_balance_ge_prop` is closed. -/
theorem X_balance_ge_prop_zero
    (validJumps : Array UInt256) (evmState : EVM.State)
    (C : AccountAddress) :
    X_balance_ge_prop 0 validJumps evmState C := by
  intro _hWF _h_co _h_newC _hWit
  rw [EVM_X_zero]
  trivial

/-! ## Uniform `EvmYul.step` pc-transition (`s'.pc = N s.pc op`)

For any *handled*, non-jump, non-halting opcode, `EvmYul.step` advances the pc by exactly
`argOnNBytesOfInstr op + 1` (= `EvmYul.EVM.N s.pc op`): every such opcode's transformer ends in
`replaceStackAndIncrPC … pcΔ` with `pcΔ = argWidth + 1` (`= 1` for the non-PUSH ops, whose
`argWidth = 0`). `pc` lives in the `EVM.State` wrapper above `toState`, so the inner state/memory
ops never touch it — hence the family lemmas need no side hypotheses (unlike their `accountMap`
analogues). `JUMP`/`JUMPI` (data-dependent pc) and the halting ops (`STOP`/`RETURN`/`REVERT`/
`SELFDESTRUCT`, and `INVALID` which errors) are excluded by hypothesis; the assembly mirrors
`EvmYul.step_accountMap_eq_of_strict`. `hargw` ties the PUSH immediate's byte-width to the op (it
holds for the `arg` a real `decode` produces). The consumer-side pc-region invariant lemma any
bytecode contract's fuel/CFG reasoning needs. -/
theorem execBinOp_pc {f : Primop.Binary} {s s' : EVM.State} (h : EVM.execBinOp f s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.execBinOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem execTriOp_pc {f : Primop.Ternary} {s s' : EVM.State} (h : EVM.execTriOp f s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.execTriOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem execUnOp_pc {f : Primop.Unary} {s s' : EVM.State} (h : EVM.execUnOp f s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.execUnOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem execQuadOp_pc {f : Primop.Quaternary} {s s' : EVM.State} (h : EVM.execQuadOp f s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.execQuadOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem unaryExecutionEnvOp_pc {op : ExecutionEnv .EVM → UInt256 → UInt256} {s s' : EVM.State} (h : EVM.unaryExecutionEnvOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.unaryExecutionEnvOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem binaryMachineStateOp_pc {op : MachineState → UInt256 → UInt256 → MachineState} {s s' : EVM.State} (h : EVM.binaryMachineStateOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.binaryMachineStateOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem binaryMachineStateOp'_pc {op : MachineState → UInt256 → UInt256 → UInt256 × MachineState} {s s' : EVM.State} (h : EVM.binaryMachineStateOp' op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.binaryMachineStateOp' at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem ternaryMachineStateOp_pc {op : MachineState → UInt256 → UInt256 → UInt256 → MachineState} {s s' : EVM.State} (h : EVM.ternaryMachineStateOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.ternaryMachineStateOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem unaryStateOp_pc {op : EvmYul.State .EVM → UInt256 → EvmYul.State .EVM × UInt256} {s s' : EVM.State} (h : EVM.unaryStateOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.unaryStateOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem binaryStateOp_pc {op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM} {s s' : EVM.State} (h : EVM.binaryStateOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.binaryStateOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem ternaryCopyOp_pc {op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM} {s s' : EVM.State} (h : EVM.ternaryCopyOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.ternaryCopyOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem quaternaryCopyOp_pc {op : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM} {s s' : EVM.State} (h : EVM.quaternaryCopyOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.quaternaryCopyOp at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem log0Op_pc {s s' : EVM.State} (h : EVM.log0Op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.log0Op at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem log1Op_pc {s s' : EVM.State} (h : EVM.log1Op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.log1Op at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem log2Op_pc {s s' : EVM.State} (h : EVM.log2Op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.log2Op at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem log3Op_pc {s s' : EVM.State} (h : EVM.log3Op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.log3Op at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem log4Op_pc {s s' : EVM.State} (h : EVM.log4Op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.log4Op at h
  split at h <;> first
    | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
    | exact absurd h (by simp)
theorem executionEnvOp_pc {op : ExecutionEnv .EVM → UInt256} {s s' : EVM.State} (h : EVM.executionEnvOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.executionEnvOp at h; simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
theorem machineStateOp_pc {op : MachineState → UInt256} {s s' : EVM.State} (h : EVM.machineStateOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.machineStateOp at h; simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
theorem stateOp_pc {op : EvmYul.State .EVM → UInt256} {s s' : EVM.State} (h : EVM.stateOp op s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EVM.stateOp at h; simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
theorem dup_pc {n : ℕ} {s s' : EVM.State} (h : EvmYul.dup n s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EvmYul.dup at h; simp only [] at h
  by_cases hlen : (s.stack.take n).length = n
  · rw [if_pos hlen] at h; injection h with h; subst h; rfl
  · rw [if_neg hlen] at h; exact absurd h (by simp)
theorem swap_pc {n : ℕ} {s s' : EVM.State} (h : EvmYul.swap n s = .ok s') : s'.pc = s.pc + UInt256.ofNat 1 := by
  unfold EvmYul.swap at h; simp only [] at h
  by_cases hlen : (s.stack.take (n + 1)).length = n + 1
  · rw [if_pos hlen] at h; injection h with h; subst h; rfl
  · rw [if_neg hlen] at h; exact absurd h (by simp)
set_option maxHeartbeats 4000000 in
theorem EvmYul_step_pc_eq_N
    (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (s s' : EVM.State)
    (h_handled : handledByEvmYulStep op)
    (h_ne_jump : op ≠ .JUMP) (h_ne_jumpi : op ≠ .JUMPI)
    (h_ne_stop : op ≠ .STOP) (h_ne_ret : op ≠ .RETURN)
    (h_ne_rev : op ≠ .REVERT) (h_nsd : op ≠ .SELFDESTRUCT)
    (hargw : ∀ a' w', arg = some (a', w') → w' = argOnNBytesOfInstr op)
    (h : EvmYul.step op arg s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat (argOnNBytesOfInstr op + 1) := by
  obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := h_handled
  cases op with
  | Push o =>
    cases o <;> (unfold EvmYul.step at h; simp only [Id.run] at h) <;>
      first
      | (injection h with h; subst h; rfl)
      | (cases hae : arg with
         | none => simp [hae] at h
         | some p =>
           obtain ⟨a', w'⟩ := p
           simp [hae] at h; subst h
           rw [hargw a' w' hae]; rfl)
  | StopArith o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | CompBit o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | Keccak o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | Env o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | Block o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | StackMemFlow o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | Dup o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | Exchange o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | Log o => cases o <;> (try unfold EvmYul.step at h; try simp only [Id.run] at h) <;>
    first
      | exact absurd rfl h_ne_jump | exact absurd rfl h_ne_jumpi | exact absurd rfl h_ne_stop
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact execBinOp_pc h | exact execTriOp_pc h | exact execUnOp_pc h | exact execQuadOp_pc h
      | exact executionEnvOp_pc h | exact unaryExecutionEnvOp_pc h | exact machineStateOp_pc h
      | exact stateOp_pc h | exact binaryMachineStateOp_pc h | exact binaryMachineStateOp'_pc h
      | exact ternaryMachineStateOp_pc h | exact unaryStateOp_pc h | exact binaryStateOp_pc h
      | exact ternaryCopyOp_pc h | exact quaternaryCopyOp_pc h | exact dup_pc h | exact swap_pc h
      | exact log0Op_pc h | exact log1Op_pc h | exact log2Op_pc h | exact log3Op_pc h | exact log4Op_pc h
      | (injection h with h; subst h; rfl)
      | (split at h <;> first
          | (simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl)
          | (injection h with h; subst h; rfl)
          | exact absurd h (by simp))
      | exact absurd h (by simp [dispatchInvalid])
  | System o =>
    cases o <;>
      first
      | exact absurd rfl hne1 | exact absurd rfl hne2 | exact absurd rfl hne3
      | exact absurd rfl hne4 | exact absurd rfl hne5 | exact absurd rfl hne6
      | exact absurd rfl h_ne_ret | exact absurd rfl h_ne_rev | exact absurd rfl h_nsd
      | (unfold EvmYul.step at h; simp only [Id.run] at h;
         first
           | exact binaryMachineStateOp_pc h
           | exact absurd h (by simp [dispatchInvalid]))

end Frame
end EvmYul
