import EvmYul.Frame.StepShapes

/-!
# Per-opcode machine-state (memory) shape lemmas

Companions to `StepShapes.lean` for the *memory* dimension: for each opcode a
contract's memory-tracking walk crosses, a `step_OP_shape_mem` lemma proving the
step preserves `toMachineState.memory` and `toMachineState.activeWords` (the two
fields `MLOAD`/`RETURN` read — `lookupMemory` gates on `activeWords`). The ops
that *do* touch memory get exposing forms instead: `step_MLOAD_shape_mem` (pushes
`lookupMemory`, bumps `activeWords`), `step_MSTORE_shape_mem` (the `mstore` write,
full effect), and `step_RETURN_shape_strong` (pins `H_return`, the halt output).

Same proof pattern as the `_strong` family: unfold the step dispatch, substitute,
and read the fields off the record update — every conclusion is `rfl` after
`subst`. Used by the downstream memory-threading `X` walk (a compiled getter's
`RETURN`ed bytes).
-/

namespace EvmYul.Frame

open EvmYul EvmYul.EVM

theorem step_PUSH0_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.Push .PUSH0, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  injection hStep with hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_JUMPDEST_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.JUMPDEST, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  injection hStep with hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_PUSH_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (op : Operation.POp)
    (hOpNeq : op ≠ .PUSH0)
    (v : UInt256) (n : Nat)
    (hStep : EVM.step (f' + 1) cost (some (.Push op, some (v, n))) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  cases op
  · exact absurd rfl hOpNeq
  all_goals (
    simp only [Id.run] at hStep
    injection hStep with hStep
    subst hStep
    exact ⟨rfl, rfl⟩)

theorem step_CALLVALUE_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CALLVALUE, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_CALLDATASIZE_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CALLDATASIZE, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_CALLDATALOAD_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.CALLDATALOAD, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_SLOAD_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SLOAD, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_ISZERO_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ISZERO, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_LT_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.LT, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_EQ_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.EQ, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_SHR_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SHR, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_ADD_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ADD, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_SUB_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SUB, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_POP_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.POP, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_JUMP_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.JUMP, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_JUMPI_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.JUMPI, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_DUP1_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP1, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 1 (hd :: tl) = [hd] from rfl,
             List.length_singleton, ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_DUP2_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP2, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 2 (hd1 :: hd2 :: tl) = [hd1, hd2] from rfl,
             show ([hd1, hd2] : List UInt256).length = 2 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_SWAP1_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP1, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (1 + 1) (hd1 :: hd2 :: tl) = [hd1, hd2] from rfl,
             show List.drop (1 + 1) (hd1 :: hd2 :: tl) = tl from rfl,
             show ([hd1, hd2] : List UInt256).length = 1 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_SWAP2_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP2, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (2 + 1) (hd1 :: hd2 :: hd3 :: tl) = [hd1, hd2, hd3] from rfl,
             show List.drop (2 + 1) (hd1 :: hd2 :: hd3 :: tl) = tl from rfl,
             show ([hd1, hd2, hd3] : List UInt256).length = 2 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

/-- MLOAD, memory-exposing: pushes exactly the word at the popped offset
(`MachineState.lookupMemory`), leaves `memory` untouched, and bumps
`activeWords` by the Yellow-Paper `M` accounting. -/
theorem step_MLOAD_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MLOAD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = s.toMachineState.lookupMemory hd :: tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap ∧
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords
      = UInt256.ofNat (MachineState.M s.toMachineState.activeWords.toNat hd.toNat 32) := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- MSTORE, memory-exposing: pops offset/value, writes the word
(`MachineState.mstore`), and bumps `activeWords` — the full machine-state
effect (`executionEnv`/`accountMap` preserved). -/
theorem step_MSTORE_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MSTORE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap ∧
    s'.toMachineState.memory = (s.toMachineState.mstore hd1 hd2).memory ∧
    s'.toMachineState.activeWords = (s.toMachineState.mstore hd1 hd2).activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp EVM.binaryMachineStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- RETURN strong: like `step_RETURN_shape`, additionally proves `accountMap`
preservation and pins the halt output — `H_return` is exactly the memory slice
`readWithPadding offset size` (`MachineState.evmReturn`), which the `X` loop
returns as the run's output bytes. -/
theorem step_RETURN_shape_strong
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.RETURN, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap ∧
    s'.toMachineState.H_return
      = s.toMachineState.memory.readWithPadding hd1.toNat hd2.toNat := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp EVM.binaryMachineStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Arithmetic / stack-shuffle memory-preservation shapes (Solady body walk)

The `mem` (memory + activeWords preservation) counterparts of the arithmetic value bricks and
the wider DUP/SWAP shapes, forced by walking a value-returning function's body in memory mode
(so its returned bytes can be pinned through the ABI-encode/`RETURN` epilogue). Each mirrors the
nearest neighbour above (`step_ADD_shape_mem` for the binaries, `step_ISZERO_shape_mem` for the
unary `NOT`, `step_DUP2_shape_mem` / `step_SWAP2_shape_mem` for the shuffles). -/

theorem step_MUL_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MUL, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_DIV_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DIV, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_GT_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.GT, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_SLT_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SLT, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_XOR_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.XOR, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_NOT_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.NOT, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_DUP3_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP3, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 3 (hd1 :: hd2 :: hd3 :: tl) = [hd1, hd2, hd3] from rfl,
             show ([hd1, hd2, hd3] : List UInt256).length = 3 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_DUP4_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP4, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 4 (hd1 :: hd2 :: hd3 :: hd4 :: tl) = [hd1, hd2, hd3, hd4] from rfl,
             show ([hd1, hd2, hd3, hd4] : List UInt256).length = 4 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_DUP6_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 hd5 hd6 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP6, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 6 (hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: tl)
                = [hd1, hd2, hd3, hd4, hd5, hd6] from rfl,
             show ([hd1, hd2, hd3, hd4, hd5, hd6] : List UInt256).length = 6 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_SWAP3_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP3, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (3 + 1) (hd1 :: hd2 :: hd3 :: hd4 :: tl) = [hd1, hd2, hd3, hd4] from rfl,
             show List.drop (3 + 1) (hd1 :: hd2 :: hd3 :: hd4 :: tl) = tl from rfl,
             show ([hd1, hd2, hd3, hd4] : List UInt256).length = 3 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

theorem step_SWAP4_shape_mem
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 hd5 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP4, arg)) s = .ok s') :
    s'.toMachineState.memory = s.toMachineState.memory ∧
    s'.toMachineState.activeWords = s.toMachineState.activeWords := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (4 + 1) (hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: tl)
               = [hd1, hd2, hd3, hd4, hd5] from rfl,
             show List.drop (4 + 1) (hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: tl) = tl from rfl,
             show ([hd1, hd2, hd3, hd4, hd5] : List UInt256).length = 4 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl⟩

end EvmYul.Frame
