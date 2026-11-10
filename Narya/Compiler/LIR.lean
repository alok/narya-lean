/-
  Narya.Compiler.LIR — Low-Level Stack-Frame & Accumulator IR with Verified Lowering

  Stage 3 of Leonardo de Moura's SViL Nov 2026 "New Code Generator" architecture:
    `MIR` ──(`LIR.lowerFromMIR`)──▶ `List LIRInstr`

  Models a flat register-accumulator + 16-byte-aligned stack-slot machine (`acc` = `x0`,
  `stack` = hardware `sp` slots `[sp, #16*k]`), tracks exact operational instruction
  ticks via `TimeM`, and carries a complete zero-`sorry` compiler correctness proof
  (`LIR.exec_lowerFromMIR_eq`) for arbitrary nested `letAlloc`, `binOp`, and `joinIfZero`!
-/
import Narya.Compiler.TimeM
import Narya.Compiler.MIR

namespace Narya.Compiler

/-- Low-level register/stack-slot machine instructions (`LIRInstr`).
    Maps 1-to-1 onto `arm64-apple-darwin` instructions in `Narya.Compiler.Arm64`! -/
inductive LIRInstr where
  /-- Load 64-bit constant into accumulator `x0` (`movz`/`movk`). -/
  | loadImm (val : UInt64)
  /-- Copy ABI parameter `idx` (`x2`/`x3` saved from `x0`/`x1`) into `x0`. -/
  | loadParam (idx : Fin 2)
  /-- Load 64-bit value from 16-byte stack slot `[sp, #(16 * slotIdx)]` into `x0`. -/
  | loadSlot (slotIdx : Nat)
  /-- Push `x0` onto 16-byte aligned stack (`str x0, [sp, #-16]!`). -/
  | pushAcc
  /-- Pop and discard top 16-byte stack slot (`add sp, sp, #16`). -/
  | popDrop
  /-- Pop saved LHS into scratch `x1` (`ldr x1, [sp], #16`) and compute `x0 := op x1 x0`. -/
  | popBinOp (op : BinOp64)
  /-- Conditional zero branch (`cbz x0, zeroLabel`). -/
  | condZero (zeroBranch : List LIRInstr) (nonZeroBranch : List LIRInstr)
  deriving Repr, Inhabited

/-- Machine state of `LIR`: accumulator register `acc` (`x0`) and 64-bit stack slots `stack`. -/
structure LIRState where
  acc : UInt64 := 0
  stack : List UInt64 := []
  deriving DecidableEq, Repr, Inhabited

namespace LIR

mutual
/-- Execute a single `LIRInstr` (and nested `condZero` blocks) on `st`. -/
def step (p₀ p₁ : UInt64) (st : LIRState) : LIRInstr → LIRState
  | .loadImm v => { st with acc := v }
  | .loadParam i => { st with acc := if i.val == 0 then p₀ else p₁ }
  | .loadSlot slot => { st with acc := st.stack[slot]?.getD 0 }
  | .pushAcc => { st with stack := st.acc :: st.stack }
  | .popDrop => { st with stack := st.stack.drop 1 }
  | .popBinOp op =>
    match st.stack with
    | lhs :: rest => { acc := op.eval lhs st.acc, stack := rest }
    | [] => { st with acc := op.eval 0 st.acc }
  | .condZero zBr nzBr =>
    if st.acc == 0 then exec p₀ p₁ zBr st
    else exec p₀ p₁ nzBr st

/-- Execute a sequence of `LIRInstr`s from left to right. -/
def exec (p₀ p₁ : UInt64) : List LIRInstr → LIRState → LIRState
  | [], st => st
  | i :: is, st => exec p₀ p₁ is (step p₀ p₁ st i)
end

mutual
/-- Timed `LIR` execution in `TimeM` charging 1 tick per executed instruction! -/
def stepTimed (p₀ p₁ : UInt64) (st : LIRState) : LIRInstr → TimeM LIRState
  | .loadImm v => TimeM.tick 1 { st with acc := v }
  | .loadParam i => TimeM.tick 1 { st with acc := if i.val == 0 then p₀ else p₁ }
  | .loadSlot slot => TimeM.tick 1 { st with acc := st.stack[slot]?.getD 0 }
  | .pushAcc => TimeM.tick 1 { st with stack := st.acc :: st.stack }
  | .popDrop => TimeM.tick 1 { st with stack := st.stack.drop 1 }
  | .popBinOp op =>
    match st.stack with
    | lhs :: rest => TimeM.tick 1 { acc := op.eval lhs st.acc, stack := rest }
    | [] => TimeM.tick 1 { st with acc := op.eval 0 st.acc }
  | .condZero zBr nzBr => do
    let st' ← TimeM.tick 1 st
    if st'.acc == 0 then execTimed p₀ p₁ zBr st'
    else execTimed p₀ p₁ nzBr st'

def execTimed (p₀ p₁ : UInt64) : List LIRInstr → LIRState → TimeM LIRState
  | [], st => pure st
  | i :: is, st => do
    let st' ← stepTimed p₀ p₁ st i
    execTimed p₀ p₁ is st'
end

/-- Sequential composition law for `LIR.exec`. -/
@[simp]
theorem exec_append (p₀ p₁ : UInt64) (c₁ c₂ : List LIRInstr) (st : LIRState) :
    exec p₀ p₁ (c₁ ++ c₂) st = exec p₀ p₁ c₂ (exec p₀ p₁ c₁ st) := by
  induction c₁ generalizing st with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.cons_append, exec]
    exact ih (step p₀ p₁ st i)

/-! ### Verified `MIR → LIR` Compiler with Exact Stack-Height Indexing -/

/-- Compile an `MIR` term given:
    - `varHeights`: the stack depth `H` at the moment each lexical variable was pushed
    - `curH`: current stack depth (`st.stack.length = curH`) -/
def compileAux (varHeights : List Nat) (curH : Nat) : MIR → List LIRInstr
  | .lit v => [.loadImm v]
  | .param i => [.loadParam i]
  | .var ix =>
    match varHeights[ix]? with
    | some h => [.loadSlot (curH - 1 - h)]
    | none => [.loadImm 0]
  | .binOp op lhs rhs =>
    compileAux varHeights curH lhs ++
    [.pushAcc] ++
    compileAux varHeights (curH + 1) rhs ++
    [.popBinOp op]
  | .letAlloc _ val body =>
    compileAux varHeights curH val ++
    [.pushAcc] ++
    compileAux (curH :: varHeights) (curH + 1) body ++
    [.popDrop]
  | .joinIfZero cond zBr nzBr =>
    compileAux varHeights curH cond ++
    [.condZero (compileAux varHeights curH zBr) (compileAux varHeights curH nzBr)]

/-- Lower a closed (or open) `MIR` expression to `List LIRInstr`. -/
def lowerFromMIR (m : MIR) : List LIRInstr :=
  compileAux [] 0 m

/-! ### Stack-Environment Simulation Invariant & Correctness Proof (`zero sorry`) -/

/-- Relation stating that hardware `stack` of height `curH` faithfully realizes lexical `env`
    at recorded push heights `varHeights`. -/
def EnvMatchesStack (env : List UInt64) (varHeights : List Nat) (curH : Nat)
    (stack : List UInt64) : Prop :=
  stack.length = curH ∧
  (∀ (ix : Nat),
    match env[ix]?, varHeights[ix]? with
    | some v, some h => h < curH ∧ stack[curH - 1 - h]? = some v
    | none, none => True
    | _, _ => False)

theorem envMatches_empty : EnvMatchesStack [] [] 0 [] := by
  refine ⟨rfl, fun ix => ?_⟩
  simp

/-- Pushing a temporary operand `tmp` onto `stack` preserves all existing lexical variable lookups! -/
theorem envMatches_push_temp {env : List UInt64} {varHeights : List Nat} {curH : Nat}
    {stack : List UInt64} (tmp : UInt64)
    (hMatch : EnvMatchesStack env varHeights curH stack) :
    EnvMatchesStack env varHeights (curH + 1) (tmp :: stack) := by
  refine ⟨by simp [hMatch.1], fun ix => ?_⟩
  have hIx := hMatch.2 ix
  cases hE : env[ix]? <;> cases hV : varHeights[ix]? <;> simp only [hE, hV] at hIx ⊢
  rename_i v h
  rcases hIx with ⟨hLt, hLookup⟩
  refine ⟨by omega, ?_⟩
  have hIdxEq : curH + 1 - 1 - h = (curH - 1 - h) + 1 := by omega
  rw [hIdxEq]
  simpa using hLookup

/-- Pushing a new `let`-bound variable `v` onto `stack` extends `EnvMatchesStack` to `v :: env`! -/
theorem envMatches_push_let {env : List UInt64} {varHeights : List Nat} {curH : Nat}
    {stack : List UInt64} (v : UInt64)
    (hMatch : EnvMatchesStack env varHeights curH stack) :
    EnvMatchesStack (v :: env) (curH :: varHeights) (curH + 1) (v :: stack) := by
  refine ⟨by simp [hMatch.1], fun ix => ?_⟩
  cases ix with
  | zero =>
    simp only [List.getElem?_cons_zero]
    refine ⟨by omega, ?_⟩
    have hZ : curH + 1 - 1 - curH = 0 := by omega
    rw [hZ]
    rfl
  | succ ix' =>
    simp only [List.getElem?_cons_succ]
    exact (envMatches_push_temp v hMatch).2 ix'

/-- **Main `MIR → LIR` Simulation Theorem (`exec_compileAux`)**:
    Executing `compileAux varHeights curH m` from any state `st` satisfying `EnvMatchesStack`:
    1. Computes `acc = MIR.eval p₀ p₁ env m`
    2. Restores `st.stack` **completely unchanged**! -/
theorem exec_compileAux (p₀ p₁ : UInt64) (m : MIR) :
    ∀ (env : List UInt64) (varHeights : List Nat) (curH : Nat) (st : LIRState),
      EnvMatchesStack env varHeights curH st.stack →
      exec p₀ p₁ (compileAux varHeights curH m) st =
        { acc := MIR.eval p₀ p₁ env m, stack := st.stack } := by
  induction m with
  | lit v =>
    intro env vh curH st _
    rfl
  | param i =>
    intro env vh curH st _
    rfl
  | var ix =>
    intro env vh curH st hMatch
    have hIx := hMatch.2 ix
    simp only [compileAux, MIR.eval]
    cases hE : env[ix]? <;> cases hV : vh[ix]? <;> simp only [hE, hV] at hIx ⊢
    · rfl
    · rcases hIx with ⟨_, hSlot⟩
      simp [exec, step, hSlot]
  | binOp op l r ihl ihr =>
    intro env vh curH st hMatch
    simp only [compileAux, exec_append]
    rw [ihl env vh curH st hMatch]
    simp only [exec, step]
    have hPush := envMatches_push_temp (MIR.eval p₀ p₁ env l) hMatch
    rw [ihr env vh (curH + 1) { acc := MIR.eval p₀ p₁ env l, stack := MIR.eval p₀ p₁ env l :: st.stack } hPush]
    rfl
  | letAlloc own val body ihv ihb =>
    intro env vh curH st hMatch
    simp only [compileAux, exec_append]
    rw [ihv env vh curH st hMatch]
    simp only [exec, step]
    let v := MIR.eval p₀ p₁ env val
    have hLet := envMatches_push_let v hMatch
    rw [ihb (v :: env) (curH :: vh) (curH + 1) { acc := v, stack := v :: st.stack } hLet]
    rfl
  | joinIfZero cond zBr nzBr ihc ihz ihnz =>
    intro env vh curH st hMatch
    simp only [compileAux, exec_append]
    rw [ihc env vh curH st hMatch]
    simp only [exec, step, MIR.eval]
    split
    · exact ihz env vh curH { acc := MIR.eval p₀ p₁ env cond, stack := st.stack } hMatch
    · exact ihnz env vh curH { acc := MIR.eval p₀ p₁ env cond, stack := st.stack } hMatch

/-- **Theorem D3.3 (`exec_lowerFromMIR_eq`)**: Closed `LIR` execution produces the exact
    64-bit return value of `MIR.eval` with a clean empty stack! -/
@[simp]
theorem exec_lowerFromMIR_eq (p₀ p₁ : UInt64) (m : MIR) :
    exec p₀ p₁ (lowerFromMIR m) {} = { acc := MIR.eval p₀ p₁ [] m, stack := [] } := by
  exact exec_compileAux p₀ p₁ m [] [] 0 {} envMatches_empty

end LIR

end Narya.Compiler
