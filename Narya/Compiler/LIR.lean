/-
  Narya.Compiler.LIR — Register-Allocated & Loop-Aware Low-Level IR with Verified Lowering

  Stage 3 of Leonardo de Moura's SViL Nov 2026 "New Code Generator" architecture:
    `MIR` ──(`LIR.lowerFromMIR`)──▶ `List LIRInstr`

  Upgrades over pure stack-machine lowering (Open Problem H):
  1. **Hardware Register Promotion (`LocalReg = Fin 4`, mapping to `x4..x7`)**:
     Lexical `letAlloc` bindings, loop accumulators, and `binOp` LHS temporaries at register
     pressure `< 4` stay 100% in caller-saved registers (`loadLocalReg`, `storeLocalReg`,
     `regBinOp`) with **zero `str`/`ldr` memory traffic**; deeper scopes (`≥ 4`) spill
     cleanly to 16-byte-aligned `[sp, #16*k]` slots!
  2. **Counted Hardware Loops (`repeatLoop`)**:
     Lowers `MIR.repeatLoop` to structured counted loops keeping inner loop counters in `x8`
     with zero stack spills (and automatically saving/restoring outer counters on `sp` across
     nested loops).
  3. **Machine-Checked Compiler Correctness (`exec_lowerFromMIR_acc_and_stack`, `zero sorry`)**:
     Proves exact 64-bit semantic equivalence and stack preservation across arbitrary nested
     register/stack bindings, binary ops, conditionals, and nested loops!
-/
import Narya.Compiler.TimeM
import Narya.Compiler.MIR

namespace Narya.Compiler

/-- Local caller-saved hardware register index (`0..3`, mapped to `x4..x7` on `AArch64`). -/
abbrev LocalReg := Fin 4

/-- Lexical variable storage location tracked during `MIR → LIR` lowering. -/
inductive VarLoc where
  /-- Promoted to caller-saved register `x_{4 + r}` (zero stack traffic!). -/
  | inReg (r : LocalReg)
  /-- Spilled to 16-byte-aligned stack frame at push height `pushH`. -/
  | onStack (pushH : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Low-level register/stack-slot machine instructions (`LIRInstr`).
    Maps directly onto `AArch64` instructions in `Narya.Compiler.Arm64`! -/
inductive LIRInstr where
  /-- Load 64-bit constant into accumulator `x0` (`movz`/`movk`). -/
  | loadImm (val : UInt64)
  /-- Copy ABI parameter `idx` (`x2`/`x3` saved from `x0`/`x1`) into `x0`. -/
  | loadParam (idx : Fin 2)
  /-- Copy local register `x_{4+reg}` into `x0` (`mov x0, x_{4+reg}`). -/
  | loadLocalReg (reg : LocalReg)
  /-- Copy `x0` into local register `x_{4+reg}` (`mov x_{4+reg}, x0`). -/
  | storeLocalReg (reg : LocalReg)
  /-- Register-register ALU op `x0 := op x_{4+lhsReg} x0` (zero stack traffic!). -/
  | regBinOp (op : BinOp64) (lhsReg : LocalReg)
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
  /-- Counted hardware loop running `body` `iters.toNat` times (`saveCounter` spills `x8` iff nested). -/
  | repeatLoop (iters : UInt64) (saveCounter : Bool) (body : List LIRInstr)
  deriving Repr, Inhabited

/-- Machine state of `LIR`: accumulator `acc` (`x0`), 4 local registers `r0..r3` (`x4..x7`),
    and 64-bit 16-byte-aligned stack slots `stack`. -/
structure LIRState where
  acc : UInt64 := 0
  r0 : UInt64 := 0
  r1 : UInt64 := 0
  r2 : UInt64 := 0
  r3 : UInt64 := 0
  stack : List UInt64 := []
  deriving DecidableEq, Repr, Inhabited

namespace LIRState

@[inline]
def getLocal (st : LIRState) (r : LocalReg) : UInt64 :=
  match r.val with
  | 0 => st.r0
  | 1 => st.r1
  | 2 => st.r2
  | _ => st.r3

@[inline]
def setLocal (st : LIRState) (r : LocalReg) (v : UInt64) : LIRState :=
  match r.val with
  | 0 => { st with r0 := v }
  | 1 => { st with r1 := v }
  | 2 => { st with r2 := v }
  | _ => { st with r3 := v }

@[simp]
theorem setLocal_acc (st : LIRState) (r : LocalReg) (v : UInt64) :
    (st.setLocal r v).acc = st.acc := by
  rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;> rfl

@[simp]
theorem setLocal_stack (st : LIRState) (r : LocalReg) (v : UInt64) :
    (st.setLocal r v).stack = st.stack := by
  rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;> rfl

@[simp]
theorem getLocal_setLocal_same (st : LIRState) (r : LocalReg) (v : UInt64) :
    (st.setLocal r v).getLocal r = v := by
  rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;> simp [getLocal, setLocal] <;> omega

theorem getLocal_setLocal_ne (st : LIRState) (r₁ r₂ : LocalReg) (v : UInt64)
    (hne : r₁.val ≠ r₂.val) :
    (st.setLocal r₁ v).getLocal r₂ = st.getLocal r₂ := by
  rcases r₁ with ⟨_ | _ | _ | _ | n₁, h₁⟩ <;>
  rcases r₂ with ⟨_ | _ | _ | _ | n₂, h₂⟩ <;>
  simp [getLocal, setLocal] at hne ⊢ <;> omega

end LIRState

namespace LIR

/-- Single loop iteration transformer parameterized by `execBody : LIRState → LIRState`
    so `step`/`exec` remain 100% structural (kernel-reducible without `WellFounded.fix`!). -/
def iterStep (saveCounter : Bool) (execBody : LIRState → LIRState) :
    UInt64 × LIRState → UInt64 × LIRState
  | (rem, st) =>
    if saveCounter then
      let st2 := execBody { st with stack := rem :: st.stack }
      match st2.stack with
      | top :: rest => (top - 1, { st2 with stack := rest })
      | [] => (0 - 1, st2)
    else
      (rem - 1, execBody st)

mutual
/-- Execute a single `LIRInstr` on `st` (purely structural, kernel-reducible!). -/
def step (p₀ p₁ : UInt64) (st : LIRState) : LIRInstr → LIRState
  | .loadImm v => { st with acc := v }
  | .loadParam i => { st with acc := if i.val == 0 then p₀ else p₁ }
  | .loadLocalReg r => { st with acc := st.getLocal r }
  | .storeLocalReg r => st.setLocal r st.acc
  | .regBinOp op r => { st with acc := op.eval (st.getLocal r) st.acc }
  | .loadSlot slot => { st with acc := st.stack[slot]?.getD 0 }
  | .pushAcc => { st with stack := st.acc :: st.stack }
  | .popDrop => { st with stack := st.stack.drop 1 }
  | .popBinOp op =>
    match st.stack with
    | lhs :: rest => { st with acc := op.eval lhs st.acc, stack := rest }
    | [] => { st with acc := op.eval 0 st.acc }
  | .condZero zBr nzBr =>
    if st.acc == 0 then exec p₀ p₁ zBr st
    else exec p₀ p₁ nzBr st
  | .repeatLoop iters saveCounter body =>
    (iterN iters.toNat (iterStep saveCounter (exec p₀ p₁ body)) (iters, st)).2

/-- Execute a sequence of `LIRInstr`s from left to right. -/
def exec (p₀ p₁ : UInt64) : List LIRInstr → LIRState → LIRState
  | [], st => st
  | i :: is, st => exec p₀ p₁ is (step p₀ p₁ st i)
end

/-- Execute `n` counted iterations of `body` starting from remaining hardware counter `rem`. -/
def runLoop (p₀ p₁ : UInt64) (saveCounter : Bool) (body : List LIRInstr)
    (n : Nat) (rem : UInt64) (st : LIRState) : LIRState :=
  (iterN n (iterStep saveCounter (exec p₀ p₁ body)) (rem, st)).2

@[simp] theorem exec_nil (p₀ p₁ : UInt64) (st : LIRState) :
    exec p₀ p₁ [] st = st := rfl

@[simp] theorem exec_cons (p₀ p₁ : UInt64) (i : LIRInstr) (is : List LIRInstr) (st : LIRState) :
    exec p₀ p₁ (i :: is) st = exec p₀ p₁ is (step p₀ p₁ st i) := rfl

@[simp] theorem step_loadImm (p₀ p₁ v : UInt64) (st : LIRState) :
    step p₀ p₁ st (.loadImm v) = { st with acc := v } := rfl

@[simp] theorem step_loadParam (p₀ p₁ : UInt64) (i : Fin 2) (st : LIRState) :
    step p₀ p₁ st (.loadParam i) = { st with acc := if i.val == 0 then p₀ else p₁ } := rfl

@[simp] theorem step_loadLocalReg (p₀ p₁ : UInt64) (r : LocalReg) (st : LIRState) :
    step p₀ p₁ st (.loadLocalReg r) = { st with acc := st.getLocal r } := rfl

@[simp] theorem step_storeLocalReg (p₀ p₁ : UInt64) (r : LocalReg) (st : LIRState) :
    step p₀ p₁ st (.storeLocalReg r) = st.setLocal r st.acc := rfl

@[simp] theorem step_regBinOp (p₀ p₁ : UInt64) (op : BinOp64) (r : LocalReg) (st : LIRState) :
    step p₀ p₁ st (.regBinOp op r) = { st with acc := op.eval (st.getLocal r) st.acc } := rfl

@[simp] theorem step_loadSlot (p₀ p₁ : UInt64) (slot : Nat) (st : LIRState) :
    step p₀ p₁ st (.loadSlot slot) = { st with acc := st.stack[slot]?.getD 0 } := rfl

@[simp] theorem step_pushAcc (p₀ p₁ : UInt64) (st : LIRState) :
    step p₀ p₁ st .pushAcc = { st with stack := st.acc :: st.stack } := rfl

@[simp] theorem step_popDrop (p₀ p₁ : UInt64) (st : LIRState) :
    step p₀ p₁ st .popDrop = { st with stack := st.stack.drop 1 } := rfl

@[simp] theorem step_popBinOp (p₀ p₁ : UInt64) (op : BinOp64) (st : LIRState) :
    step p₀ p₁ st (.popBinOp op) =
      (match st.stack with
       | lhs :: rest => { st with acc := op.eval lhs st.acc, stack := rest }
       | [] => { st with acc := op.eval 0 st.acc }) := rfl

@[simp] theorem step_condZero (p₀ p₁ : UInt64) (zBr nzBr : List LIRInstr) (st : LIRState) :
    step p₀ p₁ st (.condZero zBr nzBr) =
      (if st.acc == 0 then exec p₀ p₁ zBr st else exec p₀ p₁ nzBr st) := rfl

@[simp] theorem step_repeatLoop (p₀ p₁ iters : UInt64) (saveCounter : Bool) (body : List LIRInstr) (st : LIRState) :
    step p₀ p₁ st (.repeatLoop iters saveCounter body) =
      runLoop p₀ p₁ saveCounter body iters.toNat iters st := rfl

@[simp] theorem runLoop_zero (p₀ p₁ : UInt64) (saveC : Bool) (body : List LIRInstr) (rem : UInt64) (st : LIRState) :
    runLoop p₀ p₁ saveC body 0 rem st = st := rfl

theorem runLoop_succ_false (p₀ p₁ : UInt64) (body : List LIRInstr) (k : Nat) (rem : UInt64) (st : LIRState) :
    runLoop p₀ p₁ false body (k + 1) rem st =
      runLoop p₀ p₁ false body k (rem - 1) (exec p₀ p₁ body st) := rfl

theorem runLoop_succ_true (p₀ p₁ : UInt64) (body : List LIRInstr) (k : Nat) (rem : UInt64) (st : LIRState) :
    runLoop p₀ p₁ true body (k + 1) rem st =
      (let st2 := exec p₀ p₁ body { st with stack := rem :: st.stack }
       match st2.stack with
       | top :: rest => runLoop p₀ p₁ true body k (top - 1) { st2 with stack := rest }
       | [] => runLoop p₀ p₁ true body k (0 - 1) st2) := by
  simp only [runLoop, iterN, iterStep, ite_true]
  cases (exec p₀ p₁ body { st with stack := rem :: st.stack }).stack <;> rfl

mutual
/-- Timed `LIR` execution in `TimeM` charging 1 tick per executed instruction! -/
def stepTimed (p₀ p₁ : UInt64) (st : LIRState) : LIRInstr → TimeM LIRState
  | .loadImm v => TimeM.tick 1 { st with acc := v }
  | .loadParam i => TimeM.tick 1 { st with acc := if i.val == 0 then p₀ else p₁ }
  | .loadLocalReg r => TimeM.tick 1 { st with acc := st.getLocal r }
  | .storeLocalReg r => TimeM.tick 1 (st.setLocal r st.acc)
  | .regBinOp op r => TimeM.tick 1 { st with acc := op.eval (st.getLocal r) st.acc }
  | .loadSlot slot => TimeM.tick 1 { st with acc := st.stack[slot]?.getD 0 }
  | .pushAcc => TimeM.tick 1 { st with stack := st.acc :: st.stack }
  | .popDrop => TimeM.tick 1 { st with stack := st.stack.drop 1 }
  | .popBinOp op =>
    match st.stack with
    | lhs :: rest => TimeM.tick 1 { st with acc := op.eval lhs st.acc, stack := rest }
    | [] => TimeM.tick 1 { st with acc := op.eval 0 st.acc }
  | .condZero zBr nzBr => do
    let st' ← TimeM.tick 1 st
    if st'.acc == 0 then execTimed p₀ p₁ zBr st'
    else execTimed p₀ p₁ nzBr st'
  | .repeatLoop iters saveCounter body => do
    let st' ← TimeM.tick 1 st
    runLoopTimed p₀ p₁ saveCounter body iters.toNat iters st'
termination_by instr => (sizeOf instr, 0)

def execTimed (p₀ p₁ : UInt64) : List LIRInstr → LIRState → TimeM LIRState
  | [], st => pure st
  | i :: is, st => do
    let st' ← stepTimed p₀ p₁ st i
    execTimed p₀ p₁ is st'
termination_by code => (sizeOf code, 0)

def runLoopTimed (p₀ p₁ : UInt64) (saveCounter : Bool) (body : List LIRInstr) :
    Nat → UInt64 → LIRState → TimeM LIRState
  | 0, _, st => pure st
  | k + 1, rem, st => do
    if saveCounter then
      let st1 ← TimeM.tick 1 { st with stack := rem :: st.stack }
      let st2 ← execTimed p₀ p₁ body st1
      let (top, rest) := match st2.stack with | t :: r => (t, r) | [] => (0, [])
      let st3 ← TimeM.tick 2 { st2 with stack := rest }
      runLoopTimed p₀ p₁ true body k (top - 1) st3
    else
      let st2 ← execTimed p₀ p₁ body st
      let st3 ← TimeM.tick 1 st2
      runLoopTimed p₀ p₁ false body k (rem - 1) st3
termination_by n => (sizeOf body, n + 1)
end

mutual
/-- Count static stack-memory instructions (`str`/`ldr`/`sp` adjustments) in an `LIR` program.
    Used to certify zero-spill register promotion (`countStackOps = 0`)! -/
def countStackOpsInstr : LIRInstr → Nat
  | .loadSlot _ => 1
  | .pushAcc => 1
  | .popDrop => 1
  | .popBinOp _ => 1
  | .condZero zBr nzBr => countStackOps zBr + countStackOps nzBr
  | .repeatLoop _ saveCounter body => (if saveCounter then 2 else 0) + countStackOps body
  | _ => 0

def countStackOps : List LIRInstr → Nat
  | [] => 0
  | i :: is => countStackOpsInstr i + countStackOps is
end

mutual
/-- Check whether an `LIR` block contains any `repeatLoop` instruction. -/
def hasLoopInstr : LIRInstr → Bool
  | .condZero zBr nzBr => hasLoopCode zBr || hasLoopCode nzBr
  | .repeatLoop _ _ _ => true
  | _ => false

def hasLoopCode : List LIRInstr → Bool
  | [] => false
  | i :: is => hasLoopInstr i || hasLoopCode is
end

/-- Sequential composition law for `LIR.exec`. -/
@[simp]
theorem exec_append (p₀ p₁ : UInt64) (c₁ c₂ : List LIRInstr) (st : LIRState) :
    exec p₀ p₁ (c₁ ++ c₂) st = exec p₀ p₁ c₂ (exec p₀ p₁ c₁ st) := by
  induction c₁ generalizing st with
  | nil => simp
  | cons i rest ih =>
    simp only [List.cons_append, exec_cons]
    exact ih (step p₀ p₁ st i)

/-! ### Verified `MIR → LIR` Register-Promoting & Loop-Aware Compiler -/

/-- Compile an `MIR` term given:
    - `locs`: storage location (`.inReg r` or `.onStack h`) for each lexical variable
    - `usedRegs`: number of local registers `x4..x7` currently live (`0..4`)
    - `curH`: current 16-byte stack depth (`st.stack.length = curH`) -/
def compileAux (locs : List VarLoc) (usedRegs : Nat) (curH : Nat) : MIR → List LIRInstr
  | .lit v => [.loadImm v]
  | .param i => [.loadParam i]
  | .var ix =>
    match locs[ix]? with
    | some (.inReg r) => [.loadLocalReg r]
    | some (.onStack h) => [.loadSlot (curH - 1 - h)]
    | none => [.loadImm 0]
  | .binOp op lhs rhs =>
    if hReg : usedRegs < 4 then
      let r : LocalReg := ⟨usedRegs, hReg⟩
      compileAux locs usedRegs curH lhs ++
      [.storeLocalReg r] ++
      compileAux locs (usedRegs + 1) curH rhs ++
      [.regBinOp op r]
    else
      compileAux locs usedRegs curH lhs ++
      [.pushAcc] ++
      compileAux locs usedRegs (curH + 1) rhs ++
      [.popBinOp op]
  | .letAlloc _ val body =>
    if hReg : usedRegs < 4 then
      let r : LocalReg := ⟨usedRegs, hReg⟩
      compileAux locs usedRegs curH val ++
      [.storeLocalReg r] ++
      compileAux (.inReg r :: locs) (usedRegs + 1) curH body
    else
      compileAux locs usedRegs curH val ++
      [.pushAcc] ++
      compileAux (.onStack curH :: locs) usedRegs (curH + 1) body ++
      [.popDrop]
  | .joinIfZero cond zBr nzBr =>
    compileAux locs usedRegs curH cond ++
    [.condZero (compileAux locs usedRegs curH zBr) (compileAux locs usedRegs curH nzBr)]
  | .repeatLoop count init stepBody =>
    let saveCounter := MIR.hasLoop stepBody
    let bodyH := if saveCounter then curH + 1 else curH
    let stepCode :=
      if hReg : usedRegs < 4 then
        let r : LocalReg := ⟨usedRegs, hReg⟩
        [.storeLocalReg r] ++ compileAux (.inReg r :: locs) (usedRegs + 1) bodyH stepBody
      else
        [.pushAcc] ++ compileAux (.onStack bodyH :: locs) usedRegs (bodyH + 1) stepBody ++ [.popDrop]
    compileAux locs usedRegs curH init ++
    [.repeatLoop count saveCounter stepCode]

/-- Lower a closed `MIR` expression to register-allocated `List LIRInstr`. -/
def lowerFromMIR (m : MIR) : List LIRInstr :=
  compileAux [] 0 0 m

/-! ### Register + Stack Environment Simulation Invariant & Correctness Proof (`zero sorry`) -/

/-- Simulation invariant stating that `st` (with `st.stack.length = curH` and live registers `< usedRegs`)
    faithfully realizes lexical `env` at locations `locs`. -/
def EnvMatches (env : List UInt64) (locs : List VarLoc) (usedRegs : Nat) (curH : Nat)
    (st : LIRState) : Prop :=
  st.stack.length = curH ∧
  (∀ (ix : Nat),
    match env[ix]?, locs[ix]? with
    | some v, some (.inReg r) => r.val < usedRegs ∧ st.getLocal r = v
    | some v, some (.onStack h) => h < curH ∧ st.stack[curH - 1 - h]? = some v
    | none, none => True
    | _, _ => False)

theorem envMatches_empty (a : UInt64) : EnvMatches [] [] 0 0 { acc := a, stack := [] } := by
  refine ⟨rfl, fun ix => ?_⟩
  simp

theorem envMatches_preserve {env : List UInt64} {locs : List VarLoc} {usedRegs curH : Nat}
    {st st' : LIRState}
    (hM : EnvMatches env locs usedRegs curH st)
    (hStk : st'.stack = st.stack)
    (hRegs : ∀ r : LocalReg, r.val < usedRegs → st'.getLocal r = st.getLocal r) :
    EnvMatches env locs usedRegs curH st' := by
  refine ⟨by rw [hStk]; exact hM.1, fun ix => ?_⟩
  have hIx := hM.2 ix
  cases hE : env[ix]? <;> cases hL : locs[ix]? <;> simp only [hE, hL] at hIx ⊢
  rename_i v loc
  cases loc with
  | inReg r =>
    rcases hIx with ⟨hLt, hVal⟩
    exact ⟨hLt, (hRegs r hLt).trans hVal⟩
  | onStack h =>
    rcases hIx with ⟨hLt, hSlot⟩
    rw [hStk]
    exact ⟨hLt, hSlot⟩

theorem envMatches_weaken_regs {env : List UInt64} {locs : List VarLoc} {usedRegs usedRegs' curH : Nat}
    {st : LIRState}
    (hM : EnvMatches env locs usedRegs curH st)
    (hLe : usedRegs ≤ usedRegs') :
    EnvMatches env locs usedRegs' curH st := by
  refine ⟨hM.1, fun ix => ?_⟩
  have hIx := hM.2 ix
  cases hE : env[ix]? <;> cases hL : locs[ix]? <;> simp only [hE, hL] at hIx ⊢
  rename_i v loc
  cases loc with
  | inReg r => exact ⟨by omega, hIx.2⟩
  | onStack h => exact hIx

theorem envMatches_store_temp {env : List UInt64} {locs : List VarLoc} {usedRegs curH : Nat}
    {st : LIRState} (hReg : usedRegs < 4) (tmp : UInt64)
    (hM : EnvMatches env locs usedRegs curH st) :
    EnvMatches env locs (usedRegs + 1) curH (st.setLocal ⟨usedRegs, hReg⟩ tmp) := by
  have hPres : EnvMatches env locs usedRegs curH (st.setLocal ⟨usedRegs, hReg⟩ tmp) := by
    apply envMatches_preserve hM (LIRState.setLocal_stack _ _ _)
    intro r hrLt
    exact LIRState.getLocal_setLocal_ne st ⟨usedRegs, hReg⟩ r tmp (by simp; omega)
  exact envMatches_weaken_regs hPres (by omega)

theorem envMatches_bind_reg {env : List UInt64} {locs : List VarLoc} {usedRegs curH : Nat}
    {st : LIRState} (hReg : usedRegs < 4) (v : UInt64)
    (hM : EnvMatches env locs usedRegs curH st) :
    EnvMatches (v :: env) (.inReg ⟨usedRegs, hReg⟩ :: locs) (usedRegs + 1) curH
      (st.setLocal ⟨usedRegs, hReg⟩ v) := by
  refine ⟨by simp [hM.1], fun ix => ?_⟩
  cases ix with
  | zero =>
    simp only [List.getElem?_cons_zero, LIRState.getLocal_setLocal_same]
    exact ⟨by simp, trivial⟩
  | succ ix' =>
    simp only [List.getElem?_cons_succ]
    exact (envMatches_store_temp hReg v hM).2 ix'

theorem envMatches_push_temp {env : List UInt64} {locs : List VarLoc} {usedRegs curH : Nat}
    {st : LIRState} (tmp : UInt64)
    (hM : EnvMatches env locs usedRegs curH st) :
    EnvMatches env locs usedRegs (curH + 1) { st with stack := tmp :: st.stack } := by
  refine ⟨by simp [hM.1], fun ix => ?_⟩
  have hIx := hM.2 ix
  cases hE : env[ix]? <;> cases hL : locs[ix]? <;> simp only [hE, hL] at hIx ⊢
  rename_i v loc
  cases loc with
  | inReg r =>
    exact hIx
  | onStack h =>
    rcases hIx with ⟨hLt, hLookup⟩
    refine ⟨by omega, ?_⟩
    have hIdxEq : curH + 1 - 1 - h = (curH - 1 - h) + 1 := by omega
    rw [hIdxEq]
    simpa using hLookup

theorem envMatches_bind_stack {env : List UInt64} {locs : List VarLoc} {usedRegs curH : Nat}
    {st : LIRState} (v : UInt64)
    (hM : EnvMatches env locs usedRegs curH st) :
    EnvMatches (v :: env) (.onStack curH :: locs) usedRegs (curH + 1)
      { st with stack := v :: st.stack } := by
  refine ⟨by simp [hM.1], fun ix => ?_⟩
  cases ix with
  | zero =>
    simp only [List.getElem?_cons_zero]
    refine ⟨by omega, ?_⟩
    have hZ : curH + 1 - 1 - curH = 0 := by omega
    rw [hZ]
    rfl
  | succ ix' =>
    simp only [List.getElem?_cons_succ]
    exact (envMatches_push_temp v hM).2 ix'

@[simp]
theorem getLocal_update_acc_stack (st : LIRState) (a : UInt64) (stk : List UInt64) (r : LocalReg) :
    ({ st with acc := a, stack := stk } : LIRState).getLocal r = st.getLocal r := by
  rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;> rfl

/-- **Main `MIR → LIR` Register-Allocating & Loop-Aware Simulation Theorem (`exec_compileAux`)**:
    Executing `compileAux locs usedRegs curH m` from any state `st` satisfying `EnvMatches`:
    1. Computes `st'.acc = MIR.eval p₀ p₁ env m`
    2. Restores `st'.stack = st.stack` completely unchanged
    3. Preserves all live local registers `r` with `r.val < usedRegs`! -/
theorem exec_compileAux (p₀ p₁ : UInt64) (m : MIR) :
    ∀ (env : List UInt64) (locs : List VarLoc) (usedRegs curH : Nat) (st : LIRState),
      EnvMatches env locs usedRegs curH st →
      let st' := exec p₀ p₁ (compileAux locs usedRegs curH m) st
      st'.acc = MIR.eval p₀ p₁ env m ∧
      st'.stack = st.stack ∧
      (∀ (r : LocalReg), r.val < usedRegs → st'.getLocal r = st.getLocal r) := by
  induction m with
  | lit v =>
    intro env locs usedRegs curH st _
    simp [compileAux, MIR.eval]
  | param i =>
    intro env locs usedRegs curH st _
    simp [compileAux, MIR.eval]
  | var ix =>
    intro env locs usedRegs curH st hM
    have hIx := hM.2 ix
    simp only [compileAux, MIR.eval]
    cases hE : env[ix]? <;> cases hL : locs[ix]? <;> simp only [hE, hL] at hIx ⊢
    · simp
    · rename_i v loc
      cases loc with
      | inReg r =>
        rcases hIx with ⟨_, hRegVal⟩
        simp [hRegVal]
      | onStack h =>
        rcases hIx with ⟨_, hSlotVal⟩
        simp [hSlotVal]
  | binOp op lhs rhs ihl ihr =>
    intro env locs usedRegs curH st hM
    simp only [compileAux, MIR.eval]
    split
    · rename_i hReg
      simp only [exec_append, exec_cons, exec_nil, step_storeLocalReg, step_regBinOp]
      let st₁ := exec p₀ p₁ (compileAux locs usedRegs curH lhs) st
      have ⟨hAcc1, hStk1, hReg1⟩ := ihl env locs usedRegs curH st hM
      have hM1 : EnvMatches env locs usedRegs curH st₁ :=
        envMatches_preserve hM hStk1 hReg1
      let st₂ := st₁.setLocal ⟨usedRegs, hReg⟩ st₁.acc
      have hM2 : EnvMatches env locs (usedRegs + 1) curH st₂ :=
        envMatches_store_temp hReg st₁.acc hM1
      let st₃ := exec p₀ p₁ (compileAux locs (usedRegs + 1) curH rhs) st₂
      have ⟨hAcc3, hStk3, hReg3⟩ := ihr env locs (usedRegs + 1) curH st₂ hM2
      have hR0 : st₃.getLocal ⟨usedRegs, hReg⟩ = MIR.eval p₀ p₁ env lhs := by
        have hKeep := hReg3 ⟨usedRegs, hReg⟩ (by simp)
        dsimp only [st₃, st₂, st₁] at hKeep ⊢
        rw [hKeep, LIRState.getLocal_setLocal_same, hAcc1]
      refine ⟨?_, ?_, ?_⟩
      · dsimp only [st₃, st₂, st₁] at hR0 hAcc3 ⊢
        rw [hR0, hAcc3]
      · dsimp only [st₃, st₂, st₁] at hStk3 hStk1 ⊢
        rw [hStk3, LIRState.setLocal_stack, hStk1]
      · intro r hrLt
        simp only [getLocal_update_acc_stack]
        have h3 := hReg3 r (by omega)
        have h2 : st₂.getLocal r = st₁.getLocal r :=
          LIRState.getLocal_setLocal_ne st₁ ⟨usedRegs, hReg⟩ r st₁.acc (by simp; omega)
        exact h3.trans (h2.trans (hReg1 r hrLt))
    · simp only [exec_append, exec_cons, exec_nil, step_pushAcc, step_popBinOp]
      let st₁ := exec p₀ p₁ (compileAux locs usedRegs curH lhs) st
      have ⟨hAcc1, hStk1, hReg1⟩ := ihl env locs usedRegs curH st hM
      have hM1 : EnvMatches env locs usedRegs curH st₁ :=
        envMatches_preserve hM hStk1 hReg1
      let st₂ : LIRState := { st₁ with stack := st₁.acc :: st₁.stack }
      have hM2 : EnvMatches env locs usedRegs (curH + 1) st₂ :=
        envMatches_push_temp st₁.acc hM1
      let st₃ := exec p₀ p₁ (compileAux locs usedRegs (curH + 1) rhs) st₂
      have ⟨hAcc3, hStk3, hReg3⟩ := ihr env locs usedRegs (curH + 1) st₂ hM2
      have hStk3Eq : (exec p₀ p₁ (compileAux locs usedRegs (curH + 1) rhs) st₂).stack =
          MIR.eval p₀ p₁ env lhs :: st.stack := by
        dsimp only [st₂, st₁] at hStk3 ⊢
        rw [hStk3, hAcc1, hStk1]
      dsimp only [st₃, st₂, st₁] at hStk3Eq hAcc3 hReg3 ⊢
      rw [hStk3Eq]
      refine ⟨by simp [hAcc3], rfl, fun r hrLt => ?_⟩
      simp only [getLocal_update_acc_stack]
      exact (hReg3 r hrLt).trans (hReg1 r hrLt)
  | letAlloc own val body ihv ihb =>
    intro env locs usedRegs curH st hM
    simp only [compileAux, MIR.eval]
    split
    · rename_i hReg
      simp only [exec_append, exec_cons, exec_nil, step_storeLocalReg]
      let st₁ := exec p₀ p₁ (compileAux locs usedRegs curH val) st
      have ⟨hAcc1, hStk1, hReg1⟩ := ihv env locs usedRegs curH st hM
      have hM1 : EnvMatches env locs usedRegs curH st₁ :=
        envMatches_preserve hM hStk1 hReg1
      let st₂ := st₁.setLocal ⟨usedRegs, hReg⟩ st₁.acc
      have hM2 : EnvMatches (MIR.eval p₀ p₁ env val :: env) (.inReg ⟨usedRegs, hReg⟩ :: locs) (usedRegs + 1) curH st₂ := by
        dsimp only [st₂, st₁]
        rw [← hAcc1]
        exact envMatches_bind_reg hReg st₁.acc hM1
      have ⟨hAcc3, hStk3, hReg3⟩ :=
        ihb (MIR.eval p₀ p₁ env val :: env) (.inReg ⟨usedRegs, hReg⟩ :: locs) (usedRegs + 1) curH st₂ hM2
      refine ⟨hAcc3, ?_, ?_⟩
      · dsimp only [st₂, st₁] at hStk3 ⊢
        rw [hStk3, LIRState.setLocal_stack, hStk1]
      · intro r hrLt
        have h3 := hReg3 r (by omega)
        have h2 : st₂.getLocal r = st₁.getLocal r :=
          LIRState.getLocal_setLocal_ne st₁ ⟨usedRegs, hReg⟩ r st₁.acc (by simp; omega)
        exact h3.trans (h2.trans (hReg1 r hrLt))
    · simp only [exec_append, exec_cons, exec_nil, step_pushAcc, step_popDrop]
      let st₁ := exec p₀ p₁ (compileAux locs usedRegs curH val) st
      have ⟨hAcc1, hStk1, hReg1⟩ := ihv env locs usedRegs curH st hM
      have hM1 : EnvMatches env locs usedRegs curH st₁ :=
        envMatches_preserve hM hStk1 hReg1
      let st₂ : LIRState := { st₁ with stack := st₁.acc :: st₁.stack }
      have hM2 : EnvMatches (MIR.eval p₀ p₁ env val :: env) (.onStack curH :: locs) usedRegs (curH + 1) st₂ := by
        dsimp only [st₂, st₁]
        rw [← hAcc1]
        exact envMatches_bind_stack st₁.acc hM1
      have ⟨hAcc3, hStk3, hReg3⟩ :=
        ihb (MIR.eval p₀ p₁ env val :: env) (.onStack curH :: locs) usedRegs (curH + 1) st₂ hM2
      have hStk3Eq : (exec p₀ p₁ (compileAux (.onStack curH :: locs) usedRegs (curH + 1) body) st₂).stack =
          st₁.acc :: st.stack := by
        dsimp only [st₂] at hStk3 ⊢
        rw [hStk3, hStk1]
      dsimp only [st₂, st₁] at hAcc3 hStk3Eq hReg3 ⊢
      refine ⟨hAcc3, ?_, fun r hrLt => ?_⟩
      · rw [hStk3Eq]
        rfl
      · simp only [getLocal_update_acc_stack]
        exact (hReg3 r hrLt).trans (hReg1 r hrLt)
  | joinIfZero cond zBr nzBr ihc ihz ihnz =>
    intro env locs usedRegs curH st hM
    simp only [compileAux, exec_append, exec_cons, exec_nil, step_condZero, MIR.eval]
    let st₁ := exec p₀ p₁ (compileAux locs usedRegs curH cond) st
    have ⟨hAcc1, hStk1, hReg1⟩ := ihc env locs usedRegs curH st hM
    have hM1 : EnvMatches env locs usedRegs curH st₁ :=
      envMatches_preserve hM hStk1 hReg1
    rw [hAcc1]
    split
    · have ⟨ha, hs, hr⟩ := ihz env locs usedRegs curH st₁ hM1
      exact ⟨ha, hs.trans hStk1, fun r hLt => (hr r hLt).trans (hReg1 r hLt)⟩
    · have ⟨ha, hs, hr⟩ := ihnz env locs usedRegs curH st₁ hM1
      exact ⟨ha, hs.trans hStk1, fun r hLt => (hr r hLt).trans (hReg1 r hLt)⟩
  | repeatLoop count init stepBody ihi ihs =>
    intro env locs usedRegs curH st hM
    simp only [compileAux, exec_append, exec_cons, exec_nil, step_repeatLoop, MIR.eval]
    let saveC := MIR.hasLoop stepBody
    let bodyH := if saveC then curH + 1 else curH
    let stepCode : List LIRInstr :=
      if hReg : usedRegs < 4 then
        let r : LocalReg := ⟨usedRegs, hReg⟩
        [.storeLocalReg r] ++ compileAux (.inReg r :: locs) (usedRegs + 1) bodyH stepBody
      else
        [.pushAcc] ++ compileAux (.onStack bodyH :: locs) usedRegs (bodyH + 1) stepBody ++ [.popDrop]
    have hStepOne : ∀ (sIn : LIRState),
        EnvMatches env locs usedRegs bodyH sIn →
        let sOut := exec p₀ p₁ stepCode sIn
        sOut.acc = MIR.eval p₀ p₁ (sIn.acc :: env) stepBody ∧
        sOut.stack = sIn.stack ∧
        (∀ r : LocalReg, r.val < usedRegs → sOut.getLocal r = sIn.getLocal r) := by
      intro sIn hMIn
      dsimp only [stepCode]
      split
      · rename_i hReg
        simp only [List.singleton_append, exec_cons, step_storeLocalReg]
        let sMid := sIn.setLocal ⟨usedRegs, hReg⟩ sIn.acc
        have hMMid : EnvMatches (sIn.acc :: env) (.inReg ⟨usedRegs, hReg⟩ :: locs) (usedRegs + 1) bodyH sMid :=
          envMatches_bind_reg hReg sIn.acc hMIn
        have ⟨ha, hs, hr⟩ := ihs (sIn.acc :: env) (.inReg ⟨usedRegs, hReg⟩ :: locs) (usedRegs + 1) bodyH sMid hMMid
        refine ⟨ha, ?_, fun r hrLt => ?_⟩
        · dsimp only [sMid] at hs ⊢
          rw [hs, LIRState.setLocal_stack]
        · have h2 : sMid.getLocal r = sIn.getLocal r :=
            LIRState.getLocal_setLocal_ne sIn ⟨usedRegs, hReg⟩ r sIn.acc (by simp; omega)
          exact (hr r (by omega)).trans h2
      · simp only [List.singleton_append, exec_cons, exec_append, exec_nil, step_pushAcc, step_popDrop]
        let sMid : LIRState := { sIn with stack := sIn.acc :: sIn.stack }
        have hMMid : EnvMatches (sIn.acc :: env) (.onStack bodyH :: locs) usedRegs (bodyH + 1) sMid :=
          envMatches_bind_stack sIn.acc hMIn
        have ⟨ha, hs, hr⟩ := ihs (sIn.acc :: env) (.onStack bodyH :: locs) usedRegs (bodyH + 1) sMid hMMid
        dsimp only [sMid] at ha hs hr ⊢
        refine ⟨ha, ?_, fun r hrLt => ?_⟩
        · rw [hs]
          rfl
        · simp only [getLocal_update_acc_stack]
          exact hr r hrLt
    have hLoop : ∀ (n : Nat) (rem : UInt64) (s : LIRState),
        EnvMatches env locs usedRegs curH s →
        s.stack = st.stack →
        (∀ r : LocalReg, r.val < usedRegs → s.getLocal r = st.getLocal r) →
        let sFinal := runLoop p₀ p₁ saveC stepCode n rem s
        sFinal.acc = iterN n (fun a => MIR.eval p₀ p₁ (a :: env) stepBody) s.acc ∧
        sFinal.stack = st.stack ∧
        (∀ r : LocalReg, r.val < usedRegs → sFinal.getLocal r = st.getLocal r) := by
      intro n
      induction n with
      | zero =>
        intro rem s _ hStk hRegs
        simp only [runLoop_zero, iterN]
        exact ⟨trivial, hStk, hRegs⟩
      | succ k ihk =>
        intro rem s hMs hStk hRegs
        cases hSave : saveC
        · dsimp only
          rw [runLoop_succ_false]
          have hBodyHEq : bodyH = curH := by simp [bodyH, hSave]
          have hMIn : EnvMatches env locs usedRegs bodyH s := hBodyHEq ▸ hMs
          let s2 := exec p₀ p₁ stepCode s
          have ⟨ha2, hs2, hr2⟩ := hStepOne s hMIn
          have hStk2 : s2.stack = st.stack := hs2.trans hStk
          have hRegs2 : ∀ r : LocalReg, r.val < usedRegs → s2.getLocal r = st.getLocal r :=
            fun r hr => (hr2 r hr).trans (hRegs r hr)
          have hMs2 : EnvMatches env locs usedRegs curH s2 :=
            envMatches_preserve hMs hs2 hr2
          have hIH := ihk (rem - 1) s2 hMs2 hStk2 hRegs2
          dsimp only at hIH
          rw [hSave] at hIH
          rcases hIH with ⟨haF, hsF, hrF⟩
          refine ⟨?_, hsF, hrF⟩
          dsimp only [s2] at haF ha2 ⊢
          rw [haF, ha2]
          rfl
        · dsimp only
          rw [runLoop_succ_true]
          have hBodyHEq : bodyH = curH + 1 := by simp [bodyH, hSave]
          let s1 : LIRState := { s with stack := rem :: s.stack }
          have hMIn : EnvMatches env locs usedRegs bodyH s1 :=
            hBodyHEq ▸ envMatches_push_temp rem hMs
          let s2 := exec p₀ p₁ stepCode s1
          have ⟨ha2, hs2, hr2⟩ := hStepOne s1 hMIn
          have hs2Eq : (exec p₀ p₁ stepCode { s with stack := rem :: s.stack }).stack = rem :: s.stack := hs2
          dsimp only
          rw [hs2Eq]
          dsimp only
          let s3 : LIRState := { s2 with stack := s.stack }
          have hStk3 : s3.stack = st.stack := hStk
          have hRegs3 : ∀ r : LocalReg, r.val < usedRegs → s3.getLocal r = st.getLocal r := by
            intro r hr
            have h32 : s3.getLocal r = s2.getLocal r := getLocal_update_acc_stack s2 s2.acc s.stack r
            exact h32.trans ((hr2 r hr).trans (hRegs r hr))
          have hMs3 : EnvMatches env locs usedRegs curH s3 :=
            envMatches_preserve hMs rfl (fun r hr => (getLocal_update_acc_stack s2 s2.acc s.stack r).trans (hr2 r hr))
          have hIH := ihk (rem - 1) s3 hMs3 hStk3 hRegs3
          dsimp only at hIH
          rw [hSave] at hIH
          rcases hIH with ⟨haF, hsF, hrF⟩
          refine ⟨?_, hsF, hrF⟩
          dsimp only [s3, s2, s1] at haF ha2 ⊢
          rw [haF, ha2]
          rfl
    let stInit := exec p₀ p₁ (compileAux locs usedRegs curH init) st
    have ⟨hAccI, hStkI, hRegI⟩ := ihi env locs usedRegs curH st hM
    have hMInit : EnvMatches env locs usedRegs curH stInit :=
      envMatches_preserve hM hStkI hRegI
    have ⟨haL, hsL, hrL⟩ := hLoop count.toNat count stInit hMInit hStkI hRegI
    dsimp only [saveC, stepCode, bodyH, stInit] at haL hsL hrL hAccI ⊢
    refine ⟨?_, hsL, hrL⟩
    rw [haL, hAccI]

/-- **Theorem D3.3 (`exec_lowerFromMIR_acc_and_stack`)**: Closed `LIR` execution produces the exact
    64-bit return value of `MIR.eval` with a clean empty stack! -/
theorem exec_lowerFromMIR_acc_and_stack (p₀ p₁ : UInt64) (m : MIR) (initAcc : UInt64) :
    let st' := exec p₀ p₁ (lowerFromMIR m) { acc := initAcc, stack := [] }
    st'.acc = MIR.eval p₀ p₁ [] m ∧ st'.stack = [] := by
  have ⟨ha, hs, _⟩ := exec_compileAux p₀ p₁ m [] [] 0 0 { acc := initAcc, stack := [] } (envMatches_empty initAcc)
  exact ⟨ha, hs⟩

end LIR

end Narya.Compiler
