/-
  Narya.Compiler.Arm64 — Formal AArch64 ISA Semantics, Register-Allocated Loops & Cross-Platform Native Runner

  Stage 4 (Final Stage) of Leonardo de Moura's SViL Nov 2026 "New Code Generator" pipeline:
    `Core.Term` ──▶ `HIR` ──(`HIR.opt`)──▶ `HIR` ──▶ `MIR` ──▶ `LIR` ──▶ `Arm64` (`.s` Mach-O & ELF)

  Features:
  1. **Formal 64-bit `AArch64` Register + Aligned-Stack Machine (`Arm64State`, `Arm64Instr`)**:
     Models `x0..x7` (`x0` return/acc, `x1` scratch, `x2..x3` ABI params, `x4..x7` register-promoted
     locals), dedicated caller-saved hardware loop counter `x8` (`loopX8` with `cbz`/`sub #1`/`cbnz`),
     16-bit chunked `movz`/`movk` constant synthesis (proved exact via `bv_decide`), and `cbz` blocks.
  2. **End-to-End Machine-Checked Compiler Theorems (`compileFullPipeline_correct`, `zero sorry`)**:
     Proves that running the emitted `AArch64` machine code produces the **exact 64-bit `UInt64`**
     denotation of the source `HIR` program for ALL 64-bit inputs `(arg0, arg1)` with clean stack,
     including arbitrary register-promoted bindings and nested hardware loops!
  3. **Cross-Platform `arm64-apple-darwin` (Mach-O) & `aarch64-linux-gnu` (ELF) Native Runner**:
     Emits genuine Mach-O or ELF `.s` assembly, links via `clang`/`cc` with an AAPCS64 C harness,
     executes natively on Apple Silicon or Linux ARM64 hardware, and returns the live `UInt64`!
-/
import Std.Tactic.BVDecide
import Narya.Compiler.LIR

namespace Narya.Compiler

/-- General-purpose 64-bit `AArch64` registers `x0..x7` used by the verified backend.
    (Hardware register `x8` is reserved exclusively for counted loop control `loopX8`.) -/
inductive Reg64 where
  | x0 -- Accumulator & AAPCS64 64-bit return register
  | x1 -- Scratch operand register & AAPCS64 2nd argument on entry
  | x2 -- Saved AAPCS64 `arg0`
  | x3 -- Saved AAPCS64 `arg1`
  | x4 -- Caller-saved promoted local register `r0`
  | x5 -- Caller-saved promoted local register `r1`
  | x6 -- Caller-saved promoted local register `r2`
  | x7 -- Caller-saved promoted local register `r3`
  deriving DecidableEq, Repr, Inhabited

namespace Reg64

def asmName : Reg64 → String
  | .x0 => "x0"
  | .x1 => "x1"
  | .x2 => "x2"
  | .x3 => "x3"
  | .x4 => "x4"
  | .x5 => "x5"
  | .x6 => "x6"
  | .x7 => "x7"

/-- Map `LIR` `LocalReg` (`0..3`) to caller-saved `AArch64` register `x4..x7`. -/
@[inline]
def ofLocal (r : LocalReg) : Reg64 :=
  match r.val with
  | 0 => .x4
  | 1 => .x5
  | 2 => .x6
  | _ => .x7

end Reg64

/-- Valid `movk` 16-bit lane shift amounts on `AArch64` (`#16`, `#32`, `#48`). -/
inductive Shift16 where
  | s16
  | s32
  | s48
  deriving DecidableEq, Repr, Inhabited

namespace Shift16

def bits : Shift16 → UInt64
  | .s16 => 16
  | .s32 => 32
  | .s48 => 48

end Shift16

/-- Verified subset of `AArch64` (`arm64-apple-darwin` & `aarch64-linux-gnu`) instructions. -/
inductive Arm64Instr where
  /-- `mov rd, rs` -/
  | movReg (rd rs : Reg64)
  /-- `movz rd, #imm16` (zeros upper 48 bits, writes lower 16 bits) -/
  | movz (rd : Reg64) (imm16 : UInt64)
  /-- `movk rd, #imm16, lsl #shift` (patches 16-bit lane in-place) -/
  | movk (rd : Reg64) (imm16 : UInt64) (shift : Shift16)
  /-- `str rs, [sp, #-16]!` (16-byte aligned pre-index push) -/
  | push16 (rs : Reg64)
  /-- `ldr rd, [sp], #16` (16-byte aligned post-index pop) -/
  | pop16 (rd : Reg64)
  /-- `add sp, sp, #16` (discard top 16-byte stack slot) -/
  | drop16
  /-- `ldr rd, [sp, #(16 * slotIdx)]` (load 64-bit value from 16-byte stack slot) -/
  | ldrSlot16 (rd : Reg64) (slotIdx : Nat)
  /-- 64-bit ALU / bitwise register instruction `op rd, rn, rm` (`rd := op rn rm`). -/
  | aluReg (op : BinOp64) (rd rn rm : Reg64)
  /-- Structured `cbz reg, L_zero` ... `b L_end` `L_zero:` ... `L_end:` block. -/
  | cbzBlock (reg : Reg64) (zeroCode : List Arm64Instr) (nonZeroCode : List Arm64Instr)
  /-- Hardware counted loop in `x8` (`movz/movk x8, #iters; cbz x8, L_end; L_loop: ... sub x8, x8, #1; cbnz x8, L_loop`). -/
  | loopX8 (iters : UInt64) (saveX8 : Bool) (bodyCode : List Arm64Instr)
  deriving Repr, Inhabited

/-- Formal `AArch64` register file (`x0..x8`) + 16-byte-aligned stack state. -/
structure Arm64State where
  x0 : UInt64 := 0
  x1 : UInt64 := 0
  x2 : UInt64 := 0
  x3 : UInt64 := 0
  x4 : UInt64 := 0
  x5 : UInt64 := 0
  x6 : UInt64 := 0
  x7 : UInt64 := 0
  x8 : UInt64 := 0
  stack : List UInt64 := []
  deriving DecidableEq, Repr, Inhabited

namespace Arm64State

@[inline]
def getReg (st : Arm64State) : Reg64 → UInt64
  | .x0 => st.x0
  | .x1 => st.x1
  | .x2 => st.x2
  | .x3 => st.x3
  | .x4 => st.x4
  | .x5 => st.x5
  | .x6 => st.x6
  | .x7 => st.x7

@[inline]
def setReg (st : Arm64State) (r : Reg64) (v : UInt64) : Arm64State :=
  match r with
  | .x0 => { st with x0 := v }
  | .x1 => { st with x1 := v }
  | .x2 => { st with x2 := v }
  | .x3 => { st with x3 := v }
  | .x4 => { st with x4 := v }
  | .x5 => { st with x5 := v }
  | .x6 => { st with x6 := v }
  | .x7 => { st with x7 := v }

@[simp]
theorem setReg_x8 (st : Arm64State) (r : Reg64) (v : UInt64) :
    (st.setReg r v).x8 = st.x8 := by
  cases r <;> rfl

/-- Initial AAPCS64 entry state when C calls `narya_entry(arg0, arg1)`! -/
def initABI (arg0 arg1 : UInt64) : Arm64State :=
  { x0 := arg0, x1 := arg1 }

end Arm64State

namespace Arm64

/-- Semantics of `AArch64` `movz`: zero-extends low 16 bits. -/
@[inline]
def evalMovz (imm16 : UInt64) : UInt64 :=
  imm16 &&& 0xFFFF

/-- Semantics of `AArch64` `movk`: inserts 16-bit immediate at `shift` while keeping other 48 bits! -/
@[inline]
def evalMovk (old imm16 : UInt64) (sh : Shift16) : UInt64 :=
  let s := sh.bits
  let mask : UInt64 := (0xFFFF : UInt64) <<< s
  (old &&& ~~~mask) ||| ((imm16 &&& 0xFFFF) <<< s)

/-- **64-Bit Hardware `movz`+`movk` Reconstruction Theorem (`movzk_reconstruct_u64`)**:
    Loading the four 16-bit halfwords of ANY 64-bit `v : UInt64` via `movz` + three `movk`s
    reconstructs `v` **bit-for-bit identically**, verified by SAT/bit-blasting (`bv_decide`)! -/
theorem movzk_reconstruct_u64 (v : UInt64) :
    evalMovk
      (evalMovk
        (evalMovk (evalMovz (v &&& 0xFFFF)) ((v >>> 16) &&& 0xFFFF) .s16)
        ((v >>> 32) &&& 0xFFFF) .s32)
      ((v >>> 48) &&& 0xFFFF) .s48 = v := by
  simp only [evalMovz, evalMovk, Shift16.bits]
  bv_decide

/-- Single `loopX8` iteration transformer parameterized by `execBody : Arm64State → Arm64State`
    so `Arm64.step` and `Arm64.exec` remain 100% structural (kernel-reducible via `decide`!). -/
def iterStepArm64 (saveX8 : Bool) (execBody : Arm64State → Arm64State) (st : Arm64State) : Arm64State :=
  if saveX8 then
    let s2 := execBody { st with stack := st.x8 :: st.stack }
    match s2.stack with
    | top :: rest => { s2 with x8 := top - 1, stack := rest }
    | [] => { s2 with x8 := 0 - 1 }
  else
    let s2 := execBody st
    { s2 with x8 := s2.x8 - 1 }

mutual
/-- Execute a single `Arm64Instr` on `st` (purely structural, kernel-reducible!). -/
def step (st : Arm64State) : Arm64Instr → Arm64State
  | .movReg rd rs => st.setReg rd (st.getReg rs)
  | .movz rd imm => st.setReg rd (evalMovz imm)
  | .movk rd imm sh => st.setReg rd (evalMovk (st.getReg rd) imm sh)
  | .push16 rs => { st with stack := st.getReg rs :: st.stack }
  | .pop16 rd =>
    match st.stack with
    | top :: rest => { (st.setReg rd top) with stack := rest }
    | [] => st.setReg rd 0
  | .drop16 => { st with stack := st.stack.drop 1 }
  | .ldrSlot16 rd slot => st.setReg rd (st.stack[slot]?.getD 0)
  | .aluReg op rd rn rm =>
    st.setReg rd (op.eval (st.getReg rn) (st.getReg rm))
  | .cbzBlock reg zCode nzCode =>
    if st.getReg reg == 0 then exec zCode st
    else exec nzCode st
  | .loopX8 iters saveX8 bodyCode =>
    iterN iters.toNat (iterStepArm64 saveX8 (exec bodyCode)) { st with x8 := iters }

/-- Execute a list of `Arm64Instr`s sequentially. -/
def exec : List Arm64Instr → Arm64State → Arm64State
  | [], st => st
  | i :: is, st => exec is (step st i)
end

/-- Execute `n` iterations of `loopX8` hardware loop body. -/
def runLoop (saveX8 : Bool) (bodyCode : List Arm64Instr) (n : Nat) (st : Arm64State) : Arm64State :=
  iterN n (iterStepArm64 saveX8 (exec bodyCode)) st

@[simp] theorem exec_nil (st : Arm64State) : exec [] st = st := rfl

@[simp] theorem exec_cons (i : Arm64Instr) (is : List Arm64Instr) (st : Arm64State) :
    exec (i :: is) st = exec is (step st i) := rfl

@[simp] theorem step_movReg (rd rs : Reg64) (st : Arm64State) :
    step st (.movReg rd rs) = st.setReg rd (st.getReg rs) := rfl

@[simp] theorem step_movz (rd : Reg64) (imm : UInt64) (st : Arm64State) :
    step st (.movz rd imm) = st.setReg rd (evalMovz imm) := rfl

@[simp] theorem step_movk (rd : Reg64) (imm : UInt64) (sh : Shift16) (st : Arm64State) :
    step st (.movk rd imm sh) = st.setReg rd (evalMovk (st.getReg rd) imm sh) := rfl

@[simp] theorem step_push16 (rs : Reg64) (st : Arm64State) :
    step st (.push16 rs) = { st with stack := st.getReg rs :: st.stack } := rfl

@[simp] theorem step_pop16 (rd : Reg64) (st : Arm64State) :
    step st (.pop16 rd) =
      (match st.stack with
       | top :: rest => { (st.setReg rd top) with stack := rest }
       | [] => st.setReg rd 0) := rfl

@[simp] theorem step_drop16 (st : Arm64State) :
    step st .drop16 = { st with stack := st.stack.drop 1 } := rfl

@[simp] theorem step_ldrSlot16 (rd : Reg64) (slot : Nat) (st : Arm64State) :
    step st (.ldrSlot16 rd slot) = st.setReg rd (st.stack[slot]?.getD 0) := rfl

@[simp] theorem step_aluReg (op : BinOp64) (rd rn rm : Reg64) (st : Arm64State) :
    step st (.aluReg op rd rn rm) = st.setReg rd (op.eval (st.getReg rn) (st.getReg rm)) := rfl

@[simp] theorem step_cbzBlock (reg : Reg64) (zCode nzCode : List Arm64Instr) (st : Arm64State) :
    step st (.cbzBlock reg zCode nzCode) =
      (if st.getReg reg == 0 then exec zCode st else exec nzCode st) := rfl

@[simp] theorem step_loopX8 (iters : UInt64) (saveX8 : Bool) (bodyCode : List Arm64Instr) (st : Arm64State) :
    step st (.loopX8 iters saveX8 bodyCode) =
      runLoop saveX8 bodyCode iters.toNat { st with x8 := iters } := rfl

@[simp] theorem runLoop_zero (saveX8 : Bool) (bodyCode : List Arm64Instr) (st : Arm64State) :
    runLoop saveX8 bodyCode 0 st = st := rfl

theorem runLoop_succ_false (bodyCode : List Arm64Instr) (k : Nat) (st : Arm64State) :
    runLoop false bodyCode (k + 1) st =
      (let s2 := exec bodyCode st
       runLoop false bodyCode k { s2 with x8 := s2.x8 - 1 }) := rfl

theorem runLoop_succ_true (bodyCode : List Arm64Instr) (k : Nat) (st : Arm64State) :
    runLoop true bodyCode (k + 1) st =
      (let s2 := exec bodyCode { st with stack := st.x8 :: st.stack }
       match s2.stack with
       | top :: rest => runLoop true bodyCode k { s2 with x8 := top - 1, stack := rest }
       | [] => runLoop true bodyCode k { s2 with x8 := 0 - 1 }) := by
  simp only [runLoop, iterN, iterStepArm64, ite_true]
  cases (exec bodyCode { st with stack := st.x8 :: st.stack }).stack <;> rfl

@[simp]
theorem exec_append (c₁ c₂ : List Arm64Instr) (st : Arm64State) :
    exec (c₁ ++ c₂) st = exec c₂ (exec c₁ st) := by
  induction c₁ generalizing st with
  | nil => simp
  | cons i rest ih =>
    simp only [List.cons_append, exec_cons]
    exact ih (step st i)

/-! ### `LIR → Arm64` Instruction Selection -/

/-- Emit exact 4-instruction `movz`/`movk` sequence materializing any 64-bit `v : UInt64` into `x0`. -/
def emitLoadImm64 (v : UInt64) : List Arm64Instr :=
  [ .movz .x0 (v &&& 0xFFFF)
  , .movk .x0 ((v >>> 16) &&& 0xFFFF) .s16
  , .movk .x0 ((v >>> 32) &&& 0xFFFF) .s32
  , .movk .x0 ((v >>> 48) &&& 0xFFFF) .s48 ]

@[simp]
theorem exec_emitLoadImm64 (v : UInt64) (st : Arm64State) :
    exec (emitLoadImm64 v) st = { st with x0 := v } := by
  simp only [emitLoadImm64, exec_cons, exec_nil, step_movz, step_movk, Arm64State.setReg, Arm64State.getReg]
  rw [movzk_reconstruct_u64 v]

mutual
/-- Lower a single `LIRInstr` into `Arm64Instr`s. -/
def emitInstr : LIRInstr → List Arm64Instr
  | .loadImm v => emitLoadImm64 v
  | .loadParam i =>
    if i.val == 0 then [.movReg .x0 .x2] else [.movReg .x0 .x3]
  | .loadLocalReg r => [.movReg .x0 (Reg64.ofLocal r)]
  | .storeLocalReg r => [.movReg (Reg64.ofLocal r) .x0]
  | .regBinOp op r => [.aluReg op .x0 (Reg64.ofLocal r) .x0]
  | .loadSlot slot => [.ldrSlot16 .x0 slot]
  | .pushAcc => [.push16 .x0]
  | .popDrop => [.drop16]
  | .popBinOp op => [.pop16 .x1, .aluReg op .x0 .x1 .x0]
  | .condZero zBr nzBr =>
    [.cbzBlock .x0 (emitCode zBr) (emitCode nzBr)]
  | .repeatLoop iters saveCounter body =>
    [.loopX8 iters saveCounter (emitCode body)]

/-- Lower a list of `LIRInstr`s into `Arm64Instr`s. -/
def emitCode : List LIRInstr → List Arm64Instr
  | [] => []
  | i :: is => emitInstr i ++ emitCode is
end

/-- Complete `Arm64` function body including AAPCS64 entry prologue (`mov x2, x0; mov x3, x1`). -/
def emitFunction (lirCode : List LIRInstr) : List Arm64Instr :=
  [.movReg .x2 .x0, .movReg .x3 .x1] ++ emitCode lirCode

/-- Compile an `HIR` program all the way through `HIR.opt → MIR → LIR → Arm64`! -/
def compileFullPipeline (prog : HIR) : List Arm64Instr :=
  let hirOpt := HIR.opt prog
  let mir := MIR.lowerFromHIR hirOpt
  let lir := LIR.lowerFromMIR mir
  emitFunction lir

/-! ### Hardware Loop-Counter (`x8`) Non-Interference Theorem -/

mutual
/-- Theorem certifying that loop-free `LIR` instructions never modify hardware loop counter `x8`! -/
theorem noLoopInstr_preserves_x8 (instr : LIRInstr) (hNo : LIR.hasLoopInstr instr = false)
    (st : Arm64State) :
    (exec (emitInstr instr) st).x8 = st.x8 := by
  cases instr with
  | loadImm v => simp [emitInstr]
  | loadParam i =>
    simp only [emitInstr]
    split <;> simp [Arm64State.setReg]
  | loadLocalReg r =>
    rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;> simp [emitInstr, Reg64.ofLocal, Arm64State.setReg]
  | storeLocalReg r =>
    rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;> simp [emitInstr, Reg64.ofLocal, Arm64State.setReg]
  | regBinOp op r =>
    rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;> simp [emitInstr, Reg64.ofLocal, Arm64State.setReg]
  | loadSlot s => simp [emitInstr, Arm64State.setReg]
  | pushAcc => simp [emitInstr]
  | popDrop => simp [emitInstr]
  | popBinOp op =>
    simp only [emitInstr, exec_cons, exec_nil, step_pop16, step_aluReg]
    cases st.stack <;> simp [Arm64State.setReg]
  | condZero zBr nzBr =>
    simp only [LIR.hasLoopInstr, Bool.or_eq_false_iff] at hNo
    simp only [emitInstr, exec_cons, exec_nil, step_cbzBlock]
    split
    · exact noLoopCode_preserves_x8 zBr hNo.1 st
    · exact noLoopCode_preserves_x8 nzBr hNo.2 st
  | repeatLoop _ _ _ =>
    simp [LIR.hasLoopInstr] at hNo

theorem noLoopCode_preserves_x8 (code : List LIRInstr) (hNo : LIR.hasLoopCode code = false)
    (st : Arm64State) :
    (exec (emitCode code) st).x8 = st.x8 := by
  cases code with
  | nil => simp [emitCode]
  | cons i rest =>
    simp only [LIR.hasLoopCode, Bool.or_eq_false_iff] at hNo
    simp only [emitCode, exec_append]
    rw [noLoopCode_preserves_x8 rest hNo.2]
    exact noLoopInstr_preserves_x8 i hNo.1 st
end

/-! ### `LIR → Arm64` Simulation Proof & End-to-End Correctness Theorem (`zero sorry`) -/

/-- State projection invariant relating `Arm64State` (`x0`, `x2..x7`, `stack`) to `LIRState`. -/
def MatchesLIR (p₀ p₁ : UInt64) (ast : Arm64State) (lst : LIRState) : Prop :=
  ast.x0 = lst.acc ∧
  ast.x2 = p₀ ∧
  ast.x3 = p₁ ∧
  ast.x4 = lst.r0 ∧
  ast.x5 = lst.r1 ∧
  ast.x6 = lst.r2 ∧
  ast.x7 = lst.r3 ∧
  ast.stack = lst.stack

mutual
theorem step_simulates_lir (p₀ p₁ : UInt64) (instr : LIRInstr) :
    ∀ (ast : Arm64State) (lst : LIRState),
      MatchesLIR p₀ p₁ ast lst →
      MatchesLIR p₀ p₁ (exec (emitInstr instr) ast) (LIR.step p₀ p₁ lst instr) := by
  cases instr with
  | loadImm v =>
    intro ast lst ⟨_, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    simp [emitInstr, MatchesLIR, hx2, hx3, hx4, hx5, hx6, hx7, hstk]
  | loadParam i =>
    intro ast lst ⟨_, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    simp only [emitInstr, LIR.step_loadParam]
    split <;> simp [Arm64State.setReg, Arm64State.getReg, MatchesLIR, hx2, hx3, hx4, hx5, hx6, hx7, hstk]
  | loadLocalReg r =>
    intro ast lst ⟨_, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;>
      simp [emitInstr, Reg64.ofLocal, Arm64State.setReg, Arm64State.getReg, LIRState.getLocal,
            MatchesLIR, hx2, hx3, hx4, hx5, hx6, hx7, hstk] <;> omega
  | storeLocalReg r =>
    intro ast lst ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;>
      simp [emitInstr, Reg64.ofLocal, Arm64State.setReg, Arm64State.getReg, LIRState.setLocal,
            MatchesLIR, hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk] <;> omega
  | regBinOp op r =>
    intro ast lst ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    rcases r with ⟨_ | _ | _ | _ | n, h⟩ <;>
      simp [emitInstr, Reg64.ofLocal, Arm64State.setReg, Arm64State.getReg, LIRState.getLocal,
            MatchesLIR, hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk] <;> omega
  | loadSlot slot =>
    intro ast lst ⟨_, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    simp [emitInstr, Arm64State.setReg, MatchesLIR, hx2, hx3, hx4, hx5, hx6, hx7, hstk]
  | pushAcc =>
    intro ast lst ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    simp [emitInstr, Arm64State.getReg, MatchesLIR, hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk]
  | popDrop =>
    intro ast lst ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    simp [emitInstr, MatchesLIR, hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk]
  | popBinOp op =>
    intro ast lst ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    simp only [emitInstr, exec_cons, exec_nil, step_pop16, step_aluReg, LIR.step_popBinOp, hstk]
    cases hLst : lst.stack with
    | nil =>
      simp [Arm64State.setReg, Arm64State.getReg, MatchesLIR, hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk, hLst]
    | cons lhs rest =>
      simp [Arm64State.setReg, Arm64State.getReg, MatchesLIR, hx0, hx2, hx3, hx4, hx5, hx6, hx7]
  | condZero zBr nzBr =>
    intro ast lst hM
    rcases hM with ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    simp only [emitInstr, exec_cons, exec_nil, step_cbzBlock, Arm64State.getReg, LIR.step_condZero, hx0]
    split
    · exact exec_simulates_lir p₀ p₁ zBr ast lst ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    · exact exec_simulates_lir p₀ p₁ nzBr ast lst ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
  | repeatLoop iters saveC body =>
    intro ast lst ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
    simp only [emitInstr, exec_cons, exec_nil, step_loopX8, LIR.step_repeatLoop]
    exact runLoop_simulates_lir p₀ p₁ saveC body iters.toNat iters
      { ast with x8 := iters } lst
      ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
      (fun _ => rfl)
termination_by (sizeOf instr, 0)

theorem exec_simulates_lir (p₀ p₁ : UInt64) (code : List LIRInstr) :
    ∀ (ast : Arm64State) (lst : LIRState),
      MatchesLIR p₀ p₁ ast lst →
      MatchesLIR p₀ p₁ (exec (emitCode code) ast) (LIR.exec p₀ p₁ code lst) := by
  cases code with
  | nil =>
    intro ast lst hM
    simpa [emitCode] using hM
  | cons i rest =>
    intro ast lst hM
    simp only [emitCode, exec_append, LIR.exec_cons]
    have hStep := step_simulates_lir p₀ p₁ i ast lst hM
    exact exec_simulates_lir p₀ p₁ rest (exec (emitInstr i) ast) (LIR.step p₀ p₁ lst i) hStep
termination_by (sizeOf code, 0)

theorem runLoop_simulates_lir (p₀ p₁ : UInt64) (saveC : Bool) (body : List LIRInstr)
    (n : Nat) :
    ∀ (rem : UInt64) (ast : Arm64State) (lst : LIRState),
      MatchesLIR p₀ p₁ ast lst →
      (saveC = true → ast.x8 = rem) →
      MatchesLIR p₀ p₁
        (runLoop saveC (emitCode body) n ast)
        (LIR.runLoop p₀ p₁ saveC body n rem lst) := by
  cases n with
  | zero =>
    intro rem ast lst hM _
    simpa using hM
  | succ k =>
    intro rem ast lst hM hX8
    cases saveC with
    | false =>
      rw [runLoop_succ_false, LIR.runLoop_succ_false]
      dsimp only
      let s2 := exec (emitCode body) ast
      let st2 := LIR.exec p₀ p₁ body lst
      have hM2 : MatchesLIR p₀ p₁ s2 st2 := exec_simulates_lir p₀ p₁ body ast lst hM
      rcases hM2 with ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
      exact runLoop_simulates_lir p₀ p₁ false body k (rem - 1)
        { s2 with x8 := s2.x8 - 1 } st2
        ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
        (fun h => by cases h)
    | true =>
      rw [runLoop_succ_true, LIR.runLoop_succ_true]
      dsimp only
      have hRemEq : ast.x8 = rem := hX8 rfl
      rcases hM with ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, hstk⟩
      let s1 : Arm64State := { ast with stack := ast.x8 :: ast.stack }
      let st1 : LIRState := { lst with stack := rem :: lst.stack }
      have hM1 : MatchesLIR p₀ p₁ s1 st1 :=
        ⟨hx0, hx2, hx3, hx4, hx5, hx6, hx7, by simp [s1, st1, hRemEq, hstk]⟩
      let s2 := exec (emitCode body) s1
      let st2 := LIR.exec p₀ p₁ body st1
      have hM2 : MatchesLIR p₀ p₁ s2 st2 := exec_simulates_lir p₀ p₁ body s1 st1 hM1
      rcases hM2 with ⟨hx0_2, hx2_2, hx3_2, hx4_2, hx5_2, hx6_2, hx7_2, hstk_2⟩
      dsimp only [s2, st2, s1, st1] at hx0_2 hx2_2 hx3_2 hx4_2 hx5_2 hx6_2 hx7_2 hstk_2 ⊢
      rw [hstk_2]
      cases hSt2 : (LIR.exec p₀ p₁ body { lst with stack := rem :: lst.stack }).stack with
      | nil =>
        dsimp only
        exact runLoop_simulates_lir p₀ p₁ true body k (0 - 1) _ _
          ⟨hx0_2, hx2_2, hx3_2, hx4_2, hx5_2, hx6_2, hx7_2, hSt2.symm⟩
          (fun _ => rfl)
      | cons top rest =>
        dsimp only
        exact runLoop_simulates_lir p₀ p₁ true body k (top - 1) _ _
          ⟨hx0_2, hx2_2, hx3_2, hx4_2, hx5_2, hx6_2, hx7_2, rfl⟩
          (fun _ => rfl)
termination_by (sizeOf body, n + 1)
end

/-- Prologue simulation: `emitFunction lir` saves AAPCS64 `(arg0, arg1)` into `(x2, x3)`
    and simulates `LIR.exec arg0 arg1 lir { acc := arg0, stack := [] }`. -/
theorem emitFunction_simulates_lir (arg0 arg1 : UInt64) (lirCode : List LIRInstr) :
    MatchesLIR arg0 arg1
      (exec (emitFunction lirCode) (Arm64State.initABI arg0 arg1))
      (LIR.exec arg0 arg1 lirCode { acc := arg0, stack := [] }) := by
  unfold emitFunction
  rw [exec_append]
  have hPrologue :
      MatchesLIR arg0 arg1
        (exec [.movReg .x2 .x0, .movReg .x3 .x1] (Arm64State.initABI arg0 arg1))
        { acc := arg0, stack := [] } := by
    simp [Arm64State.initABI, Arm64State.setReg, Arm64State.getReg, MatchesLIR]
  exact exec_simulates_lir arg0 arg1 lirCode _ _ hPrologue

/-- **End-to-End Multi-IR Compiler Correctness Theorem (`compileFullPipeline_correct`, `0 sorry`)**:
    For **every** `HIR` program `prog` (including `repeatLoop`, `ifZero`, and arbitrarily deep
    register-promoted / stack-spilled `letBind`s) and **every** pair of 64-bit hardware arguments `(arg0, arg1)`,
    running `compileFullPipeline prog` on `AArch64` leaves the **exact** source denotation
    `HIR.eval arg0 arg1 [] prog` in return register `x0`! -/
theorem compileFullPipeline_correct (prog : HIR) (arg0 arg1 : UInt64) :
    (exec (compileFullPipeline prog) (Arm64State.initABI arg0 arg1)).x0 =
      HIR.eval arg0 arg1 [] prog := by
  simp only [compileFullPipeline]
  have hSim := emitFunction_simulates_lir arg0 arg1
    (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt prog)))
  have ⟨hLirAcc, _⟩ := LIR.exec_lowerFromMIR_acc_and_stack arg0 arg1
    (MIR.lowerFromHIR (HIR.opt prog)) arg0
  rcases hSim with ⟨hx0, _⟩
  rw [hx0, hLirAcc, MIR.eval_lower_eq, HIR.eval_opt_eq]

/-- **AAPCS64 Stack Preservation Theorem (`compileFullPipeline_stack_clean`, `0 sorry`)**:
    Every compiled `AArch64` function returns with its hardware stack pointer `sp` completely
    restored (`stack = []`), guaranteeing zero stack leaks across arbitrary loops and branches! -/
theorem compileFullPipeline_stack_clean (prog : HIR) (arg0 arg1 : UInt64) :
    (exec (compileFullPipeline prog) (Arm64State.initABI arg0 arg1)).stack = [] := by
  simp only [compileFullPipeline]
  have hSim := emitFunction_simulates_lir arg0 arg1
    (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt prog)))
  have ⟨_, hLirStk⟩ := LIR.exec_lowerFromMIR_acc_and_stack arg0 arg1
    (MIR.lowerFromHIR (HIR.opt prog)) arg0
  rcases hSim with ⟨_, _, _, _, _, _, _, hstk⟩
  exact hstk.trans hLirStk

/-! ### Cross-Platform `arm64-apple-darwin` (Mach-O) & `aarch64-linux-gnu` (ELF) Assembly Emitter & Runner -/

/-- `AArch64` assembly mnemonic for each `BinOp64`. -/
def binOpMnemonic : BinOp64 → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .bitAnd => "and"
  | .bitOr => "orr"
  | .bitXor => "eor"
  | .shl => "lsl"
  | .shr => "lsr"

mutual
/-- Render a single `Arm64Instr` into `AArch64` assembly lines, threading a fresh label counter `lbl`. -/
def renderInstrAux (lbl : Nat) : Arm64Instr → List String × Nat
  | .movReg rd rs =>
    ([s!"  mov {rd.asmName}, {rs.asmName}"], lbl)
  | .movz rd imm =>
    let v := (imm &&& 0xFFFF).toNat
    ([s!"  movz {rd.asmName}, #{v}"], lbl)
  | .movk rd imm sh =>
    let v := (imm &&& 0xFFFF).toNat
    ([s!"  movk {rd.asmName}, #{v}, lsl #{sh.bits.toNat}"], lbl)
  | .push16 rs =>
    ([s!"  str {rs.asmName}, [sp, #-16]!"], lbl)
  | .pop16 rd =>
    ([s!"  ldr {rd.asmName}, [sp], #16"], lbl)
  | .drop16 =>
    (["  add sp, sp, #16"], lbl)
  | .ldrSlot16 rd slotIdx =>
    ([s!"  ldr {rd.asmName}, [sp, #{16 * slotIdx}]"], lbl)
  | .aluReg op rd rn rm =>
    ([s!"  {binOpMnemonic op} {rd.asmName}, {rn.asmName}, {rm.asmName}"], lbl)
  | .cbzBlock reg zCode nzCode =>
    let cur := lbl
    let zLbl := s!"L_narya_zero_{cur}"
    let endLbl := s!"L_narya_end_{cur}"
    let (nzLines, lbl1) := renderCodeAux (cur + 1) nzCode
    let (zLines, lbl2) := renderCodeAux lbl1 zCode
    let block :=
      [s!"  cbz {reg.asmName}, {zLbl}"] ++
      nzLines ++
      [s!"  b {endLbl}", s!"{zLbl}:"] ++
      zLines ++
      [s!"{endLbl}:"]
    (block, lbl2)
  | .loopX8 iters saveX8 bodyCode =>
    let cur := lbl
    let loopLbl := s!"L_narya_loop_{cur}"
    let endLbl := s!"L_narya_loop_end_{cur}"
    let (bodyLines, lbl1) := renderCodeAux (cur + 1) bodyCode
    let w0 := (iters &&& 0xFFFF).toNat
    let w1 := ((iters >>> 16) &&& 0xFFFF).toNat
    let w2 := ((iters >>> 32) &&& 0xFFFF).toNat
    let w3 := ((iters >>> 48) &&& 0xFFFF).toNat
    let savePre := if saveX8 then ["  str x8, [sp, #-16]!"] else []
    let savePost := if saveX8 then ["  ldr x8, [sp], #16"] else []
    let block :=
      [ s!"  movz x8, #{w0}"
      , s!"  movk x8, #{w1}, lsl #16"
      , s!"  movk x8, #{w2}, lsl #32"
      , s!"  movk x8, #{w3}, lsl #48"
      , s!"  cbz x8, {endLbl}"
      , s!"{loopLbl}:" ] ++
      savePre ++
      bodyLines ++
      savePost ++
      [ "  sub x8, x8, #1"
      , s!"  cbnz x8, {loopLbl}"
      , s!"{endLbl}:" ]
    (block, lbl1)

/-- Render a list of `Arm64Instr`s into assembly lines, threading `lbl`. -/
def renderCodeAux (lbl : Nat) : List Arm64Instr → List String × Nat
  | [] => ([], lbl)
  | i :: is =>
    let (l1, lbl1) := renderInstrAux lbl i
    let (l2, lbl2) := renderCodeAux lbl1 is
    (l1 ++ l2, lbl2)
end

/-- Render a complete `arm64-apple-darwin` Mach-O `.s` translation unit exporting `symName`
    (default `"_narya_entry"` for C symbol `narya_entry` on macOS). -/
def renderDarwinArm64Asm (instrs : List Arm64Instr) (symName : String := "_narya_entry") : String :=
  let (bodyLines, _) := renderCodeAux 0 instrs
  let header :=
    [ ".section __TEXT,__text,regular,pure_instructions"
    , s!".globl {symName}"
    , ".p2align 2"
    , s!"{symName}:" ]
  let footer :=
    [ "  ret"
    , "" ]
  String.intercalate "\n" (header ++ bodyLines ++ footer)

/-- Render a complete `aarch64-linux-gnu` ELF `.s` translation unit exporting `symName`
    (default `"narya_entry"` for C symbol `narya_entry` on Linux, including `.note.GNU-stack`). -/
def renderLinuxArm64Asm (instrs : List Arm64Instr) (symName : String := "narya_entry") : String :=
  let (bodyLines, _) := renderCodeAux 0 instrs
  let header :=
    [ ".text"
    , s!".global {symName}"
    , s!".type {symName}, %function"
    , ".p2align 2"
    , s!"{symName}:" ]
  let footer :=
    [ "  ret"
    , s!".size {symName}, .-{symName}"
    , ".section .note.GNU-stack,\"\",%progbits"
    , "" ]
  String.intercalate "\n" (header ++ bodyLines ++ footer)

/-- Render platform-appropriate `AArch64` assembly (`Mach-O` on macOS, `ELF` on Linux). -/
def renderNativeArm64Asm (instrs : List Arm64Instr) : String :=
  if System.Platform.isOSX then
    renderDarwinArm64Asm instrs "_narya_entry"
  else
    renderLinuxArm64Asm instrs "narya_entry"

/-- Render the minimal C AAPCS64 driver calling `narya_entry(arg0, arg1)` and printing the 64-bit unsigned result. -/
def renderCHarness (arg0 arg1 : UInt64) : String :=
  String.intercalate "\n"
    [ "#include <stdint.h>"
    , "#include <stdio.h>"
    , "#include <inttypes.h>"
    , ""
    , "extern uint64_t narya_entry(uint64_t a0, uint64_t a1);"
    , ""
    , "int main(void) {"
    , s!"  uint64_t res = narya_entry({arg0.toNat}ULL, {arg1.toNat}ULL);"
    , "  printf(\"%\" PRIu64 \"\\n\", res);"
    , "  return 0;"
    , "}"
    , "" ]

/-- Invoke the platform native `AArch64` C/assembly toolchain (`clang -arch arm64` on Darwin,
    `cc -O2` on Linux `aarch64`). -/
def compileNativeBinary (asmPath cPath binPath : System.FilePath) : IO (Except String Unit) := do
  if System.Platform.isOSX then
    let ccOut ← IO.Process.output {
      cmd := "/usr/bin/clang"
      args := #["-arch", "arm64", "-O2", asmPath.toString, cPath.toString, "-o", binPath.toString]
    }
    if ccOut.exitCode != 0 then
      return .error s!"clang -arch arm64 failed (exit {ccOut.exitCode}): {ccOut.stderr}"
    return .ok ()
  else
    let archOut ← IO.Process.output { cmd := "uname", args := #["-m"] }
    let arch := archOut.stdout.replace "\n" "" |>.replace "\r" "" |>.replace " " ""
    if arch != "aarch64" && arch != "arm64" then
      return .error s!"host architecture '{arch}' is not native AArch64"
    let ccOut ← IO.Process.output {
      cmd := "cc"
      args := #["-O2", asmPath.toString, cPath.toString, "-o", binPath.toString]
    }
    if ccOut.exitCode != 0 then
      return .error s!"cc -O2 failed (exit {ccOut.exitCode}): {ccOut.stderr}"
    return .ok ()

/-- **Cross-Platform `AArch64` Native Compiler & Runner (`compileAndRunNative`)**:
    1. Compiles `prog : HIR` through the verified `compileFullPipeline` (`HIR.opt → MIR → LIR → Arm64`)
    2. Emits genuine `arm64-apple-darwin` (Mach-O) or `aarch64-linux-gnu` (ELF) assembly & AAPCS64 C harness
    3. Links a native `AArch64` binary via `clang` / `cc`
    4. Runs on hardware, cleans up temporary files, and parses the live hardware `UInt64`! -/
def compileAndRunNative (prog : HIR) (arg0 arg1 : UInt64) : IO (Except String UInt64) := do
  let instrs := compileFullPipeline prog
  let asmSrc := renderNativeArm64Asm instrs
  let cSrc := renderCHarness arg0 arg1
  let nanos ← IO.monoNanosNow
  let stem := s!"/tmp/narya_arm64_{nanos}"
  let asmPath : System.FilePath := s!"{stem}.s"
  let cPath : System.FilePath := s!"{stem}.c"
  let binPath : System.FilePath := s!"{stem}_bin"
  try
    IO.FS.writeFile asmPath asmSrc
    IO.FS.writeFile cPath cSrc
    match ← compileNativeBinary asmPath cPath binPath with
    | .error err => return .error err
    | .ok () =>
      let runOut ← IO.Process.output {
        cmd := binPath.toString
        args := #[]
      }
      if runOut.exitCode != 0 then
        return .error s!"native binary failed (exit {runOut.exitCode}): {runOut.stderr}"
      let cleaned := runOut.stdout.replace "\n" "" |>.replace "\r" "" |>.replace " " ""
      match cleaned.toNat? with
      | some n => return .ok (UInt64.ofNat n)
      | none => return .error s!"unexpected native output: '{runOut.stdout}'"
  finally
    try IO.FS.removeFile asmPath catch _ => pure ()
    try IO.FS.removeFile cPath catch _ => pure ()
    try IO.FS.removeFile binPath catch _ => pure ()

end Arm64

end Narya.Compiler
