/-
  Narya.Compiler.Arm64 — Formal AArch64 ISA Semantics, Verified Codegen & Native Mach-O Runner

  Stage 4 (Final Stage) of Leonardo de Moura's SViL Nov 2026 "New Code Generator" pipeline:
    `Core.Term` ──▶ `HIR` ──(`HIR.opt`)──▶ `HIR` ──▶ `MIR` ──▶ `LIR` ──▶ `Arm64` (`.s` Mach-O)

  Features:
  1. **Formal 64-bit `AArch64` Register + Aligned-Stack Machine (`Arm64State`, `Arm64Instr`)**:
     Includes real 16-bit chunked `movz`/`movk` constant synthesis (proved exact for all
     64-bit `UInt64` words via `bv_decide`!), AAPCS64 register conventions (`x0..x3`, `sp`),
     and structured `cbz` conditional blocks.
  2. **End-to-End Machine-Checked Compiler Theorem (`compileFullPipeline_correct`, `zero sorry`)**:
     Proves that running the emitted `AArch64` machine code produces the **exact 64-bit `UInt64`**
     denotation of the source `HIR` program for ALL 64-bit inputs `(arg0, arg1)`!
  3. **Live Apple Silicon Mach-O Assembly Renderer & `clang` Execution (`compileAndRunNative`)**:
     Renders genuine `arm64-apple-darwin` `.s` assembly, invokes `/usr/bin/clang -arch arm64 -O2`
     with a minimal AAPCS64 C harness, executes natively on Apple Silicon hardware, and
     returns the live hardware `UInt64` result!
-/
import Std.Tactic.BVDecide
import Narya.Compiler.LIR

namespace Narya.Compiler

/-- General-purpose 64-bit `AArch64` registers used by the verified backend. -/
inductive Reg64 where
  | x0 -- Accumulator & AAPCS64 64-bit return register
  | x1 -- Scratch RHS/LHS register & AAPCS64 2nd argument on entry
  | x2 -- Saved AAPCS64 `arg0`
  | x3 -- Saved AAPCS64 `arg1`
  deriving DecidableEq, Repr, Inhabited

namespace Reg64

def asmName : Reg64 → String
  | .x0 => "x0"
  | .x1 => "x1"
  | .x2 => "x2"
  | .x3 => "x3"

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

/-- Verified subset of `AArch64` (`arm64-apple-darwin`) instructions. -/
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
  /-- Structured `cbz x0, L_zero` ... `b L_end` `L_zero:` ... `L_end:` block. -/
  | cbzBlock (reg : Reg64) (zeroCode : List Arm64Instr) (nonZeroCode : List Arm64Instr)
  deriving Repr, Inhabited

/-- Formal `AArch64` register file + 16-byte-aligned stack state. -/
structure Arm64State where
  x0 : UInt64 := 0
  x1 : UInt64 := 0
  x2 : UInt64 := 0
  x3 : UInt64 := 0
  stack : List UInt64 := []
  deriving DecidableEq, Repr, Inhabited

namespace Arm64State

@[inline]
def getReg (st : Arm64State) : Reg64 → UInt64
  | .x0 => st.x0
  | .x1 => st.x1
  | .x2 => st.x2
  | .x3 => st.x3

@[inline]
def setReg (st : Arm64State) (r : Reg64) (v : UInt64) : Arm64State :=
  match r with
  | .x0 => { st with x0 := v }
  | .x1 => { st with x1 := v }
  | .x2 => { st with x2 := v }
  | .x3 => { st with x3 := v }

/-- Initial AAPCS64 entry state when C calls `narya_entry(arg0, arg1)`! -/
def initABI (arg0 arg1 : UInt64) : Arm64State :=
  { x0 := arg0, x1 := arg1, x2 := 0, x3 := 0, stack := [] }

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

mutual
/-- Execute a single `Arm64Instr` on `st`. -/
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

/-- Execute a list of `Arm64Instr`s sequentially. -/
def exec : List Arm64Instr → Arm64State → Arm64State
  | [], st => st
  | i :: is, st => exec is (step st i)
end

@[simp]
theorem exec_append (c₁ c₂ : List Arm64Instr) (st : Arm64State) :
    exec (c₁ ++ c₂) st = exec c₂ (exec c₁ st) := by
  induction c₁ generalizing st with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.cons_append, exec]
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
  simp only [emitLoadImm64, exec, step, Arm64State.setReg, Arm64State.getReg]
  rw [movzk_reconstruct_u64 v]

mutual
/-- Lower a single `LIRInstr` into `Arm64Instr`s. -/
def emitInstr : LIRInstr → List Arm64Instr
  | .loadImm v => emitLoadImm64 v
  | .loadParam i =>
    if i.val == 0 then [.movReg .x0 .x2] else [.movReg .x0 .x3]
  | .loadSlot slot => [.ldrSlot16 .x0 slot]
  | .pushAcc => [.push16 .x0]
  | .popDrop => [.drop16]
  | .popBinOp op => [.pop16 .x1, .aluReg op .x0 .x1 .x0]
  | .condZero zBr nzBr =>
    [.cbzBlock .x0 (emitCode zBr) (emitCode nzBr)]

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

/-! ### `LIR → Arm64` Simulation Proof & End-to-End Correctness Theorem (`zero sorry`) -/

/-- State projection invariant relating `Arm64State` (with saved params `x2 = p₀, x3 = p₁`)
    to `LIRState`. -/
def MatchesLIR (p₀ p₁ : UInt64) (ast : Arm64State) (lst : LIRState) : Prop :=
  ast.x0 = lst.acc ∧ ast.x2 = p₀ ∧ ast.x3 = p₁ ∧ ast.stack = lst.stack

mutual
theorem step_simulates_lir (p₀ p₁ : UInt64) (instr : LIRInstr) :
    ∀ (ast : Arm64State) (lst : LIRState),
      MatchesLIR p₀ p₁ ast lst →
      MatchesLIR p₀ p₁ (exec (emitInstr instr) ast) (LIR.step p₀ p₁ lst instr) := by
  cases instr with
  | loadImm v =>
    intro ast lst ⟨_, hx2, hx3, hstk⟩
    simp [emitInstr, LIR.step, MatchesLIR, hx2, hx3, hstk]
  | loadParam i =>
    intro ast lst ⟨_, hx2, hx3, hstk⟩
    simp only [emitInstr, LIR.step]
    split <;> simp [exec, step, Arm64State.setReg, Arm64State.getReg, MatchesLIR, hx2, hx3, hstk]
  | loadSlot slot =>
    intro ast lst ⟨_, hx2, hx3, hstk⟩
    simp [emitInstr, exec, step, Arm64State.setReg, LIR.step, MatchesLIR, hx2, hx3, hstk]
  | pushAcc =>
    intro ast lst ⟨hx0, hx2, hx3, hstk⟩
    simp [emitInstr, exec, step, Arm64State.getReg, LIR.step, MatchesLIR, hx0, hx2, hx3, hstk]
  | popDrop =>
    intro ast lst ⟨hx0, hx2, hx3, hstk⟩
    simp [emitInstr, exec, step, LIR.step, MatchesLIR, hx0, hx2, hx3, hstk]
  | popBinOp op =>
    intro ast lst ⟨hx0, hx2, hx3, hstk⟩
    simp only [emitInstr, exec, step, LIR.step, hstk]
    cases hLst : lst.stack with
    | nil =>
      simp [Arm64State.setReg, Arm64State.getReg, MatchesLIR, hx0, hx2, hx3, hstk, hLst]
    | cons lhs rest =>
      simp [Arm64State.setReg, Arm64State.getReg, MatchesLIR, hx0, hx2, hx3]
  | condZero zBr nzBr =>
    intro ast lst hM
    rcases hM with ⟨hx0, hx2, hx3, hstk⟩
    simp only [emitInstr, exec, step, Arm64State.getReg, LIR.step, hx0]
    split
    · exact exec_simulates_lir p₀ p₁ zBr ast lst ⟨hx0, hx2, hx3, hstk⟩
    · exact exec_simulates_lir p₀ p₁ nzBr ast lst ⟨hx0, hx2, hx3, hstk⟩

theorem exec_simulates_lir (p₀ p₁ : UInt64) (code : List LIRInstr) :
    ∀ (ast : Arm64State) (lst : LIRState),
      MatchesLIR p₀ p₁ ast lst →
      MatchesLIR p₀ p₁ (exec (emitCode code) ast) (LIR.exec p₀ p₁ code lst) := by
  cases code with
  | nil =>
    intro ast lst hM
    exact hM
  | cons i rest =>
    intro ast lst hM
    simp only [emitCode, exec_append, LIR.exec]
    have hStep := step_simulates_lir p₀ p₁ i ast lst hM
    exact exec_simulates_lir p₀ p₁ rest (exec (emitInstr i) ast) (LIR.step p₀ p₁ lst i) hStep
end

/-- Prologue simulation: `emitFunction lir` saves AAPCS64 `(arg0, arg1)` into `(x2, x3)`
    and simulates `LIR.exec arg0 arg1 lir {}` starting from `{ x0 := arg0, stack := [] }`. -/
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
    simp [exec, step, Arm64State.initABI, Arm64State.setReg, Arm64State.getReg, MatchesLIR]
  exact exec_simulates_lir arg0 arg1 lirCode _ _ hPrologue

/-- **End-to-End Multi-IR Compiler Correctness Theorem (`compileFullPipeline_correct`, `0 sorry`)**:
    For **every** `HIR` program `prog` and **every** pair of 64-bit hardware arguments `(arg0, arg1)`,
    running the full multi-stage optimizing compiler (`HIR.opt → MIR.lowerFromHIR → LIR.lowerFromMIR → Arm64.emitFunction`)
    on the `AArch64` machine from `Arm64State.initABI arg0 arg1` leaves the **exact** source denotation
    `HIR.eval arg0 arg1 [] prog` in return register `x0`! -/
theorem compileFullPipeline_correct (prog : HIR) (arg0 arg1 : UInt64) :
    (exec (compileFullPipeline prog) (Arm64State.initABI arg0 arg1)).x0 =
      HIR.eval arg0 arg1 [] prog := by
  simp only [compileFullPipeline, LIR.lowerFromMIR]
  have hSim := emitFunction_simulates_lir arg0 arg1
    (LIR.compileAux [] 0 (MIR.lowerFromHIR (HIR.opt prog)))
  have hLIR := LIR.exec_compileAux arg0 arg1
    (MIR.lowerFromHIR (HIR.opt prog)) [] [] 0 { acc := arg0, stack := [] } LIR.envMatches_empty
  rw [hLIR] at hSim
  rcases hSim with ⟨hx0, _, _, _⟩
  rw [hx0, MIR.eval_lower_eq, HIR.eval_opt_eq]

/-- **AAPCS64 Stack Preservation Theorem (`compileFullPipeline_stack_clean`, `0 sorry`)**:
    Every compiled `AArch64` function returns with its hardware stack pointer `sp` completely
    restored (`stack = []`), guaranteeing zero stack leaks across arbitrary nested `let`s and branches! -/
theorem compileFullPipeline_stack_clean (prog : HIR) (arg0 arg1 : UInt64) :
    (exec (compileFullPipeline prog) (Arm64State.initABI arg0 arg1)).stack = [] := by
  simp only [compileFullPipeline, LIR.lowerFromMIR]
  have hSim := emitFunction_simulates_lir arg0 arg1
    (LIR.compileAux [] 0 (MIR.lowerFromHIR (HIR.opt prog)))
  have hLIR := LIR.exec_compileAux arg0 arg1
    (MIR.lowerFromHIR (HIR.opt prog)) [] [] 0 { acc := arg0, stack := [] } LIR.envMatches_empty
  rw [hLIR] at hSim
  exact hSim.2.2.2

/-! ### Genuine `arm64-apple-darwin` Mach-O Assembly Emitter & Live Apple Silicon Runner -/

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
/-- Render a single `Arm64Instr` into `arm64-apple-darwin` assembly lines, threading a fresh label counter `lbl`. -/
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

/-- **Live Apple Silicon Native Compiler & Runner (`compileAndRunNative`)**:
    1. Compiles `prog : HIR` through the verified `compileFullPipeline` (`HIR.opt → MIR → LIR → Arm64`)
    2. Emits genuine `arm64-apple-darwin` assembly (`_narya_entry`) and C AAPCS64 harness
    3. Invokes `/usr/bin/clang -arch arm64 -O2` to link a native Mach-O binary
    4. Runs the native Apple Silicon binary, cleans up temporary files, and parses the hardware `UInt64`! -/
def compileAndRunNative (prog : HIR) (arg0 arg1 : UInt64) : IO (Except String UInt64) := do
  let instrs := compileFullPipeline prog
  let asmSrc := renderDarwinArm64Asm instrs "_narya_entry"
  let cSrc := renderCHarness arg0 arg1
  let nanos ← IO.monoNanosNow
  let stem := s!"/tmp/narya_arm64_{nanos}"
  let asmPath : System.FilePath := s!"{stem}.s"
  let cPath : System.FilePath := s!"{stem}.c"
  let binPath : System.FilePath := s!"{stem}_bin"
  try
    IO.FS.writeFile asmPath asmSrc
    IO.FS.writeFile cPath cSrc
    let ccOut ← IO.Process.output {
      cmd := "/usr/bin/clang"
      args := #["-arch", "arm64", "-O2", asmPath.toString, cPath.toString, "-o", binPath.toString]
    }
    if ccOut.exitCode != 0 then
      return .error s!"clang -arch arm64 failed (exit {ccOut.exitCode}): {ccOut.stderr}"
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
