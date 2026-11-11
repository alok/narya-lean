/-
  Main.lean — `narya` Command-Line Theorem Prover, Mode Catalog, Native ARM64 Emitter & Benchmark Suite

  Usage:
    lake exe narya catalog                 -- List all 20 verified first-class mode theories
    lake exe narya run <file.ny>           -- Typecheck & evaluate a standalone `.ny` script
    lake exe narya eval [theory] "<expr>"  -- Check & normalize an expression
    lake exe narya asm                     -- Emit verified Darwin ARM64 `.s` assembly & execute natively
    lake exe narya bench                   -- Benchmark PackedSFace & native ARM64 vs reference evaluators
-/
import Narya

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core Narya.Syntax Narya.Elab
open Narya.Fast Narya.Compiler Narya.Examples

def printUsage : IO Unit := do
  IO.println "Narya-Lean v0.1.0 — Multi-Modal Higher Observational Type Theory & Verified ARM64 Codegen"
  IO.println ""
  IO.println "Commands:"
  IO.println "  lake exe narya catalog                List all 20 built-in 2-categorical mode theories"
  IO.println "  lake exe narya run <script.ny>        Execute a standalone .ny proof/evaluation script"
  IO.println "  lake exe narya eval <expr>            Typecheck and normalize an expression in pureHoTT"
  IO.println "  lake exe narya eval <theory> <expr>   Typecheck and normalize in a named mode theory"
  IO.println "  lake exe narya asm                    Emit verified arm64-apple-darwin assembly & run on hardware"
  IO.println "  lake exe narya bench                  Run PackedSFace & native ARM64 performance benchmarks"

def cmdCatalog : IO UInt32 := do
  IO.println s!"Verified Narya Mode Theory Catalog ({standardCatalog.length} presentations, all wf = true):"
  IO.println "────────────────────────────────────────────────────────────────────────────────────"
  let mut idx := 1
  for T in standardCatalog do
    let modNames := String.intercalate ", " (T.modalities.map (fun g => s!"{g.name}:{g.dom}->{g.cod}"))
    let cellNames := String.intercalate ", " (T.twoCells.map (fun c => c.name))
    IO.println s!"{idx}. {T.name} [default={T.defaultMode}, wf={T.wf}]"
    IO.println s!"   modes      : {String.intercalate ", " T.modes}"
    IO.println s!"   modalities : {if modNames.isEmpty then "(identity only)" else modNames}"
    IO.println s!"   2-cells    : {if cellNames.isEmpty then "(identity only)" else cellNames} ({T.rules.length} rewrite rules)"
    idx := idx + 1
  return 0

def cmdRun (path : String) : IO UInt32 := do
  let src ← IO.FS.readFile path
  match runScript pureHoTT src with
  | .error err =>
    IO.eprintln s!"[error] {err}"
    return 1
  | .ok (_, logs) =>
    for line in logs do
      IO.println line
    return 0

def cmdEval (theoryName : String) (exprSrc : String) : IO UInt32 := do
  let T := (standardCatalog.find? (fun t => t.name == theoryName)).getD pureHoTT
  let G := GlobalEnv.withStdPrelude T
  match parseTerm G exprSrc with
  | .error err =>
    IO.eprintln s!"[parse error] {err}"
    return 1
  | .ok tm =>
    match synthClosed G tm with
    | .error err =>
      IO.eprintln s!"[type error] {err}"
      return 1
    | .ok (tm', tyVal) =>
      let nf := normalize G [] 0 tm'
      IO.println s!"term : {prettyTerm [] tm'}"
      IO.println s!"type : {prettyVal G tyVal}"
      IO.println s!"norm : {prettyTerm [] nf}"
      return 0

def cmdAsm : IO UInt32 := do
  IO.println "=== 1. Verified AArch64 Assembly for `collatzStepHIR` (zero-spill `x4..x7` + `n * 2 ↝ lsl #1`) ==="
  let collatzCode := Arm64.compileFullPipeline collatzStepHIR
  IO.println (Arm64.renderNativeArm64Asm collatzCode)
  for n in ([27, 82, 1024] : List UInt64) do
    let spec := HIR.eval n 0 [] collatzStepHIR
    match ← Arm64.compileAndRunNative collatzStepHIR n 0 with
    | .ok hw =>
      IO.println s!"  [Native AArch64] collatzStep({n}) = {hw}  (HIR spec = {spec}, match = {hw == spec})"
    | .error err =>
      IO.eprintln s!"  [Native execution skipped/failed]: {err}"
      return 1
  IO.println ""
  IO.println "=== 2. Verified AArch64 Hardware `cbnz x8` Loop for `collatzOrbit111HIR` (0 stack ops!) ==="
  let orbitCode := Arm64.compileFullPipeline collatzOrbit111HIR
  IO.println (Arm64.renderNativeArm64Asm orbitCode)
  let specOrbit := HIR.eval 27 0 [] collatzOrbit111HIR
  match ← Arm64.compileAndRunNative collatzOrbit111HIR 27 0 with
  | .ok hwOrbit =>
    IO.println s!"  [Native AArch64] collatzOrbit111(27) = {hwOrbit}  (HIR spec = {specOrbit}, match = {hwOrbit == specOrbit})"
  | .error err =>
    IO.eprintln s!"  [Native execution failed]: {err}"
    return 1
  IO.println ""
  IO.println "=== 3. Verified AArch64 Assembly for 64-Bit `mix64HIR` (`0xBF58476D1CE4E5B9` `movz`/`movk`) ==="
  let mixCode := Arm64.compileFullPipeline mix64HIR
  IO.println (Arm64.renderNativeArm64Asm mixCode)
  let a0 : UInt64 := 0x123456789ABCDEF0
  let a1 : UInt64 := 0x0FEDCBA987654321
  let specMix := HIR.eval a0 a1 [] mix64HIR
  match ← Arm64.compileAndRunNative mix64HIR a0 a1 with
  | .ok hwMix =>
    IO.println s!"  [Native AArch64] mix64(0x123456789ABCDEF0, 0x0FEDCBA987654321) = {hwMix}  (HIR spec = {specMix}, match = {hwMix == specMix})"
    return 0
  | .error err =>
    IO.eprintln s!"  [Native execution failed]: {err}"
    return 1

def cmdBench : IO UInt32 := do
  IO.println "=== Narya-Lean Performance & Cost Verification Benchmark ==="
  let rank := 16
  let iters := 200000
  let refFace := SFace.id (List.replicate rank Dir.hott)
  let packedFace : PackedSFace := PackedSFace.encode refFace

  -- 1. `TimeM` formal operational step comparison:
  let refTimed := timedRefIsId refFace
  let fastTimed := timedPackedIsId packedFace
  IO.println s!"[TimeM Formal Cost] rank-{rank} SFace.isId:"
  IO.println s!"  Reference unary GADT traversal : {refTimed.time} ticks (O(d), result={refTimed.ret})"
  IO.println s!"  Packed UInt64 bitmask check    : {fastTimed.time} tick  (O(1), result={fastTimed.ret}, proven via `packed_sface_isId_correct_and_faster`)"

  -- 2. Wall-clock measurement across `iters` iterations:
  let t0 ← IO.monoNanosNow
  let mut accRef : UInt64 := 0
  for i in [0:iters] do
    if (if i % 2 == 0 then refFace.isId else refFace.isId) then
      accRef := accRef + 1
  let t1 ← IO.monoNanosNow

  let mut accFast : UInt64 := 0
  for i in [0:iters] do
    let pf : PackedSFace := { packedFace with endMask := packedFace.endMask &&& UInt64.ofNat (i ||| 1) }
    if pf.isId then
      accFast := accFast + 1
  let t2 ← IO.monoNanosNow

  let refMs := (t1 - t0).toFloat / 1000000.0
  let fastMs := (t2 - t1).toFloat / 1000000.0
  IO.println s!"[Wall-Clock {iters} checks] Ref={refMs} ms (sum={accRef}) | PackedU64={fastMs} ms (sum={accFast})"

  -- 3. Native Register-Allocated Hardware `cbnz x8` Loop (`iteratedMix64LoopHIR`, 50,000 steps, 0 stack ops):
  let t3 ← IO.monoNanosNow
  let seed : UInt64 := 123456789 + UInt64.ofNat (t3 % 1)
  let salt : UInt64 := 0x0FEDCBA987654321
  let specLoop := HIR.eval seed salt [] iteratedMix64LoopHIR
  let t4 ← IO.monoNanosNow
  let hirMs := (t4 - t3).toFloat / 1000000.0
  let stackOps := LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt iteratedMix64LoopHIR)))
  IO.println s!"[HIR.eval 50,000-trip SplitMix64] {hirMs} ms (checksum={specLoop})"

  let loopInstrs := Arm64.compileFullPipeline iteratedMix64LoopHIR
  let asmSrc := Arm64.renderNativeArm64Asm loopInstrs
  let benchCSrc := String.intercalate "\n"
    [ "#include <stdint.h>"
    , "#include <stdio.h>"
    , "#include <inttypes.h>"
    , "#include <time.h>"
    , "extern uint64_t narya_entry(uint64_t a0, uint64_t a1);"
    , "int main(void) {"
    , "  struct timespec s, e;"
    , "  clock_gettime(CLOCK_MONOTONIC, &s);"
    , s!"  uint64_t acc = narya_entry({seed.toNat}ULL, {salt.toNat}ULL);"
    , "  clock_gettime(CLOCK_MONOTONIC, &e);"
    , "  double ms = (e.tv_sec - s.tv_sec) * 1000.0 + (e.tv_nsec - s.tv_nsec) / 1000000.0;"
    , "  printf(\"checksum=%\" PRIu64 \" native_ms=%.4f\\n\", acc, ms);"
    , "  return 0;"
    , "}" ]
  let nanos ← IO.monoNanosNow
  let stem := s!"/tmp/narya_bench_{nanos}"
  let asmP : System.FilePath := s!"{stem}.s"
  let cP : System.FilePath := s!"{stem}.c"
  let binP : System.FilePath := s!"{stem}_bin"
  try
    IO.FS.writeFile asmP asmSrc
    IO.FS.writeFile cP benchCSrc
    match ← Arm64.compileNativeBinary asmP cP binP with
    | .ok () =>
      let out ← IO.Process.output { cmd := binP.toString, args := #[] }
      IO.println s!"[Native AArch64 `cbnz x8` 50,000-trip loop (stackOps={stackOps})] {out.stdout.replace "\n" ""}"
    | .error err =>
      IO.eprintln s!"[Native bench skipped]: {err}"
  finally
    try IO.FS.removeFile asmP catch _ => pure ()
    try IO.FS.removeFile cP catch _ => pure ()
    try IO.FS.removeFile binP catch _ => pure ()
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["catalog"] => cmdCatalog
  | ["run", path] => cmdRun path
  | ["eval", expr] => cmdEval "pureHoTT" expr
  | ["eval", th, expr] => cmdEval th expr
  | ["asm"] => cmdAsm
  | ["bench"] => cmdBench
  | _ =>
    printUsage
    return 0
