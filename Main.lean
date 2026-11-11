/-
  Main.lean — `narya` Command-Line Theorem Prover, Package Builder, Profiler, ThinEmitter JIT & Benchmark Suite

  Usage:
    lake exe narya catalog                                         -- List all 21 verified mode theories
    lake exe narya build [pkgDir] [--rebuild]                      -- Incremental Merkle DAG build (`stdlib` default)
    lake exe narya profile <file.ny> [--json f] [--folded f]       -- Nanosecond + allocation phase profiler & flamegraph
    lake exe narya run <file.ny>                                   -- Typecheck & evaluate a standalone `.ny` script
    lake exe narya eval [theory] "<expr>"                          -- Check & normalize an expression
    lake exe narya jit                                             -- Stream ARMv8-A machine code (`ThinEmitter`) & run via `MAP_JIT`
    lake exe narya asm                                             -- Emit verified AArch64 `.s` assembly & execute natively
    lake exe narya bench                                           -- 5-pillar performance & allocation benchmark suite
-/
import Narya

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core Narya.Syntax Narya.Elab
open Narya.Fast Narya.Compiler Narya.Compiler.ThinEmitter Narya.Meta Narya.Examples

def printUsage : IO Unit := do
  IO.println "Narya-Lean v0.3.0 — Multi-Modal Higher Observational Type Theory, Extensible .narya Syntax, Unison Digests & ThinEmitter JIT"
  IO.println ""
  IO.println "Commands:"
  IO.println "  lake exe narya catalog                                      List all 21 built-in 2-categorical mode theories"
  IO.println "  lake exe narya build [pkgDir] [--rebuild]                   Lake-style Merkle DAG build (.narya & .ny, default: stdlib)"
  IO.println "  lake exe narya hash [pkgDir|script]                         Compute Unison content-addressed (#impl, #spec, #abi) digests"
  IO.println "  lake exe narya translate <file.ny> [--out <file.narya>]     Translate legacy Lisp .ny source into clean Zero-Lisp .narya"
  IO.println "  lake exe narya profile <file.narya|.ny> [--json f] [--folded f] Phase + heap-allocation profiler & Flamegraph export"
  IO.println "  lake exe narya run <script.narya|.ny>                       Execute a standalone .narya or .ny proof/evaluation script"
  IO.println "  lake exe narya eval [theory] <expr>                         Typecheck and normalize a .narya or .ny expression"
  IO.println "  lake exe narya jit                                          In-process ThinEmitter ARMv8-A binary codegen + MAP_JIT"
  IO.println "  lake exe narya asm                                          Emit verified AArch64 .s assembly & run on hardware"
  IO.println "  lake exe narya bench                                        Run all 5 performance & allocation benchmark suites"

def cmdCatalog : IO UInt32 := do
  IO.println s!"Verified Narya Mode Theory Catalog ({standardCatalog.length} presentations, all wf = true):"
  IO.println "────────────────────────────────────────────────────────────────────────────────────"
  let mut idx := 1
  for T in standardCatalog do
    let modNames := String.intercalate ", " (T.modalities.map (fun g => s!"{g.name}:{g.dom}->{g.cod}[{reprStr g.flags.grade}]"))
    let cellNames := String.intercalate ", " (T.twoCells.map (fun c => c.name))
    let linTag := if T.linearModes.isEmpty then "" else s!", linear={T.linearModes}"
    IO.println s!"{idx}. {T.name} [default={T.defaultMode}, wf={T.wf}{linTag}]"
    IO.println s!"   modes      : {String.intercalate ", " T.modes}"
    IO.println s!"   modalities : {if modNames.isEmpty then "(identity only)" else modNames}"
    IO.println s!"   2-cells    : {if cellNames.isEmpty then "(identity only)" else cellNames} ({T.rules.length} rewrite rules)"
    idx := idx + 1
  return 0

def cmdRun (path : String) : IO UInt32 := do
  let fpath : System.FilePath := path
  let src ← IO.FS.readFile fpath
  -- Auto-hydrate any `import`ed sibling modules when running a file inside a package directory!
  let mut baseEnv := GlobalEnv.withStdPrelude pureHoTT
  let mut baseSyn := SyntaxEnv.standard
  let mut hasDeps := false
  if let some parentDir := fpath.parent then
    if let .ok deps := extractAnyImports src then
      if !deps.isEmpty then
        if let .ok dagUnits ← resolveModuleDAG parentDir deps then
          hasDeps := true
          for u in dagUnits do
            match runAnyScriptWithEnv baseEnv baseSyn u.source with
            | .ok (G', syn', _) =>
              baseEnv := G'
              baseSyn := syn'
            | .error err =>
              IO.eprintln s!"[import error in {u.path}] {err}"
              return 1
  let res :=
    if hasDeps then
      (runAnyScriptWithEnv baseEnv baseSyn src).map (fun (G, _, ls) => (G, ls))
    else
      runAnyScript pureHoTT src
  match res with
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
  match parseAnyTerm G SyntaxEnv.standard exprSrc with
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

/-- Extract `--flag <value>` from CLI argument list. -/
private def findFlagVal? (flag : String) : List String → Option String
  | [] => none
  | k :: v :: rest => if k == flag then some v else findFlagVal? flag (v :: rest)
  | [_] => none

/-- `lake exe narya translate <file.ny> [--out <file.narya>]` -/
def cmdTranslate (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "Usage: lake exe narya translate <file.ny> [--out <file.narya>]"
    return 1
  | inPath :: rest =>
    let nySrc ← IO.FS.readFile inPath
    match translateNyToModern nySrc with
    | .error err =>
      IO.eprintln s!"[translate error] {err}"
      return 1
    | .ok modernSrc =>
      match findFlagVal? "--out" rest with
      | some outPath =>
        IO.FS.writeFile outPath modernSrc
        IO.println s!"[translated] {inPath} -> {outPath}"
      | none =>
        IO.print modernSrc
      return 0

/-- `lake exe narya hash [pkgDir|script]` — Compute Unison content-addressed (#impl, #spec, #abi) digests! -/
def cmdHash (args : List String) : IO UInt32 := do
  let target : System.FilePath := args.head?.getD "stdlib"
  if ← (target / "narya.toml").pathExists then
    match ← buildPackage target (forceRebuild := false) with
    | .error err =>
      IO.eprintln s!"[hash build error] {err}"
      return 1
    | .ok res =>
      let digests ←
        if !res.defDigests.isEmpty then pure res.defDigests
        else
          match ← buildPackage target (forceRebuild := true) with
          | .ok r2 => pure r2.defDigests
          | .error _ => pure []
      IO.println (renderDigestsReport res.packageName digests)
      return 0
  else if ← target.pathExists then
    let src ← IO.FS.readFile target
    match runAnyScript pureHoTT src with
    | .error err =>
      IO.eprintln s!"[hash error] {err}"
      return 1
    | .ok (G, _) =>
      IO.println (renderDigestsReport target.toString (computeEnvDigests G))
      return 0
  else
    IO.eprintln s!"Target not found: {target}"
    return 1

/-- `lake exe narya build [pkgDir] [--rebuild]` — Lake-inspired Merkle DAG package builder! -/
def cmdBuild (rawArgs : List String) : IO UInt32 := do
  let forceRebuild := rawArgs.contains "--rebuild"
  let positional := rawArgs.filter (fun a => !a.startsWith "--")
  let pkgDir : System.FilePath := positional.head?.getD "stdlib"
  let t0 ← IO.monoNanosNow
  match ← buildPackage pkgDir forceRebuild with
  | .error err =>
    IO.eprintln s!"[build error] {err}"
    return 1
  | .ok res =>
    let wallUs := ((← IO.monoNanosNow) - t0) / 1000
    IO.println s!"=== Narya Package Build: {res.packageName} ({wallUs} µs total) ==="
    IO.println s!"  DAG order : {String.intercalate " -> " res.moduleOrder}"
    IO.println s!"  Status    : {res.rebuiltMods.length} built, {res.cachedMods.length} cached"
    for line in res.logs do
      IO.println s!"  {line}"
    if !res.emittedBins.isEmpty then
      IO.println s!"  Native ARM64 binaries ({res.emittedBins.length}):"
      for bp in res.emittedBins do
        IO.println s!"    • {bp}"
    if !res.defDigests.isEmpty then
      IO.println ""
      IO.println (renderDigestsReport res.packageName res.defDigests)
    IO.println ""
    IO.println (res.profile.renderReport s!"Build Telemetry: {res.packageName}")
    return 0

/-- `lake exe narya profile <file.narya|.ny> [--json out.json] [--folded out.folded]` -/
def cmdProfile (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "Usage: lake exe narya profile <file.narya|.ny> [--json <trace.json>] [--folded <stacks.folded>]"
    return 1
  | path :: rest =>
    -- If `path` imports sibling modules, hydrate its upstream DAG (`GlobalEnv` + `SyntaxEnv`) first!
    let fpath : System.FilePath := path
    let src ← IO.FS.readFile fpath
    let mut baseEnv := GlobalEnv.withStdPrelude pureHoTT
    let mut baseSyn := SyntaxEnv.standard
    if let some parentDir := fpath.parent then
      if let .ok deps := extractAnyImports src then
        if !deps.isEmpty then
          if let .ok dagUnits ← resolveModuleDAG parentDir deps then
            for u in dagUnits do
              if let .ok (G', syn', _) := runAnyScriptWithEnv baseEnv baseSyn u.source then
                baseEnv := G'
                baseSyn := syn'
    let profRef ← ProfileState.newRef
    match ← profileAnyScriptWithEnv profRef baseEnv baseSyn src path with
    | .error err =>
      IO.eprintln s!"[profile error] {err}"
      return 1
    | .ok (_, logs) =>
      for l in logs do
        IO.println l
      IO.println ""
      let st ← profRef.get
      IO.println (st.renderReport s!"Profile: {path}")
      if let some jsonOut := findFlagVal? "--json" rest then
        IO.FS.writeFile jsonOut st.exportChromeTraceJson
        IO.println s!"  [wrote Chrome Trace JSON] -> {jsonOut}"
      if let some foldedOut := findFlagVal? "--folded" rest then
        IO.FS.writeFile foldedOut st.exportFoldedFlamegraph
        IO.println s!"  [wrote Folded Flamegraph] -> {foldedOut}"
      return 0

/-- Format raw little-endian 32-bit ARMv8-A words as hex for inspection. -/
private def formatHexWords (bytes : ByteArray) : String := Id.run do
  let hex := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let u32Hex (w : UInt32) : String := Id.run do
    let mut cs : List Char := []
    let mut v := w
    for _ in [:8] do
      cs := (hex[(v &&& 0xF).toNat]?.getD '0') :: cs
      v := v >>> 4
    return "0x" ++ String.ofList cs
  let nWords := bytes.size / 4
  let mut ws : Array String := #[]
  for i in [:nWords] do
    let base := i * 4
    let b0 := (bytes[base]!).toUInt32
    let b1 := (bytes[base + 1]!).toUInt32
    let b2 := (bytes[base + 2]!).toUInt32
    let b3 := (bytes[base + 3]!).toUInt32
    let w : UInt32 := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
    ws := ws.push (u32Hex w)
  return String.intercalate " " ws.toList

/-- `lake exe narya jit` — In-process `ThinEmitter` ARMv8-A binary encoder + W^X `MAP_JIT` showcase! -/
def cmdJit : IO UInt32 := do
  IO.println "=== Narya ThinEmitter (Direct ARMv8-A Binary Codegen) + In-Process W^X MAP_JIT ==="
  let supported ← jitSupported
  IO.println s!"  Host AArch64 W^X JIT slab available: {supported}"
  let orbitBytes := thinCompileHIR collatzOrbit111HIR
  IO.println s!"  1. `collatzOrbit111HIR` ({orbitBytes.size} bytes, {orbitBytes.size / 4} ARMv8-A instructions):"
  IO.println s!"     words: {formatHexWords orbitBytes}"
  if supported then
    let r1 ← jitRunU64 orbitBytes 27 0
    IO.println s!"     MAP_JIT collatzOrbit111(27) => {r1} (expected 1)"
  let coreBytes := thinCompileCore tourProofCarryingCollatz
  IO.println s!"  2. `tourProofCarryingCollatz` (erased HoTT Glue univalence proof + 111-step loop, {coreBytes.size} bytes):"
  if supported then
    let t0 ← IO.monoNanosNow
    let mut checksum : UInt64 := 0
    for _ in [:200] do
      let v ← jitRunU64 (thinCompileCore tourProofCarryingCollatz) 27 0
      checksum := checksum + v
    let dtUs := ((← IO.monoNanosNow) - t0) / 1000
    IO.println s!"     200 full Core->HIR->MIR->LIR->Arm64->ByteArray->MAP_JIT runs: {dtUs} µs ({dtUs / 200} µs/run, checksum={checksum})"
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

@[noinline]
private def benchRefIsId {m n : DimCtx} (f : SFace m n) (salt : Nat) : Bool :=
  if salt == 999999999 then !f.isId else f.isId

@[noinline]
private def benchPackedIsId (pf : PackedSFace) (salt : Nat) : Bool :=
  let pf' : PackedSFace := { pf with endMask := pf.endMask &&& UInt64.ofNat (salt ||| 1) }
  pf'.isId

@[noinline]
private def benchLinearInetOnce (x : UInt64) : UInt64 × Nat × Nat × Nat :=
  let term : Term :=
    .app
      (.app
        (.lam "f" (ModPath.id "Lin")
          (.lam "z" (ModPath.id "Lin")
            (.app (.bvar 1) (ModPath.id "Lin") (.u64BinOp .add (.bvar 0) (.u64Lit 10)))))
        (ModPath.id "Lin")
        (.lam "y" (ModPath.id "Lin") (.u64BinOp .mul (.bvar 0) (.u64Lit 2))))
      (ModPath.id "Lin")
      (.u64Lit x)
  let (res, finNet) := INet.evalLinearTermU64 term 64
  (res.getD 0, finNet.interactions, finNet.fanCommutations, finNet.reductionGrows)

@[noinline]
private def benchThinCompileOrbit (extra : UInt64) : ByteArray :=
  if extra == 999999999 then thinCompileHIR mix64HIR else thinCompileHIR collatzOrbit111HIR

def cmdBench : IO UInt32 := do
  IO.println "╔════════════════════════════════════════════════════════════════════════════════╗"
  IO.println "║  Narya-Lean 5-Pillar Performance, Allocation & Native JIT Benchmark Suite     ║"
  IO.println "╚════════════════════════════════════════════════════════════════════════════════╝"

  -- Pillar 1: `PackedSFace` O(1) bitmask vs unary `SFace` GADT
  let rank := 16
  let iters := 200000
  let refFace := SFace.id (List.replicate rank Dir.hott)
  let packedFace : PackedSFace := PackedSFace.encode refFace
  let refTimed := timedRefIsId refFace
  let fastTimed := timedPackedIsId packedFace
  let t0 ← IO.monoNanosNow
  let mut accRef : UInt64 := 0
  for i in [0:iters] do
    if benchRefIsId refFace i then accRef := accRef + 1
  let t1 ← IO.monoNanosNow
  let mut accFast : UInt64 := 0
  for i in [0:iters] do
    if benchPackedIsId packedFace i then accFast := accFast + 1
  let t2 ← IO.monoNanosNow
  IO.println s!"[1. Cubical PackedSFace (rank={rank}, {iters} ops)]"
  IO.println s!"    TimeM formal ticks : Ref={refTimed.time} (O(d)) vs PackedU64={fastTimed.time} (O(1))"
  IO.println s!"    Wall-clock         : Ref={(t1 - t0) / 1000} µs (sum={accRef}) vs PackedU64={(t2 - t1) / 1000} µs (sum={accFast})"

  -- Pillar 2: Sorbet `FastGlobalTable` + 16-byte `PackedNode` `TermArena`
  let mut bigEnv := GlobalEnv.withStdPrelude pureHoTT
  for idx in [:128] do
    bigEnv := bigEnv.add (.ax s!"decl_{idx}" "M" (.uu 0))
  let fastTbl := FastGlobalTable.ofGlobalEnv bigEnv
  let targetSym := (fastTbl.syms.lookup? "decl_0").getD 0
  let g0 ← IO.monoNanosNow
  let mut hitsList : Nat := 0
  for _ in [:20000] do
    if (bigEnv.lookup? "decl_0").isSome then hitsList := hitsList + 1
  let g1 ← IO.monoNanosNow
  let mut hitsFast : Nat := 0
  for _ in [:20000] do
    if (fastTbl.lookupById? targetSym).isSome then hitsFast := hitsFast + 1
  let g2 ← IO.monoNanosNow

  let ar0 := TermArena.empty 512
  let (sA0, sy1) := ar0.syms.intern "arg0"
  let (sA1, sy2) := sy1.intern "arg1"
  let subDag : Term := .u64BinOp .add (.u64BinOp .mul (.global "arg0") (.u64Lit 3)) (.u64Lit 1)
  let fullDag : Term := .u64BinOp .add subDag subDag
  let (rootNid, arBuilt) := ({ ar0 with syms := sy2 }).internTerm fullDag
  let hA0 ← IO.getNumHeartbeats
  let a0Ns ← IO.monoNanosNow
  let mut arenaAcc : UInt64 := 0
  for i in [:50000] do
    arenaAcc := arenaAcc + arBuilt.evalU64 sA0 sA1 i.toUInt64 0 32 [] rootNid
  let a1Ns ← IO.monoNanosNow
  let hA1 ← IO.getNumHeartbeats
  IO.println s!"[2. Sorbet SymId Table & 16-Byte PackedNode TermArena]"
  IO.println s!"    20k Global lookups : String list={(g1 - g0) / 1000} µs ({hitsList}) vs O(1) SymId={(g2 - g1) / 1000} µs ({hitsFast})"
  IO.println s!"    50k Arena evalU64  : {(a1Ns - a0Ns) / 1000} µs (hcHits={arBuilt.hcHits}, allocs={hA1 - hA0}, sum={arenaAcc})"

  -- Pillar 3: Linear Interaction Nets (`0` DUP fans, `0` reduction grows!)
  let i0Ns ← IO.monoNanosNow
  let mut inetSum : UInt64 := 0
  let mut totalInteractions : Nat := 0
  let mut totalComms : Nat := 0
  let mut totalGrows : Nat := 0
  for i in [:5000] do
    let (v, steps, comms, grows) := benchLinearInetOnce i.toUInt64
    inetSum := inetSum + v
    totalInteractions := totalInteractions + steps
    totalComms := totalComms + comms
    totalGrows := totalGrows + grows
  let i1Ns ← IO.monoNanosNow
  IO.println s!"[3. Linear Interaction Net (Benton LNL grade `1`)]"
  IO.println s!"    5,000 reductions   : {(i1Ns - i0Ns) / 1000} µs | interactions={totalInteractions} | fanComms={totalComms} | arenaGrows={totalGrows} (sum={inetSum})"

  -- Pillar 4: `ThinEmitter` + In-Process `MAP_JIT` vs spawning `clang` subprocess!
  let c0Ns ← IO.monoNanosNow
  let clangRes ← Arm64.compileAndRunNative collatzOrbit111HIR 27 0
  let c1Ns ← IO.monoNanosNow
  let clangUs := (c1Ns - c0Ns) / 1000

  if (← jitSupported) then
    let j0Ns ← IO.monoNanosNow
    let mut jitSum : UInt64 := 0
    for i in [:200] do
      let code := benchThinCompileOrbit i.toUInt64
      jitSum := jitSum + (← jitRunU64 code 27 0)
    let j1Ns ← IO.monoNanosNow
    let perJitUs := Nat.max 1 ((j1Ns - j0Ns) / 200000)
    let speedup := clangUs / perJitUs
    IO.println s!"[4. ThinEmitter + W^X MAP_JIT vs `clang` Subprocess]"
    IO.println s!"    `clang` 1x run     : {clangUs} µs (res={clangRes.toOption})"
    IO.println s!"    ThinEmitter+JIT    : {(j1Ns - j0Ns) / 1000} µs for 200 compile+runs (~{perJitUs} µs/run, ~{speedup}x faster, sum={jitSum})"

  -- Pillar 5: 50,000-step SplitMix64 `HIR.eval` vs Native `MAP_JIT` AArch64 `cbnz x8` loop (`stackOps = 0`)!
  let l0Ns ← IO.monoNanosNow
  let seed : UInt64 := 123456789
  let salt : UInt64 := 0x0FEDCBA987654321
  let specLoop := HIR.eval seed salt [] iteratedMix64LoopHIR
  let l1Ns ← IO.monoNanosNow
  let stackOps := LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt iteratedMix64LoopHIR)))
  if (← jitSupported) then
    let loopCode := thinCompileHIR iteratedMix64LoopHIR
    let n0Ns ← IO.monoNanosNow
    let hwLoop ← jitRunU64 loopCode seed salt
    let n1Ns ← IO.monoNanosNow
    IO.println s!"[5. 50,000-Step SplitMix64 Loop (`cbnz x8`, stackOps={stackOps})]"
    IO.println s!"    HIR.eval interp    : {(l1Ns - l0Ns) / 1000} µs (checksum={specLoop})"
    IO.println s!"    MAP_JIT AArch64    : {(n1Ns - n0Ns) / 1000} µs (checksum={hwLoop}, exact match={hwLoop == specLoop})"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["catalog"] => cmdCatalog
  | "build" :: rest => cmdBuild rest
  | "hash" :: rest => cmdHash rest
  | "translate" :: rest => cmdTranslate rest
  | "profile" :: rest => cmdProfile rest
  | ["run", path] => cmdRun path
  | ["eval", expr] => cmdEval "pure_hott" expr
  | ["eval", th, expr] => cmdEval th expr
  | ["jit"] => cmdJit
  | ["asm"] => cmdAsm
  | ["bench"] => cmdBench
  | _ =>
    printUsage
    return 0
