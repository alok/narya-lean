/-
  Narya.Meta.Profiler — Hierarchical Nanosecond + Allocation Profiler & Flamegraph/Trace Exporter

  Modeled on Lean 4's `src/Lean/Util/Profiler.lean` + Nelson Elhage's Sorbet phase telemetry:
  1. **Dual Wall-Clock + Heap-Allocation Measurement**:
     Records both monotonic nanoseconds (`IO.monoNanosNow`) AND exact per-thread runtime small-heap
     allocation ticks (`IO.getNumHeartbeats`) across nested hierarchical spans!
  2. **Compiler & Runtime Domain Counters (`PerfCounters`)**:
     Tracks `arenaNodes`, `arenaHcHits`, `inetInteractions`, `inetFanComms`, `thinEmitBytes`,
     `jitRuns`, `cacheHits`, and `cacheMisses`.
  3. **Standard Industry Exporters**:
     - Aligned terminal hotspot summary table (`renderReport`)
     - Chrome `chrome://tracing` / Perfetto / Speedscope Trace Event JSON (`exportChromeTraceJson`)
     - Brendan Gregg collapsed stack Flamegraph `.folded` (`exportFoldedFlamegraph`)
-/
import Narya.Syntax.Parser
import Narya.Fast.Arena
import Narya.Fast.InteractionNet
import Narya.Compiler.ThinEmitter

namespace Narya.Meta

open Narya.Modal Narya.Modal.Combinators Narya.Core Narya.Core.Safety Narya.Core.Linear Narya.Core.Unify
open Narya.Syntax Narya.Fast Narya.Compiler Narya.Compiler.ThinEmitter

/-- Domain-specific architectural telemetry counters. -/
structure PerfCounters where
  arenaNodes       : Nat := 0
  arenaHcHits      : Nat := 0
  inetInteractions : Nat := 0
  inetFanComms     : Nat := 0
  thinEmitBytes    : Nat := 0
  jitRuns          : Nat := 0
  cacheHits        : Nat := 0
  cacheMisses      : Nat := 0
  deriving Repr, Inhabited

/-- A single completed hierarchical profiling span. -/
structure ProfileSpan where
  category   : String
  name       : String
  stackPath  : List String -- outermost-first stack path for folded flamegraphs
  startNs    : Nat
  durNs      : Nat
  allocTicks : Nat         -- `IO.getNumHeartbeats` delta (exact small-heap allocations!)
  deriving Repr, Inhabited

/-- Mutable profiler state threaded via `IO.Ref ProfileState`. -/
structure ProfileState where
  originNs    : Nat := 0
  activeStack : List String := []
  spans       : Array ProfileSpan := #[]
  counters    : PerfCounters := {}
  deriving Repr, Inhabited

namespace ProfileState

/-- Initialize a fresh `IO.Ref ProfileState` anchored at the current monotonic clock. -/
def newRef : IO (IO.Ref ProfileState) := do
  let now ← IO.monoNanosNow
  IO.mkRef { originNs := now }

/-- Opaque `@[noinline]` `IO` barrier preventing Lean's LCNF optimizer from hoisting
    pure computations across `IO.monoNanosNow` / `IO.getNumHeartbeats` boundaries! -/
@[noinline]
def runMeasuredPure {α : Type} (thunk : Unit → α) : IO α :=
  pure (thunk ())

/-- Measure a nested `IO` action under `(category, name)`, capturing exact wall-clock ns & heap allocs! -/
def withSpan {α : Type} (ref : IO.Ref ProfileState) (category name : String) (act : IO α) : IO α := do
  let stBefore ← ref.get
  let path := stBefore.activeStack ++ [s!"{category}:{name}"]
  ref.modify fun s => { s with activeStack := path }
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  try
    let res ← act
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    let span : ProfileSpan := {
      category := category
      name := name
      stackPath := path
      startNs := t0 - stBefore.originNs
      durNs := t1 - t0
      allocTicks := h1 - h0
    }
    ref.modify fun s => { s with activeStack := stBefore.activeStack, spans := s.spans.push span }
    return res
  catch e =>
    ref.modify fun s => { s with activeStack := stBefore.activeStack }
    throw e

/-- Convenience wrapper measuring a pure `Unit → α` thunk strictly inside `withSpan`. -/
def withSpanPure {α : Type} (ref : IO.Ref ProfileState) (category name : String) (thunk : Unit → α) : IO α :=
  withSpan ref category name (runMeasuredPure thunk)

/-- Escape a string for safe JSON emission. -/
private def jsonEscape (s : String) : String :=
  let s1 := s.replace "\\" "\\\\"
  let s2 := s1.replace "\"" "\\\""
  let s3 := s2.replace "\n" "\\n"
  s3.replace "\t" "\\t"

/-- Export spans in Chrome Trace Event Format (`chrome://tracing`, Perfetto UI, Speedscope)! -/
def exportChromeTraceJson (st : ProfileState) : String := Id.run do
  let mut events : Array String := #[]
  for sp in st.spans do
    -- Chrome Trace timestamps (`ts`, `dur`) are in float or integer microseconds; we emit integer µs + exact `dur_ns` in `args`!
    let tsUs := sp.startNs / 1000
    let durUs := Nat.max 1 (sp.durNs / 1000)
    let ev :=
      "{\"name\":\"" ++ jsonEscape sp.name ++ "\"," ++
      "\"cat\":\"" ++ jsonEscape sp.category ++ "\"," ++
      "\"ph\":\"X\"," ++
      s!"\"ts\":{tsUs},\"dur\":{durUs},\"pid\":1,\"tid\":1," ++
      s!"\"args\":\{\"dur_ns\":{sp.durNs},\"alloc_heartbeats\":{sp.allocTicks}}}"
    events := events.push ev
  let body := String.intercalate ",\n  " events.toList
  return "{\n  \"displayTimeUnit\": \"ms\",\n  \"traceEvents\": [\n  " ++ body ++ "\n  ]\n}\n"

/-- Export spans in Brendan Gregg `.folded` stack flamegraph format (`a;b;c <microseconds>`). -/
def exportFoldedFlamegraph (st : ProfileState) : String := Id.run do
  let mut lines : Array String := #[]
  for sp in st.spans do
    let stackStr := String.intercalate ";" sp.stackPath
    let us := Nat.max 1 (sp.durNs / 1000)
    lines := lines.push s!"{stackStr} {us}"
  return String.intercalate "\n" lines.toList ++ "\n"

/-- Right-pad a string to `width` spaces for clean aligned CLI tables. -/
private def padRight (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else s ++ String.ofList (List.replicate (width - s.length) ' ')

/-- Left-pad a string to `width` spaces for right-aligned numeric columns. -/
private def padLeft (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else String.ofList (List.replicate (width - s.length) ' ') ++ s

/-- Render a clean, human-readable terminal phase hotspot & allocation breakdown table! -/
def renderReport (st : ProfileState) (title : String := "Narya Phase & Allocation Profile") : String := Id.run do
  -- Aggregate top-level category totals
  let mut cats : List (String × Nat × Nat × Nat) := [] -- (cat, count, totalNs, totalAllocs)
  let mut grandNs : Nat := 0
  let mut grandAllocs : Nat := 0
  for sp in st.spans do
    -- Sum leaf / Depth-1 spans into grand total so nested spans aren't double-counted
    if sp.stackPath.length == 1 then
      grandNs := grandNs + sp.durNs
      grandAllocs := grandAllocs + sp.allocTicks
    let mut found := false
    let mut updated : List (String × Nat × Nat × Nat) := []
    for (c, cnt, ns, al) in cats do
      if c == sp.category then
        found := true
        updated := updated ++ [(c, cnt + 1, ns + sp.durNs, al + sp.allocTicks)]
      else
        updated := updated ++ [(c, cnt, ns, al)]
    if !found then
      updated := updated ++ [(sp.category, 1, sp.durNs, sp.allocTicks)]
    cats := updated

  -- Sort categories descending by `totalNs`
  let sortedCats := cats.toArray.qsort (fun (_, _, nsA, _) (_, _, nsB, _) => nsA > nsB)

  let mut out : Array String := #[]
  out := out.push s!"╔══════════════════════════════════════════════════════════════════════════════╗"
  out := out.push s!"║  {padRight title 74}  ║"
  out := out.push s!"╚══════════════════════════════════════════════════════════════════════════════╝"
  out := out.push "  Category            Spans      Wall Time (µs)     Share (%)    Heap Allocs"
  out := out.push "  ────────────────────────────────────────────────────────────────────────────"
  let denom := if grandNs == 0 then 1 else grandNs
  for (cat, cnt, ns, al) in sortedCats do
    let usStr := toString (ns / 1000) ++ "." ++ toString ((ns % 1000) / 100)
    let pctTenths := (ns * 1000) / denom
    let pctStr := s!"{pctTenths / 10}.{pctTenths % 10}%"
    let row :=
      "  " ++ padRight cat 18 ++
      padLeft (toString cnt) 7 ++
      padLeft usStr 18 ++
      padLeft pctStr 14 ++
      padLeft (toString al) 15
    out := out.push row
  out := out.push "  ────────────────────────────────────────────────────────────────────────────"
  let totalUs := s!"{grandNs / 1000}.{(grandNs % 1000) / 100}"
  out := out.push ("  " ++ padRight "TOTAL (top-level)" 18 ++
    padLeft (toString st.spans.size) 7 ++
    padLeft totalUs 18 ++
    padLeft "100.0%" 14 ++
    padLeft (toString grandAllocs) 15)
  let c := st.counters
  out := out.push ""
  out := out.push s!"  [Counters] Arena nodes={c.arenaNodes} (hash-cons hits={c.arenaHcHits}) | INet steps={c.inetInteractions} (fan-comms={c.inetFanComms})"
  out := out.push s!"             ThinEmitter bytes={c.thinEmitBytes} | MAP_JIT runs={c.jitRuns} | Build cache hits={c.cacheHits} misses={c.cacheMisses}"
  return String.intercalate "\n" out.toList

end ProfileState

/-! ## Instrumented `.ny` Script Runner (`profileScriptWithEnv`) -/

/-- Execute a `.ny` script with fine-grained phase spans, Sorbet `TermArena` interning,
    and automatic `ThinEmitter` + `MAP_JIT` compilation on erasable `U64` definitions! -/
def profileScriptWithEnv (prof : IO.Ref ProfileState) (G0 : GlobalEnv) (script : String)
    (modLabel : String := "<script>") : IO (Except String (GlobalEnv × List String)) := do
  ProfileState.withSpan prof "module" modLabel do
    let parsedRes ← ProfileState.withSpanPure prof "parse" modLabel fun () =>
      let toks := tokenize script
      parseSExps (toks.length + 32) toks
    match parsedRes with
    | .error e => return .error e
    | .ok (forms, rem) =>
      if !rem.isEmpty then return .error s!"Trailing tokens: {rem}"
      let mut G := G0
      let mut arena := TermArena.empty 256
      let mut logs : List String := []
      for form in forms do
        let m := G.theory.defaultMode
        match form with
        | .list [.atom "import", _] => pure ()
        | .list [.atom "theory", .atom tName] =>
          match standardCatalog.find? (fun t => t.name == tName) with
          | some T' =>
            if G.theory.name != T'.name then
              G := GlobalEnv.withStdPrelude T'
            logs := logs ++ [s!"[theory] '{T'.name}' (mode: {T'.defaultMode})"]
          | none => return .error s!"Unknown mode theory '{tName}'"

        | .list [.atom "axiom", .atom name, tyExp] =>
          let stepRes ← ProfileState.withSpanPure prof "typecheck" s!"axiom:{name}" fun () => do
            let ty ← elaborateSExp 512 G.theory m [] tyExp
            let (ty', u) ← synthClosed G ty
            let _ ← ensureUniverse u
            pure ty'
          match stepRes with
          | .error e => return .error e
          | .ok ty' =>
            G := G.add (.ax name m ty')
            logs := logs ++ [s!"[axiom] {name} : {prettyTerm [] ty'}"]

        | .list [.atom "def", .atom name, tyExp, bodyExp] =>
          let elabRes ← ProfileState.withSpanPure prof "elaborate" name fun () => do
            let ty ← elaborateSExp 512 G.theory m [] tyExp
            let body ← elaborateSExp 512 G.theory m [] bodyExp
            pure (ty, body)
          match elabRes with
          | .error e => return .error e
          | .ok (ty, body) =>
            -- 1. Intern in Sorbet flat `TermArena`
            let arena' ← ProfileState.withSpanPure prof "arena_intern" name fun () =>
              let (_, a1) := arena.internTerm ty
              let (_, a2) := a1.internTerm body
              a2
            let addedNodes := arena'.nodes.size - arena.nodes.size
            let addedHits := arena'.hcHits - arena.hcHits
            arena := arena'
            prof.modify fun s =>
              { s with counters := { s.counters with
                  arenaNodes := s.counters.arenaNodes + addedNodes
                  arenaHcHits := s.counters.arenaHcHits + addedHits } }

            -- 2. Check QTT linearity + guardedness + kernel bidirectional check
            let chkRes ← ProfileState.withSpanPure prof "typecheck" name fun () => do
              checkLinearity G.theory m body
              addSafeCheckedDef G name ty body .kinetic
            match chkRes with
            | .error e => return .error e
            | .ok G' =>
              G := G'
              logs := logs ++ [s!"[def] {name} : {prettyTerm [] ty}"]
              -- 3. If `ErasableCore [] body`, automatically ThinEmit + verify via `MAP_JIT`!
              if ErasableCore [] body then
                let code ← ProfileState.withSpanPure prof "thin_emit" name fun () =>
                  thinCompileCore body
                prof.modify fun s =>
                  { s with counters := { s.counters with thinEmitBytes := s.counters.thinEmitBytes + code.size } }
                if (← jitSupported) then
                  let jitVal ← ProfileState.withSpan prof "jit_exec" name do
                    jitRunU64 code 27 0
                  prof.modify fun s =>
                    { s with counters := { s.counters with jitRuns := s.counters.jitRuns + 1 } }
                  logs := logs ++ [s!"[jit] {name}(27, 0) => {jitVal} ({code.size} ARM64 bytes)"]

        | .list [.atom "codef", .atom name, tyExp, bodyExp] =>
          let chkRes ← ProfileState.withSpanPure prof "typecheck" s!"codef:{name}" fun () => do
            let ty ← elaborateSExp 512 G.theory m [] tyExp
            let body ← elaborateSExp 512 G.theory m [] bodyExp
            addSafeCheckedDef G name ty body .potential
          match chkRes with
          | .error e => return .error e
          | .ok G' =>
            G := G'
            logs := logs ++ [s!"[codef] {name}"]

        | .list [.atom "solve", .atom holeIdStr, lhsExp, rhsExp] =>
          let solRes ← ProfileState.withSpanPure prof "unify" s!"?{holeIdStr}" fun () => do
            let hid := holeIdStr.toNat?.getD 0
            let lhs ← elaborateSExp 512 G.theory m [] lhsExp
            let rhs ← elaborateSExp 512 G.theory m [] rhsExp
            let mc0 := MetaCtx.empty.addUnsolved hid (.uu 0) 0
            match unifyTerms G mc0 0 lhs rhs with
            | .equal mc1 =>
              match mc1.lookupSolutionTerm? hid with
              | some sol => .ok s!"[solve] ?{hid} := {prettyTerm [] sol}"
              | none => .ok s!"[solve] unified ?{hid}"
            | .blocked b _ => .error s!"Blocked on ?{b}"
            | .notEqual => .error s!"Unification failed: terms are not convertible"
          match solRes with
          | .error e => return .error e
          | .ok line => logs := logs ++ [line]

        | .list [.atom "check", tmExp] =>
          let cRes ← ProfileState.withSpanPure prof "typecheck" "check_cmd" fun () => do
            let tm ← elaborateSExp 512 G.theory m [] tmExp
            let (tm', tyVal) ← synthClosed G tm
            pure s!"[check] {prettyTerm [] tm'} : {prettyVal G tyVal}"
          match cRes with
          | .error e => return .error e
          | .ok line => logs := logs ++ [line]

        | .list [.atom "eval", tmExp] =>
          let eRes ← ProfileState.withSpanPure prof "nbe_eval" "eval_cmd" fun () => do
            let tm ← elaborateSExp 512 G.theory m [] tmExp
            let (tm', tyVal) ← synthClosed G tm
            let nf := normalize G [] 0 tm'
            pure s!"[eval] {prettyTerm [] nf} : {prettyVal G tyVal}"
          match eRes with
          | .error e => return .error e
          | .ok line => logs := logs ++ [line]

        | other => return .error s!"Unrecognized top-level command: {reprStr other}"
      return .ok (G, logs)

end Narya.Meta
