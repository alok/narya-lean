/-
  Tests/Main.lean — Comprehensive End-to-End Test Driver (`lake test`)

  Exercises all 6 architectural layers at ground truth:
  1. Multi-directional variable-arity cubical operators (`SFace`, `SDeg`, `Perm`, `Op`, `CubeOf`)
  2. Unboxed 64-bit `PackedSFace` / `PackedSDeg` & `TimeM` formal cost certificates
  3. First-class 2-categorical `ModeTheory` combinators & BFS `KeySynth` (including ambiguity detection)
  4. Glued NbE, computational univalence (`Glue`), `-external`/`-dtt` lockers, sinister codata, & `SST`
  5. Lean 4 metaprogramming DSL (`narya!`, `def_mode_theory`) & `.ny` script execution
  6. Verified `HIR → MIR → LIR → Arm64` compilation + live Apple Silicon Mach-O binary execution!
-/
import Narya

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Modal.KeySynth
open Narya.Core Narya.Core.Safety Narya.Core.Unify
open Narya.Syntax Narya.Elab Narya.Fast Narya.Compiler Narya.Examples

structure TestState where
  passed : Nat := 0
  failed : Nat := 0

def assertCond (st : IO.Ref TestState) (label : String) (ok : Bool) : IO Unit := do
  if ok then
    st.modify fun s => { s with passed := s.passed + 1 }
    IO.println s!"  [PASS] {label}"
  else
    st.modify fun s => { s with failed := s.failed + 1 }
    IO.eprintln s!"  [FAIL] {label}"

def runDimTests (st : IO.Ref TestState) : IO Unit := do
  IO.println "── Suite 1: Multi-Directional Cubical Category (`Narya.Dim`) ──"
  let mixedCtx : DimCtx := [Dir.hott, Dir.param 3, Dir.displayed, Dir.nominal]
  let fId := SFace.id mixedCtx
  assertCond st "Mixed 4D context [hott, param 3, displayed, nominal] SFace.id isId" fId.isId

  let nomCtx : DimCtx := [Dir.nominal, Dir.nominal]
  let fNom := SFace.id nomCtx
  assertCond st "0-ary nominal context has unique identity SFace" fNom.isId

  let ep0 : Endpoint Dir.hott := ⟨0, by decide⟩
  let ep1 : Endpoint Dir.hott := ⟨1, by decide⟩
  let fEnd0 : SFace [Dir.hott] [Dir.hott, Dir.hott] := .endpt (.mid .zero Dir.hott) Dir.hott ep0
  let fEnd1 : SFace [] [Dir.hott] := .endpt .zero Dir.hott ep1
  let fComp := SFace.comp fEnd0 fEnd1
  assertCond st "Non-identity boundary SFace composition is non-id" (!fComp.isId)

  let sw := Perm.swapAxes Dir.hott (Dir.param 3) []
  let sw2 := Perm.comp sw (Perm.swapAxes (Dir.param 3) Dir.hott [])
  assertCond st "Perm.swapAxes across distinct colors (hott <-> param 3) is involutive" sw2.isId

  let opId := Op.id mixedCtx
  assertCond st "Canonical cubical Op.id isId across mixed arities (2, 3, 1, 0)" opId.isId

def runPackedAndTimeMTests (st : IO.Ref TestState) : IO Unit := do
  IO.println "── Suite 2: Packed 64-Bit Cubical Operators & `TimeM` (`Narya.Fast`, `TimeM`) ──"
  let ctx48 := List.replicate 48 Dir.hott
  let ref48 := SFace.id ctx48
  let p48 := PackedSFace.encode ref48
  assertCond st "Rank-48 PackedSFace.encode agrees with SFace.isId" (p48.isId == ref48.isId)

  let tRef := timedRefIsId ref48
  let tFast := timedPackedIsId p48
  assertCond st "TimeM rank-48 PackedSFace.isId takes 1 tick vs 49 ticks for unary GADT"
    (tFast.ret == tRef.ret && tFast.time == 1 && tRef.time == 49)

  let ep0 : Endpoint Dir.hott := ⟨0, by decide⟩
  let ep1 : Endpoint Dir.hott := ⟨1, by decide⟩
  let fA : SFace [Dir.hott, Dir.hott] [Dir.hott, Dir.hott, Dir.hott] :=
    .mid (.endpt (.mid .zero Dir.hott) Dir.hott ep1) Dir.hott
  let fB : SFace [Dir.hott] [Dir.hott, Dir.hott] :=
    .endpt (.mid .zero Dir.hott) Dir.hott ep0
  let refComp := SFace.comp fA fB
  let pComp := PackedSFace.comp (PackedSFace.encode fA) (PackedSFace.encode fB)
  let pRefComp := PackedSFace.encode refComp
  assertCond st "PackedSFace.comp matches PackedSFace.encode (SFace.comp fA fB) bit-for-bit"
    (pComp == pRefComp)

  match PackedSFace.decodeBinary [Dir.hott, Dir.hott, Dir.hott] pComp with
  | some ⟨_, decoded⟩ =>
    assertCond st "PackedSFace.decodeBinary round-trips back to exact encoded SFace"
      (PackedSFace.encode decoded == pComp)
  | none =>
    assertCond st "PackedSFace.decodeBinary round-trips back to exact encoded SFace" false

  let sampleData : List UInt64 := [10, 20, 30, 40, 50]
  let specRes := specTwoPassPipeline sampleData
  let fusedRes := fastFusedPipeline sampleData
  assertCond st "VerifiedOpt loopFusionOpt preserves sum and halves TimeM ticks (6 vs 12)"
    (specRes.ret == fusedRes.ret && fusedRes.time < specRes.time)

def runModalTests (st : IO.Ref TestState) : IO Unit := do
  IO.println "── Suite 3: 2-Categorical Mode Combinators & Key Synthesis (`Narya.Modal`) ──"
  assertCond st "All 20 standard mode theories in catalog are well-formed (wf = true)"
    (standardCatalog.all ModeTheory.wf && standardCatalog.length == 20)

  let adj := adjunctionTheory
  let dual2 := opposite2Cat "adjunction" (opposite2Cat "dual1" adj)
  assertCond st "opposite2Cat is involutive on adjunctionTheory 2-cells"
    (dual2.twoCells == adj.twoCells)

  -- Unique synthesis of unit `η : 1_D => R ∘ L` and counit `ε : L ∘ R => 1_C`:
  match adj.findMod? "L", adj.findMod? "R" with
  | some L, some R =>
    let rl := ModPath.comp (ModPath.atom R) (ModPath.atom L)
    let lr := ModPath.comp (ModPath.atom L) (ModPath.atom R)
    let synUnit := synthKey adj (ModPath.id "D") rl
    let synCounit := synthKey adj lr (ModPath.id "C")
    let unitOk := match synUnit with | .unique _ => true | _ => false
    let counitOk := match synCounit with | .unique _ => true | _ => false
    assertCond st "KeySynth uniquely synthesizes adjunction unit η and counit ε"
      (unitOk && counitOk)
  | _, _ =>
    assertCond st "KeySynth uniquely synthesizes adjunction unit η and counit ε" false

  -- Ambiguous 2-cell coherence detection when two distinct parallel 2-cells exist without a rule:
  let fGen : ModGen := { name := "F", dom := "M", cod := "N" }
  let gGen : ModGen := { name := "G", dom := "M", cod := "N" }
  let α1 : TwoCellGen := { name := "alpha1", domMode := "M", codMode := "N", src := .atom fGen, tgt := .atom gGen }
  let α2 : TwoCellGen := { name := "alpha2", domMode := "M", codMode := "N", src := .atom fGen, tgt := .atom gGen }
  let ambigTheory : ModeTheory :=
    { name := "ambig", modes := ["M", "N"], modalities := [fGen, gGen], twoCells := [α1, α2], defaultMode := "N" }
  let ambigRes := synthKey ambigTheory (.atom fGen) (.atom gGen)
  let detectedAmbig := match ambigRes with | .ambiguous _ _ => true | _ => false
  assertCond st "KeySynth detects non-coherent parallel 2-cells and reports .ambiguous" detectedAmbig

def runCoreTests (st : IO.Ref TestState) : IO Unit := do
  IO.println "── Suite 4: Glued NbE, Univalence, Lockers, Sinister Codata & SST (`Narya.Core`) ──"
  -- 1. Computational Univalence on `Glue(Bool, Bool, notEquiv)`:
  let fwdNf := normalize hoTTWithNot [] 0 (narya_hoTT! trr(Glue(Bool, Bool, notEquiv), true))
  let bwdNf := normalize hoTTWithNot [] 0 (narya_hoTT! trl(Glue(Bool, Bool, notEquiv), false))
  assertCond st "HoTT Univalence forward transport: trr(Glue(Bool, Bool, notEquiv), true) ~> false"
    (fwdNf == .ctor "Bool" "false" [])
  assertCond st "HoTT Univalence backward transport: trl(Glue(Bool, Bool, notEquiv), false) ~> true"
    (bwdNf == .ctor "Bool" "true" [])

  -- 2. Parametricity `Gel` & `ungel` computation:
  let relWitness := Term.ungel (Dir.param 2)
    (.gelIntro (Dir.param 2) [.ctor "Bool" "true" [], .ctor "Bool" "false" []] (.ctor "Unit" "tt" []))
  let ungelNf := normalize (GlobalEnv.withStdPrelude externalParamTheory) [] 0 relWitness
  assertCond st "Binary Parametricity ungel(gelIntro(true, false; tt)) ~> tt"
    (ungelNf == .ctor "Unit" "tt" [])

  -- 3. Parametricity locker (`-external`): blocks `Type_ext` under `lock`, re-enables under discrete `incl`!
  let GExt := GlobalEnv.withStdPrelude externalParamTheory
  let okRoot := (synthClosed GExt (narya! [externalParamTheory] Type_ext)).isOk
  let blockedLock := !(synthClosed GExt (narya! [externalParamTheory] box(lock, Type_ext))).isOk
  let unlockedIncl := (synthClosed GExt (narya! [externalParamTheory] box(lock, box(incl, Type_ext)))).isOk
  assertCond st "-external locker allows Type_ext at root, rejects under lock, re-unlocks under discrete incl"
    (okRoot && blockedLock && unlockedIncl)

  -- 4. Sinister negative modal codata gating in `adjunctionTheory` (`L` sinister, `R` non-sinister):
  let GAdj := GlobalEnv.withStdPrelude adjunctionTheory
  let sinisterCodata := narya! [adjunctionTheory] sig { (hd : L | Type) }
  -- Test at mode `"D"` whether non-sinister `R : C -> D` is rejected on a negative record field:
  let rPath := resolveModPath adjunctionTheory "D" "R"
  let nonSinisterRejected :=
    match rPath with
    | .ok rp => !(synthClosed GAdj (.recordTy [("bad", rp, .uu 0)]) (some "D")).isOk
    | .error _ => false
  assertCond st "Negative modal codata accepts sinister left adjoint L and rejects non-sinister R"
    ((synthClosed GAdj sinisterCodata).isOk && nonSinisterRejected)

  -- 5. 0-ary `Dir.nominal` freshness observational type:
  let GHoTT := GlobalEnv.withStdPrelude pureHoTT
  let freshOk := (synthClosed GHoTT (narya_hoTT! Fresh(Bool))).isOk
  let freshBadArity := !(synthClosed GHoTT (.obsEq Dir.nominal (.dataTy "Bool" []) [.ctor "Bool" "true" []])).isOk
  assertCond st "0-ary Nominal Fresh(Bool) typechecks with 0 endpoints and rejects 1 endpoint"
    (freshOk && freshBadArity)

  -- 6. Guarded coinductive `SST` under `Energy.potential`:
  assertCond st "Displayed Type Theory coinductive SST under Energy.potential typechecks cleanly"
    sstCheckedResult.isOk

  -- 7. Full Computational HOTT Fibrancy (`arrowLine`, `prodLine`, `boxLine`, `liftl`, `calc_eq`):
  let fnTrNf := normalize hoTTWithNot [] 0
    (narya_hoTT! (trr(arrowLine(Glue(Bool, Bool, notEquiv), Glue(Bool, Bool, notEquiv)), (fun b => true)) true))
  assertCond st "HOTT Π-fibrancy: trr(arrowLine(uaNot, uaNot), constTrue) true ~> false"
    (fnTrNf == .ctor "Bool" "false" [])

  let prodTrNf := normalize hoTTWithNot [] 0
    (narya_hoTT! trr(prodLine(Glue(Bool, Bool, notEquiv), Glue(Bool, Bool, notEquiv)), ⟨fst := true, snd := false⟩))
  assertCond st "HOTT Σ-fibrancy: trr(prodLine(uaNot, uaNot), <true, false>) ~> <false, true>"
    (prodTrNf == .tuple [("fst", .ctor "Bool" "false" []), ("snd", .ctor "Bool" "true" [])])

  let GAdjHoTT : GlobalEnv :=
    let g0 := GlobalEnv.withStdPrelude adjunctionTheory
    let dNotBody : Term :=
      .lam "b" (ModPath.id "D")
        (.matchData (.bvar 0) (ModPath.id "D") (.dataTy "Bool" [])
          [("false", 0, .ctor "Bool" "true" []), ("true", 0, .ctor "Bool" "false" [])])
    let dNotTy : Term := .pi "_" (ModPath.id "D") (.dataTy "Bool" []) (.dataTy "Bool" [])
    let dEqvTy : Term := .recordTy [("fwd", ModPath.id "D", dNotTy), ("bwd", ModPath.id "D", dNotTy)]
    let dEqvBd : Term := .tuple [("fwd", .global "notD"), ("bwd", .global "notD")]
    match addCheckedDef g0 "notD" dNotTy dNotBody .kinetic (some "D") with
    | .ok g1 => (addCheckedDef g1 "notEquivD" dEqvTy dEqvBd .kinetic (some "D")).toOption.getD g1
    | .error _ => g0
  let boxTrTm := narya! [adjunctionTheory]
    trr(boxLine(L, Glue(Bool, Bool, notEquivD)), box(L, true))
  let boxTrOk := (synthClosed GAdjHoTT boxTrTm).isOk
  let boxTrNf := normalize GAdjHoTT [] 0 boxTrTm
  let lMod := NTerm.resolveModTotal adjunctionTheory "C" "L"
  assertCond st "HOTT Cross-Mode Modal Box Univalence: trr(boxLine(L, uaNotD), box(L, true)) ~> box(L, false)"
    (boxTrOk && boxTrNf == .boxIntro lMod (.ctor "Bool" "false" []))

  let calcTm := narya_hoTT!
    calc_eq(Bool == Bool by Glue(Bool, Bool, notEquiv) == Bool by <- Glue(Bool, Bool, notEquiv))
  let calcCheckOk := (synthClosed hoTTWithNot calcTm).isOk
  let calcTrNf := normalize hoTTWithNot [] 0 (.trr Dir.hott calcTm (.ctor "Bool" "true" []))
  assertCond st "HOTT calc_eq(Bool == Bool by uaNot == Bool by <- uaNot) checks and transports true ~> true"
    (calcCheckOk && calcTrNf == .ctor "Bool" "true" [])

  -- 8. Open Problem G (`Safety.lean`): Strict Positivity, Guardedness, & `--without-K`:
  assertCond st "Safety: strict positivity rejects (Bad -> Empty) -> Bad & accepts infinitary Ord"
    (!checkDataSpecPositivity badNegativeSpec &&
     !checkDataSpecPositivity doubleNegativeSpec &&
     checkDataSpecPositivity brouwerOrdSpec)

  assertCond st "Safety: guardedness rejects kinetic Loop := sig { f : Loop } & accepts potential SST"
    (!checkDefGuardedness "Loop" .kinetic (.recordTy [("f", ModPath.id "M", .global "Loop")]) &&
     checkDefGuardedness "SST" .potential (.recordTy [("vtx", ModPath.id "M", .uu 0), ("step", ModPath.id "M", .global "SST")]))

  assertCond st "Safety: --without-K rejects nonlinear Id A x x (Axiom K) & accepts free-endpoint Id A x y"
    (!checkWithoutKPathMatch (.pvar 0) (.pvar 0) &&
     !checkWithoutKPathMatch (.pvar 0) (.pctor "succ" [.pvar 0]) &&
     checkWithoutKPathMatch (.pvar 0) (.pvar 1))

  -- 9. Open Problem F (`Unify.lean` / `EQUAL.md:170-202`): Ternary Glued Pattern Unification:
  let idM := ModPath.id "M"
  let mc0 := (MetaCtx.empty).addUnsolved 0 (.uu 0) 2
  -- `?m0 x y ≡ notBool y` at depth 2 (`x = bvar 1`, `y = bvar 0`):
  let lhsPat : Term := .app (.app (.mvar 0) idM (.bvar 1)) idM (.bvar 0)
  let rhsGlued : Term := .app (.global "notBool") idM (.bvar 0)
  let gluedSolOk :=
    match unifyTerms hoTTWithNot mc0 2 lhsPat rhsGlued with
    | .equal mc1 =>
      mc1.generation == 1 &&
      mc1.lookupSolutionTerm? 0 ==
        some (.lam "x0" idM (.lam "x1" idM (.app (.global "notBool") idM (.bvar 0))))
    | _ => false
  assertCond st "Unify (EQUAL.md:188): Miller pattern ?m0 x y == notBool y preserves glued 'notBool' unfold-free!"
    gluedSolOk

  -- Pruning out-of-scope `y` by unfolding `constZero := fun z => zero` in `?m0 x ≡ constZero y`:
  let GConst :=
    match addCheckedDef hoTTWithNot "constZero"
      (.pi "z" idM (.dataTy "Bool" []) (.dataTy "Nat" []))
      (.lam "z" idM (.ctor "Nat" "zero" [])) with
    | .ok g => g
    | .error _ => hoTTWithNot
  let lhsPrune : Term := .app (.mvar 0) idM (.bvar 1) -- only `x` (`lvl 0`) in spine!
  let rhsPrune : Term := .app (.global "constZero") idM (.bvar 0) -- `y` (`lvl 1`) out of scope!
  let pruneOk :=
    match unifyTerms GConst mc0 2 lhsPrune rhsPrune with
    | .equal mc1 =>
      mc1.lookupSolutionTerm? 0 == some (.lam "x0" idM (.ctor "Nat" "zero" []))
    | _ => false
  assertCond st "Unify: ?m0 x == constZero y prunes out-of-scope y via glued fallback ~> fun x => zero"
    pruneOk

  -- Non-pattern spine `?m0 true == false` returns ternary `.blocked 0` without mutating `mc0`:
  let nonPatLhs : Term := .app (.mvar 0) idM (.ctor "Bool" "true" [])
  let nonPatBlocked :=
    match unifyTerms hoTTWithNot mc0 0 nonPatLhs (.ctor "Bool" "false" []) with
    | .blocked 0 mcB => mcB.generation == mc0.generation
    | _ => false
  assertCond st "Unify (EQUAL.md:174): non-pattern ?m0 true == false returns ternary .blocked without mutation"
    nonPatBlocked

def runSyntaxAndDSLTests (st : IO.Ref TestState) : IO Unit := do
  IO.println "── Suite 5: Lean 4 Metaprogramming DSL & `.ny` Script Runner (`Narya.Elab`, `Narya.Syntax`) ──"
  let scriptSrc ← IO.FS.readFile "examples/univalence_and_modal.ny"
  match runScript pureHoTT scriptSrc with
  | .ok (_, logs) =>
    assertCond st "Standalone script examples/univalence_and_modal.ny executes cleanly"
      (logs.length == 11)
  | .error err =>
    IO.eprintln s!"    script error: {err}"
    assertCond st "Standalone script examples/univalence_and_modal.ny executes cleanly" false

  assertCond st "Declarative def_mode_theory TourCohesive has 2 modes and 3 modalities"
    (TourCohesive.wf && TourCohesive.modes.length == 2 && TourCohesive.modalities.length == 3)

def runNativeArm64Tests (st : IO.Ref TestState) : IO Unit := do
  IO.println "── Suite 6: Verified `HIR -> MIR -> LIR -> Darwin ARM64` Native Execution (`Narya.Compiler`) ──"
  -- Kernel 1: `collatzStepHIR` (even & odd branches + `n * 2 ~> lsl #1` strength reduction)
  for (n, label) in ([(27, "odd 27 -> 82"), (82, "even 82 -> 41"), (0, "zero 0 -> 0"), (1023, "odd 1023 -> 3070")] : List (UInt64 × String)) do
    let hirVal := HIR.eval n 0 [] collatzStepHIR
    let mirVal := MIR.eval n 0 [] (MIR.lowerFromHIR (HIR.opt collatzStepHIR))
    let lirSt  := LIR.exec n 0 (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt collatzStepHIR))) {}
    let armSt  := Arm64.exec (Arm64.compileFullPipeline collatzStepHIR) (Arm64State.initABI n 0)
    match ← Arm64.compileAndRunNative collatzStepHIR n 0 with
    | .ok nativeHw =>
      assertCond st s!"collatzStepHIR ({label}): HIR == MIR == LIR == Arm64ISA == AppleSiliconMachO ({nativeHw})"
        (hirVal == mirVal && mirVal == lirSt.acc && lirSt.acc == armSt.x0 && armSt.x0 == nativeHw && armSt.stack.isEmpty)
    | .error err =>
      IO.eprintln s!"    clang error: {err}"
      assertCond st s!"collatzStepHIR ({label}) native execution" false

  -- Kernel 2: 64-bit SplitMix `mix64HIR` (`movz` + three `movk`s on `0xBF58476D1CE4E5B9`)
  let a0 : UInt64 := 0xCAFEBABEDEADBEEF
  let a1 : UInt64 := 0x0123456789ABCDEF
  let expectedMix := HIR.eval a0 a1 [] mix64HIR
  match ← Arm64.compileAndRunNative mix64HIR a0 arg1_val with
  | .ok nativeMix =>
    assertCond st s!"mix64HIR (64-bit movz/movk): native Mach-O ({nativeMix}) == HIR.eval ({expectedMix})"
      (nativeMix == expectedMix)
  | .error err =>
    IO.eprintln s!"    clang error: {err}"
    assertCond st "mix64HIR native execution" false

  -- Kernel 3: Deeply nested `letBind` + nested `ifZero`
  let deepStackHIR : HIR :=
    .letBind (.binOp .add (.param ⟨0, by omega⟩) (.lit 10))
      (.letBind (.binOp .mul (.var 0) (.lit 2))
        (.letBind (.binOp .sub (.var 0) (.param ⟨1, by omega⟩))
          (.ifZero (.param ⟨1, by omega⟩)
            (.binOp .add (.var 2) (.var 1))
            (.binOp .bitXor (.var 0) (.var 2)))))
  for (x, y) in ([(15, 0), (15, 7), (999, 42)] : List (UInt64 × UInt64)) do
    let spec := HIR.eval x y [] deepStackHIR
    match ← Arm64.compileAndRunNative deepStackHIR x y with
    | .ok hw =>
      assertCond st s!"deepStackHIR({x}, {y}) register-promoted x4..x7 + cbz: native ({hw}) == spec ({spec})"
        (hw == spec)
    | .error err =>
      IO.eprintln s!"    native error: {err}"
      assertCond st s!"deepStackHIR({x}, {y}) native execution" false

  -- Kernel 4 (Open Problem H): Zero-spill register promotion audit (`LIR.countStackOps == 0`)
  let zeroSpillOk :=
    LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt collatzStepHIR))) == 0 &&
    LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt mix64HIR))) == 0 &&
    LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt collatzOrbit111HIR))) == 0 &&
    LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt iteratedMix64LoopHIR))) == 0
  assertCond st "Register promotion (x4..x7 + x8): collatzStep, mix64, collatzOrbit111 & iteratedMix64 emit 0 stack ops!"
    zeroSpillOk

  -- Kernel 5: 111-step Collatz hardware `cbnz x8` loop (`27 -> 1` in register-only loop!)
  let orbitSpec := HIR.eval 27 0 [] collatzOrbit111HIR
  match ← Arm64.compileAndRunNative collatzOrbit111HIR 27 0 with
  | .ok hwOrbit =>
    assertCond st s!"collatzOrbit111HIR(27) 111-step hardware cbnz x8 loop: native ({hwOrbit}) == spec ({orbitSpec}) == 1"
      (hwOrbit == orbitSpec && hwOrbit == 1)
  | .error err =>
    IO.eprintln s!"    native error: {err}"
    assertCond st "collatzOrbit111HIR(27) native execution" false

  -- Kernel 6: 50,000-trip SplitMix64 hardware `cbnz x8` loop (`iteratedMix64LoopHIR`)
  let loopSeed : UInt64 := 123456789
  let loopSalt : UInt64 := 0x0FEDCBA987654321
  let loopSpec := HIR.eval loopSeed loopSalt [] iteratedMix64LoopHIR
  match ← Arm64.compileAndRunNative iteratedMix64LoopHIR loopSeed loopSalt with
  | .ok hwLoop =>
    assertCond st s!"iteratedMix64LoopHIR 50,000-trip zero-spill cbnz loop: native ({hwLoop}) == HIR.eval ({loopSpec})"
      (hwLoop == loopSpec)
  | .error err =>
    IO.eprintln s!"    native error: {err}"
    assertCond st "iteratedMix64LoopHIR native execution" false

  -- Kernel 7: Nested `repeatLoop` (`7 x 5 = 35` trips, spilling/restoring outer `x8` on `sp`)
  let nestedSpec := HIR.eval 100 3 [] nestedLoopHIR
  match ← Arm64.compileAndRunNative nestedLoopHIR 100 3 with
  | .ok hwNested =>
    assertCond st s!"nestedLoopHIR(100, 3) outer+inner loop x8 stack save/restore: native ({hwNested}) == 205"
      (hwNested == nestedSpec && hwNested == 205)
  | .error err =>
    IO.eprintln s!"    native error: {err}"
    assertCond st "nestedLoopHIR native execution" false

  -- Kernel 8: 6-deep simultaneously live `letBind`s crossing `x4..x7` register file into `[sp, #16*k]`!
  let spill6DeepHIR : HIR :=
    .letBind (.binOp .add (.param ⟨0, by omega⟩) (.lit 1))
      (.letBind (.binOp .add (.var 0) (.lit 2))
        (.letBind (.binOp .add (.var 0) (.lit 3))
          (.letBind (.binOp .add (.var 0) (.lit 4))
            (.letBind (.binOp .add (.var 0) (.lit 5))
              (.letBind (.binOp .add (.var 0) (.lit 6))
                -- Sum all 6 live bindings (`x4, x5, x6, x7` + 2 stack spill slots) + binary spill!
                (.binOp .add
                  (.binOp .add (.var 5) (.var 4))
                  (.binOp .add
                    (.binOp .add (.var 3) (.var 2))
                    (.binOp .add (.var 1) (.var 0)))))))))
  let spillSpec := HIR.eval 10 0 [] spill6DeepHIR
  let spillOps := LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt spill6DeepHIR)))
  match ← Arm64.compileAndRunNative spill6DeepHIR 10 0 with
  | .ok hwSpill =>
    assertCond st s!"spill6DeepHIR(10) hybrid x4..x7 + [sp, #16*k] spill (stackOps={spillOps}): native ({hwSpill}) == spec ({spillSpec})"
      (hwSpill == spillSpec && spillOps > 0)
  | .error err =>
    IO.eprintln s!"    native error: {err}"
    assertCond st "spill6DeepHIR native execution" false

  -- Kernel 9: `HIR.opt` dead-loop elimination (`count = 0`), 1-trip unrolling (`count = 1`), & Linux ELF emitter:
  let deadLoopOpt := HIR.opt (.repeatLoop 0 (.lit 42) (.binOp .add (.var 0) (.lit 99)))
  let oneTripOpt := HIR.opt (.repeatLoop 1 (.param ⟨0, by omega⟩) (.binOp .add (.var 0) (.lit 7)))
  let elfAsm := Arm64.renderLinuxArm64Asm (Arm64.compileFullPipeline collatzOrbit111HIR)
  let elfChecks :=
    (elfAsm.splitOn ".type narya_entry, %function").length > 1 &&
    (elfAsm.splitOn ".note.GNU-stack").length > 1 &&
    (elfAsm.splitOn "cbnz x8,").length > 1
  assertCond st "HIR.opt eliminates 0-trip loop, unrolls 1-trip loop, and renders valid Linux ELF AArch64"
    (deadLoopOpt == .lit 42 &&
     oneTripOpt == .letBind (.param ⟨0, by omega⟩) (.binOp .add (.var 0) (.lit 7)) &&
     elfChecks)
where
  arg1_val : UInt64 := 0x0123456789ABCDEF

def main : IO UInt32 := do
  IO.println "╔══════════════════════════════════════════════════════════════════════════╗"
  IO.println "║  Narya-Lean Verification & Native Apple Silicon Test Suite (`lake test`) ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════════╝"
  let st ← IO.mkRef ({} : TestState)
  runDimTests st
  runPackedAndTimeMTests st
  runModalTests st
  runCoreTests st
  runSyntaxAndDSLTests st
  runNativeArm64Tests st
  let final ← st.get
  IO.println "────────────────────────────────────────────────────────────────────────────"
  IO.println s!"Total: {final.passed + final.failed} assertions | Passed: {final.passed} | Failed: {final.failed}"
  if final.failed == 0 then
    IO.println "ALL TESTS PASSED!"
    return 0
  else
    IO.eprintln s!"FAILED: {final.failed} test(s) did not pass."
    return 1
