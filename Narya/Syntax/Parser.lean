/-
  Narya.Syntax.Parser — Standalone Surface Parser, Safe Elaborator & Module Import Extractor

  Supports human-readable S-expression / declaration scripts for `lake exe narya`,
  resolving named binders (`pi`, `lam`, `let`, `record`, `funext`, `u64_repeat`) to De Bruijn
  indices, resolving modality / 2-cell names against the active `ModeTheory`, solving `?id`
  interactive holes via `Unify.unifyTerms`, and enforcing `Safety` + `Linear` checks!
-/
import Narya.Syntax.Pretty
import Narya.Core.Safety
import Narya.Core.Unify
import Narya.Core.Linear

namespace Narya.Syntax

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core
open Narya.Core.Safety Narya.Core.Unify Narya.Core.Linear

/-- S-expression token tree for standalone `.ny` scripts. -/
inductive SExp where
  | atom (s : String)
  | list (xs : List SExp)
  deriving BEq, Repr, Inhabited

/-- Tokenize an input string, stripping `-- ...` line comments. -/
def tokenize (input : String) : List String :=
  let cleanLines := (input.splitOn "\n").map fun line =>
    match line.splitOn "--" with
    | hd :: _ => hd
    | [] => ""
  let spaced := (String.intercalate " " cleanLines)
    |>.replace "(" " ( "
    |>.replace ")" " ) "
  (spaced.splitOn " ").filter (fun s => !s.isEmpty)

/-- Parse a token list into a list of top-level `SExp` forms. -/
def parseSExps (fuel : Nat) (toks : List String) : Except String (List SExp × List String) :=
  match fuel with
  | 0 => .error "Parser out of fuel"
  | fuel' + 1 =>
    match toks with
    | [] => .ok ([], [])
    | ")" :: rest => .ok ([], ")" :: rest)
    | "(" :: rest => do
      let (inner, afterInner) ← parseSExps fuel' rest
      match afterInner with
      | ")" :: tail =>
        let (more, rem) ← parseSExps fuel' tail
        .ok (.list inner :: more, rem)
      | _ => .error "Unclosed '(' in .ny script"
    | tok :: rest => do
      let (more, rem) ← parseSExps fuel' rest
      .ok (.atom tok :: more, rem)

/-- Kernel-reducible `"id:"` prefix stripper on `List Char`. -/
def stripIdPrefix : List Char → Option String
  | 'i' :: 'd' :: ':' :: rest => some (String.ofList rest)
  | _ => none

/-- Kernel-reducible character splitter on `List Char`. -/
def splitCharsAux (sep : Char) (acc : List Char) : List Char → List String
  | [] => [String.ofList acc.reverse]
  | c :: cs =>
    if c == sep then String.ofList acc.reverse :: splitCharsAux sep [] cs
    else splitCharsAux sep (c :: acc) cs

/-- Kernel-reducible `.`-splitter for modality path strings (`"R.L"` -> `["R", "L"]`). -/
def splitByDot (s : String) : List String :=
  splitCharsAux '.' [] s.toList

/-- Resolve a modality path string (e.g. `"id:M"`, `"L"`, `"R.L"`) in `T`. -/
def resolveModPath (T : ModeTheory) (defaultMode : ModeId) (raw : String) : Except String ModPath :=
  if strEq raw "_" || strEq raw "id" then
    .ok (ModPath.id defaultMode)
  else
    match stripIdPrefix raw.toList with
    | some mName => .ok (ModPath.id mName)
    | none =>
      let parts := splitByDot raw
      let rec buildSteps : List String → Except String (List ModGen)
        | [] => .ok []
        | p :: ps => do
          match T.findMod? p with
          | some g =>
            let rest ← buildSteps ps
            .ok (g :: rest)
          | none => .error s!"Unknown modality '{p}' in theory '{T.name}'"
      do
        let gs ← buildSteps parts
        match gs.head?, gs.getLast? with
        | some first, some last =>
          let mp : ModPath := { dom := last.dom, cod := first.cod, steps := gs }
          if mp.wf then .ok mp else .error s!"Non-composable modality path '{raw}'"
        | _, _ => .ok (ModPath.id defaultMode)

/-- Resolve a direction tag (`"hott"`, `"param"`, `"param3"`, `"disp"`, `"nom"`). -/
def resolveDir : String → Except String Dir
  | "hott" | "e" => .ok Dir.hott
  | "param" | "br" | "p" => .ok (Dir.param 2)
  | "param3" => .ok (Dir.param 3)
  | "disp" | "d" => .ok Dir.displayed
  | "nom" | "w" => .ok Dir.nominal
  | other => .error s!"Unknown direction '{other}'"

/-- Find De Bruijn index of `name` in local binder stack `locals`. -/
def findLocalIx? (locals : List String) (name : String) : Option Nat :=
  locals.findIdx? (· == name)

def resolveBinOp64 : String → Option BinOp64
  | "u64_add" => some .add
  | "u64_sub" => some .sub
  | "u64_mul" => some .mul
  | "u64_and" => some .bitAnd
  | "u64_or"  => some .bitOr
  | "u64_xor" => some .bitXor
  | "u64_shl" => some .shl
  | "u64_shr" => some .shr
  | _ => none

mutual
def elabRecordTele (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String) :
    List SExp → Except String (List FieldDecl)
  | [] => .ok []
  | .list [.atom fname, .atom modStr, ftyExp] :: rest =>
    match fuel with
    | 0 => .error "Elaborator out of fuel"
    | fuel' + 1 => do
      let mp ← resolveModPath T mode modStr
      let fty ← elaborateSExp fuel' T mp.dom locals ftyExp
      let rest' ← elabRecordTele fuel' T mode (fname :: locals) rest
      .ok ((fname, mp, fty) :: rest')
  | .list [.atom fname, ftyExp] :: rest =>
    match fuel with
    | 0 => .error "Elaborator out of fuel"
    | fuel' + 1 => do
      let mp := ModPath.id mode
      let fty ← elaborateSExp fuel' T mode locals ftyExp
      let rest' ← elabRecordTele fuel' T mode (fname :: locals) rest
      .ok ((fname, mp, fty) :: rest')
  | other :: _ => .error s!"Invalid record field declaration: {reprStr other}"

def elabTupleFields (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String) :
    List SExp → Except String (List (String × Term))
  | [] => .ok []
  | .list [.atom fname, valExp] :: rest =>
    match fuel with
    | 0 => .error "Elaborator out of fuel"
    | fuel' + 1 => do
      let v ← elaborateSExp fuel' T mode locals valExp
      let rest' ← elabTupleFields fuel' T mode locals rest
      .ok ((fname, v) :: rest')
  | other :: _ => .error s!"Invalid tuple field assignment: {reprStr other}"

/-- Desugar an `SExp` into a core `Term` under `T` and local binder stack `locals`. -/
def elaborateSExp (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String)
    (sexp : SExp) : Except String Term :=
  match fuel with
  | 0 => .error "Elaborator out of fuel"
  | fuel' + 1 =>
    match sexp with
    | .atom "Type" | .atom "UU" => .ok (.uu 0)
    | .atom "Type1" => .ok (.uu 1)
    | .atom "Type_ext" | .atom "UU_ext" => .ok (.uuExt 0)
    | .atom "U64" => .ok .u64Ty
    | .atom "zero" => .ok (.ctor "Nat" "zero" [])
    | .atom "true" => .ok (.ctor "Bool" "true" [])
    | .atom "false" => .ok (.ctor "Bool" "false" [])
    | .atom "tt" => .ok (.ctor "Unit" "tt" [])
    | .atom "Nat" => .ok (.dataTy "Nat" [])
    | .atom "Bool" => .ok (.dataTy "Bool" [])
    | .atom "Unit" => .ok (.dataTy "Unit" [])
    | .atom "Empty" => .ok (.dataTy "Empty" [])
    | .atom "?" => .ok (.mvar 0)
    | .atom ident =>
      match findLocalIx? locals ident with
      | some ix => .ok (.bvar ix)
      | none => .ok (.global ident)
    | .list [.atom "u64", .atom numStr] =>
      match numStr.toNat? with
      | some n => .ok (.u64Lit n.toUInt64)
      | none => .error s!"Invalid U64 literal '{numStr}'"
    | .list [.atom "?", .atom idStr] | .list [.atom "hole", .atom idStr] =>
      match idStr.toNat? with
      | some id => .ok (.mvar id)
      | none => .error s!"Invalid hole id '{idStr}'"
    | .list [.atom "Type", .atom lvlStr] =>
      match lvlStr.toNat? with
      | some l => .ok (.uu l)
      | none => .error s!"Invalid universe level '{lvlStr}'"
    | .list [.atom "succ", nExp] => do
      let n ← elaborateSExp fuel' T mode locals nExp
      .ok (.ctor "Nat" "succ" [n])
    | .list [.atom "pi", .atom x, .atom modStr, domExp, codExp] => do
      let mp ← resolveModPath T mode modStr
      let dom ← elaborateSExp fuel' T mp.dom locals domExp
      let cod ← elaborateSExp fuel' T mode (x :: locals) codExp
      .ok (.pi x mp dom cod)
    | .list [.atom "arrow", domExp, codExp] => do
      let mp := ModPath.id mode
      let dom ← elaborateSExp fuel' T mode locals domExp
      let cod ← elaborateSExp fuel' T mode ("_" :: locals) codExp
      .ok (.pi "_" mp dom cod)
    | .list [.atom "lam", .atom x, .atom modStr, bodyExp] => do
      let mp ← resolveModPath T mode modStr
      let body ← elaborateSExp fuel' T mode (x :: locals) bodyExp
      .ok (.lam x mp body)
    | .list [.atom "fun", .atom x, bodyExp] => do
      let mp := ModPath.id mode
      let body ← elaborateSExp fuel' T mode (x :: locals) bodyExp
      .ok (.lam x mp body)
    | .list [.atom "let", .atom x, tyExp, valExp, bodyExp] => do
      let ty ← elaborateSExp fuel' T mode locals tyExp
      let val ← elaborateSExp fuel' T mode locals valExp
      let body ← elaborateSExp fuel' T mode (x :: locals) bodyExp
      .ok (.letIn x ty val body)
    | .list [.atom "app_mod", fnExp, .atom modStr, argExp] => do
      let mp ← resolveModPath T mode modStr
      let fn ← elaborateSExp fuel' T mode locals fnExp
      let arg ← elaborateSExp fuel' T mp.dom locals argExp
      .ok (.app fn mp arg)
    | .list [.atom "box", .atom modStr, tyExp] => do
      let mp ← resolveModPath T mode modStr
      let ty ← elaborateSExp fuel' T mp.dom locals tyExp
      .ok (.modalBox mp ty)
    | .list [.atom "box_intro", .atom modStr, subExp] => do
      let mp ← resolveModPath T mode modStr
      let sub ← elaborateSExp fuel' T mp.dom locals subExp
      .ok (.boxIntro mp sub)
    | .list (.atom "record" :: fieldExps) => do
      let tele ← elabRecordTele fuel' T mode locals fieldExps
      .ok (.recordTy tele)
    | .list (.atom "tuple" :: fieldExps) => do
      let fs ← elabTupleFields fuel' T mode locals fieldExps
      .ok (.tuple fs)
    | .list [.atom "proj", subExp, .atom fld] => do
      let sub ← elaborateSExp fuel' T mode locals subExp
      .ok (.proj sub fld)
    | .list [.atom "funext", .atom x, bodyExp] => do
      let mp := ModPath.id mode
      let locals3 := (x ++ "2") :: (x ++ "1") :: (x ++ "0") :: locals
      let body ← elaborateSExp fuel' T mode locals3 bodyExp
      .ok (.funext Dir.hott mp body)
    | .list [.atom "hap", pfExp, a0Exp, a1Exp, paExp] => do
      let pf ← elaborateSExp fuel' T mode locals pfExp
      let a0 ← elaborateSExp fuel' T mode locals a0Exp
      let a1 ← elaborateSExp fuel' T mode locals a1Exp
      let pa ← elaborateSExp fuel' T mode locals paExp
      .ok (.hap Dir.hott pf a0 a1 pa)
    | .list [.atom "u64_ifz", cExp, zExp, nzExp] => do
      let c ← elaborateSExp fuel' T mode locals cExp
      let z ← elaborateSExp fuel' T mode locals zExp
      let nz ← elaborateSExp fuel' T mode locals nzExp
      .ok (.u64IfZero c z nz)
    | .list [.atom "u64_repeat", .atom cntStr, initExp, .atom accVar, stepExp] => do
      match cntStr.toNat? with
      | none => .error s!"Invalid u64_repeat count '{cntStr}'"
      | some cnt => do
        let init ← elaborateSExp fuel' T mode locals initExp
        let step ← elaborateSExp fuel' T mode (accVar :: locals) stepExp
        .ok (.u64Repeat cnt.toUInt64 init step)
    | .list (.atom "Id" :: tyExp :: endExps) => do
      let ty ← elaborateSExp fuel' T mode locals tyExp
      let ends ← endExps.mapM (elaborateSExp fuel' T mode locals)
      .ok (.obsEq Dir.hott ty ends)
    | .list (.atom "Br" :: tyExp :: endExps) => do
      let ty ← elaborateSExp fuel' T mode locals tyExp
      let ends ← endExps.mapM (elaborateSExp fuel' T mode locals)
      .ok (.obsEq (Dir.param 2) ty ends)
    | .list [.atom "Disp", tyExp, e₀Exp] => do
      let ty ← elaborateSExp fuel' T mode locals tyExp
      let e₀ ← elaborateSExp fuel' T mode locals e₀Exp
      .ok (.obsEq Dir.displayed ty [e₀])
    | .list [.atom "Fresh", tyExp] => do
      let ty ← elaborateSExp fuel' T mode locals tyExp
      .ok (.obsEq Dir.nominal ty [])
    | .list [.atom "refl", subExp] => do
      let sub ← elaborateSExp fuel' T mode locals subExp
      .ok (.refl Dir.hott sub)
    | .list [.atom "refl_dir", .atom gStr, subExp] => do
      let g ← resolveDir gStr
      let sub ← elaborateSExp fuel' T mode locals subExp
      .ok (.refl g sub)
    | .list [.atom "Glue", aExp, bExp, relExp] => do
      let a ← elaborateSExp fuel' T mode locals aExp
      let b ← elaborateSExp fuel' T mode locals bExp
      let r ← elaborateSExp fuel' T mode locals relExp
      .ok (.gel Dir.hott [a, b] r)
    | .list [.atom "Gel", aExp, bExp, relExp] => do
      let a ← elaborateSExp fuel' T mode locals aExp
      let b ← elaborateSExp fuel' T mode locals bExp
      let r ← elaborateSExp fuel' T mode locals relExp
      .ok (.gel (Dir.param 2) [a, b] r)
    | .list [.atom "trr", lineExp, xExp] => do
      let l ← elaborateSExp fuel' T mode locals lineExp
      let x ← elaborateSExp fuel' T mode locals xExp
      .ok (.trr Dir.hott l x)
    | .list [.atom "trl", lineExp, xExp] => do
      let l ← elaborateSExp fuel' T mode locals lineExp
      let x ← elaborateSExp fuel' T mode locals xExp
      .ok (.trl Dir.hott l x)
    | .list [.atom "liftr", lineExp, xExp] => do
      let l ← elaborateSExp fuel' T mode locals lineExp
      let x ← elaborateSExp fuel' T mode locals xExp
      .ok (.liftr Dir.hott l x)
    | .list [.atom "liftl", lineExp, xExp] => do
      let l ← elaborateSExp fuel' T mode locals lineExp
      let x ← elaborateSExp fuel' T mode locals xExp
      .ok (.liftl Dir.hott l x)
    | .list [.atom "sym", pExp] => do
      let p ← elaborateSExp fuel' T mode locals pExp
      .ok (.sym Dir.hott p)
    | .list [.atom "trans", pExp, qExp] => do
      let p ← elaborateSExp fuel' T mode locals pExp
      let q ← elaborateSExp fuel' T mode locals qExp
      .ok (.trans Dir.hott p q)
    | .list [.atom "arrow_line", dExp, cExp] => do
      let d ← elaborateSExp fuel' T mode locals dExp
      let c ← elaborateSExp fuel' T mode locals cExp
      .ok (.arrowLine Dir.hott (ModPath.id mode) d c)
    | .list [.atom "prod_line", .atom fN, .atom sN, fExp, sExp] => do
      let f ← elaborateSExp fuel' T mode locals fExp
      let s ← elaborateSExp fuel' T mode locals sExp
      .ok (.prodLine Dir.hott fN sN f s)
    | .list [.atom "box_line", .atom modStr, inExp] => do
      let mp ← resolveModPath T mode modStr
      let inner ← elaborateSExp fuel' T mp.dom locals inExp
      .ok (.boxLine Dir.hott mp inner)
    | .list [.atom opStr, lExp, rExp] =>
      match resolveBinOp64 opStr with
      | some bop => do
        let l ← elaborateSExp fuel' T mode locals lExp
        let r ← elaborateSExp fuel' T mode locals rExp
        .ok (.u64BinOp bop l r)
      | none => do
        let fn ← elaborateSExp fuel' T mode locals (.atom opStr)
        let a1 ← elaborateSExp fuel' T mode locals lExp
        let a2 ← elaborateSExp fuel' T mode locals rExp
        let mp := ModPath.id mode
        .ok (.app (.app fn mp a1) mp a2)
    | .list (fnExp :: argExps) => do
      let fn ← elaborateSExp fuel' T mode locals fnExp
      let args ← argExps.mapM (elaborateSExp fuel' T mode locals)
      let mp := ModPath.id mode
      .ok (args.foldl (fun acc a => .app acc mp a) fn)
    | .list [] => .error "Empty () expression"
end

/-- Parse a single surface expression string into a `Term`. -/
def parseTerm (G : GlobalEnv) (input : String) (mode : Option ModeId := none) : Except String Term := do
  let toks := tokenize input
  let (forms, rem) ← parseSExps (toks.length + 16) toks
  if !rem.isEmpty then .error s!"Unexpected trailing tokens: {rem}"
  match forms with
  | [one] => elaborateSExp 512 G.theory (mode.getD G.theory.defaultMode) [] one
  | _ => .error "Expected a single top-level expression"

/-- Strip optional surrounding double quotes `"foo"` -> `"foo"`. -/
def unquoteAtom (s : String) : String :=
  if s.startsWith "\"" && s.endsWith "\"" && s.length >= 2 then
    ((s.drop 1).dropEnd 1).toString
  else s

/-- Extract all `(import <module>)` dependencies from a `.ny` source file. -/
def extractImports (script : String) : Except String (List String) := do
  let toks := tokenize script
  let (forms, rem) ← parseSExps (toks.length + 32) toks
  if !rem.isEmpty then .error s!"Trailing tokens: {rem}"
  let mut deps : List String := []
  for form in forms do
    match form with
    | .list [.atom "import", .atom modName] =>
      let clean := unquoteAtom modName
      if !deps.contains clean then deps := deps ++ [clean]
    | _ => pure ()
  return deps

/-- Execute a `.ny` command script starting from an existing `GlobalEnv` `G0`,
    enforcing `Safety` (`addSafeCheckedDef`) and `Linear` (`checkLinearity`) invariants! -/
def runScriptWithEnv (G0 : GlobalEnv) (script : String) :
    Except String (GlobalEnv × List String) := do
  let toks := tokenize script
  let (forms, rem) ← parseSExps (toks.length + 32) toks
  if !rem.isEmpty then .error s!"Trailing tokens: {rem}"
  let mut G := G0
  let mut logs : List String := []
  for form in forms do
    match form with
    | .list [.atom "import", .atom modName] =>
      let _ := modName
      pure ()
    | .list [.atom "theory", .atom tName] =>
      match standardCatalog.find? (fun t => t.name == tName) with
      | some T' =>
        -- Preserve already-imported compatible definitions if theory matches, else reset prelude
        if G.theory.name == T'.name then
          logs := logs ++ [s!"[theory] active '{T'.name}' (default mode: {T'.defaultMode})"]
        else
          G := GlobalEnv.withStdPrelude T'
          logs := logs ++ [s!"[theory] switched to '{T'.name}' (default mode: {T'.defaultMode})"]
      | none => throw s!"Unknown standard mode theory '{tName}'"
    | .list [.atom "axiom", .atom name, tyExp] =>
      let m := G.theory.defaultMode
      let ty ← elaborateSExp 512 G.theory m [] tyExp
      let (ty', u) ← synthClosed G ty
      let _ ← ensureUniverse u
      G := G.add (.ax name m ty')
      logs := logs ++ [s!"[axiom] {name} : {prettyTerm [] ty'}"]
    | .list [.atom "def", .atom name, tyExp, bodyExp] =>
      let m := G.theory.defaultMode
      let ty ← elaborateSExp 512 G.theory m [] tyExp
      let body ← elaborateSExp 512 G.theory m [] bodyExp
      checkLinearity G.theory m body
      G ← addSafeCheckedDef G name ty body .kinetic
      logs := logs ++ [s!"[def] {name} : {prettyTerm [] ty}"]
    | .list [.atom "codef", .atom name, tyExp, bodyExp] =>
      let m := G.theory.defaultMode
      let ty ← elaborateSExp 512 G.theory m [] tyExp
      let body ← elaborateSExp 512 G.theory m [] bodyExp
      G ← addSafeCheckedDef G name ty body .potential
      logs := logs ++ [s!"[codef] {name} : {prettyTerm [] ty}"]
    | .list [.atom "solve", .atom holeIdStr, lhsExp, rhsExp] =>
      let m := G.theory.defaultMode
      let hid := holeIdStr.toNat?.getD 0
      let lhs ← elaborateSExp 512 G.theory m [] lhsExp
      let rhs ← elaborateSExp 512 G.theory m [] rhsExp
      let mc0 := MetaCtx.empty.addUnsolved hid (.uu 0) 0
      match unifyTerms G mc0 0 lhs rhs with
      | .equal mc1 =>
        match mc1.lookupSolutionTerm? hid with
        | some sol => logs := logs ++ [s!"[solve] ?{hid} := {prettyTerm [] sol}"]
        | none => logs := logs ++ [s!"[solve] unified (no binding needed for ?{hid})"]
      | .blocked b _ => throw s!"Unification blocked on metavariable ?{b}"
      | .notEqual => throw s!"Unification failed: terms are not convertible"
    | .list [.atom "check", tmExp] =>
      let m := G.theory.defaultMode
      let tm ← elaborateSExp 512 G.theory m [] tmExp
      let (tm', tyVal) ← synthClosed G tm
      logs := logs ++ [s!"[check] {prettyTerm [] tm'} : {prettyVal G tyVal}"]
    | .list [.atom "eval", tmExp] =>
      let m := G.theory.defaultMode
      let tm ← elaborateSExp 512 G.theory m [] tmExp
      let (tm', tyVal) ← synthClosed G tm
      let nf := normalize G [] 0 tm'
      logs := logs ++ [s!"[eval] {prettyTerm [] nf} : {prettyVal G tyVal}"]
    | other => throw s!"Unrecognized top-level command: {reprStr other}"
  return (G, logs)

/-- Execute a `.ny` command script from fresh `initTheory` prelude, preserving exact CLI behavior. -/
def runScript (initTheory : ModeTheory := pureHoTT) (script : String) :
    Except String (GlobalEnv × List String) := do
  -- Note: when starting fresh on `examples/univalence_and_modal.ny`, always log `(theory pure_hott)`!
  let toks := tokenize script
  let (forms, rem) ← parseSExps (toks.length + 32) toks
  if !rem.isEmpty then .error s!"Trailing tokens: {rem}"
  let mut G := GlobalEnv.withStdPrelude initTheory
  let mut logs : List String := []
  for form in forms do
    match form with
    | .list [.atom "theory", .atom tName] =>
      match standardCatalog.find? (fun t => t.name == tName) with
      | some T' =>
        G := GlobalEnv.withStdPrelude T'
        logs := logs ++ [s!"[theory] switched to '{T'.name}' (default mode: {T'.defaultMode})"]
      | none => throw s!"Unknown standard mode theory '{tName}'"
    | _ =>
      let singleToks :=
        match form with
        | .atom a => a
        | _ => ""
      let _ := singleToks
      -- Delegate all non-`theory` commands to a shared helper!
      let (G', ls) ← runSingleForm G form
      G := G'
      logs := logs ++ ls
  return (G, logs)
where
  runSingleForm (G : GlobalEnv) (form : SExp) : Except String (GlobalEnv × List String) := do
    let m := G.theory.defaultMode
    match form with
    | .list [.atom "import", _] => .ok (G, [])
    | .list [.atom "axiom", .atom name, tyExp] =>
      let ty ← elaborateSExp 512 G.theory m [] tyExp
      let (ty', u) ← synthClosed G ty
      let _ ← ensureUniverse u
      .ok (G.add (.ax name m ty'), [s!"[axiom] {name} : {prettyTerm [] ty'}"])
    | .list [.atom "def", .atom name, tyExp, bodyExp] =>
      let ty ← elaborateSExp 512 G.theory m [] tyExp
      let body ← elaborateSExp 512 G.theory m [] bodyExp
      checkLinearity G.theory m body
      let G' ← addSafeCheckedDef G name ty body .kinetic
      .ok (G', [s!"[def] {name} : {prettyTerm [] ty}"])
    | .list [.atom "codef", .atom name, tyExp, bodyExp] =>
      let ty ← elaborateSExp 512 G.theory m [] tyExp
      let body ← elaborateSExp 512 G.theory m [] bodyExp
      let G' ← addSafeCheckedDef G name ty body .potential
      .ok (G', [s!"[codef] {name} : {prettyTerm [] ty}"])
    | .list [.atom "solve", .atom holeIdStr, lhsExp, rhsExp] =>
      let hid := holeIdStr.toNat?.getD 0
      let lhs ← elaborateSExp 512 G.theory m [] lhsExp
      let rhs ← elaborateSExp 512 G.theory m [] rhsExp
      let mc0 := MetaCtx.empty.addUnsolved hid (.uu 0) 0
      match unifyTerms G mc0 0 lhs rhs with
      | .equal mc1 =>
        match mc1.lookupSolutionTerm? hid with
        | some sol => .ok (G, [s!"[solve] ?{hid} := {prettyTerm [] sol}"])
        | none => .ok (G, [s!"[solve] unified ?{hid}"])
      | .blocked b _ => .error s!"Unification blocked on metavariable ?{b}"
      | .notEqual => .error s!"Unification failed: terms are not convertible"
    | .list [.atom "check", tmExp] =>
      let tm ← elaborateSExp 512 G.theory m [] tmExp
      let (tm', tyVal) ← synthClosed G tm
      .ok (G, [s!"[check] {prettyTerm [] tm'} : {prettyVal G tyVal}"])
    | .list [.atom "eval", tmExp] =>
      let tm ← elaborateSExp 512 G.theory m [] tmExp
      let (tm', tyVal) ← synthClosed G tm
      let nf := normalize G [] 0 tm'
      .ok (G, [s!"[eval] {prettyTerm [] nf} : {prettyVal G tyVal}"])
    | other => .error s!"Unrecognized top-level command: {reprStr other}"

end Narya.Syntax
