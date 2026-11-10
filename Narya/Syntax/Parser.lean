/-
  Narya.Syntax.Parser — Standalone Surface Parser & Name Resolver for CLI `.ny` Scripts

  Supports human-readable S-expression / declaration scripts for `lake exe narya`,
  resolving named binders (`pi`, `lam`, `let`, `sig`) to De Bruijn indices and
  resolving modality / 2-cell names against the active `ModeTheory`!
-/
import Narya.Syntax.Pretty

namespace Narya.Syntax

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core

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

/-- Resolve a modality path string (e.g. `"id:M"`, `"L"`, `"R.L"`) in `T`. -/
def resolveModPath (T : ModeTheory) (defaultMode : ModeId) (raw : String) : Except String ModPath :=
  if raw == "_" || raw == "id" then
    .ok (ModPath.id defaultMode)
  else if raw.startsWith "id:" then
    .ok (ModPath.id (raw.drop 3).toString)
  else
    let parts := raw.splitOn "."
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
    | .atom "zero" => .ok (.ctor "Nat" "zero" [])
    | .atom "true" => .ok (.ctor "Bool" "true" [])
    | .atom "false" => .ok (.ctor "Bool" "false" [])
    | .atom "tt" => .ok (.ctor "Unit" "tt" [])
    | .atom ident =>
      match findLocalIx? locals ident with
      | some ix => .ok (.bvar ix)
      | none => .ok (.global ident)
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
    | .list [.atom "proj", subExp, .atom fld] => do
      let sub ← elaborateSExp fuel' T mode locals subExp
      .ok (.proj sub fld)
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
    | .list (fnExp :: argExps) => do
      let fn ← elaborateSExp fuel' T mode locals fnExp
      let args ← argExps.mapM (elaborateSExp fuel' T mode locals)
      let mp := ModPath.id mode
      .ok (args.foldl (fun acc a => .app acc mp a) fn)
    | .list [] => .error "Empty () expression"

/-- Parse a single surface expression string into a `Term`. -/
def parseTerm (G : GlobalEnv) (input : String) (mode : Option ModeId := none) : Except String Term := do
  let toks := tokenize input
  let (forms, rem) ← parseSExps (toks.length + 16) toks
  if !rem.isEmpty then .error s!"Unexpected trailing tokens: {rem}"
  match forms with
  | [one] => elaborateSExp 512 G.theory (mode.getD G.theory.defaultMode) [] one
  | _ => .error "Expected a single top-level expression"

/-- Execute a `.ny` command script, returning updated `GlobalEnv` and log lines. -/
def runScript (initTheory : ModeTheory := pureHoTT) (script : String) :
    Except String (GlobalEnv × List String) := do
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
      G ← addCheckedDef G name ty body .kinetic
      logs := logs ++ [s!"[def] {name} : {prettyTerm [] ty}"]
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

end Narya.Syntax
