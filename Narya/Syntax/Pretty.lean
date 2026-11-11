/-
  Narya.Syntax.Pretty — Familiar Lean-Style Pretty-Printer for Narya Terms & Values

  Formats De Bruijn `Term`s and semantic `Val`s using human-readable bound variable
  names, modal annotations `(x : μ | A) → B`, and familiar higher-observational
  constructors (`Id`, `Br`, `Disp`, `Fresh`, `Gel`, `Glue`, `trr`, `trl`, `refl`).
-/
import Narya.Core

namespace Narya.Syntax

open Narya.Dim Narya.Modal Narya.Core

/-- Render a `Dir` prefix nicely (`Id` for HoTT, `Br` for binary param, `Disp` for dTT, `Fresh` for nominal). -/
def prettyObsHead : Dir → String
  | { name := "e", arity := 2, fibrant := true, .. } => "Id"
  | { name := "p", arity := 2, fibrant := false, .. } => "Br"
  | { name := "d", arity := 1, .. } => "Disp"
  | { name := "w", arity := 0, .. } => "Fresh"
  | g => s!"Obs[{g.name}/{g.arity}]"

mutual

def prettyTeleFields (names : List String) : List (String × ModPath × Term) → List String
  | [] => []
  | (fname, fmod, fty) :: rest =>
    let tyStr := prettyTerm names fty
    let hdr :=
      if fmod.steps.isEmpty then s!"{fname} : {tyStr}"
      else s!"({fname} : {fmod.pretty} | {tyStr})"
    hdr :: prettyTeleFields (fname :: names) rest

def prettyTupleItems (names : List String) : List (String × Term) → List String
  | [] => []
  | (fname, ftm) :: rest =>
    s!"{fname} := {prettyTerm names ftm}" :: prettyTupleItems names rest

def prettyList (names : List String) : List Term → List String
  | [] => []
  | t :: ts => prettyTerm names t :: prettyList names ts

def prettyBranches (names : List String) : List (String × Nat × Term) → List String
  | [] => []
  | (cn, ar, bd) :: rest =>
    let bVars := (List.range ar).map (fun i => s!"y{i}")
    let s := s!"| {cn} {String.intercalate " " bVars} => {prettyTerm (bVars.reverse ++ names) bd}"
    s :: prettyBranches names rest

/-- Pretty-print a `Term` under De Bruijn binder name stack `names` (`names[0]` = index 0). -/
def prettyTerm (names : List String) : Term → String
  | .bvar ix =>
    match names[ix]? with
    | some n => n
    | none => s!"#{ix}"
  | .mvar id => s!"?m{id}"
  | .global n => n
  | .uu 0 => "Type"
  | .uu l => s!"Type {l}"
  | .uuExt 0 => "Type_ext"
  | .uuExt l => s!"Type_ext {l}"
  | .pi x mod dom cod =>
    let xFresh := if names.contains x then s!"{x}_{names.length}" else x
    let domStr := prettyTerm names dom
    let codStr := prettyTerm (xFresh :: names) cod
    if mod.steps.isEmpty then s!"({xFresh} : {domStr}) → {codStr}"
    else s!"({xFresh} : {mod.pretty} | {domStr}) → {codStr}"
  | .lam x mod body =>
    let xFresh := if names.contains x then s!"{x}_{names.length}" else x
    let bodyStr := prettyTerm (xFresh :: names) body
    if mod.steps.isEmpty then s!"(fun {xFresh} => {bodyStr})"
    else s!"(fun ({xFresh} : {mod.pretty}) => {bodyStr})"
  | .app fn mod arg =>
    let fnStr := prettyTerm names fn
    let argStr := prettyTerm names arg
    if mod.steps.isEmpty then s!"({fnStr} {argStr})"
    else s!"({fnStr} ({argStr} @ {mod.pretty}))"
  | .letIn x ty val body =>
    let xFresh := if names.contains x then s!"{x}_{names.length}" else x
    s!"(let {xFresh} : {prettyTerm names ty} := {prettyTerm names val}; {prettyTerm (xFresh :: names) body})"
  | .key cell sub =>
    s!"({prettyTerm names sub} #{cell.pretty})"
  | .modalBox mod ty =>
    s!"⟨{mod.pretty} | {prettyTerm names ty}⟩"
  | .boxIntro mod sub =>
    s!"box[{mod.pretty}]({prettyTerm names sub})"
  | .letBox x mod scrut _ body =>
    s!"(let box[{mod.pretty}] {x} := {prettyTerm names scrut}; {prettyTerm (x :: names) body})"
  | .recordTy fields =>
    s!"sig \{ {String.intercalate ", " (prettyTeleFields names fields)} }"
  | .tuple fields =>
    s!"⟨{String.intercalate ", " (prettyTupleItems names fields)}⟩"
  | .proj sub field =>
    s!"{prettyTerm names sub}.{field}"
  | .dataTy name [] => name
  | .dataTy name params =>
    s!"({name} {String.intercalate " " (prettyList names params)})"
  | .ctor _ cName [] => cName
  | .ctor _ cName args =>
    s!"({cName} {String.intercalate " " (prettyList names args)})"
  | .matchData scrut winMod _ branches =>
    let bStrs := prettyBranches names branches
    s!"(match@{winMod.pretty} {prettyTerm names scrut} with {String.intercalate " " bStrs})"
  | .obsEq g ty ends =>
    let args := prettyTerm names ty :: prettyList names ends
    s!"({prettyObsHead g} {String.intercalate " " args})"
  | .obsHet g tyB ends =>
    let args := prettyTerm names tyB :: prettyList names ends
    s!"({prettyObsHead g}_het {String.intercalate " " args})"
  | .refl g sub =>
    let tag := if g == Dir.hott then "refl" else s!"refl_{g.name}"
    s!"({tag} {prettyTerm names sub})"
  | .sym _ p =>
    s!"(sym {prettyTerm names p})"
  | .ap _ fn argB =>
    s!"(ap {prettyTerm names fn} {prettyTerm names argB})"
  | .gel g tys rel =>
    let head := if g == Dir.hott then "Glue" else "Gel"
    s!"({head} [{String.intercalate ", " (prettyList names tys)}] {prettyTerm names rel})"
  | .gelIntro _ ends wit =>
    s!"(gel⟨{String.intercalate ", " (prettyList names ends)}; {prettyTerm names wit}⟩)"
  | .ungel _ bTm =>
    s!"(ungel {prettyTerm names bTm})"
  | .trr _ tyL x₀ =>
    s!"(trr {prettyTerm names tyL} {prettyTerm names x₀})"
  | .trl _ tyL x₁ =>
    s!"(trl {prettyTerm names tyL} {prettyTerm names x₁})"
  | .liftr _ tyL x₀ =>
    s!"(liftr {prettyTerm names tyL} {prettyTerm names x₀})"
  | .liftl _ tyL x₁ =>
    s!"(liftl {prettyTerm names tyL} {prettyTerm names x₁})"
  | .trans _ p q =>
    s!"(trans {prettyTerm names p} {prettyTerm names q})"
  | .arrowLine _ mod dL cL =>
    if mod.steps.isEmpty then s!"(arrowLine {prettyTerm names dL} {prettyTerm names cL})"
    else s!"(arrowLine@{mod.pretty} {prettyTerm names dL} {prettyTerm names cL})"
  | .piLine _ x mod dL c0 c1 cL =>
    let xFresh := if names.contains x then s!"{x}_{names.length}" else x
    s!"(piLine ({xFresh} : {mod.pretty}) {prettyTerm names dL} {prettyTerm (xFresh :: names) c0} {prettyTerm (xFresh :: names) c1} {prettyTerm ((xFresh ++ "2") :: (xFresh ++ "1") :: (xFresh ++ "0") :: names) cL})"
  | .prodLine _ fN sN fL sL =>
    s!"(prodLine {fN} {sN} {prettyTerm names fL} {prettyTerm names sL})"
  | .sigLine _ fN sN _ _ fL s0 s1 sL =>
    s!"(sigLine {fN} {sN} {prettyTerm names fL} {prettyTerm (fN :: names) s0} {prettyTerm (fN :: names) s1} {prettyTerm ((fN ++ "2") :: (fN ++ "1") :: (fN ++ "0") :: names) sL})"
  | .boxLine _ mod inL =>
    s!"(boxLine[{mod.pretty}] {prettyTerm names inL})"
  | .pathJ _ _ base _ reflC target path =>
    s!"(J {prettyTerm names base} {prettyTerm names reflC} {prettyTerm names target} {prettyTerm names path})"
  | .funext _ mod body =>
    let bNames := ["px", "x1", "x0"] ++ names
    if mod.steps.isEmpty then s!"(funext {prettyTerm bNames body})"
    else s!"(funext@{mod.pretty} {prettyTerm bNames body})"
  | .hap _ pf a₀ a₁ pa =>
    s!"(hap {prettyTerm names pf} {prettyTerm names a₀} {prettyTerm names a₁} {prettyTerm names pa})"
  | .u64Ty => "U64"
  | .u64Lit v => s!"{v}u64"
  | .u64BinOp op l r => s!"({op.name} {prettyTerm names l} {prettyTerm names r})"
  | .u64IfZero c z nz => s!"(u64_ifz {prettyTerm names c} {prettyTerm names z} {prettyTerm names nz})"
  | .u64Repeat iters init step =>
    s!"(u64_repeat {iters} {prettyTerm names init} (fun acc => {prettyTerm ("acc" :: names) step}))"

end

/-- Pretty-print a closed `Val` by quoting via NbE `quoteVal`. -/
def prettyVal (G : GlobalEnv) (v : Val) (depth : Nat := 0) : String :=
  prettyTerm [] (quoteVal defaultFuel G depth v)

end Narya.Syntax
