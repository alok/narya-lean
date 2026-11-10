/-
  Narya.Elab.DSL — Lean 4 Metaprogramming Surface Syntax & Interactive Commands

  Exposes familiar Lean 4 syntax (`fun x => ...`, `(x : A) → B`, `(x : L | A) → B`,
  `Id`, `Br`, `Disp`, `Fresh`, `Gel`, `Glue`, `refl`, `trr`, `trl`, `⟨f := v⟩`)
  compiled hygienically via `declare_syntax_cat` + `macro_rules` + `CommandElabM`
  into `Narya.Core.Term`, plus `#narya_check`, `#narya_eval`, and `def_mode_theory`!
-/
import Lean
import Narya.Syntax.Parser

namespace Narya.Elab

open Lean Elab Command Meta
open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core Narya.Syntax

/-! ### Named Intermediate AST (`NTerm`) for Hygienic Lexical + Modal Resolution -/

/-- Named surface AST produced by Lean 4 `narya_tm` syntax macros before De Bruijn
    indexing and `ModeTheory` modality/2-cell resolution. -/
inductive NTerm where
  | var (name : String)
  | uu (lvl : Nat)
  | uuExt (lvl : Nat)
  | pi (name : String) (modName : String) (dom : NTerm) (cod : NTerm)
  | lam (name : String) (modName : String) (body : NTerm)
  | app (fn : NTerm) (modName : String) (arg : NTerm)
  | letIn (name : String) (ty : NTerm) (val : NTerm) (body : NTerm)
  | key (keyName : String) (sub : NTerm)
  | modalBox (modName : String) (ty : NTerm)
  | boxIntro (modName : String) (sub : NTerm)
  | recordTy (fields : List (String × String × NTerm))
  | tuple (fields : List (String × NTerm))
  | proj (sub : NTerm) (field : String)
  | obsEq (g : Dir) (ty : NTerm) (ends : List NTerm)
  | obsHet (g : Dir) (tyB : NTerm) (ends : List NTerm)
  | refl (g : Dir) (sub : NTerm)
  | sym (g : Dir) (p : NTerm)
  | ap (g : Dir) (fn : NTerm) (argB : NTerm)
  | gel (g : Dir) (tys : List NTerm) (rel : NTerm)
  | gelIntro (g : Dir) (ends : List NTerm) (wit : NTerm)
  | ungel (g : Dir) (sub : NTerm)
  | trr (tyL : NTerm) (x₀ : NTerm)
  | trl (tyL : NTerm) (x₁ : NTerm)
  | liftr (tyL : NTerm) (x₀ : NTerm)
  deriving BEq, Repr, Inhabited

namespace NTerm

/-- Resolve a modality string (`"_"`, `"L"`, `"R.L"`) in `T` at `currMode` (total with fallback). -/
def resolveModTotal (T : ModeTheory) (currMode : ModeId) (raw : String) : ModPath :=
  match resolveModPath T currMode raw with
  | .ok mp => mp
  | .error _ => ModPath.id currMode

/-- Resolve a 2-cell generator name in `T` (total with identity fallback). -/
def resolveKeyTotal (T : ModeTheory) (currMode : ModeId) (kName : String) : TwoCellExpr :=
  match T.findTwoCell? kName with
  | some c => .gen c
  | none => .id2 (ModPath.id currMode)

mutual

def toCoreTele (T : ModeTheory) (mode : ModeId) (locals : List String) :
    List (String × String × NTerm) → List (String × ModPath × Narya.Core.Term)
  | [] => []
  | (fn, mStr, fty) :: rest =>
    let mp := resolveModTotal T mode mStr
    let cTy := toCore T mp.dom locals fty
    (fn, mp, cTy) :: toCoreTele T mode (fn :: locals) rest

def toCoreTuple (T : ModeTheory) (mode : ModeId) (locals : List String) :
    List (String × NTerm) → List (String × Narya.Core.Term)
  | [] => []
  | (fn, ftm) :: rest =>
    (fn, toCore T mode locals ftm) :: toCoreTuple T mode locals rest

def toCoreList (T : ModeTheory) (mode : ModeId) (locals : List String) :
    List NTerm → List Narya.Core.Term
  | [] => []
  | t :: ts => toCore T mode locals t :: toCoreList T mode locals ts

/-- Lower `NTerm` into `Narya.Core.Term` with De Bruijn indices and resolved `ModPath`s. -/
def toCore (T : ModeTheory) (mode : ModeId) (locals : List String) : NTerm → Narya.Core.Term
  | .var name =>
    match locals.findIdx? (· == name) with
    | some ix => .bvar ix
    | none =>
      match name with
      | "zero" => .ctor "Nat" "zero" []
      | "true" => .ctor "Bool" "true" []
      | "false" => .ctor "Bool" "false" []
      | "tt" => .ctor "Unit" "tt" []
      | _ => .global name
  | .uu lvl => .uu lvl
  | .uuExt lvl => .uuExt lvl
  | .pi name modStr dom cod =>
    let mp := resolveModTotal T mode modStr
    .pi name mp (toCore T mp.dom locals dom) (toCore T mode (name :: locals) cod)
  | .lam name modStr body =>
    let mp := resolveModTotal T mode modStr
    .lam name mp (toCore T mode (name :: locals) body)
  | .app fn modStr arg =>
    let mp := resolveModTotal T mode modStr
    -- Built-in constructor helper for `succ n`:
    match fn with
    | .var "succ" =>
      if !(locals.contains "succ") && modStr == "_" then
        .ctor "Nat" "succ" [toCore T mode locals arg]
      else
        .app (toCore T mode locals fn) mp (toCore T mp.dom locals arg)
    | _ => .app (toCore T mode locals fn) mp (toCore T mp.dom locals arg)
  | .letIn name ty val body =>
    .letIn name (toCore T mode locals ty) (toCore T mode locals val) (toCore T mode (name :: locals) body)
  | .key kName sub =>
    .key (resolveKeyTotal T mode kName) (toCore T mode locals sub)
  | .modalBox modStr ty =>
    let mp := resolveModTotal T mode modStr
    .modalBox mp (toCore T mp.dom locals ty)
  | .boxIntro modStr sub =>
    let mp := resolveModTotal T mode modStr
    .boxIntro mp (toCore T mp.dom locals sub)
  | .recordTy fs => .recordTy (toCoreTele T mode locals fs)
  | .tuple fs => .tuple (toCoreTuple T mode locals fs)
  | .proj sub fld => .proj (toCore T mode locals sub) fld
  | .obsEq g ty ends => .obsEq g (toCore T mode locals ty) (toCoreList T mode locals ends)
  | .obsHet g tyB ends => .obsHet g (toCore T mode locals tyB) (toCoreList T mode locals ends)
  | .refl g sub => .refl g (toCore T mode locals sub)
  | .sym g p => .sym g (toCore T mode locals p)
  | .ap g fn argB => .ap g (toCore T mode locals fn) (toCore T mode locals argB)
  | .gel g tys rel => .gel g (toCoreList T mode locals tys) (toCore T mode locals rel)
  | .gelIntro g ends wit => .gelIntro g (toCoreList T mode locals ends) (toCore T mode locals wit)
  | .ungel g sub => .ungel g (toCore T mode locals sub)
  | .trr tyL x₀ => .trr Dir.hott (toCore T mode locals tyL) (toCore T mode locals x₀)
  | .trl tyL x₁ => .trl Dir.hott (toCore T mode locals tyL) (toCore T mode locals x₁)
  | .liftr tyL x₀ => .liftr Dir.hott (toCore T mode locals tyL) (toCore T mode locals x₀)

end

end NTerm

/-! ### Custom Lean 4 Syntax Categories (`narya_tm`, `narya_field`, `narya_assign`) -/

declare_syntax_cat narya_tm
declare_syntax_cat narya_field
declare_syntax_cat narya_assign

-- Record/codata field declarations & tuple assignments:
syntax ident " : " narya_tm : narya_field
syntax "(" ident " : " ident " | " narya_tm ")" : narya_field
syntax ident " := " narya_tm : narya_assign

-- Atomic & structured Narya terms in familiar Lean 4 syntax:
syntax "Type" : narya_tm
syntax "Type " num : narya_tm
syntax "Type_ext" : narya_tm
syntax ident : narya_tm
syntax "(" narya_tm ")" : narya_tm

-- Binders & arrows:
syntax:25 "(" ident " : " narya_tm ")" " → " narya_tm:25 : narya_tm
syntax:25 "(" ident " : " narya_tm ")" " -> " narya_tm:25 : narya_tm
syntax:25 "(" ident " : " ident " | " narya_tm ")" " → " narya_tm:25 : narya_tm
syntax:25 "(" ident " : " ident " | " narya_tm ")" " -> " narya_tm:25 : narya_tm
syntax:25 narya_tm:26 " → " narya_tm:25 : narya_tm
syntax:25 narya_tm:26 " -> " narya_tm:25 : narya_tm

syntax:20 "fun " ident " => " narya_tm:20 : narya_tm
syntax:20 "fun " "(" ident " : " ident ")" " => " narya_tm:20 : narya_tm
syntax:20 "let " ident " : " narya_tm " := " narya_tm " ; " narya_tm:20 : narya_tm

-- Records, codata, tuples, projections, modalities:
syntax "sig" "{" narya_field,* "}" : narya_tm
syntax "⟨" narya_assign,* "⟩" : narya_tm
syntax:80 "proj" "(" narya_tm "," ident ")" : narya_tm
syntax:80 "key" "(" narya_tm "," ident ")" : narya_tm
syntax:80 "Box" "(" ident "," narya_tm ")" : narya_tm
syntax:80 "box" "(" ident "," narya_tm ")" : narya_tm
syntax:80 "app_mod" "(" narya_tm "," ident "," narya_tm ")" : narya_tm

-- Higher observational types, Gel/Glue, & HoTT fibrancy:
syntax "Id" "(" narya_tm "," narya_tm "," narya_tm ")" : narya_tm
syntax "Br" "(" narya_tm "," narya_tm "," narya_tm ")" : narya_tm
syntax "Disp" "(" narya_tm "," narya_tm ")" : narya_tm
syntax "Fresh" "(" narya_tm ")" : narya_tm
syntax "IdHet" "(" narya_tm "," narya_tm "," narya_tm ")" : narya_tm
syntax "BrHet" "(" narya_tm "," narya_tm "," narya_tm ")" : narya_tm
syntax "refl" "(" narya_tm ")" : narya_tm
syntax "refl_br" "(" narya_tm ")" : narya_tm
syntax "refl_disp" "(" narya_tm ")" : narya_tm
syntax "Gel" "(" narya_tm "," narya_tm "," narya_tm ")" : narya_tm
syntax "Glue" "(" narya_tm "," narya_tm "," narya_tm ")" : narya_tm
syntax "gelIntro" "(" narya_tm "," narya_tm ";" narya_tm ")" : narya_tm
syntax "ungel" "(" narya_tm ")" : narya_tm
syntax "trr" "(" narya_tm "," narya_tm ")" : narya_tm
syntax "trl" "(" narya_tm "," narya_tm ")" : narya_tm
syntax "liftr" "(" narya_tm "," narya_tm ")" : narya_tm

-- Juxtaposition application:
syntax:70 narya_tm:70 ppSpace narya_tm:71 : narya_tm

-- Quotation macros into `NTerm` and `Narya.Core.Term`:
syntax "narya_ntm!" narya_tm : term
syntax "narya_field!" narya_field : term
syntax "narya_assign!" narya_assign : term
syntax "narya!" "[" term "]" narya_tm : term
syntax "narya_hoTT!" narya_tm : term

macro_rules
  | `(narya_field! $f:ident : $t:narya_tm) =>
    `(($(quote f.getId.toString), "_", narya_ntm! $t))
  | `(narya_field! ($f:ident : $m:ident | $t:narya_tm)) =>
    `(($(quote f.getId.toString), $(quote m.getId.toString), narya_ntm! $t))
  | `(narya_assign! $f:ident := $t:narya_tm) =>
    `(($(quote f.getId.toString), narya_ntm! $t))

macro_rules
  | `(narya_ntm! Type) => `(NTerm.uu 0)
  | `(narya_ntm! Type $n:num) => `(NTerm.uu $n)
  | `(narya_ntm! Type_ext) => `(NTerm.uuExt 0)
  | `(narya_ntm! $x:ident) => `(NTerm.var $(quote x.getId.toString))
  | `(narya_ntm! ($t:narya_tm)) => `(narya_ntm! $t)
  | `(narya_ntm! ($x:ident : $a:narya_tm) → $b:narya_tm) =>
    `(NTerm.pi $(quote x.getId.toString) "_" (narya_ntm! $a) (narya_ntm! $b))
  | `(narya_ntm! ($x:ident : $a:narya_tm) -> $b:narya_tm) =>
    `(NTerm.pi $(quote x.getId.toString) "_" (narya_ntm! $a) (narya_ntm! $b))
  | `(narya_ntm! ($x:ident : $m:ident | $a:narya_tm) → $b:narya_tm) =>
    `(NTerm.pi $(quote x.getId.toString) $(quote m.getId.toString) (narya_ntm! $a) (narya_ntm! $b))
  | `(narya_ntm! ($x:ident : $m:ident | $a:narya_tm) -> $b:narya_tm) =>
    `(NTerm.pi $(quote x.getId.toString) $(quote m.getId.toString) (narya_ntm! $a) (narya_ntm! $b))
  | `(narya_ntm! $a:narya_tm → $b:narya_tm) =>
    `(NTerm.pi "_" "_" (narya_ntm! $a) (narya_ntm! $b))
  | `(narya_ntm! $a:narya_tm -> $b:narya_tm) =>
    `(NTerm.pi "_" "_" (narya_ntm! $a) (narya_ntm! $b))
  | `(narya_ntm! fun $x:ident => $b:narya_tm) =>
    `(NTerm.lam $(quote x.getId.toString) "_" (narya_ntm! $b))
  | `(narya_ntm! fun ($x:ident : $m:ident) => $b:narya_tm) =>
    `(NTerm.lam $(quote x.getId.toString) $(quote m.getId.toString) (narya_ntm! $b))
  | `(narya_ntm! let $x:ident : $ty:narya_tm := $v:narya_tm ; $b:narya_tm) =>
    `(NTerm.letIn $(quote x.getId.toString) (narya_ntm! $ty) (narya_ntm! $v) (narya_ntm! $b))
  | `(narya_ntm! sig { $[$fs:narya_field],* }) =>
    `(NTerm.recordTy [ $[narya_field! $fs],* ])
  | `(narya_ntm! ⟨ $[$as:narya_assign],* ⟩) =>
    `(NTerm.tuple [ $[narya_assign! $as],* ])
  | `(narya_ntm! proj($t:narya_tm, $f:ident)) =>
    `(NTerm.proj (narya_ntm! $t) $(quote f.getId.toString))
  | `(narya_ntm! key($t:narya_tm, $k:ident)) =>
    `(NTerm.key $(quote k.getId.toString) (narya_ntm! $t))
  | `(narya_ntm! Box($m:ident, $t:narya_tm)) =>
    `(NTerm.modalBox $(quote m.getId.toString) (narya_ntm! $t))
  | `(narya_ntm! box($m:ident, $t:narya_tm)) =>
    `(NTerm.boxIntro $(quote m.getId.toString) (narya_ntm! $t))
  | `(narya_ntm! app_mod($fn:narya_tm, $m:ident, $a:narya_tm)) =>
    `(NTerm.app (narya_ntm! $fn) $(quote m.getId.toString) (narya_ntm! $a))
  | `(narya_ntm! Id($ty:narya_tm, $a:narya_tm, $b:narya_tm)) =>
    `(NTerm.obsEq Dir.hott (narya_ntm! $ty) [narya_ntm! $a, narya_ntm! $b])
  | `(narya_ntm! Br($ty:narya_tm, $a:narya_tm, $b:narya_tm)) =>
    `(NTerm.obsEq (Dir.param 2) (narya_ntm! $ty) [narya_ntm! $a, narya_ntm! $b])
  | `(narya_ntm! Disp($ty:narya_tm, $a:narya_tm)) =>
    `(NTerm.obsEq Dir.displayed (narya_ntm! $ty) [narya_ntm! $a])
  | `(narya_ntm! Fresh($ty:narya_tm)) =>
    `(NTerm.obsEq Dir.nominal (narya_ntm! $ty) [])
  | `(narya_ntm! IdHet($p:narya_tm, $a:narya_tm, $b:narya_tm)) =>
    `(NTerm.obsHet Dir.hott (narya_ntm! $p) [narya_ntm! $a, narya_ntm! $b])
  | `(narya_ntm! BrHet($p:narya_tm, $a:narya_tm, $b:narya_tm)) =>
    `(NTerm.obsHet (Dir.param 2) (narya_ntm! $p) [narya_ntm! $a, narya_ntm! $b])
  | `(narya_ntm! refl($a:narya_tm)) =>
    `(NTerm.refl Dir.hott (narya_ntm! $a))
  | `(narya_ntm! refl_br($a:narya_tm)) =>
    `(NTerm.refl (Dir.param 2) (narya_ntm! $a))
  | `(narya_ntm! refl_disp($a:narya_tm)) =>
    `(NTerm.refl Dir.displayed (narya_ntm! $a))
  | `(narya_ntm! Gel($a:narya_tm, $b:narya_tm, $r:narya_tm)) =>
    `(NTerm.gel (Dir.param 2) [narya_ntm! $a, narya_ntm! $b] (narya_ntm! $r))
  | `(narya_ntm! Glue($a:narya_tm, $b:narya_tm, $r:narya_tm)) =>
    `(NTerm.gel Dir.hott [narya_ntm! $a, narya_ntm! $b] (narya_ntm! $r))
  | `(narya_ntm! gelIntro($a:narya_tm, $b:narya_tm ; $w:narya_tm)) =>
    `(NTerm.gelIntro (Dir.param 2) [narya_ntm! $a, narya_ntm! $b] (narya_ntm! $w))
  | `(narya_ntm! ungel($p:narya_tm)) =>
    `(NTerm.ungel (Dir.param 2) (narya_ntm! $p))
  | `(narya_ntm! trr($p:narya_tm, $x:narya_tm)) =>
    `(NTerm.trr (narya_ntm! $p) (narya_ntm! $x))
  | `(narya_ntm! trl($p:narya_tm, $x:narya_tm)) =>
    `(NTerm.trl (narya_ntm! $p) (narya_ntm! $x))
  | `(narya_ntm! liftr($p:narya_tm, $x:narya_tm)) =>
    `(NTerm.liftr (narya_ntm! $p) (narya_ntm! $x))
  | `(narya_ntm! $fn:narya_tm $arg:narya_tm) =>
    `(NTerm.app (narya_ntm! $fn) "_" (narya_ntm! $arg))

macro_rules
  | `(narya! [$T:term] $t:narya_tm) =>
    `(NTerm.toCore $T ($T).defaultMode [] (narya_ntm! $t))
  | `(narya_hoTT! $t:narya_tm) =>
    `(NTerm.toCore pureHoTT pureHoTT.defaultMode [] (narya_ntm! $t))

/-! ### Interactive Lean 4 InfoView Commands (`#narya_check`, `#narya_eval`) -/

/-- Format the output of checking a Narya term in `G`. -/
def formatCheckReport (G : GlobalEnv) (tm : Narya.Core.Term) : String :=
  match synthClosed G tm with
  | .ok (tm', tyVal) => s!"{prettyTerm [] tm'} : {prettyVal G tyVal}"
  | .error err => s!"[Narya Type Error] {err}"

/-- Format the output of evaluating/normalizing a Narya term in `G`. -/
def formatEvalReport (G : GlobalEnv) (tm : Narya.Core.Term) : String :=
  match synthClosed G tm with
  | .ok (tm', tyVal) =>
    let nf := normalize G [] 0 tm'
    s!"{prettyTerm [] nf} : {prettyVal G tyVal}"
  | .error err => s!"[Narya Type Error] {err}"

syntax "#narya_check" "[" term "]" narya_tm : command
syntax "#narya_eval" "[" term "]" narya_tm : command

macro_rules
  | `(#narya_check [$G:term] $t:narya_tm) =>
    `(#eval IO.println (formatCheckReport $G (NTerm.toCore ($G).theory ($G).theory.defaultMode [] (narya_ntm! $t))))
  | `(#narya_eval [$G:term] $t:narya_tm) =>
    `(#eval IO.println (formatEvalReport $G (NTerm.toCore ($G).theory ($G).theory.defaultMode [] (narya_ntm! $t))))

/-! ### Declarative `def_mode_theory` Macro -/

declare_syntax_cat narya_mode_decl
syntax "mode" ident : narya_mode_decl
syntax "modality" ident ":" ident "->" ident : narya_mode_decl
syntax "sinister_modality" ident ":" ident "->" ident : narya_mode_decl
syntax "discrete_modality" ident ":" ident "->" ident : narya_mode_decl

syntax "def_mode_theory" ident "default_mode" ident "where" narya_mode_decl* : command

elab_rules : command
  | `(def_mode_theory $name:ident default_mode $defMode:ident where $[$decls:narya_mode_decl]*) => do
    let defStr : TSyntax `term := quote defMode.getId.toString
    let nameStr : TSyntax `term := quote name.getId.toString
    let mut modeTerms : Array (TSyntax `term) := #[defStr]
    let mut mods : Array (TSyntax `term) := #[]
    for d in decls do
      match d with
      | `(narya_mode_decl| mode $m:ident) =>
        modeTerms := modeTerms.push (quote m.getId.toString)
      | `(narya_mode_decl| modality $g:ident : $dom:ident -> $cod:ident) =>
        let gS : TSyntax `term := quote g.getId.toString
        let dS : TSyntax `term := quote dom.getId.toString
        let cS : TSyntax `term := quote cod.getId.toString
        let t ← `(term| ({ name := $gS, dom := $dS, cod := $cS, flags := { tangible := true, pellucid := true } } : ModGen))
        mods := mods.push t
      | `(narya_mode_decl| sinister_modality $g:ident : $dom:ident -> $cod:ident) =>
        let gS : TSyntax `term := quote g.getId.toString
        let dS : TSyntax `term := quote dom.getId.toString
        let cS : TSyntax `term := quote cod.getId.toString
        let t ← `(term| ({ name := $gS, dom := $dS, cod := $cS, flags := { tangible := true, pellucid := true, sinister := true } } : ModGen))
        mods := mods.push t
      | `(narya_mode_decl| discrete_modality $g:ident : $dom:ident -> $cod:ident) =>
        let gS : TSyntax `term := quote g.getId.toString
        let dS : TSyntax `term := quote dom.getId.toString
        let cS : TSyntax `term := quote cod.getId.toString
        let t ← `(term| ({ name := $gS, dom := $dS, cod := $cS, flags := { tangible := true, pellucid := true, discreteDirs := [Dir.hott, Dir.param 2] } } : ModGen))
        mods := mods.push t
      | _ => pure ()
    let cmd ← `(command|
      def $name : ModeTheory := {
        name := $nameStr
        modes := dedup [ $[$modeTerms],* ]
        modalities := [ $[$mods],* ]
        twoCells := []
        rules := []
        defaultMode := $defStr
      })
    elabCommand cmd

end Narya.Elab
