/-
  Narya.Dim.Cube — Multi-Directional Variable-Arity Cubes & Boundary Tubes

  Port and dependent-type simplification of OCaml Narya's `lib/dim/cube.ml`
  and `lib/dim/tube.ml`.
  In OCaml, lacking dependent type families `DimCtx → Type u`, `Cube` required
  500+ lines of `gt` trees, backwards-forwards `bplus` witnesses, and `Fam2`
  functors. In Lean 4, defining `DepCube` by structural recursion with motive-shifting
  `fun k => F (g :: k)` keeps `DepCube F n : Type u` with zero universe bump,
  making `DepCube`, `CubeOf`, and `TubeOf` total, computable, and provably functorial!
-/
import Narya.Dim.Op

namespace Narya.Dim

universe u v

/-- A dependent cube of dimension `n` where the entry at face `f : SFace k n`
    has dependent type `F k : Type u` (with zero universe bump!). -/
def DepCube (F : DimCtx → Type u) : DimCtx → Type u
  | [] => F []
  | g :: m => (Endpoint g → DepCube F m) × DepCube (fun k => F (g :: k)) m

namespace DepCube

/-- Look up the entry of `DepCube F n` at any strict face `f : SFace k n`. -/
def find {F : DimCtx → Type u} {k n : DimCtx} (c : DepCube F n) (f : SFace k n) : F k :=
  match f, c with
  | .zero, val => val
  | .endpt f' _ e, (ends, _) => find (ends e) f'
  | .mid f' g, (_, mid) => find (F := fun r => F (g :: r)) mid f'

/-- Extract the top-dimensional cell `F n` (at `SFace.id n`). -/
def findTop {F : DimCtx → Type u} {n : DimCtx} (c : DepCube F n) : F n :=
  find c (SFace.id n)

/-- Tabulate a `DepCube F n` from its universal lookup function `∀ {k}, SFace k n → F k`. -/
def build {F : DimCtx → Type u} :
    (n : DimCtx) → (∀ {k : DimCtx}, SFace k n → F k) → DepCube F n
  | [], mk => mk .zero
  | g :: m, mk =>
    ( fun e => build m (fun f => mk (.endpt f g e))
    , build (F := fun k => F (g :: k)) m (fun f => mk (.mid f g)) )

/-- **Universal Tabulation Law (`find_build`)**: Looking up `f` in `build n mk`
    computes directly to `mk f`! -/
@[simp]
theorem find_build {F : DimCtx → Type u} (n : DimCtx)
    (mk : ∀ {k : DimCtx}, SFace k n → F k) {k : DimCtx} (f : SFace k n) :
    find (build n mk) f = mk f := by
  induction f generalizing F with
  | zero => rfl
  | endpt f' g e ih =>
    exact ih (F := F) (fun x => mk (.endpt x g e))
  | mid f' g ih =>
    exact ih (F := fun r => F (g :: r)) (fun x => mk (.mid x g))

/-- **Uniqueness / Eta Law (`build_find`)**: Re-tabulating a cube's faces reconstructs it. -/
@[simp]
theorem build_find {F : DimCtx → Type u} :
    ∀ (n : DimCtx) (c : DepCube F n), build n (fun f => find c f) = c
  | [], _ => rfl
  | g :: m, (ends, mid) => by
    simp only [build]
    refine Prod.ext ?_ ?_
    · funext e
      exact build_find m (ends e)
    · exact build_find (F := fun r => F (g :: r)) m mid

end DepCube

/-- Non-dependent `n`-cube storing an element of `α` for every strict face of `n`.
    Matches `('n, 'a) CubeOf.t` in OCaml Narya. -/
abbrev CubeOf (α : Type u) (n : DimCtx) : Type u :=
  DepCube (fun _ => α) n

namespace CubeOf

def singleton {α : Type u} (x : α) : CubeOf α [] := x

def find {α : Type u} {k n : DimCtx} (c : CubeOf α n) (f : SFace k n) : α :=
  DepCube.find c f

def findTop {α : Type u} {n : DimCtx} (c : CubeOf α n) : α :=
  DepCube.findTop c

def build {α : Type u} (n : DimCtx) (mk : ∀ {k : DimCtx}, SFace k n → α) : CubeOf α n :=
  DepCube.build n mk

def map {α : Type u} {β : Type v} {n : DimCtx} (fn : α → β) (c : CubeOf α n) : CubeOf β n :=
  build n (fun f => fn (find c f))

/-- Collect all face entries of a `CubeOf α n` in canonical traversal order.
    For `n = [g₁, ..., gᵣ]`, there are `∏ᵢ (gᵢ.arity + 1)` faces! -/
def toList {α : Type u} : {n : DimCtx} → CubeOf α n → List α
  | [], x => [x]
  | g :: _, (ends, mid) =>
    let endLists := (List.finRange g.arity).flatMap (fun e => toList (ends e))
    endLists ++ toList mid

/-- Act on an `n`-cube by a degeneracy `fa : Deg m n`, given how `Deg` acts on entries.
    Exact port of `act_cube` from `lib/core/act.ml:120-133`! -/
def act {α : Type u} {β : Type v} {m n : DimCtx}
    (actor : ∀ {p q : DimCtx}, α → Deg p q → β)
    (xs : CubeOf α n) (fa : Deg m n) : CubeOf β m :=
  build m (fun fb =>
    match Op.degSFace fa fb with
    | .mk fd fc => actor (find xs fd) fc)

@[simp]
theorem map_id {α : Type u} {n : DimCtx} (c : CubeOf α n) :
    map (fun x => x) c = c := by
  exact DepCube.build_find n c

theorem map_comp {α β γ : Type u} {n : DimCtx} (g : β → γ) (f : α → β) (c : CubeOf α n) :
    map g (map f c) = map (fun x => g (f x)) c := by
  unfold map build
  congr
  funext k face
  simp [CubeOf.find]

/-- **Identity Action Theorem (`act_id`)**: If `actor x (Deg.id _) = x`, then
    acting on a cube `xs` by `Deg.id n` leaves `xs` strictly unchanged!
    (Justifies short-circuiting identity cube actions in `act.ml`!) -/
theorem act_id {α : Type u} {n : DimCtx}
    (actor : ∀ {p q : DimCtx}, α → Deg p q → α)
    (hActorId : ∀ {p : DimCtx} (x : α), actor x (Deg.id p) = x)
    (xs : CubeOf α n) :
    act actor xs (Deg.id n) = xs := by
  unfold act build
  have hFun : (fun {k : DimCtx} (fb : SFace k n) =>
      match Op.degSFace (Deg.id n) fb with
      | .mk fd fc => actor (find xs fd) fc) = (fun {k : DimCtx} (fb : SFace k n) => find xs fb) := by
    funext k fb
    rw [Op.degSFace_id_left fb]
    dsimp only
    exact hActorId (find xs fb)
  rw [hFun]
  exact DepCube.build_find n xs

end CubeOf

/-- A boundary tube `TubeOf α n` stores an element of `α` for every *proper* strict face
    (`f.isId = false`) of an `n`-cube — i.e., all faces except the interior top cell `SFace.id n`.
    Used to represent instantiation arguments of `Id`/`Br` types (e.g. `{a₀} {a₁}` for `Id A a₀ a₁`). -/
inductive TubeOf (α : Type u) : DimCtx → Type u where
  | zero : TubeOf α []
  | suc {m : DimCtx} (g : Dir)
      (ends : Endpoint g → CubeOf α m)
      (mid : TubeOf α m) :
      TubeOf α (g :: m)

namespace TubeOf

/-- Look up any proper strict face (`f.isId = false`) in a boundary `TubeOf α n`. -/
def findProper {α : Type u} {k n : DimCtx} :
    TubeOf α n → (f : SFace k n) → f.isId = false → α
  | .zero, .zero, h => by simp [SFace.isId] at h
  | .suc _ ends _, .endpt f _ e, _ => CubeOf.find (ends e) f
  | .suc _ _ mid, .mid f _, h =>
    mid.findProper f (by simpa [SFace.isId] using h)

/-- Complete a boundary `TubeOf α n` plus a top cell `top : α` into a full `CubeOf α n`! -/
def plug {α : Type u} {n : DimCtx} : TubeOf α n → α → CubeOf α n
  | .zero, top => top
  | .suc _ ends mid, top => (ends, mid.plug top)

/-- Extract the boundary `TubeOf α n` of a full `CubeOf α n` by forgetting its top cell. -/
def boundary {α : Type u} : {n : DimCtx} → CubeOf α n → TubeOf α n
  | [], _ => .zero
  | g :: _, (ends, mid) => .suc g ends (boundary mid)

/-- **Tube–Cube Reassembly Theorem (`plug_boundary_findTop`)**: Taking the boundary of
    any `n`-cube and plugging back its top cell recovers the exact `n`-cube! -/
@[simp]
theorem plug_boundary_findTop {α : Type u} :
    ∀ {n : DimCtx} (c : CubeOf α n), (boundary c).plug (CubeOf.findTop c) = c
  | [], _ => rfl
  | g :: _, (ends, mid) => by
    simp only [boundary, plug, CubeOf.findTop, DepCube.findTop, SFace.id, DepCube.find]
    exact congrArg (Prod.mk ends) (plug_boundary_findTop mid)

end TubeOf

end Narya.Dim
