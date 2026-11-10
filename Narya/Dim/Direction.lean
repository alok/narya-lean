/-
  Narya.Dim.Direction — Multi-Directional Dimension Generators

  Resolves Open Problem 1 (part 1): Upstream OCaml Narya supports only a single
  built-in dimension direction at runtime (`lib/dim/README.md:5`,
  `docs/source/observational.rst:4`). Here we parameterize dimensions over an
  open universe of colored direction generators `Dir`, each carrying:
  - `name`     : direction symbol (`"e"` for HoTT, `"p"` for parametricity,
                 `"d"` for unary simplicial display, `"w"` for nominal weakening)
  - `arity`    : number of endpoints of a 1-cube in this direction (`0`, `1`, `2`, `k`)
  - `fibrant`  : whether paths in this direction admit transport & path-lifting
  - `internal` : whether degeneracies are internal or modally-guarded external
-/

namespace Narya.Dim

/-- A colored dimension direction in multi-directional Higher Observational Type Theory. -/
structure Dir where
  /-- Short identifier for superscripts and diagnostics (e.g. `"e"`, `"p"`, `"d"`, `"w"`). -/
  name : String
  /-- Number of endpoints of a 1-dimensional cube in this direction. -/
  arity : Nat
  /-- True if types carry computational HoTT fibrancy (`trr`, `trl`, `liftr`, `liftl`) along this direction. -/
  fibrant : Bool := false
  /-- True if parametricity/degeneracies are available internally in arbitrary contexts;
      false if guarded by a parametric locker modality (`-external` / `-dtt`). -/
  internal : Bool := true
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Dir

/-- Standard HoTT path direction (`e`, binary endpoints `0, 1`, fibrant, internal). -/
def hott : Dir :=
  { name := "e", arity := 2, fibrant := true, internal := true }

/-- Variable-arity parametricity / bridge direction (`p`, default binary `arity = 2`). -/
def param (arity : Nat := 2) (internal : Bool := true) : Dir :=
  { name := "p", arity := arity, fibrant := false, internal := internal }

/-- Unary semi-simplicial display direction (`d`, `arity = 1`, modally guarded external) for dTT (`SST`). -/
def displayed : Dir :=
  { name := "d", arity := 1, fibrant := false, internal := false }

/-- Nullary nominal / weakening direction (`w`, `arity = 0`, Schanuel presheaf model with fresh binder `И`). -/
def nominal : Dir :=
  { name := "w", arity := 0, fibrant := false, internal := true }

instance : ToString Dir where
  toString d := d.name

end Dir

/-- An endpoint of a 1-cube in direction `g`.
    Note: when `g = Dir.nominal` (`arity = 0`), `Endpoint g = Fin 0` is uninhabited,
    statically ruling out strict boundary faces in purely nominal dimensions! -/
abbrev Endpoint (g : Dir) : Type := Fin g.arity

end Narya.Dim
