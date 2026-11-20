import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Elaboration

/-!
# Well-formedness: a positive and a negative program for each clause, and the controls

Every row is decided by the kernel (`decide`). For each clause of `WellFormed` (patterns, scope,
distinct sites) and for the surface clause (consistent declarations): one program that passes and one
that fails exactly that clause. The pattern clause's control shows where the class stops: an unknown
applied to a constant has two solutions with different readings (`outside_class_not_principal`). The
class does not keep such stores out of runs: `ExampleWaiting` has a well-formed program whose run
reaches one with no most general solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExamplesWellFormed

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration

/-! ## Names used below -/

/-- A second-order unknown of one parameter, unopened, of a site. -/
def holeKey (site : List ℕ) (index : ℕ) : MKey := ⟨site, index, ([()], ())⟩

/-- `$F x` under one binder: the unknown applied to the bound variable. -/
def holeAtBound (site : List ℕ) (index : ℕ) : Term (signature MSig (fam mkeys)) [()] () :=
  .op (.inr (.mk ⟨[], holeKey site index⟩)) (.cons (.var .zero) .nil)

/-- `$F a`: the unknown applied to a datum. -/
def holeAt (site : List ℕ) (index : ℕ) (a : MData) : MData :=
  .op (.inr (.mk ⟨[], holeKey site index⟩)) (.cons a .nil)

/-- `(lam x. body)`. -/
def lam (body : Term (signature MSig (fam mkeys)) [()] ()) : MData := .op (.inl .lam) (.cons body .nil)

abbrev C := Comp mkeys [] () MTy
abbrev E := Equation mkeys [] () MTy
abbrev P := Program mkeys [] () MTy

/-- A program from its equations (text is read as a root call). -/
def prog (eqs : List E) : P := ⟨eqs, fun t => .apply t⟩

/-! ## Patterns -/

/-- `(= (f (lam x. $F x)) (lam y. $F y))`: a second-order pattern under a binder. -/
def patternGood : P :=
  prog [⟨[100], tuple [sym "f", lam (holeAtBound [100] 0)], .ret (lam (holeAtBound [100] 0))⟩]

/-- `(= (f ($F a)) a)`: the unknown applied to a constant, outside the class. -/
def patternBad : P :=
  prog [⟨[100], tuple [sym "f", holeAt [100] 0 (sym "a")], .ret (sym "a")⟩]

theorem patternGood_wellFormed : WellFormed patternGood := by decide
theorem patternBad_not_wellFormed : ¬ WellFormed patternBad := by decide

/-- `(= (app (lam x. $F x) $a) ($F $a))`: the right-hand side applies `$F` to a datum, which its
left-hand side determines. -/
def beta : P :=
  prog [⟨[100], tuple [sym "app", lam (holeAtBound [100] 0), mvar [100] 1],
    .ret (holeAt [100] 0 (mvar [100] 1))⟩]

/-- `(= (f $x) ($G a))`: an undetermined unknown applied to a constant. -/
def undetermined : P :=
  prog [⟨[100], tuple [sym "f", mvar [100] 0], .ret (holeAt [100] 1 (sym "a"))⟩]

theorem beta_wellFormed : WellFormed beta := by decide
theorem undetermined_not_wellFormed : ¬ WellFormed undetermined := by decide

/-! ## Scope -/

/-- `(= (f $x) (let $y $x $y))`: the arrow's own name only in its pattern and body. -/
def scopeGood : P :=
  prog [⟨[100], tuple [sym "f", mvar [100] 0],
    .let_ [101] (mvar [101] 0) (.ret (mvar [100] 0)) (.ret (mvar [101] 0))⟩]

/-- The arrow's own name used in the computation it binds, where it is not in scope. -/
def scopeBad : P :=
  prog [⟨[100], tuple [sym "f", mvar [100] 0],
    .let_ [101] (mvar [101] 0) (.ret (mvar [101] 0)) (.ret (mvar [101] 0))⟩]

/-- A name crossing into an arrow's pattern (the outer `$x` refined by the arrow) is in scope. -/
def scopeCrossing : P :=
  prog [⟨[100], tuple [sym "f", mvar [100] 0],
    .let_ [101] (tuple [mvar [100] 0, mvar [101] 0]) (.ret (tuple [num 1, num 2])) (.ret (mvar [101] 0))⟩]

theorem scopeGood_wellFormed : WellFormed scopeGood := by decide
theorem scopeBad_not_wellFormed : ¬ WellFormed scopeBad := by decide
theorem scopeCrossing_wellFormed : WellFormed scopeCrossing := by decide

/-! ## Distinct sites -/

/-- Two nested arrows at two sites. -/
def sitesGood : P :=
  prog [⟨[100], tuple [sym "f"],
    .let_ [101] (mvar [101] 0) (.ret (num 1))
      (.let_ [102] (mvar [102] 0) (.ret (num 2)) (.ret (tuple [mvar [101] 0, mvar [102] 0])))⟩]

/-- The same arrows sharing one site. -/
def sitesBad : P :=
  prog [⟨[100], tuple [sym "f"],
    .let_ [101] (mvar [101] 0) (.ret (num 1))
      (.let_ [101] (mvar [101] 1) (.ret (num 2)) (.ret (tuple [mvar [101] 0, mvar [101] 1])))⟩]

theorem sitesGood_wellFormed : WellFormed sitesGood := by decide
theorem sitesBad_not_wellFormed : ¬ WellFormed sitesBad := by decide

/-! ## Declarations (surface) -/

theorem declarations_consistent :
    DeclarationsConsistent [⟨"f", [.atom, .value "Number"], .undefined⟩,
      ⟨"f", [.code "Expr", .undefined], .value "Number"⟩] := by decide

theorem declarations_conflict :
    ¬ DeclarationsConsistent [⟨"f", [.atom, .value "Number"], .undefined⟩,
      ⟨"f", [.value "Number", .value "Number"], .undefined⟩] := by decide

/-! ## Why the pattern class stops there -/

/-- The datum `(g a a)`. -/
def gaa : MData := tuple [sym "g", sym "a", sym "a"]

/-- The two closed solutions of `$F a ≐ (g a a)` at `$F`: `λx. g x x` and `λx. g a a`. -/
def bodyBoth : Term MSig [()] () :=
  .op (.tup 3) (.cons (.op (.sym "g") .nil) (.cons (.var .zero) (.cons (.var .zero) .nil)))
def bodyConst : Term MSig [()] () :=
  .op (.tup 3) (.cons (.op (.sym "g") .nil) (.cons (.op (.sym "a") .nil) (.cons (.op (.sym "a") .nil) .nil)))

/-- The image of a name of each arity: `body` for one parameter, `a` otherwise. -/
def bodyFor (body : Term MSig [()] ()) (Δ : List Unit) : Term MSig Δ () :=
  match Δ with
  | [()] => body
  | _ => rename (Γ := []) (fun _ impossible => nomatch impossible) (csym "a")

/-- A solution sending every one-parameter unknown to `body`, and every other name to `a`. -/
def solveWith (body : Term MSig [()] ()) : Assignment (fam mkeys) noNames :=
  fun x => Rigid.includeTerm noNames (bodyFor body x.key.arity.1)

/-- **The control**: the store `$F a ≐ (g a a)` reads `$F b` both as `(g b b)` and as `(g a a)`. Two
readings alone do not refute a most general solution (the empty store reads a name in many ways and
has one); that a store of this kind has none is `ExampleWaiting.no_principal`. -/
theorem outside_class_not_principal :
    Reads [(holeAt [100] 0 (sym "a"), gaa)] (holeAt [100] 0 (sym "b"))
        (ctuple [csym "g", csym "b", csym "b"]) ∧
      Reads [(holeAt [100] 0 (sym "a"), gaa)] (holeAt [100] 0 (sym "b"))
        (ctuple [csym "g", csym "a", csym "a"]) :=
  ⟨⟨Empty, noNames, solveWith bodyBoth, fun e member => by
      rw [List.mem_singleton.mp member]; rfl, rfl⟩,
    ⟨Empty, noNames, solveWith bodyConst, fun e member => by
      rw [List.mem_singleton.mp member]; rfl, rfl⟩⟩

/-- The two readings of `$F b` differ, so that store does not determine `$F b`. -/
theorem outside_class_readings_differ :
    ctuple [csym "g", csym "b", csym "b"] ≠ ctuple [csym "g", csym "a", csym "a"] := by
  decide

#print axioms patternGood_wellFormed
#print axioms patternBad_not_wellFormed
#print axioms scopeBad_not_wellFormed
#print axioms sitesBad_not_wellFormed
#print axioms declarations_conflict
#print axioms outside_class_not_principal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExamplesWellFormed
