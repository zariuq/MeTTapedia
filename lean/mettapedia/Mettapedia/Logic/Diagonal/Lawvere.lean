import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Defs
import Mettapedia.Computability.ReflectiveCode

/-!
# Lawvere's diagonal argument, relative to a relation and a class of maps

Lawvere (1969): if `e : C → C → Y` is surjective onto `C → Y`, every
endomap of `Y` has a fixed point.  Mathlib states this for types as
`Function.exists_fixed_point_of_surjective`.  Every use of the argument in this
development needs a weaker hypothesis, and one step of the proof suffices:

* **the diagonal step** (`diagonal`): if some code `c` represents the map
  `x ↦ f (e x x)`, up to a relation `R`, then `e c c` is an `R`-fixed point of
  `f`.  Nothing else is used.

Surjectivity is replaced by *representability of the diagonal composite*,
relative to a relation (equality, extensional equality of programs, one-step
reduction, convertibility) and to a class of maps (all maps, computable maps,
polynomial maps).

**Positive reading** (fixed points, recursion): `exists_fixedPoint`,
`lawvere`, and, through the relation, Kleene's recursion theorem, the
fixed-point combinator and replication (in their own modules).

**Negative reading** (no total internal decision):
`not_representable_of_fixedPointFree`; Cantor (`cantor_surjective'`,
recovering `Function.cantor_surjective`), Tarski's form for Boolean
predicates (`not_surjective_bool`), and the abstract form of Rice's theorem
(`not_representable_decider`): an `R`-invariant property that holds somewhere
and fails somewhere has no decider whose diagonal composite is represented.

**Code/behaviour retractions** (`exists_fixedPoint_of_staticBeta`,
`exists_fixedPoint_of_betaAlong`): a reflective interface whose processes are
maps on names, with `drop (quote p) = p` (or `≈ p`), is point-surjective, so
every endomap of the values has a fixed point.  Consequently no such interface
exists onto Boolean predicates (`not_staticBeta_bool`): the retraction can
only hold on a fragment.

**Controls.**  The unit type admits a surjective code map
(`unit_surjective`), where every endomap has its fixed point.  A code map
that is not surjective coexists with a fixed-point-free endomap
(`constantRun_not_surjective`, `bool_not_fixedPointFree`).  A map class that
is represented but not closed under the diagonal composite gives no fixed
point (`constantMaps_pointSurjective`, `not_diagonal_mem_constantMaps`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Diagonal

universe u v

section Relative

variable {Code : Type u} {Value : Type v}

/-- `code` represents `g` through `run`, up to `R`: running `code` on any
argument gives a value `R`-related to `g` of that argument. -/
def RepresentsBy (run : Code → Code → Value) (R : Value → Value → Prop) (code : Code)
    (g : Code → Value) : Prop :=
  ∀ argument, R (run code argument) (g argument)

/-- Some code represents `g` up to `R`. -/
def Representable (run : Code → Code → Value) (R : Value → Value → Prop)
    (g : Code → Value) : Prop :=
  ∃ code, RepresentsBy run R code g

/-- **Point-surjectivity relative to a class of maps**: every map of the class
is represented up to `R`. -/
def PointSurjectiveOn (run : Code → Code → Value) (R : Value → Value → Prop)
    (maps : Set (Code → Value)) : Prop :=
  ∀ g ∈ maps, Representable run R g

/-- The diagonal composite of an endomap: run the argument on itself, then
apply `f`. -/
def diagonalComposite (run : Code → Code → Value) (f : Value → Value) : Code → Value :=
  fun argument => f (run argument argument)

/-- **The diagonal step.**  If `code` represents the diagonal composite of `f`
up to `R`, then running `code` on itself gives an `R`-fixed point of `f`. -/
theorem diagonal (run : Code → Code → Value) (R : Value → Value → Prop) (f : Value → Value)
    {code : Code} (represents : RepresentsBy run R code (diagonalComposite run f)) :
    R (run code code) (f (run code code)) :=
  represents code

/-- **Lawvere's fixed-point theorem, relative form.** -/
theorem exists_fixedPoint (run : Code → Code → Value) (R : Value → Value → Prop)
    (f : Value → Value) (representable : Representable run R (diagonalComposite run f)) :
    ∃ value, R value (f value) :=
  let ⟨_, represents⟩ := representable
  ⟨_, diagonal run R f represents⟩

/-- The same, from point-surjectivity on a class closed under the diagonal
composite of `f`. -/
theorem exists_fixedPoint_of_pointSurjectiveOn {run : Code → Code → Value}
    {R : Value → Value → Prop} {maps : Set (Code → Value)}
    (surjective : PointSurjectiveOn run R maps) (f : Value → Value)
    (closed : diagonalComposite run f ∈ maps) : ∃ value, R value (f value) :=
  exists_fixedPoint run R f (surjective _ closed)

/-- **Contrapositive.**  If `f` has no `R`-fixed point, no code represents its
diagonal composite. -/
theorem not_representable_of_fixedPointFree (run : Code → Code → Value)
    (R : Value → Value → Prop) {f : Value → Value} (free : ∀ value, ¬ R value (f value)) :
    ¬ Representable run R (diagonalComposite run f) := by
  intro representable
  obtain ⟨value, fixed⟩ := exists_fixedPoint run R f representable
  exact free value fixed

/-- A class closed under the diagonal composite of a fixed-point-free map is
not represented. -/
theorem not_pointSurjectiveOn_of_fixedPointFree {run : Code → Code → Value}
    {R : Value → Value → Prop} {maps : Set (Code → Value)} {f : Value → Value}
    (free : ∀ value, ¬ R value (f value)) (closed : diagonalComposite run f ∈ maps) :
    ¬ PointSurjectiveOn run R maps :=
  fun surjective => not_representable_of_fixedPointFree run R free (surjective _ closed)

end Relative

/-! ## The surjective case -/

section Surjective

variable {Code : Type u} {Value : Type v}

/-- A surjective code map represents every map, up to equality. -/
theorem representable_of_surjective {run : Code → Code → Value}
    (surjective : Function.Surjective run) (g : Code → Value) :
    Representable run (fun value value' => value' = value) g :=
  let ⟨code, runs⟩ := surjective g
  ⟨code, fun argument => congrFun runs argument ▸ rfl⟩

/-- **Lawvere's fixed-point theorem** (1969), for types: a surjection
`Code → (Code → Value)` forces every endomap of `Value` to have a fixed point.
This is the statement of Mathlib's `Function.exists_fixed_point_of_surjective`,
obtained here from the relative form. -/
theorem lawvere {run : Code → Code → Value} (surjective : Function.Surjective run)
    (f : Value → Value) : ∃ value, f value = value :=
  exists_fixedPoint run (fun value value' => value' = value) f
    (representable_of_surjective surjective _)

/-- **Contrapositive**: a fixed-point-free endomap rules out every surjection
onto the maps into its type. -/
theorem not_surjective_of_fixedPointFree {f : Value → Value} (free : ∀ value, f value ≠ value)
    (run : Code → Code → Value) : ¬ Function.Surjective run := by
  intro surjective
  obtain ⟨value, fixed⟩ := lawvere surjective f
  exact free value fixed

/-- Negation of propositions has no fixed point. -/
theorem not_fixedPointFree (proposition : Prop) : (¬ proposition) ≠ proposition := by
  intro same
  have holds : proposition ↔ ¬ proposition := Iff.of_eq same.symm
  have notHolds : ¬ proposition := fun p => holds.mp p p
  exact notHolds (holds.mpr notHolds)

/-- **Cantor's theorem** from Lawvere's: no surjection onto the subsets.  This
is Mathlib's `Function.cantor_surjective`, with `Set α = α → Prop` and `Not`
as the fixed-point-free endomap. -/
theorem cantor_surjective' {α : Type u} (e : α → Set α) : ¬ Function.Surjective e :=
  not_surjective_of_fixedPointFree (f := Not) not_fixedPointFree e

/-- Boolean negation has no fixed point. -/
theorem bool_not_fixedPointFree : ∀ value : Bool, (!value) ≠ value := by decide

/-- **Tarski's form**: no code map is surjective onto the Boolean predicates on
codes. -/
theorem not_surjective_bool (run : Code → Code → Bool) : ¬ Function.Surjective run :=
  not_surjective_of_fixedPointFree bool_not_fixedPointFree run

/-- **In types, point-surjectivity forces triviality**: a surjection onto
`Code → Value` makes `Value` a subsingleton.  Decidable equality on `Value`
builds the fixed-point-free swap without choice. -/
theorem subsingleton_of_surjective [DecidableEq Value] {run : Code → Code → Value}
    (surjective : Function.Surjective run) : Subsingleton Value := by
  refine ⟨fun first second => ?_⟩
  by_contra different
  have free : ∀ value : Value, (if value = first then second else first) ≠ value := by
    intro value
    by_cases isFirst : value = first
    · rw [if_pos isFirst, isFirst]
      exact fun same => different same.symm
    · rw [if_neg isFirst]
      exact fun same => isFirst same.symm
  exact not_surjective_of_fixedPointFree free run surjective

end Surjective

/-! ## The negative reading: no internal decider -/

section Decider

variable {Code : Type u} {Value : Type v}

/-- The swap of a decider: answer `no` where the decider says the property
holds, and `yes` elsewhere. -/
def swap (decide : Value → Bool) (yes no : Value) (value : Value) : Value :=
  bif decide value then no else yes

/-- **The swap of a correct decider of an `R`-invariant property has no
`R`-fixed point**, when `yes` has the property and `no` lacks it. -/
theorem swap_fixedPointFree (R : Value → Value → Prop) {P : Value → Prop}
    (invariant : ∀ {value value' : Value}, R value value' → (P value ↔ P value'))
    {decide : Value → Bool} (correct : ∀ value, decide value = true ↔ P value)
    {yes no : Value} (yesHolds : P yes) (noFails : ¬ P no) :
    ∀ value, ¬ R value (swap decide yes no value) := by
  intro value related
  have same := invariant related
  cases decided : decide value with
  | false =>
      rw [swap, decided, cond_false] at same
      exact (by simpa using decided : ¬ decide value = true)
        ((correct value).mpr (same.mpr yesHolds))
  | true =>
      rw [swap, decided, cond_true] at same
      exact noFails (same.mp ((correct value).mp decided))

/-- **Abstract Rice theorem.**  If an `R`-invariant property holds at `yes` and
fails at `no`, then for any correct decider the diagonal composite of its swap
is not represented.  Read positively: an internal decider (one whose composites
are represented) of a nontrivial invariant property does not exist. -/
theorem not_representable_decider (run : Code → Code → Value) (R : Value → Value → Prop)
    {P : Value → Prop}
    (invariant : ∀ {value value' : Value}, R value value' → (P value ↔ P value'))
    {decide : Value → Bool} (correct : ∀ value, decide value = true ↔ P value)
    {yes no : Value} (yesHolds : P yes) (noFails : ¬ P no) :
    ¬ Representable run R (diagonalComposite run (swap decide yes no)) :=
  not_representable_of_fixedPointFree run R
    (swap_fixedPointFree R invariant correct yesHolds noFails)

end Decider

/-! ## Code/behaviour retractions -/

section Retraction

open Mettapedia.Computability.ReflectiveCode

variable {Name : Type u} {Value : Type v}

/-- A reflective interface whose processes are the maps on names, with literal
beta `drop (quote p) = p`, makes `drop` a surjection onto the maps on names:
every endomap of the values has a fixed point. -/
theorem exists_fixedPoint_of_staticBeta (interface : Interface (Name → Value) Name)
    (beta : interface.StaticBeta) (f : Value → Value) : ∃ value, f value = value :=
  lawvere (Interface.drop_surjective_of_staticBeta interface beta) f

/-- Relative beta, pointwise up to `R`, gives `R`-fixed points: the quote of a
map represents it. -/
theorem exists_fixedPoint_of_betaAlong (interface : Interface (Name → Value) Name)
    (R : Value → Value → Prop)
    (beta : interface.BetaAlong fun first second => ∀ name, R (first name) (second name))
    (f : Value → Value) : ∃ value, R value (f value) :=
  exists_fixedPoint interface.drop R f
    ⟨interface.quote (diagonalComposite interface.drop f),
      beta (diagonalComposite interface.drop f)⟩

/-- **The retraction holds only on a fragment**: no reflective interface onto
the Boolean predicates on names satisfies literal beta. -/
theorem not_staticBeta_bool (interface : Interface (Name → Bool) Name) :
    ¬ interface.StaticBeta := by
  intro beta
  obtain ⟨value, fixed⟩ := exists_fixedPoint_of_staticBeta interface beta (fun b => !b)
  exact bool_not_fixedPointFree value fixed

end Retraction

/-! ## Controls -/

section Controls

/-- **Positive control.**  Onto the unit type, a code map is surjective, and
every endomap has its fixed point. -/
theorem unit_surjective : Function.Surjective (fun (_ _ : Unit) => ()) :=
  fun _ => ⟨(), funext fun _ => rfl⟩

theorem unit_fixedPoint (f : Unit → Unit) : ∃ value, f value = value :=
  lawvere unit_surjective f

/-- A code map whose codes run as constants. -/
def constantRun (code _argument : Bool) : Bool := code

/-- **Negative control.**  The constant code map is not surjective (the
identity is not a constant), and Boolean negation, which it cannot contradict,
has no fixed point: without point-surjectivity, fixed-point-free endomaps
exist. -/
theorem constantRun_not_surjective : ¬ Function.Surjective constantRun := by
  intro surjective
  obtain ⟨code, runs⟩ := surjective id
  have atFalse := congrFun runs false
  have atTrue := congrFun runs true
  simp only [constantRun, id] at atFalse atTrue
  exact Bool.false_ne_true (atFalse.symm.trans atTrue)

/-- The constant maps on Booleans. -/
def constantMaps : Set (Bool → Bool) := {g | ∀ first second, g first = g second}

/-- **A represented class that is not closed under the diagonal composite.**
The constant code map represents every constant map exactly. -/
theorem constantMaps_pointSurjective :
    PointSurjectiveOn constantRun (fun value value' => value = value') constantMaps := by
  intro g constant
  exact ⟨g false, fun argument => constant false argument⟩

/-- The diagonal composite of negation is not constant, so the class escapes
the diagonal argument, and negation keeps no fixed point. -/
theorem not_diagonal_mem_constantMaps :
    diagonalComposite constantRun (fun b => !b) ∉ constantMaps := by
  intro constant
  have := constant false true
  simp [diagonalComposite, constantRun] at this

end Controls

end Mettapedia.Logic.Diagonal
