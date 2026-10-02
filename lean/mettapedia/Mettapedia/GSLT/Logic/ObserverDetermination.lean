import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity

/-!
# How an equivalence determines its admissible observers

A context is admissible for a relation when it preserves it.  Starting from an
admissible class `A`, the *determination step* `A.determined obs` collects the
contexts that preserve the `A`-relative equivalence.  This module proves:

* `le_determined`: `A ≤ A.determined obs` (every context of `A` preserves the
  `A`-relative equivalence);
* `relEquiv_determined_iff`: the determined class has the same relative
  equivalence as `A`;
* `determined_idempotent`: determination is idempotent, so the determined class
  is a fixed point after one round;
* `le_determined_of_relEquiv_iff`: the determined class is the largest class
  with that equivalence.

The step is inflationary and idempotent but not monotone; the controls module
exhibits classes `A ≤ B` with `A.determined obs ≰ B.determined obs`.  The
underlying reason is that preservation of a relation is of mixed variance: a
context can preserve a coarse relation and fail to preserve a finer one, and
conversely.

The *two-step determination* fixes a set of mandatory interaction contexts,
takes the relative equivalence of the class they generate, and then takes the
class of all contexts preserving it (`relEquiv_dStar_iff`, `dStar_largest`).
The top class is always a fixed point too (`determined_top`), with the finest
equivalence, so "the greatest fixed point" in the class order is the top class,
and it is the mandatory contexts that select the behavioural solution.

Finally, `relEquiv_sup_generatedBy_iff` characterises conservative extensions of
an observer class: adding contexts to `A` leaves the relative equivalence
unchanged exactly when every added context preserves it, and a single added
context that does not preserve it separates a pair the old class identifies
(`not_relEquiv_sup_of_not_preserved`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.AdmissibleContextCongruence

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext

universe uS uContext uRule uAtom

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}

/-- A context preserves a relation when it maps related terms to related terms. -/
def Preserves (context : rules.Context) (relation : S.Term → S.Term → Prop) : Prop :=
  ∀ ⦃left right : S.Term⦄, relation left right →
    relation (rules.plug context left) (rules.plug context right)

/-- A relation respects the equations when it is invariant under them on both
sides. -/
def RespectsEquations (relation : S.Term → S.Term → Prop) : Prop :=
  ∀ ⦃left left' right right' : S.Term⦄, S.Equiv left left' → S.Equiv right right' →
    relation left right → relation left' right'

namespace AdmissibleClass

/-- **The admissible class of a relation**: the contexts that preserve it.  It
is closed under composition because the relation respects the equations. -/
def admissibleFor (relation : S.Term → S.Term → Prop) (respects : RespectsEquations relation) :
    AdmissibleClass rules where
  Admissible context := Preserves context relation
  identity_mem := fun left right related =>
    respects (S.equations.iseqv.symm (rules.plug_identity left))
      (S.equations.iseqv.symm (rules.plug_identity right)) related
  compose_mem := fun {outer inner} preservesOuter preservesInner left right related =>
    respects (S.equations.iseqv.symm (rules.plug_compose outer inner left))
      (S.equations.iseqv.symm (rules.plug_compose outer inner right))
      (preservesOuter (preservesInner related))

theorem admissibleFor_admissible {relation : S.Term → S.Term → Prop}
    {respects : RespectsEquations relation} {context : rules.Context} :
    (admissibleFor relation respects).Admissible context ↔ Preserves context relation :=
  Iff.rfl

variable (observations : ContextualRules.Observations.{uAtom} S)

theorem relEquiv_respectsEquations (A : AdmissibleClass rules) :
    RespectsEquations (A.RelEquiv observations) :=
  fun _ _ _ _ leftEquivalent rightEquivalent related =>
    A.relEquiv_of_equiv_of_equiv observations leftEquivalent rightEquivalent related

/-- **The determination step**: all contexts that preserve the `A`-relative
equivalence. -/
def determined (A : AdmissibleClass rules) : AdmissibleClass rules :=
  admissibleFor (A.RelEquiv observations) (A.relEquiv_respectsEquations observations)

theorem determined_admissible {A : AdmissibleClass rules} {context : rules.Context} :
    (A.determined observations).Admissible context ↔
      Preserves context (A.RelEquiv observations) :=
  Iff.rfl

/-- Determination is inflationary: this is T1. -/
theorem le_determined (A : AdmissibleClass rules) : A ≤ A.determined observations :=
  fun _ admissible _ _ related => A.relEquiv_closedUnder observations admissible related

/-- **The determined class has the same equivalence.**  One inclusion is T2;
the other is T3, since the `A`-relative equivalence is a reduction bisimulation
closed under the determined class by definition. -/
theorem relEquiv_determined_iff (A : AdmissibleClass rules) {left right : S.Term} :
    (A.determined observations).RelEquiv observations left right ↔
      A.RelEquiv observations left right :=
  ⟨AdmissibleClass.relEquiv_antitone observations (A.le_determined observations),
    fun related => (A.determined observations).relEquiv_of_isReductionBisimulation observations
      (A.isReductionBisimulation_relEquiv observations)
      (fun _ _ _ admissible held => admissible held) related⟩

/-- **The determined class is the largest class with that equivalence** (T5):
every context of a class preserves that class's own equivalence. -/
theorem le_determined_of_relEquiv_iff (A B : AdmissibleClass rules)
    (same : ∀ left right, B.RelEquiv observations left right ↔ A.RelEquiv observations left right) :
    B ≤ A.determined observations := by
  intro context admissible left right related
  exact (same _ _).mp
    (B.relEquiv_closedUnder observations admissible ((same _ _).mpr related))

/-- Determination is idempotent: one round reaches a fixed point. -/
theorem determined_idempotent (A : AdmissibleClass rules) :
    (A.determined observations).determined observations = A.determined observations := by
  ext context
  constructor
  · intro preserves left right related
    exact (A.relEquiv_determined_iff observations).mp
      (preserves ((A.relEquiv_determined_iff observations).mpr related))
  · intro preserves left right related
    exact (A.relEquiv_determined_iff observations).mpr
      (preserves ((A.relEquiv_determined_iff observations).mp related))

/-- The fixed points of determination are the classes that contain every
context preserving their own equivalence. -/
theorem determined_eq_self_iff (A : AdmissibleClass rules) :
    A.determined observations = A ↔
      ∀ context, Preserves context (A.RelEquiv observations) → A.Admissible context := by
  constructor
  · intro fixed context preserves
    rw [← fixed]
    exact preserves
  · intro closed
    exact le_antisymm (fun context preserves => closed context preserves)
      (A.le_determined observations)

/-- The top class is always a fixed point, with the finest equivalence. -/
theorem determined_top :
    (⊤ : AdmissibleClass rules).determined observations = ⊤ :=
  le_antisymm le_top ((⊤ : AdmissibleClass rules).le_determined observations)

/-! ## Conservative and strict extensions of an observer class -/

/-- **Extension criterion.**  A class `B ≥ A` has the same relative equivalence
as `A` exactly when every context of `B` preserves the `A`-relative
equivalence. -/
theorem relEquiv_iff_iff_le_determined {A B : AdmissibleClass rules} (le : A ≤ B) :
    (∀ left right, B.RelEquiv observations left right ↔ A.RelEquiv observations left right) ↔
      B ≤ A.determined observations := by
  constructor
  · exact A.le_determined_of_relEquiv_iff observations B
  · intro below left right
    refine ⟨AdmissibleClass.relEquiv_antitone observations le, fun related => ?_⟩
    exact AdmissibleClass.relEquiv_antitone observations below
      ((A.relEquiv_determined_iff observations).mpr related)

/-- **Adding observers.**  Adjoining a set of contexts to `A` is conservative
exactly when every adjoined context preserves the `A`-relative equivalence. -/
theorem relEquiv_sup_generatedBy_iff (A : AdmissibleClass rules)
    (added : Set rules.Context) :
    (∀ left right, (A ⊔ generatedBy added).RelEquiv observations left right ↔
        A.RelEquiv observations left right) ↔
      ∀ context ∈ added, Preserves context (A.RelEquiv observations) := by
  rw [relEquiv_iff_iff_le_determined observations le_sup_left, sup_le_iff, generatedBy_le_iff]
  exact ⟨fun both context member => both.2 member,
    fun preserved => ⟨A.le_determined observations, fun context member => preserved context member⟩⟩

/-- **Strict extension.**  An adjoined context that maps an `A`-equivalent pair
to an `A`-inequivalent pair separates that pair in the extended class. -/
theorem not_relEquiv_sup_of_not_preserved (A : AdmissibleClass rules)
    {added : Set rules.Context} {context : rules.Context} (member : context ∈ added)
    {left right : S.Term}
    (separated : ¬ A.RelEquiv observations (rules.plug context left) (rules.plug context right)) :
    ¬ (A ⊔ generatedBy added).RelEquiv observations left right := by
  intro related
  have admissible : (A ⊔ generatedBy added).Admissible context :=
    (le_sup_right : generatedBy added ≤ A ⊔ generatedBy added) context (generator_mem member)
  exact separated (AdmissibleClass.relEquiv_antitone observations le_sup_left
    ((A ⊔ generatedBy added).relEquiv_closedUnder observations admissible related))

/-! ## Two-step determination from mandatory interaction contexts -/

/-- The equivalence fixed by the mandatory interaction contexts: the relative
equivalence of the class they generate. -/
def equivStar (mandatory : Set rules.Context) (left right : S.Term) : Prop :=
  (generatedBy mandatory).RelEquiv observations left right

/-- The class determined by the mandatory interaction contexts: every context
that preserves `equivStar`. -/
def dStar (mandatory : Set rules.Context) : AdmissibleClass rules :=
  (generatedBy mandatory).determined observations

/-- The mandatory contexts are admissible for their own equivalence. -/
theorem generatedBy_le_dStar (mandatory : Set rules.Context) :
    generatedBy mandatory ≤ dStar observations mandatory :=
  (generatedBy mandatory).le_determined observations

/-- **T4 (fixed point).**  The determined class has exactly the equivalence the
mandatory contexts fix. -/
theorem relEquiv_dStar_iff (mandatory : Set rules.Context) {left right : S.Term} :
    (dStar observations mandatory).RelEquiv observations left right ↔
      equivStar observations mandatory left right :=
  (generatedBy mandatory).relEquiv_determined_iff observations

/-- The determined class is a fixed point of determination. -/
theorem dStar_determined (mandatory : Set rules.Context) :
    (dStar observations mandatory).determined observations = dStar observations mandatory :=
  (generatedBy mandatory).determined_idempotent observations

/-- **T5 (largest).**  Every class whose relative equivalence is `equivStar` is
contained in the determined class. -/
theorem dStar_largest (mandatory : Set rules.Context) (B : AdmissibleClass rules)
    (same : ∀ left right, B.RelEquiv observations left right ↔
      equivStar observations mandatory left right) :
    B ≤ dStar observations mandatory :=
  (generatedBy mandatory).le_determined_of_relEquiv_iff observations B same

end AdmissibleClass

end Mettapedia.GSLT.AdmissibleContextCongruence
