import Mettapedia.Languages.OpenTheory.BindingRules

/-!
# OpenTheory theorem substitution

This module implements the ninth primitive theorem rule at OpenTheory
revision `f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`.  The source operation
substitutes the current sequent while preserving its axiom-provenance tags.

The admission object carries `TermSubst.TypeCorrect`; raw substitutions remain
available as syntax, but a wrong-typed map cannot inhabit the primitive rule's
input.  Hypothesis sets are mapped extensionally, so two substituted alpha
classes may lawfully collapse to one.
-/

namespace Mettapedia.Languages.OpenTheory

/-- A simultaneous type-and-term substitution admitted for theorem replay. -/
structure TypeCorrectTermSubstitution where
  raw : TermSubst
  typeCorrect : raw.TypeCorrect

namespace TypeCorrectTermSubstitution

/-- Apply an admitted substitution to one checked canonical term. -/
def apply (substitution : TypeCorrectTermSubstitution)
    (term : CanonicalTerm) : CanonicalTerm :=
  substitution.raw.applyChecked substitution.typeCorrect term

/-- Apply an admitted substitution to an extensional hypothesis set. -/
def applyHypotheses (substitution : TypeCorrectTermSubstitution)
    (hypotheses : Finset CanonicalTerm) : Finset CanonicalTerm :=
  hypotheses.image substitution.apply

end TypeCorrectTermSubstitution

/-! ## Independent structural semantics -/

/-- Structural graph of admitted substitution on one canonical term. -/
def TermSubstitutionSemantics
    (substitution : TypeCorrectTermSubstitution)
    (input output : CanonicalTerm) : Prop :=
  output.term = substitution.raw.applyDB input.term

/-- Structural graph of the extensional image of a hypothesis set. -/
def HypothesisSubstitutionSemantics
    (substitution : TypeCorrectTermSubstitution)
    (input output : Finset CanonicalTerm) : Prop :=
  ∀ term, term ∈ output ↔
    ∃ source ∈ input, TermSubstitutionSemantics substitution source term

theorem apply_eq_iff_termSubstitutionSemantics
    (substitution : TypeCorrectTermSubstitution)
    (input output : CanonicalTerm) :
    substitution.apply input = output ↔
      TermSubstitutionSemantics substitution input output := by
  constructor
  · intro equality
    rw [← equality]
    rfl
  · intro semantics
    apply CanonicalTerm.ext_term
    exact semantics.symm

theorem applyHypotheses_semantics
    (substitution : TypeCorrectTermSubstitution)
    (hypotheses : Finset CanonicalTerm) :
    HypothesisSubstitutionSemantics substitution hypotheses
      (substitution.applyHypotheses hypotheses) := by
  intro term
  simp only [TypeCorrectTermSubstitution.applyHypotheses, Finset.mem_image]
  constructor
  · rintro ⟨source, membership, equality⟩
    exact ⟨source, membership,
      (apply_eq_iff_termSubstitutionSemantics _ _ _).mp equality⟩
  · rintro ⟨source, membership, semantics⟩
    exact ⟨source, membership,
      (apply_eq_iff_termSubstitutionSemantics _ _ _).mpr semantics⟩

/-- The structural image relation determines its finite output exactly. -/
theorem HypothesisSubstitutionSemantics.unique
    {substitution : TypeCorrectTermSubstitution}
    {input left right : Finset CanonicalTerm}
    (leftSemantics : HypothesisSubstitutionSemantics substitution input left)
    (rightSemantics : HypothesisSubstitutionSemantics substitution input right) :
    left = right := by
  ext term
  rw [leftSemantics term, rightSemantics term]

/-- Declarative semantics of primitive theorem substitution. -/
def TheoremSubstitutionSemantics
    (substitution : TypeCorrectTermSubstitution)
    (input out : Theorem) : Prop :=
  out.axioms = input.axioms ∧
    HypothesisSubstitutionSemantics substitution
      input.sequent.hyp out.sequent.hyp ∧
    TermSubstitutionSemantics substitution
      input.sequent.concl out.sequent.concl

/-! ## Executable rule and exactness -/

/-- Apply a type-correct substitution to a theorem's current sequent. -/
def substituteTheorem
    (substitution : TypeCorrectTermSubstitution) (input : Theorem) : Theorem :=
  Theorem.preserveAxiomsResult input
    (substitution.applyHypotheses input.sequent.hyp)
    (substitution.apply input.sequent.concl)

/-- Uniform option-valued primitive-rule interface. -/
def checkTheoremSubstitution
    (substitution : TypeCorrectTermSubstitution) (input : Theorem) :
    Option Theorem :=
  some (substituteTheorem substitution input)

theorem substituteTheorem_semantics
    (substitution : TypeCorrectTermSubstitution) (input : Theorem) :
    TheoremSubstitutionSemantics substitution input
      (substituteTheorem substitution input) := by
  refine ⟨rfl, applyHypotheses_semantics substitution input.sequent.hyp, ?_⟩
  rw [← apply_eq_iff_termSubstitutionSemantics]
  rfl

theorem TheoremSubstitutionSemantics.unique
    {substitution : TypeCorrectTermSubstitution} {input left right : Theorem}
    (leftSemantics : TheoremSubstitutionSemantics substitution input left)
    (rightSemantics : TheoremSubstitutionSemantics substitution input right) :
    left = right := by
  apply Theorem.ext
  · exact leftSemantics.1.trans rightSemantics.1.symm
  · apply Sequent.ext
    · exact leftSemantics.2.1.unique rightSemantics.2.1
    · have leftConclusion :
          substitution.apply input.sequent.concl = left.sequent.concl :=
        (apply_eq_iff_termSubstitutionSemantics _ _ _).mpr
          leftSemantics.2.2
      have rightConclusion :
          substitution.apply input.sequent.concl = right.sequent.concl :=
        (apply_eq_iff_termSubstitutionSemantics _ _ _).mpr
          rightSemantics.2.2
      exact leftConclusion.symm.trans rightConclusion

theorem checkTheoremSubstitution_eq_some_iff
    (substitution : TypeCorrectTermSubstitution)
    (input out : Theorem) :
    checkTheoremSubstitution substitution input = some out ↔
      TheoremSubstitutionSemantics substitution input out := by
  constructor
  · intro accepted
    have equality : substituteTheorem substitution input = out :=
      Option.some.inj accepted
    rw [← equality]
    exact substituteTheorem_semantics substitution input
  · intro semantics
    have equality :=
      (substituteTheorem_semantics substitution input).unique semantics
    exact congrArg some equality

/-- Primitive theorem substitution is deterministic. -/
theorem TheoremSubstitutionSemantics.deterministic
    {substitution : TypeCorrectTermSubstitution} {input left right : Theorem}
    (leftSemantics : TheoremSubstitutionSemantics substitution input left)
    (rightSemantics : TheoremSubstitutionSemantics substitution input right) :
    left = right :=
  leftSemantics.unique rightSemantics

/-! ## Positive and negative admission controls -/

namespace TheoremSubstitutionExamples

open BindingExamples

def renameXToYRaw : TermSubst :=
  ⟨TypeSubst.empty,
    [(xIndividual, CheckedSourceTerm.ofVariable yIndividual)]⟩

theorem renameXToY_typeCorrect : renameXToYRaw.TypeCorrect := by
  intro entry membership
  simp only [renameXToYRaw, List.mem_singleton] at membership
  subst entry
  rfl

def renameXToY : TypeCorrectTermSubstitution :=
  ⟨renameXToYRaw, renameXToY_typeCorrect⟩

def inputTheorem : Theorem := Theorem.emptyResult {freeX} freeX

def expectedTheorem : Theorem := Theorem.emptyResult {freeY} freeY

theorem renameXToY_freeX : renameXToY.apply freeX = freeY := by
  apply CanonicalTerm.ext_term
  change renameXToYRaw.applyDB freeX.term = freeY.term
  have variableUnchanged :
      renameXToYRaw.types.applyVar xIndividual = xIndividual := by
    simp [renameXToYRaw, TypeSubst.applyVar]
  have found :
      renameXToYRaw.lookup (renameXToYRaw.types.applyVar xIndividual) =
        some (CheckedSourceTerm.ofVariable yIndividual) := by
    rw [variableUnchanged]
    simp [renameXToYRaw, TermSubst.lookup, TermSubst.keySame]
  rw [show freeX.term = .free xIndividual by rfl,
    TermSubst.applyDB_free_of_lookup_some _ _ _ found]
  simp [CheckedSourceTerm.canonical, CheckedSourceTerm.ofVariable,
    freeY, SourceTerm.toDB, boundIndex]

/-- A nontrivial admitted substitution maps both hypothesis and conclusion. -/
theorem renameXToY_accepts :
    checkTheoremSubstitution renameXToY inputTheorem = some expectedTheorem := by
  apply (checkTheoremSubstitution_eq_some_iff _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro term
    simp only [inputTheorem, expectedTheorem, Theorem.emptyResult,
      Finset.mem_singleton]
    constructor
    · intro equality
      subst term
      exact ⟨freeX, rfl,
        (apply_eq_iff_termSubstitutionSemantics _ _ _).mp renameXToY_freeX⟩
    · rintro ⟨source, sourceEquality, semantics⟩
      subst source
      have resultEquality :=
        (apply_eq_iff_termSubstitutionSemantics _ _ _).mpr semantics
      exact resultEquality.symm.trans renameXToY_freeX
  · exact (apply_eq_iff_termSubstitutionSemantics _ _ _).mp
      renameXToY_freeX

def wrongTypeRaw : TermSubst :=
  ⟨TypeSubst.empty,
    [(xIndividual,
      CheckedSourceTerm.ofVariable
        ⟨Name.global "p", Ty.bool⟩)]⟩

/-- A wrong-typed term map cannot inhabit the primitive substitution input. -/
example : ¬ wrongTypeRaw.TypeCorrect := by
  intro allegedlyCorrect
  have entryCorrect := allegedlyCorrect
    (xIndividual,
      CheckedSourceTerm.ofVariable
        ⟨Name.global "p", Ty.bool⟩)
    (by simp [wrongTypeRaw])
  simp [CheckedSourceTerm.ofVariable, xIndividual, Examples.individual,
    Ty.bool, TypeOp.bool, Name.global] at entryCorrect

end TheoremSubstitutionExamples

end Mettapedia.Languages.OpenTheory
