import Mettapedia.Languages.OpenTheory.Binding
import Mettapedia.Languages.OpenTheory.CoreRules

/-!
# OpenTheory abstraction and beta-conversion rules

This module implements the two binding-sensitive primitive inference rules at
OpenTheory revision `f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`:

* `abs` abstracts both sides of an equality, provided the selected typed
  variable is not free in any hypothesis;
* `betaConv` contracts one root beta redex and proves the corresponding
  primitive equality.

Each executable operation is related to an independently stated structural
semantics.  Axiom provenance is preserved by `abs`; `betaConv` introduces no
axiom tag or hypothesis.
-/

namespace Mettapedia.Languages.OpenTheory

/-! ## Freshness at the theorem boundary -/

/-- One exact typed variable occurs freely in at least one hypothesis. -/
def FreeInHypotheses
    (sourceVar : SourceVar) (hypotheses : Finset CanonicalTerm) : Prop :=
  ∃ term ∈ hypotheses, DBTerm.FreeOccurrence sourceVar term.term

/-- Executable finite-hypothesis occurrence test. -/
def hasFreeInHypothesesB
    (sourceVar : SourceVar) (hypotheses : Finset CanonicalTerm) : Bool :=
  decide ((hypotheses.filter fun term =>
    DBTerm.hasFree sourceVar term.term = true).Nonempty)

/-- The executable hypothesis occurrence test is exact. -/
theorem hasFreeInHypothesesB_eq_true_iff
    (sourceVar : SourceVar) (hypotheses : Finset CanonicalTerm) :
    hasFreeInHypothesesB sourceVar hypotheses = true ↔
      FreeInHypotheses sourceVar hypotheses := by
  simp only [hasFreeInHypothesesB, decide_eq_true_eq,
    Finset.filter_nonempty_iff, DBTerm.hasFree_eq_true_iff,
    FreeInHypotheses]

theorem hasFreeInHypothesesB_eq_false_iff
    (sourceVar : SourceVar) (hypotheses : Finset CanonicalTerm) :
    hasFreeInHypothesesB sourceVar hypotheses = false ↔
      ¬ FreeInHypotheses sourceVar hypotheses := by
  rw [← Bool.not_eq_true]
  exact not_congr
    (hasFreeInHypothesesB_eq_true_iff sourceVar hypotheses)

namespace Theorem

/-- A unary primitive-rule result preserving exact axiom provenance. -/
def preserveAxiomsResult (input : Theorem)
    (hyp : Finset CanonicalTerm) (concl : CanonicalTerm) : Theorem :=
  { axioms := input.axioms
    axiomsBoolean := input.axiomsBoolean
    sequent := ⟨hyp, concl⟩ }

end Theorem

@[simp] theorem theorem_preserveAxiomsResult_eq_iff_hasParts
    (input : Theorem) (hyp : Finset CanonicalTerm)
    (concl : CanonicalTerm) (out : Theorem) :
    Theorem.preserveAxiomsResult input hyp concl = out ↔
      HasParts out input.axioms hyp concl := by
  constructor
  · intro equality
    subst out
    exact ⟨rfl, rfl, rfl⟩
  · intro parts
    exact parts.eq.symm

/-! ## Independent declarative semantics -/

/-- Declarative semantics of primitive theorem abstraction. -/
def AbsSemantics
    (sourceVar : SourceVar) (input out : Theorem) : Prop :=
  ¬ FreeInHypotheses sourceVar input.sequent.hyp ∧
    ∃ left right leftAbs rightAbs equality,
      CanonicalTerm.EqualityViewSemantics
        input.sequent.concl left right ∧
      CanonicalTerm.AbstractionSemantics sourceVar left leftAbs ∧
      CanonicalTerm.AbstractionSemantics sourceVar right rightAbs ∧
      CanonicalTerm.EqualityConstructionSemantics leftAbs rightAbs equality ∧
      HasParts out input.axioms input.sequent.hyp equality

/-- Declarative semantics of primitive beta conversion. -/
def BetaConvSemantics (redex : CanonicalTerm) (out : Theorem) : Prop :=
  ∃ reduced equality,
    CanonicalTerm.BetaReductionSemantics redex reduced ∧
      CanonicalTerm.EqualityConstructionSemantics redex reduced equality ∧
      HasParts out ∅ ∅ equality

/-! ## Executable rules -/

/-- Execute primitive abstraction with its exact hypothesis-freshness gate. -/
def checkAbs (sourceVar : SourceVar) (input : Theorem) : Option Theorem :=
  if hasFreeInHypothesesB sourceVar input.sequent.hyp then
    none
  else do
    let (left, right) ← input.sequent.concl.destEquality?
    let leftAbs := left.abstractFree sourceVar
    let rightAbs := right.abstractFree sourceVar
    let equality ← leftAbs.mkEquality? rightAbs
    pure (Theorem.preserveAxiomsResult input input.sequent.hyp equality)

/-- Execute primitive beta conversion on one checked root redex. -/
def checkBetaConv (redex : CanonicalTerm) : Option Theorem := do
  let reduced ← redex.betaReduce?
  let equality ← redex.mkEquality? reduced
  pure (Theorem.emptyResult ∅ equality)

/-! ## Exact success and failure correspondence -/

theorem checkAbs_eq_some_iff
    (sourceVar : SourceVar) (input out : Theorem) :
    checkAbs sourceVar input = some out ↔
      AbsSemantics sourceVar input out := by
  by_cases occurs :
      hasFreeInHypothesesB sourceVar input.sequent.hyp = true
  · have semOccurs : FreeInHypotheses sourceVar input.sequent.hyp :=
      (hasFreeInHypothesesB_eq_true_iff _ _).mp occurs
    simp [checkAbs, occurs, AbsSemantics, semOccurs]
  · have absentB :
        hasFreeInHypothesesB sourceVar input.sequent.hyp = false :=
      Bool.eq_false_of_not_eq_true occurs
    have semFresh : ¬ FreeInHypotheses sourceVar input.sequent.hyp :=
      (hasFreeInHypothesesB_eq_false_iff _ _).mp absentB
    simp [checkAbs, absentB, AbsSemantics, semFresh,
      Option.bind_eq_some_iff,
      CanonicalTerm.destEquality?_eq_some_iff,
      CanonicalTerm.abstractionSemantics_iff_eq,
      CanonicalTerm.mkEquality?_eq_some_iff]

theorem checkBetaConv_eq_some_iff
    (redex : CanonicalTerm) (out : Theorem) :
    checkBetaConv redex = some out ↔ BetaConvSemantics redex out := by
  simp [checkBetaConv, BetaConvSemantics, Option.bind_eq_some_iff,
    CanonicalTerm.betaReduce?_eq_some_iff,
    CanonicalTerm.mkEquality?_eq_some_iff]

private theorem option_eq_none_iff_no_semantics {alpha : Type}
    (result : Option alpha) (Semantics : alpha → Prop)
    (adequate : ∀ out, result = some out ↔ Semantics out) :
    result = none ↔ ¬ ∃ out, Semantics out := by
  constructor
  · intro rejected ⟨out, semantics⟩
    have accepted := (adequate out).mpr semantics
    rw [rejected] at accepted
    contradiction
  · intro impossible
    cases accepted : result with
    | none => rfl
    | some out =>
        exfalso
        exact impossible ⟨out, (adequate out).mp accepted⟩

theorem checkAbs_eq_none_iff
    (sourceVar : SourceVar) (input : Theorem) :
    checkAbs sourceVar input = none ↔
      ¬ ∃ out, AbsSemantics sourceVar input out := by
  apply option_eq_none_iff_no_semantics
  exact checkAbs_eq_some_iff sourceVar input

theorem checkBetaConv_eq_none_iff (redex : CanonicalTerm) :
    checkBetaConv redex = none ↔
      ¬ ∃ out, BetaConvSemantics redex out := by
  apply option_eq_none_iff_no_semantics
  exact checkBetaConv_eq_some_iff redex

/-! ## Proof-relevant rule evidence and dispatch -/

inductive BindingRequest where
  | abs (sourceVar : SourceVar) (input : Theorem)
  | betaConv (redex : CanonicalTerm)

inductive BindingEvidence : BindingRequest → Theorem → Type where
  | abs
      (fresh : ¬ FreeInHypotheses sourceVar input.sequent.hyp)
      (left right leftAbs rightAbs equality : CanonicalTerm)
      (view : CanonicalTerm.EqualityViewSemantics
        input.sequent.concl left right)
      (leftAbstraction : CanonicalTerm.AbstractionSemantics
        sourceVar left leftAbs)
      (rightAbstraction : CanonicalTerm.AbstractionSemantics
        sourceVar right rightAbs)
      (construction : CanonicalTerm.EqualityConstructionSemantics
        leftAbs rightAbs equality)
      (parts : HasParts out input.axioms input.sequent.hyp equality) :
      BindingEvidence (.abs sourceVar input) out
  | betaConv
      (reduced equality : CanonicalTerm)
      (reduction : CanonicalTerm.BetaReductionSemantics redex reduced)
      (construction : CanonicalTerm.EqualityConstructionSemantics
        redex reduced equality)
      (parts : HasParts out ∅ ∅ equality) :
      BindingEvidence (.betaConv redex) out

def BindingStep (request : BindingRequest) (out : Theorem) : Prop :=
  Nonempty (BindingEvidence request out)

theorem absSemantics_iff_bindingStep
    (sourceVar : SourceVar) (input out : Theorem) :
    AbsSemantics sourceVar input out ↔
      BindingStep (.abs sourceVar input) out := by
  constructor
  · rintro ⟨fresh, left, right, leftAbs, rightAbs, equality, view,
      leftAbstraction, rightAbstraction, construction, parts⟩
    exact ⟨BindingEvidence.abs fresh left right leftAbs rightAbs equality view
      leftAbstraction rightAbstraction construction parts⟩
  · rintro ⟨evidence⟩
    cases evidence with
    | abs fresh left right leftAbs rightAbs equality view leftAbstraction
        rightAbstraction construction parts =>
        exact ⟨fresh, left, right, leftAbs, rightAbs, equality, view,
          leftAbstraction, rightAbstraction, construction, parts⟩

theorem betaConvSemantics_iff_bindingStep
    (redex : CanonicalTerm) (out : Theorem) :
    BetaConvSemantics redex out ↔
      BindingStep (.betaConv redex) out := by
  constructor
  · rintro ⟨reduced, equality, reduction, construction, parts⟩
    exact ⟨BindingEvidence.betaConv reduced equality reduction construction parts⟩
  · rintro ⟨evidence⟩
    cases evidence with
    | betaConv reduced equality reduction construction parts =>
        exact ⟨reduced, equality, reduction, construction, parts⟩

def checkBinding : BindingRequest → Option Theorem
  | .abs sourceVar input => checkAbs sourceVar input
  | .betaConv redex => checkBetaConv redex

theorem checkBinding_eq_some_iff
    (request : BindingRequest) (out : Theorem) :
    checkBinding request = some out ↔ BindingStep request out := by
  cases request with
  | abs sourceVar input =>
      rw [checkBinding, checkAbs_eq_some_iff,
        absSemantics_iff_bindingStep]
  | betaConv redex =>
      rw [checkBinding, checkBetaConv_eq_some_iff,
        betaConvSemantics_iff_bindingStep]

theorem BindingStep.deterministic
    {request : BindingRequest} {left right : Theorem}
    (leftStep : BindingStep request left)
    (rightStep : BindingStep request right) : left = right := by
  have leftAccepted := (checkBinding_eq_some_iff request left).mpr leftStep
  have rightAccepted := (checkBinding_eq_some_iff request right).mpr rightStep
  exact Option.some.inj (leftAccepted.symm.trans rightAccepted)

/-! ## Positive and negative rule controls -/

namespace BindingRuleExamples

open BindingExamples

private theorem freeXEqualityAvailable :
    (freeX.mkEquality? freeX).isSome = true := by
  simp [CanonicalTerm.mkEquality?, freeX]

def freeXEquality : CanonicalTerm :=
  (freeX.mkEquality? freeX).get freeXEqualityAvailable

theorem freeXEqualityResult :
    freeX.mkEquality? freeX = some freeXEquality := by
  exact (Option.some_get freeXEqualityAvailable).symm

def freeXRefl : Theorem := Theorem.emptyResult ∅ freeXEquality

def freeXAbs : CanonicalTerm := freeX.abstractFree xIndividual

private theorem freeXAbsEqualityAvailable :
    (freeXAbs.mkEquality? freeXAbs).isSome = true := by
  simp [CanonicalTerm.mkEquality?, freeXAbs, CanonicalTerm.abstractFree,
    freeX]

def freeXAbsEquality : CanonicalTerm :=
  (freeXAbs.mkEquality? freeXAbs).get freeXAbsEqualityAvailable

theorem freeXAbsEqualityResult :
    freeXAbs.mkEquality? freeXAbs = some freeXAbsEquality := by
  exact (Option.some_get freeXAbsEqualityAvailable).symm

def freeXAbsRefl : Theorem :=
  Theorem.preserveAxiomsResult freeXRefl freeXRefl.sequent.hyp
    freeXAbsEquality

/-- Abstraction succeeds when the selected variable is absent from hypotheses. -/
example : checkAbs xIndividual freeXRefl = some freeXAbsRefl := by
  apply (checkAbs_eq_some_iff _ _ _).mpr
  have originalConstruction :
      CanonicalTerm.EqualityConstructionSemantics
        freeX freeX freeXEquality :=
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp freeXEqualityResult
  have view : CanonicalTerm.EqualityViewSemantics
      freeXRefl.sequent.concl freeX freeX := by
    change CanonicalTerm.EqualityViewSemantics freeXEquality freeX freeX
    exact originalConstruction
  have abstractConstruction :
      CanonicalTerm.EqualityConstructionSemantics
        freeXAbs freeXAbs freeXAbsEquality :=
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp
      freeXAbsEqualityResult
  refine ⟨?_, freeX, freeX, freeXAbs, freeXAbs, freeXAbsEquality,
    view, ?_, ?_, abstractConstruction, ?_⟩
  · intro occurrence
    rcases occurrence with ⟨term, membership, found⟩
    change term ∈ (∅ : Finset CanonicalTerm) at membership
    simp at membership
  · simp [freeXAbs]
  · simp [freeXAbs]
  · exact ⟨rfl, rfl, rfl⟩

def capturedHypothesisRefl : Theorem :=
  ⟨freeXRefl.axioms, freeXRefl.axiomsBoolean,
    ⟨{freeX}, freeXRefl.sequent.concl⟩⟩

/-- The same abstraction is rejected when the variable occurs in a hypothesis. -/
example : checkAbs xIndividual capturedHypothesisRefl = none := by
  have occurs :
      FreeInHypotheses xIndividual capturedHypothesisRefl.sequent.hyp := by
    refine ⟨freeX, ?_, DBTerm.FreeOccurrence.here⟩
    simp [capturedHypothesisRefl]
  have occursB :=
    (hasFreeInHypothesesB_eq_true_iff xIndividual
      capturedHypothesisRefl.sequent.hyp).mpr occurs
  simp [checkAbs, occursB]

private theorem betaEqualityAvailable :
    (identityAppliedToY.mkEquality? freeY).isSome = true := by
  simp [CanonicalTerm.mkEquality?, identityAppliedToY, freeY]

def betaEquality : CanonicalTerm :=
  (identityAppliedToY.mkEquality? freeY).get betaEqualityAvailable

theorem betaEqualityResult :
    identityAppliedToY.mkEquality? freeY = some betaEquality := by
  exact (Option.some_get betaEqualityAvailable).symm

def betaTheorem : Theorem := Theorem.emptyResult ∅ betaEquality

/-- Beta conversion accepts a checked root redex. -/
example : checkBetaConv identityAppliedToY = some betaTheorem := by
  apply (checkBetaConv_eq_some_iff _ _).mpr
  have reduction :
      CanonicalTerm.BetaReductionSemantics identityAppliedToY freeY := by
    exact ⟨Examples.individual, .bound 0, freeY, by
      simp [identityAppliedToY, freeY], by simp [freeY]⟩
  have construction :
      CanonicalTerm.EqualityConstructionSemantics
        identityAppliedToY freeY betaEquality :=
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp betaEqualityResult
  exact ⟨freeY, betaEquality, reduction, construction, ⟨rfl, rfl, rfl⟩⟩

/-- A checked non-redex is rejected by beta conversion. -/
example : checkBetaConv freeY = none := by
  simp [checkBetaConv, CanonicalTerm.betaReduce?, freeY]

end BindingRuleExamples

end Mettapedia.Languages.OpenTheory
