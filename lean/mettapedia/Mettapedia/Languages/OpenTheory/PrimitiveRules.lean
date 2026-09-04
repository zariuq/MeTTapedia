import Mettapedia.Languages.OpenTheory.TheoremSubstitutionRule

/-!
# Complete OpenTheory primitive theorem-rule surface

This module assembles the nine primitive theorem rules at OpenTheory revision
`f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1` without conflating them with
constant/type definitions or with the optional standard theorem axioms.

The three independently developed rule families remain visible in the sum:

* six nonbinding core rules;
* abstraction and beta conversion;
* type-correct simultaneous theorem substitution.

The combined checker accepts exactly the corresponding proof-relevant
one-step evidence and is deterministic.
-/

namespace Mettapedia.Languages.OpenTheory

/-- The exact nine primitive theorem-rule names of the pinned source. -/
inductive PrimitiveRuleKind where
  | axiom
  | abs
  | app
  | assume
  | betaConv
  | deductAntisym
  | eqMp
  | refl
  | subst
deriving DecidableEq, Repr

/-- A request for any pinned primitive theorem rule. -/
inductive PrimitiveRequest where
  | core (request : CoreRequest)
  | binding (request : BindingRequest)
  | subst (substitution : TypeCorrectTermSubstitution) (input : Theorem)

namespace PrimitiveRequest

/-- The source rule name selected by a concrete request. -/
def kind : PrimitiveRequest → PrimitiveRuleKind
  | .core (.axiom _) => .axiom
  | .core (.assume _) => .assume
  | .core (.refl _) => .refl
  | .core (.app _ _) => .app
  | .core (.deductAntisym _ _) => .deductAntisym
  | .core (.eqMp _ _) => .eqMp
  | .binding (.abs _ _) => .abs
  | .binding (.betaConv _) => .betaConv
  | .subst _ _ => .subst

end PrimitiveRequest

/-- Proof-relevant evidence for any pinned primitive theorem step. -/
inductive PrimitiveEvidence : PrimitiveRequest → Theorem → Type where
  | core (evidence : CoreEvidence request out) :
      PrimitiveEvidence (.core request) out
  | binding (evidence : BindingEvidence request out) :
      PrimitiveEvidence (.binding request) out
  | subst
      (evidence : TheoremSubstitutionSemantics substitution input out) :
      PrimitiveEvidence (.subst substitution input) out

/-- Declarative one-step derivability for the complete pinned kernel. -/
def PrimitiveStep (request : PrimitiveRequest) (out : Theorem) : Prop :=
  Nonempty (PrimitiveEvidence request out)

/-- Execute any pinned primitive theorem rule. -/
def checkPrimitive : PrimitiveRequest → Option Theorem
  | .core request => checkCore request
  | .binding request => checkBinding request
  | .subst substitution input =>
      checkTheoremSubstitution substitution input

/-- Combined checking is exactly proof-relevant primitive derivability. -/
theorem checkPrimitive_eq_some_iff
    (request : PrimitiveRequest) (out : Theorem) :
    checkPrimitive request = some out ↔ PrimitiveStep request out := by
  cases request with
  | core request =>
      rw [checkPrimitive, checkCore_eq_some_iff]
      constructor
      · rintro ⟨evidence⟩
        exact ⟨PrimitiveEvidence.core evidence⟩
      · rintro ⟨evidence⟩
        cases evidence with
        | core coreEvidence => exact ⟨coreEvidence⟩
  | binding request =>
      rw [checkPrimitive, checkBinding_eq_some_iff]
      constructor
      · rintro ⟨evidence⟩
        exact ⟨PrimitiveEvidence.binding evidence⟩
      · rintro ⟨evidence⟩
        cases evidence with
        | binding bindingEvidence => exact ⟨bindingEvidence⟩
  | subst substitution input =>
      rw [checkPrimitive, checkTheoremSubstitution_eq_some_iff]
      constructor
      · intro evidence
        exact ⟨PrimitiveEvidence.subst evidence⟩
      · rintro ⟨primitiveEvidence⟩
        cases primitiveEvidence with
        | subst substitutionEvidence => exact substitutionEvidence

/-- Combined rejection is exactly absence of a primitive evidence witness. -/
theorem checkPrimitive_eq_none_iff (request : PrimitiveRequest) :
    checkPrimitive request = none ↔ ¬ ∃ out, PrimitiveStep request out := by
  constructor
  · intro rejected ⟨out, step⟩
    have accepted := (checkPrimitive_eq_some_iff request out).mpr step
    rw [rejected] at accepted
    contradiction
  · intro impossible
    cases accepted : checkPrimitive request with
    | none => rfl
    | some out =>
        exfalso
        exact impossible ⟨out,
          (checkPrimitive_eq_some_iff request out).mp accepted⟩

/-- The complete pinned primitive relation is deterministic. -/
theorem PrimitiveStep.deterministic
    {request : PrimitiveRequest} {left right : Theorem}
    (leftStep : PrimitiveStep request left)
    (rightStep : PrimitiveStep request right) : left = right := by
  have leftAccepted := (checkPrimitive_eq_some_iff request left).mpr leftStep
  have rightAccepted := (checkPrimitive_eq_some_iff request right).mpr rightStep
  exact Option.some.inj (leftAccepted.symm.trans rightAccepted)

/-! ## Coverage canaries -/

/-- Every one of the nine source rule names is represented explicitly. -/
def primitiveRuleKinds : List PrimitiveRuleKind :=
  [.axiom, .abs, .app, .assume, .betaConv, .deductAntisym, .eqMp, .refl,
    .subst]

theorem mem_primitiveRuleKinds (kind : PrimitiveRuleKind) :
    kind ∈ primitiveRuleKinds := by
  cases kind <;> simp [primitiveRuleKinds]

theorem primitiveRuleKinds_nodup : primitiveRuleKinds.Nodup := by
  decide

theorem primitiveRuleKinds_length : primitiveRuleKinds.length = 9 := by
  rfl

/-- A malformed beta request remains rejected by the combined checker. -/
example :
    checkPrimitive (.binding (.betaConv BindingExamples.freeY)) = none := by
  simp [checkPrimitive, checkBinding, checkBetaConv,
    CanonicalTerm.betaReduce?, BindingExamples.freeY]

/-- A nontrivial theorem substitution genuinely inhabits the combined rule. -/
example :
    checkPrimitive
        (.subst TheoremSubstitutionExamples.renameXToY
          TheoremSubstitutionExamples.inputTheorem) =
      some TheoremSubstitutionExamples.expectedTheorem := by
  exact TheoremSubstitutionExamples.renameXToY_accepts

end Mettapedia.Languages.OpenTheory
