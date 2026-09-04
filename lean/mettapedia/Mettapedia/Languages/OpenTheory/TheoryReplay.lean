import Mettapedia.Languages.OpenTheory.TheoryClosure

/-!
# Exact replay interface for policy-qualified OpenTheory theories

For any decidable axiom policy, the least OpenTheory theory closure has an
exact `RuleWitness`.  The witness is the pinned primitive request itself; the
Boolean root test checks the exact ordered premise list, the policy obligation,
and the complete structural theorem result including axiom provenance.

This is the generic NIK-facing boundary.  It does not designate any policy as
HOL, and it does not add the still-missing definition or article-machine
layers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

namespace Theorem

/-- Executable structural theorem equality, including axiom provenance.
Unlike `sourceEqB`, this deliberately does not forget axiom tags. -/
def structuralSame (left right : Theorem) : Bool :=
  decide (left.axioms = right.axioms) &&
    decide (left.sequent = right.sequent)

@[simp]
theorem structuralSame_eq_true_iff (left right : Theorem) :
    left.structuralSame right = true ↔ left = right := by
  constructor
  · intro same
    simp only [structuralSame, Bool.and_eq_true, decide_eq_true_eq] at same
    exact Theorem.ext same.1 same.2
  · intro equal
    subst right
    simp [structuralSame]

/-- Executable equality of complete theorem state, including axiom
provenance.  This is intentionally stricter than source theorem equality. -/
instance instDecidableEq : DecidableEq Theorem := fun left right =>
  if same : left.structuralSame right = true then
    isTrue ((structuralSame_eq_true_iff left right).mp same)
  else
    isFalse fun equal =>
      same ((structuralSame_eq_true_iff left right).mpr equal)

end Theorem

private def finsetAll {A : Type*} (values : Finset A)
    (predicate : A → Bool) : Bool :=
  Finset.fold Bool.and true predicate values

private theorem finsetAll_eq_true_iff {A : Type*} [DecidableEq A]
    (values : Finset A) (predicate : A → Prop)
    [DecidablePred predicate] :
    finsetAll values (fun value => decide (predicate value)) = true ↔
      ∀ value ∈ values, predicate value := by
  induction values using Finset.induction_on with
  | empty => simp [finsetAll]
  | @insert value values absent ih =>
      unfold finsetAll
      rw [Finset.fold_insert absent]
      change
        (decide (predicate value) &&
            finsetAll values (fun item => decide (predicate item))) = true ↔
          ∀ item ∈ insert value values, predicate item
      rw [Bool.and_eq_true, ih]
      simp

/-- Decide whether every finite axiom-provenance tag satisfies a policy. -/
def theoremAxiomsAllowedB (policy : AxiomPolicy) [DecidablePred policy]
    (result : Theorem) : Bool :=
  finsetAll result.axioms fun sequent => decide (policy sequent)

@[simp]
theorem theoremAxiomsAllowedB_eq_true_iff
    (policy : AxiomPolicy) [DecidablePred policy] (result : Theorem) :
    theoremAxiomsAllowedB policy result = true ↔
      policy.AllowsTheorem result := by
  exact finsetAll_eq_true_iff result.axioms policy

/-- Boolean form of the exact policy obligation on a primitive request. -/
def requestInputAxiomsAllowedB (policy : AxiomPolicy) [DecidablePred policy] :
    PrimitiveRequest → Bool
  | .core (.axiom sequent) => decide (policy sequent)
  | .core (.assume _term) => true
  | .core (.refl _term) => true
  | .core (.app left right) =>
      theoremAxiomsAllowedB policy left && theoremAxiomsAllowedB policy right
  | .core (.deductAntisym left right) =>
      theoremAxiomsAllowedB policy left && theoremAxiomsAllowedB policy right
  | .core (.eqMp equality premise) =>
      theoremAxiomsAllowedB policy equality &&
        theoremAxiomsAllowedB policy premise
  | .binding (.abs _sourceVar input) => theoremAxiomsAllowedB policy input
  | .binding (.betaConv _redex) => true
  | .subst _substitution input => theoremAxiomsAllowedB policy input

@[simp]
theorem requestInputAxiomsAllowedB_eq_true_iff
    (policy : AxiomPolicy) [DecidablePred policy]
    (request : PrimitiveRequest) :
    requestInputAxiomsAllowedB policy request = true ↔
      request.InputAxiomsAllowed policy := by
  cases request with
  | core request =>
      cases request <;>
        simp [requestInputAxiomsAllowedB,
          PrimitiveRequest.InputAxiomsAllowed,
          CoreRequest.InputAxiomsAllowed]
  | binding request =>
      cases request <;>
        simp [requestInputAxiomsAllowedB,
          PrimitiveRequest.InputAxiomsAllowed,
          BindingRequest.InputAxiomsAllowed]
  | subst substitution input =>
      simp [requestInputAxiomsAllowedB,
        PrimitiveRequest.InputAxiomsAllowed]

/-- Executable structural equality for ordered theorem premise lists. -/
def theoremListStructuralSame : List Theorem → List Theorem → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      left.structuralSame right && theoremListStructuralSame lefts rights
  | _, _ => false

@[simp]
theorem theoremListStructuralSame_eq_true_iff :
    ∀ left right,
      theoremListStructuralSame left right = true ↔ left = right
  | [], [] => by simp [theoremListStructuralSame]
  | [], _right :: _rights => by simp [theoremListStructuralSame]
  | _left :: _lefts, [] => by simp [theoremListStructuralSame]
  | left :: lefts, right :: rights => by
      simp only [theoremListStructuralSame, Bool.and_eq_true,
        Theorem.structuralSame_eq_true_iff,
        theoremListStructuralSame_eq_true_iff, List.cons.injEq]

/-- Compare the executable primitive result with one exact structural theorem. -/
def checkedOutputStructuralSame (request : PrimitiveRequest)
    (out : Theorem) : Bool :=
  match checkPrimitive request with
  | none => false
  | some result => result.structuralSame out

@[simp]
theorem checkedOutputStructuralSame_eq_true_iff
    (request : PrimitiveRequest) (out : Theorem) :
    checkedOutputStructuralSame request out = true ↔
      PrimitiveStep request out := by
  cases accepted : checkPrimitive request with
  | none =>
      constructor
      · simp [checkedOutputStructuralSame, accepted]
      · intro step
        have executable := (checkPrimitive_eq_some_iff request out).mpr step
        rw [accepted] at executable
        contradiction
  | some result =>
      constructor
      · intro same
        have equal : result = out := by
          simpa [checkedOutputStructuralSame, accepted] using same
        subst out
        exact (checkPrimitive_eq_some_iff request result).mp accepted
      · intro step
        have executable := (checkPrimitive_eq_some_iff request out).mpr step
        have equal : result = out := Option.some.inj
          (accepted.symm.trans executable)
        subst out
        simp [checkedOutputStructuralSame, accepted]

/-- Boolean rule-instance test for one decidable policy-qualified theory. -/
def policyRuleIsInstance (policy : AxiomPolicy) [DecidablePred policy]
    (request : PrimitiveRequest) (premises : List Theorem)
    (out : Theorem) : Bool :=
  theoremListStructuralSame request.premises premises &&
    requestInputAxiomsAllowedB policy request &&
    checkedOutputStructuralSame request out

@[simp]
theorem policyRuleIsInstance_eq_true_iff
    (policy : AxiomPolicy) [DecidablePred policy]
    (request : PrimitiveRequest) (premises : List Theorem)
    (out : Theorem) :
    policyRuleIsInstance policy request premises out = true ↔
      request.premises = premises ∧
      request.InputAxiomsAllowed policy ∧
      PrimitiveStep request out := by
  simp [policyRuleIsInstance, Bool.and_eq_true, and_assoc]

/-- Exact finite-replay witnesses for the pinned primitive kernel under any
decidable axiom policy. -/
def policyRuleWitness (policy : AxiomPolicy) [DecidablePred policy] :
    RuleWitness (PolicyPrimitiveRule policy) where
  W := PrimitiveRequest
  isInstance := policyRuleIsInstance policy
  sound := by
    intro request premises out accepted
    have exactStep :=
      (policyRuleIsInstance_eq_true_iff policy request premises out).mp
        accepted
    exact ⟨request, exactStep.1, exactStep.2.1, exactStep.2.2⟩
  complete := by
    intro premises out rule
    obtain ⟨request, premisesExact, policyAllowed, step⟩ := rule
    exact ⟨request,
      (policyRuleIsInstance_eq_true_iff policy request premises out).mpr
        ⟨premisesExact, policyAllowed, step⟩⟩

end Mettapedia.Languages.OpenTheory
