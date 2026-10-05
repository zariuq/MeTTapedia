import Mettapedia.Languages.MM0.Presentation.CalculusProgramCorrespondence
import Mettapedia.Languages.MM0.Presentation.CalculusWitness

/-!
# The contract of the checker of the MM0 calculus

The checker runs the program of a computed leaf to completion, while the
specified checker runs it within the fuel the leaf names. The two agree on
every certificate whose leaves name enough fuel, and every certificate has
such a version that differs only in the fuel of its leaves; the data the
checker reads does not record fuel.

So the checker returns `True` for a goal and a certificate exactly when the
specified checker accepts the certificate once its leaves name enough fuel, and
`False` exactly when it accepts it at no fuel. Its leaf evaluator returns only
facts of the theory, so a certificate it accepts for a derivability judgment
is a kernel derivation. A submitted kernel witness is accepted, through its
translation, exactly when the kernel checks it.

These are statements about the engine's semantics of the program. Generated
MeTTa and its runtime are a separate boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.Languages.MM0.Kernel
open Calculus
open ComputationalContext ComputationalArguments ComputationalProof ComputationalConversion

local notation "P" => calculusProgram
local notation "H" => dataEqualityHost

/-! ## Leaves of a certificate -/

section Leaves

variable {Query Other : Type}

mutual

/-- The same certificate with every computed leaf changed. -/
def mapLeaves (change : Query → Other) : CompactProof Query → CompactProof Other
  | .replay raw => .replay raw
  | .computed query => .computed (change query)
  | .node ruleInstance children => .node ruleInstance (mapLeavesList change children)

def mapLeavesList (change : Query → Other) : List (CompactProof Query) → List (CompactProof Other)
  | [] => []
  | proof :: proofs => mapLeaves change proof :: mapLeavesList change proofs

end

mutual

/-- The computed leaves of a certificate. -/
def leaves : CompactProof Query → List Query
  | .replay _ => []
  | .computed query => [query]
  | .node _ children => leavesList children

def leavesList : List (CompactProof Query) → List Query
  | [] => []
  | proof :: proofs => leaves proof ++ leavesList proofs

end

variable (definition : ValidatedCalculusLanguageDef)

mutual

theorem check_mapLeaves (evaluate : Other → Option Pattern) (change : Query → Other) :
    ∀ (goal : Pattern) (proof : CompactProof Query),
      check definition evaluate goal (mapLeaves change proof) =
        check definition (evaluate ∘ change) goal proof
  | _, .replay _ => by simp only [mapLeaves, check]
  | _, .computed _ => by simp only [mapLeaves, check, Function.comp]
  | goal, .node ruleInstance children => by
      simp only [mapLeaves, check]
      cases instantiateRule? definition ruleInstance with
      | none => rfl
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          simp only [checkChildren_mapLeaves evaluate change premises children]

theorem checkChildren_mapLeaves (evaluate : Other → Option Pattern) (change : Query → Other) :
    ∀ (premises : List Pattern) (children : List (CompactProof Query)),
      checkChildren definition evaluate premises (mapLeavesList change children) =
        checkChildren definition (evaluate ∘ change) premises children
  | [], [] => by simp [mapLeavesList, checkChildren]
  | [], _ :: _ => by simp [mapLeavesList, checkChildren]
  | _ :: _, [] => by simp [mapLeavesList, checkChildren]
  | premise :: premises, child :: children => by
      simp only [mapLeavesList, checkChildren, check_mapLeaves evaluate change premise child,
        checkChildren_mapLeaves evaluate change premises children]

end

mutual

/-- **Only the leaves of a certificate matter to its evaluator.** -/
theorem check_congr {first second : Query → Option Pattern} :
    ∀ (goal : Pattern) (proof : CompactProof Query),
      (∀ query ∈ leaves proof, first query = second query) →
        check definition first goal proof = check definition second goal proof
  | _, .replay _, _ => by simp only [check]
  | _, .computed query, same => by simp only [check, same query (by simp [leaves])]
  | goal, .node ruleInstance children, same => by
      simp only [check]
      cases instantiateRule? definition ruleInstance with
      | none => rfl
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          simp only [checkChildren_congr premises children (by simpa [leaves] using same)]

theorem checkChildren_congr {first second : Query → Option Pattern} :
    ∀ (premises : List Pattern) (children : List (CompactProof Query)),
      (∀ query ∈ leavesList children, first query = second query) →
        checkChildren definition first premises children =
          checkChildren definition second premises children
  | [], [], _ => by simp [checkChildren]
  | [], _ :: _, _ => by simp [checkChildren]
  | _ :: _, [], _ => by simp [checkChildren]
  | premise :: premises, child :: children, same => by
      simp only [leavesList, List.mem_append] at same
      simp only [checkChildren, check_congr premise child (fun query member => same query (.inl member)),
        checkChildren_congr premises children (fun query member => same query (.inr member))]

end

mutual

/-- An evaluator returning at least the judgments of another accepts at least
its certificates. -/
theorem check_mono {first second : Query → Option Pattern}
    (stronger : ∀ query goal, first query = some goal → second query = some goal) :
    ∀ (goal : Pattern) (proof : CompactProof Query),
      check definition first goal proof = true → check definition second goal proof = true
  | _, .replay _, accepted => by simpa only [check] using accepted
  | goal, .computed query, accepted => by
      simp only [check, decide_eq_true_eq] at accepted ⊢
      exact stronger query goal accepted
  | goal, .node ruleInstance children, accepted => by
      simp only [check] at accepted ⊢
      cases application : instantiateRule? definition ruleInstance with
      | none => simp [application] at accepted
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          simp only [application, Bool.and_eq_true] at accepted ⊢
          exact ⟨accepted.1, checkChildren_mono stronger premises children accepted.2⟩

theorem checkChildren_mono {first second : Query → Option Pattern}
    (stronger : ∀ query goal, first query = some goal → second query = some goal) :
    ∀ (premises : List Pattern) (children : List (CompactProof Query)),
      checkChildren definition first premises children = true →
        checkChildren definition second premises children = true
  | [], [], _ => by simp [checkChildren]
  | [], _ :: _, accepted => by simp [checkChildren] at accepted
  | _ :: _, [], accepted => by simp [checkChildren] at accepted
  | premise :: premises, child :: children, accepted => by
      simp only [checkChildren, Bool.and_eq_true] at accepted ⊢
      exact ⟨check_mono stronger premise child accepted.1,
        checkChildren_mono stronger premises children accepted.2⟩

end

theorem exists_bound {α : Type} (property : α → Nat → Prop) :
    ∀ items : List α, (∀ item ∈ items, ∃ needed, ∀ fuel, needed ≤ fuel → property item fuel) →
      ∃ needed, ∀ fuel, needed ≤ fuel → ∀ item ∈ items, property item fuel
  | [], _ => ⟨0, fun _ _ _ member => absurd member List.not_mem_nil⟩
  | item :: items, each => by
      obtain ⟨first, firstEnough⟩ := each item List.mem_cons_self
      obtain ⟨rest, restEnough⟩ := exists_bound property items
        fun other member => each other (List.mem_cons_of_mem _ member)
      refine ⟨max first rest, fun fuel enough other member => ?_⟩
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        exact firstEnough fuel (le_trans (Nat.le_max_left _ _) enough)
      · exact restEnough fuel (le_trans (Nat.le_max_right _ _) enough) other inRest

end Leaves

/-! ## Fuel at the leaves -/

variable (T : Theory)

/-- The same leaf naming another fuel. -/
def refuel (fuel : Nat) : (family T).Leaf → (family T).Leaf
  | ⟨index, leaf⟩ => ⟨index, ⟨leaf.query, leaf.answer, fuel⟩⟩

theorem leafCode_refuel (fuel : Nat) : ∀ leaf : (family T).Leaf,
    leafCode T (refuel T fuel leaf) = leafCode T leaf
  | ⟨.lookup, ⟨_, _, _⟩⟩ | ⟨.instantiate, ⟨(_, _, _), _, _⟩⟩ | ⟨.convert, ⟨(_, _), _, _⟩⟩ => rfl

mutual

/-- **The checker does not read the fuel of a leaf.** -/
theorem certificateCode_refuel (fuel : Nat) : ∀ proof : CompactProof (family T).Leaf,
    certificateCode T (mapLeaves (refuel T fuel) proof) = certificateCode T proof
  | .replay _ => rfl
  | .computed leaf => leafCode_refuel T fuel leaf
  | .node ⟨⟨rule⟩, arguments⟩ children => by
      simp only [mapLeaves, certificateCode, certificateCodes_refuel fuel children]

theorem certificateCodes_refuel (fuel : Nat) : ∀ proofs : List (CompactProof (family T).Leaf),
    certificateCodes T (mapLeavesList (refuel T fuel) proofs) = certificateCodes T proofs
  | [] => rfl
  | proof :: proofs => by
      simp only [mapLeavesList, certificateCodes, certificateCode_refuel fuel proof,
        certificateCodes_refuel fuel proofs]

end

theorem request_refuel (fuel : Nat) (goal : Pattern) (proof : CompactProof (family T).Leaf) :
    request T goal (mapLeaves (refuel T fuel) proof) = request T goal proof := by
  simp only [request, certificateCode_refuel]

theorem settledEvaluate_refuel (fuel : Nat) (leaf : (family T).Leaf) :
    settledEvaluate T (refuel T fuel leaf) = settledEvaluate T leaf := by
  obtain ⟨index, ⟨query, answer, _⟩⟩ := leaf
  cases index <;> rfl

/-- **A leaf is settled exactly when its authored relation relates the query
and the claimed answer.** -/
theorem settled_iff : ∀ leaf : (family T).Leaf,
    settled T leaf = true ↔ ((family T).computation leaf.1).relation leaf.2.query leaf.2.answer
  | ⟨.lookup, ⟨index, declaration, _⟩⟩ => by
      simp only [settled, decide_eq_true_eq]
      show _ ↔ T.theoremSignature index = some declaration
      constructor
      · intro same
        cases found : T.theoremSignature index with
        | none => simp [found] at same
        | some stored =>
            simp only [found, Option.map_some, Option.some.injEq] at same
            exact congrArg some (ComputationalAdmission.encodeTheorem_injective same)
      · intro found
        rw [found]
        rfl
  | ⟨.instantiate, ⟨(context, declaration, arguments), result, _⟩⟩ => by
      simp only [settled, decide_eq_true_eq]
      exact TheoremDecl.instantiate_eq_some_iff _ _ _ _ _
  | ⟨.convert, ⟨(context, witness), ⟨left, right, sort⟩, _⟩⟩ => by
      simp only [settled, decide_eq_true_eq]
      exact ConvWitness.conversion_eq_some_iff _ _ _ _ _ _ _

theorem settledEvaluate_of_evaluate {leaf : (family T).Leaf} {goal : Pattern}
    (returned : (family T).evaluate leaf = some goal) : settledEvaluate T leaf = some goal := by
  obtain ⟨index, leaf⟩ := leaf
  obtain ⟨related, rfl⟩ := AuthoredFamily.evaluate_eq_some (F := family T) returned
  have verdict : settled T ⟨index, leaf⟩ = true := (settled_iff T ⟨index, leaf⟩).mpr related
  simp [settledEvaluate, verdict]

/-- Every leaf, once it names enough fuel, is evaluated as it is settled. -/
theorem evaluate_eventually (leaf : (family T).Leaf) :
    ∃ needed, ∀ fuel, needed ≤ fuel →
      (family T).evaluate (refuel T fuel leaf) = settledEvaluate T leaf := by
  obtain ⟨index, leaf⟩ := leaf
  cases verdict : settled T ⟨index, leaf⟩
  · refine ⟨0, fun fuel _ => ?_⟩
    have unrelated : ¬ ((family T).computation index).relation leaf.query leaf.answer := by
      intro related
      have := (settled_iff T ⟨index, leaf⟩).mpr related
      simp [verdict] at this
    rw [show settledEvaluate T ⟨index, leaf⟩ = none by simp [settledEvaluate, verdict]]
    exact AuthoredFamily.evaluate_eq_none (F := family T) (leaf := ⟨leaf.query, leaf.answer, fuel⟩)
      unrelated
  · have related := (settled_iff T ⟨index, leaf⟩).mp verdict
    obtain ⟨needed, runs⟩ := ((family T).computation index).runs_of_relation related
    refine ⟨needed, fun fuel enough => ?_⟩
    rw [show settledEvaluate T ⟨index, leaf⟩ = some ((family T).judgment index leaf.query leaf.answer) by
      simp [settledEvaluate, verdict]]
    exact AuthoredFamily.evaluate_of_runs (F := family T) (runs fuel enough)

/-- **Every certificate settles once its leaves name enough fuel.** -/
theorem enough_fuel (goal : Pattern) (proof : CompactProof (family T).Leaf) :
    ∃ needed, ∀ fuel, needed ≤ fuel →
      check formMM0 (family T).evaluate goal (mapLeaves (refuel T fuel) proof) =
        check formMM0 (settledEvaluate T) goal proof := by
  obtain ⟨needed, enough⟩ := exists_bound
    (fun leaf fuel => (family T).evaluate (refuel T fuel leaf) = settledEvaluate T leaf)
    (leaves proof) (fun leaf _ => evaluate_eventually T leaf)
  refine ⟨needed, fun fuel atLeast => ?_⟩
  rw [check_mapLeaves]
  exact check_congr formMM0 goal proof fun leaf member => enough fuel atLeast leaf member

theorem settled_of_accepted {goal : Pattern} {proof : CompactProof (family T).Leaf} {fuel : Nat}
    (accepted : check formMM0 (family T).evaluate goal (mapLeaves (refuel T fuel) proof) = true) :
    check formMM0 (settledEvaluate T) goal proof = true := by
  have settledRefueled := check_mono formMM0 (fun _ _ => settledEvaluate_of_evaluate T) goal _ accepted
  rw [check_mapLeaves] at settledRefueled
  rwa [show settledEvaluate T ∘ refuel T fuel = settledEvaluate T from
    funext (settledEvaluate_refuel T fuel)] at settledRefueled

/-! ## The contract -/

/-- **The verdict of the checker** on every goal and certificate: exactly one
result, the shared checker's verdict with settled leaves. -/
theorem certificate_returns_iff (goal : Pattern) (proof : CompactProof (family T).Leaf)
    (result : Term) :
    Applies P H "mm0:certificate" (request T goal proof) result ↔
      result = boolean (check formMM0 (settledEvaluate T) goal proof) :=
  ⟨fun returned => returned.deterministic (certificate_computes T goal proof),
    fun same => same ▸ certificate_computes T goal proof⟩

/-- **With enough fuel at every leaf, the checker returns the verdict of the
specified checker.** -/
theorem certificate_exact {goal : Pattern} {proof : CompactProof (family T).Leaf}
    (enough : ∀ leaf ∈ leaves proof, (family T).evaluate leaf = settledEvaluate T leaf) :
    Applies P H "mm0:certificate" (request T goal proof)
      (boolean (check formMM0 (family T).evaluate goal proof)) := by
  rw [check_congr formMM0 goal proof enough]
  exact certificate_computes T goal proof

/-- **The checker returns `True` exactly when the specified checker accepts
the certificate with enough fuel at its leaves.** -/
theorem certificate_accepts_iff (goal : Pattern) (proof : CompactProof (family T).Leaf) :
    Applies P H "mm0:certificate" (request T goal proof) (.sym "True") ↔
      ∃ fuel, check formMM0 (family T).evaluate goal (mapLeaves (refuel T fuel) proof) = true := by
  rw [certificate_returns_iff]
  obtain ⟨needed, enough⟩ := enough_fuel T goal proof
  constructor
  · intro same
    refine ⟨needed, ?_⟩
    rw [enough needed le_rfl]
    cases verdict : check formMM0 (settledEvaluate T) goal proof
    · simp [verdict, boolean] at same
    · rfl
  · rintro ⟨fuel, accepted⟩
    simp [settled_of_accepted T accepted, boolean]

/-- **The checker returns `False` exactly when the specified checker refuses
the certificate at every fuel of its leaves.** -/
theorem certificate_refuses_iff (goal : Pattern) (proof : CompactProof (family T).Leaf) :
    Applies P H "mm0:certificate" (request T goal proof) (.sym "False") ↔
      ∀ fuel, check formMM0 (family T).evaluate goal (mapLeaves (refuel T fuel) proof) = false := by
  rw [certificate_returns_iff]
  constructor
  · intro same fuel
    cases accepted : check formMM0 (family T).evaluate goal (mapLeaves (refuel T fuel) proof)
    · rfl
    · simp [settled_of_accepted T accepted, boolean] at same
  · intro refused
    obtain ⟨needed, enough⟩ := enough_fuel T goal proof
    rw [← enough needed le_rfl, refused needed]
    rfl

/-- **A certificate accepted by the specified checker is accepted by the
checker.** -/
theorem certificate_accepts_of_check {goal : Pattern} {proof : CompactProof (family T).Leaf}
    (accepted : check formMM0 (family T).evaluate goal proof = true) :
    Applies P H "mm0:certificate" (request T goal proof) (.sym "True") := by
  rw [certificate_returns_iff,
    check_mono formMM0 (fun _ _ => settledEvaluate_of_evaluate T) goal proof accepted]
  rfl

/-- The checker runs to completion on every goal and certificate. -/
theorem certificate_eventually_stable (goal : Pattern) (proof : CompactProof (family T).Leaf) :
    ∃ needed, ∀ fuel, needed ≤ fuel →
      apply P H fuel "mm0:certificate" (request T goal proof) =
        .value (boolean (check formMM0 (settledEvaluate T) goal proof)) :=
  (certificate_computes T goal proof).at_least

/-! ## Soundness -/

/-- **The leaf evaluator of the checker returns only facts of the theory.** -/
theorem settled_returnsFacts : (mm0 T).ReturnsFacts (settledEvaluate T) := by
  intro leaf goal returned
  obtain ⟨index, leaf⟩ := leaf
  unfold settledEvaluate at returned
  split at returned
  · next verdict =>
      cases returned
      exact ⟨index, leaf.query, leaf.answer, (settled_iff T ⟨index, leaf⟩).mp verdict, rfl⟩
  · cases returned

theorem settled_coversFacts : (mm0 T).CoversFacts (settledEvaluate T) := by
  intro goal holds
  obtain ⟨index, query, answer, related, rfl⟩ := holds
  refine ⟨⟨index, ⟨query, answer, 0⟩⟩, ?_⟩
  have verdict := (settled_iff T ⟨index, ⟨query, answer, 0⟩⟩).mpr related
  unfold settledEvaluate
  rw [if_pos verdict]
  rfl

theorem settled_of_returned {goal : Pattern} {proof : CompactProof (family T).Leaf}
    (returned : Applies P H "mm0:certificate" (request T goal proof) (.sym "True")) :
    check formMM0 (settledEvaluate T) goal proof = true := by
  rw [certificate_returns_iff] at returned
  cases verdict : check formMM0 (settledEvaluate T) goal proof
  · simp [verdict, boolean] at returned
  · rfl

/-- **A goal the checker accepts is derivable from the rules and the facts of
the theory.** -/
theorem accepts_of_returned {goal : Pattern} {proof : CompactProof (family T).Leaf}
    (returned : Applies P H "mm0:certificate" (request T goal proof) (.sym "True")) :
    (mm0 T).Accepts goal :=
  ((mm0 T).accepts_iff goal).mpr
    (AuthoredCalculus.implementation_sound (settled_returnsFacts T) (settled_of_returned T returned))

/-- **Soundness for the kernel**: a derivability judgment the checker accepts
is derived by the MM0 kernel. -/
theorem derives_of_returned {context : Context} {hypotheses : List Preterm} {expression : Preterm}
    {proof : CompactProof (family T).Leaf}
    (returned : Applies P H "mm0:certificate"
      (request T (derivesJ context hypotheses expression) proof) (.sym "True")) :
    Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses expression :=
  implementation_derives (settled_returnsFacts T) (settled_of_returned T returned)

/-- **Completeness for the kernel**: every kernel derivation has a certificate
the checker accepts. -/
theorem returned_of_derives {context : Context} {hypotheses : List Preterm} {expression : Preterm}
    (derived : Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
      expression) :
    ∃ proof, Applies P H "mm0:certificate"
      (request T (derivesJ context hypotheses expression) proof) (.sym "True") := by
  obtain ⟨proof, accepted⟩ := (accepts_iff_derives context hypotheses expression).mpr derived
  exact ⟨proof, certificate_accepts_of_check T accepted⟩

/-! ## Submitted witnesses -/

theorem hypothesisChain_refuel (fuel : Nat) : ∀ (index : Nat) (hypotheses : List Preterm),
    mapLeaves (refuel T fuel) (Witness.hypothesisChain T index hypotheses) =
      Witness.hypothesisChain T index hypotheses
  | _, [] => by simp only [Witness.hypothesisChain, Witness.ruleNode, mapLeaves, mapLeavesList]
  | 0, _ :: _ => by simp only [Witness.hypothesisChain, Witness.ruleNode, mapLeaves, mapLeavesList]
  | index + 1, _ :: rest => by
      simp only [Witness.hypothesisChain, Witness.ruleNode, mapLeaves, mapLeavesList,
        hypothesisChain_refuel fuel index rest]

mutual

theorem translate_refuel (fuel other : Nat) (context : Context) (hypotheses : List Preterm) :
    ∀ witness : ProofWitness,
      mapLeaves (refuel T fuel) (Witness.translate T other context hypotheses witness) =
        Witness.translate T fuel context hypotheses witness
  | .hyp index => by
      simp only [Witness.translate, Witness.ruleNode, mapLeaves, mapLeavesList, hypothesisChain_refuel]
  | .theoremApp index arguments children => by
      simp only [Witness.translate, Witness.ruleNode, mapLeaves, mapLeavesList, refuel,
        translateAll_refuel fuel other context hypotheses children]
  | .conversion witness child => by
      simp only [Witness.translate, Witness.ruleNode, mapLeaves, mapLeavesList, refuel,
        translate_refuel fuel other context hypotheses child]

theorem translateAll_refuel (fuel other : Nat) (context : Context) (hypotheses : List Preterm) :
    ∀ (children : List ProofWitness) (expressions : List Preterm),
      mapLeaves (refuel T fuel) (Witness.translateAll T other context hypotheses children expressions) =
        Witness.translateAll T fuel context hypotheses children expressions
  | [], _ => by simp only [Witness.translateAll, Witness.ruleNode, mapLeaves, mapLeavesList]
  | child :: children, expressions => by
      simp only [Witness.translateAll, Witness.ruleNode, mapLeaves, mapLeavesList,
        translate_refuel fuel other context hypotheses child,
        translateAll_refuel fuel other context hypotheses children]

end

/-- **A submitted MM0 witness is accepted by the checker, through its
translation at any fuel, exactly when the kernel checks it.** -/
theorem witness_accepted_iff (fuel : Nat) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (expression : Preterm) :
    ProofWitness.Checks T.termSignature T.definitionSignature T.theoremSignature
        context hypotheses witness expression ↔
      Applies P H "mm0:certificate"
        (request T (derivesJ context hypotheses expression)
          (Witness.translate T fuel context hypotheses witness)) (.sym "True") := by
  rw [certificate_accepts_iff, Witness.checks_iff_accepted]
  simp only [translate_refuel]

/-- **The checker refuses the translation of a witness exactly when the kernel
does not check it.** -/
theorem witness_refused_iff (fuel : Nat) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (expression : Preterm) :
    ¬ ProofWitness.Checks T.termSignature T.definitionSignature T.theoremSignature
        context hypotheses witness expression ↔
      Applies P H "mm0:certificate"
        (request T (derivesJ context hypotheses expression)
          (Witness.translate T fuel context hypotheses witness)) (.sym "False") := by
  rw [witness_accepted_iff T fuel, certificate_returns_iff, certificate_returns_iff]
  cases check formMM0 (settledEvaluate T) (derivesJ context hypotheses expression)
    (Witness.translate T fuel context hypotheses witness) <;> simp [boolean]

end Mettapedia.Languages.MM0.Presentation.ComputationalCalculus
