import Mettapedia.GSLT.ProofPlans.Plan
import Mettapedia.GSLT.ProofPlans.Contexts
import Mettapedia.GSLT.ProofPlans.Fixture
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClone
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenDischarge

/-!
# Proof plans of a validated proof definition

For a validated proof definition, a proof plan is an `OpenDerivation`: its
ordered context lists the obligations.  These are the operations of the
definition's derivation clone (`derivationClone`), so the general theory of
`ProofPlans.Plan` applies without a second carrier.

**Completions are discharges.**  A closed derivation completes a plan exactly
when `OpenDerivation.discharge` produces it from checked evidence for the
obligations (`mem_completions_iff_discharge`).  Partial discharge by
`OpenDerivation.bind` refines the completion space (`refines_bind`); its
staged form is `OpenDerivation.discharge_bind`.  With an exact authority for
the obligations, a plan has a completion exactly when every obligation's
claim holds (`completions_nonempty_iff_meaning`), which is the discharge gate
`ExactJudgmentEncoding.discharge_of_all` read on completion spaces.

**Plan soundness.**  Three readings, from untrusted artifacts to semantics:

* *wire level*: if the open checker accepts a raw plan and the kernel checker
  accepts raw proofs of its obligations, then the raw completion is a raw proof
  of the goal accepted by the kernel checker (`wire_plan_soundness`);
* *semantic level*: every meaning preserved by the rules holds of the goal
  whenever it holds of the obligations (`truthOfMeaning`, `plan_sound`);
* *elaboration*: a plan over a method library, whose methods are implemented
  by kernel derivation templates (an `Interpretation`), elaborates to a kernel
  plan with the same obligations; elaborating a completion is completing the
  elaborated plan with elaborated evidence (`mapDerivation_discharge`).  This
  is the plan-soundness theorem of typed proof plans in these terms: a method
  schema's soundness theorem is its typed kernel template, certificates for
  side conditions are the checked rule applications, and kernel proofs of the
  obligations close the plan.

**Controls** (in the fixture kernel).
* A plan whose obligation is false has no completion although its goal is
  derivable (`planXC_no_completion`, `goalC_derivable`): a plan is not
  evidence for its goal.
* Discharging an obligation can shrink the completion space strictly
  (`dischargeFirst_strict`).
* Refinement is coarser than being an instance: two dead plans refine each
  other and neither is an instance of the other (`refines_not_instanceOf`).
* The library macro `A ⊢ C` elaborates to the kernel plan `bc(ab(?A))`
  (`elaborate_libraryPlan`), and the library's completion elaborates to the
  kernel completion (`elaborate_library_completion`); a library with an
  unsound schema admits no elaboration at all (`Fixture.badLibrary_no_elaboration`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.OSLF.Programs

/-- Proof plans of a validated proof definition: plans of its derivation
clone. -/
abbrev DerivationPlan (object : Object) (goal : Pattern) : Type :=
  Plan (derivationClone object) goal

/-- An open derivation read as a proof plan: its context lists the
obligations. -/
def ofOpen {object : Object} {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation object.definition context goal) :
    DerivationPlan object goal :=
  ⟨context, derivation⟩

variable {object : Object}

/-- The open derivation of a plan, as an `OpenDerivation`. -/
abbrev DerivationPlan.derivation {goal : Pattern} (plan : DerivationPlan object goal) :
    OpenDerivation object.definition plan.obligations goal :=
  plan.body

/-! ## Completions are discharges -/

/-- Clone substitution is `OpenDerivation.bind`. -/
theorem substitute_eq_bind {source target : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation object.definition source goal)
    (environment : OpenDerivationList object.definition target source) :
    (derivationClone object).substitute derivation (fun index => environment.get index) =
      OpenDerivation.bind derivation environment := by
  show OpenDerivation.bind derivation
      (OpenDerivationList.ofFn _ fun index => environment.get index) = _
  rw [OpenDerivationList.ofFn_get]

/-- **Completions are discharges.**  A closed derivation completes a plan
exactly when discharging the plan's obligations with checked evidence
produces it. -/
theorem mem_completions_iff_discharge {goal : Pattern}
    (plan : DerivationPlan object goal) (derivation : Derivation object.definition goal) :
    OpenDerivation.ofClosed derivation ∈ completions (derivationClone object) plan ↔
      ∃ evidence : DerivationList object.definition plan.obligations,
        plan.derivation.discharge evidence = derivation := by
  constructor
  · intro member
    obtain ⟨environment, equation⟩ := mem_completions_iff.mp member
    have bound : OpenDerivation.bind plan.body
        (OpenDerivationList.ofFn plan.obligations environment) =
          OpenDerivation.ofClosed derivation := equation
    refine ⟨(OpenDerivationList.ofFn plan.obligations environment).close, ?_⟩
    unfold OpenDerivation.discharge
    rw [OpenDerivationList.ofClosed_close, bound, OpenDerivation.close_ofClosed]
  · rintro ⟨evidence, equation⟩
    refine mem_completions_iff.mpr
      ⟨fun index => (OpenDerivationList.ofClosed evidence).get index, ?_⟩
    show OpenDerivation.bind plan.body (OpenDerivationList.ofFn plan.obligations
      fun index => (OpenDerivationList.ofClosed evidence).get index) =
        OpenDerivation.ofClosed derivation
    rw [OpenDerivationList.ofFn_get, ← equation]
    unfold OpenDerivation.discharge
    rw [OpenDerivation.ofClosed_close]

/-- **Completions are substitution instances with closed evidence**, stated
with ordered evidence vectors. -/
theorem mem_completions_iff_bind {goal : Pattern} (plan : DerivationPlan object goal)
    (completion : OpenDerivation object.definition [] goal) :
    completion ∈ completions (derivationClone object) plan ↔
      ∃ evidence : OpenDerivationList object.definition [] plan.obligations,
        plan.derivation.bind evidence = completion := by
  constructor
  · intro member
    obtain ⟨environment, equation⟩ := mem_completions_iff.mp member
    exact ⟨OpenDerivationList.ofFn _ environment, equation⟩
  · rintro ⟨evidence, equation⟩
    exact mem_completions_iff.mpr ⟨fun index => evidence.get index,
      (substitute_eq_bind _ _).trans equation⟩

/-- Every discharge of a plan is one of its completions. -/
theorem discharge_mem_completions {goal : Pattern} (plan : DerivationPlan object goal)
    (evidence : DerivationList object.definition plan.obligations) :
    OpenDerivation.ofClosed (plan.derivation.discharge evidence) ∈
      completions (derivationClone object) plan :=
  (mem_completions_iff_discharge plan _).mpr ⟨evidence, rfl⟩

/-- Reading closed derivations as open ones is injective. -/
theorem ofClosed_injective {goal : Pattern} {left right : Derivation object.definition goal}
    (equal : OpenDerivation.ofClosed (context := []) left = OpenDerivation.ofClosed right) :
    left = right := by
  have closed := congrArg OpenDerivation.close equal
  rwa [OpenDerivation.close_ofClosed, OpenDerivation.close_ofClosed] at closed

/-- Every completion is a closed derivation. -/
theorem completion_eq_ofClosed {goal : Pattern}
    (completion : OpenDerivation object.definition [] goal) :
    completion = OpenDerivation.ofClosed completion.close :=
  (OpenDerivation.ofClosed_close completion).symm

/-- **Partial discharge refines the completion space.** -/
theorem refines_bind {context : List Pattern} {goal : Pattern}
    (plan : DerivationPlan object goal)
    (environment : OpenDerivationList object.definition context plan.obligations) :
    Completion.Refines (Completes (derivationClone object))
      (ofOpen (plan.derivation.bind environment)) plan := by
  have refined : ofOpen (plan.derivation.bind environment) =
      plan.refine (fun index => environment.get index) := by
    show (⟨context, OpenDerivation.bind plan.body environment⟩ :
        DerivationPlan object goal) =
      ⟨context, OpenDerivation.bind plan.body
        (OpenDerivationList.ofFn _ fun index => environment.get index)⟩
    rw [OpenDerivationList.ofFn_get]
  rw [refined]
  exact refine_refines plan _

/-- Discharge the first obligation of a plan with a closed derivation. -/
def dischargeFirst {head : Pattern} {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition (head :: context) goal)
    (derivation : Derivation object.definition head) :
    OpenDerivation object.definition context goal :=
  plan.bind (.cons (OpenDerivation.ofClosed derivation)
    (assumptionEnvironment object.definition context))

/-- Discharging the first obligation refines the completion space. -/
theorem dischargeFirst_refines {head : Pattern} {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition (head :: context) goal)
    (derivation : Derivation object.definition head) :
    Completion.Refines (Completes (derivationClone object))
      (ofOpen (dischargeFirst plan derivation)) (ofOpen plan) :=
  refines_bind (ofOpen plan) _

/-- A plan has a completion exactly when its obligations have checked
evidence. -/
theorem completions_nonempty_iff_evidence {goal : Pattern} (plan : DerivationPlan object goal) :
    (completions (derivationClone object) plan).Nonempty ↔
      Nonempty (DerivationList object.definition plan.obligations) := by
  rw [completions_nonempty_iff]
  constructor
  · rintro ⟨environment⟩
    exact ⟨(OpenDerivationList.ofFn plan.obligations environment).close⟩
  · rintro ⟨evidence⟩
    exact ⟨fun index => (OpenDerivationList.ofClosed evidence).get index⟩

/-- **With an exact authority for its obligations, a plan has a completion
exactly when every obligation's claim holds**: the discharge gate of
`ExactJudgmentEncoding.discharge_of_all`, as a statement about completion
spaces. -/
theorem completions_nonempty_iff_meaning {Claim : Type} {Meaning : Claim → Prop}
    (adequacy : ExactJudgmentEncoding Claim Meaning object.definition) (claims : List Claim)
    {goal : Pattern}
    (plan : OpenDerivation object.definition
      (claims.map adequacy.toJudgmentEncodingAdequacy.encode) goal) :
    (completions (derivationClone object) (ofOpen plan)).Nonempty ↔
      ∀ claim ∈ claims, Meaning claim :=
  (completions_nonempty_iff_evidence (ofOpen plan)).trans
    (adequacy.context_correspondence claims)

/-! ## Plan soundness -/

/-- **Plan soundness for untrusted artifacts.**  If the open checker accepts a
raw plan for `goal` over the obligations `context`, and the kernel checker
accepts a raw proof of every obligation, then substituting those proofs into
the plan gives a raw proof of `goal` accepted by the kernel checker. -/
theorem wire_plan_soundness {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern} {plan : RawOpenProof}
    (planAccepted : checkOpenRaw definition context goal plan = true)
    {evidence : List RawProof}
    (evidenceAccepted : checkRawChildren definition context evidence = true) :
    ∃ proof : RawProof, checkRaw definition goal proof = true ∧
      rawToOpen proof = RawOpenProof.substitute (rawToOpenList evidence) plan := by
  obtain ⟨typedPlan, planErased⟩ := checkOpenRaw_exact_derivation planAccepted
  obtain ⟨typedEvidence, evidenceErased⟩ :=
    checkRawChildren_exists_derivations_with_exact_erasure evidenceAccepted
  refine ⟨(typedPlan.discharge typedEvidence).erase,
    checkRaw_erase (typedPlan.discharge typedEvidence), ?_⟩
  rw [← eraseOpen_ofClosed]
  unfold OpenDerivation.discharge
  rw [OpenDerivation.ofClosed_close, OpenDerivation.eraseOpen_bind, eraseOpenList_ofClosed,
    evidenceErased, planErased]

/-- A meaning preserved by every rule application is a truth assignment of the
derivation clone. -/
def truthOfMeaning (object : Object) (meaning : Pattern → Prop)
    (ruleSound : ∀ ruleInstance premises conclusion,
      RuleApplication object.definition ruleInstance premises conclusion →
        (∀ premise ∈ premises, meaning premise) → meaning conclusion) :
    Truth (derivationClone object) where
  holds := meaning
  sound := fun derivation contextHolds =>
    OpenDerivation.sound_of_ruleApplications meaning ruleSound
      (fun premise member => by
        obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
        exact contextHolds index)
      derivation

/-! ## Elaboration through a method library -/

/-- **Elaborate a plan**: every method instance is replaced by its kernel
template; the obligations are kept. -/
def elaborate {source target : Object} (interpretation : Interpretation source target)
    {goal : Pattern} (plan : DerivationPlan source goal) : DerivationPlan target goal :=
  ⟨plan.obligations, interpretation.mapOpen plan.derivation⟩

/-- Evidence elaborated through an interpretation. -/
def mapEvidence {source target : Object} (interpretation : Interpretation source target)
    {goals : List Pattern} (evidence : DerivationList source.definition goals) :
    DerivationList target.definition goals :=
  (interpretation.mapOpenList (OpenDerivationList.ofClosed (context := []) evidence)).close

/-- **Plan soundness through elaboration.**  Elaborating a completion equals
completing the elaborated plan with the elaborated evidence. -/
theorem mapDerivation_discharge {source target : Object}
    (interpretation : Interpretation source target) {context : List Pattern}
    {goal : Pattern} (plan : OpenDerivation source.definition context goal)
    (evidence : DerivationList source.definition context) :
    interpretation.mapDerivation (plan.discharge evidence) =
      (interpretation.mapOpen plan).discharge (mapEvidence interpretation evidence) := by
  unfold Interpretation.mapDerivation OpenDerivation.discharge mapEvidence
  rw [OpenDerivation.ofClosed_close, Interpretation.mapOpen_bind,
    OpenDerivationList.ofClosed_close]

/-- Elaboration maps completions of a plan to completions of the elaborated
plan. -/
theorem elaborate_completion {source target : Object}
    (interpretation : Interpretation source target) {goal : Pattern}
    (plan : DerivationPlan source goal) (derivation : Derivation source.definition goal)
    (member : OpenDerivation.ofClosed derivation ∈ completions (derivationClone source) plan) :
    OpenDerivation.ofClosed (interpretation.mapDerivation derivation) ∈
      completions (derivationClone target) (elaborate interpretation plan) := by
  obtain ⟨evidence, rfl⟩ := (mem_completions_iff_discharge plan derivation).mp member
  exact (mem_completions_iff_discharge (elaborate interpretation plan) _).mpr
    ⟨mapEvidence interpretation evidence,
      (mapDerivation_discharge interpretation plan.derivation evidence).symm⟩

/-! ## Controls -/

namespace PlanControls

open Fixture

/-- The kernel truth assignment as a truth assignment of plans. -/
def kernelPlanTruth : Truth (derivationClone kernel) :=
  truthOfMeaning kernel kernelTruth kernelRules_preserve_truth

/-- **Positive.**  Discharging `bc(ab(?A))` with `axA₁` gives the kernel
derivation `bc(ab(axA₁))`. -/
theorem planC_discharge : planC.discharge (.cons dA₁ .nil) = dC := rfl

theorem dC_mem_completions :
    OpenDerivation.ofClosed dC ∈ completions (derivationClone kernel) (ofOpen planC) :=
  (mem_completions_iff_discharge (ofOpen planC) dC).mpr ⟨.cons dA₁ .nil, planC_discharge⟩

/-- The goal `C` is derivable. -/
theorem goalC_derivable : Nonempty (Derivation kernelDefinition C) := ⟨dC⟩

/-- **Negative.**  The plan `xc(?X)` for the derivable goal `C` has no
completion, because its obligation is false. -/
theorem planXC_no_completion :
    ∀ completion, completion ∉ completions (derivationClone kernel) (ofOpen planXC) :=
  kernelPlanTruth.completions_empty (ofOpen planXC) ⟨0, Nat.one_pos⟩ fun holds => holds.1 rfl

/-- The two axioms for `A` give different derivations. -/
theorem dA₁_ne_dA₂ : dA₁ ≠ dA₂ := by
  intro equal
  injection equal with sameInstance
  simp [ruleInstance, ruleAxA₁, ruleAxA₂, groundRule] at sameInstance

theorem dBA₁_ne_dBA₂ : dBA₁ ≠ dBA₂ := by
  intro equal
  injection equal with _ _ _ children
  injection children with _ _ heads _
  exact dA₁_ne_dA₂ heads

/-- Discharging `ab(?A)` with `axA₁` gives the closed plan `ab(axA₁)`. -/
theorem dischargeFirst_planAB : dischargeFirst planAB dA₁ = OpenDerivation.ofClosed dBA₁ :=
  rfl

/-- **Refinement can be strict.**  `ab(axA₂)` completes `ab(?A)` but not its
refinement by `axA₁`. -/
theorem dischargeFirst_strict :
    OpenDerivation.ofClosed dBA₂ ∈ completions (derivationClone kernel) (ofOpen planAB) ∧
      OpenDerivation.ofClosed dBA₂ ∉
        completions (derivationClone kernel) (ofOpen (dischargeFirst planAB dA₁)) := by
  constructor
  · exact (mem_completions_iff_discharge (ofOpen planAB) dBA₂).mpr ⟨.cons dA₂ .nil, rfl⟩
  · intro member
    have closedMember : (OpenDerivation.ofClosed dBA₂ : (derivationClone kernel).Hom [] B) ∈
        completions (derivationClone kernel)
          (Plan.closed (derivationClone kernel) (OpenDerivation.ofClosed dBA₁)) := member
    have equal := (mem_completions_closed_iff _ _).mp closedMember
    exact dBA₁_ne_dBA₂ (ofClosed_injective equal).symm

/-- `bc(ab(?A))` beside an unused false obligation `X`. -/
def planCWithDeadObligation : OpenDerivation kernelDefinition [A, X] C :=
  OpenDerivation.bind planC (.cons (.assumption ⟨0, by simp⟩) .nil)

theorem planCWithDeadObligation_no_completion :
    ∀ completion, completion ∉
      completions (derivationClone kernel) (ofOpen planCWithDeadObligation) :=
  kernelPlanTruth.completions_empty (ofOpen planCWithDeadObligation) ⟨1, by decide⟩
    fun holds => holds.1 rfl

/-- **Refinement is coarser than being an instance.**  The two dead plans for
`C` have the same (empty) completion space, so each refines the other, and
neither is an instance of the other. -/
theorem refines_not_instanceOf :
    Completion.Refines (Completes (derivationClone kernel))
        (ofOpen planXC) (ofOpen planCWithDeadObligation) ∧
      Completion.Refines (Completes (derivationClone kernel))
        (ofOpen planCWithDeadObligation) (ofOpen planXC) ∧
      ¬ InstanceOf (ofOpen planXC) (ofOpen planCWithDeadObligation) ∧
      ¬ InstanceOf (ofOpen planCWithDeadObligation) (ofOpen planXC) := by
  refine ⟨fun completion member => absurd member (planXC_no_completion completion),
    fun completion member => absurd member (planCWithDeadObligation_no_completion completion),
    ?_, ?_⟩
  · rintro ⟨environment, equation⟩
    have rooted : planXC = OpenDerivation.bind planCWithDeadObligation
        (OpenDerivationList.ofFn _ environment) := equation
    injection rooted with sameInstance
    simp [ruleInstance, ruleXC, ruleBC, groundRule] at sameInstance
  · rintro ⟨environment, equation⟩
    have rooted : planCWithDeadObligation = OpenDerivation.bind planXC
        (OpenDerivationList.ofFn _ environment) := equation
    injection rooted with sameInstance
    simp [ruleInstance, ruleXC, ruleBC, groundRule] at sameInstance

/-! ### Elaboration -/

/-- **Positive.**  The library macro `lib-ac(?A)` elaborates to the kernel plan
`bc(ab(?A))`, with the same obligation. -/
theorem elaborate_libraryPlan : elaborateLibrary.mapOpen libraryPlan = planC := rfl

/-- **Positive.**  The library completion `lib-ac(lib-axA)` elaborates to the
kernel completion `bc(ab(axA₁))`. -/
theorem elaborate_library_completion :
    elaborateLibrary.mapDerivation (libraryPlan.discharge (.cons libraryA .nil)) = dC := rfl

/-- The same equation, read through the elaboration theorem: completing the
elaborated plan with the elaborated evidence. -/
theorem elaborate_library_completion' :
    (elaborateLibrary.mapOpen libraryPlan).discharge
        (mapEvidence elaborateLibrary (.cons libraryA .nil)) = dC := by
  rw [← mapDerivation_discharge]
  exact elaborate_library_completion

/-! ### Untrusted artifacts -/

/-- The raw plan `bc(ab(?0))`. -/
def rawPlanC : RawOpenProof := planC.eraseOpen

theorem rawPlanC_accepted : checkOpenRaw kernelDefinition [A] C rawPlanC = true :=
  checkOpenRaw_erase planC

/-- **Positive.**  The raw plan completed by the raw proof of `axA₁` is a raw
proof of `C` accepted by the kernel checker. -/
theorem wire_positive :
    ∃ proof : RawProof, checkRaw kernelDefinition C proof = true ∧
      rawToOpen proof = RawOpenProof.substitute (rawToOpenList [dA₁.erase]) rawPlanC :=
  wire_plan_soundness rawPlanC_accepted (by
    simp only [checkRawChildren, checkRaw_erase dA₁, Bool.and_true])

/-- The erasure of a closed derivation determines its goal. -/
theorem erase_determines_goal {definition : ValidatedCalculusLanguageDef}
    {first second : Pattern} (left : Derivation definition first)
    (right : Derivation definition second) (erased : left.erase = right.erase) :
    first = second := by
  refine (eraseOpen_determines (OpenDerivation.ofClosed (context := []) left)
    (OpenDerivation.ofClosed (context := []) right) ?_).1
  rw [eraseOpen_ofClosed, eraseOpen_ofClosed, erased]

/-- **Negative.**  A raw proof of `B` offered for the obligation `A` is rejected
by the kernel checker, so it cannot complete the plan. -/
theorem wire_wrong_evidence_rejected :
    checkRawChildren kernelDefinition [A] [dB.erase] = false := by
  cases accepted : checkRawChildren kernelDefinition [A] [dB.erase] with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨derivations, erased⟩ :=
        checkRawChildren_exists_derivations_with_exact_erasure accepted
      cases derivations with
      | cons derivation rest =>
          simp only [DerivationList.erase, List.cons.injEq] at erased
          have same := erase_determines_goal derivation dB erased.1
          simp [A, B, judgment] at same

end PlanControls

end Mettapedia.GSLT.ProofPlans
