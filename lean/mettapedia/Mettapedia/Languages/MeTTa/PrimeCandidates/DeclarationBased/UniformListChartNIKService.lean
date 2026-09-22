import Mettapedia.GSLT.LanguageDef.NIK
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLUniformList
import Mettapedia.Logic.HOL.UniformListInductionChart

/-!
# Uniform-list chart production and intrinsic HOL proof admission

The semantic target is source HOL derivability under an exact list of
assumptions, not chart acceptance or native proposition formation. Submitted
equational certificates are replayed and reconstructed into a proof of the
original higher-order list theorem using its stated induction principle.

The native proof service is intrinsic: its proof-typed inputs have already
been admitted by the surrounding Lean/HOL calculus. Its executable binding
check does not independently validate arbitrary external HOL proof bytes.
HOL derivability, conditional model soundness and formed native representation
remain separate judgments; no native dependent proof inhabitant is supplied.
Chart rejection is non-admission, never a refutation of the source formula.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace UniformListChartNIKService

open Mettapedia.Logic HOL HOL.UniformListInduction
open HOL.UniformListInductionChart HOL.GroundUnaryEquationalChart
open Mettapedia.GSLT.LanguageDef NIKMetalogic

local instance : DecidableEq BaseSort
  | .element, .element | .sequence, .sequence | .count, .count => .isTrue rfl
  | .element, .sequence | .element, .count | .sequence, .element
  | .sequence, .count | .count, .element | .count, .sequence =>
      .isFalse (by intro h; cases h)

local instance (τ : HOL.Ty BaseSort) : DecidableEq (Symbol τ) := by
  intro a b
  cases a <;> cases b <;> exact .isTrue rfl

variable (Γ : HOL.Ctx BaseSort)

/-- The signature and context are fixed by the type; both assumptions and
conclusion remain explicit source HOL syntax. -/
abbrev SourceClaim := List (Sentence Γ) × Sentence Γ

def sourceTarget : AdmissionObject where
  Carrier := SourceClaim Γ
  Meaning := fun claim => ExtDerivation Symbol claim.1 claim.2

/-- Intrinsic source proofs, not serialized or unchecked proof terms. -/
def intrinsicProofSystem : NativeProofSystem (SourceClaim Γ) where
  ProofObject := { claim : SourceClaim Γ // ExtDerivation Symbol claim.1 claim.2 }
  Judges := fun proof claim => proof.1 = claim

def intrinsicKernel : NativeProofKernel (intrinsicProofSystem Γ) where
  decide claim proof := decide (proof.1 = claim)
  correct _ _ := decide_eq_true_iff

theorem intrinsic_meaning_exact (claim : SourceClaim Γ) :
    (sourceTarget Γ).Meaning claim ↔
      Nonempty ((intrinsicProofSystem Γ).ProofFibre claim) := by
  constructor
  · intro derivation
    exact ⟨⟨⟨claim, derivation⟩, rfl⟩⟩
  · rintro ⟨⟨⟨source, derivation⟩, binding⟩⟩
    cases binding
    exact derivation

def nativeProofService : NIK.Service (sourceTarget Γ) :=
  .nativeProof (intrinsicProofSystem Γ) (intrinsicKernel Γ) (intrinsic_meaning_exact Γ)

theorem native_accepts_iff_derivable (claim : SourceClaim Γ) :
    ExtDerivation Symbol claim.1 claim.2 ↔
      ∃ proof, (intrinsicKernel Γ).decide claim proof = true :=
  NIK.Service.nativeProof_accepts_iff_meaning
    (target := sourceTarget Γ)
    (intrinsicProofSystem Γ) (intrinsicKernel Γ) (intrinsic_meaning_exact Γ) claim

theorem native_acceptance_derivation (claim : SourceClaim Γ)
    (proof : (intrinsicProofSystem Γ).ProofObject)
    (accepted : (intrinsicKernel Γ).decide claim proof = true) :
    ExtDerivation Symbol claim.1 claim.2 :=
  (native_accepts_iff_derivable Γ claim).mpr ⟨proof, accepted⟩

theorem native_acceptance_sound (claim : SourceClaim Γ)
    (proof : (intrinsicProofSystem Γ).ProofObject)
    (accepted : (intrinsicKernel Γ).decide claim proof = true)
    (model : HenkinModel BaseSort Symbol) (valuation : model.Valuation Γ)
    (respects : model.FunctionsRespectEqv)
    (admissible : model.ValuationAdmissible valuation)
    (assumptions : Soundness.SatisfiesHyps model valuation claim.1) :
    (model.denote claim.2 valuation).down :=
  Soundness.extDerivation_sound (native_acceptance_derivation Γ claim proof accepted)
    respects admissible assumptions

/-! ## Submitted equational leaves and source reconstruction -/

def mapLengthClaim : SourceClaim Γ := (theory, mapLength)

/-- The certificates have the existing universal-algebra derivation syntax.
Their source premises and the final source request are independently supplied
and checked; no submitted acceptance bit or HOL derivation is trusted. -/
structure ReplayRequest where
  claim : SourceClaim Γ
  basePremises : List (Sentence (mapping :: Γ))
  stepPremises : List (Sentence (stepContext Γ))
  baseProof : Certificate (baseChart Γ) (baseSystem Γ)
  stepProof : Certificate (stepChart Γ) (stepSystem Γ)

def replayAccepted (request : ReplayRequest Γ) : Bool :=
  decide (request.claim = mapLengthClaim Γ) &&
  decide (request.basePremises = baseAssumptions Γ) &&
  decide (request.stepPremises = stepAssumptions Γ) &&
  accepts (baseChart Γ) 1 request.basePremises (baseGoal Γ) (baseSystem Γ) request.baseProof &&
  accepts (stepChart Γ) 2 request.stepPremises (stepGoal Γ) (stepSystem Γ) request.stepProof

theorem replayAccepted_iff (request : ReplayRequest Γ) :
    replayAccepted Γ request = true ↔
      request.claim = mapLengthClaim Γ ∧
      request.basePremises = baseAssumptions Γ ∧
      request.stepPremises = stepAssumptions Γ ∧
      accepts (baseChart Γ) 1 request.basePremises (baseGoal Γ)
        (baseSystem Γ) request.baseProof = true ∧
      accepts (stepChart Γ) 2 request.stepPremises (stepGoal Γ)
        (stepSystem Γ) request.stepProof = true := by
  simp only [replayAccepted, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

private theorem base_reconstruct (proof : Certificate (baseChart Γ) (baseSystem Γ))
    (accepted : accepts (baseChart Γ) 1 (baseAssumptions Γ) (baseGoal Γ)
      (baseSystem Γ) proof = true) :
    ExtDerivation Symbol equations (baseGoal Γ) := by
  apply accepts_reconstruct_licensed (baseChart Γ) 1 (baseAssumptions Γ)
    (baseGoal Γ) (baseSystem Γ) proof accepted (ν := fun _ => .const .zero)
  intro φ member
  simp only [baseAssumptions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact base_obligation (.var .vz)
  · exact .hyp (by simp [equations])

private theorem step_reconstruct (proof : Certificate (stepChart Γ) (stepSystem Γ))
    (accepted : accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) proof = true) :
    ExtDerivation Symbol (preservesLength (stepFunction Γ) (stepSequence Γ) :: equations)
      (stepGoal Γ) := by
  apply accepts_reconstruct_licensed (stepChart Γ) 2 (stepAssumptions Γ)
    (stepGoal Γ) (stepSystem Γ) proof accepted (ν := fun _ => .const .zero)
  have liftEquation {φ : Sentence (stepContext Γ)}
      (h : ExtDerivation Symbol equations φ) :
      ExtDerivation Symbol
        (preservesLength (stepFunction Γ) (stepSequence Γ) :: equations) φ :=
    ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ) h
  intro φ member
  simp only [stepAssumptions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact liftEquation (.eqAppArg (.const Symbol.length)
      (map_cons_equation (stepFunction Γ) (stepElement Γ) (stepSequence Γ)))
  · exact liftEquation (length_cons_equation
      (.app (stepFunction Γ) (stepElement Γ)) (map (stepFunction Γ) (stepSequence Γ)))
  · exact .hyp (by simp [preservesLength])
  · exact liftEquation (length_cons_equation (stepElement Γ) (stepSequence Γ))

private theorem predicate_step_reconstruct
    (proof : Certificate (stepChart Γ) (stepSystem Γ))
    (accepted : accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) proof = true) :
    ExtDerivation Symbol equations
      (inductionStep (lengthPredicate (.var .vz :
        HOL.UniformListInduction.Expr (mapping :: Γ) mapping))) := by
  apply ExtDerivation.allI
  apply ExtDerivation.allI
  apply ExtDerivation.impI
  simp only [weaken_equations, weaken_lengthPredicate]
  apply predicate_of_equation
  change ExtDerivation Symbol
    (.app (lengthPredicate (stepFunction Γ)) (stepSequence Γ) :: equations) (stepGoal Γ)
  have ih : ExtDerivation Symbol
      (.app (lengthPredicate (stepFunction Γ)) (stepSequence Γ) :: equations)
      (preservesLength (stepFunction Γ) (stepSequence Γ)) :=
    equation_of_predicate (.hyp (by simp))
  exact .impE
    (ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ)
      (.impI (step_reconstruct Γ proof accepted))) ih

/-- The submitted proofs, not fixed replacement certificates, supply the
equational leaves of the reconstructed object-HOL induction derivation. -/
theorem mapLength_of_accepted_leaves
    (baseProof : Certificate (baseChart Γ) (baseSystem Γ))
    (stepProof : Certificate (stepChart Γ) (stepSystem Γ))
    (baseAccepted : accepts (baseChart Γ) 1 (baseAssumptions Γ) (baseGoal Γ)
      (baseSystem Γ) baseProof = true)
    (stepAccepted : accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) stepProof = true) :
    ExtDerivation Symbol (theory (Γ := Γ)) mapLength := by
  apply ExtDerivation.allI
  simp only [weaken_theory]
  have liftEquation {φ : Sentence (mapping :: Γ)}
      (h : ExtDerivation Symbol equations φ) : ExtDerivation Symbol theory φ :=
    ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ) h
  have base : ExtDerivation Symbol (equations (Γ := mapping :: Γ))
      (preservesLength (.var .vz) nil) :=
    .eqTrans (base_reconstruct Γ baseProof baseAccepted)
      (.eqSymm (.hyp (by simp [equations, lengthNil])))
  have predicateAll := induction_reconstruction (lengthPredicate (.var .vz))
    (Δ := theory) (.hyp (by simp [theory]))
    (predicate_of_equation (liftEquation base))
    (liftEquation (predicate_step_reconstruct Γ stepProof stepAccepted))
  apply ExtDerivation.allI
  simp only [weaken_theory]
  apply equation_of_predicate
  have weakened := ExtDerivation.rename (Rename.weaken (σ := sequence)) predicateAll
  have atSequence := ExtDerivation.allE (.var .vz) weakened
  simpa [weakenHyps, weaken, rename, Rename.lift, Rename.weaken, instantiate,
    subst, Subst.single, Subst.lift, lengthPredicate, preservesLength, length, map,
    theory, equations, inductionPrinciple, inductionStep, mapNil, mapCons,
    lengthNil, lengthCons, cons, nil, succ] using atSequence

theorem replay_reconstruct (request : ReplayRequest Γ)
    (accepted : replayAccepted Γ request = true) :
    ExtDerivation Symbol request.claim.1 request.claim.2 := by
  rcases (replayAccepted_iff Γ request).mp accepted with
    ⟨claim, basePremises, stepPremises, baseAccepted, stepAccepted⟩
  rw [basePremises] at baseAccepted
  rw [stepPremises] at stepAccepted
  rw [claim]
  exact mapLength_of_accepted_leaves Γ request.baseProof request.stepProof
    baseAccepted stepAccepted

/-- Failed binding or failed equational replay produces no intrinsic proof.
The successful branch constructs its derivation from this request's actual
certificates. -/
def produce? (request : ReplayRequest Γ) : Option (intrinsicProofSystem Γ).ProofObject :=
  if accepted : replayAccepted Γ request = true then
    some ⟨request.claim, replay_reconstruct Γ request accepted⟩
  else none

theorem produce_isSome_iff (request : ReplayRequest Γ) :
    (produce? Γ request).isSome = true ↔ replayAccepted Γ request = true := by
  unfold produce?
  split
  · rename_i accepted
    exact ⟨fun _ => accepted, fun _ => rfl⟩
  · rename_i rejected
    constructor
    · intro impossible
      cases impossible
    · intro accepted
      exact False.elim (rejected accepted)

theorem produce_binds_request (request : ReplayRequest Γ)
    (proof : (intrinsicProofSystem Γ).ProofObject)
    (produced : produce? Γ request = some proof) : proof.1 = request.claim := by
  unfold produce? at produced
  split at produced
  · exact congrArg Subtype.val (Option.some.inj produced.symm)
  · cases produced

theorem produced_native_accepted (request : ReplayRequest Γ)
    (proof : (intrinsicProofSystem Γ).ProofObject)
    (produced : produce? Γ request = some proof) :
    (intrinsicKernel Γ).decide request.claim proof = true :=
  (intrinsicKernel Γ).correct _ _ |>.mpr (produce_binds_request Γ request proof produced)

/-- Admission of this produced proof checks the entire source claim, including
the ordered assumption list. This is syntactic binding, not a decision that
two theories have the same consequences. -/
theorem produced_native_acceptance_iff (request : ReplayRequest Γ)
    (proof : (intrinsicProofSystem Γ).ProofObject)
    (produced : produce? Γ request = some proof) (claim : SourceClaim Γ) :
    (intrinsicKernel Γ).decide claim proof = true ↔ claim = request.claim := by
  rw [(intrinsicKernel Γ).correct]
  change proof.1 = claim ↔ claim = request.claim
  rw [produce_binds_request Γ request proof produced]
  exact eq_comm

theorem request_mismatch_rejected (request : ReplayRequest Γ)
    (different : request.claim ≠ mapLengthClaim Γ) : produce? Γ request = none := by
  unfold produce?
  split
  · rename_i accepted
    exact False.elim (different ((replayAccepted_iff Γ request).mp accepted).1)
  · rfl

/-! ## Actual production and controls -/

def actualRequest : ReplayRequest Γ where
  claim := mapLengthClaim Γ
  basePremises := baseAssumptions Γ
  stepPremises := stepAssumptions Γ
  baseProof := baseCertificate Γ
  stepProof := stepCertificate Γ

theorem actual_replay_accepted : replayAccepted Γ (actualRequest Γ) = true := rfl

/-- Extract the actual producer output after its executable replay succeeds. -/
def actualNativeProof : (intrinsicProofSystem Γ).ProofObject :=
  (produce? Γ (actualRequest Γ)).get
    ((produce_isSome_iff Γ (actualRequest Γ)).mpr (actual_replay_accepted Γ))

theorem actual_produced : produce? Γ (actualRequest Γ) = some (actualNativeProof Γ) := rfl

theorem actual_native_accepted :
    (intrinsicKernel Γ).decide (mapLengthClaim Γ) (actualNativeProof Γ) = true :=
  produced_native_accepted Γ (actualRequest Γ) (actualNativeProof Γ) (actual_produced Γ)

theorem actual_source_derivation : ExtDerivation Symbol (theory (Γ := Γ)) mapLength :=
  native_acceptance_derivation Γ (mapLengthClaim Γ) (actualNativeProof Γ)
    (actual_native_accepted Γ)

theorem altered_local_premise_rejected :
    produce? Γ { actualRequest Γ with stepPremises := alteredStepAssumptions Γ } = none := rfl

theorem missing_local_premise_rejected :
    produce? Γ { actualRequest Γ with stepPremises := missingStepAssumptions Γ } = none := rfl

theorem malformed_leaf_rejected :
    produce? Γ { actualRequest Γ with stepProof := malformedCertificate Γ } = none := rfl

theorem missing_induction_request_rejected :
    produce? Γ { actualRequest Γ with claim := (equations, mapLength) } = none := rfl

theorem changed_conclusion_request_rejected :
    produce? Γ { actualRequest Γ with claim := (theory, lengthNil) } = none := rfl

theorem missing_induction_native_rejected :
    (intrinsicKernel Γ).decide (equations, mapLength) (actualNativeProof Γ) = false := rfl

theorem changed_conclusion_native_rejected :
    (intrinsicKernel Γ).decide (theory, lengthNil) (actualNativeProof Γ) = false := rfl

/-- This is stronger than rejection of one packet: no intrinsic HOL proof can
be admitted for the equations-only closed claim. The countermodel concerns
exactly the displayed count/list axioms, not a stronger arithmetic theory. -/
theorem missing_induction_has_no_native_proof :
    ¬ ∃ proof, (intrinsicKernel []).decide (equations, mapLength) proof = true := by
  rintro ⟨proof, accepted⟩
  exact equations_do_not_derive_mapLength
    (native_acceptance_derivation [] (equations, mapLength) proof accepted)

/-- Changing the target from derivability under the submitted assumptions to
unconditional truth in the junk model invalidates native-proof adequacy. The
accepted induction proof cannot justify that change of meaning. -/
theorem unconditional_junk_meaning_not_adequate :
    ¬ (∀ claim : SourceClaim [], JunkModel.model.models claim.2 ↔
      Nonempty ((intrinsicProofSystem []).ProofFibre claim)) := by
  intro adequate
  apply JunkModel.mapLength_invalid
  apply (adequate (mapLengthClaim [])).mpr
  exact ⟨⟨actualNativeProof [],
    (intrinsicKernel []).correct _ _ |>.mp (actual_native_accepted [])⟩⟩

/-! ## The same source claim has a separately formed representation -/

open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
  Presentation.FormationSensitive in
/-- Successful production connects native source-proof admission to the
representation of its exact source assumptions and conclusion. The final
judgments form propositions; they are not proof inhabitants of them. -/
theorem produced_admission_and_representation (request : ReplayRequest Γ)
    (proof : (intrinsicProofSystem Γ).ProofObject)
    (produced : produce? Γ request = some proof) :
    (intrinsicKernel Γ).decide request.claim proof = true ∧
      ExtDerivation Symbol request.claim.1 request.claim.2 ∧
      represent signature request.claim.2 = some rawMapLength ∧
      request.claim.1.map (represent signature) = (rawTheory (n := Γ.length)).map some ∧
      Judgment rules (context types Γ) rawMapLength (.const `HOLUniformList.prop) ∧
      (∀ formula ∈ rawTheory (n := Γ.length),
        Judgment rules (context types Γ) formula (.const `HOLUniformList.prop)) := by
  have accepted := (produce_isSome_iff Γ request).mp
    (show (produce? Γ request).isSome = true by rw [produced]; rfl)
  have binding := ((replayAccepted_iff Γ request).mp accepted).1
  refine ⟨produced_native_accepted Γ request proof produced,
    replay_reconstruct Γ request accepted, ?_, ?_, mapLength_formed Γ, theory_formed Γ⟩
  · rw [binding]
    exact mapLength_represented Γ
  · rw [binding]
    exact theory_represented Γ

open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
  Presentation.FormationSensitive in
theorem actual_admission_and_formation :
    (intrinsicKernel Γ).decide (mapLengthClaim Γ) (actualNativeProof Γ) = true ∧
      ExtDerivation Symbol (theory (Γ := Γ)) mapLength ∧
      represent signature (mapLength (Γ := Γ)) = some rawMapLength ∧
      (theory (Γ := Γ)).map (represent signature) = (rawTheory (n := Γ.length)).map some ∧
      Judgment rules (context types Γ) rawMapLength (.const `HOLUniformList.prop) ∧
      (∀ formula ∈ rawTheory (n := Γ.length),
        Judgment rules (context types Γ) formula (.const `HOLUniformList.prop)) :=
  produced_admission_and_representation Γ (actualRequest Γ) (actualNativeProof Γ)
    (actual_produced Γ)

open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
  Presentation.FormationSensitive in
/-- Forming the same represented conclusion cannot supply a missing source
induction assumption or manufacture an admitted source proof. -/
theorem formed_conclusion_does_not_supply_induction :
    Judgment rules (context types []) rawMapLength (.const `HOLUniformList.prop) ∧
      ¬ ∃ proof, (intrinsicKernel []).decide (equations, mapLength) proof = true :=
  ⟨mapLength_formed [], missing_induction_has_no_native_proof⟩

#print axioms mapLength_of_accepted_leaves
#print axioms replay_reconstruct
#print axioms produced_native_acceptance_iff
#print axioms native_acceptance_sound
#print axioms actual_admission_and_formation
#print axioms altered_local_premise_rejected
#print axioms malformed_leaf_rejected
#print axioms missing_induction_has_no_native_proof
#print axioms unconditional_junk_meaning_not_adequate
#print axioms formed_conclusion_does_not_supply_induction

end UniformListChartNIKService
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
