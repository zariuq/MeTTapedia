import Mettapedia.Logic.HOL.ProofSyntaxStructural
import Mettapedia.Logic.HOL.Embedding.GroundUnaryEquationalProofSyntax
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListChartNIKService

/-!
# Submitted uniform-list certificates produce retained HOL derivations

The actual request's base and step certificates drive structural reconstruction
into the complete retained HOL calculus. Indexed equation leaves expand proofs
from the displayed equations; a fixed object-HOL induction scaffold combines
the resulting subtrees. No tree is chosen from proposition-valued derivability.

Erasure agrees with the existing intrinsic service producer on the exact source
claim and ordered assumptions. This retains a guest HOL proof, not a native
inhabitant of its represented proposition, and selects no final proof kernel.
The existing binding checker is not an external/raw-byte proof validator.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace UniformListChartProofSyntax

open Mettapedia.Logic HOL HOL.UniformListInduction
open HOL.UniformListInductionChart HOL.GroundUnaryEquationalChart

local instance : DecidableEq BaseSort
  | .element, .element | .sequence, .sequence | .count, .count => .isTrue rfl
  | .element, .sequence | .element, .count | .sequence, .element
  | .sequence, .count | .count, .element | .count, .sequence =>
      .isFalse (by intro h; cases h)

local instance (τ : HOL.Ty BaseSort) : DecidableEq (Symbol τ) := by
  intro a b
  cases a <;> cases b <;> exact .isTrue rfl

variable {Γ : HOL.Ctx BaseSort}

private def predicateBeta (f : UniformListInduction.Expr Γ mapping)
    (xs : UniformListInduction.Expr Γ sequence) (Δ : List (Sentence Γ)) :
    ProofSyntax Symbol Δ (.eq (.app (lengthPredicate f) xs) (preservesLength f xs)) := by
  simpa only [lengthPredicate, instantiate_lengthPredicateBody] using
    (ProofSyntax.beta (Δ := Δ) xs (preservesLength (weaken f) (.var .vz)))

private def predicateOfEquation {f : UniformListInduction.Expr Γ mapping}
    {xs : UniformListInduction.Expr Γ sequence} {Δ : List (Sentence Γ)}
    (proof : ProofSyntax Symbol Δ (preservesLength f xs)) :
    ProofSyntax Symbol Δ (.app (lengthPredicate f) xs) :=
  .impE (.eqPropER (predicateBeta f xs Δ)) proof

private def equationOfPredicate {f : UniformListInduction.Expr Γ mapping}
    {xs : UniformListInduction.Expr Γ sequence} {Δ : List (Sentence Γ)}
    (proof : ProofSyntax Symbol Δ (.app (lengthPredicate f) xs)) :
    ProofSyntax Symbol Δ (preservesLength f xs) :=
  .impE (.eqPropEL (predicateBeta f xs Δ)) proof

private def baseEquation (f : UniformListInduction.Expr Γ mapping) :
    ProofSyntax Symbol equations (preservesLength f nil) := by
  have ax : ProofSyntax Symbol (equations (Γ := Γ)) mapNil := .hyp ⟨0, by simp [equations]⟩
  have proof : ProofSyntax Symbol equations (.eq (map f nil) nil) := by
    simpa [mapNil, instantiate, subst, Subst.single, map, nil] using ProofSyntax.allE f ax
  exact .eqAppArg (.const .length) proof

private theorem substitute_weaken {σ τ : HOL.Ty BaseSort}
    (term : UniformListInduction.Expr Γ σ) (body : UniformListInduction.Expr Γ τ) :
    subst (Subst.single term) (weaken body) = body := instantiate_weaken term body

private theorem substitute_renamed_weaken {σ τ : HOL.Ty BaseSort}
    (term : UniformListInduction.Expr Γ σ) (body : UniformListInduction.Expr Γ τ) :
    subst (Subst.single term) (HOL.rename Rename.weaken body) = body :=
  instantiate_weaken term body

private def mapConsEquation (f : UniformListInduction.Expr Γ mapping)
    (x : UniformListInduction.Expr Γ element) (xs : UniformListInduction.Expr Γ sequence) :
    ProofSyntax Symbol equations
      (.eq (map f (cons x xs)) (cons (.app f x) (map f xs))) := by
  have ax : ProofSyntax Symbol (equations (Γ := Γ)) mapCons := .hyp ⟨1, by simp [equations]⟩
  have atFunction : ProofSyntax Symbol equations
      (.all (.all (.eq
        (map (weaken (weaken f)) (cons (.var (.vs .vz)) (.var .vz)))
        (cons (.app (weaken (weaken f)) (.var (.vs .vz)))
          (map (weaken (weaken f)) (.var .vz)))))) := by
    simpa [mapCons, map, cons, instantiate, subst, Subst.single, Subst.lift,
      weaken, Rename.weaken] using ProofSyntax.allE f ax
  have atElement := ProofSyntax.allE x atFunction
  have atSequence := ProofSyntax.allE xs atElement
  simpa [map, cons, instantiate, subst, Subst.single, Subst.lift,
    substitute_weaken, substitute_renamed_weaken] using atSequence

private def lengthConsEquation (x : UniformListInduction.Expr Γ element)
    (xs : UniformListInduction.Expr Γ sequence) :
    ProofSyntax Symbol equations (.eq (length (cons x xs)) (succ (length xs))) := by
  have ax : ProofSyntax Symbol (equations (Γ := Γ)) lengthCons := .hyp ⟨3, by simp [equations]⟩
  have atElement := ProofSyntax.allE x ax
  have atSequence := ProofSyntax.allE xs atElement
  simpa [lengthCons, length, cons, succ, instantiate, subst, Subst.single,
    Subst.lift, substitute_renamed_weaken] using atSequence

private def inductionReconstruction (p : UniformListInduction.Expr Γ predicate)
    {Δ : List (Sentence Γ)} (principle : ProofSyntax Symbol Δ inductionPrinciple)
    (base : ProofSyntax Symbol Δ (.app p nil))
    (step : ProofSyntax Symbol Δ (inductionStep p)) :
    ProofSyntax Symbol Δ (.all (.app (weaken p) (.var .vz))) := by
  have instanceProof : ProofSyntax Symbol Δ
      (.imp (.app p nil)
        (.imp (inductionStep p) (.all (.app (weaken p) (.var .vz))))) := by
    simpa [inductionPrinciple, inductionStep, nil, cons, instantiate, subst, Subst.single,
      Subst.lift, weaken, HOL.rename, Rename.lift, Rename.weaken] using
      ProofSyntax.allE p principle
  exact .impE (.impE instanceProof base) step

variable (Γ : HOL.Ctx BaseSort)

/-- The base system's actual equation occurrence chooses its displayed source
proof. These are not proofs of the complete chart goal. -/
def baseLicense (i : Fin (baseSystem Γ).equations.length)
    (ν : Nat → UniformListInduction.Expr (mapping :: Γ) count) :
    ProofSyntax Symbol equations (formula (baseChart Γ) ν ((baseSystem Γ).equations.get i)) := by
  change Fin 2 at i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact baseEquation (.var .vz)
  · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    exact .hyp ⟨2, by simp [equations]⟩

/-- All four cons equations are reconstructed from their source equation or
the actual induction-hypothesis occurrence, in the original order. -/
def stepLicense (i : Fin (stepSystem Γ).equations.length)
    (ν : Nat → UniformListInduction.Expr (stepContext Γ) count) :
    ProofSyntax Symbol (preservesLength (stepFunction Γ) (stepSequence Γ) :: equations)
      (formula (stepChart Γ) ν ((stepSystem Γ).equations.get i)) := by
  change Fin 4 at i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact (ProofSyntax.eqAppArg (.const Symbol.length)
      (mapConsEquation (stepFunction Γ) (stepElement Γ) (stepSequence Γ))).prepend _
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact (lengthConsEquation (.app (stepFunction Γ) (stepElement Γ))
        (map (stepFunction Γ) (stepSequence Γ))).prepend _
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact .hyp ⟨0, by simp⟩
      · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        exact (lengthConsEquation (stepElement Γ) (stepSequence Γ)).prepend _

def baseReconstruct (certificate : Certificate (baseChart Γ) (baseSystem Γ))
    (accepted : accepts (baseChart Γ) 1 (baseAssumptions Γ) (baseGoal Γ)
      (baseSystem Γ) certificate = true) : ProofSyntax Symbol equations (baseGoal Γ) :=
  reconstructAccepted (baseChart Γ) 1 (baseAssumptions Γ) (baseGoal Γ)
    (baseSystem Γ) certificate accepted (baseLicense Γ) (fun _ => .const .zero)

def stepReconstruct (certificate : Certificate (stepChart Γ) (stepSystem Γ))
    (accepted : accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) certificate = true) :
    ProofSyntax Symbol (preservesLength (stepFunction Γ) (stepSequence Γ) :: equations)
      (stepGoal Γ) :=
  reconstructAccepted (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
    (stepSystem Γ) certificate accepted (stepLicense Γ) (fun _ => .const .zero)

private def predicateStep (certificate : Certificate (stepChart Γ) (stepSystem Γ))
    (accepted : accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) certificate = true) :
    ProofSyntax Symbol equations
      (inductionStep (lengthPredicate (.var .vz :
        UniformListInduction.Expr (mapping :: Γ) mapping))) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  simp only [weaken_equations, weaken_lengthPredicate]
  apply predicateOfEquation
  change ProofSyntax Symbol
    (.app (lengthPredicate (stepFunction Γ)) (stepSequence Γ) :: equations) (stepGoal Γ)
  have ih : ProofSyntax Symbol
      (.app (lengthPredicate (stepFunction Γ)) (stepSequence Γ) :: equations)
      (preservesLength (stepFunction Γ) (stepSequence Γ)) :=
    equationOfPredicate (.hyp ⟨0, by simp⟩)
  exact .impE ((ProofSyntax.impI (stepReconstruct Γ certificate accepted)).prepend _) ih

/-- The complete object-HOL induction tree contains the subtrees reconstructed
from these supplied certificates. Only its induction scaffold is fixed. -/
def mapLengthFromCertificates
    (baseProof : Certificate (baseChart Γ) (baseSystem Γ))
    (stepProof : Certificate (stepChart Γ) (stepSystem Γ))
    (baseAccepted : accepts (baseChart Γ) 1 (baseAssumptions Γ) (baseGoal Γ)
      (baseSystem Γ) baseProof = true)
    (stepAccepted : accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) stepProof = true) :
    ProofSyntax Symbol (theory (Γ := Γ)) mapLength := by
  apply ProofSyntax.allI
  simp only [weaken_theory]
  have base : ProofSyntax Symbol (equations (Γ := mapping :: Γ))
      (preservesLength (.var .vz) nil) :=
    .eqTrans (baseReconstruct Γ baseProof baseAccepted) (.eqSymm (.hyp ⟨2, by simp [equations]⟩))
  have predicateAll := inductionReconstruction (lengthPredicate (.var .vz))
    (Δ := theory) (.hyp ⟨0, by simp [theory]⟩)
    (predicateOfEquation (base.prepend _))
    ((predicateStep Γ stepProof stepAccepted).prepend _)
  apply ProofSyntax.allI
  simp only [weaken_theory]
  apply equationOfPredicate
  have weakened := ProofSyntax.rename (Rename.weaken (σ := sequence)) predicateAll
  have atSequence := ProofSyntax.allE (.var .vz) weakened
  simpa [weakenHyps, weaken, HOL.rename, Rename.lift, Rename.weaken, instantiate,
    subst, Subst.single, Subst.lift, lengthPredicate, preservesLength, length, map,
    theory, equations, inductionPrinciple, inductionStep, mapNil, mapCons,
    lengthNil, lengthCons, cons, nil, succ] using atSequence

def reconstruct (request : UniformListChartNIKService.ReplayRequest Γ)
    (accepted : UniformListChartNIKService.replayAccepted Γ request = true) :
    ProofSyntax Symbol request.claim.1 request.claim.2 := by
  have facts := (UniformListChartNIKService.replayAccepted_iff Γ request).mp accepted
  have claim := facts.1
  have basePremises := facts.2.1
  have stepPremises := facts.2.2.1
  have baseAccepted := facts.2.2.2.1
  have stepAccepted := facts.2.2.2.2
  rw [basePremises] at baseAccepted
  rw [stepPremises] at stepAccepted
  rw [claim]
  exact mapLengthFromCertificates Γ request.baseProof request.stepProof baseAccepted stepAccepted

def produce? (request : UniformListChartNIKService.ReplayRequest Γ) :
    Option (ProofSyntax Symbol request.claim.1 request.claim.2) :=
  if accepted : UniformListChartNIKService.replayAccepted Γ request = true then
    some (reconstruct Γ request accepted)
  else none

theorem reconstruct_meaning (request : UniformListChartNIKService.ReplayRequest Γ)
    (accepted : UniformListChartNIKService.replayAccepted Γ request = true) :
    (UniformListChartNIKService.sourceTarget Γ).Meaning request.claim :=
  (reconstruct Γ request accepted).erase

/-- The old result is exactly the coarse erasure of this retained producer.
Equality here identifies intrinsic admissions, not intensional proof trees. -/
theorem produce_erasure (request : UniformListChartNIKService.ReplayRequest Γ) :
    (produce? Γ request).map ProofSyntax.intrinsicAdmission =
      UniformListChartNIKService.produce? Γ request := by
  unfold produce? UniformListChartNIKService.produce?
  split <;> rfl

theorem reconstruct_native_accepted (request : UniformListChartNIKService.ReplayRequest Γ)
    (accepted : UniformListChartNIKService.replayAccepted Γ request = true) :
    (UniformListChartNIKService.intrinsicKernel Γ).decide request.claim
      (reconstruct Γ request accepted).intrinsicAdmission = true := by
  apply (UniformListChartNIKService.intrinsicKernel Γ).correct _ _ |>.mpr
  rfl

theorem rejected_no_tree (request : UniformListChartNIKService.ReplayRequest Γ)
    (rejected : UniformListChartNIKService.replayAccepted Γ request = false) :
    produce? Γ request = none := by simp [produce?, rejected]

def actualProof : ProofSyntax Symbol (theory (Γ := Γ)) mapLength :=
  reconstruct Γ (UniformListChartNIKService.actualRequest Γ)
    (UniformListChartNIKService.actual_replay_accepted Γ)

theorem actual_produced :
    produce? Γ (UniformListChartNIKService.actualRequest Γ) = some (actualProof Γ) := rfl

theorem malformed_rejected : produce? Γ
    { UniformListChartNIKService.actualRequest Γ with stepProof := malformedCertificate Γ } =
      none := rfl

theorem changed_premise_rejected : produce? Γ
    { UniformListChartNIKService.actualRequest Γ with stepPremises := alteredStepAssumptions Γ } =
      none := rfl

theorem missing_induction_rejected : produce? Γ
    { UniformListChartNIKService.actualRequest Γ with claim := (equations, mapLength) } =
      none := rfl

/-! ## Two accepted submitted strategies remain inspectably different -/

/-- A genuine alternative input certificate: two explicit symmetry steps
around the submitted base transitivity proof. Its conclusion is unchanged. -/
def detouredBaseCertificate : Certificate (baseChart Γ) (baseSystem Γ) :=
  .node (atom (baseChart Γ) 0, atom (baseChart Γ) 2)
    (.symm (atom (baseChart Γ) 2) (atom (baseChart Γ) 0)) 1
    (fun _ => .node (atom (baseChart Γ) 2, atom (baseChart Γ) 0)
      (.symm (atom (baseChart Γ) 0) (atom (baseChart Γ) 2)) 1
      (fun _ => baseCertificate Γ))

def detouredRequest : UniformListChartNIKService.ReplayRequest Γ :=
  { UniformListChartNIKService.actualRequest Γ with baseProof := detouredBaseCertificate Γ }

theorem detoured_accepted :
    UniformListChartNIKService.replayAccepted Γ (detouredRequest Γ) = true := rfl

def detouredProof : ProofSyntax Symbol (theory (Γ := Γ)) mapLength :=
  reconstruct Γ (detouredRequest Γ) (detoured_accepted Γ)

theorem detoured_produced : produce? Γ (detouredRequest Γ) = some (detouredProof Γ) := rfl

theorem same_intrinsic_admission :
    (actualProof Γ).intrinsicAdmission = (detouredProof Γ).intrinsicAdmission :=
  ProofSyntax.intrinsicAdmission_eq _ _

theorem actual_tree_nodes : (actualProof []).nodeCount = 50 := by decide +kernel

theorem detoured_tree_nodes : (detouredProof []).nodeCount = 52 := by decide +kernel

theorem submitted_certificates_distinct : baseCertificate Γ ≠ detouredBaseCertificate Γ := by
  intro equal
  have counts := congrArg Derivation.nodeCount equal
  change 3 = 5 at counts
  omega

/-- The actual chart strategy is retained through source licensing, both
object binders, renaming and induction reconstruction. -/
theorem retained_strategies_distinct : actualProof [] ≠ detouredProof [] := by
  intro equal
  have counts := congrArg ProofSyntax.nodeCount equal
  rw [actual_tree_nodes, detoured_tree_nodes] at counts
  omega

theorem retained_observations_distinct : (actualProof []).observe ≠ (detouredProof []).observe := by
  intro equal
  have counts := congrArg Derivation.nodeCount equal
  change (actualProof []).nodeCount = (detouredProof []).nodeCount at counts
  rw [actual_tree_nodes, detoured_tree_nodes] at counts
  omega

theorem no_decoder_of_intrinsic_admission :
    ¬ ∃ decode : (UniformListChartNIKService.intrinsicProofSystem []).ProofObject →
        ProofSyntax Symbol (theory (Γ := [])) mapLength,
      decode (actualProof []).intrinsicAdmission = actualProof [] ∧
      decode (detouredProof []).intrinsicAdmission = detouredProof [] :=
  ProofSyntax.no_common_decoder _ _ retained_strategies_distinct

end UniformListChartProofSyntax
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
