import Mettapedia.Logic.ProofSearch.PolynomialPlans
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLProofObligationControls

/-!
# Filling a retained HOL plan and compiling its actual reconstruction

The unfinished plan retains a solved major implication and an open minor
premise. Filling the minor inserts a hypothesis method; the major subtree
does not change. The resulting proof tree passes through the existing compiler
with its existing typing and denotation theorems. Choosing a different actual
hypothesis occurrence changes both the retained proof and the compiled term.
No search policy, rule admission condition, or implementation authority changes.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace PolynomialHOLProofPlanControls

open Mettapedia.Logic HOL
open ProofSearch ProofObligations
open Presentation FormationSensitiveHOLInterface HOLNativeGenericProofCompiler
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open FormationSensitiveHOLGenericProofInstances.CallGuard

private abbrev Goal := HOLAdapter.Goal Unit Constant
private abbrev Solution := @HOLAdapter.Solution Unit Constant

/-- This client uses the existing lawful refinements as its route inventory. -/
private abbrev methods (goal : Goal) (route : Refinement Solution goal) := route

private abbrev root := HOLProofObligationControls.goal
private abbrev leaf := HOLProofObligationControls.leaf
private abbrev introduction := HOLProofObligationControls.route

def elimination : Refinement Solution leaf :=
  ProofObligations.HOL.impE HOLProofObligationControls.atom HOLProofObligationControls.atom

def major : Solution (elimination.query ⟨0⟩) := .impI (.hyp 0)

/-- Only the minor premise is pending; checked leaves retain their actual trees. -/
inductive Hole : Goal → Type
  | checked {goal : Goal} (proof : Solution goal) : Hole goal
  | minor : Hole leaf

def children : ∀ occurrence, PolynomialPlans.Plan methods Hole (elimination.query occurrence) :=
  fun occurrence => Fin.cases
    (motive := fun index : Fin 2 => PolynomialPlans.Plan methods Hole
      (elimination.query ⟨index⟩))
    (PolynomialPlans.hole methods (.checked major))
    (fun _ => PolynomialPlans.hole methods .minor) occurrence.down

def partialLeaf : PolynomialPlans.Plan methods Hole leaf :=
  PolynomialPlans.applyMethod methods elimination children

def partialPlan : PolynomialPlans.Plan methods Hole root :=
  PolynomialPlans.applyMethod methods introduction (fun _ => partialLeaf)

def inspect : ∀ goal, Hole goal → Option (Solution goal)
  | _, .checked proof => some proof
  | _, .minor => none

noncomputable def pending : PolynomialPlans.Plan methods (fun goal => Option (Solution goal)) root :=
  PolynomialPlans.fill methods
    (fun _ value => PolynomialPlans.hole methods (inspect _ value)) partialPlan

/-- An unfinished tree remains a value but does not reconstruct a parent proof. -/
theorem pending_has_no_parent : PolynomialPlans.reconstruct? methods pending = none := by
  change introduction.tryRebuild (fun _ => elimination.tryRebuild
    (fun occurrence => PolynomialPlans.reconstruct? methods
      (PolynomialPlans.fill methods
        (fun _ value => PolynomialPlans.hole methods (inspect _ value))
        (children occurrence)))) = none
  apply (Refinement.tryRebuild_eq_none_iff _ _).2
  refine ⟨⟨⟨⟨⟨0⟩, ⟨0⟩⟩, ⟨0⟩⟩, ⟨0⟩⟩, ?_⟩
  change elimination.tryRebuild _ = none
  apply (Refinement.tryRebuild_eq_none_iff _ _).2
  exact ⟨⟨1⟩, rfl⟩

/-- Replacement uses an existing proof method, rather than inserting an axiom. -/
def replacement (proof : Solution leaf) :
    ∀ goal, Hole goal → PolynomialPlans.Plan methods Solution goal
  | _, .checked checked => PolynomialPlans.hole methods checked
  | _, .minor => PolynomialPlans.applyMethod methods (Refinement.discharged proof)
      (fun occurrence => Fin.elim0 occurrence.down)

theorem solved_major_retained (proof : Solution leaf) :
    PolynomialPlans.fill methods (replacement proof) (children ⟨0⟩) =
      PolynomialPlans.hole methods major := rfl

theorem minor_gets_its_method (proof : Solution leaf) :
    PolynomialPlans.fill methods (replacement proof) (children ⟨1⟩) =
      PolynomialPlans.applyMethod methods (Refinement.discharged proof)
        (fun occurrence => Fin.elim0 occurrence.down) := rfl

noncomputable def filled (proof : Solution leaf) : PolynomialPlans.Plan methods Solution root :=
  PolynomialPlans.fill methods (replacement proof) partialPlan

def returned (proof : Solution leaf) : Solution root :=
  .allI (.allI (.impI (.impI (.impE major proof))))

/-- Reconstruction folds the retained major and the newly supplied minor. -/
theorem reconstruct_filled (proof : Solution leaf) :
    PolynomialPlans.reconstruct methods (filled proof) = returned proof := rfl

private abbrev signature := FormationSensitiveHOLInvariant.signature
private abbrev operations := Operations.logicalOnly signature proofName proofName_fresh

def native : Tower.Tm 0 := .lam (.lam (.lam (.lam (.app (.lam (.var 0)) (.var 0)))))

def nativeOlder : Tower.Tm 0 := .lam (.lam (.lam (.lam (.app (.lam (.var 0)) (.var 1)))))

set_option maxRecDepth 10000 in
theorem actual_compiles : compile signature proofName operations
    (PolynomialPlans.reconstruct methods (filled HOLProofObligationControls.found.proof))
    Fin.elim0 Fin.elim0 = some native := by
  rw [reconstruct_filled]
  decide +kernel

set_option maxRecDepth 10000 in
theorem older_compiles : compile signature proofName operations
    (PolynomialPlans.reconstruct methods (filled HOLProofObligationControls.olderProof))
    Fin.elim0 Fin.elim0 = some nativeOlder := by
  change compile signature proofName operations
    (returned HOLProofObligationControls.olderProof) Fin.elim0 Fin.elim0 = some nativeOlder
  decide +kernel

theorem compiled_occurrences_distinct : native ≠ nativeOlder := by
  intro same
  cases same

theorem retained_occurrences_distinct :
    PolynomialPlans.reconstruct methods (filled HOLProofObligationControls.found.proof) ≠
      PolynomialPlans.reconstruct methods (filled HOLProofObligationControls.olderProof) := by
  intro same
  have equalCompilation := congrArg
    (fun proof => compile signature proofName operations proof (n := 0) Fin.elim0 Fin.elim0) same
  rw [actual_compiles, older_compiles] at equalCompilation
  exact compiled_occurrences_distinct (Option.some.inj equalCompilation)

private theorem objectsTyped : GenericTyping.Objects signature (gamma := []) .nil Fin.elim0 := by
  intro index; nomatch index

private theorem hypothesesTyped : GenericTyping.Hypotheses signature operations
    (gamma := []) (delta := []) .nil Fin.elim0 Fin.elim0 := by
  intro index; nomatch index

theorem native_typed :
    ∃ code, represent signature HOLProofObligationControls.query = some code ∧
      FormationSensitive.Typing operations.target .nil native
        (FormationSensitiveHOLGenericProofFamily.proof proofName code) := by
  simpa only [root, HOLProofObligationControls.goal, TelescopeAbstraction.subst_empty,
    TelescopeAbstraction.liftClosed_zero] using
    GenericTyping.compile_typed signature proofName operations
      (PolynomialPlans.reconstruct methods (filled HOLProofObligationControls.found.proof))
      objectsTyped hypothesesTyped actual_compiles

theorem native_denotes (property : CompileLanguageControl → Prop) :
    HenkinFamilySemantics.Proves (CallGuardSemantics.emptyState property) native
      HOLProofObligationControls.query := by
  apply GenericSemantics.compile_denotes signature proofName operations
    (CallGuardSemantics.semantics property)
    (PolynomialPlans.reconstruct methods (filled HOLProofObligationControls.found.proof))
    actual_compiles (CallGuardSemantics.emptyState property)
  intro index; nomatch index

/-- Equal child goals are not a license to discard a premise occurrence. -/
noncomputable def duplicatePending : PolynomialPlans.Plan methods
    (fun goal => Option (Solution goal))
    (⟨[], [], .and HOLProofObligationControls.duplicateProof
      HOLProofObligationControls.duplicateProof⟩ : Goal) :=
  PolynomialPlans.applyMethod methods HOLProofObligationControls.duplicateRoute
    (fun occurrence => PolynomialPlans.hole methods
      (HOLProofObligationControls.duplicateCandidate false occurrence))

theorem equal_goals_do_not_fill_missing_occurrences :
    PolynomialPlans.reconstruct? methods duplicatePending = none :=
  HOLProofObligationControls.either_premise_missing false

#print axioms pending_has_no_parent
#print axioms solved_major_retained
#print axioms reconstruct_filled
#print axioms actual_compiles
#print axioms retained_occurrences_distinct
#print axioms native_typed
#print axioms native_denotes
#print axioms equal_goals_do_not_fill_missing_occurrences

end PolynomialHOLProofPlanControls
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
