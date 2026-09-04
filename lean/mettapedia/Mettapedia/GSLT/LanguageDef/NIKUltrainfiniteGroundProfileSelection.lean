import Mettapedia.GSLT.Core.UltrainfiniteDoctrineFactorization

/-!
# Request-local selection of ultrainfinite ground profiles

The two ultrainfinite doctrines are capabilities, not interchangeable proofs
of a NIK bootstrap contract.  This module records three concrete, nontrivial
profiles:

* finite-stage generative unboundedness;
* a nonprincipal ultrafilter perspective; and
* their product.

A request may select either doctrine alone or both.  Selection returns actual
witness data from the core factorization, not a Boolean label.  Exact support
sets make all three requests uniquely determined.

This catalog deliberately stops before `BootstrapLayer`.  A generative ground
still needs a theorem connecting its stable observations to the requested
operational contract, while a perspective ground still needs a theorem
connecting its ultrafilter meaning to the requested `modelSound` claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKUltrainfiniteGroundProfileSelection

open Mettapedia.GSLT.Ultrainfinite.DoctrineFactorization

/-! ## Profiles and their exact capability sets -/

inductive Capability where
  | finiteStageGeneration
  | nonprincipalPerspective
  deriving DecidableEq, Repr, Fintype

inductive Profile where
  | generative
  | perspectival
  | combined
  deriving DecidableEq, Repr

def supports : Profile → Capability → Prop
  | .generative, .finiteStageGeneration => True
  | .perspectival, .nonprincipalPerspective => True
  | .combined, _ => True
  | _, _ => False

instance supportsDecidable : DecidableRel supports
  | .generative, .finiteStageGeneration => isTrue trivial
  | .generative, .nonprincipalPerspective => isFalse id
  | .perspectival, .finiteStageGeneration => isFalse id
  | .perspectival, .nonprincipalPerspective => isTrue trivial
  | .combined, _ => isTrue trivial

def supportSet (profile : Profile) : Finset Capability :=
  Finset.univ.filter (supports profile)

@[simp] theorem supportSet_generative :
    supportSet .generative = {.finiteStageGeneration} := by
  ext capability
  cases capability <;> simp [supportSet, supports]

@[simp] theorem supportSet_perspectival :
    supportSet .perspectival = {.nonprincipalPerspective} := by
  ext capability
  cases capability <;> simp [supportSet, supports]

@[simp] theorem supportSet_combined :
    supportSet .combined =
      {.finiteStageGeneration, .nonprincipalPerspective} := by
  ext capability
  cases capability <;> simp [supportSet, supports]

/-! ## Every profile carries its actual mathematical witness -/

def Evidence : Profile → Type
  | .generative => GenerativeUnboundedGround Nat Nat FiniteStage
  | .perspectival =>
      NonprincipalPerspectiveGround Nat Nat (fun _ => Nat) (fun _ => Bool)
  | .combined => NaturalCombinedGround

noncomputable def evidence : (profile : Profile) → Evidence profile
  | .generative => standardGeneration
  | .perspectival => naturalNonprincipalPerspective
  | .combined => standardNonprincipalCombined

/-! ## Exact request-local selection -/

inductive Request where
  | generationOnly
  | perspectiveOnly
  | both
  deriving DecidableEq, Repr

def Request.required : Request → Finset Capability
  | .generationOnly => {.finiteStageGeneration}
  | .perspectiveOnly => {.nonprincipalPerspective}
  | .both => {.finiteStageGeneration, .nonprincipalPerspective}

def selected : Request → Profile
  | .generationOnly => .generative
  | .perspectiveOnly => .perspectival
  | .both => .combined

/-- The selected profile has exactly the requested capabilities: no requested
axis is missing and no unrequested semantic residue is silently added. -/
theorem selected_exact (request : Request) :
    supportSet (selected request) = request.required := by
  cases request <;> simp [selected, Request.required]

/-- Exact support makes the selected profile unique. -/
theorem selected_unique (request : Request) (profile : Profile)
    (exactSupport : supportSet profile = request.required) :
    profile = selected request := by
  have generationCoordinate :=
    congrArg
      (fun capabilities : Finset Capability =>
        .finiteStageGeneration ∈ capabilities)
      exactSupport
  have perspectiveCoordinate :=
    congrArg
      (fun capabilities : Finset Capability =>
        .nonprincipalPerspective ∈ capabilities)
      exactSupport
  cases request <;> cases profile <;>
    simp [selected, Request.required, supportSet, supports] at generationCoordinate perspectiveCoordinate ⊢

/-- Selection returns actual evidence at the dependent profile type. -/
noncomputable def selectedEvidence (request : Request) :
    Evidence (selected request) :=
  evidence (selected request)

/-! ## Discriminating controls -/

theorem generation_does_not_supply_perspective :
    ¬ supports .generative .nonprincipalPerspective := by
  simp [supports]

theorem perspective_does_not_supply_generation :
    ¬ supports .perspectival .finiteStageGeneration := by
  simp [supports]

theorem combined_supplies_generation :
    supports .combined .finiteStageGeneration := by
  simp [supports]

theorem combined_supplies_perspective :
    supports .combined .nonprincipalPerspective := by
  simp [supports]

/-- The combined selected evidence retains genuine next-stage novelty. -/
theorem combined_selected_has_realized_fresh (level : Nat) :
    ∃ next : FiniteStage (level + 1),
      ∀ previous : FiniteStage level,
        standardNonprincipalCombined.generative.realize (level + 1) next ≠
          standardNonprincipalCombined.generative.realize level previous :=
  standardNonprincipalCombined.generative.exists_realized_fresh level

/-- The combined selected evidence also retains a genuinely nonprincipal
semantic view. -/
theorem combined_selected_view_nonprincipal (perspective : Nat) :
    standardNonprincipalCombined.perspectival.view ≠ pure perspective :=
  naturalNonprincipalPerspective.nonprincipal perspective

#print axioms supportSet_generative
#print axioms supportSet_perspectival
#print axioms supportSet_combined
#print axioms selected_exact
#print axioms selected_unique
#print axioms generation_does_not_supply_perspective
#print axioms perspective_does_not_supply_generation
#print axioms combined_selected_has_realized_fresh
#print axioms combined_selected_view_nonprincipal

end Mettapedia.GSLT.LanguageDef.NIKUltrainfiniteGroundProfileSelection
