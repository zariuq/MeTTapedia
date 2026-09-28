import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedBetaPathControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedIdentityPaths
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedIdentityImages

/-!
# Distinct computed endpoints in checked identity fibres

One identity formation compares a two-step result with a one-step result;
the other compares the one-step result with the neutral identity function.
The raw identity subjects and their retained endpoint certificates differ.
Four bounded searches recover the retained endpoint paths; their set-valued
identity fibres then agree on the valid context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedIdentityPathControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedTypingControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedBetaPathControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseModel
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)

private abbrev functionLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))

def firstIdentity : Tower.Tm 0 := .id functionType nestedFunction computedFunction
def firstIdentityCode : Code Tower.Head NoConversion 0 :=
  .idForm functionLevel functionFormation nestedFunctionCode computedFunctionCode
def secondIdentity : Tower.Tm 0 := .id functionType computedFunction identity
def secondIdentityCode : Code Tower.Head NoConversion 0 :=
  .idForm functionLevel functionFormation computedFunctionCode identityCode

theorem identities_checked :
    check Tower.rules noConversionCheck .nil firstIdentity (.head functionLevel)
      firstIdentityCode = true ∧
      check Tower.rules noConversionCheck .nil secondIdentity (.head functionLevel)
        secondIdentityCode = true := by
  decide +kernel

theorem identity_subjects_differ : firstIdentity ≠ secondIdentity := by
  decide +kernel

/-- The common terminal lambda is outside the unannotated structural
interpretation fragment, although retained-certificate search recognizes it. -/
theorem lambda_terminal_requires_certificate :
    ZFSetTypeExpressionInterpretation.supported (identity : Tower.Tm 0) = false ∧
      (identityCode.qualifiedBetaPath? Tower.rules TowerDecisions.headTarget
        .nil 1 identity functionType).map Subtype.val = some (identity, identityCode) :=
  ⟨rfl, rfl⟩

universe u

/-- Four bounded searches recover checked endpoint paths and establish
equality of two identity fibres with different raw source subjects. -/
theorem computed_identity_fibres_agree
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ first second,
      assemble (interpretHead h seed ground valuation) constants firstIdentityCode
        firstIdentity (.head functionLevel) = some first ∧
      assemble (interpretHead h seed ground valuation) constants secondIdentityCode
        secondIdentity (.head functionLevel) = some second ∧
      ∀ env : Environment.{u} 0, first.value env = second.value env := by
  obtain ⟨first, atFirst, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    firstIdentityCode identities_checked.1
  obtain ⟨second, atSecond, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    secondIdentityCode identities_checked.2
  refine ⟨first, second, atFirst, atSecond, ?_⟩
  intro env
  exact identity_qualified_search_endpoints_coherent
    (interpretHead h seed ground valuation) constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h seed ground valuation groundTyped)
    (empty_constants_model _ constants) .nil firstIdentityCode secondIdentityCode
    functionLevel functionLevel functionFormation nestedFunctionCode computedFunctionCode
    functionFormation computedFunctionCode identityCode .hole .hole
    identityCode identityCode identityCode identityCode
    3 2 2 1 nested_search_endpoint (by rfl) (by rfl) (by rfl)
    (valid := fun _ => True) rfl rfl identities_checked.1 identities_checked.2
    rfl rfl first second atFirst atSecond env True.intro

/-- The equality is not between empty fibres: both checked identity types
contain the empty-set proof code in every closed environment. -/
theorem computed_identity_fibres_inhabited
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ first second,
      assemble (interpretHead h seed ground valuation) constants firstIdentityCode
        firstIdentity (.head functionLevel) = some first ∧
      assemble (interpretHead h seed ground valuation) constants secondIdentityCode
        secondIdentity (.head functionLevel) = some second ∧
      ∀ env : Environment.{u} 0, ∅ ∈ first.value env ∧ ∅ ∈ second.value env := by
  obtain ⟨first, second, atFirst, atSecond, equal⟩ :=
    computed_identity_fibres_agree h seed ground valuation groundTyped constants
  obtain ⟨computed, _, normal, atComputed, _, atNormal, computedEqual⟩ :=
    computed_functions_return_identity h seed ground valuation groundTyped constants
  obtain ⟨left, right, atLeft, atRight, secondValue⟩ :=
    assemble_identity_endpoints (interpretHead h seed ground valuation) constants
      secondIdentityCode functionType computedFunction identity (.head functionLevel)
      functionLevel functionFormation computedFunctionCode identityCode .hole second rfl atSecond
  rw [atComputed] at atLeft
  cases Option.some.inj atLeft
  rw [atNormal] at atRight
  cases Option.some.inj atRight
  refine ⟨first, second, atFirst, atSecond, ?_⟩
  intro env
  have secondMember : ∅ ∈ second.value env := by
    rw [secondValue]
    exact (ZFSetTraceProofDecoding.mem_truthCode _ ∅).mpr
      ⟨rfl, (computedEqual env).1⟩
  exact ⟨(equal env).symm ▸ secondMember, secondMember⟩

#print axioms identities_checked
#print axioms identity_subjects_differ
#print axioms lambda_terminal_requires_certificate
#print axioms computed_identity_fibres_agree
#print axioms computed_identity_fibres_inhabited

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedIdentityPathControls
