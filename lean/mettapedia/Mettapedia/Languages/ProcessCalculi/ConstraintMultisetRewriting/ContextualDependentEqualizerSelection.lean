import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalEqualizer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentVariableFactorization

/-!
# Computed dependent equalizers of parameter maps

The mask retains exactly the indices at which two maps agree. Exact
declaration compatibility proves that this mask retains its dependencies.
Normal context selection therefore computes a typed equalizer. Typed equality
of two normal instances of one endpoint forces both its value and annotation
through that equalizer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEqualizerSelection

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentTypedInversion ContextualDependentEta
open ContextualDependentNormalSelection ContextualDependentRenameAgreement

def mask {n m : Nat} (first second : Ren n m) (index : Fin n) : Bool := decide (first index = second index)

theorem mask_iff {n m : Nat} (first second : Ren n m) (index : Fin n) :
    mask first second index = true ↔ first index = second index := by simp [mask]

theorem mask_closed {Head : Type} {n m : Nat} {source : Ctx Head n} {target : Ctx Head m}
    (first second : Ren n m) (firstCompatible : CtxRen source target first) (secondCompatible : CtxRen source target second) :
    Closed source (mask first second) := by
  intro index retained dependency present
  have same := (mask_iff first second index).mp retained
  have types : Presentation.rename first (Ctx.lookup source index) = Presentation.rename second (Ctx.lookup source index) := by
    rw [← firstCompatible, ← secondCompatible, same]
  exact (mask_iff first second dependency).mpr ((rename_eq_iff_agrees _ first second).mp types dependency present)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem selected_equalizes {source : Context S.R} {m : Nat} (first second : Ren source.arity m)
    (selected : Selected source (mask first second)) (index : Fin selected.source.arity) :
    first (selected.inclusion.forward index) = second (selected.inclusion.forward index) :=
  (mask_iff first second _).mp ((selected.image _).mp ⟨index, rfl⟩)

def factor {source other : Context S.R} {m : Nat} (first second : Ren source.arity m)
    (selected : Selected source (mask first second)) (cone : Inclusion other source)
    (compatible : CtxRen other.raw source.raw cone.forward)
    (equalizes : ∀ index, first (cone.forward index) = second (cone.forward index)) : Inclusion other selected.source :=
  ContextualDependentVariableFactorization.inclusion selected.inclusion cone
    (fun index => (selected.image _).mpr ((mask_iff first second _).mpr (equalizes index))) selected.compatible compatible

theorem factor_image {source other : Context S.R} {m : Nat} (first second : Ren source.arity m)
    (selected : Selected source (mask first second)) (cone : Inclusion other source)
    (compatible : CtxRen other.raw source.raw cone.forward)
    (equalizes : ∀ index, first (cone.forward index) = second (cone.forward index)) (index : Fin other.arity) :
    selected.inclusion.forward ((factor first second selected cone compatible equalizes).forward index) = cone.forward index :=
  ContextualDependentVariableFactorization.factor_image selected.inclusion.forward cone.forward
    (fun position => (selected.image _).mpr ((mask_iff first second _).mpr (equalizes position))) index

theorem factor_unique {source other : Context S.R} {m : Nat} (first second : Ren source.arity m)
    (selected : Selected source (mask first second)) (cone : Inclusion other source)
    (compatible : CtxRen other.raw source.raw cone.forward)
    (equalizes : ∀ index, first (cone.forward index) = second (cone.forward index))
    (candidate : Ren other.arity selected.source.arity)
    (image : ∀ index, selected.inclusion.forward (candidate index) = cone.forward index) :
    candidate = (factor first second selected cone compatible equalizes).forward :=
  ContextualDependentVariableFactorization.factor_unique selected.inclusion.forward cone.forward
    (fun position => (selected.image _).mpr ((mask_iff first second _).mpr (equalizes position)))
    selected.inclusion.injective candidate image

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)

def selectEqualizer {source target : Context S.R} (first second : Inclusion source target)
    (firstCompatible : CtxRen source.raw target.raw first.forward) (secondCompatible : CtxRen source.raw target.raw second.forward)
    (normal : NormalContext (S := S) source.raw) : Selected source (mask first.forward second.forward) :=
  (ContextualDependentNormalSelection.select facts roots heads algebra headTypingUnique complete declared reflects
    source.raw source.formed normal (mask first.forward second.forward)).get
      (select_of_closed facts roots heads algebra headTypingUnique complete declared reflects source.raw source.formed normal _
        (mask_closed first.forward second.forward firstCompatible secondCompatible))

variable (rigid : ∀ name, S.roles name = .rigid)

include complete rigid in
theorem endpoint_forces_mask {source target : Context S.R} (first second : Inclusion source target)
    (endpoint : TotalTerm source)
    (same : (frames S.levels).E (endpoint.reindex first.hom) (endpoint.reindex second.hom))
    (typeNormal : Normal (S := S) endpoint.1.code) (valueNormal : Normal (S := S) endpoint.2.code) :
    ∀ index ∈ endpoint.1.code.support ∪ endpoint.2.code.support, mask first.forward second.forward index = true := by
  have types := same.1
  have values := same.2
  change TypeEq S.R target.raw (subst (renSub first.forward) endpoint.1.code)
    (subst (renSub second.forward) endpoint.1.code) at types
  change Equal S.R target.raw (subst (renSub first.forward) endpoint.2.code)
    (subst (renSub second.forward) endpoint.2.code) (subst (renSub first.forward) endpoint.1.code) at values
  simp only [subst_renSub] at types values
  have typeAgreement := ContextualDependentNormalEqualizer.typeEq_agreement rigid complete target.formed
    endpoint.1.code first.forward second.forward types typeNormal
  have valueAgreement := ContextualDependentNormalEqualizer.equal_agreement rigid complete target.formed
    endpoint.2.code first.forward second.forward values valueNormal
  intro index present
  apply (mask_iff first.forward second.forward index).mpr
  rcases Finset.mem_union.mp present with present | present
  · exact typeAgreement index present
  · exact valueAgreement index present

def recoverEqualizer {source target : Context S.R} (first second : Inclusion source target)
    (firstCompatible : CtxRen source.raw target.raw first.forward) (secondCompatible : CtxRen source.raw target.raw second.forward)
    (contextNormal : NormalContext (S := S) source.raw) (endpoint : TotalTerm source)
    (same : (frames S.levels).E (endpoint.reindex first.hom) (endpoint.reindex second.hom))
    (typeNormal : Normal (S := S) endpoint.1.code) (valueNormal : Normal (S := S) endpoint.2.code) :
    let selected := selectEqualizer facts roots heads algebra headTypingUnique complete declared
      (ContextualDependentScopeConsequence.root_reflection rigid) first second firstCompatible secondCompatible contextNormal
    ContextualDependentEndpointInversion.Recovered selected.inclusion endpoint :=
  let selected := selectEqualizer facts roots heads algebra headTypingUnique complete declared
    (ContextualDependentScopeConsequence.root_reflection rigid) first second firstCompatible secondCompatible contextNormal
  (ContextualDependentEndpointInversion.recover facts roots heads algebra headTypingUnique complete declared
    (ContextualDependentScopeConsequence.root_reflection rigid) selected.inclusion selected.compatible endpoint typeNormal valueNormal).get (by
      apply (ContextualDependentEndpointInversion.success_iff_support facts roots heads algebra headTypingUnique complete declared
        (ContextualDependentScopeConsequence.root_reflection rigid) selected.inclusion selected.compatible endpoint typeNormal valueNormal).mpr
      intro index present
      exact (selected.image index).mpr (endpoint_forces_mask complete rigid first second endpoint same typeNormal valueNormal index present))

end ContextualDependentEqualizerSelection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
