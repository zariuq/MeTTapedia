import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentCwfMorphism
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentErasureBoundary
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.CwfInhabitationInstitution
import Mettapedia.TypeTheory.GlobalPointReduct

/-!
# The model-reduct obstruction for raw simple syntax

The strict CwF morphism preserves satisfaction at translated global points.
An institution comorphism with this signature functor would additionally
require a natural reduct of all target global points. Naturality at closed
substitutions would recover each source point, contradicting the loss of
intrinsic typing information proved by the erasure collision.

The obstruction fixes both raw context categories and their signature functor.
It does not refute conservativity of typing or comparisons after quotienting
conversion, and it does not concern the separate constant-family semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SimpleFragmentInstitutionBoundary

open _root_.CategoryTheory Opposite
open scoped _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open FourFaceBetaExperiment.IntrinsicSTT
open SimpleFragmentCwfMorphism SimpleFragmentErasureBoundary
open Presentation


abbrev SourceContext := syntacticCwfWithTerminal.toCwf.base.Context
abbrev TargetContext := CwfInhabitationInstitution.towerCwf.toCwf.base.Context

def sourceEmpty : SourceContext := ⟨[]⟩
def targetEmpty : TargetContext := contextFunctor.obj sourceEmpty

instance : Subsingleton (sourceEmpty ⟶ sourceEmpty) where
  allEq left right := by
    funext A v
    exact nomatch v

/-- A closed intrinsic term is a global substitution into its singleton context. -/
def closedPoint {A : Ty} (t : Term [] A) : sourceEmpty ⟶ (⟨[A]⟩ : SourceContext) :=
  Substitution.extend (Substitution.id []) t

theorem closedPoints_ne :
    @closedPoint (.arr .atom .atom) discardAtomicIdentity ≠
      @closedPoint (.arr .atom .atom) discardFunctionIdentity := by
  intro equal
  exact discardIdentities_ne (congrArg (fun σ => σ Var.zero) equal)

theorem mapped_closedPoints_eq :
    contextFunctor.map (closedPoint discardAtomicIdentity) =
      contextFunctor.map (closedPoint discardFunctionIdentity) := by
  apply SyntacticContextual.ContextHom.ext
  funext index
  refine Fin.cases ?_ (fun i => Fin.elim0 i) index
  exact erase_discardIdentities_eq

/-- Naturality alone rules out a reverse map of global-point functors. -/
theorem no_globalPointReduct :
    ¬ Nonempty (contextFunctor ⋙ coyoneda.obj (op targetEmpty) ⟶
      coyoneda.obj (op sourceEmpty)) := by
  apply Mettapedia.TypeTheory.GlobalPointReduct.no_reduct_of_collision
    (𝟙 targetEmpty) (closedPoint discardAtomicIdentity)
    (closedPoint discardFunctionIdentity) closedPoints_ne
  rw [mapped_closedPoints_eq]

abbrev simpleInstitution :=
  Mettapedia.TypeTheory.CwfInhabitationInstitution.ofCwf syntacticCwfWithTerminal

/-- Read the object action of a model reduct as a map of global points. -/
def pointReductOfModelReduct
    (reduct : contextFunctor.op.op ⋙ CwfInhabitationInstitution.towerInstitution.model ⟶
      simpleInstitution.model) :
    contextFunctor ⋙ coyoneda.obj (op targetEmpty) ⟶ coyoneda.obj (op sourceEmpty) where
  app Γ := TypeCat.ofHom fun point =>
    ((reduct.app (op (op Γ))).toFunctor.obj (Discrete.mk point)).as
  naturality := by
    intro Γ Δ σ
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext point
    have natural := reduct.naturality (Quiver.Hom.op (Quiver.Hom.op σ))
    exact congrArg
      (fun map : (contextFunctor.op.op ⋙ CwfInhabitationInstitution.towerInstitution.model).obj
          (op (op Γ)) ⟶ simpleInstitution.model.obj (op (op Δ)) =>
        @Discrete.as (Substitution Δ.val [])
          (map.toFunctor.obj (Discrete.mk point))) natural

/-- There is no institution comorphism over this raw erasure functor,
regardless of the proposed sentence translation. -/
theorem no_comorphism_over_erasure :
    ¬ ∃ route : Mettapedia.Logic.Institution.Comorphism simpleInstitution
        CwfInhabitationInstitution.towerInstitution,
      route.mapSignature = contextFunctor.op := by
  rintro ⟨route, signature⟩
  have reduct := route.mapModel
  rw [signature] at reduct
  exact no_globalPointReduct ⟨pointReductOfModelReduct reduct⟩

/-- The forward CwF map still preserves satisfaction at every translated point. -/
theorem satisfaction_preserved (Γ : List Ty) (point : Substitution Γ []) (A : Ty)
    (satisfied : simpleInstitution.satisfies (op ⟨Γ⟩) (Discrete.mk point) A) :
    CwfInhabitationInstitution.towerInstitution.satisfies
      (contextFunctor.op.obj (op ⟨Γ⟩)) (Discrete.mk (mapSubstitution point))
      (simpleType (mapContext Γ) A) := by
  obtain ⟨term⟩ := satisfied
  change Nonempty (SyntacticContextual.Term (mapContext [])
    ((simpleType (mapContext Γ) A).reindex (mapSubstitution point)))
  rw [simpleType_reindex]
  exact ⟨mapTerm term⟩

#print axioms closedPoints_ne
#print axioms mapped_closedPoints_eq
#print axioms no_globalPointReduct
#print axioms no_comorphism_over_erasure
#print axioms satisfaction_preserved

end SimpleFragmentInstitutionBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
