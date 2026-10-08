import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementModelMapContextComparison
import Mettapedia.TypeTheory.ContextualCorrectedBaseLift

/-!
# Corrected display comparison of generated refinement interpretations

The actual context isomorphism lifts by earned cartesian factorization to a
complete corrected contextual cell. Its family naturality and comprehension
square cover every supplied source family, including dependent refinements.
The inverse has the same complete coherence. Declaration-admitted uniqueness
is a subsequent theorem, rather than a premise of this construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateModel
open Refinement.Abstract

universe u z p
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}
  {targetModel : LocalModel.{max u z,max u z,max u z,max u z,p} C}
  {target : ModelData S C targetModel}
variable (headers : HeaderFormation D)
  (first second : ModelMap (Interpretation.sourceData.{u,z} headers) target)

noncomputable def baseIso : first.morphism.toPseudo.base ≅ second.morphism.toPseudo.base :=
  NatIso.ofComponents (fun Γ => (contextIso headers first second).app Γ.val.down)
    (fun {_Γ _Δ} arrow => contextIso_naturality headers first second arrow.down)

noncomputable def correctedIso : first.morphism.toPseudo ≅ second.morphism.toPseudo :=
  Mettapedia.TypeTheory.ContextualCorrectedBaseLift.liftIso (baseIso headers first second)

@[simp] theorem correctedIso_base_component
    (Γ : (Interpretation.SourceModel.{u,z} D).toCwf.base.Context) :
    (correctedIso headers first second).hom.base.app Γ =
      (contextIso headers first second).hom.app Γ.val.down := rfl

theorem correctedIso_comprehension (Γ : (Interpretation.SourceModel.{u,z} D).toCwf.Ctx)
    (A : Mettapedia.GSLT.Core.ContextualLadder.TypeOver
      (Interpretation.SourceModel.{u,z} D).toCwf Γ) :
    (first.morphism.toPseudo.comprehensionIso Γ A.val).hom ≫
        ((correctedIso headers first second).hom.family Γ A).substitution ≫
          TypeOver.extensionSubstitution ((correctedIso headers first second).hom.base.app ⟨Γ⟩)
            (second.morphism.toPseudo.mapType A.val) =
      (correctedIso headers first second).hom.base.app
        ⟨(Interpretation.SourceModel.{u,z} D).toCwf.ext Γ A.val⟩ ≫
        (second.morphism.toPseudo.comprehensionIso Γ A.val).hom :=
  (correctedIso headers first second).hom.comprehension_coherence Γ A

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison
