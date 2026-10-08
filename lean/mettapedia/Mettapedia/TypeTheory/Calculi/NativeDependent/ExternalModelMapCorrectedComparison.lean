import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapContextComparison
import Mettapedia.TypeTheory.ContextualCorrectedBaseLift

/-!
# Corrected comparison of generated dependent model maps

The context isomorphism comes from earned source evaluation and actual raw
context presentations. Its cartesian lift constructs the full displayed cell,
including naturality and the corrected comprehension square. The inverse is
also a genuine corrected cell. Unique classifying cells require their local
primitive and logical admission conditions, separately from this existence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualCorrectedBaseLift

universe u
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{u, u, u, u}} {target : ModelData S C}
variable (headers : HeaderFormation D)
  (first second : ModelMap (SyntacticModel.data headers) target)

/-- Reintroducing the CwF context wrapper retains the actual components
and all substitution naturality of the syntactic comparison. -/
noncomputable def baseIso : first.morphism.toPseudo.base ≅ second.morphism.toPseudo.base :=
  NatIso.ofComponents (fun Γ => (contextIso headers first second).app Γ.val)
    (fun {_Γ _Δ} arrow => contextIso_naturality headers first second arrow)

/-- Both displayed directions and their inverse equations are earned by
cartesian factorization and actual corrected-cell composition. -/
noncomputable def correctedIso : first.morphism.toPseudo ≅ second.morphism.toPseudo :=
  ContextualCorrectedBaseLift.liftIso (baseIso headers first second)

@[simp] theorem correctedIso_base_component
    (Γ : (QuotientCwf.cwf D).base.Context) :
    (correctedIso headers first second).hom.base.app Γ =
      (contextIso headers first second).hom.app Γ.val := rfl

/-- The complete corrected comprehension equation holds at every supplied
source family, including families formed by dependent products and sums. -/
theorem correctedIso_comprehension (Γ : (QuotientCwf.cwf D).Ctx)
    (A : Mettapedia.GSLT.Core.ContextualLadder.TypeOver (QuotientCwf.cwf D) Γ) :
    (first.morphism.toPseudo.comprehensionIso Γ A.val).hom ≫
        ((correctedIso headers first second).hom.family Γ A).substitution ≫
          TypeOver.extensionSubstitution ((correctedIso headers first second).hom.base.app ⟨Γ⟩)
            (second.morphism.toPseudo.mapType A.val) =
      (correctedIso headers first second).hom.base.app ⟨(QuotientCwf.cwf D).ext Γ A.val⟩ ≫
        (second.morphism.toPseudo.comprehensionIso Γ A.val).hom :=
  (correctedIso headers first second).hom.comprehension_coherence Γ A

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ModelMapComparison
