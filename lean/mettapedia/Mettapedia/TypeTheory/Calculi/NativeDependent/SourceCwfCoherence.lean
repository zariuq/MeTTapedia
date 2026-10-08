import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfSubstitution

/-!
# Full source display-map recovery in generated native families

Complete native maps between generated source type declarations have unique
source display-map origins. This morphism correspondence commutes with the
same substitution comparison used for generated terms. Comprehension keeps
the source extension and its actual projection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open NativeLocalTypeFormers ContextualModelTelescopes

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

def sourceFamilyMap {context : K.Ctx} {first second : TypeOver K context}
    (arrow : first ⟶ second) : sourceFamily first.val ⟶ sourceFamily second.val :=
  Functor.whiskerLeft (objectName (⟨context⟩ : Base K)).mapElements (CwfYoneda.familyMap K arrow)

def originalFamilyMap {context : K.Ctx} {first second : TypeOver K context}
    (map : sourceFamily first.val ⟶ sourceFamily second.val) :
    CwfYoneda.family K first.val ⟶ CwfYoneda.family K second.val where
  app point := map.app ((objectNameInverse (⟨context⟩ : Base K)).mapElements.obj point)
  naturality _ _ change := map.naturality ((objectNameInverse (⟨context⟩ : Base K)).mapElements.map change)

theorem original_source_family_map {context : K.Ctx} {first second : TypeOver K context}
    (arrow : first ⟶ second) :
    originalFamilyMap (sourceFamilyMap arrow) = CwfYoneda.familyMap K arrow := by
  ext point receipt
  rfl

theorem source_original_family_map {context : K.Ctx} {first second : TypeOver K context}
    (map : sourceFamily first.val ⟶ sourceFamily second.val) :
    Functor.whiskerLeft (objectName (⟨context⟩ : Base K)).mapElements (originalFamilyMap map) = map := by
  ext point receipt
  rcases point with ⟨world, singleton, environment⟩
  cases singleton
  rfl

def recoverSourceFamilyMap {context : K.Ctx} {first second : TypeOver K context}
    (map : sourceFamily first.val ⟶ sourceFamily second.val) : first ⟶ second :=
  CwfYoneda.recoverFamilyMap K (originalFamilyMap map)

theorem recover_source_family_map {context : K.Ctx} {first second : TypeOver K context}
    (arrow : first ⟶ second) : recoverSourceFamilyMap (sourceFamilyMap arrow) = arrow := by
  unfold recoverSourceFamilyMap
  rw [original_source_family_map, CwfYoneda.recoverFamilyMap_familyMap]

theorem source_family_map_recover {context : K.Ctx} {first second : TypeOver K context}
    (map : sourceFamily first.val ⟶ sourceFamily second.val) :
    sourceFamilyMap (recoverSourceFamilyMap map) = map := by
  unfold sourceFamilyMap recoverSourceFamilyMap
  rw [CwfYoneda.familyMap_recoverFamilyMap]
  exact source_original_family_map map

def sourceFamilyFunctor (context : K.Ctx) :
    TypeOver K context ⥤ DisplayedFamily (objectScope (⟨context⟩ : Base K)).1 where
  obj type := sourceFamily type.val
  map := sourceFamilyMap
  map_id type := by
    ext point receipt
    apply Subtype.ext
    exact K.id_comp receipt.val
  map_comp first second := by
    ext point receipt
    apply Subtype.ext
    exact K.comp_assoc second.substitution first.substitution receipt.val

/-- Every complete native map comes from a unique original source display map. -/
def sourceFamilyFullyFaithful (context : K.Ctx) : (sourceFamilyFunctor (K := K) context).FullyFaithful where
  preimage := recoverSourceFamilyMap
  map_preimage := source_family_map_recover
  preimage_map := recover_source_family_map

theorem source_substitution_naturality {context replacement : K.Ctx}
    (before : K.Sub replacement context) {first second : TypeOver K context}
    (arrow : first ⟶ second) :
    sourceFamilyMap (TypeOver.reindexArrow before arrow) ≫
        (sourceSubstitutionIso second.val before).hom =
      (sourceSubstitutionIso first.val before).hom ≫
        Functor.whiskerLeft (originalMap
          (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from before)).mapElements
          (sourceFamilyMap arrow) := by
  ext point receipt
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (CwfYoneda.substitutionIso_naturality K before arrow)
    ((objectName (⟨replacement⟩ : Base K)).mapElements.obj point)) receipt

def sourceSubstitutionNaturalIso {context replacement : K.Ctx}
    (before : K.Sub replacement context) :
    TypeOver.reindexFunctor before ⋙ sourceFamilyFunctor replacement ≅
      sourceFamilyFunctor context ⋙ (Functor.whiskeringLeft _ _ _).obj
        (originalMap (show (⟨replacement⟩ : Base K) ⟶ ⟨context⟩ from before)).mapElements :=
  NatIso.ofComponents (fun type => sourceSubstitutionIso type.val before)
    (fun arrow => source_substitution_naturality before arrow)

def sourceComprehensionIso {context : K.Ctx} (type : K.Ty context) :
    (sourceScope type).1 ≅ yoneda.obj (⟨K.ext context type⟩ : Base K) :=
  RepresentableIndexedDeclarations.fibreScopeIso (displayArrow type)

theorem source_comprehension_projection {context : K.Ctx} (type : K.Ty context) :
    (sourceComprehensionIso type).hom ≫
        yoneda.map (show (⟨K.ext context type⟩ : Base K) ⟶ ⟨context⟩ from K.wk type) =
      (NativeModel (Base K)).toCwf.wk (sourceMeaning type) ≫
        objectName (⟨context⟩ : Base K) :=
  RepresentableIndexedDeclarations.comprehension_projection (displayArrow type)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
