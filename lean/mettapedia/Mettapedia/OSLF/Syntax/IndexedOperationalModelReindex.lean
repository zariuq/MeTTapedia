import Mettapedia.OSLF.Syntax.IndexedOperationalModelsOver
import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationTransport
import Mathlib.CategoryTheory.Equivalence

/-!
# Reindexing proof-relevant operational models

An authored presentation can vary over a category of binding/equation
models. Changing that base category along a functor retains the exact
rule algebra and its firing witnesses. Fullness and faithfulness of the
base change lift to the operational model categories without imposing
coverage or reflection on individual events.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Mettapedia.OSLF.Binding.IndexedOperationalModelsOver

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

universe uBase uIndex uShape uPosition uC vC uD vD

variable {Base : Type uBase}
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (P : C ⥤ Presentation.{uBase, uIndex, uShape, uPosition} Base)
variable (F : D ⥤ C)

/-- Reindex a presentation-dependent operational model along a change of
its authored base category, retaining its individual evidence algebra. -/
noncomputable def reindexFunctor : Model (F ⋙ P) ⥤ Model P where
  obj X :=
    { base := F.obj X.base
      evidence := X.evidence }
  map f :=
    { base := F.map f.base
      evidence := f.evidence
      presentationEq := by
        change f.evidence.presentation = P.map (F.map f.base)
        exact f.presentationEq }
  map_id := by
    intro X
    apply Hom.ext P
    · exact F.map_id X.base
    · rfl
  map_comp := by
    intro X Y Z f g
    apply Hom.ext P
    · exact F.map_comp f.base g.base
    · rfl

/-- The reindexing operation commutes exactly with forgetting the
operational algebra. -/
theorem reindexFunctor_forget :
    reindexFunctor P F ⋙ forget P =
      forget (F ⋙ P) ⋙ F := by
  rfl

/-- Freely generating rule trees commutes with a change of the authored
base interpretation. This connects the two adjunctions on the nose. -/
theorem freeFunctor_reindex :
    F ⋙ freeFunctor P =
      freeFunctor (F ⋙ P) ⋙ reindexFunctor P F := by
  rfl

/-- Reindexing along the identity authored interpretation changes neither
the base model nor any operational evidence map. -/
theorem reindexFunctor_id :
    reindexFunctor P (𝟭 C) = 𝟭 (Model P) := by
  rfl

/-- Successive changes of authored base are coherent: the corresponding
changes of proof-relevant rule models compose on both objects and maps. -/
theorem reindexFunctor_comp
    {E : Type*} [Category E] (H : E ⥤ D) :
    reindexFunctor P (H ⋙ F) =
      reindexFunctor (F ⋙ P) H ⋙ reindexFunctor P F := by
  rfl

/-- If base interpretations distinguish maps, so do their operational
extensions: the evidence map is kept verbatim. -/
instance reindexFunctor_faithful [F.Faithful] :
    (reindexFunctor P F).Faithful where
  map_injective := by
    intro X Y f g equal
    apply Hom.ext (F ⋙ P)
    · exact F.map_injective (congrArg Hom.base equal)
    · exact congrArg
        (fun h : Hom P ((reindexFunctor P F).obj X)
          ((reindexFunctor P F).obj Y) => h.evidence) equal

/-- Every operational map over a base map in the image of `F` has a unique
preimage once `F` is full. No target-step coverage is required. -/
instance reindexFunctor_full [F.Full] :
    (reindexFunctor P F).Full where
  map_surjective := by
    intro X Y f
    let pre := F.preimage f.base
    let lifted : Hom (F ⋙ P) X Y :=
      { base := pre
        evidence := f.evidence
        presentationEq := by
          have hPre : F.map pre = f.base := F.map_preimage f.base
          have hP : P.map (F.map pre) = P.map f.base :=
            congrArg P.map hPre
          change f.evidence.presentation = P.map (F.map pre)
          exact f.presentationEq.trans hP.symm }
    refine ⟨lifted, ?_⟩
    apply Hom.ext P
    · exact F.map_preimage f.base
    · rfl

/-- Freely generated operational models detect every missing base map.
Consequently, reindexing is full exactly when the underlying change of
authored base models is full. -/
theorem reindexFunctor_full_iff :
    (reindexFunctor P F).Full ↔ F.Full := by
  constructor
  · intro hFull
    refine ⟨?_⟩
    intro a b f
    let source := free (F ⋙ P) a
    let target := free (F ⋙ P) b
    let lifted : (reindexFunctor P F).obj source ⟶
        (reindexFunctor P F).obj target := freeMap P f
    obtain ⟨g, hg⟩ := hFull.map_surjective lifted
    exact ⟨g.base, congrArg
      (fun h : Hom P ((reindexFunctor P F).obj source)
        ((reindexFunctor P F).obj target) => h.base) hg⟩
  · intro hFull
    let baseFull : F.Full := hFull
    infer_instance

/-- Free rule trees also detect every collapse of distinct base maps.
Operational evidence does not repair a nonfaithful change of base. -/
theorem reindexFunctor_faithful_iff :
    (reindexFunctor P F).Faithful ↔ F.Faithful := by
  constructor
  · intro hFaithful
    refine ⟨?_⟩
    intro a b f g same
    let source := free (F ⋙ P) a
    let target := free (F ⋙ P) b
    have sameOperational :
        (reindexFunctor P F).map (freeMap (F ⋙ P) f) =
          (reindexFunctor P F).map (freeMap (F ⋙ P) g) := by
      apply Hom.ext P
      · exact same
      · change
          Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory.freeMap
            (P.map (F.map f)) =
          Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory.freeMap
            (P.map (F.map g))
        exact congrArg
          Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory.freeMap
          (congrArg P.map same)
    have recovered := hFaithful.map_injective sameOperational
    exact congrArg
      (fun h : Hom (F ⋙ P) source target => h.base) recovered
  · intro hFaithful
    let baseFaithful : F.Faithful := hFaithful
    infer_instance

/-- An operational reindexing cannot become essentially surjective if
the underlying base interpretation misses an object up to isomorphism.
Free rule-tree models witness the obstruction. -/
theorem reindexFunctor_essSurj_implies_base
    (hEss : (reindexFunctor P F).EssSurj) : F.EssSurj := by
  refine ⟨?_⟩
  intro A
  obtain ⟨X, ⟨iso⟩⟩ := hEss.mem_essImage (free P A)
  exact ⟨X.base, ⟨(forget P).mapIso iso⟩⟩

/-- On-the-nose object coverage lifts directly to operational models:
there is no additional obstruction from the rule algebra. -/
theorem reindexFunctor_essSurj_of_surjective_obj
    (onto : Function.Surjective F.obj) :
    (reindexFunctor P F).EssSurj := by
  refine ⟨?_⟩
  intro X
  cases X with
  | mk base evidence =>
      obtain ⟨pre, rfl⟩ := onto base
      exact ⟨{ base := pre, evidence := evidence }, ⟨Iso.refl _⟩⟩

/-- Essential surjectivity of the authored base comparison lifts to the
proof-relevant operational layer. An isomorphism of base interpretations
induces an isomorphism of rule presentations; pulling the target rule
algebra back along it supplies the required source model. -/
noncomputable instance reindexFunctor_essSurj [F.EssSurj] :
    (reindexFunctor P F).EssSurj where
  mem_essImage X := by
    let A : D := F.objPreimage X.base
    let e : F.obj A ≅ X.base := F.objObjPreimageIso X.base
    let pe : P.obj (F.obj A) ≅ P.obj X.base := P.mapIso e
    let pulled := pullbackEquipped (X.equipped P) pe.hom
    let Y : Model (F ⋙ P) :=
      { base := A, evidence := pulled.model }
    let evidenceIso := pullbackEquippedIso (X.equipped P) pe
    let modelIso : (reindexFunctor P F).obj Y ≅ X :=
      { hom := { base := e.hom
                 evidence := evidenceIso.hom
                 presentationEq := rfl }
        inv := { base := e.inv
                 evidence := evidenceIso.inv
                 presentationEq := by
                   exact pullbackEquippedReverse_presentation (X.equipped P) pe }
        hom_inv_id := by
          apply Hom.ext P
          · exact e.hom_inv_id
          · exact evidenceIso.hom_inv_id
        inv_hom_id := by
          apply Hom.ext P
          · exact e.inv_hom_id
          · exact evidenceIso.inv_hom_id }
    exact ⟨Y, ⟨modelIso⟩⟩

/-- A categorical equivalence of authored models remains an equivalence
when every model is equipped with an algebra of individual rule firings.
The equivalence transports the actions and witnesses, rather than
identifying firings with their endpoint relation. -/
noncomputable instance reindexFunctor_isEquivalence [F.IsEquivalence] :
    (reindexFunctor P F).IsEquivalence where

/-- The equivalence of operational models induced by a base equivalence. -/
noncomputable def reindexEquivalence [F.IsEquivalence] :
    Model (F ⋙ P) ≌ Model P :=
  (reindexFunctor P F).asEquivalence

/-- Equipping authored models with freely varying proof-relevant rule
algebras neither creates nor destroys an equivalence of their base
interpretation categories. The reverse direction is detected by the
free rule-tree models. -/
theorem reindexFunctor_isEquivalence_iff :
    (reindexFunctor P F).IsEquivalence ↔ F.IsEquivalence := by
  constructor
  · intro operational
    have full : (reindexFunctor P F).Full := operational.full
    have faithful : (reindexFunctor P F).Faithful := operational.faithful
    have essSurj : (reindexFunctor P F).EssSurj := operational.essSurj
    exact ⟨(reindexFunctor_faithful_iff P F).mp faithful,
      (reindexFunctor_full_iff P F).mp full,
      reindexFunctor_essSurj_implies_base P F essSurj⟩
  · intro base
    exact @reindexFunctor_isEquivalence Base C _ D _ P F base

end Mettapedia.OSLF.Binding.IndexedOperationalModelsOver
