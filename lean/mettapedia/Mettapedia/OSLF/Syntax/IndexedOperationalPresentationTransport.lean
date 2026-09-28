import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationCategory

/-!
# Reindexing operational evidence along a presentation map

A cartesian map of scoped-rule presentations can pull a semantic rule
algebra back to the source presentation. The resulting map to the
original model retains every recursive premise input and its action.
This is the object-transport operation needed when a context classifier
changes the chosen presentation without changing the authored rule.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedRuleAlgebraPullback

universe uBase uIndex uShape uPosition

variable {Base : Type uBase}
variable {P : Presentation.{uBase, uIndex, uShape, uPosition} Base}
variable (X : Equipped.{uBase, uIndex, uShape, uPosition} Base)
variable (h : P ⟶ X.presentation)

/-- Pull a rule algebra back along an exact map of rule presentations.
The target's evidence carrier is indexed by the mapped source judgment. -/
noncomputable def pullbackEquipped : Equipped.{uBase, uIndex, uShape, uPosition} Base where
  presentation := P
  model :=
    { carrier := fun b i => X.model.carrier b (h.judgment b i)
      rules := IndexedRuleAlgebraPullback.pullback h.rules X.model.rules }

/-- The reindexed algebra maps to its original interpretation. Its
individual evidence values are unchanged, and preservation of each
constructor action follows from the polynomial pullback law. -/
noncomputable def pullbackEquippedMap :
    Equipped.Map (pullbackEquipped X h) X where
  presentation := h
  toFun := fun _ _ value => value
  preserves := by
    intro b i layer
    rfl

/-- Reindexing along the identity presentation map leaves the entire
semantic rule algebra unchanged. -/
theorem pullbackEquipped_id :
    pullbackEquipped X (𝟙 X.presentation) = X := by
  cases X with
  | mk presentation model =>
      cases model
      rfl

/-- Pulling a rule algebra back in two stages agrees with pulling it back
along the composite presentation map. This includes the recursive action,
not just the carrier family. -/
theorem pullbackEquipped_comp
    {Q : Presentation.{uBase, uIndex, uShape, uPosition} Base}
    (f : P ⟶ Q) (g : Q ⟶ X.presentation) :
    pullbackEquipped (pullbackEquipped X g) f =
      pullbackEquipped X (f ≫ g) := by
  dsimp [pullbackEquipped]
  change
    ({ presentation := P
       model :=
         { carrier := fun b i =>
             X.model.carrier b (g.judgment b (f.judgment b i))
           rules := pullback f.rules (pullback g.rules X.model.rules) } } :
       Equipped Base) =
    ({ presentation := P
       model :=
         { carrier := fun b i =>
             X.model.carrier b (g.judgment b (f.judgment b i))
           rules := pullback (f.rules.comp g.rules) X.model.rules } } :
       Equipped Base)
  rw [IndexedRuleAlgebraPullback.pullback_comp
    f.rules g.rules X.model.rules]

/-- Pulling an equipped presentation back along an isomorphism and then
along its inverse returns the original algebra. -/
theorem pullbackEquipped_iso_roundTrip
    (e : P ≅ X.presentation) :
    pullbackEquipped (pullbackEquipped X e.hom) e.inv = X := by
  rw [pullbackEquipped_comp, e.inv_hom_id, pullbackEquipped_id]

/-- The inverse direction also restores the pulled-back algebra. -/
theorem pullbackEquipped_iso_roundTrip_inv
    (e : P ≅ X.presentation) :
    pullbackEquipped
      (pullbackEquipped (pullbackEquipped X e.hom) e.inv) e.hom =
      pullbackEquipped X e.hom := by
  calc
    _ = pullbackEquipped (pullbackEquipped X e.hom)
          (e.hom ≫ e.inv) :=
      pullbackEquipped_comp (pullbackEquipped X e.hom) e.hom e.inv
    _ = pullbackEquipped X e.hom := by
      have changed := congrArg
        (fun f : P ⟶ P =>
          pullbackEquipped (P := P) (pullbackEquipped X e.hom) f)
        e.hom_inv_id
      exact changed.trans (pullbackEquipped_id (pullbackEquipped X e.hom))

/-- A map back to the pulled-back model along an isomorphism of rule
presentations. Algebra preservation comes from the ordinary pullback map
after transporting the twice-pulled-back model along its proved equality. -/
noncomputable def pullbackEquippedReverse
    (e : P ≅ X.presentation) :
    Equipped.Map X (pullbackEquipped X e.hom) :=
  eqToHom (pullbackEquipped_iso_roundTrip X e).symm ≫
    pullbackEquippedMap (pullbackEquipped X e.hom) e.inv

/-- The reverse algebra map lies over the inverse presentation map. -/
theorem pullbackEquippedReverse_presentation
    (e : P ≅ X.presentation) :
    (pullbackEquippedReverse X e).presentation = e.inv := by
  have eqmap : (forget (Base := Base)).map
      (eqToHom (pullbackEquipped_iso_roundTrip X e).symm) =
      𝟙 X.presentation := by
    rw [eqToHom_map]
    exact eqToHom_refl _ _
  change (forget (Base := Base)).map
      (pullbackEquippedReverse X e) = e.inv
  simp only [pullbackEquippedReverse, Functor.map_comp, eqmap]
  change 𝟙 X.presentation ≫ e.inv = e.inv
  simp

/-- Forward then reverse transport is the identity on the authored
presentation. The corresponding evidence-function equation is separate. -/
theorem pullbackEquipped_forward_reverse_presentation
    (e : P ≅ X.presentation) :
    (forget (Base := Base)).map
      (pullbackEquippedMap X e.hom ≫ pullbackEquippedReverse X e) =
        𝟙 P := by
  simp only [Functor.map_comp]
  change e.hom ≫ (pullbackEquippedReverse X e).presentation = 𝟙 P
  rw [pullbackEquippedReverse_presentation]
  exact e.hom_inv_id

/-- Reverse then forward transport is the identity on the target
presentation, before proving the corresponding evidence-function equation. -/
theorem pullbackEquipped_reverse_forward_presentation
    (e : P ≅ X.presentation) :
    (forget (Base := Base)).map
      (pullbackEquippedReverse X e ≫ pullbackEquippedMap X e.hom) =
        𝟙 X.presentation := by
  simp only [Functor.map_comp]
  change (pullbackEquippedReverse X e).presentation ≫ e.hom =
    𝟙 X.presentation
  rw [pullbackEquippedReverse_presentation]
  exact e.inv_hom_id

private theorem eqToHom_evidence_heq
    {Y : Equipped.{uBase, uIndex, uShape, uPosition} Base}
    (equal : X = Y) (b : Base) (j : X.presentation.Judgment b)
    (value : X.model.carrier b j) :
    (eqToHom equal : X ⟶ Y).toFun b j value ≍ value := by
  cases equal
  rfl

/-- Transport forward and back is the identity on both the rule
presentation and every individual evidence value. -/
theorem pullbackEquipped_forward_reverse
    (e : P ≅ X.presentation) :
    pullbackEquippedMap X e.hom ≫ pullbackEquippedReverse X e =
      𝟙 (pullbackEquipped X e.hom) := by
  apply Equipped.Map.ext_of_pointwise
    (pullbackEquipped_forward_reverse_presentation X e)
  intro b i value
  change (eqToHom (pullbackEquipped_iso_roundTrip X e).symm :
      X ⟶ pullbackEquipped (pullbackEquipped X e.hom) e.inv).toFun
        b (e.hom.judgment b i) value ≍ value
  exact eqToHom_evidence_heq X
    (pullbackEquipped_iso_roundTrip X e).symm b _ value

/-- Transport back and forward is also the identity on the target's
presentation and evidence algebra. -/
theorem pullbackEquipped_reverse_forward
    (e : P ≅ X.presentation) :
    pullbackEquippedReverse X e ≫ pullbackEquippedMap X e.hom =
      𝟙 X := by
  apply Equipped.Map.ext_of_pointwise
    (pullbackEquipped_reverse_forward_presentation X e)
  intro b i value
  change (eqToHom (pullbackEquipped_iso_roundTrip X e).symm :
      X ⟶ pullbackEquipped (pullbackEquipped X e.hom) e.inv).toFun
        b i value ≍ value
  exact eqToHom_evidence_heq X
    (pullbackEquipped_iso_roundTrip X e).symm b i value

/-- Isomorphic authored rule presentations carry isomorphic categories
of proof-relevant algebra interpretations. The constructed isomorphism
preserves the complete evidence carrier and all recursive rule actions. -/
noncomputable def pullbackEquippedIso
    (e : P ≅ X.presentation) :
    pullbackEquipped X e.hom ≅ X where
  hom := pullbackEquippedMap X e.hom
  inv := pullbackEquippedReverse X e
  hom_inv_id := pullbackEquipped_forward_reverse X e
  inv_hom_id := pullbackEquipped_reverse_forward X e

end Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory
