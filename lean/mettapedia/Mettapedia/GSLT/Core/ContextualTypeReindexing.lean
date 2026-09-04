import Mettapedia.GSLT.Core.ContextualTypeCategory

/-!
# Reindexing types and display maps

A substitution `σ : Γ → Δ` sends a type over `Δ` to its substituted type
over `Γ`.  On display maps this is the pullback action induced by context
comprehension.  This module constructs the action explicitly from weakening,
the generic variable, pairing, and term substitution.

The raw object and arrow actions are separated from the functor-law proof.
That separation exposes the exact cartesian-lifting equations instead of
hiding them behind an assumed pullback operation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

namespace TypeOver

/-- The canonical map from the display context of `A[σ]` to the display
context of `A`.  It is the substitution-level pullback leg selected by the
CwF comprehension structure. -/
def extensionSubstitution {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) (A : C.Ty Δ) :
    C.Sub (C.ext Γ (C.tySub A substitution)) (C.ext Δ A) :=
  C.pair
    (C.compS substitution (C.wk (C.tySub A substitution))) A
    (cast (by rw [C.tySub_comp]) (C.vz (C.tySub A substitution)))

/-- The pullback leg lies over the original substitution. -/
theorem wk_extensionSubstitution {C : Cwf.{u, v, w, w'}}
    {Γ Δ : C.Ctx} (substitution : C.Sub Γ Δ) (A : C.Ty Δ) :
    C.compS (C.wk A) (extensionSubstitution substitution A) =
      C.compS substitution (C.wk (C.tySub A substitution)) :=
  C.wk_pair _ _ _

/-- The generic variable of the substituted type is the pullback of the
generic variable of the original type.  The statement is heterogeneous so
it records the canonical equality without fixing a particular cast normal
form. -/
theorem vz_extensionSubstitution {C : Cwf.{u, v, w, w'}}
    {Γ Δ : C.Ctx} (substitution : C.Sub Γ Δ) (A : C.Ty Δ) :
    HEq (C.tmSub (C.vz A) (extensionSubstitution substitution A))
      (C.vz (C.tySub A substitution)) := by
  unfold extensionSubstitution
  let liftedVariable :
      C.Tm (C.ext Γ (C.tySub A substitution))
        (C.tySub A
          (C.compS substitution (C.wk (C.tySub A substitution)))) :=
    cast (congrArg (C.Tm (C.ext Γ (C.tySub A substitution)))
      (C.tySub_comp A substitution
        (C.wk (C.tySub A substitution))).symm)
      (C.vz (C.tySub A substitution))
  have beta := C.vz_pair
    (C.compS substitution (C.wk (C.tySub A substitution))) A
    liftedVariable
  exact (heq_of_eq beta).trans
    ((cast_heq _ liftedVariable).trans
      (cast_heq _ (C.vz (C.tySub A substitution))))

/-- Reindex a bundled type object. -/
def reindexObject {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) (A : TypeOver C Δ) : TypeOver C Γ where
  val := C.tySub A.val substitution

/-- The term presenting the pullback of a display map. -/
def reindexArrowTerm {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) {A B : TypeOver C Δ}
    (morphism : A ⟶ B) :
    C.Tm (C.ext Γ (C.tySub A.val substitution))
      (C.tySub (C.tySub B.val substitution)
        (C.wk (C.tySub A.val substitution))) :=
  cast (by
      rw [← C.tySub_comp, wk_extensionSubstitution, C.tySub_comp])
    (C.tmSub (toTerm morphism)
      (extensionSubstitution substitution A.val))

/-- Pull back a display map along a context substitution. -/
def reindexArrow {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) {A B : TypeOver C Δ}
    (morphism : A ⟶ B) :
    reindexObject substitution A ⟶ reindexObject substitution B :=
  ofTerm (reindexArrowTerm substitution morphism)

/-- Reading the term of a reindexed display map returns the explicitly
reindexed term. -/
theorem toTerm_reindexArrow {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) {A B : TypeOver C Δ}
    (morphism : A ⟶ B) :
    toTerm (reindexArrow substitution morphism) =
      reindexArrowTerm substitution morphism :=
  toTerm_ofTerm _

/-- The explicitly reindexed term is the raw substitution of the original
display-map term along the selected comprehension lift, before selecting a
cast normal form. -/
theorem reindexArrowTerm_raw_heq {C : Cwf.{u, v, w, w'}}
    {Γ Δ : C.Ctx} (substitution : C.Sub Γ Δ)
    {A B : TypeOver C Δ} (morphism : A ⟶ B) :
    HEq (reindexArrowTerm substitution morphism)
      (C.tmSub (toTerm morphism)
        (extensionSubstitution substitution A.val)) :=
  cast_heq _ _

/-- Pulling back a display map and then following the selected comprehension
lift is the same substitution as following the original display map and then
lifting the base substitution.  This is the cartesian square from which the
functor laws are derived. -/
theorem extensionSubstitution_naturality
    {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) {A B : TypeOver C Δ}
    (morphism : A ⟶ B) :
    C.compS (extensionSubstitution substitution B.val)
        (reindexArrow substitution morphism).substitution =
      C.compS morphism.substitution
        (extensionSubstitution substitution A.val) := by
  apply TypeOver.substitution_ext
  · calc
      C.compS (C.wk B.val)
          (C.compS (extensionSubstitution substitution B.val)
            (reindexArrow substitution morphism).substitution) =
          C.compS
            (C.compS (C.wk B.val)
              (extensionSubstitution substitution B.val))
            (reindexArrow substitution morphism).substitution :=
        (C.comp_assoc _ _ _).symm
      _ = C.compS
            (C.compS substitution
              (C.wk (C.tySub B.val substitution)))
            (reindexArrow substitution morphism).substitution := by
        rw [wk_extensionSubstitution]
      _ = C.compS substitution
            (C.compS (C.wk (C.tySub B.val substitution))
              (reindexArrow substitution morphism).substitution) :=
        C.comp_assoc _ _ _
      _ = C.compS substitution
            (C.wk (C.tySub A.val substitution)) := by
        have pulledOver := (reindexArrow substitution morphism).over
        change C.compS (C.wk (C.tySub B.val substitution))
            (reindexArrow substitution morphism).substitution =
          C.wk (C.tySub A.val substitution) at pulledOver
        exact congrArg (fun base => C.compS substitution base) pulledOver
      _ = C.compS
            (C.compS (C.wk B.val) morphism.substitution)
            (extensionSubstitution substitution A.val) := by
        rw [morphism.over, wk_extensionSubstitution]
      _ = C.compS (C.wk B.val)
            (C.compS morphism.substitution
              (extensionSubstitution substitution A.val)) :=
        C.comp_assoc _ _ _
  · have liftedVariableTypes :
        C.tySub (C.tySub B.val (C.wk B.val))
            (extensionSubstitution substitution B.val) =
          C.tySub (C.tySub B.val substitution)
            (C.wk (C.tySub B.val substitution)) := by
      rw [← C.tySub_comp, wk_extensionSubstitution, C.tySub_comp]
    have displayedTermTypes :
        C.tySub B.val (C.wk A.val) =
          C.tySub (C.tySub B.val (C.wk B.val))
            morphism.substitution := by
      rw [← C.tySub_comp, morphism.over]
    exact
      (tmSub_comp_heq (C.vz B.val)
        (extensionSubstitution substitution B.val)
        (reindexArrow substitution morphism).substitution).trans
      ((tmSub_heq liftedVariableTypes
        (vz_extensionSubstitution substitution B.val)
        (reindexArrow substitution morphism).substitution).trans
      ((vz_ofTerm_heq
        (reindexArrowTerm substitution morphism)).trans
      ((reindexArrowTerm_raw_heq substitution morphism).trans
      ((tmSub_heq displayedTermTypes
        (toTerm_raw_heq morphism)
        (extensionSubstitution substitution A.val)).trans
        (tmSub_comp_heq (C.vz B.val) morphism.substitution
          (extensionSubstitution substitution A.val)).symm))))

/-- The selected comprehension lift is monic with respect to arrows lying
over the reindexed base.  This is the uniqueness half of the cartesian
lifting property needed for the reindexing functor laws. -/
theorem extensionSubstitution_cancel
    {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) {source : TypeOver C Γ}
    {B : TypeOver C Δ}
    {left right : source ⟶ reindexObject substitution B}
    (compositesEqual :
      C.compS (extensionSubstitution substitution B.val)
          left.substitution =
        C.compS (extensionSubstitution substitution B.val)
          right.substitution) :
    left = right := by
  apply Hom.ext
  apply TypeOver.substitution_ext
  · have leftOver := left.over
    have rightOver := right.over
    change C.compS (C.wk (C.tySub B.val substitution))
        left.substitution = C.wk source.val
      at leftOver
    change C.compS (C.wk (C.tySub B.val substitution))
        right.substitution = C.wk source.val
      at rightOver
    exact leftOver.trans rightOver.symm
  · have liftedVariableTypes :
        C.tySub (C.tySub B.val (C.wk B.val))
            (extensionSubstitution substitution B.val) =
          C.tySub (C.tySub B.val substitution)
            (C.wk (C.tySub B.val substitution)) := by
      rw [← C.tySub_comp, wk_extensionSubstitution, C.tySub_comp]
    have composedReadEquality :
        HEq
          (C.tmSub (C.vz B.val)
            (C.compS (extensionSubstitution substitution B.val)
              left.substitution))
          (C.tmSub (C.vz B.val)
            (C.compS (extensionSubstitution substitution B.val)
              right.substitution)) := by
      rw [compositesEqual]
    exact
      (tmSub_heq liftedVariableTypes
        (vz_extensionSubstitution substitution B.val)
        left.substitution).symm.trans
      ((tmSub_comp_heq (C.vz B.val)
        (extensionSubstitution substitution B.val)
        left.substitution).symm.trans
      (composedReadEquality.trans
      ((tmSub_comp_heq (C.vz B.val)
        (extensionSubstitution substitution B.val)
        right.substitution).trans
      (tmSub_heq liftedVariableTypes
        (vz_extensionSubstitution substitution B.val)
        right.substitution))))

/-- Candidate reindexing functor induced by the object and display-map
actions above. -/
def reindexFunctor {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) : TypeOver C Δ ⥤ TypeOver C Γ where
  obj := reindexObject substitution
  map := reindexArrow substitution
  map_id A := by
    apply extensionSubstitution_cancel substitution
    change C.compS (extensionSubstitution substitution A.val)
        (reindexArrow substitution (𝟙 A)).substitution =
      C.compS (extensionSubstitution substitution A.val)
        (C.idS (C.ext Γ (C.tySub A.val substitution)))
    have naturality :=
      extensionSubstitution_naturality substitution (𝟙 A)
    change C.compS (extensionSubstitution substitution A.val)
        (reindexArrow substitution (𝟙 A)).substitution =
      C.compS (C.idS (C.ext Δ A.val))
        (extensionSubstitution substitution A.val) at naturality
    exact naturality.trans
      ((C.id_comp _).trans (C.comp_id _).symm)
  map_comp {X Y Z} left right := by
    apply extensionSubstitution_cancel substitution
    have compositeNaturality :=
      extensionSubstitution_naturality substitution (left ≫ right)
    change C.compS (extensionSubstitution substitution Z.val)
        (reindexArrow substitution (left ≫ right)).substitution =
      C.compS (left ≫ right).substitution
        (extensionSubstitution substitution X.val) at compositeNaturality
    have leftNaturality :=
      extensionSubstitution_naturality substitution left
    change C.compS (extensionSubstitution substitution Y.val)
        (reindexArrow substitution left).substitution =
      C.compS left.substitution
        (extensionSubstitution substitution X.val) at leftNaturality
    have leftWhiskered := congrArg
      (fun inner => C.compS right.substitution inner)
      leftNaturality.symm
    have rightNaturality :=
      extensionSubstitution_naturality substitution right
    change C.compS (extensionSubstitution substitution Z.val)
        (reindexArrow substitution right).substitution =
      C.compS right.substitution
        (extensionSubstitution substitution Y.val) at rightNaturality
    have reassociateLeft :=
      (C.comp_assoc right.substitution
        (extensionSubstitution substitution Y.val)
        (reindexArrow substitution left).substitution).symm
    have rightWhiskered := congrArg
      (fun outer => C.compS outer
        (reindexArrow substitution left).substitution)
      rightNaturality.symm
    have reassociateFinal :=
      C.comp_assoc (extensionSubstitution substitution Z.val)
        (reindexArrow substitution right).substitution
        (reindexArrow substitution left).substitution
    rw [compositeNaturality]
    change C.compS (C.compS right.substitution left.substitution)
        (extensionSubstitution substitution X.val) =
      C.compS (extensionSubstitution substitution Z.val)
        (C.compS (reindexArrow substitution right).substitution
          (reindexArrow substitution left).substitution)
    rw [C.comp_assoc]
    exact leftWhiskered.trans
      (reassociateLeft.trans
        (rightWhiskered.trans reassociateFinal))

/-! ## Concrete positive and negative controls -/

/-- In the families model, the selected extension substitution maps
`(γ,a)` to `(σ γ,a)`. -/
theorem families_extensionSubstitution_apply
    {Γ Δ : Type} (substitution : Γ → Δ) (A : Δ → Type)
    (point : Σ γ : Γ, A (substitution γ)) :
    extensionSubstitution (C := familiesCwf) substitution A point =
      ⟨substitution point.1, point.2⟩ := rfl

/-- Reindexing Boolean negation along the unique map from `Bool` to the
one-point context remains non-identity. -/
theorem reindexed_boolNegation_ne_identity :
    reindexArrow (C := familiesCwf)
        (fun _ : Bool => PUnit.unit) boolNegationDisplay ≠
      𝟙 (reindexObject (C := familiesCwf)
        (fun _ : Bool => PUnit.unit) unitBoolType) := by
  intro equalArrows
  have equalSubstitutions := congrArg Hom.substitution equalArrows
  have atTrue := congrFun equalSubstitutions
    (⟨false, true⟩ : Σ _ : Bool, Bool)
  have valuesEqual := congrArg (fun point => point.2) atTrue
  change false = true at valuesEqual
  cases valuesEqual

#print axioms TypeOver.extensionSubstitution
#print axioms TypeOver.wk_extensionSubstitution
#print axioms TypeOver.vz_extensionSubstitution
#print axioms TypeOver.reindexObject
#print axioms TypeOver.reindexArrowTerm
#print axioms TypeOver.reindexArrow
#print axioms TypeOver.toTerm_reindexArrow
#print axioms TypeOver.reindexArrowTerm_raw_heq
#print axioms TypeOver.extensionSubstitution_naturality
#print axioms TypeOver.extensionSubstitution_cancel
#print axioms TypeOver.reindexFunctor
#print axioms TypeOver.families_extensionSubstitution_apply
#print axioms TypeOver.reindexed_boolNegation_ne_identity

end TypeOver

end Mettapedia.GSLT.Core.ContextualLadder
