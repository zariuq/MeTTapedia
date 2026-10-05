import Mettapedia.TypeTheory.ContextualEnumerationCovers
import Mettapedia.TypeTheory.ContextualImageFactorizationControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls

/-!
# Infinite growing controls for contextual fibre composition and covers

The actual source gains a new position at every natural-number context.
Authored and observed carriers live in different larger universes; Boolean
provenance remains in the composed enumeration. Binary coproducts keep
their summand tags. Identity fibres stay small even on the ambient hyperset
family whose complete fibre cannot have an original-bound small cover.

Transporting all locally authored enumeration data produces a natural
parameter cover, but its old row receipts miss a newly introduced argument.
The induced map to the literal pullback is therefore not covering. An
authored future enumeration supplies that new member at the same original
receipt bound, and the stronger future-data construction has a covering
pullback diagram. No generic enumeration selection is used here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallMapControls

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualSmallMapConstructions ContextualEnumerationCovers
open ContextualImageFactorizationControls
open Mettapedia.TypeTheory.MaterialSets.Hypersets

abbrev unitFamily := terminal (E := Nat)

def collapseAuthored : NaturalHom authored unitFamily where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

def collapseObserved : NaturalHom observed unitFamily where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

def authoredEnumerations : UniformEnumerations collapseAuthored := fun stage value => {
  Carrier := receipts.obj stage
  value code := ⟨ULift.up code, by cases value; rfl⟩
  covered receipt := ⟨receipt.val.down, Subtype.ext rfl⟩ }

def observedEnumerations : UniformEnumerations collapseObserved := fun stage value => {
  Carrier := Fin (stage + 1)
  value position := ⟨ULift.up position, by cases value; rfl⟩
  covered receipt := ⟨receipt.val.down, Subtype.ext rfl⟩ }

def composedEnumeration (stage : Nat) : Enumeration.{0, 1}
    (Fibre (reading.comp collapseObserved) stage PUnit.unit) :=
  compositionEnumeration reading collapseObserved stage PUnit.unit (observedEnumerations stage PUnit.unit)
    (fibreEnumeration stage)

theorem composed_smallFibres : SmallFibres (reading.comp collapseObserved) :=
  smallFibres_compose_of_enumerations reading collapseObserved fibreEnumeration
    (fun stage value => ⟨observedEnumerations stage value⟩)

theorem composed_code_value (stage : Nat) (position : Fin (stage + 1)) (tag : Bool) :
    ((composedEnumeration stage).value ⟨position, tag⟩).val = ULift.up (position, tag) := rfl

theorem composedEnumeration_injective (stage : Nat) : Function.Injective (composedEnumeration stage).value := by
  intro first second same
  have receiptsEq := congrArg (fun entry : Fibre (reading.comp collapseObserved) stage PUnit.unit =>
    entry.val.down) same
  exact Sigma.ext (congrArg Prod.fst receiptsEq) (heq_of_eq (congrArg Prod.snd receiptsEq))

theorem composed_new_receipt_not_old_image (stage : Nat) :
    ¬ ∃ old : authored.obj stage, authored.map (extension stage) old =
      ((composedEnumeration (stage + 1)).value
        ⟨⟨stage + 1, Nat.lt_succ_self (stage + 1)⟩, true⟩).val :=
  new_receipt_not_old_image stage

def coproductData : UniformEnumerations (coproductMap collapseAuthored collapseObserved) :=
  coproductEnumerations collapseAuthored collapseObserved authoredEnumerations observedEnumerations

theorem actual_coproduct_smallFibres : SmallFibres (coproductMap collapseAuthored collapseObserved) :=
  smallFibres_coproduct collapseAuthored collapseObserved
    (fun stage value => ⟨authoredEnumerations stage value⟩)
    (fun stage value => ⟨observedEnumerations stage value⟩)

theorem coproduct_tags_retained (stage : Nat) (left : authored.obj stage) (right : observed.obj stage) :
    (coproductMap collapseAuthored collapseObserved).app stage (Sum.inl left) ≠
      (coproductMap collapseAuthored collapseObserved).app stage (Sum.inr right) := by
  intro same
  change Sum.inl PUnit.unit = Sum.inr PUnit.unit at same
  cases same

def ambient : Nat ⥤ Type 1 where
  obj _ := HSet.{0}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

theorem ambient_identity_smallFibres : SmallFibres (identity ambient) := identity_smallFibres ambient

theorem ambient_has_no_small_global_cover {I : Type} (value : I → ambient.obj 0) :
    ¬ Function.Surjective value := CoveredFuturePowerControls.hset_has_no_small_cover value

def initialLocal : (localFamily collapseAuthored).obj 0 :=
  localSeed collapseAuthored 0 PUnit.unit (authoredEnumerations 0 PUnit.unit)

def laterLocal : (localFamily collapseAuthored).obj 1 :=
  (localFamily collapseAuthored).map (extension 0) initialLocal

def omittedLocalPoint : (pullback collapseAuthored (localProjection collapseAuthored)).obj 1 :=
  ⟨(newReceipt 0, laterLocal), rfl⟩

theorem actual_local_parameter_cover (stage : Nat) :
    Function.Surjective ((localProjection collapseAuthored).app stage) :=
  localProjection_surjective collapseAuthored (fun stage value => ⟨authoredEnumerations stage value⟩) stage

theorem actual_local_rows_smallFibres : SmallFibres (localRowsProjection collapseAuthored) :=
  localRows_smallFibres collapseAuthored

/-- The natural local-data triangle exists, but its old codes do not cover
the new position in the current literal pullback. -/
theorem local_triangle_not_quasi_pullback :
    ¬ Function.Surjective ((localToPullback collapseAuthored).app 1) := by
  intro onto
  obtain ⟨row, same⟩ := onto omittedLocalPoint
  have valueEq : (localRowsReadout collapseAuthored).app 1 row = newReceipt 0 :=
    congrArg (fun point : (pullback collapseAuthored (localProjection collapseAuthored)).obj 1 => point.val.1) same
  have receiptEq : (localRowsProjection collapseAuthored).app 1 row = laterLocal :=
    congrArg (fun point : (pullback collapseAuthored (localProjection collapseAuthored)).obj 1 => point.val.2) same
  obtain ⟨code, represents⟩ := (localRowsEnumeration collapseAuthored 1 laterLocal).covered ⟨row, receiptEq⟩
  have readoutEq := congrArg (fun entry : Fibre (localRowsProjection collapseAuthored) 1 laterLocal =>
    (localRowsReadout collapseAuthored).app 1 entry.val) represents
  change authored.map (𝟙 0 ≫ extension 0) ((authoredEnumerations 0 PUnit.unit).value code).val =
    (localRowsReadout collapseAuthored).app 1 row at readoutEq
  rw [Category.id_comp] at readoutEq
  exact new_receipt_not_old_image 0 ⟨((authoredEnumerations 0 PUnit.unit).value code).val,
    readoutEq.trans valueEq⟩

def authoredFutureData (stage : Nat) (value : unitFamily.obj stage) :
    FutureEnumerations collapseAuthored stage value :=
  fun future => authoredEnumerations future.1 (unitFamily.map future.2 value)

theorem actual_future_data_nonempty : ∀ stage value, Nonempty (FutureEnumerations collapseAuthored stage value) :=
  fun stage value => ⟨authoredFutureData stage value⟩

def initialFuture : (futureFamily collapseAuthored).obj 0 :=
  futureSeed collapseAuthored 0 PUnit.unit (authoredFutureData 0 PUnit.unit)

def laterFuture : (futureFamily collapseAuthored).obj 1 :=
  (futureFamily collapseAuthored).map (extension 0) initialFuture

/-- Future metadata reads the new fibre at its actual target, retaining
the same original small receipt universe. -/
theorem future_current_enumeration_contains_new_receipt :
    ((currentEnumeration collapseAuthored 1 laterFuture).value (newReceipt 0).down).val = newReceipt 0 := rfl

theorem actual_future_pullback_smallFibres :
    SmallFibres (pullbackSecond collapseAuthored (futureProjection collapseAuthored)) :=
  futurePullback_smallFibres collapseAuthored

theorem actual_future_top_cover (stage : Nat) :
    Function.Surjective ((pullbackFirst collapseAuthored (futureProjection collapseAuthored)).app stage) :=
  futureTop_surjective collapseAuthored actual_future_data_nonempty stage

theorem future_pulled_enumeration_contains_new_receipt :
    ((pulledEnumerations collapseAuthored 1 laterFuture).value (newReceipt 0).down).val.val.1 = newReceipt 0 := rfl

theorem actual_future_classifier_current (stage : Nat) (argument : authored.obj stage) :
    ((fibreClassifier collapseAuthored actual_future_data_nonempty).app stage PUnit.unit).val.holds
      (CoveredFuturePowerFamilies.current authored stage argument) := rfl

end Mettapedia.TypeTheory.ContextualSmallMapControls
