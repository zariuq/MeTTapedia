import Mettapedia.CategoryTheory.InternalPredicateFunctionObject
import Mettapedia.CategoryTheory.PredicateDoctrine

/-!
# The finite predicate object of an earned higher-order doctrine

The classifier constructs actual truth and conjunction arrows. Their finite
diagrams follow from classification and the fibre operations. Complete
generalized predicate maps and functions are identified with the original
doctrine fibres, retaining their substitution and order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.HigherOrderInternalPredicateObject

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject

universe u v p
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (doctrine : PredicateDoctrine.HigherOrder.{u,v,p} C)

def decode {context : C} (predicate : context ⟶ doctrine.generic.object) :
    doctrine.Fiber context := doctrine.reindex predicate doctrine.generic.truth

theorem decode_characteristic {context : C} (predicate : doctrine.Fiber context) :
    decode doctrine (doctrine.generic.characteristic context predicate) = predicate :=
  doctrine.generic.classifies context predicate

theorem decode_injective {context : C} :
    Function.Injective (decode doctrine (context := context)) := by
  intro first second same
  exact (doctrine.generic.unique context (decode doctrine first) first rfl).trans
    (doctrine.generic.unique context (decode doctrine first) second same.symm).symm

def operations : Operations C where
  proposition := doctrine.generic.object
  truth := doctrine.generic.characteristic (𝟙_ C) ⊤
  conjunction := doctrine.generic.characteristic _
    (decode doctrine (fst _ _) ⊓ decode doctrine (snd _ _))

theorem decode_substitution {first second : C} (incoming : first ⟶ second)
    (predicate : second ⟶ doctrine.generic.object) :
    decode doctrine (incoming ≫ predicate) = doctrine.reindex incoming (decode doctrine predicate) :=
  doctrine.reindex_comp incoming predicate doctrine.generic.truth

theorem decode_meet {context : C} (first second : (operations doctrine).Fiber context) :
    decode doctrine ((operations doctrine).meet first second) =
      decode doctrine first ⊓ decode doctrine second := by
  change doctrine.reindex (lift first second ≫ doctrine.generic.characteristic _ _)
    doctrine.generic.truth = _
  rw [doctrine.reindex_comp, doctrine.generic.classifies, doctrine.reindex_inf]
  change doctrine.reindex (lift first second) (doctrine.reindex (fst _ _) doctrine.generic.truth) ⊓
    doctrine.reindex (lift first second) (doctrine.reindex (snd _ _) doctrine.generic.truth) = _
  rw [← doctrine.reindex_comp, ← doctrine.reindex_comp, lift_fst, lift_snd]
  rfl

theorem decode_top (context : C) : decode doctrine ((operations doctrine).top context) = ⊤ := by
  change doctrine.reindex (toUnit context ≫ doctrine.generic.characteristic _ ⊤)
    doctrine.generic.truth = ⊤
  rw [doctrine.reindex_comp, doctrine.generic.classifies, doctrine.reindex_top]

private theorem conjunction_after {context : C}
    (tuple : context ⟶ doctrine.generic.object ⊗ doctrine.generic.object) :
    tuple ≫ (operations doctrine).conjunction =
      (operations doctrine).meet (tuple ≫ fst _ _) (tuple ≫ snd _ _) := by
  change tuple ≫ (operations doctrine).conjunction =
    lift (tuple ≫ fst _ _) (tuple ≫ snd _ _) ≫ (operations doctrine).conjunction
  exact (congrArg (fun arrow => arrow ≫ (operations doctrine).conjunction)
    (lift_comp_fst_snd tuple)).symm

theorem laws : (operations doctrine).Laws where
  commutativity := by
    apply decode_injective doctrine
    change decode doctrine ((operations doctrine).meet (snd _ _) (fst _ _)) =
      decode doctrine (operations doctrine).conjunction
    have direct : (operations doctrine).meet (fst _ _) (snd _ _) =
        (operations doctrine).conjunction := by
      simp only [Operations.meet, lift_fst_snd, Category.id_comp]
    rw [← direct, decode_meet, decode_meet]
    exact inf_comm _ _
  associativity := by
    apply decode_injective doctrine
    change decode doctrine ((operations doctrine).meet
      (fst _ _ ≫ (operations doctrine).conjunction) (snd _ _)) =
      decode doctrine ((operations doctrine).meet (fst _ _ ≫ fst _ _)
        (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ (operations doctrine).conjunction))
    rw [conjunction_after, decode_meet, decode_meet, decode_meet]
    have rightNested := decode_meet doctrine
      (fst (doctrine.generic.object ⊗ doctrine.generic.object) doctrine.generic.object ≫ snd _ _)
      (snd (doctrine.generic.object ⊗ doctrine.generic.object) doctrine.generic.object)
    exact (inf_assoc _ _ _).trans (congrArg (_ ⊓ ·) rightNested.symm)
  idempotence := by
    apply decode_injective doctrine
    change decode doctrine ((operations doctrine).meet (𝟙 _) (𝟙 _)) = decode doctrine (𝟙 _)
    rw [decode_meet, inf_idem]
    rfl
  truthUnit := by
    apply decode_injective doctrine
    change decode doctrine ((operations doctrine).meet (𝟙 _) ((operations doctrine).top _)) =
      decode doctrine (𝟙 _)
    rw [decode_meet, decode_top, inf_top_eq]
    rfl

def orderEquiv (context : C) :
    letI := (operations doctrine).semilattice (laws doctrine) context
    (operations doctrine).Fiber context ≃o doctrine.Fiber context := by
  letI := (operations doctrine).semilattice (laws doctrine) context
  refine
    { toFun := decode doctrine
      invFun := doctrine.generic.characteristic context
      left_inv := fun predicate =>
        (doctrine.generic.unique context (decode doctrine predicate) predicate rfl).symm
      right_inv := decode_characteristic doctrine
      map_rel_iff' := ?_ }
  intro first second
  change decode doctrine first ≤ decode doctrine second ↔ first ≤ second
  constructor
  · intro ordered
    change (operations doctrine).meet second first = first
    apply decode_injective doctrine
    rw [decode_meet]
    exact inf_eq_right.mpr ordered
  · intro ordered
    change (operations doctrine).meet second first = first at ordered
    exact inf_eq_right.mp ((decode_meet doctrine second first).symm.trans
      (congrArg (decode doctrine) ordered))

def family {value parameter : C}
    (predicate : parameter ⟶ InternalPredicateFunctionObject.power (operations doctrine) value) :
    doctrine.Fiber (value ⊗ parameter) :=
  decode doctrine (InternalPredicateFunctionObject.read (operations doctrine) predicate)

theorem family_meet {value parameter : C}
    (first second : (InternalPredicateFunctionObject.operations (operations doctrine) value).Fiber parameter) :
    family doctrine ((InternalPredicateFunctionObject.operations (operations doctrine) value).meet first second) =
      family doctrine first ⊓ family doctrine second := by
  rw [family, InternalPredicateFunctionObject.read_meet, decode_meet]
  rfl

theorem family_injective {value parameter : C} :
    Function.Injective (family doctrine (value := value) (parameter := parameter)) :=
  (decode_injective doctrine).comp (InternalPredicateFunctionObject.read_injective (operations doctrine))

theorem family_substitution {value first second : C} (incoming : first ⟶ second)
    (predicate : second ⟶ InternalPredicateFunctionObject.power (operations doctrine) value) :
    family doctrine (incoming ≫ predicate) = doctrine.reindex (value ◁ incoming) (family doctrine predicate) := by
  rw [family, InternalPredicateFunctionObject.read_substitution, decode_substitution]
  rfl

end Mettapedia.CategoryTheory.HigherOrderInternalPredicateObject
