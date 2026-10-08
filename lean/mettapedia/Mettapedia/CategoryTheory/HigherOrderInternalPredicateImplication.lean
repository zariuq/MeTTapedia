import Mettapedia.CategoryTheory.HigherOrderInternalPredicateObject
import Mettapedia.CategoryTheory.InternalPredicateImplication

/-!
# The classifier earns the finite implication diagrams

The actual characteristic map of the fibre implication interprets two
independent predicate inputs. Its complete reading earns the local ordered
consequent, unit and counit diagrams, rather than supplying an all-context
interpretation law to the finite predicate interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.HigherOrderInternalPredicateImplication

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open HigherOrderInternalPredicateObject

universe u v p
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (doctrine : PredicateDoctrine.HigherOrder.{u,v,p} C)

def operation : doctrine.generic.object ⊗ doctrine.generic.object ⟶ doctrine.generic.object :=
  doctrine.generic.characteristic _ (decode doctrine (fst _ _) ⇨ decode doctrine (snd _ _))

theorem applied_read {context : C} (first second : (operations doctrine).Fiber context) :
    decode doctrine (InternalPredicateImplication.applyOperation (operations doctrine)
      (operation doctrine) first second) = decode doctrine first ⇨ decode doctrine second := by
  change doctrine.reindex (lift first second ≫ doctrine.generic.characteristic _ _)
    doctrine.generic.truth = _
  rw [doctrine.reindex_comp, doctrine.generic.classifies, doctrine.reindex_himp]
  change doctrine.reindex (lift first second) (doctrine.reindex (fst _ _) doctrine.generic.truth) ⇨
    doctrine.reindex (lift first second) (doctrine.reindex (snd _ _) doctrine.generic.truth) = _
  rw [← doctrine.reindex_comp, ← doctrine.reindex_comp, lift_fst, lift_snd]
  rfl

variable [HasEqualizers C]

private theorem ordered_inputs :
    (operations doctrine).meet
      (InternalPredicateImplication.larger (operations doctrine))
      (InternalPredicateImplication.smaller (operations doctrine)) =
        InternalPredicateImplication.smaller (operations doctrine) := by
  let inclusion := InternalPredicateImplication.orderInclusion (operations doctrine)
  have complete := equalizer.condition (operations doctrine).conjunction
    (fst doctrine.generic.object doctrine.generic.object)
  have conjunctionRead :
      (operations doctrine).meet (inclusion ≫ fst _ _) (inclusion ≫ snd _ _) =
        inclusion ≫ (operations doctrine).conjunction :=
    congrArg (fun arrow => arrow ≫ (operations doctrine).conjunction)
      (lift_comp_fst_snd inclusion)
  exact ((operations doctrine).meet_comm (laws doctrine) _ _).trans
    (conjunctionRead.trans complete)

def qualification : InternalPredicateImplication.Qualification (operations doctrine) where
  operation := operation doctrine
  monotonicity := by
    apply decode_injective doctrine
    rw [decode_meet]
    simp only [applied_read]
    apply inf_eq_right.mpr
    apply himp_le_himp_left
    have ordered := inf_eq_right.mp ((decode_meet doctrine _ _).symm.trans
      (congrArg (decode doctrine) (ordered_inputs doctrine)))
    let outgoing : InternalPredicateImplication.monotonicityScope (operations doctrine) ⟶
        InternalPredicateImplication.orderedPairs (operations doctrine) := snd _ _
    have transported := doctrine.reindex_mono outgoing ordered
    simpa only [InternalPredicateImplication.smallerConsequent,
      InternalPredicateImplication.largerConsequent, decode_substitution, outgoing] using transported
  unit := by
    apply decode_injective doctrine
    rw [decode_meet, applied_read, decode_meet]
    apply inf_eq_right.mpr
    exact le_himp_iff.mpr (le_of_eq (inf_comm _ _))
  counit := by
    apply decode_injective doctrine
    rw [decode_meet, decode_meet, applied_read]
    exact inf_eq_right.mpr inf_himp_le

end Mettapedia.CategoryTheory.HigherOrderInternalPredicateImplication
