import Mettapedia.OSLF.Syntax.PresheafEventImageComparisonBridge
import Mettapedia.GSLT.Topos.PresheafEventModalControls
import Mettapedia.OSLF.Programs.NativeType
import Mathlib.CategoryTheory.Functor.Const

/-!
# Discriminating reduction-image and modal controls

The existing growing-event control is read through the shared reduction-image
interface. The existing GSLT span is a constant presheaf event graph, and its
shared may-step operation agrees with the OSLF program modality. Consequently
the existing additional-step interpretation supplies an actual failure of
exact diamond transport through this same presheaf graph interface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.PresheafEventImageComparison.Controls

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Topos.ConstructivePresheaf (EventGraph)
open Mettapedia.GSLT.Topos.PresheafEventModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Programs

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The existing operational GSLT span, in standard constant presheaves. -/
def gsltEventGraph (C : Type u) [Category.{v} C] (S : GSLT.{w}) : EventGraph C where
  vertex := (Functor.const C).obj S.Term
  edge := (Functor.const C).obj (gsltSpan S).Edge
  source :=
    { app _ := TypeCat.ofHom (gsltSpan S).source
      naturality _ _ _ := rfl }
  target :=
    { app _ := TypeCat.ofHom (gsltSpan S).target
      naturality _ _ _ := rfl }

def gsltPredicate (S : GSLT.{w}) (predicate : S.Term → Prop) :
    Subfunctor (gsltEventGraph C S).vertex where
  obj _ := {x | predicate x}
  map _ _ holds := holds

/-- Reduction sections of this graph are exactly the independently-existing
GSLT step relation, rather than a new relation asserted to model it. -/
theorem gslt_reduction_spec (S : GSLT.{w}) (X : C) (x y : S.Term) :
    (x, y) ∈ (reduction (gsltEventGraph C S)).obj X ↔ S.Step x y :=
  (mem_reduction_iff _ _ _).trans (gsltSpan_edge_iff_step S x y)

theorem gslt_diamond_comparison (S : GSLT.{w}) (predicate : S.Term → Prop)
    (X : C) (x : S.Term) :
    x ∈ (diamond (gsltEventGraph C S) (gsltPredicate S predicate)).obj X ↔
      gsltDiamond S predicate x := by
  refine (diamond_reduction_spec (gsltEventGraph C S) (gsltPredicate S predicate) X x).trans ?_
  change (∃ y : S.Term, (x, y) ∈ (reduction (gsltEventGraph C S)).obj X ∧ predicate y) ↔ _
  rw [gsltDiamond_spec]
  apply exists_congr
  intro y
  exact and_congr_left fun _ => gslt_reduction_spec S X x y

/-- The already authored additional-step interpretation induces a genuine
forward map of the retained presheaf event graphs. -/
def addedStepGraphHom :
    FreePresheafEventExtension.Hom
      (fixedGraph (gsltEventGraph C AddedStep.inert))
      (fixedGraph (gsltEventGraph C AddedStep.stepping)) where
  edgeMap :=
    { app _ := TypeCat.ofHom fun event =>
        ⟨event.source, event.target, AddedStep.forth event.step⟩
      naturality _ _ _ := rfl }
  source_comm := by ext X event; rfl
  target_comm := by ext X event; rfl

theorem addedStep_diamond_forward (predicate : Bool → Prop) :
    diamond (gsltEventGraph C AddedStep.inert) (gsltPredicate AddedStep.inert predicate) ≤
      diamond (gsltEventGraph C AddedStep.stepping) (gsltPredicate AddedStep.stepping predicate) :=
  diamond_le_of_graphHom addedStepGraphHom _

/-- The same forward interpretation fails exact diamond transport, now
through the actual shared presheaf graph and predicate construction. -/
theorem addedStep_diamond_not_natural (X : C) :
    true ∈ (diamond (gsltEventGraph C AddedStep.stepping)
      (gsltPredicate AddedStep.stepping (nativeTypeOf AddedStep.stepping false).1)).obj X ∧
      true ∉ (diamond (gsltEventGraph C AddedStep.inert)
        (gsltPredicate AddedStep.inert
          (AddedStep.inclusion.pullback (nativeTypeOf AddedStep.stepping false)).1)).obj X := by
  exact ⟨(gslt_diamond_comparison AddedStep.stepping _ X true).2 AddedStep.diamond_not_natural.1,
    fun holds => AddedStep.diamond_not_natural.2
      ((gslt_diamond_comparison AddedStep.inert _ X true).1 holds)⟩

/-- On the unchanged stepping graph, the identity interpretation has the
exact may-step transport licensed by the existing bounded-morphism theorem. -/
theorem stepping_identity_diamond (X : C) (predicate : EquationPredicate AddedStep.stepping)
    (x : Bool) :
    x ∈ (diamond (gsltEventGraph C AddedStep.stepping)
      (gsltPredicate AddedStep.stepping
        ((⟨id, id⟩ : EquationRespectingMap AddedStep.stepping AddedStep.stepping).pullback
          predicate).1)).obj X ↔
      ((⟨id, id⟩ : EquationRespectingMap AddedStep.stepping AddedStep.stepping).pullback
        (semanticDiamond AddedStep.stepping predicate)).1 x :=
  (gslt_diamond_comparison AddedStep.stepping _ X x).trans
    (((pullback_diamond_iff
      (⟨id, id⟩ : EquationRespectingMap AddedStep.stepping AddedStep.stepping)).2
        AddedStep.identity_bounded predicate x).symm)

namespace Growing

open Mettapedia.GSLT.Topos.PresheafEventModalities.Controls

/-- The actual endpoint image is absent at the early stage and present
after restriction, although the program carrier is unchanged. -/
theorem reduction_appears :
    (false, true) ∉ (reduction growing).obj 0 ∧
      (false, true) ∈ (reduction growing).obj 1 := by
  constructor
  · intro holds
    obtain ⟨event, _, _⟩ := (mem_reduction_iff growing 0 _).1 holds
    exact Nat.not_lt_zero 0 event.down
  · exact (mem_reduction_iff growing 1 _).2 ⟨⟨by decide⟩, rfl, rfl⟩

theorem present_reduction_box :
    ∀ y : Bool, (y, true) ∈ (reduction growing).obj 0 →
      y ∈ (⊥ : Subfunctor growing.vertex).obj 0 := by
  intro y holds
  obtain ⟨event, _, _⟩ := (mem_reduction_iff growing 0 _).1 holds
  exact (Nat.not_lt_zero 0 event.down).elim

/-- The internal reduction-based past box rejects that present-stage-only
test because its quantification includes the newly available future event. -/
theorem future_reduction_box_rejects :
    ¬ ∀ (Y : ℕ) (k : (0 : ℕ) ⟶ Y) (y : Bool),
      (y, growing.vertex.map k true) ∈ (reduction growing).obj Y →
        y ∈ (⊥ : Subfunctor growing.vertex).obj Y := by
  exact fun holds => internal_box_rejects_zero
    ((box_reduction_spec growing _ 0 true).2 holds)

theorem may_step_through_reduction :
    ∃ y : Bool, (false, y) ∈ (reduction growing).obj 1 ∧
      y ∈ (⊤ : Subfunctor growing.vertex).obj 1 :=
  (diamond_reduction_spec growing _ 1 false).1 new_event_diamond

end Growing

end Mettapedia.OSLF.Binding.PresheafEventImageComparison.Controls

end
