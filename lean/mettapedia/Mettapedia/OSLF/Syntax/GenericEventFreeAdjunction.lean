import Mettapedia.OSLF.Syntax.EventGraphSlice
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Free adjoining of firing events in a general target

For any event endpoint object, graphs are the slice over that object.
If the target has binary coproducts, freely adjoining a chosen generator
graph is the standard coproduct/under-category adjunction. This construction
does not assume that the target has images or a subobject classifier.

The existing slice-coproduct theorem compares the pointwise disjoint sum of
authored presheaf events with the categorical coproduct. The adjunction here
states the corresponding free-event law in any target with the coproducts
needed to interpret it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.GenericEventFreeAdjunction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.EventGraphSlice
open Mettapedia.OSLF.Binding.FreePresheafEventExtension

universe u v w

variable {D : Type u} [Category.{v} D] [HasBinaryProducts D]
    [HasBinaryCoproducts D]

/-- A graph of generators is freely adjoined to any graph over the same
endpoint object. The codomain records the chosen map of generators. -/
noncomputable def freeEvents (programs : D)
    (generators : Categorical.EventGraph programs) :
    Categorical.EventGraph programs ⥤ Under generators :=
  Under.costar generators

/-- The relative universal property of freely adjoining event generators
in every target with binary coproducts. -/
noncomputable def freeEventsAdjunction (programs : D)
    (generators : Categorical.EventGraph programs) :
    freeEvents programs generators ⊣ Under.forget generators :=
  Under.costarAdjForget generators

section PresheafComparison

variable {C : Type u} [Category.{v} C] (V : C ⥤ Type w)

private noncomputable instance graphHasBinaryCoproducts :
    HasBinaryCoproducts (Graph V) := by
  exact @hasBinaryCoproducts_of_hasColimit_pair (Graph V) _
    (fun {G K} => HasColimit.mk
      ⟨graphSumCofan V G K, graphSumIsColimit V G K⟩)

/-- The explicit disjoint sum of authored presheaf events agrees with the
chosen coproduct of endpoint-slice graphs. Both carry the same individual
event witnesses and both endpoint maps. -/
noncomputable def graphSumIsoCoproduct (G K : Graph V) :
    toSlice V (graphSum G K) ≅
      toSlice V G ⨿ toSlice V K := by
  letI : (toSliceFunctor V).IsEquivalence :=
    (graphSliceEquivalence V).isEquivalence_functor
  haveI : PreservesColimit (pair G K) (toSliceFunctor V) := inferInstance
  let e₁ :=
    (graphSumIsColimit V G K).coconePointUniqueUpToIso
      (coprodIsCoprod G K)
  let e₂ : toSlice V (graphSum G K) ≅
      (toSliceFunctor V).obj (G ⨿ K) :=
    (toSliceFunctor V).mapIso e₁
  let e₃ : toSlice V G ⨿ toSlice V K ≅
      (toSliceFunctor V).obj (G ⨿ K) :=
    PreservesColimitPair.iso (toSliceFunctor V) G K
  exact e₂ ≪≫ e₃.symm

end PresheafComparison

end Mettapedia.OSLF.Binding.GenericEventFreeAdjunction

namespace Mettapedia.OSLF.Binding.GenericEventFreeAdjunction.RhoExample

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.EventGraphSlice
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents

/-- Free adjoining of the actual source COMM/Drop generators in the
category of internal event graphs over equation-class rho processes. -/
noncomputable def sourceCategoricalFreeAdjunction :
    freeEvents states EventGraphSlice.RhoExample.sourceProductEventSlice ⊣
      Under.forget EventGraphSlice.RhoExample.sourceProductEventSlice :=
  freeEventsAdjunction states EventGraphSlice.RhoExample.sourceProductEventSlice

/-- For any prior rho event graph, the authored disjoint-sum construction
is the categorical coproduct of that graph and the COMM/Drop generators. -/
noncomputable def sourceGraphSumIso (prior : Graph states) :
    toSlice states (graphSum prior sourceEvents) ≅
      toSlice states prior ⨿ toSlice states sourceEvents :=
  graphSumIsoCoproduct states prior sourceEvents

end Mettapedia.OSLF.Binding.GenericEventFreeAdjunction.RhoExample
