import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.GSLT.Core.ContextualLadderBaseCategory
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Logic.Equiv.Defs

/-!
# Changing the size presentation of a dependent contextual model

Contexts, substitutions, types and terms are lifted separately. All actions
are the supplied model's actual actions, wrapped in `ULift`; their laws are
derived from the supplied model and transport through those wrappers. The
readout equivalences retain each original context, arrow, family and section.

Lifting to common sufficiently large levels permits the existing homogeneous
CwF morphism interfaces to compare models whose native size presentations
differ. This is an external change of carriers, not an internal universe
type or a new universe capability of the modeled language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCwfUniverseLift

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w' uc vs wt ms

open _root_.CategoryTheory

theorem up_heq {α β : Type w'} {first : α} {second : β} (same : HEq first second) :
    HEq (ULift.up first : ULift.{ms} α) (ULift.up second : ULift.{ms} β) := by
  cases same
  rfl

theorem cast_down {α β : Type w'} (nativeEquality : α = β)
    (liftedEquality : ULift.{ms} α = ULift.{ms} β) (value : ULift.{ms} α) :
    (cast liftedEquality value).down = cast nativeEquality value.down := by
  cases nativeEquality
  rfl

/-- Every contextual carrier is retained with an independently selected
lift level. The original equations earn the lifted comprehension laws. -/
def lift (C : Cwf.{u, v, w, w'}) :
    Cwf.{max u uc, max v vs, max w wt, max w' ms} where
  Ctx := ULift.{uc} C.Ctx
  Sub source target := ULift.{vs} (C.Sub source.down target.down)
  idS context := ⟨C.idS context.down⟩
  compS later earlier := ⟨C.compS later.down earlier.down⟩
  id_comp morphism := congrArg ULift.up (C.id_comp morphism.down)
  comp_id morphism := congrArg ULift.up (C.comp_id morphism.down)
  comp_assoc later middle earlier :=
    congrArg ULift.up (C.comp_assoc later.down middle.down earlier.down)
  Ty context := ULift.{wt} (C.Ty context.down)
  tySub type morphism := ⟨C.tySub type.down morphism.down⟩
  tySub_id type := congrArg ULift.up (C.tySub_id type.down)
  tySub_comp type later earlier := congrArg ULift.up (C.tySub_comp type.down later.down earlier.down)
  Tm context type := ULift.{ms} (C.Tm context.down type.down)
  tmSub term morphism := ⟨C.tmSub term.down morphism.down⟩
  tmSub_id term := by
    apply eq_of_heq
    exact (up_heq ((heq_of_eq (C.tmSub_id term.down)).trans (cast_heq _ _))).trans
      (cast_heq _ term).symm
  tmSub_comp term later earlier := by
    apply eq_of_heq
    exact (up_heq ((heq_of_eq (C.tmSub_comp term.down later.down earlier.down)).trans
      (cast_heq _ _))).trans (cast_heq _ _).symm
  ext context type := ⟨C.ext context.down type.down⟩
  wk type := ⟨C.wk type.down⟩
  vz type := ⟨C.vz type.down⟩
  pair morphism type term := ⟨C.pair morphism.down type.down term.down⟩
  wk_pair morphism type term := congrArg ULift.up (C.wk_pair morphism.down type.down term.down)
  vz_pair morphism type term := by
    apply eq_of_heq
    exact (up_heq ((heq_of_eq (C.vz_pair morphism.down type.down term.down)).trans
      (cast_heq _ _))).trans (cast_heq _ term).symm
  pair_eta type morphism := by
    apply congrArg ULift.up
    rw [cast_down (by rw [← C.tySub_comp])]
    exact C.pair_eta type.down morphism.down

def liftWithTerminal (C : CwfWithTerminal.{u, v, w, w'}) :
    CwfWithTerminal.{max u uc, max v vs, max w wt, max w' ms} where
  toCwf := lift C.toCwf
  empty := ⟨C.empty⟩
  toEmpty context := ⟨C.toEmpty context.down⟩
  toEmpty_unique context morphism := congrArg ULift.up (C.toEmpty_unique context.down morphism.down)

/-- All four lifted carriers can use a single sufficiently large level. -/
abbrev commonLift (C : Cwf.{u, v, w, w'}) :
    Cwf.{max u v w w' uc, max u v w w' uc, max u v w w' uc, max u v w w' uc} :=
  lift.{u, v, w, w', max u v w w' uc, max u v w w' uc, max u v w w' uc, max u v w w' uc} C

abbrev commonLiftWithTerminal (C : CwfWithTerminal.{u, v, w, w'}) :
    CwfWithTerminal.{max u v w w' uc, max u v w w' uc, max u v w w' uc, max u v w w' uc} :=
  liftWithTerminal.{u, v, w, w', max u v w w' uc, max u v w w' uc,
    max u v w w' uc, max u v w w' uc} C

def upFunctor (C : Cwf.{u, v, w, w'}) :
    C.base.Context ⥤ (lift.{u, v, w, w', uc, vs, wt, ms} C).base.Context where
  obj context := ⟨⟨context.val⟩⟩
  map morphism := ⟨morphism⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def downFunctor (C : Cwf.{u, v, w, w'}) :
    (lift.{u, v, w, w', uc, vs, wt, ms} C).base.Context ⥤ C.base.Context where
  obj context := ⟨context.val.down⟩
  map morphism := morphism.down
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The change of size retains the complete category of substitutions. -/
def baseEquivalence (C : Cwf.{u, v, w, w'}) :
    C.base.Context ≌ (lift.{u, v, w, w', uc, vs, wt, ms} C).base.Context where
  functor := upFunctor C
  inverse := downFunctor C
  unitIso := NatIso.ofComponents (fun context => Iso.refl context)
    (by intro source target morphism; simp [upFunctor, downFunctor])
  counitIso := NatIso.ofComponents (fun context => Iso.refl context)
    (by
      intro source target morphism
      exact congrArg ULift.up
        ((C.id_comp morphism.down).trans (C.comp_id morphism.down).symm))
  functor_unitIso_comp context := congrArg ULift.up (C.id_comp (C.idS context.val))

def contextEquiv (C : Cwf.{u, v, w, w'}) :
    (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx ≃ C.Ctx := Equiv.ulift

def substitutionEquiv (C : Cwf.{u, v, w, w'})
    (source target : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx) :
    (lift C).Sub source target ≃ C.Sub source.down target.down := Equiv.ulift

def typeEquiv (C : Cwf.{u, v, w, w'})
    (context : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx) :
    (lift C).Ty context ≃ C.Ty context.down := Equiv.ulift

def termEquiv (C : Cwf.{u, v, w, w'})
    (context : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx) (type : (lift C).Ty context) :
    (lift C).Tm context type ≃ C.Tm context.down type.down := Equiv.ulift

@[simp] theorem id_readout (C : Cwf.{u, v, w, w'})
    (context : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx) :
    ((lift C).idS context).down = C.idS context.down := rfl

@[simp] theorem composition_readout (C : Cwf.{u, v, w, w'})
    {source middle target : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (later : (lift C).Sub middle target) (earlier : (lift C).Sub source middle) :
    ((lift C).compS later earlier).down = C.compS later.down earlier.down := rfl

@[simp] theorem type_substitution_readout (C : Cwf.{u, v, w, w'})
    {source target : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (type : (lift C).Ty target) (morphism : (lift C).Sub source target) :
    ((lift C).tySub type morphism).down = C.tySub type.down morphism.down := rfl

@[simp] theorem term_substitution_readout (C : Cwf.{u, v, w, w'})
    {source target : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    {type : (lift C).Ty target} (term : (lift C).Tm target type) (morphism : (lift C).Sub source target) :
    ((lift C).tmSub term morphism).down = C.tmSub term.down morphism.down := rfl

@[simp] theorem extension_readout (C : Cwf.{u, v, w, w'})
    (context : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx) (type : (lift C).Ty context) :
    ((lift C).ext context type).down = C.ext context.down type.down := rfl

@[simp] theorem projection_readout (C : Cwf.{u, v, w, w'})
    {context : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx} (type : (lift C).Ty context) :
    ((lift C).wk type).down = C.wk type.down := rfl

@[simp] theorem variable_readout (C : Cwf.{u, v, w, w'})
    {context : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx} (type : (lift C).Ty context) :
    ((lift C).vz type).down = C.vz type.down := rfl

@[simp] theorem pair_readout (C : Cwf.{u, v, w, w'})
    {source target : (lift.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (morphism : (lift C).Sub source target) (type : (lift C).Ty target)
    (term : (lift C).Tm source ((lift C).tySub type morphism)) :
    ((lift C).pair morphism type term).down = C.pair morphism.down type.down term.down := rfl

@[simp] theorem terminal_readout (C : CwfWithTerminal.{u, v, w, w'}) :
    (liftWithTerminal.{u, v, w, w', uc, vs, wt, ms} C).empty.down = C.empty := rfl

@[simp] theorem terminal_map_readout (C : CwfWithTerminal.{u, v, w, w'})
    (context : (lift.{u, v, w, w', uc, vs, wt, ms} C.toCwf).Ctx) :
    ((liftWithTerminal C).toEmpty context).down = C.toEmpty context.down := rfl

end Mettapedia.TypeTheory.ContextualCwfUniverseLift
