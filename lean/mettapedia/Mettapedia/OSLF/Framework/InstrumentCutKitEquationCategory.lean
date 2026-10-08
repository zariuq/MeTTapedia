import Mettapedia.OSLF.Framework.InstrumentCutKitCategory
import Mettapedia.OSLF.Syntax.SortedConstructorPaddingRelativePushout

/-!
# The supported kit category on actual unary-unit equation classes

Arrows are independently generated term or context classes. Hereditary kit
support is tested on their earned normal arrow, so it is independent of the
supplied padding representative. Complete normalization and embedding
roundtrips construct a full faithful based equivalence with the actual kit
category. Original constructors and distinct hole positions remain intact.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.OSLF.SortedConstructors.Padding
open Mettapedia.CategoryTheory.GroundPath

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutKitEquationCategoryQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

structure EquationKitObject (opened : InstrumentObservations.Policy Symbols) where
  base : EquationObject (signature arity) (.base : Srt Symbols arity)

instance equationKitCategory (opened : InstrumentObservations.Policy Symbols) :
    Category.{u} (EquationKitObject arity opened) where
  Hom first second := {arrow : first.base ⟶ second.base //
    KitArrow arity opened ((normalizationFunctor (signature arity) .base).map arrow)}
  id object := ⟨𝟙 object.base, by
    rw [_root_.CategoryTheory.Functor.map_id]
    exact KitArrow.id arity opened _⟩
  comp first second := ⟨first.val ≫ second.val, by
    rw [Functor.map_comp]
    exact first.property.comp arity second.property⟩
  id_comp arrow := Subtype.ext (Category.id_comp arrow.val)
  comp_id arrow := Subtype.ext (Category.comp_id arrow.val)
  assoc first second third := Subtype.ext (Category.assoc first.val second.val third.val)

def equationKitOrigin (opened : InstrumentObservations.Policy Symbols) : EquationKitObject arity opened := ⟨.origin⟩

def equationKitInterface (opened : InstrumentObservations.Policy Symbols) (sort : Srt Symbols arity) :
    EquationKitObject arity opened := ⟨.interface sort⟩

def kitNormalization (opened : InstrumentObservations.Policy Symbols) :
    EquationKitObject arity opened ⥤ KitObject arity opened where
  obj object := ⟨(normalizationFunctor (signature arity) .base).obj object.base⟩
  map arrow := ⟨(normalizationFunctor (signature arity) .base).map arrow.val, arrow.property⟩
  map_id object := Subtype.ext ((normalizationFunctor (signature arity) .base).map_id object.base)
  map_comp first second := Subtype.ext
    ((normalizationFunctor (signature arity) .base).map_comp first.val second.val)

instance kitNormalization_faithful (opened : InstrumentObservations.Policy Symbols) :
    (kitNormalization arity opened).Faithful where
  map_injective := by
    intro source target first second same
    apply Subtype.ext
    let _ := normalization_faithful (signature arity) (.base : Srt Symbols arity)
    apply (normalizationFunctor (signature arity) .base).map_injective
    exact congrArg (fun arrow : (kitNormalization arity opened).obj source ⟶
      (kitNormalization arity opened).obj target => arrow.val) same

instance kitNormalization_full (opened : InstrumentObservations.Policy Symbols) :
    (kitNormalization arity opened).Full where
  map_surjective := by
    intro source target supplied
    let normal := normalizationFunctor (signature arity) (.base : Srt Symbols arity)
    let _ : normal.Full := normalization_full (signature arity) (.base : Srt Symbols arity)
    let lifted : source ⟶ target := ⟨normal.preimage supplied.val, by
      change KitArrow arity opened (normal.map (normal.preimage supplied.val))
      exact (normal.map_preimage supplied.val).symm ▸ supplied.property⟩
    exact ⟨lifted, Subtype.ext (normal.map_preimage supplied.val)⟩

theorem kitNormalization_objects (opened : InstrumentObservations.Policy Symbols) :
    Function.Surjective (kitNormalization arity opened).obj := by
  intro object
  obtain ⟨original, readout⟩ := normalization_objects (signature arity) .base object.base
  refine ⟨⟨original⟩, ?_⟩
  cases object
  cases readout
  rfl

instance kitNormalization_essSurj (opened : InstrumentObservations.Policy Symbols) :
    (kitNormalization arity opened).EssSurj where
  mem_essImage object := by
    obtain ⟨original, readout⟩ := kitNormalization_objects arity opened object
    exact ⟨original, ⟨eqToIso readout⟩⟩

instance kitNormalization_isEquivalence (opened : InstrumentObservations.Policy Symbols) :
    (kitNormalization arity opened).IsEquivalence where

def kitEquationEquivalence (opened : InstrumentObservations.Policy Symbols) :
    EquationKitObject arity opened ≌ KitObject arity opened := (kitNormalization arity opened).asEquivalence

def equationKitValue {opened : InstrumentObservations.Policy Symbols} {sort : Srt Symbols arity}
    (value : Class (signature arity) (.base : Srt Symbols arity) sort)
    (supported : KitSupported arity opened (Padding.value (signature arity) .base value)) :
    equationKitOrigin arity opened ⟶ equationKitInterface arity opened sort :=
  ⟨classTermArrow (signature arity) .base value, .value supported⟩

def equationKitContext {opened : InstrumentObservations.Policy Symbols} {source target : Srt Symbols arity}
    (context : ContextClass (signature arity) (.base : Srt Symbols arity) source target)
    (supported : KitContext arity opened (contextValue (signature arity) .base context)) :
    equationKitInterface arity opened source ⟶ equationKitInterface arity opened target :=
  ⟨classContextArrow (signature arity) .base context, .context supported⟩

theorem equationKitValue_readout {opened : InstrumentObservations.Policy Symbols} {sort : Srt Symbols arity}
    (value : Class (signature arity) (.base : Srt Symbols arity) sort)
    (supported : KitSupported arity opened (Padding.value (signature arity) .base value)) :
    (kitNormalization arity opened).map (equationKitValue arity value supported) =
      kitValue arity (Padding.value (signature arity) .base value) supported := rfl

theorem equationKitContext_readout {opened : InstrumentObservations.Policy Symbols} {source target : Srt Symbols arity}
    (context : ContextClass (signature arity) (.base : Srt Symbols arity) source target)
    (supported : KitContext arity opened (contextValue (signature arity) .base context)) :
    (kitNormalization arity opened).map (equationKitContext arity context supported) =
      kitContext arity (contextValue (signature arity) .base context) supported := rfl

end Mettapedia.OSLF.Framework.InstrumentCutContexts
