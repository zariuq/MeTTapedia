import Mettapedia.OSLF.Framework.InstrumentCutKitEquationComparison

/-!
# All-label kit expansion on independently generated equation arrows

Policy expansion keeps each whole equation class. Its square with the earned
normalization functors commutes. Every firing at an old source and old label
recovers an old supported target with exactly the supplied quotient arrow;
the reaction's existing rule, occurrence and IPO are retained. Consequently
larger-kit bisimulation implies old-kit bisimulation at every interface and
literal label, independently of the supplied padding representatives.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutKitEquationMonotonicityQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

variable {first second third : InstrumentObservations.Policy Symbols}
variable (larger : ∀ constructor, first constructor → second constructor)
include larger

def equationKitExpansion : EquationKitObject arity first ⥤ EquationKitObject arity second where
  obj object := ⟨object.base⟩
  map arrow := ⟨arrow.val, arrow.property.monotone arity larger⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance equationKitExpansion_faithful : (equationKitExpansion arity larger).Faithful where
  map_injective := by
    intro source target before after same
    apply Subtype.ext
    exact congrArg (fun arrow : (equationKitExpansion arity larger).obj source ⟶
      (equationKitExpansion arity larger).obj target => arrow.val) same

theorem equationKitExpansion_normalization :
    equationKitExpansion arity larger ⋙ kitNormalization arity second =
      kitNormalization arity first ⋙ kitExpansion arity larger := rfl

omit larger in
theorem equationKitExpansion_identity (opened : InstrumentObservations.Policy Symbols) :
    equationKitExpansion arity (fun constructor (permission : opened constructor) => permission) =
      𝟭 (EquationKitObject arity opened) := rfl

theorem equationKitExpansion_composition (further : ∀ constructor, second constructor → third constructor) :
    equationKitExpansion arity (fun constructor permission => further constructor (larger constructor permission)) =
      equationKitExpansion arity larger ⋙ equationKitExpansion arity further := rfl

theorem equationKit_step_monotone {Origins : Type w} {proper : SourceRule arity → Prop}
    {sourceInterface targetInterface : EquationKitObject arity first}
    {label : sourceInterface ⟶ targetInterface} {source : equationKitOrigin arity first ⟶ sourceInterface}
    {target : equationKitOrigin arity first ⟶ targetInterface}
    (step : ActIPO (equationKitRules arity Origins first proper) label source target) :
    ActIPO (equationKitRules arity Origins second proper) ((equationKitExpansion arity larger).map label)
      ((equationKitExpansion arity larger).map source) ((equationKitExpansion arity larger).map target) := by
  apply (equationKit_step_iff arity Origins second proper _ _ _).mpr
  exact kit_category_step_monotone arity larger
    ((equationKit_step_iff arity Origins first proper label source target).mp step)

/-- The old target uses the identical supplied equation arrow. The only
newly reconstructed datum is its earned old hereditary support proof. -/
theorem equationKit_step_reflect {Origins : Type w} {proper : SourceRule arity → Prop}
    {sourceInterface targetInterface : EquationKitObject arity first}
    {label : sourceInterface ⟶ targetInterface} {source : equationKitOrigin arity first ⟶ sourceInterface}
    {target : equationKitOrigin arity second ⟶ (equationKitExpansion arity larger).obj targetInterface}
    (step : ActIPO (equationKitRules arity Origins second proper) ((equationKitExpansion arity larger).map label)
      ((equationKitExpansion arity larger).map source) target) :
    ∃ oldTarget : equationKitOrigin arity first ⟶ targetInterface,
      (equationKitExpansion arity larger).map oldTarget = target ∧
        oldTarget.val = target.val ∧ ActIPO (equationKitRules arity Origins first proper) label source oldTarget := by
  have normalStep := (equationKit_step_iff arity Origins second proper _ _ _).mp step
  have ambient := (kit_category_step_iff arity Origins second proper _ _ _).mp normalStep
  obtain ⟨supported, oldStep⟩ := kit_step_old_label_target_closure arity source.property label.property ambient
  let oldTarget : equationKitOrigin arity first ⟶ targetInterface := ⟨target.val, supported⟩
  refine ⟨oldTarget, Subtype.ext rfl, rfl, ?_⟩
  apply (equationKit_step_iff arity Origins first proper label source oldTarget).mpr
  exact (kit_category_step_iff arity Origins first proper _ _ _).mpr oldStep

theorem equationKit_bisimulation_monotone {Origins : Type w} {proper : SourceRule arity → Prop}
    {interface : EquationKitObject arity first} {left right : equationKitOrigin arity first ⟶ interface}
    (related : IPOBisimilar (equationKitRules arity Origins second proper)
      ((equationKitExpansion arity larger).map left) ((equationKitExpansion arity larger).map right)) :
    IPOBisimilar (equationKitRules arity Origins first proper) left right := by
  have normalRelated := (equationKit_bisimilar_iff arity Origins second proper _ _).mp related
  apply (equationKit_bisimilar_iff arity Origins first proper left right).mpr
  exact kit_bisimulation_monotone arity larger normalRelated

end Mettapedia.OSLF.Framework.InstrumentCutContexts
