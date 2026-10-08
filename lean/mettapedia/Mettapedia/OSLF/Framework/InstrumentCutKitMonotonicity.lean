import Mettapedia.OSLF.Framework.InstrumentCutKitTransitions

/-!
# Instrument-set monotonicity for the actual supported IPO systems

Increasing a kit embeds its entire typed context category. The inclusion
preserves and reflects IPOs by the earned ambient candidate comparison.
Matched larger-kit firings along an old supported label recover their old
permission and complete old target. Restricting the bisimulation family then
proves the downward implication for every old label and interface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutKitMonotonicityQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

variable {first second : InstrumentObservations.Policy Symbols}
variable (larger : ∀ constructor, first constructor → second constructor)
include larger

theorem KitConstructor.monotone {constructor : Constructor Symbols arity}
    (supported : KitConstructor arity first constructor) : KitConstructor arity second constructor := by
  cases supported with
  | original constructor => exact .original constructor
  | arguments constructor permission => exact .arguments constructor (larger _ permission)
  | probe instrument permission => exact .probe instrument (larger _ permission)
  | cut instrument permission => exact .cut instrument (larger _ permission)

theorem KitSupported.monotone {sort : Srt Symbols arity} {value : Value arity sort}
    (supported : KitSupported arity first value) : KitSupported arity second value := by
  refine @Term.rec (signature arity)
    (fun _ value => KitSupported arity first value → KitSupported arity second value)
    ?_ sort value supported
  intro constructor children inductionHypothesis supported
  exact ⟨supported.1.monotone arity larger,
    fun position => inductionHypothesis position (supported.2 position)⟩

theorem KitFrame.monotone {source target : Srt Symbols arity}
    {frame : Frame (signature arity) source target} (supported : KitFrame arity first frame) :
    KitFrame arity second frame := by
  refine @Frame.casesOn (signature arity)
    (fun _ _ frame => KitFrame arity first frame → KitFrame arity second frame)
    source target frame ?_ supported
  intro constructor position siblings supported
  exact ⟨supported.1.monotone arity larger,
    fun other different => (supported.2 other different).monotone arity larger⟩

theorem KitContext.monotone {source target : Srt Symbols arity}
    {context : Context (signature arity) source target} (supported : KitContext arity first context) :
    KitContext arity second context := by
  induction supported with
  | nil => exact .nil _
  | cons previous frame inductionHypothesis => exact .cons inductionHypothesis (frame.monotone arity larger)

theorem KitArrow.monotone {source target : ContextObject (signature arity)} {arrow : source ⟶ target}
    (supported : KitArrow arity first arrow) : KitArrow arity second arrow := by
  cases supported with
  | identity => exact .identity
  | value supported => exact .value (supported.monotone arity larger)
  | context supported => exact .context (supported.monotone arity larger)

def kitExpansion : KitObject arity first ⥤ KitObject arity second where
  obj object := ⟨object.base⟩
  map arrow := ⟨arrow.val, arrow.property.monotone arity larger⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem kitExpansion_ambient : kitExpansion arity larger ⋙ kitInclusion arity second =
    kitInclusion arity first := rfl

instance kitExpansion_faithful : (kitExpansion arity larger).Faithful where
  map_injective := by
    intro source target firstArrow secondArrow same
    apply Subtype.ext
    exact congrArg (fun arrow : (kitExpansion arity larger).obj source ⟶
      (kitExpansion arity larger).obj target => arrow.val) same

theorem kitExpansion_idemPushout_iff {W X Y Z : KitObject arity first}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (square : f ≫ h = g ≫ i) :
    IsIdemPushout f g h i square ↔
      IsIdemPushout ((kitExpansion arity larger).map f) ((kitExpansion arity larger).map g)
        ((kitExpansion arity larger).map h) ((kitExpansion arity larger).map i)
        (by rw [← Functor.map_comp, square, Functor.map_comp]) := by
  have ambient : f.val ≫ h.val = g.val ≫ i.val :=
    congrArg (fun arrow : W ⟶ Z => arrow.val) square
  have mapped : (kitExpansion arity larger).map f ≫ (kitExpansion arity larger).map h =
      (kitExpansion arity larger).map g ≫ (kitExpansion arity larger).map i := Subtype.ext ambient
  exact (kit_idemPushout_iff arity square).trans (kit_idemPushout_iff arity mapped).symm

theorem kit_category_step_monotone {Origins : Type w} {proper : SourceRule arity → Prop}
    {sourceInterface targetInterface : KitObject arity first}
    {label : sourceInterface ⟶ targetInterface} {source : kitOrigin arity first ⟶ sourceInterface}
    {target : kitOrigin arity first ⟶ targetInterface}
    (step : ActIPO (kitCategoryRules arity Origins first proper) label source target) :
    ActIPO (kitCategoryRules arity Origins second proper) ((kitExpansion arity larger).map label)
      ((kitExpansion arity larger).map source) ((kitExpansion arity larger).map target) :=
  (kit_category_step_iff arity Origins second proper _ _ _).mpr
    (kit_step_monotone arity larger ((kit_category_step_iff arity Origins first proper _ _ _).mp step))

/-- Reflection supplies the actual old target and its whole mapped arrow.
The larger firing's occurrence, origin, reaction context and IPO are retained
by `kit_step_support_recover`, rather than replaced by a support-only result. -/
theorem kit_category_step_reflect {Origins : Type w} {proper : SourceRule arity → Prop}
    {sourceInterface targetInterface : KitObject arity first}
    {label : sourceInterface ⟶ targetInterface} {source : kitOrigin arity first ⟶ sourceInterface}
    {target : kitOrigin arity second ⟶ (kitExpansion arity larger).obj targetInterface}
    (step : ActIPO (kitCategoryRules arity Origins second proper) ((kitExpansion arity larger).map label)
      ((kitExpansion arity larger).map source) target) :
    ∃ oldTarget : kitOrigin arity first ⟶ targetInterface,
      (kitExpansion arity larger).map oldTarget = target ∧
        ActIPO (kitCategoryRules arity Origins first proper) label source oldTarget := by
  have ambient := (kit_category_step_iff arity Origins second proper _ _ _).mp step
  obtain ⟨supported, oldStep⟩ := kit_step_old_label_target_closure arity source.property label.property ambient
  let oldTarget : kitOrigin arity first ⟶ targetInterface := ⟨target.val, supported⟩
  exact ⟨oldTarget, Subtype.ext rfl,
    (kit_category_step_iff arity Origins first proper label source oldTarget).mpr oldStep⟩

/-- Bisimulation is restricted across the genuine grammar inclusion. Its
matching obligations quantify all old labels, not only selected probes. -/
theorem kit_bisimulation_monotone {Origins : Type w} {proper : SourceRule arity → Prop}
    {interface : KitObject arity first} {left right : kitOrigin arity first ⟶ interface}
    (related : IPOBisimilar (kitCategoryRules arity Origins second proper)
      ((kitExpansion arity larger).map left) ((kitExpansion arity larger).map right)) :
    IPOBisimilar (kitCategoryRules arity Origins first proper) left right := by
  let relation : (interface : KitObject arity first) →
      (kitOrigin arity first ⟶ interface) → (kitOrigin arity first ⟶ interface) → Prop :=
    fun _ firstAgent secondAgent => IPOBisimilar (kitCategoryRules arity Origins second proper)
      ((kitExpansion arity larger).map firstAgent) ((kitExpansion arity larger).map secondAgent)
  refine ⟨relation, ?_, related⟩
  intro current firstAgent secondAgent currentRelated
  constructor
  · intro nextInterface label next step
    have newStep := kit_category_step_monotone arity larger step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_forward currentRelated newStep
    obtain ⟨oldMatched, readout, oldStep⟩ := kit_category_step_reflect arity larger matchedStep
    refine ⟨oldMatched, oldStep, ?_⟩
    change IPOBisimilar (kitCategoryRules arity Origins second proper)
      ((kitExpansion arity larger).map next) ((kitExpansion arity larger).map oldMatched)
    exact readout.symm ▸ successors
  · intro nextInterface label next step
    have newStep := kit_category_step_monotone arity larger step
    obtain ⟨matched, matchedStep, successors⟩ := ipoBisimilar_backward currentRelated newStep
    obtain ⟨oldMatched, readout, oldStep⟩ := kit_category_step_reflect arity larger matchedStep
    refine ⟨oldMatched, oldStep, ?_⟩
    change IPOBisimilar (kitCategoryRules arity Origins second proper)
      ((kitExpansion arity larger).map oldMatched) ((kitExpansion arity larger).map next)
    exact readout.symm ▸ successors

end Mettapedia.OSLF.Framework.InstrumentCutContexts
