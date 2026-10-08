import Mettapedia.OSLF.Framework.InstrumentCutKitCategoryObservations
import Mettapedia.OSLF.Framework.InstrumentCutContextControls

/-!
# Kit grammar, complete firing, origin and proper-future controls

The binary source cut keeps two different supplied leaves. Proper firing
separates two presently opaque sources, so independent partial-view equality
does not characterize the complete reactive bisimulation. Unavailable argument
frames still form ambient IPOs, but are rejected by the actual kit grammar.
Repeated receipt origins and empty-origin failure remain explicit.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutKitControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence
open InstrumentCutContexts InstrumentCutContextControls

local instance instrumentCutKitControlsQuiver : Quiver (Srt Symbol arity) := frameQuiver sig

def falseLeafKit : InstrumentObservations.Policy Symbol := fun constructor => constructor = .leaf false

theorem fullKit_permission (constructor : Symbol) : cutKit constructor := by
  cases constructor with
  | leaf color => exact Or.inl ⟨color, rfl⟩
  | cut => exact Or.inr rfl

theorem falseLeaf_expansion : ∀ constructor, falseLeafKit constructor → cutKit constructor := by
  intro constructor permission
  cases permission
  exact Or.inl ⟨false, rfl⟩

theorem every_source_fully_opened (source : InstrumentObservations.Tree Symbol arity) : FullyOpened arity cutKit source := by
  induction source with
  | node constructor children inductionHypothesis => exact ⟨fullKit_permission constructor, inductionHypothesis⟩

theorem complete_source_reconstruction
    (other : InstrumentObservations.Tree Symbol arity) :
    IPOBisimilar (kitCategoryRules arity Bool cutKit (fun rule => rule = properRule))
      (kitSource arity cutKit properRule.redex) (kitSource arity cutKit other) ↔ properRule.redex = other :=
  kit_category_interactive_iff_equal arity Bool cutKit _ _ _ (every_source_fully_opened properRule.redex)

def firstKitReceipt : KitFiringReceipt arity Bool cutKit (.ask Symbol.cut) askInstance.body askInstance.output :=
  ⟨firstOccurrence, Or.inr rfl, rfl, rfl⟩

def secondKitReceipt : KitFiringReceipt arity Bool cutKit (.ask Symbol.cut) askInstance.body askInstance.output :=
  ⟨secondOccurrence, Or.inr rfl, rfl, rfl⟩

theorem duplicate_kit_origins_are_retained : firstKitReceipt ≠ secondKitReceipt := by
  intro same
  have origins := congrArg (fun receipt => receipt.occurrence.origin) same
  cases origins

theorem receipt_retains_both_children :
    firstKitReceipt.occurrence.instance_.body = originalCut arity sourceCut (leaf false) (leaf true) ∧
      firstKitReceipt.occurrence.instance_.output = bundle arity Symbol.cut arguments ∧
      arguments 0 = leaf false ∧ arguments 1 = leaf true := ⟨rfl, rfl, rfl, rfl⟩

theorem kit_receipt_actual_firing :
    ActIPO (kitRules arity Bool cutKit (fun rule => rule = properRule))
      (contextArrow sig (probeContext arity (.ask Symbol.cut)))
      (termArrow sig askInstance.body) (termArrow sig askInstance.output) :=
  firstKitReceipt.step arity _

theorem empty_origins_remove_the_same_firing :
    ¬ ActIPO (kitRules arity PEmpty cutKit (fun rule => rule = properRule))
      (contextArrow sig (probeContext arity (.ask Symbol.cut)))
      (termArrow sig askInstance.body) (termArrow sig askInstance.output) := by
  intro step
  obtain ⟨occurrence, _, _, _⟩ := (kit_probe_step_iff arity PEmpty cutKit _ _ _ _).mp step
  exact occurrence.origin.elim

theorem old_label_keeps_complete_target
    {target : kitOrigin arity cutKit ⟶
      (kitExpansion arity falseLeaf_expansion).obj (kitInterface arity falseLeafKit (.arguments (.leaf false)))}
    (step : ActIPO (kitCategoryRules arity Bool cutKit (fun rule => rule = properRule))
      ((kitExpansion arity falseLeaf_expansion).map (kitProbeContext arity falseLeafKit (.ask (.leaf false)) rfl))
      ((kitExpansion arity falseLeaf_expansion).map (kitSource arity falseLeafKit (sourceLeaf false))) target) :
    ∃ oldTarget : kitOrigin arity falseLeafKit ⟶ kitInterface arity falseLeafKit (.arguments (.leaf false)),
      (kitExpansion arity falseLeaf_expansion).map oldTarget = target ∧
        ActIPO (kitCategoryRules arity Bool falseLeafKit (fun rule => rule = properRule))
          (kitProbeContext arity falseLeafKit (.ask (.leaf false)) rfl)
          (kitSource arity falseLeafKit (sourceLeaf false)) oldTarget :=
  kit_category_step_reflect arity falseLeaf_expansion step

def foreignLeftFrame : Frame sig (.base : Srt Symbol arity) (.arguments Symbol.cut) :=
  Frame.slot (signature := sig) (Constructor.arguments Symbol.cut) (0 : Fin 2) (fun _ _ => leaf false)

def foreignRightFrame : Frame sig (.base : Srt Symbol arity) (.arguments Symbol.cut) :=
  Frame.slot (signature := sig) (Constructor.arguments Symbol.cut) (1 : Fin 2) (fun _ _ => leaf false)

theorem foreign_frames_differ : foreignLeftFrame ≠ foreignRightFrame := by
  intro same
  have positions := congrArg (fun frame : Frame sig (.base : Srt Symbol arity) (.arguments Symbol.cut) => frame.position.val) same
  change (0 : Nat) = 1 at positions
  omega

theorem foreign_frames_same_ground_readout : foreignLeftFrame.fill (leaf false) = foreignRightFrame.fill (leaf false) := by
  apply congrArg (Term.node (signature := sig) (Constructor.arguments Symbol.cut))
  funext position
  fin_cases position <;> rfl

theorem foreign_frames_actual_ambientIPO :
    IsIdemPushout (termArrow sig (leaf false)) (termArrow sig (leaf false))
      (contextArrow sig (@Quiver.Hom.toPath (Srt Symbol arity) (frameQuiver sig) _ _ foreignLeftFrame))
      (contextArrow sig (@Quiver.Hom.toPath (Srt Symbol arity) (frameQuiver sig) _ _ foreignRightFrame))
      (congrArg (termArrow sig) foreign_frames_same_ground_readout) :=
  distinct_single_frames_ipo (action sig) foreignLeftFrame foreignRightFrame foreign_frames_differ
    (leaf false) (leaf false) (congrArg (termArrow sig) foreign_frames_same_ground_readout)

theorem unavailable_argument_frame_rejected : ¬ KitFrame arity falseLeafKit foreignLeftFrame := by
  intro supported
  cases supported.1 with
  | arguments _ permission => cases permission

theorem partial_views_same_before_proper_firing :
    InstrumentObservations.view falseLeafKit properRule.redex =
      InstrumentObservations.view falseLeafKit (sourceLeaf true) := by
  simp [InstrumentObservations.view, falseLeafKit, properRule, sourceLeaf]

theorem proper_firing_in_actual_small_kit :
    ActIPO (kitCategoryRules arity Bool falseLeafKit (fun rule => rule = properRule))
      (𝟙 (kitInterface arity falseLeafKit .base))
      (kitSource arity falseLeafKit properRule.redex) (kitSource arity falseLeafKit properRule.reactum) := by
  apply (kit_category_step_iff arity Bool falseLeafKit _ _ _ _).mpr
  refine ⟨properRule.reaction, Or.inr ⟨properRule, rfl, rfl⟩, 𝟙 _, rfl, ?_, rfl⟩
  exact ground_identityReactionIPO (action sig) (embedSource arity properRule.redex)
    (embedSource arity properRule.redex) .nil rfl

set_option backward.isDefEq.respectTransparency false in
theorem opaque_leaf_has_no_proper_identity_firing
    (target : kitOrigin arity falseLeafKit ⟶ kitInterface arity falseLeafKit .base) :
    ¬ ActIPO (kitCategoryRules arity Bool falseLeafKit (fun rule => rule = properRule))
      (𝟙 (kitInterface arity falseLeafKit .base)) (kitSource arity falseLeafKit (sourceLeaf true)) target := by
  intro step
  obtain ⟨rule, membership, reaction, square, _, _⟩ :=
    (kit_category_step_iff arity Bool falseLeafKit _ _ _ _).mp step
  rcases membership with ⟨instrument, occurrence, _, rfl⟩ | ⟨sourceRule, rfl, rfl⟩
  · cases reaction with
    | context path =>
      have outputPure : sourcePure arity ((action sig).path path
          (cut arity instrument (probe arity instrument) occurrence.instance_.body)) := by
        have readout := (Arrow.value.inj square).symm
        rw [readout]
        change sourcePure arity (embedSource arity (sourceLeaf true))
        exact embedSource_pure arity (sourceLeaf true)
      exact (administrative_redex_not_pure arity instrument occurrence.instance_
        (sourcePure_context arity path _ outputPure)).elim
  · cases reaction with
    | context path =>
      have readout : (action sig).path path (embedSource arity properRule.redex) =
          embedSource arity (sourceLeaf true) := (Arrow.value.inj square).symm
      cases path with
      | nil =>
        have heads := Term.head_eq (signature := sig) _ _ readout
        cases heads
      | cons previous frame =>
        obtain ⟨position, _, _, _⟩ := source_frame_fill_lift arity frame
          ((action sig).path previous (embedSource arity properRule.redex)) (Symbol.leaf true)
          (fun index => Fin.elim0 index) readout
        exact position.elim0

/-- An independently equal root view fails the complete future-sensitive
reactive comparison. Both terms have actual supported arrows in the kit. -/
theorem partial_view_kernel_is_not_full_bisimulation :
    ¬ IPOBisimilar (kitCategoryRules arity Bool falseLeafKit (fun rule => rule = properRule))
      (kitSource arity falseLeafKit properRule.redex) (kitSource arity falseLeafKit (sourceLeaf true)) := by
  intro related
  obtain ⟨matched, response, _⟩ := ipoBisimilar_forward related proper_firing_in_actual_small_kit
  exact opaque_leaf_has_no_proper_identity_firing matched response

end Mettapedia.OSLF.Framework.InstrumentCutKitControls
