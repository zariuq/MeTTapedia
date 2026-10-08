import Mettapedia.OSLF.Framework.InstrumentCutKitEquationMonotonicity
import Mettapedia.OSLF.Framework.InstrumentCutKitEquationControls

/-!
# Binary firing, complete old targets and a genuinely new quotient label

The smaller kit opens the binary source cut, retaining both differently
coloured children. Every larger-kit firing at its supplied padded source and
actual Ask label recovers the same complete quotient target in the old kit.
The expansion also admits a nullary leaf Ask with a real firing; that whole
label has no preimage in the smaller category, even modulo padding equations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutKitEquationMonotonicityControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.OSLF.SortedConstructors.Padding
open Mettapedia.GSLT.RedexRelativeCongruence
open InstrumentCutContexts InstrumentCutContextControls InstrumentCutKitControls
open InstrumentCutKitEquationControls

local instance instrumentCutKitEquationMonotonicityControlsQuiver : Quiver (Srt Symbol arity) := frameQuiver sig

def cutOnlyKit : InstrumentObservations.Policy Symbol := fun constructor => constructor = .cut

theorem cutOnly_expansion : ∀ constructor, cutOnlyKit constructor → cutKit constructor := by
  intro constructor permission
  cases permission
  exact Or.inr rfl

def oldPaddedAgent : equationKitOrigin arity cutOnlyKit ⟶ equationKitInterface arity cutOnlyKit .base :=
  equationKitValue arity (classOf paddedBody) (by
    change KitSupported arity cutOnlyKit (Padding.normalize sig .base paddedBody)
    rw [padded_body_source_readout]
    exact embedSource_kitSupported arity cutOnlyKit properRule.redex)

def oldAsk : equationKitInterface arity cutOnlyKit .base ⟶
    equationKitInterface arity cutOnlyKit (.arguments Symbol.cut) :=
  equationKitContext arity (contextClassOf (embedContext sig .base (probeContext arity (.ask Symbol.cut)))) (by
    change KitContext arity cutOnlyKit (normalizeContext sig .base (embedContext sig .base (probeContext arity (.ask Symbol.cut))))
    rw [normalize_embedContext]
    exact .cons (.nil _) (kit_probeFrame_supported arity cutOnlyKit (.ask Symbol.cut) rfl))

theorem arguments_supported_in_old_kit (position : Fin 2) : KitSupported arity cutOnlyKit (arguments position) := by
  fin_cases position
  · change KitSupported arity cutOnlyKit (leaf false)
    exact source_leaf_readout false ▸ embedSource_kitSupported arity cutOnlyKit (sourceLeaf false)
  · change KitSupported arity cutOnlyKit (leaf true)
    exact source_leaf_readout true ▸ embedSource_kitSupported arity cutOnlyKit (sourceLeaf true)

def oldOutput : equationKitOrigin arity cutOnlyKit ⟶
    equationKitInterface arity cutOnlyKit (.arguments Symbol.cut) :=
  equationKitValue arity (classOf rawOutput) (by
    change KitSupported arity cutOnlyKit (Padding.normalize sig .base (embed sig .base (bundle arity Symbol.cut arguments)))
    rw [normalize_embed]
    exact kitSupported_bundle arity cutOnlyKit Symbol.cut rfl arguments arguments_supported_in_old_kit)

theorem mapped_old_padded_agent : (equationKitExpansion arity cutOnly_expansion).map oldPaddedAgent = paddedAgent :=
  Subtype.ext rfl

theorem mapped_old_ask : (equationKitExpansion arity cutOnly_expansion).map oldAsk = quotientAsk :=
  Subtype.ext rfl

theorem mapped_old_output : (equationKitExpansion arity cutOnly_expansion).map oldOutput = quotientOutput :=
  Subtype.ext rfl

set_option backward.isDefEq.respectTransparency false in
theorem actual_old_binary_ask_firing :
    ActIPO (equationKitRules arity Bool cutOnlyKit (fun rule => rule = properRule)) oldAsk oldPaddedAgent oldOutput := by
  have newStep : ActIPO (equationKitRules arity Bool cutKit (fun rule => rule = properRule))
      ((equationKitExpansion arity cutOnly_expansion).map oldAsk)
      ((equationKitExpansion arity cutOnly_expansion).map oldPaddedAgent)
      ((equationKitExpansion arity cutOnly_expansion).map oldOutput) := by
    rw [mapped_old_ask, mapped_old_padded_agent, mapped_old_output]
    exact padded_ask_actualIPO
  obtain ⟨recovered, same, _, oldStep⟩ := equationKit_step_reflect arity cutOnly_expansion newStep
  have recoveredEqual : recovered = oldOutput := (equationKitExpansion arity cutOnly_expansion).map_injective same
  exact recoveredEqual ▸ oldStep

/-- No target-shape hypothesis is supplied: support follows from the actual
old source, old label and full larger firing. -/
theorem every_supplied_binary_result_recovers_its_old_equation_arrow
    (target : equationKitOrigin arity cutKit ⟶
      (equationKitExpansion arity cutOnly_expansion).obj (equationKitInterface arity cutOnlyKit (.arguments Symbol.cut)))
    (step : ActIPO (equationKitRules arity Bool cutKit (fun rule => rule = properRule))
      ((equationKitExpansion arity cutOnly_expansion).map oldAsk)
      ((equationKitExpansion arity cutOnly_expansion).map oldPaddedAgent) target) :
    ∃ oldTarget : equationKitOrigin arity cutOnlyKit ⟶ equationKitInterface arity cutOnlyKit (.arguments Symbol.cut),
      oldTarget.val = target.val ∧ (equationKitExpansion arity cutOnly_expansion).map oldTarget = target ∧
        ActIPO (equationKitRules arity Bool cutOnlyKit (fun rule => rule = properRule)) oldAsk oldPaddedAgent oldTarget := by
  obtain ⟨oldTarget, mapped, wholeArrow, oldStep⟩ := equationKit_step_reflect arity cutOnly_expansion step
  exact ⟨oldTarget, wholeArrow, mapped, oldStep⟩

set_option backward.isDefEq.respectTransparency false in
theorem actual_padding_relation_restricts_to_old_kit :
    IPOBisimilar (equationKitRules arity Bool cutOnlyKit (fun rule => rule = properRule))
      oldPaddedAgent (quotientSource cutOnlyKit properRule.redex) := by
  apply equationKit_bisimulation_monotone arity cutOnly_expansion
  rw [mapped_old_padded_agent]
  have sourceMapped : (equationKitExpansion arity cutOnly_expansion).map
      (quotientSource cutOnlyKit properRule.redex) = quotientSource cutKit properRule.redex := Subtype.ext rfl
  rw [sourceMapped]
  exact (padded_complete_source_reconstruction properRule.redex).mpr rfl

def newLeafAsk : equationKitInterface arity cutKit .base ⟶
    equationKitInterface arity cutKit (.arguments (.leaf false)) :=
  equationKitContext arity (contextClassOf (embedContext sig .base (probeContext arity (.ask (.leaf false))))) (by
    change KitContext arity cutKit (normalizeContext sig .base (embedContext sig .base (probeContext arity (.ask (.leaf false)))))
    rw [normalize_embedContext]
    exact .cons (.nil _) (kit_probeFrame_supported arity cutKit (.ask (.leaf false)) (fullKit_permission _)))

def newLeafOutput : equationKitOrigin arity cutKit ⟶ equationKitInterface arity cutKit (.arguments (.leaf false)) :=
  equationKitValue arity (classOf (embed sig .base (bundle arity (.leaf false) (fun position => Fin.elim0 position)))) (by
    change KitSupported arity cutKit (Padding.normalize sig .base
      (embed sig .base (bundle arity (.leaf false) (fun position => Fin.elim0 position))))
    rw [normalize_embed]
    exact kitSupported_bundle arity cutKit (.leaf false) (fullKit_permission _) _ (fun position => Fin.elim0 position))

set_option backward.isDefEq.respectTransparency false in
theorem newly_admitted_leaf_label_actually_fires :
    ActIPO (equationKitRules arity Bool cutKit (fun rule => rule = properRule)) newLeafAsk
      (quotientSource cutKit (sourceLeaf false)) newLeafOutput := by
  apply (equationKit_step_iff arity Bool cutKit _ _ _ _).mpr
  apply (kit_category_step_iff arity Bool cutKit _ _ _ _).mpr
  change ActIPO (kitRules arity Bool cutKit (fun rule => rule = properRule))
    (contextArrow sig (normalizeContext sig .base (embedContext sig .base (probeContext arity (.ask (.leaf false))))))
    (termArrow sig (Padding.normalize sig .base (embed sig .base (embedSource arity (sourceLeaf false)))))
    (termArrow sig (Padding.normalize sig .base (embed sig .base (bundle arity (.leaf false) (fun position => Fin.elim0 position)))))
  rw [normalize_embedContext, normalize_embed, normalize_embed, source_leaf_readout]
  let receipt : KitFiringReceipt arity Bool cutKit (.ask (.leaf false)) (leaf false)
      (bundle arity (.leaf false) (fun position => Fin.elim0 position)) :=
    ⟨⟨false, .ask (Symbol.leaf false) (fun position => Fin.elim0 position)⟩, fullKit_permission _, rfl, rfl⟩
  exact receipt.step arity _

theorem new_leaf_label_has_no_old_quotient_preimage :
    ¬ ∃ oldLabel : equationKitInterface arity cutOnlyKit .base ⟶
        equationKitInterface arity cutOnlyKit (.arguments (.leaf false)),
      (equationKitExpansion arity cutOnly_expansion).map oldLabel = newLeafAsk := by
  rintro ⟨oldLabel, same⟩
  have classes := congrArg (fun arrow : equationKitInterface arity cutKit .base ⟶
    equationKitInterface arity cutKit (.arguments (.leaf false)) => arrow.val) same
  change oldLabel.val = newLeafAsk.val at classes
  have normalized := congrArg ((normalizationFunctor sig .base).map) classes
  have supported := oldLabel.property
  rw [normalized] at supported
  change KitArrow arity cutOnlyKit (contextArrow sig
    (normalizeContext sig .base (embedContext sig .base (probeContext arity (.ask (.leaf false)))))) at supported
  rw [normalize_embedContext] at supported
  cases supported with
  | context supported =>
    cases supported with
    | cons previous frameSupported =>
      have constructorSupported := frameSupported.1
      change KitConstructor arity cutOnlyKit (Constructor.cut (.ask (.leaf false))) at constructorSupported
      cases constructorSupported with
      | cut instrument permission =>
        change Symbol.leaf false = Symbol.cut at permission
        cases permission

end Mettapedia.OSLF.Framework.InstrumentCutKitEquationMonotonicityControls
