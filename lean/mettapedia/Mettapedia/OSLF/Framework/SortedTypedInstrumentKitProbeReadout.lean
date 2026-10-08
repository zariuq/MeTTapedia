import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitFiringComparison
import Mettapedia.OSLF.Framework.SortedTypedInstrumentOriginalProbeTargetSupport

/-!
# Complete probe readings in an actual typed instrument kit

The kit label is the supplied probe context with independently derived
hereditary support. Its actual ask and get IPO steps retain the whole
heterogeneous tuple. Original source declarations are independently indexed;
their mapped firings are compared to the full combined family only after
the actual declaration is read. A pure get successor then excludes the
original alternative, including source unit rules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}

def sourceRuleFamily
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    (rule : ReactionRule (.origin : SourceCategory source Parallel)) : Prop :=
  ∃ index, originalRules index = rule

theorem ambient_rule_combined (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {rule : ReactionRule (.origin : ContextCategory source Parallel)}
    (admitted : ambientRules (NativeOrigins := NativeOrigins) originalRules opened rule) :
    combinedSourceRules (sourceRuleFamily originalRules) NativeOrigins rule := by
  obtain ⟨declaration, rfl⟩ := admitted
  cases declaration with
  | original index =>
    exact Or.inr ⟨originalRules index, ⟨index, rfl⟩, rfl⟩
  | administrative occurrence permitted => exact Or.inl ⟨occurrence, rfl⟩

theorem ambient_step_combined (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : ContextCategory source Parallel}
    {agent : (.origin : ContextCategory source Parallel) ⟶ before} {label : before ⟶ after}
    {target : (.origin : ContextCategory source Parallel) ⟶ after}
    (step : ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules opened) label agent target) :
    ActIPO (combinedSourceRules (sourceRuleFamily originalRules) NativeOrigins) label agent target := by
  obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := step
  exact ⟨rule, ambient_rule_combined opened originalRules admitted, reaction, square, minimal, output⟩

theorem category_step_combined (opened : Policy source Parallel)
    (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))
    {before after : Object opened} {agent : origin opened ⟶ before} {label : before ⟶ after}
    {target : origin opened ⟶ after}
    (step : ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) label agent target) :
    ActIPO (combinedSourceRules (sourceRuleFamily originalRules) NativeOrigins) label.val agent.val target.val :=
  ambient_step_combined opened originalRules ((category_step_iff opened originalRules _ _ _).mp step)

theorem probeContext_supported (opened : Policy source Parallel) (instrument : Probe source Parallel)
    (permission : opened (instrumentHead instrument)) : ContextSupported opened (probeContext instrument) := by
  apply ContextSupported.frame (.cut instrument permission) ?_ (.hole _)
  intro position different
  fin_cases position
  · exact (probe_supported_iff opened instrument).mpr permission
  · exact (different rfl).elim

def probeArrow (opened : Policy source Parallel) (instrument : Probe source Parallel)
    (permission : opened (instrumentHead instrument)) :
    interface opened (receiver instrument) ⟶ interface opened (result instrument) :=
  context (contextClassOf (probeContext instrument))
    ⟨probeContext instrument, probeContext_supported opened instrument permission, rfl⟩

theorem probeArrow_val (opened : Policy source Parallel) (instrument : Probe source Parallel)
    (permission : opened (instrumentHead instrument)) :
    (probeArrow opened instrument permission).val = SortedTypedInstruments.probeLabel instrument := rfl

variable (opened : Policy source Parallel)
  (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))

theorem permitted_ambient_step (occurrence : Occurrence source Parallel NativeOrigins)
    (permitted : Permitted opened occurrence) :
    ActIPO (ambientRules (NativeOrigins := NativeOrigins) originalRules opened)
      occurrence.label occurrence.agent occurrence.target := by
  exact ⟨occurrence.rule, ⟨.administrative occurrence permitted, rfl⟩, 𝟙 _,
    occurrence.complete_probe_square.trans (Category.comp_id occurrence.rule.redex).symm,
    raw_right_identity_isIPO _ occurrence.complete_probe_square,
    (Category.comp_id occurrence.rule.reactum).symm⟩

theorem ask_step (origin : NativeOrigins) (head : SourceHead source Parallel) (arguments : Arguments head)
    (permission : opened head) (children : ∀ position, Supported opened (arguments position)) :
    ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (probeArrow opened (.ask head) permission)
      (value (classOf (sourceNode head arguments))
        ⟨_, (sourceNode_supported_iff opened head arguments).mpr children, rfl⟩)
      (value (classOf (bundle head arguments))
        ⟨_, (bundle_supported_iff opened head arguments).mpr ⟨permission, children⟩, rfl⟩) :=
  (category_step_iff opened originalRules _ _ _).mpr
    (permitted_ambient_step opened originalRules (.ask origin head arguments) ⟨permission, children⟩)

theorem get_step (origin : NativeOrigins) (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) (permission : opened head)
    (children : ∀ other, Supported opened (arguments other)) :
    ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (probeArrow opened (.get head position) permission)
      (value (classOf (bundle head arguments))
        ⟨_, (bundle_supported_iff opened head arguments).mpr ⟨permission, children⟩, rfl⟩)
      (value (classOf (arguments position)) ⟨_, children position, rfl⟩) :=
  (category_step_iff opened originalRules _ _ _).mpr
    (permitted_ambient_step opened originalRules (.get origin head arguments position) ⟨permission, children⟩)

theorem ask_step_readout (head : SourceHead source Parallel) (permission : opened head)
    (before : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (beforeSupported : ClassSupported opened before)
    (after : ValueClass (source := source) (Parallel := Parallel) (.arguments head))
    (afterSupported : ClassSupported opened after)
    (step : ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (probeArrow opened (.ask head) permission) (value before beforeSupported) (value after afterSupported)) :
    ∃ _origin : NativeOrigins, ∃ arguments : Arguments head,
      before = classOf (sourceNode head arguments) ∧ after = classOf (bundle head arguments) :=
  (combined_ask_step_iff (sourceRuleFamily originalRules) head before after).mp
    (category_step_combined opened originalRules step)

theorem get_pure_result_readout (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) (permission : opened head)
    (children : ∀ other, Supported opened (arguments other))
    (after : ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position)))
    (afterSupported : ClassSupported opened after) (pure : classObserverCount after = 0)
    (step : ActIPO (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (probeArrow opened (.get head position) permission)
      (value (classOf (bundle head arguments))
        ⟨_, (bundle_supported_iff opened head arguments).mpr ⟨permission, children⟩, rfl⟩)
      (value after afterSupported)) :
    Nonempty NativeOrigins ∧ after = classOf (arguments position) :=
  combined_get_pure_result_readout (sourceRuleFamily originalRules) head arguments position after pure
    (category_step_combined opened originalRules step)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
