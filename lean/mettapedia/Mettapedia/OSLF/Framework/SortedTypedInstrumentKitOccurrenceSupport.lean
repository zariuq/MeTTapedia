import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitRPOComparison
import Mettapedia.OSLF.Framework.SortedTypedInstrumentFiring

/-!
# Complete occurrence support recovered from an actual typed redex

An administrative permission is attached to its authored instrument head,
and every supplied child must belong to the kit grammar. These independent
conditions are recovered from support of the whole redex class. They earn
support of the complete result for ask, get and build without replacing the
supplied origin, position or argument tuple.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}

theorem supported_node_iff (opened : Policy source Parallel)
    (constructor : Constructor source Parallel)
    (arguments : (position : Fin ((signature source Parallel).arity constructor)) →
      Value (source := source) (Parallel := Parallel) ((signature source Parallel).input constructor position)) :
    Supported opened (.node constructor arguments) ↔
      Allowed opened constructor ∧ ∀ position, Supported opened (arguments position) := by
  constructor
  · intro supported
    have zero := supported.weight_zero
    change constructorWeight opened constructor +
      (∑ position, HereditaryWeight.term (constructorWeight opened) (arguments position)) = 0 at zero
    obtain ⟨constructorZero, childrenZero⟩ := Nat.add_eq_zero_iff.mp zero
    refine ⟨(allowed_iff_weight_zero opened constructor).mpr constructorZero, ?_⟩
    intro position
    have bounded := Finset.single_le_sum
      (fun other _ => Nat.zero_le (HereditaryWeight.term (constructorWeight opened) (arguments other)))
      (Finset.mem_univ position)
    exact supported_of_weight_zero opened (arguments position) (by omega)
  · exact fun complete => .node complete.1 complete.2

theorem supported_parallel_iff (opened : Policy source Parallel) {sort : Srt source Parallel}
    (parallel : NativeParallel sort) (first second : Value (source := source) (Parallel := Parallel) sort) :
    Supported opened (.cut parallel first second) ↔ Supported opened first ∧ Supported opened second := by
  constructor
  · intro supported
    cases supported with
    | cut _ before after => exact ⟨before, after⟩
  · exact fun children => .cut parallel children.1 children.2

theorem classOf_supported_iff (opened : Policy source Parallel) {sort : Srt source Parallel}
    (supplied : Value (source := source) (Parallel := Parallel) sort) :
    ClassSupported opened (classOf supplied) ↔ Supported opened supplied := by
  rw [class_supported_iff_weight_zero, supported_iff_weight_zero]
  rfl

theorem value_arrow_supported_iff (opened : Policy source Parallel) {sort : Srt source Parallel}
    (supplied : Value (source := source) (Parallel := Parallel) sort) :
    ArrowSupported opened (RawArrow.value (classOf supplied) :
      (.origin : ContextCategory source Parallel) ⟶ .interface sort) ↔ Supported opened supplied := by
  rw [arrow_supported_iff_weight_zero, supported_iff_weight_zero]
  rfl

theorem sourceNode_supported_iff (opened : Policy source Parallel) (head : SourceHead source Parallel)
    (arguments : Arguments head) :
    Supported opened (sourceNode head arguments) ↔ ∀ position, Supported opened (arguments position) := by
  cases head with
  | ordinary constructor =>
    change Supported opened (.node (signature := signature source Parallel)
      (Parallel := NativeParallel) (Constructor.original constructor) arguments) ↔ _
    rw [supported_node_iff]
    exact ⟨fun complete => complete.2, fun children => ⟨.original constructor, children⟩⟩
  | properCut sort parallel =>
    change Supported opened (.cut (signature := signature source Parallel)
      (Parallel := NativeParallel) (sort := .original sort) parallel (arguments 0) (arguments 1)) ↔ _
    rw [supported_parallel_iff]
    constructor
    · intro children position
      fin_cases position
      · exact children.1
      · exact children.2
    · exact fun children => ⟨children 0, children 1⟩
  | unit sort parallel =>
    exact ⟨fun _ position => Fin.elim0 position, fun _ => .zero (sort := .original sort) parallel⟩

theorem bundle_supported_iff (opened : Policy source Parallel) (head : SourceHead source Parallel)
    (arguments : Arguments head) :
    Supported opened (bundle head arguments) ↔ opened head ∧ ∀ position, Supported opened (arguments position) := by
  change Supported opened (.node (signature := signature source Parallel)
    (Parallel := NativeParallel) (Constructor.arguments head) arguments) ↔ _
  rw [supported_node_iff]
  constructor
  · rintro ⟨allowed, children⟩
    cases allowed with
    | arguments _ permission => exact ⟨permission, children⟩
  · exact fun complete => ⟨.arguments head complete.1, complete.2⟩

theorem probe_supported_iff (opened : Policy source Parallel) (instrument : Probe source Parallel) :
    Supported opened (probe instrument) ↔ opened (instrumentHead instrument) := by
  change Supported opened (.node (signature := signature source Parallel)
    (Parallel := NativeParallel) (Constructor.probe instrument) (fun position => Fin.elim0 position)) ↔ _
  rw [supported_node_iff]
  constructor
  · rintro ⟨allowed, _⟩
    cases allowed with
    | probe _ permission => exact permission
  · exact fun permission => ⟨.probe instrument permission, fun position => Fin.elim0 position⟩

theorem cut_probe_supported_iff (opened : Policy source Parallel) (instrument : Probe source Parallel)
    (body : Value (source := source) (Parallel := Parallel) (receiver instrument)) :
    Supported opened (cut instrument (probe instrument) body) ↔
      opened (instrumentHead instrument) ∧ Supported opened body := by
  unfold cut
  rw [supported_node_iff]
  constructor
  · rintro ⟨allowed, children⟩
    have permission : opened (instrumentHead instrument) := by
      cases allowed with
      | cut _ permission => exact permission
    exact ⟨permission, children (Fin.succ (0 : Fin 1))⟩
  · rintro ⟨permission, bodySupported⟩
    refine ⟨.cut instrument permission, ?_⟩
    intro position
    fin_cases position
    · exact (probe_supported_iff opened instrument).mpr permission
    · exact bodySupported

def Permitted (opened : Policy source Parallel) : Occurrence source Parallel Origins → Prop
  | .ask _ head arguments => opened head ∧ ∀ position, Supported opened (arguments position)
  | .get _ head arguments _ => opened head ∧ ∀ position, Supported opened (arguments position)
  | .build _ head arguments => opened head ∧ ∀ position, Supported opened (arguments position)

theorem occurrence_redex_supported_iff (opened : Policy source Parallel)
    (occurrence : Occurrence source Parallel Origins) :
    ArrowSupported opened occurrence.rule.redex ↔ Permitted opened occurrence := by
  change ArrowSupported opened (RawArrow.value (classOf
    (cut occurrence.instrument (probe occurrence.instrument) occurrence.body))) ↔ _
  rw [value_arrow_supported_iff, cut_probe_supported_iff]
  cases occurrence with
  | ask origin head arguments =>
    change (opened head ∧ Supported opened (sourceNode head arguments)) ↔ _
    rw [sourceNode_supported_iff]
    rfl
  | get origin head arguments position =>
    change (opened head ∧ Supported opened (bundle head arguments)) ↔ _
    rw [bundle_supported_iff]
    exact ⟨fun complete => ⟨complete.1, complete.2.2⟩,
      fun complete => ⟨complete.1, complete⟩⟩
  | build origin head arguments =>
    change (opened head ∧ Supported opened (bundle head arguments)) ↔ _
    rw [bundle_supported_iff]
    exact ⟨fun complete => ⟨complete.1, complete.2.2⟩,
      fun complete => ⟨complete.1, complete⟩⟩

theorem occurrence_output_supported {opened : Policy source Parallel}
    {occurrence : Occurrence source Parallel Origins} (permitted : Permitted opened occurrence) :
    Supported opened occurrence.output := by
  cases occurrence with
  | ask origin head arguments => exact (bundle_supported_iff opened head arguments).mpr permitted
  | get origin head arguments position => exact permitted.2 position
  | build origin head arguments => exact (sourceNode_supported_iff opened head arguments).mpr permitted.2

theorem occurrence_target_supported {opened : Policy source Parallel}
    {occurrence : Occurrence source Parallel Origins} (permitted : Permitted opened occurrence) :
    ArrowSupported opened occurrence.rule.reactum :=
  (value_arrow_supported_iff opened occurrence.output).mpr (occurrence_output_supported permitted)

theorem Permitted.monotone {first second : Policy source Parallel}
    (inclusion : ∀ head, first head → second head) {occurrence : Occurrence source Parallel Origins}
    (permitted : Permitted first occurrence) : Permitted second occurrence := by
  cases occurrence with
  | ask origin head arguments => exact ⟨inclusion head permitted.1, fun position => (permitted.2 position).monotone inclusion⟩
  | get origin head arguments position => exact ⟨inclusion head permitted.1, fun other => (permitted.2 other).monotone inclusion⟩
  | build origin head arguments => exact ⟨inclusion head permitted.1, fun position => (permitted.2 position).monotone inclusion⟩

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
