import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitSupport

/-!
# Whole sorted contexts and factor closure for an instrument kit

The permitted grammar retains each frame's actual input position, all typed
siblings and every parallel residue. Zero missing-permission weight is earned
from that grammar and conversely reconstructs it. Filling, composition and
their factor readouts descend through the independently formed AC1 context
equations and apply to arbitrary ground values and source interfaces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

inductive ContextSupported (opened : Policy source Parallel) :
    {first second : Srt source Parallel} →
      RawContext (signature source Parallel) NativeParallel first second → Prop where
  | hole (sort : Srt source Parallel) : ContextSupported opened (.hole : RawContext (signature source Parallel) NativeParallel sort sort)
  | frame {first : Srt source Parallel} {constructor : Constructor source Parallel}
      {position : Fin ((signature source Parallel).arity constructor)}
      {siblings : (other : Fin ((signature source Parallel).arity constructor)) → other ≠ position →
        Value (source := source) (Parallel := Parallel) ((signature source Parallel).input constructor other)}
      {inner : RawContext (signature source Parallel) NativeParallel first ((signature source Parallel).input constructor position)}
      (allowed : Allowed opened constructor) (children : ∀ other different, Supported opened (siblings other different))
      (previous : ContextSupported opened inner) :
      ContextSupported opened (.frame constructor position siblings inner)
  | left {first second : Srt source Parallel} (parallel : NativeParallel second)
      {inner : RawContext (signature source Parallel) NativeParallel first second}
      {sibling : Value (source := source) (Parallel := Parallel) second}
      (previous : ContextSupported opened inner) (stored : Supported opened sibling) :
      ContextSupported opened (.left parallel inner sibling)
  | right {first second : Srt source Parallel} (parallel : NativeParallel second)
      {sibling : Value (source := source) (Parallel := Parallel) second}
      {inner : RawContext (signature source Parallel) NativeParallel first second}
      (stored : Supported opened sibling) (previous : ContextSupported opened inner) :
      ContextSupported opened (.right parallel sibling inner)

theorem ContextSupported.weight_zero {opened : Policy source Parallel} {first second : Srt source Parallel}
    {supplied : RawContext (signature source Parallel) NativeParallel first second}
    (supported : ContextSupported opened supplied) :
    HereditaryWeight.context (constructorWeight opened) supplied = 0 := by
  induction supported with
  | hole => rfl
  | frame allowed children previous inductionHypothesis =>
    change constructorWeight opened _ +
      HereditaryWeight.siblings (signature := signature source Parallel) (Parallel := NativeParallel)
        (constructorWeight opened) _ _ _ +
      HereditaryWeight.context (signature := signature source Parallel) (Parallel := NativeParallel)
        (constructorWeight opened) _ = 0
    rw [(allowed_iff_weight_zero opened _).mp allowed, inductionHypothesis]
    unfold HereditaryWeight.siblings
    simp only [Supported.weight_zero (children _ _), dite_eq_ite, ite_self, Finset.sum_const_zero, Nat.add_zero]
  | left parallel previous stored inductionHypothesis =>
    change HereditaryWeight.context (signature := signature source Parallel) (Parallel := NativeParallel)
      (constructorWeight opened) _ +
      HereditaryWeight.term (signature := signature source Parallel) (Parallel := NativeParallel)
        (constructorWeight opened) _ = 0
    rw [inductionHypothesis, stored.weight_zero]
  | right parallel stored previous inductionHypothesis =>
    change HereditaryWeight.term (signature := signature source Parallel) (Parallel := NativeParallel)
      (constructorWeight opened) _ +
      HereditaryWeight.context (signature := signature source Parallel) (Parallel := NativeParallel)
        (constructorWeight opened) _ = 0
    rw [stored.weight_zero, inductionHypothesis]

theorem context_supported_of_weight_zero (opened : Policy source Parallel) {first second : Srt source Parallel}
    (supplied : RawContext (signature source Parallel) NativeParallel first second)
    (zero : HereditaryWeight.context (constructorWeight opened) supplied = 0) : ContextSupported opened supplied := by
  revert zero
  apply @RawContext.rec (signature source Parallel) NativeParallel first
    (fun _ supplied => HereditaryWeight.context (constructorWeight opened) supplied = 0 → ContextSupported opened supplied)
    (t := supplied)
  · intro _
    exact .hole first
  · intro constructor position siblings inner inductionHypothesis zero
    change constructorWeight opened constructor +
      HereditaryWeight.siblings (constructorWeight opened) constructor position siblings +
        HereditaryWeight.context (constructorWeight opened) inner = 0 at zero
    have constructorZero : constructorWeight opened constructor = 0 := by omega
    have siblingsZero : HereditaryWeight.siblings (constructorWeight opened) constructor position siblings = 0 := by omega
    have innerZero : HereditaryWeight.context (constructorWeight opened) inner = 0 := by omega
    exact .frame ((allowed_iff_weight_zero opened constructor).mpr constructorZero)
      (fun other different => supported_of_weight_zero opened (siblings other different)
        (HereditaryWeight.siblings_zero (constructorWeight opened) siblings siblingsZero other different))
      (inductionHypothesis innerZero)
  · intro target parallel inner sibling inductionHypothesis zero
    change HereditaryWeight.context (constructorWeight opened) inner +
      HereditaryWeight.term (constructorWeight opened) sibling = 0 at zero
    exact .left parallel (inductionHypothesis (Nat.add_eq_zero_iff.mp zero).1)
      (supported_of_weight_zero opened sibling (Nat.add_eq_zero_iff.mp zero).2)
  · intro target parallel sibling inner inductionHypothesis zero
    change HereditaryWeight.term (constructorWeight opened) sibling +
      HereditaryWeight.context (constructorWeight opened) inner = 0 at zero
    exact .right parallel (supported_of_weight_zero opened sibling (Nat.add_eq_zero_iff.mp zero).1)
      (inductionHypothesis (Nat.add_eq_zero_iff.mp zero).2)

theorem context_supported_iff_weight_zero (opened : Policy source Parallel) {first second : Srt source Parallel}
    (supplied : RawContext (signature source Parallel) NativeParallel first second) :
    ContextSupported opened supplied ↔ HereditaryWeight.context (constructorWeight opened) supplied = 0 :=
  ⟨ContextSupported.weight_zero, context_supported_of_weight_zero opened supplied⟩

theorem context_supported_equation (opened : Policy source Parallel) {first second : Srt source Parallel}
    {before after : RawContext (signature source Parallel) NativeParallel first second}
    (equation : ContextEquation before after) : ContextSupported opened before ↔ ContextSupported opened after := by
  rw [context_supported_iff_weight_zero, context_supported_iff_weight_zero,
    HereditaryWeight.context_equation (constructorWeight opened) equation]

def ClassContextSupported (opened : Policy source Parallel) {first second : Srt source Parallel}
    (supplied : ContextClass (signature source Parallel) NativeParallel first second) : Prop :=
  ∃ raw : RawContext (signature source Parallel) NativeParallel first second,
    ContextSupported opened raw ∧ contextClassOf raw = supplied

theorem class_context_supported_iff_weight_zero (opened : Policy source Parallel) {first second : Srt source Parallel}
    (supplied : ContextClass (signature source Parallel) NativeParallel first second) :
    ClassContextSupported opened supplied ↔ HereditaryWeight.classContext (constructorWeight opened) supplied = 0 := by
  constructor
  · rintro ⟨raw, supported, rfl⟩
    exact supported.weight_zero
  · revert supplied
    intro supplied
    refine Quotient.inductionOn supplied ?_
    intro raw zero
    exact ⟨raw, context_supported_of_weight_zero opened raw zero, rfl⟩

inductive ArrowSupported (opened : Policy source Parallel) :
    {first second : ContextCategory source Parallel} → (first ⟶ second) → Prop where
  | identity : ArrowSupported opened (RawArrow.identity (signature := signature source Parallel) (Parallel := NativeParallel))
  | value {sort : Srt source Parallel} {supplied : ValueClass (source := source) (Parallel := Parallel) sort}
      (supported : ClassSupported opened supplied) : ArrowSupported opened (RawArrow.value supplied)
  | context {first second : Srt source Parallel}
      {supplied : ContextClass (signature source Parallel) NativeParallel first second}
      (supported : ClassContextSupported opened supplied) : ArrowSupported opened (RawArrow.context supplied)

theorem arrow_supported_iff_weight_zero (opened : Policy source Parallel) {first second : ContextCategory source Parallel}
    (supplied : first ⟶ second) :
    ArrowSupported opened supplied ↔ HereditaryWeight.arrow (constructorWeight opened) supplied = 0 := by
  cases supplied with
  | identity => exact ⟨fun _ => rfl, fun _ => .identity⟩
  | value supplied =>
    constructor
    · intro supported
      cases supported with
      | value supported => exact (class_supported_iff_weight_zero opened supplied).mp supported
    · exact fun zero => .value ((class_supported_iff_weight_zero opened supplied).mpr zero)
  | context supplied =>
    constructor
    · intro supported
      cases supported with
      | context supported => exact (class_context_supported_iff_weight_zero opened supplied).mp supported
    · exact fun zero => .context ((class_context_supported_iff_weight_zero opened supplied).mpr zero)

theorem ArrowSupported.id (opened : Policy source Parallel) (object : ContextCategory source Parallel) :
    ArrowSupported opened (𝟙 object) :=
  (arrow_supported_iff_weight_zero opened (𝟙 object)).mpr (HereditaryWeight.arrow_id _ object)

theorem ArrowSupported.comp {opened : Policy source Parallel} {first second third : ContextCategory source Parallel}
    {before : first ⟶ second} {after : second ⟶ third}
    (supportedBefore : ArrowSupported opened before) (supportedAfter : ArrowSupported opened after) :
    ArrowSupported opened (before ≫ after) :=
  (arrow_supported_iff_weight_zero opened _).mpr
    ((HereditaryWeight.composite_zero_iff _ before after).mpr
      ⟨(arrow_supported_iff_weight_zero opened before).mp supportedBefore,
        (arrow_supported_iff_weight_zero opened after).mp supportedAfter⟩)

theorem arrow_supported_comp_iff (opened : Policy source Parallel) {first second third : ContextCategory source Parallel}
    (before : first ⟶ second) (after : second ⟶ third) :
    ArrowSupported opened (before ≫ after) ↔ ArrowSupported opened before ∧ ArrowSupported opened after := by
  rw [arrow_supported_iff_weight_zero, arrow_supported_iff_weight_zero, arrow_supported_iff_weight_zero]
  exact HereditaryWeight.composite_zero_iff _ before after

theorem context_supported_fill_iff (opened : Policy source Parallel) {first second : Srt source Parallel}
    (context : ContextClass (signature source Parallel) NativeParallel first second)
    (supplied : ValueClass (source := source) (Parallel := Parallel) first) :
    ClassSupported opened (context.fill supplied) ↔ ClassContextSupported opened context ∧ ClassSupported opened supplied := by
  rw [class_supported_iff_weight_zero, class_context_supported_iff_weight_zero,
    class_supported_iff_weight_zero, HereditaryWeight.class_fill]
  exact Nat.add_eq_zero_iff

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
