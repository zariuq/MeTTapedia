import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshSyntaxBinding
import Mettapedia.Languages.MeTTa.HE.ContextualAlias

/-! Open variable-data capture uses the same contextual binder as closed
capture. Fresh aliases retain their unassigned representative, and older
closed values keep their full annotated representation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenSyntaxBinding

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open Spec.Type.RuntimeRefinement
open HEFreshSyntaxBinding

theorem bound_read_fixed (policy readingPolicy : Policy) (before : Frame) (name : String) (value : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) (absent : name ∉ TypeSubst.typeVars value.erase)
    (fixed : before.read policy value = value) :
    (bindFrame policy before name value fresh absent).read readingPolicy (.var name) = value := by
  simpa only [bindFrame, Frame.read, Entry.Value.substitute, Entry.Value.bind, Entry.Value.resolve,
    List.lookup_cons, beq_self_eq_true, Option.getD_some] using fixed

theorem source_fixed_nonvariable (policy : Policy) (before : Frame) (name : String) (value : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) (absent : name ∉ TypeSubst.typeVars value.erase)
    (fixed : before.read policy value = value) (nonvariable : ∀ key, value.erase ≠ .var key) :
    Entry.Value.UnifyRel policy.rebuilding before.environment value (.var name)
      (bindFrame policy before name value fresh absent).environment := by
  apply Entry.Value.UnifyRel.ordinary
  have materialized : Entry.Value.substitute policy.rebuilding (Entry.Value.resolve before.environment) value = value := by
    simpa only [Frame.read] using fixed
  rw [materialized]
  simp only [Entry.Value.substitute, resolve_fresh before name fresh]
  exact .bindRight nonvariable absent

theorem source_alias (policy : Policy) (before : Frame) (left right : String)
    (leftFresh : left ∉ specBindingVars before.bindings)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) :
    Entry.Value.UnifyRel policy.rebuilding before.environment (.var left) (.var right)
      (bindFrame policy before left (.var right) leftFresh
        (by simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using different)).environment := by
  apply Entry.Value.UnifyRel.ordinary
  simp only [Entry.Value.substitute, resolve_fresh before left leftFresh, resolve_fresh before right rightFresh]
  exact .bindLeft (by simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using different)

theorem other_stays_fresh (policy : Policy) (before : Frame) (name other : String) (value : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings) (absent : name ∉ TypeSubst.typeVars value.erase)
    (otherFresh : other ∉ specBindingVars before.bindings) (different : other ≠ name)
    (otherAbsent : other ∉ TypeSubst.typeVars value.erase) :
    other ∉ specBindingVars (bindFrame policy before name value fresh absent).bindings := by
  rw [binding_keeps_caller]
  simpa [HEFreshRangeFrame.extend, specBindingVars, and_assoc, and_left_comm, and_comm]
    using And.intro (And.intro otherFresh different) otherAbsent

export Mettapedia.Languages.MeTTa.HE.ContextualAlias (resolve_bind_other)

theorem older_closed_read (policy readingPolicy : Policy) (before : Frame) (name other : String)
    (value previous : Entry.Value) (fresh : name ∉ specBindingVars before.bindings)
    (absent : name ∉ TypeSubst.typeVars value.erase) (different : other ≠ name)
    (read : before.read readingPolicy (.var other) = previous)
    (closed : TypeSubst.typeVars previous.erase = []) :
    (bindFrame policy before name value fresh absent).read readingPolicy (.var other) = previous := by
  simp only [bindFrame, Frame.read, Entry.Value.substitute]
  rw [resolve_bind_other policy.rebuilding before.environment name other value different]
  have resolved : Entry.Value.resolve before.environment other = previous := by
    simpa only [Frame.read, Entry.Value.substitute] using read
  rw [resolved]
  exact ground_substitution policy.rebuilding _ previous closed

theorem older_untouched_read (policy readingPolicy : Policy) (before : Frame) (name other : String)
    (value previous : Entry.Value) (fresh : name ∉ specBindingVars before.bindings)
    (absent : name ∉ TypeSubst.typeVars value.erase) (different : other ≠ name)
    (read : before.read readingPolicy (.var other) = previous)
    (untouched : name ∉ TypeSubst.typeVars previous.erase) :
    (bindFrame policy before name value fresh absent).read readingPolicy (.var other) = previous := by
  simp only [bindFrame, Frame.read, Entry.Value.substitute]
  rw [resolve_bind_other policy.rebuilding before.environment name other value different]
  have resolved : Entry.Value.resolve before.environment other = previous := by
    simpa only [Frame.read, Entry.Value.substitute] using read
  rw [resolved]
  apply Entry.Value.substitute_of_fixed_variables
  intro key occurs
  have omitted : key ≠ name := by
    intro same
    exact untouched (same ▸ occurs)
  simp only [Entry.Value.resolve, List.lookup_cons, beq_eq_false_iff_ne.mpr omitted,
    List.lookup_nil, Option.getD_none]

theorem mem_bound_support (policy : Policy) (before : Frame) (key : String) (value : Entry.Value)
    (fresh : key ∉ specBindingVars before.bindings) (absent : key ∉ TypeSubst.typeVars value.erase)
    (name : String) :
    name ∈ specBindingVars (bindFrame policy before key value fresh absent).bindings ↔
      name ∈ specBindingVars before.bindings ∨ name = key ∨ name ∈ TypeSubst.typeVars value.erase := by
  rw [binding_keeps_caller]
  simp [HEFreshRangeFrame.extend, specBindingVars, or_assoc, or_comm]

theorem other_fixed_read (policy readingPolicy : Policy) (before : Frame) (name other : String)
    (value : Entry.Value) (fresh : name ∉ specBindingVars before.bindings)
    (absent : name ∉ TypeSubst.typeVars value.erase) (different : other ≠ name)
    (fixed : before.read readingPolicy (.var other) = .var other) :
    (bindFrame policy before name value fresh absent).read readingPolicy (.var other) = .var other := by
  simp only [bindFrame, Frame.read, Entry.Value.substitute]
  rw [resolve_bind_other policy.rebuilding before.environment name other value different]
  have resolved : Entry.Value.resolve before.environment other = .var other := by
    simpa only [Frame.read, Entry.Value.substitute] using fixed
  rw [resolved]
  simp only [Entry.Value.substitute, Entry.Value.resolve, List.lookup_cons,
    beq_eq_false_iff_ne.mpr different, List.lookup_nil, Option.getD_none]

theorem alias_read (policy readingPolicy : Policy) (before : Frame) (left right : String)
    (leftFresh : left ∉ specBindingVars before.bindings)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) :
    let after := bindFrame policy before left (.var right) leftFresh
      (by simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using different)
    after.read readingPolicy (.var left) = .var right ∧
      after.read readingPolicy (.var right) = .var right := by
  dsimp only
  have fixed (readingPolicy : Policy) : before.read readingPolicy (.var right) = .var right := by
    simpa only [Frame.read, Entry.Value.substitute] using resolve_fresh before right rightFresh
  exact ⟨bound_read_fixed policy readingPolicy before left (.var right) leftFresh _ (fixed policy),
    other_fixed_read policy readingPolicy before left right (.var right) leftFresh _ (Ne.symm different) (fixed readingPolicy)⟩

/-- The contextual unifier's reached certificate entails every incoming
constraint. It may add private keys; raw record identity is not required. -/
theorem unifier_preserves_constraints (policy : Policy) (before after : Frame) (left right : Entry.Value)
    (unified : Entry.Value.UnifyRel policy.rebuilding before.environment left right after.environment) :
    ∀ valuation, TypeBindingSatisfied valuation after.bindings → TypeBindingSatisfied valuation before.bindings := by
  intro valuation model
  have reached := (after.certified.theory valuation).mpr model
  have incoming := ((unified.solutions before.certified.normal valuation).mp reached).1
  exact (before.certified.theory valuation).mp incoming

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenSyntaxBinding
