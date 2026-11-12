import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Aliasing an unassigned contextual variable to a fresh representative

The left name may occur inside held caller values. Its actual read must still
be itself; mere occurrence is not assignment. The fresh right representative
adds an equality while the existing contextual binder updates older values.
The frame certificate is derived from that source unification and a source
match/merge, not assumed for the output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ContextualAlias

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Bindings.ScopeObservation.ModelTransport
open Spec.Match.Merge Spec.Match.SolutionTheory

theorem resolve_fresh (before : Frame) (name : String) (fresh : name ∉ specBindingVars before.bindings) :
    Entry.Value.resolve before.environment name = .var name :=
  Entry.Value.resolve_of_not_mem_keys before.environment name
    (TypeSubst.not_mem_keys_of_lookup_eq_none (before.certified.lookup_none_of_outside fresh))

def aliasBindings (before : Bindings) (left right : String) : Bindings :=
  let matched := Bindings.empty.addEquality left right
  ⟨matched.assignments ++ before.assignments, matched.equalities ++ before.equalities⟩

theorem candidate (before : Frame) (left right : String)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) :
    UnifyCandidateRel (.var left) (.var right) before.bindings (aliasBindings before.bindings left right) := by
  obtain ⟨oldModel, oldSatisfied⟩ := before.certified.satisfiable
  let model : String → Atom := fun name => if name = right then oldModel left else oldModel name
  have preserved : TypeBindingSatisfied model before.bindings := by
    apply (specTypeBindingSatisfied_congr_of_bindingVars (left := oldModel) (right := model) ?_).mp oldSatisfied
    intro name present
    have other : name ≠ right := by intro same; subst name; exact rightFresh present
    simp [model, other]
  have paired : TypeBindingSatisfied model (Bindings.empty.addEquality left right) := by
    simp [TypeBindingSatisfied, Bindings.empty, Bindings.addEquality, model, different]
  exact ⟨Bindings.empty.addEquality left right, .varVar left right (semanticLoopFree_of_assignments_nil rfl),
    LogicalMergeRel.append_of_common_model ⟨model, paired, preserved⟩⟩

theorem unifies (policy : Policy) (before : Frame) (left right : String)
    (fixed : before.read policy (.var left) = .var left)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) :
    Entry.Value.UnifyRel policy.rebuilding before.environment (.var left) (.var right)
      (Entry.Value.bind policy.rebuilding before.environment left (.var right)) := by
  have leftRead : Entry.Value.resolve before.environment left = .var left := by
    simpa only [Frame.read, Entry.Value.substitute] using fixed
  apply Entry.Value.UnifyRel.ordinary
  simp only [Entry.Value.substitute, leftRead, resolve_fresh before right rightFresh]
  exact .bindLeft (by simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using different)

def aliasFrame (policy : Policy) (before : Frame) (left right : String)
    (fixed : before.read policy (.var left) = .var left)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) : Frame :=
  ⟨aliasBindings before.bindings left right,
   Entry.Value.bind policy.rebuilding before.environment left (.var right),
   (unifies policy before left right fixed rightFresh different).certifies before.certified
     (by simpa only [Entry.Value.erase] using candidate before left right rightFresh different)⟩

private theorem lookup_filter_map (entries : Entry.Value.Environment) (name key : String)
    (transform : Entry.Value → Entry.Value) (different : name ≠ key) :
    List.lookup name ((entries.filter (fun row => row.1 != key)).map (fun row => (row.1, transform row.2))) =
      (List.lookup name entries).map transform := by
  induction entries with
  | nil => rfl
  | cons row tail ih =>
      rcases row with ⟨head, value⟩
      by_cases removed : head = key
      · subst head
        simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr different] using ih
      · by_cases selected : name = head
        · subst head
          simp [removed]
        · simpa [List.lookup_cons, removed, beq_eq_false_iff_ne.mpr selected] using ih

theorem resolve_bind_other (rebuilding : Entry.RebuildPolicy) (entries : Entry.Value.Environment)
    (name other : String) (value : Entry.Value) (different : other ≠ name) :
    let selected := Entry.Value.substitute rebuilding (Entry.Value.resolve entries) value
    Entry.Value.resolve (Entry.Value.bind rebuilding entries name value) other =
      Entry.Value.substitute rebuilding (Entry.Value.resolve [(name, selected)]) (Entry.Value.resolve entries other) := by
  dsimp only
  unfold Entry.Value.bind
  simp only [Entry.Value.resolve, List.lookup_cons, beq_eq_false_iff_ne.mpr different]
  rw [lookup_filter_map entries other name _ different]
  cases found : List.lookup other entries with
  | none => simp [Entry.Value.substitute, Entry.Value.resolve, List.lookup_cons, beq_eq_false_iff_ne.mpr different]
  | some previous => rfl


theorem bound_read (policy readingPolicy : Policy) (before : Frame) (left right : String)
    (fixed : before.read policy (.var left) = .var left)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) :
    (aliasFrame policy before left right fixed rightFresh different).read readingPolicy (.var left) = .var right := by
  simp only [aliasFrame, Frame.read, Entry.Value.substitute, Entry.Value.bind, Entry.Value.resolve,
    List.lookup_cons, beq_self_eq_true, Option.getD_some]
  simpa only [Entry.Value.resolve] using resolve_fresh before right rightFresh

theorem other_read (policy readingPolicy : Policy) (before : Frame) (left right other : String)
    (fixed : before.read policy (.var left) = .var left)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) (otherDifferent : other ≠ left) :
    (aliasFrame policy before left right fixed rightFresh different).read readingPolicy (.var other) =
      Entry.Value.substitute policy.rebuilding (Entry.Value.resolve [(left, .var right)])
        (before.read readingPolicy (.var other)) := by
  simp only [aliasFrame, Frame.read, Entry.Value.substitute]
  rw [resolve_bind_other policy.rebuilding before.environment left other (.var right) otherDifferent]
  simp only [Entry.Value.substitute, resolve_fresh before right rightFresh]

theorem other_fixed (policy readingPolicy : Policy) (before : Frame) (left right other : String)
    (fixed : before.read policy (.var left) = .var left)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) (otherDifferent : other ≠ left)
    (otherFixed : before.read readingPolicy (.var other) = .var other) :
    (aliasFrame policy before left right fixed rightFresh different).read readingPolicy (.var other) = .var other := by
  rw [other_read policy readingPolicy before left right other fixed rightFresh different otherDifferent, otherFixed]
  simp only [Entry.Value.substitute, Entry.Value.resolve, List.lookup_cons,
    beq_eq_false_iff_ne.mpr otherDifferent, List.lookup_nil, Option.getD_none]

theorem older_untouched (policy readingPolicy : Policy) (before : Frame) (left right other : String)
    (fixed : before.read policy (.var left) = .var left)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) (otherDifferent : other ≠ left)
    (previous : Entry.Value) (read : before.read readingPolicy (.var other) = previous)
    (untouched : left ∉ TypeSubst.typeVars previous.erase) :
    (aliasFrame policy before left right fixed rightFresh different).read readingPolicy (.var other) = previous := by
  rw [other_read policy readingPolicy before left right other fixed rightFresh different otherDifferent, read]
  apply Entry.Value.substitute_of_fixed_variables
  intro key occurs
  have omitted : key ≠ left := by intro same; exact untouched (same ▸ occurs)
  simp only [Entry.Value.resolve, List.lookup_cons, beq_eq_false_iff_ne.mpr omitted, List.lookup_nil, Option.getD_none]

theorem support (policy : Policy) (before : Frame) (left right : String)
    (fixed : before.read policy (.var left) = .var left)
    (rightFresh : right ∉ specBindingVars before.bindings) (different : left ≠ right) (name : String) :
    name ∈ specBindingVars (aliasFrame policy before left right fixed rightFresh different).bindings ↔
      name ∈ specBindingVars before.bindings ∨ name = left ∨ name = right := by
  simp [aliasFrame, aliasBindings, Bindings.empty, Bindings.addEquality, specBindingVars,
    or_assoc, or_comm]

end Mettapedia.Languages.MeTTa.HE.ContextualAlias
