import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenSyntaxBinding

/-! Two fresh variable-valued fold parameters are captured by actual
left-variable unification. Their independent canonical representatives remain
free; unrelated closed captures and the caller's constraints are retained. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldOpenParameters

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEFreshSyntaxBinding

theorem capture (policy : Policy) (before : Frame) (names : Fin 4 → String)
    (injective : Function.Injective names)
    (fresh : ∀ index, names index ∉ specBindingVars before.bindings) :
    ∃ after : Frame,
      Entry.Value.UnifyListRel policy.rebuilding before.environment
        [.var (names 0), .var (names 1)] [.var (names 2), .var (names 3)] after.environment ∧
      after.bindings = (before.bindings.assign (names 0) (.var (names 2))).assign (names 1) (.var (names 3)) ∧
      (∀ readingPolicy,
        after.read readingPolicy (.var (names 0)) = .var (names 2) ∧
        after.read readingPolicy (.var (names 1)) = .var (names 3) ∧
        after.read readingPolicy (.var (names 2)) = .var (names 2) ∧
        after.read readingPolicy (.var (names 3)) = .var (names 3)) ∧
      (∀ readingPolicy key value,
        key ≠ names 0 → key ≠ names 1 → before.read readingPolicy (.var key) = value →
        TypeSubst.typeVars value.erase = [] → after.read readingPolicy (.var key) = value) ∧
      (∀ name, name ∈ specBindingVars after.bindings ↔ name ∈ specBindingVars before.bindings ∨
        name = names 0 ∨ name = names 1 ∨ name = names 2 ∨ name = names 3) := by
  have apart (i j : Fin 4) (different : i ≠ j) : names i ≠ names j := fun same => different (injective same)
  let middle := bindFrame policy before (names 0) (.var (names 2)) (fresh 0)
    (by simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using apart 0 2 (by decide))
  have middleFresh (i : Fin 4) (notFirst : i ≠ 0) (notRepresentative : i ≠ 2) :
      names i ∉ specBindingVars middle.bindings := by
    apply HEOpenSyntaxBinding.other_stays_fresh policy before (names 0) (names i) (.var (names 2))
      (fresh 0) _ (fresh i) (apart i 0 notFirst)
    simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using apart i 2 notRepresentative
  let after := bindFrame policy middle (names 1) (.var (names 3))
    (middleFresh 1 (by decide) (by decide))
    (by simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using apart 1 3 (by decide))
  have first := HEOpenSyntaxBinding.source_alias policy before (names 0) (names 2)
    (fresh 0) (fresh 2) (apart 0 2 (by decide))
  have second := HEOpenSyntaxBinding.source_alias policy middle (names 1) (names 3)
    (middleFresh 1 (by decide) (by decide)) (middleFresh 3 (by decide) (by decide)) (apart 1 3 (by decide))
  refine ⟨after, .cons first (.cons second (.nil _)), ?_, ?_, ?_, ?_⟩
  · simp only [after, middle, bindFrame, Entry.Value.erase]
  · intro readingPolicy
    have firstReads := HEOpenSyntaxBinding.alias_read policy readingPolicy before (names 0) (names 2)
      (fresh 0) (fresh 2) (apart 0 2 (by decide))
    have secondReads := HEOpenSyntaxBinding.alias_read policy readingPolicy middle (names 1) (names 3)
      (middleFresh 1 (by decide) (by decide)) (middleFresh 3 (by decide) (by decide)) (apart 1 3 (by decide))
    refine ⟨?_, secondReads.1, ?_, secondReads.2⟩
    · apply HEOpenSyntaxBinding.older_untouched_read policy readingPolicy middle (names 1) (names 0)
        (.var (names 3)) (.var (names 2)) _ _ (apart 0 1 (by decide)) firstReads.1
      simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using apart 1 2 (by decide)
    · exact HEOpenSyntaxBinding.other_fixed_read policy readingPolicy middle (names 1) (names 2)
        (.var (names 3)) _ _ (apart 2 1 (by decide)) firstReads.2
  · intro readingPolicy key value notFirst notSecond read closed
    have kept := HEOpenSyntaxBinding.older_closed_read policy readingPolicy before (names 0) key
      (.var (names 2)) value (fresh 0)
      (by simpa only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton] using apart 0 2 (by decide)) notFirst read closed
    exact HEOpenSyntaxBinding.older_closed_read policy readingPolicy middle (names 1) key
      (.var (names 3)) value _ _ notSecond kept closed
  · intro name
    dsimp only [after]
    rw [HEOpenSyntaxBinding.mem_bound_support]
    dsimp only [middle]
    rw [HEOpenSyntaxBinding.mem_bound_support]
    simp only [Entry.Value.erase, TypeSubst.typeVars, List.mem_singleton]
    tauto

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldOpenParameters
