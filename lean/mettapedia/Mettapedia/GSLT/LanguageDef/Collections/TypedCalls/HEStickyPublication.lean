import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Mark unchanged successful expressions without clearing inherited marks

The local publication action of Rust `check_alternatives` sets an expression's
evaluated mark when its erased result equals the original expression. It
otherwise keeps the returned value, including a mark earned by an inner
producer. CeTTa's `he_mark_answers_of` also skips already marked answers.

This is a value-publication adapter, not a new evaluator or a global claim
that the ready source profile is faithful to either implementation. Resolver
readback of a closed bound value is distinct from the public apply-bindings
operation that can clear a replaced root's mark.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStickyPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval

def publish (original : Atom) (value : Entry.Value) : Entry.Value :=
  if !isErrorAtom value.erase && original == value.erase then value.withStatus .held else value

theorem erase_publish (original : Atom) (value : Entry.Value) :
    (publish original value).erase = value.erase := by
  unfold publish
  split <;> simp only [Entry.Value.erase_withStatus]

theorem unchanged_success (original : Atom) (value : Entry.Value)
    (same : original = value.erase) (clean : isErrorAtom value.erase = false) :
    publish original value = value.withStatus .held := by simp [publish, same, clean]

theorem changed_retains_value (original : Atom) (value : Entry.Value)
    (different : original ≠ value.erase) : publish original value = value := by
  simp [publish, different]

theorem held_survives (original : Atom) (value : Entry.Value) (held : value.status = .held) :
    publish original value = value := by
  cases value with
  | symbol name => simp [Entry.Value.status] at held
  | var name => simp [Entry.Value.status] at held
  | grounded value => simp [Entry.Value.status] at held
  | expression status fields =>
      have same : status = .held := held
      subst status
      unfold publish
      split <;> rfl

/-- The value-aware preserving policy implements this local action exactly.
This does not identify its independent rebuilding or evaluation policies. -/
theorem preserving_policy_matches (original : Atom) (value : Entry.Value) (frame : BindingFrame) :
    publish original value = Entry.Value.publish .unchangedPreserving original frame value := by
  cases value with
  | symbol name => simp [publish, Entry.Value.publish, Entry.Value.withStatus, Entry.Value.erase]
  | var name => simp [publish, Entry.Value.publish, Entry.Value.withStatus, Entry.Value.erase]
  | grounded value => simp [publish, Entry.Value.publish, Entry.Value.withStatus, Entry.Value.erase]
  | expression status fields =>
      by_cases error : isErrorAtom (.expression (fields.map Entry.Value.erase)) = true
      · simp [publish, Entry.Value.publish, Entry.publish, Entry.Value.withStatus, Entry.Value.erase, Entry.Value.status, error]
      · have clean : isErrorAtom (.expression (fields.map Entry.Value.erase)) = false := Bool.eq_false_iff.mpr error
        by_cases same : original = .expression (fields.map Entry.Value.erase)
        · simp [publish, Entry.Value.publish, Entry.publish, Entry.Value.withStatus, Entry.Value.erase,
            clean, same]
        · simp [publish, Entry.Value.publish, Entry.publish, Entry.Value.withStatus, Entry.Value.erase, Entry.Value.status,
            clean, same, Ne.symm same]

/-- An unchanged successful constructor has the same publication in the
ready source profile and the mark-if-unchanged operation. -/
theorem ready_agrees_on_unchanged (original : Atom) (value : Entry.Value) (frame : BindingFrame)
    (same : original = value.erase) (clean : isErrorAtom value.erase = false) :
    publish original value = Entry.Value.publish .successes original frame value := by
  rw [unchanged_success original value same clean]
  cases value <;> simp [Entry.Value.publish, Entry.publish, Entry.Value.withStatus, Entry.Value.erase] at *
  assumption

/-- An enclosing call receiving an already held success does not need the
stronger rule that marks every changed active expression. -/
theorem ready_agrees_on_held (original : Atom) (value : Entry.Value) (frame : BindingFrame)
    (held : value.status = .held) (clean : isErrorAtom value.erase = false) :
    publish original value = Entry.Value.publish .successes original frame value := by
  rw [held_survives original value held]
  cases value with
  | symbol name => simp [Entry.Value.status] at held
  | var name => simp [Entry.Value.status] at held
  | grounded value => simp [Entry.Value.status] at held
  | expression status fields =>
      have same : status = .held := held
      subst status
      simp only [Entry.Value.erase] at clean
      simp only [Entry.Value.publish, Entry.publish, Entry.Value.erase, clean, Bool.false_eq_true, if_false,
        Entry.Value.withStatus]

namespace Controls

def original : Atom := .expression [.symbol "outer"]
def active : Entry.Value := .expression .active [.symbol "inner", .grounded (.int 7)]
def held : Entry.Value := .expression .held [.symbol "inner", .grounded (.int 7)]

theorem changed_active_does_not_become_ready :
    publish original active = active ∧
      Entry.Value.publish .successes original (BindingFrame.historical Bindings.empty) active = held ∧ active ≠ held := by
  constructor
  · simp [publish, original, active, Entry.Value.erase]
  constructor
  · simp [Entry.Value.publish, Entry.publish, Entry.Value.withStatus, active, held, Entry.Value.erase, isErrorAtom]
  · intro equal
    have statuses := congrArg Entry.Value.status equal
    cases statuses

theorem inherited_mark_is_not_cleared :
    publish original held = held ∧
      Entry.Value.publish .unchanged original (BindingFrame.historical Bindings.empty) held = active ∧ held ≠ active := by
  constructor
  · simp [publish, original, held, Entry.Value.erase]
  constructor
  · simp [Entry.Value.publish, Entry.publish, Entry.Value.withStatus, original, active, held, Entry.Value.erase, isErrorAtom]
  · intro equal
    have statuses := congrArg Entry.Value.status equal
    cases statuses

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStickyPublication
