import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldEmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshSyntaxBinding

/-! Fresh emitted control remains valid when the actual body boundary reads
it through the retained caller. Canonical parameter variables need only be
fixed by that read, not absent from the caller's alias classes. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldReadback

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HECollectionFoldEmission

theorem resolve_of_fixed (policy : Policy) (frame : Frame) (name : String)
    (fixed : frame.read policy (.var name) = .var name) : Entry.Value.resolve frame.environment name = .var name := by
  simpa only [Frame.read, Entry.Value.substitute] using fixed

theorem substituteBinder_absent (policy : Policy) (name : String) (replacement value : Entry.Value)
    (absent : name ∉ TypeSubst.typeVars value.erase) :
    substituteBinder policy name replacement value = value := by
  apply Entry.Value.substitute_of_fixed_variables
  intro key occurs
  have different : key ≠ name := by
    intro same
    exact absent (same ▸ occurs)
  simp only [if_neg different]

/-- The chain operand is inserted once in the next helper invocation. The
saved operation and its two canonical variables are not rewritten. -/
theorem next_call_substitution (policy : Policy) (name left right : String)
    (replacement context : Entry.Value) (tail : List Entry.Value) (operationMark : Entry.Status)
    (leftDifferent : left ≠ name) (rightDifferent : right ≠ name)
    (tailClosed : TypeSubst.typeVarsList (tail.map Entry.Value.erase) = [])
    (contextClosed : TypeSubst.typeVars context.erase = []) :
    let operation := Entry.Value.expression operationMark [.symbol CollectionStdlibSource.appendName, .var left, .var right]
    substituteBinder policy name replacement
      (.expression .active [.symbol "eval", call tail (.var name) left right operation context]) =
      .expression .active [.symbol "eval", call tail replacement left right operation context] := by
  dsimp only
  have tailFixed := substituteBinder_absent policy name replacement (.expression .active tail) (by
    simp only [Entry.Value.erase, TypeSubst.typeVars, tailClosed, List.not_mem_nil, not_false_eq_true])
  have contextFixed := substituteBinder_absent policy name replacement context (by
    simp only [contextClosed, List.not_mem_nil, not_false_eq_true])
  have operationFixed := substituteBinder_absent policy name replacement
      (.expression operationMark [.symbol CollectionStdlibSource.appendName, .var left, .var right]) (by
    simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList, Ne.symm leftDifferent, Ne.symm rightDifferent])
  unfold substituteBinder at tailFixed contextFixed operationFixed ⊢
  cases rebuilding : policy.rebuilding <;>
    simp [call, Entry.Value.substitute, Entry.Value.rebuildStatus, rebuilding,
      leftDifferent, rightDifferent] at tailFixed contextFixed operationFixed ⊢ <;>
    simp_all

theorem call_read (policy : Policy) (frame : Frame) (items : List Entry.Value) (init : Entry.Value)
    (left right : String) (context : Entry.Value) (operationMark : Entry.Status)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (initClosed : TypeSubst.typeVars init.erase = [])
    (itemsClosed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = [])
    (contextClosed : TypeSubst.typeVars context.erase = []) :
    let operation := Entry.Value.expression operationMark [.symbol CollectionStdlibSource.appendName, .var left, .var right]
    frame.read policy (call items init left right operation context) = call items init left right operation context := by
  dsimp only
  apply Entry.Value.substitute_of_fixed_variables
  intro name occurs
  simp only [call, Entry.Value.erase, List.map_cons, List.map_nil, TypeSubst.typeVars,
    TypeSubst.typeVarsList, initClosed, itemsClosed, contextClosed, List.nil_append,
    List.append_nil, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at occurs
  have fixedLeft := resolve_of_fixed policy frame left leftFixed
  have fixedRight := resolve_of_fixed policy frame right rightFixed
  aesop

theorem context_substitution (policy : Policy) (name left right : String)
    (context init : Entry.Value) (items : List Entry.Value) (operationMark : Entry.Status)
    (leftDifferent : left ≠ name) (rightDifferent : right ≠ name)
    (itemsClosed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = [])
    (initClosed : TypeSubst.typeVars init.erase = []) :
    let operation := Entry.Value.expression operationMark [.symbol CollectionStdlibSource.appendName, .var left, .var right]
    substituteBinder policy name context
      (.expression .active [.symbol "eval", call items init left right operation (.var name)]) =
      .expression .active [.symbol "eval", call items init left right operation context] := by
  dsimp only
  have itemsFixed := substituteBinder_absent policy name context (.expression .active items) (by
    simp only [Entry.Value.erase, TypeSubst.typeVars, itemsClosed, List.not_mem_nil, not_false_eq_true])
  have initFixed := substituteBinder_absent policy name context init (by
    simp only [initClosed, List.not_mem_nil, not_false_eq_true])
  have operationFixed := substituteBinder_absent policy name context
      (.expression operationMark [.symbol CollectionStdlibSource.appendName, .var left, .var right]) (by
    simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList, Ne.symm leftDifferent, Ne.symm rightDifferent])
  unfold substituteBinder at itemsFixed initFixed operationFixed ⊢
  cases rebuilding : policy.rebuilding <;>
    simp [call, Entry.Value.substitute, Entry.Value.rebuildStatus, rebuilding,
      leftDifferent, rightDifferent] at itemsFixed initFixed operationFixed ⊢ <;>
    simp_all

theorem step_read (policy : Policy) (frame : Frame) (avoid : List String)
    (head : Entry.Value) (tail : List Entry.Value) (init : Entry.Value) (left right : String)
    (context : Entry.Value) (operationMark : Entry.Status)
    (different : left ≠ right)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (initClosed : TypeSubst.typeVars init.erase = []) (headClosed : TypeSubst.typeVars head.erase = [])
    (tailClosed : TypeSubst.typeVarsList (tail.map Entry.Value.erase) = [])
    (contextClosed : TypeSubst.typeVars context.erase = [])
    (fresh : chainName avoid (.expression operationMark [.symbol CollectionStdlibSource.appendName, .var left, .var right]) ∉
      specBindingVars frame.bindings) :
    let operation := Entry.Value.expression operationMark [.symbol CollectionStdlibSource.appendName, .var left, .var right]
    frame.read policy (step avoid head tail init left right operation context) =
      step avoid head tail init left right operation context := by
  dsimp only
  apply Entry.Value.substitute_of_fixed_variables
  intro name occurs
  have replacement := collapse_template avoid init head left right different operationMark
  simp only [step, replacement, call, Entry.Value.erase, List.map_cons, List.map_nil,
    TypeSubst.typeVars, TypeSubst.typeVarsList, initClosed, headClosed, tailClosed, contextClosed,
    List.nil_append, List.append_nil, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at occurs
  have fixedChain := HEFreshSyntaxBinding.resolve_fresh frame _ fresh
  have fixedLeft := resolve_of_fixed policy frame left leftFixed
  have fixedRight := resolve_of_fixed policy frame right rightFixed
  aesop

theorem protected_step_read (policy : Policy) (frame : Frame) (hidden : List String)
    (live : List Atom) (scope : List String) (head : Entry.Value) (tail : List Entry.Value)
    (init : Entry.Value) (left right : String) (context : Entry.Value) (operationMark : Entry.Status)
    (different : left ≠ right) (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (initClosed : TypeSubst.typeVars init.erase = []) (headClosed : TypeSubst.typeVars head.erase = [])
    (tailClosed : TypeSubst.typeVarsList (tail.map Entry.Value.erase) = [])
    (contextClosed : TypeSubst.typeVars context.erase = []) :
    let operation := Entry.Value.expression operationMark [.symbol CollectionStdlibSource.appendName, .var left, .var right]
    frame.read policy (emission hidden live scope frame (head :: tail) init left right operation context) =
      emission hidden live scope frame (head :: tail) init left right operation context := by
  dsimp only
  apply step_read policy frame _ head tail init left right context operationMark different leftFixed rightFixed
    initClosed headClosed tailClosed contextClosed
  exact (protects_caller_and_hidden hidden live scope frame (head :: tail) init left right _ context).1

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldReadback
