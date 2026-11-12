import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericSource
import Mettapedia.Languages.MeTTa.HE.ContextualUnificationFrame

/-!
# Source-order capture of the authored collection let

The pattern aliases the caller's still-unassigned variable. The collected
tuple is captured as marked data, and the template remains open in the two
fold binders. A source frame is earned from the complete local unifier trace.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetCapture

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEFreshSyntaxBinding HECollectionNumericFold

def template (listName left right : String) (init : Int) : Entry.Value :=
  .expression .active [.symbol "foldl-atom", .var listName, number init, .var left, .var right,
    HECollectionFoldSourceLoop.operation .active left right (operatorName := "+")]

def call (values : List Int) (init : Int) (listName left right : String) (itemsMark : Entry.Status) : Entry.Value :=
  .expression .active [.symbol "let", .var listName, .expression itemsMark (numbers values), template listName left right init]

def pattern (names : Fin 6 → String) : Atom :=
  .expression [.symbol "let", .var (names 3), .var (names 4), .var (names 5)]

def body (names : Fin 6 → String) : Atom :=
  .expression [.symbol "unify", .var (names 4), .var (names 3), .var (names 5), Atom.empty]

def instruction (values : List Int) (init : Int) (patternName left right : String) (itemsMark : Entry.Status) : Entry.Value :=
  .expression .active [.symbol "unify", .expression itemsMark (numbers values), .var patternName,
    template patternName left right init, Entry.Value.ofAtom Atom.empty]

theorem template_read (policy : Policy) (before : Frame) (listName left right listAfter : String) (init : Int)
    (listRead : before.read policy (.var listName) = .var listAfter)
    (leftRead : before.read policy (.var left) = .var left)
    (rightRead : before.read policy (.var right) = .var right) :
    before.read policy (template listName left right init) = template listAfter left right init := by
  have resolved (name : String) (value : Entry.Value) (read : before.read policy (.var name) = value) :
      Entry.Value.resolve before.environment name = value := by
    simpa only [Frame.read, Entry.Value.substitute] using read
  simp only [template, HECollectionFoldSourceLoop.operation, Frame.read, Entry.Value.substitute,
    resolved _ _ listRead, resolved _ _ leftRead, resolved _ _ rightRead,
    HEFreshSyntaxBinding.ground_substitution policy.rebuilding _ (number init) (number_closed init),
    List.map_cons, List.map_nil, HEFreshEquationFrames.Range.active_rebuild]

theorem capture (policy : Policy) (before : Frame) (names : Fin 6 → String)
    (injective : Function.Injective names)
    (fresh : ∀ i, 3 ≤ i.val → names i ∉ specBindingVars before.bindings)
    (fixed : ∀ i, i.val < 3 → before.read policy (.var (names i)) = .var (names i))
    (values : List Int) (init : Int) (itemsMark : Entry.Status) :
    ∃ after : Frame,
      Spec.Eval.Steps.UnifyCandidateRel
        (call values init (names 0) (names 1) (names 2) itemsMark).erase (pattern names)
        before.bindings after.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment
        (call values init (names 0) (names 1) (names 2) itemsMark)
        (Entry.Value.ofAtom (pattern names)) after.environment ∧
      after.read policy (Entry.Value.ofAtom (body names)) =
        instruction values init (names 3) (names 1) (names 2) itemsMark ∧
      after.read policy (.var (names 3)) = .var (names 3) ∧
      after.read policy (.var (names 1)) = .var (names 1) ∧
      after.read policy (.var (names 2)) = .var (names 2) := by
  have apart (i j : Fin 6) (different : i ≠ j) : names i ≠ names j := fun same => different (injective same)
  have namesEq (i j : Fin 6) : names i = names j ↔ i = j := ⟨fun same => injective same, congrArg names⟩
  have fixed0 := fixed 0 (by decide)
  let aliased := ContextualAlias.aliasFrame policy before (names 0) (names 3) fixed0 (fresh 3 (by decide)) (apart 0 3 (by decide))
  have aliasRead : aliased.read policy (.var (names 0)) = .var (names 3) :=
    ContextualAlias.bound_read policy policy before _ _ fixed0 (fresh 3 (by decide)) (apart 0 3 (by decide))
  have aliasFixed (i : Fin 6) (different : i ≠ 0)
      (oldFixed : before.read policy (.var (names i)) = .var (names i)) :
      aliased.read policy (.var (names i)) = .var (names i) :=
    ContextualAlias.other_fixed policy policy before _ _ _ fixed0 (fresh 3 (by decide))
      (apart 0 3 (by decide)) (apart i 0 different) oldFixed
  have aliasFresh (i : Fin 6) (lower : 4 ≤ i.val) : names i ∉ specBindingVars aliased.bindings := by
    rw [ContextualAlias.support]
    simp [fresh i (by omega), namesEq, show i ≠ 0 by omega, show i ≠ 3 by omega]
  let tuple := Entry.Value.expression itemsMark (numbers values)
  have tupleClosed : TypeSubst.typeVars tuple.erase = [] := by
    simpa only [tuple, Entry.Value.erase, TypeSubst.typeVars] using numbers_closed values
  let withData := bindFrame policy aliased (names 4) tuple (aliasFresh 4 (by decide)) (by simp [tupleClosed])
  have dataFixed (i : Fin 6) (different : i ≠ 4)
      (oldFixed : aliased.read policy (.var (names i)) = .var (names i)) :
      withData.read policy (.var (names i)) = .var (names i) :=
    HEOpenSyntaxBinding.other_fixed_read policy policy aliased _ _ tuple (aliasFresh 4 (by decide))
      (by simp [tupleClosed]) (apart i 4 different) oldFixed
  have freshFixed (i : Fin 6) (lower : 3 ≤ i.val) : before.read policy (.var (names i)) = .var (names i) := by
    simpa only [Frame.read, Entry.Value.substitute] using resolve_fresh before _ (fresh i lower)
  have fixed3 := dataFixed 3 (by decide) (aliasFixed 3 (by decide) (freshFixed 3 (by decide)))
  have fixed1 := dataFixed 1 (by decide) (aliasFixed 1 (by decide) (fixed 1 (by decide)))
  have fixed2 := dataFixed 2 (by decide) (aliasFixed 2 (by decide) (fixed 2 (by decide)))
  have oldListRead : withData.read policy (.var (names 0)) = .var (names 3) :=
    HEOpenSyntaxBinding.older_untouched_read policy policy aliased (names 4) (names 0) tuple (.var (names 3))
      (aliasFresh 4 (by decide)) (by simp [tupleClosed]) (apart 0 4 (by decide)) aliasRead
      (by simp [Entry.Value.erase, TypeSubst.typeVars, namesEq])
  let captured := template (names 3) (names 1) (names 2) init
  have capturedFixed : withData.read policy captured = captured := template_read policy withData _ _ _ _ init fixed3 fixed1 fixed2
  have originalTemplate : withData.read policy (template (names 0) (names 1) (names 2) init) = captured :=
    template_read policy withData _ _ _ _ init oldListRead fixed1 fixed2
  have templateFresh : names 5 ∉ specBindingVars withData.bindings :=
    HEFreshSyntaxBinding.other_stays_fresh policy aliased (names 4) (names 5) tuple
      (aliasFresh 4 (by decide)) (aliasFresh 5 (by decide)) (apart 5 4 (by decide)) tupleClosed
  have templateAbsent : names 5 ∉ TypeSubst.typeVars captured.erase := by
    simp [captured, template, HECollectionFoldSourceLoop.operation, Entry.Value.erase,
      TypeSubst.typeVars, TypeSubst.typeVarsList, number_closed, namesEq]
  let capturedFrame := bindFrame policy withData (names 5) captured templateFresh templateAbsent
  have templateUnified : Entry.Value.UnifyRel policy.rebuilding withData.environment
      (template (names 0) (names 1) (names 2) init) (.var (names 5)) capturedFrame.environment := by
    apply Entry.Value.UnifyRel.ordinary
    change Entry.Value.AppliedUnifyRel policy.rebuilding withData.environment
      (withData.read policy (template (names 0) (names 1) (names 2) init))
      (withData.read policy (.var (names 5))) capturedFrame.environment
    rw [originalTemplate]
    simp only [Frame.read, Entry.Value.substitute, resolve_fresh withData (names 5) templateFresh]
    exact .bindRight (by intro key; simp [captured, template, Entry.Value.erase]) templateAbsent
  have trace : Entry.Value.UnifyRel policy.rebuilding before.environment
      (call values init (names 0) (names 1) (names 2) itemsMark) (Entry.Value.ofAtom (pattern names)) capturedFrame.environment := by
    have resolveFixed (i : Fin 6) : Entry.Value.resolve before.environment (names i) = .var (names i) := by
      by_cases small : i.val < 3
      · simpa only [Frame.read, Entry.Value.substitute] using fixed i small
      · exact resolve_fresh before _ (fresh i (by omega))
    apply Entry.Value.UnifyRel.ordinary
    have queryFixed : before.read policy (call values init (names 0) (names 1) (names 2) itemsMark) =
        call values init (names 0) (names 1) (names 2) itemsMark := by
      apply Entry.Value.substitute_of_fixed_variables
      intro key occurs
      simp only [call, template, HECollectionFoldSourceLoop.operation, Entry.Value.erase,
        List.map_cons, List.map_nil, TypeSubst.typeVars, TypeSubst.typeVarsList,
        numbers_closed, number_closed, List.nil_append, List.append_nil] at occurs
      aesop
    change Entry.Value.AppliedUnifyRel policy.rebuilding before.environment
      (before.read policy (call values init (names 0) (names 1) (names 2) itemsMark))
      (before.read policy (Entry.Value.ofAtom (pattern names))) capturedFrame.environment
    rw [queryFixed]
    simp only [pattern, Entry.Value.ofAtom, Frame.read, Entry.Value.substitute, List.map_cons, List.map_nil,
      resolveFixed, HEFreshEquationFrames.Range.active_rebuild, call]
    exact .expression (.cons (.ordinary (.identical (by simp [Entry.Value.substitute])))
      (.cons (ContextualAlias.unifies policy before _ _ fixed0 (fresh 3 (by decide)) (apart 0 3 (by decide)))
        (.cons (source_binding policy aliased (names 4) tuple (aliasFresh 4 (by decide)) tupleClosed)
          (.cons templateUnified (.nil _)))))
  obtain ⟨after, reachedEnvironment, candidate⟩ := ContextualUnificationFrame.frame_of_unification policy before _ _ _ trace
  have sameRead (value : Entry.Value) : after.read policy value = capturedFrame.read policy value := by
    simp only [Frame.read, reachedEnvironment]
  have lastFixed (i : Fin 6) (different : i ≠ 5)
      (priorFixed : withData.read policy (.var (names i)) = .var (names i)) :
      after.read policy (.var (names i)) = .var (names i) := by
    rw [sameRead]
    exact HEOpenSyntaxBinding.other_fixed_read policy policy withData _ _ captured templateFresh templateAbsent
      (apart i 5 different) priorFixed
  have tupleRead : capturedFrame.read policy (.var (names 4)) = tuple :=
    HEOpenSyntaxBinding.older_closed_read policy policy withData _ _ captured tuple templateFresh templateAbsent
      (apart 4 5 (by decide)) (bound_read policy aliased _ tuple (aliasFresh 4 (by decide)) tupleClosed policy) tupleClosed
  have capturedRead : capturedFrame.read policy (.var (names 5)) = captured :=
    HEOpenSyntaxBinding.bound_read_fixed policy policy withData _ captured templateFresh templateAbsent capturedFixed
  have materialized (name : String) (value : Entry.Value) (read : capturedFrame.read policy (.var name) = value) :
      Entry.Value.resolve capturedFrame.environment name = value := by
    simpa only [Frame.read, Entry.Value.substitute] using read
  refine ⟨after, ?_, ?_, ?_, lastFixed 3 (by decide) fixed3, lastFixed 1 (by decide) fixed1, lastFixed 2 (by decide) fixed2⟩
  · simpa only [Entry.Value.erase_ofAtom] using candidate
  · simpa only [reachedEnvironment] using trace
  · rw [sameRead]
    have patternRead := HEOpenSyntaxBinding.other_fixed_read policy policy withData _ _ captured templateFresh templateAbsent
      (apart 3 5 (by decide)) fixed3
    simp only [body, Entry.Value.ofAtom, List.map_cons, List.map_nil, Frame.read, Entry.Value.substitute,
      materialized _ _ tupleRead, materialized _ _ capturedRead, materialized _ _ patternRead,
      HEFreshEquationFrames.Range.active_rebuild, instruction, tuple, captured, Atom.empty]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetCapture
