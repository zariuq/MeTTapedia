import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldOpenParameters
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldFunction

/-! Source-order capture of the standard fold's data and variable operands.
These are contextual unifier derivations, not assumptions about a finished
invocation or substitutions reconstructed from erased result values. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldParameterCapture

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEFreshSyntaxBinding

theorem unify_list_append {rebuilding : Entry.RebuildPolicy} {before middle after : Entry.Value.Environment}
    {first firstPattern rest restPattern : List Entry.Value}
    (initial : Entry.Value.UnifyListRel rebuilding before first firstPattern middle)
    (remaining : Entry.Value.UnifyListRel rebuilding middle rest restPattern after) :
    Entry.Value.UnifyListRel rebuilding before (first ++ rest) (firstPattern ++ restPattern) after :=
  match initial with
  | .nil _ => remaining
  | .cons head tail => .cons head (unify_list_append tail remaining)
termination_by structural initial

theorem closed_prefix_fixed (policy : Policy) (before : Frame) (left right : String)
    (first second : Entry.Value)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (different : right ≠ left) (firstClosed : TypeSubst.typeVars first.erase = [])
    (secondClosed : TypeSubst.typeVars second.erase = []) :
    ∃ after : Frame,
      Entry.Value.UnifyListRel policy.rebuilding before.environment [first, second] [.var left, .var right] after.environment ∧
      after.bindings = (before.bindings.assign left first.erase).assign right second.erase ∧
      (∀ readingPolicy, after.read readingPolicy (.var left) = first ∧ after.read readingPolicy (.var right) = second) ∧
      (∀ name, name ∈ specBindingVars after.bindings ↔ name ∈ specBindingVars before.bindings ∨ name = left ∨ name = right) ∧
      (∀ readingPolicy name, name ≠ left → name ≠ right → before.read readingPolicy (.var name) = .var name →
        after.read readingPolicy (.var name) = .var name) := by
  let middle := bindFrame policy before left first leftFresh (by simp [firstClosed])
  have rightStillFresh : right ∉ specBindingVars middle.bindings :=
    HEFreshSyntaxBinding.other_stays_fresh policy before left right first leftFresh rightFresh different firstClosed
  let after := bindFrame policy middle right second rightStillFresh (by simp [secondClosed])
  refine ⟨after, .cons (source_binding policy before left first leftFresh firstClosed)
    (.cons (source_binding policy middle right second rightStillFresh secondClosed) (.nil _)), rfl, ?_, ?_, ?_⟩
  · intro readingPolicy
    exact ⟨prior_binding_read policy before left right first second leftFresh rightFresh different firstClosed secondClosed readingPolicy,
      bound_read policy middle right second rightStillFresh secondClosed readingPolicy⟩
  · intro name
    dsimp only [after]
    rw [HEOpenSyntaxBinding.mem_bound_support]
    dsimp only [middle]
    rw [HEOpenSyntaxBinding.mem_bound_support]
    simp only [firstClosed, secondClosed, List.not_mem_nil, or_false, or_assoc]
  · intro readingPolicy name notLeft notRight fixed
    have kept := HEOpenSyntaxBinding.other_fixed_read policy readingPolicy before left name first leftFresh
      (by simp [firstClosed]) notLeft fixed
    exact HEOpenSyntaxBinding.other_fixed_read policy readingPolicy middle right name second rightStillFresh
      (by simp [secondClosed]) notRight kept

theorem closed_prefix (policy : Policy) (before : Frame) (left right : String)
    (first second : Entry.Value)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (different : right ≠ left) (firstClosed : TypeSubst.typeVars first.erase = [])
    (secondClosed : TypeSubst.typeVars second.erase = []) :
    ∃ after : Frame,
      Entry.Value.UnifyListRel policy.rebuilding before.environment [first, second] [.var left, .var right] after.environment ∧
      after.bindings = (before.bindings.assign left first.erase).assign right second.erase ∧
      (∀ readingPolicy, after.read readingPolicy (.var left) = first ∧ after.read readingPolicy (.var right) = second) ∧
      (∀ name, name ∈ specBindingVars after.bindings ↔ name ∈ specBindingVars before.bindings ∨ name = left ∨ name = right) := by
  obtain ⟨after, unified, bindings, reads, support, _fixed⟩ := closed_prefix_fixed policy before left right first second
    leftFresh rightFresh different firstClosed secondClosed
  exact ⟨after, unified, bindings, reads, support⟩

def query (pairs : List Entry.Value) (init : Entry.Value) (left right : String)
    (operatorName : String := CollectionStdlibSource.appendName) (itemsMark : Entry.Status := .active) : Entry.Value :=
  .expression .active [.symbol "foldl-atom", .expression itemsMark pairs, init, .var left, .var right,
    HECollectionFoldSourceLoop.operation (operatorName := operatorName) .active left right]

def pattern (names : Fin 8 → String) : Atom :=
  .expression [.symbol "foldl-atom", .var (names 2), .var (names 3), .var (names 4), .var (names 5), .var (names 6)]

def body (names : Fin 8 → String) : Atom :=
  .expression [.symbol "function", .expression [.symbol "chain", .expression [.symbol "context-space"], .var (names 7),
    .expression [.symbol "eval", .expression [.symbol CollectionStdlibSource.foldName,
      .var (names 2), .var (names 3), .var (names 4), .var (names 5), .var (names 6), .var (names 7)]]]]

theorem capture_fixed (policy : Policy) (before : Frame) (names : Fin 8 → String)
    (injective : Function.Injective names) (fresh : ∀ index, 2 ≤ index.val → names index ∉ specBindingVars before.bindings)
    (leftFixed : before.read policy (.var (names 0)) = .var (names 0))
    (rightFixed : before.read policy (.var (names 1)) = .var (names 1))
    (pairs : List Entry.Value) (init : Entry.Value)
    (pairsClosed : TypeSubst.typeVarsList (pairs.map Entry.Value.erase) = [])
    (initClosed : TypeSubst.typeVars init.erase = [])
    (operatorName : String := CollectionStdlibSource.appendName) (itemsMark : Entry.Status := .active) :
    ∃ after : Frame,
      Entry.Value.UnifyRel policy.rebuilding before.environment (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init (names 0) (names 1))
        (Entry.Value.ofAtom (pattern names)) after.environment ∧
      after.read policy (Entry.Value.ofAtom (body names)) =
        HECollectionFoldFunction.function pairs init (names 4) (names 5) (names 7) .active (operatorName := operatorName) (itemsMark := itemsMark) ∧
      after.read policy (.var (names 4)) = .var (names 4) ∧
      after.read policy (.var (names 5)) = .var (names 5) := by
  have apart (i j : Fin 8) (different : i ≠ j) : names i ≠ names j := fun same => different (injective same)
  have namesEq (i j : Fin 8) : names i = names j ↔ i = j := ⟨fun same => injective same, congrArg names⟩
  have listClosed : TypeSubst.typeVars (.expression itemsMark pairs : Entry.Value).erase = [] := by
    simpa only [Entry.Value.erase, TypeSubst.typeVars] using pairsClosed
  obtain ⟨closedFrame, closedUnified, _, closedReads, closedSupport, closedFixed⟩ :=
    closed_prefix_fixed policy before (names 2) (names 3) (.expression itemsMark pairs) init
      (fresh 2 (by decide)) (fresh 3 (by decide)) (apart 3 2 (by decide)) listClosed initClosed
  let aliasNames : Fin 4 → String := ![names 0, names 1, names 4, names 5]
  have aliasInjective : Function.Injective aliasNames := by
    intro i j same
    fin_cases i <;> fin_cases j <;> simp_all [aliasNames]
  have firstFixed : closedFrame.read policy (.var (names 0)) = .var (names 0) :=
    closedFixed policy (names 0) (apart 0 2 (by decide)) (apart 0 3 (by decide)) leftFixed
  have secondFixed : closedFrame.read policy (.var (names 1)) = .var (names 1) :=
    closedFixed policy (names 1) (apart 1 2 (by decide)) (apart 1 3 (by decide)) rightFixed
  have firstFresh : names 4 ∉ specBindingVars closedFrame.bindings := by
    rw [closedSupport]
    simp [fresh 4 (by decide), namesEq]
  have secondFresh : names 5 ∉ specBindingVars closedFrame.bindings := by
    rw [closedSupport]
    simp [fresh 5 (by decide), namesEq]
  obtain ⟨aliasFrame, aliasesUnified, _, aliasReads, oldReads, aliasSupport⟩ :=
    HEFoldOpenParameters.capture_fixed policy closedFrame aliasNames aliasInjective
      (by simpa [aliasNames] using firstFixed) (by simpa [aliasNames] using secondFixed)
      (by simpa [aliasNames] using firstFresh) (by simpa [aliasNames] using secondFresh)
  have support (i : Fin 8) : names i ∈ specBindingVars aliasFrame.bindings ↔
      names i ∈ specBindingVars before.bindings ∨ i = 2 ∨ i = 3 ∨ i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 := by
    rw [aliasSupport, closedSupport]
    simp only [aliasNames, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, namesEq]
    tauto
  have opFresh : names 6 ∉ specBindingVars aliasFrame.bindings := by rw [support]; simp [fresh 6 (by decide)]
  have spaceFresh : names 7 ∉ specBindingVars aliasFrame.bindings := by rw [support]; simp [fresh 7 (by decide)]
  let operation := HECollectionFoldSourceLoop.operation (operatorName := operatorName) .active (names 4) (names 5)
  have opAbsent : names 6 ∉ TypeSubst.typeVars operation.erase := by
    simp [operation, HECollectionFoldSourceLoop.operation, Entry.Value.erase, TypeSubst.typeVars,
      TypeSubst.typeVarsList, namesEq]
  let after := bindFrame policy aliasFrame (names 6) operation opFresh opAbsent
  have aliasResolve0 : Entry.Value.resolve aliasFrame.environment (names 0) = .var (names 4) := by
    simpa [Frame.read, Entry.Value.substitute, aliasNames] using (aliasReads policy).1
  have aliasResolve1 : Entry.Value.resolve aliasFrame.environment (names 1) = .var (names 5) := by
    simpa [Frame.read, Entry.Value.substitute, aliasNames] using (aliasReads policy).2.1
  have fixedOperation : aliasFrame.read policy operation = operation := by
    have leftRead := (aliasReads policy).2.2.1
    have rightRead := (aliasReads policy).2.2.2
    have leftResolve : Entry.Value.resolve aliasFrame.environment (names 4) = .var (names 4) := by
      simpa [Frame.read, Entry.Value.substitute, aliasNames] using leftRead
    have rightResolve : Entry.Value.resolve aliasFrame.environment (names 5) = .var (names 5) := by
      simpa [Frame.read, Entry.Value.substitute, aliasNames] using rightRead
    simp only [operation, HECollectionFoldSourceLoop.operation, Frame.read, Entry.Value.substitute,
      List.map_cons, List.map_nil, leftResolve, rightResolve, HEFreshEquationFrames.Range.active_rebuild]
  have opRead : aliasFrame.read policy (HECollectionFoldSourceLoop.operation (operatorName := operatorName) .active (names 0) (names 1)) = operation := by
    simp only [operation, HECollectionFoldSourceLoop.operation, Frame.read, Entry.Value.substitute,
      List.map_cons, List.map_nil, aliasResolve0, aliasResolve1, HEFreshEquationFrames.Range.active_rebuild]
  have opUnified : Entry.Value.UnifyRel policy.rebuilding aliasFrame.environment
      (HECollectionFoldSourceLoop.operation (operatorName := operatorName) .active (names 0) (names 1)) (.var (names 6)) after.environment := by
    apply Entry.Value.UnifyRel.ordinary
    have readEq : Entry.Value.substitute policy.rebuilding (Entry.Value.resolve aliasFrame.environment)
        (HECollectionFoldSourceLoop.operation (operatorName := operatorName) .active (names 0) (names 1)) = operation := by
      simpa only [Frame.read] using opRead
    rw [readEq]
    simp only [Entry.Value.substitute, resolve_fresh aliasFrame (names 6) opFresh]
    exact .bindRight (by intro name; simp [operation, HECollectionFoldSourceLoop.operation, Entry.Value.erase]) opAbsent
  have components := unify_list_append closedUnified (unify_list_append aliasesUnified (.cons opUnified (.nil _)))
  have originalResolve (i : Fin 8) : Entry.Value.resolve before.environment (names i) = .var (names i) := by
    by_cases first : i = 0
    · subst i
      simpa only [Frame.read, Entry.Value.substitute] using leftFixed
    by_cases second : i = 1
    · subst i
      simpa only [Frame.read, Entry.Value.substitute] using rightFixed
    exact resolve_fresh before _ (fresh i (by omega))
  have whole : Entry.Value.UnifyRel policy.rebuilding before.environment (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init (names 0) (names 1))
      (Entry.Value.ofAtom (pattern names)) after.environment := by
    apply Entry.Value.UnifyRel.ordinary
    simp only [query, pattern, HECollectionFoldSourceLoop.operation, Entry.Value.ofAtom, List.map_cons, List.map_nil, Entry.Value.substitute,
      originalResolve, ground_substitution policy.rebuilding _ init initClosed,
      HEFreshEquationFrames.Range.active_rebuild]
    have tupleRead := ground_substitution policy.rebuilding (Entry.Value.resolve before.environment)
      (.expression itemsMark pairs) listClosed
    simp only [Entry.Value.substitute] at tupleRead
    rw [tupleRead]
    apply Entry.Value.AppliedUnifyRel.expression
    apply Entry.Value.UnifyListRel.cons (.ordinary (.identical (by simp [Entry.Value.substitute])))
    simpa [aliasNames, HECollectionFoldSourceLoop.operation] using components
  have firstRead := oldReads policy (names 2) (.expression itemsMark pairs)
    (apart 2 0 (by decide)) (apart 2 1 (by decide)) (closedReads policy).1 listClosed
  have secondRead := oldReads policy (names 3) init
    (apart 3 0 (by decide)) (apart 3 1 (by decide)) (closedReads policy).2 initClosed
  have listRead := HEOpenSyntaxBinding.older_closed_read policy policy aliasFrame (names 6) (names 2)
    operation (.expression itemsMark pairs) opFresh opAbsent (apart 2 6 (by decide)) firstRead listClosed
  have initRead := HEOpenSyntaxBinding.older_closed_read policy policy aliasFrame (names 6) (names 3)
    operation init opFresh opAbsent (apart 3 6 (by decide)) secondRead initClosed
  have leftRead := HEOpenSyntaxBinding.other_fixed_read policy policy aliasFrame (names 6) (names 4)
    operation opFresh opAbsent (apart 4 6 (by decide)) (by simpa [aliasNames] using (aliasReads policy).2.2.1)
  have rightRead := HEOpenSyntaxBinding.other_fixed_read policy policy aliasFrame (names 6) (names 5)
    operation opFresh opAbsent (apart 5 6 (by decide)) (by simpa [aliasNames] using (aliasReads policy).2.2.2)
  have templateRead := HEOpenSyntaxBinding.bound_read_fixed policy policy aliasFrame (names 6) operation opFresh opAbsent fixedOperation
  have spaceRead : after.read policy (.var (names 7)) = .var (names 7) := by
    apply HEOpenSyntaxBinding.other_fixed_read policy policy aliasFrame (names 6) (names 7) operation opFresh opAbsent
      (apart 7 6 (by decide))
    simpa only [Frame.read, Entry.Value.substitute] using resolve_fresh aliasFrame (names 7) spaceFresh
  refine ⟨after, whole, ?_, leftRead, rightRead⟩
  have materialized : ∀ name value, after.read policy (.var name) = value → Entry.Value.resolve after.environment name = value := by
    intro name value read
    simpa only [Frame.read, Entry.Value.substitute] using read
  simp only [body, Entry.Value.ofAtom, List.map_cons, List.map_nil, Frame.read, Entry.Value.substitute,
    materialized _ _ listRead, materialized _ _ initRead, materialized _ _ leftRead, materialized _ _ rightRead,
    materialized _ _ templateRead, materialized _ _ spaceRead, HEFreshEquationFrames.Range.active_rebuild,
    HECollectionFoldFunction.function, HECollectionFoldFunction.body, HECollectionFoldEmission.call, operation]

theorem capture (policy : Policy) (before : Frame) (names : Fin 8 → String)
    (injective : Function.Injective names) (fresh : ∀ index, names index ∉ specBindingVars before.bindings)
    (pairs : List Entry.Value) (init : Entry.Value)
    (pairsClosed : TypeSubst.typeVarsList (pairs.map Entry.Value.erase) = [])
    (initClosed : TypeSubst.typeVars init.erase = [])
    (operatorName : String := CollectionStdlibSource.appendName) (itemsMark : Entry.Status := .active) :
    ∃ after : Frame,
      Entry.Value.UnifyRel policy.rebuilding before.environment (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init (names 0) (names 1))
        (Entry.Value.ofAtom (pattern names)) after.environment ∧
      after.read policy (Entry.Value.ofAtom (body names)) =
        HECollectionFoldFunction.function pairs init (names 4) (names 5) (names 7) .active (operatorName := operatorName) (itemsMark := itemsMark) ∧
      after.read policy (.var (names 4)) = .var (names 4) ∧
      after.read policy (.var (names 5)) = .var (names 5) := by
  have leftFixed : before.read policy (.var (names 0)) = .var (names 0) := by
    simpa only [Frame.read, Entry.Value.substitute] using resolve_fresh before (names 0) (fresh 0)
  have rightFixed : before.read policy (.var (names 1)) = .var (names 1) := by
    simpa only [Frame.read, Entry.Value.substitute] using resolve_fresh before (names 1) (fresh 1)
  exact capture_fixed policy before names injective (fun index _ => fresh index) leftFixed rightFixed
    pairs init pairsClosed initClosed operatorName itemsMark

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldParameterCapture
