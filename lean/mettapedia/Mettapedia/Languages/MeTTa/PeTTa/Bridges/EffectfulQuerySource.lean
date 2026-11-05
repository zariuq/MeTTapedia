import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQuerySource

/-!
# Captured query choices with ordered stateful bodies

The source matcher captures its occurrence choices once. Bodies then run in
authored order, passing the current store from one body to the next and
appending every answer. This is the existing evaluator's shared-state rule,
not an independent-world interpretation of nondeterminism.

The traversal theorem certifies successful completion. A failed private
traversal alone does not authorize rollback of a publicly executed prefix;
an implementation still needs its publication or residual contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics FlatQueryRelationCompilation

abbrev Body := Subst → Effects.State → Option (Effects.State × List Atom)

def traverse (body : Body) : List Subst → Effects.State × List Atom → Option (Effects.State × List Atom)
  | [], receipt => some receipt
  | bindings :: rest, receipt =>
      (body bindings receipt.1).bind fun next => traverse body rest (next.1, receipt.2 ++ next.2)

theorem traverse_append (body : Body) (first later : List Subst) (receipt : Effects.State × List Atom) :
    traverse body (first ++ later) receipt = (traverse body first receipt).bind (traverse body later) := by
  induction first generalizing receipt with
  | nil => rfl
  | cons bindings rest ih =>
      simp only [List.cons_append, traverse, ih, Option.bind_assoc]

theorem traverse_answers_extend (body : Body) (captured : List Subst)
    (before after : Effects.State) (collected answers : List Atom)
    (completed : traverse body captured (before, collected) = some (after, answers)) :
    ∃ suffix, answers = collected ++ suffix := by
  induction captured generalizing before collected with
  | nil =>
      have same : (before, collected) = (after, answers) := Option.some.inj completed
      exact ⟨[], by simpa using (Prod.mk.inj same).2.symm⟩
  | cons bindings rest ih =>
      obtain ⟨next, _, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨suffix, returned⟩ := ih next.1 (collected ++ next.2) later
      exact ⟨next.2 ++ suffix, by simpa only [List.append_assoc] using returned⟩

theorem empty_result_has_empty_prefix (body : Body) (captured : List Subst)
    (before after : Effects.State) (collected : List Atom)
    (completed : traverse body captured (before, collected) = some (after, [])) : collected = [] := by
  obtain ⟨_, equal⟩ := traverse_answers_extend body captured before after collected [] completed
  exact (List.append_eq_nil_iff.mp equal.symm).1

theorem sequence_returns (program : Program) (expression : Atom) (body : Body) (captured : List Subst)
    (law : ∀ bindings ∈ captured, ∀ before after answers, body bindings before = some (after, answers) →
      Returns program bindings before expression after answers)
    (before after : Effects.State) (collected result : List Atom)
    (completed : traverse body captured (before, collected) = some (after, result)) :
    (theory program).MultiStep
      {state := before, control := .sequence (captured.map (fun bindings => .evaluate bindings expression)) collected}
      (finished after result [] []) := by
  induction captured generalizing before collected with
  | nil =>
      have same : (before, collected) = (after, result) := Option.some.inj completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact .step (step_transition rfl) (.refl _)
  | cons bindings rest ih =>
      obtain ⟨next, first, remaining⟩ := Option.bind_eq_some_iff.mp completed
      apply sequence_cons_answers program before next.1 after (.evaluate bindings expression)
        (rest.map fun bound => .evaluate bound expression) collected next.2 result
        (law bindings (by simp) before next.1 next.2 first)
      exact ih (fun bound member => law bound (List.mem_cons_of_mem _ member)) next.1 (collected ++ next.2) remaining

def choices (bindings : Subst) (pattern : Atom) (rows : List Atom) : List Subst :=
  (sourceScan bindings pattern 0 rows).map Prod.snd

theorem scan_bindings (bindings : Subst) (pattern : Atom) (rows : List Atom) (start : Nat) :
    (sourceScan bindings pattern start rows).map Prod.snd = rows.filterMap (matchValue bindings pattern) := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
      cases matched : matchValue bindings pattern row <;> simp [sourceScan, matched, ih]

theorem choices_member (bindings : Subst) (pattern : Atom) (rows : List Atom) (bound : Subst) :
    bound ∈ choices bindings pattern rows ↔ ∃ row ∈ rows, matchValue bindings pattern row = some bound := by
  simp only [choices, scan_bindings, List.mem_filterMap]

theorem choices_extend (bindings : Subst) (pattern : Atom) (rows : List Atom) (bound : Subst)
    (member : bound ∈ choices bindings pattern rows) : bound.lookupExtends bindings := by
  obtain ⟨_, _, matched⟩ := (choices_member bindings pattern rows bound).mp member
  exact matchValue_lookup_extends matched

theorem choices_lookup_outside (bindings : Subst) (pattern : Atom) (rows : List Atom) (bound : Subst)
    (member : bound ∈ choices bindings pattern rows) (name : String)
    (outside : name ∉ Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars pattern) :
    Subst.lookup bound name = Subst.lookup bindings name := by
  obtain ⟨_, _, matched⟩ := (choices_member bindings pattern rows bound).mp member
  exact matchValue_lookup_outside matched name outside

theorem choices_controls (bindings : Subst) (pattern expression : Atom) (rows : List Atom) :
    (choices bindings pattern rows).map (fun bound => Control.evaluate bound expression) =
      queryBodies bindings rows pattern expression := by
  simpa only [choices, List.map_map, Function.comp_def] using
    sourceScan_is_queryBodies bindings pattern expression 0 rows

private theorem path_trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

theorem match_returns (program : Program) (caller : Subst) (before after : Effects.State)
    (space value pattern expression : Atom) (rows : List Atom) (body : Body) (answers : List Atom)
    (spaceReturn : PureReturns program caller before space before value)
    (snapshot : (Effects.readHandle value >>= before.read) = some rows)
    (law : ∀ bindings ∈ choices caller pattern rows, ∀ current next values, body bindings current = some (next, values) →
      Returns program bindings current expression next values)
    (completed : traverse body (choices caller pattern rows) (before, []) = some (after, answers)) :
    Returns program caller before (.expression [.symbol "match", space, pattern, expression]) after answers := by
  refine .step (step_transition rfl) (path_trans
    (path_with_caller_frames program [.query caller pattern expression] spaceReturn) ?_)
  refine .step (step_transition rfl) ?_
  simp only [withFrames, finished, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, queryAlternatives, snapshot]
  have completedBodies := sequence_returns program expression body (choices caller pattern rows)
    law before after [] answers completed
  rw [choices_controls] at completedBodies
  simpa only [finished] using completedBodies

def counted (space pattern expression : Atom) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse",
    .expression [.symbol "match", space, pattern, expression]]]

theorem counted_returns (program : Program) (caller : Subst) (before after : Effects.State)
    (space value pattern expression : Atom) (rows : List Atom) (body : Body) (answers : List Atom)
    (spaceReturn : PureReturns program caller before space before value)
    (snapshot : (Effects.readHandle value >>= before.read) = some rows)
    (law : ∀ bindings ∈ choices caller pattern rows, ∀ current next values, body bindings current = some (next, values) →
      Returns program bindings current expression next values)
    (completed : traverse body (choices caller pattern rows) (before, []) = some (after, answers)) :
    PureReturns program caller before (counted space pattern expression) after (.grounded (.int answers.length)) := by
  have collected := collapse_returns program caller before after _ _
    (match_returns program caller before after space value pattern expression rows body answers spaceReturn snapshot law completed)
  exact native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource
