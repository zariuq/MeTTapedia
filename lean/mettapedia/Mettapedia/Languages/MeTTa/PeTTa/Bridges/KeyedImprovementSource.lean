import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorSource
import Mettapedia.Machines.KeyedImprovement

/-!
# Natural-valued keyed improvement at the PeTTa source boundary

The authored block collects the complete key fibre, inserts an absent value,
or removes and replaces a single strictly larger value. Multiple rows refuse;
they are not silently deduplicated or reduced to their minimum. The worker is
private and its completed-state law does not make removal and insertion atomic.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces
open FlatQueryRelationCompilation (sourceScan)

def number (value : Nat) : Atom := .grounded (.int value)

structure Names where
  space : String
  vertex : String
  candidate : String
  current : String
  previous : String
  discard : String
  distinct : [space, vertex, candidate, current, previous, discard].Nodup

def row (head : String) (key value : Atom) : Atom := .expression [.symbol head, key, value]

def bindings (names : Names) (target : Handle) (key candidate : Nat) : Subst :=
  [(names.candidate, number candidate), (names.vertex, number key), (names.space, Effects.handleValue target)]

theorem bindings_location (names : Names) (target : Handle) (key candidate : Nat) :
    Subst.lookup (bindings names target key candidate) names.space = some (Effects.handleValue target) := by
  have separated := names.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at separated
  simp [bindings, Subst.lookup, Ne.symm separated.1.1, Ne.symm separated.1.2.1]

def pattern (names : Names) (head : String) : Atom := row head (.var names.vertex) (.var names.previous)

def query (names : Names) (head : String) : Atom :=
  .expression [.symbol "match", .var names.space, pattern names head, .var names.previous]

def values (names : Names) (head : String) (caller : Subst) (rows : List Atom) : List Atom :=
  (sourceScan caller (pattern names head) 0 rows).map (fun result => applySubst result.2 (.var names.previous))

def insertion (names : Names) (head : String) : Atom :=
  .expression [.symbol "add-atom", .var names.space, row head (.var names.vertex) (.var names.candidate)]

def removal (names : Names) (head : String) : Atom :=
  .expression [.symbol "remove-atom", .var names.space, row head (.var names.vertex) (.var names.previous)]

def insertBody (names : Names) (head : String) : Atom :=
  .expression [.symbol "let", .var names.discard, insertion names head, .var names.vertex]

def replaceBody (names : Names) (head : String) : Atom :=
  .expression [.symbol "let*", .expression [
    .expression [.var names.discard, removal names head],
    .expression [.var names.discard, insertion names head]], .var names.vertex]

def comparison (names : Names) : Atom := .expression [.symbol "<", .var names.candidate, .var names.previous]

def improvementBody (names : Names) (head : String) : Atom :=
  .expression [.symbol "if", comparison names, replaceBody names head, .expression [.symbol "empty"]]

def existingBody (names : Names) (head : String) : Atom :=
  .expression [.symbol "let", .expression [.var names.previous], .var names.current, improvementBody names head]

def absent (names : Names) : Atom :=
  .expression [.symbol "==", .var names.current, .expression []]

def source (names : Names) (head : String) : Atom :=
  .expression [.symbol "let", .var names.current, .expression [.symbol "collapse", query names head],
    .expression [.symbol "if", absent names, insertBody names head, existingBody names head]]

/-- `none` is unsupported, whereas `some none` certifies an empty fibre. -/
def decodeFibre : List Atom → Option (Option Nat)
  | [] => some none
  | [.grounded (.int (.ofNat old))] => some (some old)
  | _ => none

def write (before : Effects.State) (target : Handle) (head : String) (key candidate : Nat)
    (old : Option Nat) : Option (Effects.State × List Atom) :=
  match old with
  | none => do
      let after ← Effects.insert before target (row head (number key) (number candidate))
      pure (after, [number key])
  | some previous => if candidate < previous then do
      let middle ← Effects.erase before target (row head (number key) (number previous))
      let after ← Effects.insert middle target (row head (number key) (number candidate))
      pure (after, [number key])
    else some (before, [])

def run (names : Names) (head : String) (target : Handle) (key candidate : Nat)
    (before : Effects.State) : Option (Effects.State × List Atom) := do
  if head ∈ ["=", ":", ",", "cons"] then none else do
    let rows ← before.read target
    if ClosedQueryAdmission.rowsReady (pattern names head) rows then do
      let old ← decodeFibre (values names head (bindings names target key candidate) rows)
      write before target head key candidate old
    else none

theorem decodeFibre_exact (answers : List Atom) (old : Option Nat)
    (decoded : decodeFibre answers = some old) : answers = old.toList.map number := by
  unfold decodeFibre at decoded
  split at decoded
  · cases Option.some.inj decoded; rfl
  · cases Option.some.inj decoded; rfl
  · cases decoded

theorem query_returns (names : Names) (head : String) (program : Program) (caller : Subst)
    (target : Handle) (state : Effects.State) (rows : List Atom)
    (location : Subst.lookup caller names.space = some (Effects.handleValue target))
    (snapshot : state.read target = some rows) :
    Returns program caller state (query names head) state (values names head caller rows) := by
  have space : PureReturns program caller state (.var names.space) state (Effects.handleValue target) := by
    simpa only [applySubst, location, Option.getD_some] using variable_returns program caller state names.space
  have returned := CapturedQuerySource.match_returns program state caller (.var names.space)
    (Effects.handleValue target) rows space (by simp [snapshot]) (pattern names head) (.var names.previous)
    (fun bound => [applySubst bound (.var names.previous)])
    (fun _ _ bound _ => variable_returns program bound state names.previous)
  simpa only [query, values, ← List.map_eq_flatMap] using returned

theorem remove_returns (program : Program) (caller : Subst) (before after : Effects.State)
    (space : String) (pattern : Atom) (target : Handle) (fields : List Atom)
    (location : Subst.lookup caller space = some (Effects.handleValue target))
    (rendered : applySubst caller pattern = .expression fields) (nonempty : fields ≠ [])
    (erased : Effects.erase before target (.expression fields) = some after) :
    PureReturns program caller before (.expression [.symbol "remove-atom", .var space, pattern])
      after (Effects.boolean true) := by
  obtain ⟨rows, snapshot, _⟩ := Effects.erase_reads_back erased
  have applied : StdLib.apply before "remove-atom" [Effects.handleValue target, applySubst caller pattern] =
      .ok (after, [Effects.boolean true]) := by
    cases fields with
    | nil => contradiction
    | cons first rest =>
        change (match Effects.readHandle (Effects.handleValue target) with
          | none => Except.error Effects.Fault.invalidSpace
          | some handle => match before.read handle with
            | none => Except.error Effects.Fault.invalidSpace
            | some _ => match applySubst caller pattern with
              | .var _ => Except.ok (before, [Effects.boolean true])
              | .expression (_ :: _) => match Effects.erase before handle (applySubst caller pattern) with
                | some result => Except.ok (result, [Effects.boolean true])
                | none => Except.error Effects.Fault.invalidSpace
              | _ => Except.ok (before, [])) = _
        simp [rendered, snapshot, erased]
  have native := native_function_arguments_return program caller before after "remove-atom"
    [Effects.handleValue target, applySubst caller pattern] 2 (Effects.boolean true) (by decide) (by decide) applied
  have raw := raw_argument_answers program caller before after "remove-atom" pattern []
    [Effects.handleValue target] 1 [Effects.boolean true]
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) native
  have arguments := variable_prefix_arguments_answers program caller before after (.function "remove-atom")
    [space] [pattern] [] 0 [Effects.boolean true] (by simpa [applySubst, location] using raw)
  exact call_returns program caller before after "remove-atom" [.var space, pattern] (Effects.boolean true)
    (by simp [StdLib.known]) arguments (by decide)

theorem comparison_returns (names : Names) (program : Program) (caller : Subst) (state : Effects.State)
    (candidate previous : Nat)
    (newValue : Subst.lookup caller names.candidate = some (number candidate))
    (oldValue : Subst.lookup caller names.previous = some (number previous)) :
    PureReturns program caller state (comparison names) state (Effects.boolean (decide (candidate < previous))) := by
  apply native_binary_call_returns program caller state state state state "<" _ _ _ _ _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simpa [applySubst, newValue] using variable_returns program caller state names.candidate)
    (by simpa [applySubst, oldValue] using variable_returns program caller state names.previous)
    _ (by decide)
  change Except.ok (state, [Effects.boolean (decide ((candidate : Int) < (previous : Int)))]) = _
  simp

theorem absent_returns (names : Names) (program : Program) (caller : Subst) (state : Effects.State)
    (answers : List Atom) (found : Subst.lookup caller names.current = some (.expression answers)) :
    PureReturns program caller state (absent names) state (Effects.boolean (decide (answers = []))) := by
  have emptyValue : PureReturns program caller state (.expression []) state (.expression []) :=
    .step (step_transition rfl) (.step (step_transition rfl) (.refl _))
  apply native_binary_call_returns program caller state state state state "==" _ _ _ _ _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simpa [applySubst, found] using variable_returns program caller state names.current) emptyValue _ (by decide)
  rw [StdLib.structural_equality]
  congr 3
  apply congrArg Effects.boolean
  apply Bool.eq_iff_iff.mpr
  simp

theorem render_row (caller : Subst) (head keyName valueName : String) (key value : Nat)
    (keyRead : Subst.lookup caller keyName = some (number key))
    (valueRead : Subst.lookup caller valueName = some (number value)) :
    applySubst caller (row head (.var keyName) (.var valueName)) = row head (number key) (number value) := by
  simp [row, applySubst, applySubst.applySubstList, keyRead, valueRead]

theorem insert_body_returns (names : Names) (head : String) (program : Program) (caller bound : Subst)
    (target : Handle) (key candidate : Nat) (before after : Effects.State)
    (location : Subst.lookup caller names.space = some (Effects.handleValue target))
    (keyRead : Subst.lookup caller names.vertex = some (number key))
    (candidateRead : Subst.lookup caller names.candidate = some (number candidate))
    (matched : matchBinding caller (.var names.discard) (Effects.boolean true) = some bound)
    (resultRead : Subst.lookup bound names.vertex = some (number key))
    (written : Effects.insert before target (row head (number key) (number candidate)) = some after) :
    PureReturns program caller before (insertBody names head) after (number key) := by
  have inserted := FreshConstructorSource.insert_returns program caller before after names.space
    (row head (.var names.vertex) (.var names.candidate)) target location
    (by simpa only [render_row caller head names.vertex names.candidate key candidate keyRead candidateRead] using written)
  exact let_returns program caller bound before after after (.var names.discard) _ (.var names.vertex) _ _ inserted matched
    (by simpa [applySubst, resultRead] using variable_returns program bound after names.vertex)

theorem replace_body_returns (names : Names) (head : String) (program : Program) (caller marked : Subst)
    (target : Handle) (key candidate previous : Nat) (before middle after : Effects.State)
    (location : Subst.lookup caller names.space = some (Effects.handleValue target))
    (keyRead : Subst.lookup caller names.vertex = some (number key))
    (previousRead : Subst.lookup caller names.previous = some (number previous))
    (matched : matchBinding caller (.var names.discard) (Effects.boolean true) = some marked)
    (markedLocation : Subst.lookup marked names.space = some (Effects.handleValue target))
    (markedKey : Subst.lookup marked names.vertex = some (number key))
    (markedCandidate : Subst.lookup marked names.candidate = some (number candidate))
    (markedDiscard : Subst.lookup marked names.discard = some (Effects.boolean true))
    (erased : Effects.erase before target (row head (number key) (number previous)) = some middle)
    (written : Effects.insert middle target (row head (number key) (number candidate)) = some after) :
    PureReturns program caller before (replaceBody names head) after (number key) := by
  have removed := remove_returns program caller before middle names.space
    (row head (.var names.vertex) (.var names.previous)) target _ location
    (render_row caller head names.vertex names.previous key previous keyRead previousRead) (by simp) erased
  have inserted := insert_body_returns names head program marked marked target key candidate middle after
    markedLocation markedKey markedCandidate
    (by simp [matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, markedDiscard]) markedKey written
  exact let_star_returns program caller before after _ (.var names.vertex) _ (number key) rfl
    (let_returns program caller marked before middle after (.var names.discard) _ _ _ _ removed matched inserted)

def collected (names : Names) (target : Handle) (key candidate : Nat) (answers : List Atom) : Subst :=
  (names.current, .expression answers) :: bindings names target key candidate

def held (names : Names) (target : Handle) (key candidate previous : Nat) : Subst :=
  (names.previous, number previous) :: collected names target key candidate [number previous]

theorem write_returns (names : Names) (head : String) (program : Program) (target : Handle)
    (key candidate : Nat) (old : Option Nat) (before after : Effects.State) (answers : List Atom)
    (completed : write before target head key candidate old = some (after, answers)) :
    Returns program (collected names target key candidate (old.toList.map number)) before
      (.expression [.symbol "if", absent names, insertBody names head, existingBody names head]) after answers := by
  have separated := names.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at separated
  rcases separated with ⟨⟨hsv, hsc, hst, hsp, hsd⟩, ⟨hvc, hvt, hvp, hvd⟩,
    ⟨hct, hcp, hcd⟩, ⟨htp, htd⟩, hpd⟩
  have hvs := Ne.symm hsv
  have hcs := Ne.symm hsc
  have hcv := Ne.symm hvc
  have hts := Ne.symm hst
  have hps := Ne.symm hsp
  have hds := Ne.symm hsd
  have htv := Ne.symm hvt
  have hpv := Ne.symm hvp
  have hdv := Ne.symm hvd
  have htc := Ne.symm hct
  have hpc := Ne.symm hcp
  have hdc := Ne.symm hcd
  have hpt := Ne.symm htp
  have hdt := Ne.symm htd
  have hdp := Ne.symm hpd
  have test := absent_returns names program (collected names target key candidate (old.toList.map number)) before
    (old.toList.map number) (by simp [collected, Subst.lookup])
  cases old with
  | none =>
      obtain ⟨result, written, same⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      apply if_answers program _ before before result _ (Effects.boolean true) _ _ _
        (by simpa using test)
      simp only [beq_self_eq_true, ↓reduceIte]
      apply insert_body_returns names head program _ ((names.discard, Effects.boolean true) :: collected names target key candidate [])
        target key candidate before result
      all_goals simp_all [collected, bindings, Subst.lookup, matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
  | some previous =>
      apply if_answers program _ before before after _ (Effects.boolean false) _ _ _
        (by simpa using test)
      change Returns program (collected names target key candidate [number previous]) before (existingBody names head) after answers
      apply let_answers program _ (held names target key candidate previous) before before after
        (.expression [.var names.previous]) (.var names.current) _ (.expression [number previous]) answers
      · simpa [applySubst, collected, Subst.lookup] using
          variable_returns program (collected names target key candidate [number previous]) before names.current
      · simp_all [held, collected, bindings, matchBinding, matchValue, matchValue.matchValues,
          Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Subst.lookup]
      · have compare := comparison_returns names program (held names target key candidate previous) before candidate previous
          (by simp_all [held, collected, bindings, Subst.lookup]) (by simp [held, Subst.lookup])
        by_cases better : candidate < previous
        · rw [write, if_pos better] at completed
          obtain ⟨middle, erased, tail⟩ := Option.bind_eq_some_iff.mp completed
          obtain ⟨result, written, same⟩ := Option.bind_eq_some_iff.mp tail
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
          apply if_answers program _ before before result _ (Effects.boolean true) _ _ _ (by simpa [better] using compare)
          simp only [beq_self_eq_true, ↓reduceIte]
          apply replace_body_returns names head program _ ((names.discard, Effects.boolean true) :: held names target key candidate previous)
            target key candidate previous before middle result
          all_goals simp_all [held, collected, bindings, Subst.lookup, matchBinding, matchValue,
            Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
        · have same : (before, []) = (after, answers) := Option.some.inj (by simpa only [write, if_neg better] using completed)
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
          apply if_answers program _ before before before _ (Effects.boolean false) _ _ _ (by simpa [better] using compare)
          simpa [Effects.boolean] using empty_returns program (held names target key candidate previous) before

theorem returns (names : Names) (head : String) (program : Program) (target : Handle)
    (key candidate : Nat) (before after : Effects.State) (answers : List Atom)
    (completed : run names head target key candidate before = some (after, answers)) :
    Returns program (bindings names target key candidate) before (source names head) after answers := by
  unfold run at completed
  split at completed
  · cases completed
  · obtain ⟨rows, snapshot, rest⟩ := Option.bind_eq_some_iff.mp completed
    split at rest
    · obtain ⟨old, decoded, written⟩ := Option.bind_eq_some_iff.mp rest
      have exactValues := decodeFibre_exact _ old decoded
      have collectedSource := collapse_returns program _ before before _ _
        (query_returns names head program (bindings names target key candidate) target before rows
          (bindings_location names target key candidate) snapshot)
      rw [exactValues] at collectedSource
      apply let_answers program _ (collected names target key candidate (old.toList.map number)) before before after
        (.var names.current) _ _ (.expression (old.toList.map number)) answers collectedSource _
        (write_returns names head program target key candidate old before after answers written)
      have separated := names.distinct
      simp_all [collected, bindings, List.nodup_cons, Subst.lookup, matchBinding, matchValue,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
    · cases rest

def updatedRows (head : String) (key candidate : Nat) (old : Option Nat) (rows : List Atom) : List Atom :=
  match old with
  | none => rows ++ [row head (number key) (number candidate)]
  | some previous => if candidate < previous then
      rows.filter (· != row head (number key) (number previous)) ++ [row head (number key) (number candidate)]
    else rows

/-- The completed source row operation retains its exact list state and the
strict keyed-improvement flag. It does not quotient row order or occurrences. -/
theorem write_observation (before after : Effects.State) (target : Handle) (head : String)
    (ordinary : head ≠ "cons")
    (key candidate : Nat) (old : Option Nat) (answers : List Atom)
    (rows : List Atom) (snapshot : before.read target = some rows)
    (completed : write before target head key candidate old = some (after, answers)) :
    after.read target = some (updatedRows head key candidate old rows) ∧
    answers = (if (Mettapedia.Machines.KeyedImprovement.improve (fun _ : Unit => old) () candidate).2 then [number key] else []) ∧
    (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  cases old with
  | none =>
      obtain ⟨result, written, same⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      obtain ⟨inputRows, inputRead, resultRead⟩ := Effects.insert_reads_back written
      cases Option.some.inj (inputRead.symm.trans snapshot)
      exact ⟨resultRead, rfl,
        fun _ different => Effects.insert_read_other written different, Effects.insert_preserves_cells written⟩
  | some previous =>
      by_cases better : candidate < previous
      · rw [write, if_pos better] at completed
        obtain ⟨middle, erased, tail⟩ := Option.bind_eq_some_iff.mp completed
        obtain ⟨result, written, same⟩ := Option.bind_eq_some_iff.mp tail
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        have literal : Literal (row head (number key) (number previous)) := by
          apply Literal.constructor head _ ordinary
          intro atom member
          simp at member
          rcases member with rfl | rfl
          · exact .grounded _
          · exact .grounded _
        obtain ⟨inputRows, inputRead, middleRead⟩ := Effects.erase_literal_reads_back (by simp) literal erased
        cases Option.some.inj (inputRead.symm.trans snapshot)
        obtain ⟨middleRows, readMiddleRows, resultRead⟩ := Effects.insert_reads_back written
        have equal := Option.some.inj (readMiddleRows.symm.trans middleRead)
        subst middleRows
        refine ⟨by simpa [updatedRows, better, row] using resultRead,
          by simp [Mettapedia.Machines.KeyedImprovement.improve, better], ?_, ?_⟩
        · intro other different
          exact (Effects.insert_read_other written different).trans (Effects.erase_read_other erased different)
        · exact (Effects.insert_preserves_cells written).trans (Effects.erase_preserves_cells erased)
      · have same : (before, []) = (after, answers) := Option.some.inj (by simpa only [write, if_neg better] using completed)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        exact ⟨by simpa [updatedRows, better] using snapshot,
          by simp [Mettapedia.Machines.KeyedImprovement.improve, better], fun _ _ => rfl, rfl⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementSource
