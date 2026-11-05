import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshInsertionSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterialization

/-!
# Fresh-result counts over captured materialization phases

Fresh-only and always-successful insertion use the same store installation
worker but different source observations. Fresh results are measured by the
destination's row growth, not the number of candidate occurrences. The
completed phase conserves this quantity even when candidates repeat.

Missing access remains refusal, not zero progress. These finite-phase laws do
not by themselves prove that a frontier enumerates every required inference
or that a complete temporal-logic driver has reached its fixed point.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom atomFreeVars)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def bodySource (targetName temporary : String) (template : Atom) : Atom :=
  .expression [.symbol "let", .var temporary, .expression [.symbol "quote", template],
    FreshInsertionSource.source targetName temporary]

def emit (target : Handle) (template : Atom) : Body := fun bindings before =>
  (FreshInsertionSource.update before target (applySubst bindings template)).map
    (fun result => (result.1, FreshInsertionSource.answers result.2))

theorem emit_returns (program : Program) (bindings : Subst) (before after : Effects.State)
    (targetName temporary : String) (target : Handle) (template : Atom) (answers : List Atom)
    (different : temporary ≠ targetName)
    (location : Subst.lookup bindings targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup bindings temporary = none)
    (completed : emit target template bindings before = some (after, answers)) :
    Returns program bindings before (bodySource targetName temporary template) after answers := by
  obtain ⟨result, updated, same⟩ := Option.map_eq_some_iff.mp completed
  rcases result with ⟨next, changed⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  let locals := (temporary, applySubst bindings template) :: bindings
  have targetBound : Subst.lookup locals targetName = some (Effects.handleValue target) := by
    simpa [locals, Subst.lookup, different] using location
  have payloadBound : Subst.lookup locals temporary = some (applySubst bindings template) := by simp [locals, Subst.lookup]
  have bound : matchBinding bindings (.var temporary) (applySubst bindings template) = some locals := by
    simp [matchBinding, matchValue, matchAtom, fresh, locals]
  exact let_answers program bindings locals before before next (.var temporary) (.expression [.symbol "quote", template])
    (FreshInsertionSource.source targetName temporary) (applySubst bindings template) (FreshInsertionSource.answers changed)
    (quote_returns program bindings before template) bound
    (FreshInsertionSource.source_returns program locals before next targetName temporary target _ changed
      targetBound payloadBound updated)

theorem emit_forgets (target : Handle) (template : Atom) (bindings : Subst) (before : Effects.State) :
    (emit target template bindings before).map Prod.fst =
      GuardedInsertionSource.update before target (applySubst bindings template) := by
  simpa only [emit, Option.map_map, Function.comp_def] using
    FreshInsertionSource.forget_progress before target (applySubst bindings template)

theorem forget_traversal (target : Handle) (template : Atom) (captured : List Subst)
    (before : Effects.State) (collected : List Atom) :
    (traverse (emit target template) captured (before, collected)).map Prod.fst =
      QuerySetMaterialization.installRows target (captured.map (fun bindings => applySubst bindings template)) before := by
  induction captured generalizing before collected with
  | nil => rfl
  | cons bindings rest ih =>
      simp only [EffectfulQuerySource.traverse, List.map_cons, QuerySetMaterialization.installRows, Option.map_bind,
        Function.comp_def, ih]
      rw [← emit_forgets target template bindings before]
      rw [Option.bind_map]
      rfl

theorem traverse_growth (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State) (rows collected answers : List Atom)
    (snapshot : before.read target = some rows)
    (completed : traverse (emit target template) captured (before, collected) = some (after, answers)) :
    ∃ result, after.read target = some result ∧ result.length + collected.length = rows.length + answers.length := by
  induction captured generalizing before rows collected with
  | nil =>
      have same : (before, collected) = (after, answers) := Option.some.inj completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ⟨rows, snapshot, rfl⟩
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨receipt, updated, same⟩ := Option.map_eq_some_iff.mp first
      rcases receipt with ⟨middle, changed⟩
      cases same
      obtain ⟨old, middleRows, oldRead, middleRead, growth⟩ := FreshInsertionSource.update_growth updated
      have equalRows : old = rows := Option.some.inj (oldRead.symm.trans snapshot)
      subst old
      obtain ⟨result, afterRead, balance⟩ :=
        ih middle middleRows (collected ++ FreshInsertionSource.answers changed) middleRead later
      refine ⟨result, afterRead, ?_⟩
      simp only [List.length_append] at balance
      omega

/-- No success list is needed for the count observer. The empty phase does
not read the destination; every nonempty phase requires a complete read. -/
def countedInstall (target : Handle) (payloads : List Atom) (before : Effects.State) : Option (Effects.State × Nat) :=
  if payloads = [] then some (before, 0) else do
    let old ← before.read target
    let after ← QuerySetMaterialization.installRows target payloads before
    let result ← after.read target
    return (after, result.length - old.length)

theorem countedInstall_forgets (target : Handle) (payloads : List Atom) (before : Effects.State) :
    (countedInstall target payloads before).map Prod.fst = QuerySetMaterialization.installRows target payloads before := by
  cases payloads with
  | nil => rfl
  | cons payload rest =>
      cases snapshot : before.read target with
      | none =>
          simp [countedInstall, snapshot, QuerySetMaterialization.installRows,
            GuardedInsertionSource.missing_space_is_not_presence before target payload snapshot]
      | some rows =>
          obtain ⟨after, result, installed, afterRead⟩ :=
            QuerySetMaterialization.installRows_exists_read target (payload :: rest) before rows snapshot
          simp [countedInstall, snapshot, installed, afterRead]

theorem countedInstall_exists (target : Handle) (payloads : List Atom) (before : Effects.State)
    (rows : List Atom) (snapshot : before.read target = some rows) :
    ∃ after count, countedInstall target payloads before = some (after, count) := by
  obtain ⟨after, _, installed, _⟩ := QuerySetMaterialization.installRows_exists_read target payloads before rows snapshot
  have projected : (countedInstall target payloads before).map Prod.fst = some after :=
    (countedInstall_forgets target payloads before).trans installed
  obtain ⟨receipt, completed, _⟩ := Option.map_eq_some_iff.mp projected
  exact ⟨receipt.1, receipt.2, completed⟩

theorem traverse_count_le (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State) (collected answers : List Atom)
    (completed : traverse (emit target template) captured (before, collected) = some (after, answers)) :
    answers.length ≤ collected.length + captured.length := by
  induction captured generalizing before collected with
  | nil =>
      have same : (before, collected) = (after, answers) := Option.some.inj completed
      simp only [← (Prod.mk.inj same).2, List.length_nil, Nat.add_zero, le_refl]
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨receipt, _, same⟩ := Option.map_eq_some_iff.mp first
      rcases receipt with ⟨middle, changed⟩
      cases same
      have bound := ih middle (collected ++ FreshInsertionSource.answers changed) later
      have atMostOne : (FreshInsertionSource.answers changed).length ≤ 1 := by cases changed <;> decide
      simp only [List.length_append, List.length_cons] at bound ⊢
      omega

theorem counted_install_sound (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State) (count : Nat)
    (completed : countedInstall target (captured.map (fun bindings => applySubst bindings template)) before = some (after, count)) :
    ∃ answers, traverse (emit target template) captured (before, []) = some (after, answers) ∧ answers.length = count := by
  cases captured with
  | nil =>
      have same : (before, 0) = (after, count) := by simpa [countedInstall] using completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ⟨[], rfl, rfl⟩
  | cons bindings rest =>
      simp only [countedInstall, List.map_cons, List.cons_ne_nil, ↓reduceIte] at completed
      obtain ⟨old, oldRead, remaining⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨middle, installed, remaining⟩ := Option.bind_eq_some_iff.mp remaining
      obtain ⟨result, resultRead, same⟩ := Option.bind_eq_some_iff.mp remaining
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      have projected : (traverse (emit target template) (bindings :: rest) (before, [])).map Prod.fst = some middle := by
        rw [forget_traversal]
        exact installed
      obtain ⟨receipt, traversed, finalState⟩ := Option.map_eq_some_iff.mp projected
      rcases receipt with ⟨finish, answers⟩
      change finish = middle at finalState
      subst finish
      obtain ⟨finalRows, finalRead, growth⟩ := traverse_growth target template (bindings :: rest)
        before middle old [] answers oldRead traversed
      have equalRows : finalRows = result := Option.some.inj (finalRead.symm.trans resultRead)
      subst finalRows
      refine ⟨answers, traversed, ?_⟩
      simp only [List.length_nil, Nat.add_zero] at growth
      omega

theorem counted_install_bound (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State) (count : Nat)
    (completed : countedInstall target (captured.map (fun bindings => applySubst bindings template)) before = some (after, count)) :
    count ≤ captured.length := by
  obtain ⟨answers, traversed, size⟩ := counted_install_sound target template captured before after count completed
  simpa only [size, List.length_nil, Nat.zero_add] using traverse_count_le target template captured before after [] answers traversed

theorem empty_traversal_preserves_state (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State)
    (completed : traverse (emit target template) captured (before, []) = some (after, [])) : before = after := by
  induction captured generalizing before with
  | nil => exact (Prod.mk.inj (Option.some.inj completed)).1
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨receipt, updated, same⟩ := Option.map_eq_some_iff.mp first
      rcases receipt with ⟨middle, changed⟩
      cases same
      have noAnswers := empty_result_has_empty_prefix (emit target template) rest middle after
        ([] ++ FreshInsertionSource.answers changed) later
      cases changed with
      | true => simp [FreshInsertionSource.answers] at noAnswers
      | false =>
          have unchanged := FreshInsertionSource.zero_progress_preserves_state updated
          subst middle
          exact ih before later

theorem zero_count_preserves_state (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State)
    (completed : countedInstall target (captured.map (fun bindings => applySubst bindings template)) before = some (after, 0)) :
    before = after := by
  obtain ⟨answers, traversed, size⟩ := counted_install_sound target template captured before after 0 completed
  have empty : answers = [] := List.length_eq_zero_iff.mp size
  subst answers
  exact empty_traversal_preserves_state target template captured before after traversed

theorem query_returns (program : Program) (caller : Subst) (before after : Effects.State)
    (inputName targetName temporary : String) (input target : Handle) (pattern template : Atom) (rows answers : List Atom)
    (inputBound : Subst.lookup caller inputName = some (Effects.handleValue input))
    (targetBound : Subst.lookup caller targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup caller temporary = none) (outside : temporary ∉ atomFreeVars pattern)
    (different : temporary ≠ targetName) (snapshot : before.read input = some rows)
    (completed : traverse (emit target template) (choices caller pattern rows) (before, []) = some (after, answers)) :
    Returns program caller before (.expression [.symbol "match", .var inputName, pattern, bodySource targetName temporary template])
      after answers := by
  apply EffectfulQuerySource.match_returns program caller before after (.var inputName) (Effects.handleValue input)
    pattern (bodySource targetName temporary template) rows (emit target template) answers _ _ _ completed
  · simpa only [applySubst, inputBound, Option.getD_some] using variable_returns program caller before inputName
  · simp [snapshot]
  · intro bindings member current next values result
    apply emit_returns program bindings current next targetName temporary target template values different _ _ result
    · exact choices_extend caller pattern rows bindings member targetName _ targetBound
    · exact (choices_lookup_outside caller pattern rows bindings member temporary outside).trans fresh

theorem counted_query_returns (program : Program) (caller : Subst) (before after : Effects.State)
    (inputName targetName temporary : String) (input target : Handle) (pattern template : Atom) (rows : List Atom) (count : Nat)
    (inputBound : Subst.lookup caller inputName = some (Effects.handleValue input))
    (targetBound : Subst.lookup caller targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup caller temporary = none) (outside : temporary ∉ atomFreeVars pattern)
    (different : temporary ≠ targetName) (snapshot : before.read input = some rows)
    (completed : countedInstall target ((choices caller pattern rows).map (fun bindings => applySubst bindings template)) before =
      some (after, count)) :
    PureReturns program caller before (counted (.var inputName) pattern (bodySource targetName temporary template))
      after (.grounded (.int count)) := by
  obtain ⟨answers, traversed, lengthExact⟩ := counted_install_sound target template (choices caller pattern rows) before after count completed
  have queried := query_returns program caller before after inputName targetName temporary input target pattern template rows answers
    inputBound targetBound fresh outside different snapshot traversed
  have collected := collapse_returns program caller before after _ _ queried
  have result := native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)
  simpa only [counted, lengthExact] using result

theorem source_meaning (program : Program) (caller : Subst) (before after : Effects.State)
    (inputName targetName temporary : String) (input target : Handle) (pattern template : Atom) (rows : List Atom) (count : Nat)
    (inputBound : Subst.lookup caller inputName = some (Effects.handleValue input))
    (targetBound : Subst.lookup caller targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup caller temporary = none) (outside : temporary ∉ atomFreeVars pattern)
    (different : temporary ≠ targetName) (snapshot : before.read input = some rows)
    (completed : countedInstall target ((choices caller pattern rows).map (fun bindings => applySubst bindings template)) before =
      some (after, count)) :
    PureCallPortfolio.sourceMeaning program caller
      (counted (.var inputName) pattern (bodySource targetName temporary template)) before =
      {⟨after, [.grounded (.int count)], [], []⟩} := by
  have returned := counted_query_returns program caller before after inputName targetName temporary input target
    pattern template rows count inputBound targetBound fresh outside different snapshot completed
  ext observed
  change DeclarativeSpec.Runs program
    {state := before, control := .evaluate caller (counted (.var inputName) pattern (bodySource targetName temporary template))}
    (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program caller before after _ _ returned]
  cases observed
  simp [PureCallPortfolio.Completed.mk.injEq]

open Mettapedia.GSLT.Dynamics ObservationQualified in
def region (program : Program) (caller : Subst) (inputName targetName temporary : String)
    (input target : Handle) (pattern template : Atom)
    (inputBound : Subst.lookup caller inputName = some (Effects.handleValue input))
    (targetBound : Subst.lookup caller targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup caller temporary = none) (outside : temporary ∉ atomFreeVars pattern)
    (different : temporary ≠ targetName) :
    CertifiedRegion (PureCallPortfolio.boundary program caller
      (counted (.var inputName) pattern (bodySource targetName temporary template))) Nat where
  regime := 0
  Artifact := PureCallPortfolio.Completed
  attempt before := match before.read input with
    | none => .declined before
    | some rows =>
        let payloads := (choices caller pattern rows).map (fun bindings => applySubst bindings template)
        if ClosedQueryAdmission.phaseReady caller pattern rows before target payloads && payloads.all GuardedInsertionSource.dataRow then
          match countedInstall target payloads before with
          | none => .declined before
          | some result => .committed ⟨result.1, [.grounded (.int result.2)], [], []⟩
        else .declined before
  decode observed := {observed}
  restores before restored declined := by
    dsimp only at declined
    split at declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
    · split at declined
      · split at declined
        · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
        · cases declined
      · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact before observed accepted := by
    dsimp only at accepted
    split at accepted
    · cases accepted
    next rows snapshot =>
      split at accepted
      next =>
        split at accepted
        · cases accepted
        next result completed =>
          have same := PartialRegionPlan.Attempt.committed.inj accepted
          subst observed
          exact (source_meaning program caller before result.1 inputName targetName temporary input target pattern template
            rows result.2 inputBound targetBound fresh outside different snapshot completed).symm
      next => cases accepted

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterialization
