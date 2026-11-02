import Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionSource

/-!
# Captured-query materialization with source-visible success counts

A captured source query produces row-local bindings. Each body quotes its
template, binds a fresh local name, and performs the proved guarded insertion.
The destination may be the same space as the captured query. The selected
choices stay fixed while later insertions see the current destination.

The final support is a union, but the returned count is the number of captured
choices, including those whose payload was already present. This supplies a
baseline source phase for collection adapters; it does not identify the phase
with an extended set-space constructor or a whole temporal-logic driver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom atomFreeVars)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def bodySource (targetName temporary : String) (template : Atom) : Atom :=
  .expression [.symbol "let", .var temporary, .expression [.symbol "quote", template],
    GuardedInsertionSource.source targetName temporary]

def emit (target : Handle) (template : Atom) : Body := fun bindings before =>
  (GuardedInsertionSource.update before target (applySubst bindings template)).map
    (fun after => (after, [Effects.boolean true]))

/-- Once the template is instantiated, the emitter needs the ordered payload
occurrences, not the rest of each query binding frame. -/
def emitRows (target : Handle) : List Atom → Effects.State × List Atom → Option (Effects.State × List Atom)
  | [], receipt => some receipt
  | payload :: rest, receipt =>
      (GuardedInsertionSource.update receipt.1 target payload).bind fun next =>
        emitRows target rest (next, receipt.2 ++ [Effects.boolean true])

theorem traverse_emit_exact (target : Handle) (template : Atom) (captured : List Subst)
    (receipt : Effects.State × List Atom) :
    traverse (emit target template) captured receipt =
      emitRows target (captured.map (fun bindings => applySubst bindings template)) receipt := by
  induction captured generalizing receipt with
  | nil => rfl
  | cons bindings rest ih =>
      simp only [EffectfulQuerySource.traverse, emit, List.map_cons, emitRows, Option.bind_map, ih, Function.comp_def]

/-- Store-only installation omits the private success-answer list. Its count
is recovered from the retained occurrence list, not the final store size. -/
def installRows (target : Handle) : List Atom → Effects.State → Option Effects.State
  | [], before => some before
  | payload :: rest, before =>
      (GuardedInsertionSource.update before target payload).bind (installRows target rest)

theorem emitRows_install_exact (target : Handle) (payloads : List Atom) (before : Effects.State) (collected : List Atom) :
    emitRows target payloads (before, collected) =
      (installRows target payloads before).map (fun after =>
        (after, collected ++ List.replicate payloads.length (Effects.boolean true))) := by
  induction payloads generalizing before collected with
  | nil => simp [emitRows, installRows]
  | cons payload rest ih =>
      simp only [emitRows, installRows, Option.map_bind]
      apply congrArg ((GuardedInsertionSource.update before target payload).bind)
      funext middle
      rw [ih]
      simp [List.replicate_succ, List.append_assoc]

theorem traverse_install_exact (target : Handle) (template : Atom) (captured : List Subst)
    (before : Effects.State) (collected : List Atom) :
    traverse (emit target template) captured (before, collected) =
      (installRows target (captured.map (fun bindings => applySubst bindings template)) before).map
        (fun after => (after, collected ++ List.replicate captured.length (Effects.boolean true))) := by
  rw [traverse_emit_exact, emitRows_install_exact, List.length_map]

theorem emit_returns (program : Program) (bindings : Subst) (before after : Effects.State)
    (targetName temporary : String) (target : Handle) (template : Atom) (answers : List Atom)
    (different : temporary ≠ targetName)
    (location : Subst.lookup bindings targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup bindings temporary = none)
    (completed : emit target template bindings before = some (after, answers)) :
    Returns program bindings before (bodySource targetName temporary template) after answers := by
  obtain ⟨next, updated, same⟩ := Option.map_eq_some_iff.mp completed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  let locals := (temporary, applySubst bindings template) :: bindings
  have targetBound : Subst.lookup locals targetName = some (Effects.handleValue target) := by
    simpa [locals, Subst.lookup, different] using location
  have payloadBound : Subst.lookup locals temporary = some (applySubst bindings template) := by simp [locals, Subst.lookup]
  have bound : matchBinding bindings (.var temporary) (applySubst bindings template) = some locals := by
    simp [matchBinding, matchValue, matchAtom, fresh, locals]
  obtain ⟨rows, snapshot, _⟩ := GuardedInsertionSource.update_reads_back updated
  exact let_returns program bindings locals before before next (.var temporary) (.expression [.symbol "quote", template])
    (GuardedInsertionSource.source targetName temporary) (applySubst bindings template) (Effects.boolean true)
    (quote_returns program bindings before template) bound
    (GuardedInsertionSource.source_returns program locals before next targetName temporary target _ rows
      targetBound payloadBound snapshot updated)

theorem traverse_exists (target : Handle) (template : Atom) (captured : List Subst)
    (before : Effects.State) (rows : List Atom) (snapshot : before.read target = some rows) (collected : List Atom) :
    ∃ after answers, traverse (emit target template) captured (before, collected) = some (after, answers) := by
  induction captured generalizing before rows collected with
  | nil => exact ⟨before, collected, rfl⟩
  | cons bindings rest ih =>
      obtain ⟨middle, updated⟩ := GuardedInsertionSource.update_exists snapshot (applySubst bindings template)
      obtain ⟨old, _, current⟩ := GuardedInsertionSource.update_reads_back updated
      obtain ⟨after, answers, completed⟩ := ih middle _ current (collected ++ [Effects.boolean true])
      exact ⟨after, answers, by simp [EffectfulQuerySource.traverse, emit, updated, completed]⟩

theorem traverse_answers (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State) (collected answers : List Atom)
    (completed : traverse (emit target template) captured (before, collected) = some (after, answers)) :
    answers = collected ++ List.replicate captured.length (Effects.boolean true) := by
  induction captured generalizing before collected with
  | nil =>
      have same : (before, collected) = (after, answers) := Option.some.inj completed
      simpa using (Prod.mk.inj same).2.symm
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨middle, _, same⟩ := Option.map_eq_some_iff.mp first
      cases same
      simpa [List.replicate_succ, List.append_assoc] using ih middle (collected ++ [Effects.boolean true]) later

theorem traverse_receipt (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State) (rows collected answers : List Atom)
    (snapshot : before.read target = some rows) (distinct : rows.Nodup)
    (completed : traverse (emit target template) captured (before, collected) = some (after, answers)) :
    ∃ result, after.read target = some result ∧ result.Nodup ∧
      result.toFinset = rows.toFinset ∪ (captured.map (fun bindings => applySubst bindings template)).toFinset ∧
      answers = collected ++ List.replicate captured.length (Effects.boolean true) := by
  induction captured generalizing before rows collected with
  | nil =>
      have same : (before, collected) = (after, answers) := Option.some.inj completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ⟨rows, snapshot, distinct, by simp, by simp⟩
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨middle, updated, same⟩ := Option.map_eq_some_iff.mp first
      cases same
      obtain ⟨middleRows, middleRead, middleDistinct, middleSupport⟩ :=
        GuardedInsertionSource.update_nodup snapshot distinct updated
      obtain ⟨result, afterRead, afterDistinct, support, returned⟩ :=
        ih middle middleRows (collected ++ [Effects.boolean true]) middleRead middleDistinct later
      refine ⟨result, afterRead, afterDistinct, ?_, ?_⟩
      · simpa [middleSupport] using support
      · simpa [List.replicate_succ, List.append_assoc] using returned

theorem query_returns (program : Program) (caller : Subst) (before after : Effects.State)
    (inputName targetName temporary : String) (input target : Handle)
    (pattern template : Atom) (rows answers : List Atom)
    (inputBound : Subst.lookup caller inputName = some (Effects.handleValue input))
    (targetBound : Subst.lookup caller targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup caller temporary = none) (outside : temporary ∉ atomFreeVars pattern)
    (different : temporary ≠ targetName) (snapshot : before.read input = some rows)
    (completed : traverse (emit target template) (choices caller pattern rows) (before, []) = some (after, answers)) :
    Returns program caller before
      (.expression [.symbol "match", .var inputName, pattern, bodySource targetName temporary template]) after answers := by
  apply EffectfulQuerySource.match_returns program caller before after (.var inputName) (Effects.handleValue input)
    pattern (bodySource targetName temporary template) rows (emit target template) answers _ _ _ completed
  · simpa only [applySubst, inputBound, Option.getD_some] using variable_returns program caller before inputName
  · simp [snapshot]
  · intro bindings member current next values result
    apply emit_returns program bindings current next targetName temporary target template values different _ _ result
    · exact choices_extend caller pattern rows bindings member targetName _ targetBound
    · exact (choices_lookup_outside caller pattern rows bindings member temporary outside).trans fresh

theorem counted_query_returns (program : Program) (caller : Subst) (before after : Effects.State)
    (inputName targetName temporary : String) (input target : Handle)
    (pattern template : Atom) (rows answers : List Atom)
    (inputBound : Subst.lookup caller inputName = some (Effects.handleValue input))
    (targetBound : Subst.lookup caller targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup caller temporary = none) (outside : temporary ∉ atomFreeVars pattern)
    (different : temporary ≠ targetName) (snapshot : before.read input = some rows)
    (completed : traverse (emit target template) (choices caller pattern rows) (before, []) = some (after, answers)) :
    PureReturns program caller before (counted (.var inputName) pattern (bodySource targetName temporary template))
      after (.grounded (.int (choices caller pattern rows).length)) := by
  have returned := traverse_answers target template (choices caller pattern rows) before after [] answers completed
  have queried := query_returns program caller before after inputName targetName temporary input target pattern template
    rows answers inputBound targetBound fresh outside different snapshot completed
  have collected := collapse_returns program caller before after _ _ queried
  have result := native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)
  simpa only [counted, returned, List.nil_append, List.length_replicate] using result

theorem source_meaning (program : Program) (caller : Subst) (before after : Effects.State)
    (inputName targetName temporary : String) (input target : Handle)
    (pattern template : Atom) (rows answers : List Atom)
    (inputBound : Subst.lookup caller inputName = some (Effects.handleValue input))
    (targetBound : Subst.lookup caller targetName = some (Effects.handleValue target))
    (fresh : Subst.lookup caller temporary = none) (outside : temporary ∉ atomFreeVars pattern)
    (different : temporary ≠ targetName) (snapshot : before.read input = some rows)
    (completed : traverse (emit target template) (choices caller pattern rows) (before, []) = some (after, answers)) :
    PureCallPortfolio.sourceMeaning program caller
      (counted (.var inputName) pattern (bodySource targetName temporary template)) before =
      {⟨after, [.grounded (.int answers.length)], [], []⟩} := by
  have returned := counted_query_returns program caller before after inputName targetName temporary input target
    pattern template rows answers inputBound targetBound fresh outside different snapshot completed
  have lengthExact : answers.length = (choices caller pattern rows).length := by
    simp only [traverse_answers target template (choices caller pattern rows) before after [] answers completed,
      List.nil_append, List.length_replicate]
  rw [← lengthExact] at returned
  ext observed
  change DeclarativeSpec.Runs program
    {state := before, control := .evaluate caller (counted (.var inputName) pattern (bodySource targetName temporary template))}
    (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program caller before after _ _ returned]
  cases observed
  simp [PureCallPortfolio.Completed.mk.injEq]

open Mettapedia.GSLT.Dynamics ObservationQualified in
/-- A private completed-result worker. Runtime publication of an intermediate
prefix is not licensed by its refusal branch. -/
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
        let captured := choices caller pattern rows
        let payloads := captured.map (fun bindings => applySubst bindings template)
        if payloads.all GuardedInsertionSource.dataRow then
          match installRows target payloads before with
          | none => .declined before
          | some after => .committed ⟨after, [.grounded (.int payloads.length)], [], []⟩
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
        next after completed =>
          have same := PartialRegionPlan.Attempt.committed.inj accepted
          subst observed
          have original : traverse (emit target template) (choices caller pattern rows) (before, []) =
              some (after, List.replicate (choices caller pattern rows).length (Effects.boolean true)) := by
            rw [traverse_install_exact, completed]
            rfl
          simpa only [List.length_map, List.length_replicate, Boundary.reference, PureCallPortfolio.boundary, id_eq] using
            (source_meaning program caller before after inputName targetName temporary input target pattern template
              rows _ inputBound targetBound fresh outside different snapshot original).symm
      next => cases accepted

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.QuerySetMaterialization
