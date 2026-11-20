import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.EffectfulQuerySource

/-!
# Captured query erasure in the pinned bag profile

The match captures its occurrences before any removal. Each captured body
runs even when an earlier removal already deleted its payload. The returned
producer count therefore differs from both distinct payloads and successful
removal flags. Both a changing and an unchanged removal return one Boolean;
only the former returns true.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagErasure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def removal (spaceName : String) (fields : List Atom) : Atom :=
  .expression [.symbol "remove-atom", .var spaceName, .expression fields]

def erase (target : Handle) (fields : List Atom) : Body := fun bindings before =>
  let pattern := applySubst bindings (.expression fields)
  if Effects.removalNeedsValue pattern then none else
    (Effects.erase before target pattern).map
      (fun after => (after, [Effects.boolean (Effects.erasureChanged before after target)]))

private theorem erase_executed {target : Handle} {fields : List Atom} {bindings : Subst}
    {before after : Effects.State} {answers : List Atom}
    (completed : erase target fields bindings before = some (after, answers)) :
    Effects.removalNeedsValue (applySubst bindings (.expression fields)) = false ∧
      Effects.erase before target (applySubst bindings (.expression fields)) = some after ∧
      answers = [Effects.boolean (Effects.erasureChanged before after target)] := by
  cases specified : Effects.removalNeedsValue (applySubst bindings (.expression fields)) with
  | true => simp [erase, specified] at completed
  | false =>
      simp only [erase, specified, Bool.false_eq_true, ↓reduceIte] at completed
      obtain ⟨middle, written, same⟩ := Option.map_eq_some_iff.mp completed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ⟨rfl, written, rfl⟩

def eraseRows (target : Handle) : List Atom → Effects.State → Option Effects.State
  | [], before => some before
  | pattern :: rest, before => (Effects.erase before target pattern).bind (eraseRows target rest)

def retained (patterns rows : List Atom) : List Atom :=
  rows.filter fun row => !(patterns.any fun pattern => Effects.removalMatches pattern row)

theorem retained_cons (pattern : Atom) (patterns rows : List Atom) :
    retained (pattern :: patterns) rows =
      retained patterns (rows.filter fun row => !Effects.removalMatches pattern row) := by
  simp only [retained, List.any_cons, List.filter_filter]
  congr 1
  funext row
  cases Effects.removalMatches pattern row <;>
    cases patterns.any (fun item => Effects.removalMatches item row) <;> rfl

theorem erase_returns (program : Program) (spaceName : String) (target : Handle) (fields : List Atom)
    (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue target))
    (completed : erase target fields bindings before = some (after, answers)) :
    Returns program bindings before (removal spaceName fields) after answers := by
  obtain ⟨specified, erased, rfl⟩ := erase_executed completed
  exact KeyedImprovementSource.remove_returns program bindings before after spaceName (.expression fields) target
    location specified erased

/-- A licensed removal body can omit materializing the Boolean when only
the final store is observed. It still runs once per captured occurrence. -/
theorem traverse_erase_exact (target : Handle) (fields : List Atom) (captured : List Subst)
    (before : Effects.State) (collected : List Atom)
    (specified : ∀ bindings ∈ captured,
      Effects.removalNeedsValue (applySubst bindings (.expression fields)) = false) :
    (traverse (erase target fields) captured (before, collected)).map Prod.fst =
      eraseRows target (captured.map (fun bindings => applySubst bindings (.expression fields))) before := by
  induction captured generalizing before collected with
  | nil => rfl
  | cons bindings rest ih =>
      simp only [EffectfulQuerySource.traverse, erase, specified bindings List.mem_cons_self,
        Bool.false_eq_true, ↓reduceIte, List.map_cons, eraseRows, Option.bind_map, Option.map_bind, Function.comp_def]
      apply congrArg ((Effects.erase before target (applySubst bindings (.expression fields))).bind)
      funext middle
      exact ih middle _ (fun localBindings member => specified localBindings (List.mem_cons_of_mem _ member))

theorem traverse_erase_receipt (target : Handle) (fields : List Atom) (captured : List Subst)
    (before after : Effects.State) (collected answers : List Atom)
    (completed : traverse (erase target fields) captured (before, collected) = some (after, answers)) :
    eraseRows target (captured.map (fun bindings => applySubst bindings (.expression fields))) before = some after ∧
      answers.length = collected.length + captured.length := by
  induction captured generalizing before collected with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
      exact ⟨rfl, by simp⟩
  | cons bindings rest ih =>
      obtain ⟨⟨middle, published⟩, erased, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨_, written, rfl⟩ := erase_executed erased
      obtain ⟨final, count⟩ := ih middle _ later
      simp only [List.map_cons, eraseRows, written, Option.bind_some, final, true_and,
        List.length_append, List.length_cons, List.length_nil] at count ⊢
      omega

theorem eraseRows_exists (target : Handle) (patterns : List Atom) (before : Effects.State) (rows : List Atom)
    (snapshot : before.read target = some rows) : ∃ after, eraseRows target patterns before = some after := by
  induction patterns generalizing before rows with
  | nil => exact ⟨before, rfl⟩
  | cons pattern rest ih =>
      obtain ⟨middle, erased⟩ := Effects.erase_exists_of_read_some snapshot pattern
      obtain ⟨_, _, middleRead⟩ := Effects.erase_reads_back erased
      obtain ⟨after, later⟩ := ih middle _ middleRead
      exact ⟨after, by simp [eraseRows, erased, later]⟩

theorem eraseRows_receipt (target : Handle) (patterns : List Atom) (before after : Effects.State) (rows : List Atom)
    (snapshot : before.read target = some rows) (completed : eraseRows target patterns before = some after) :
    after.read target = some (retained patterns rows) ∧
      (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  induction patterns generalizing before rows with
  | nil =>
      cases Option.some.inj completed
      exact ⟨by simpa [retained] using snapshot, fun _ _ => rfl, rfl⟩
  | cons pattern rest ih =>
      obtain ⟨middle, erased, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨old, oldRead, middleRead⟩ := Effects.erase_reads_back erased
      have same : old = rows := Option.some.inj (oldRead.symm.trans snapshot)
      subst old
      obtain ⟨readAfter, others, cells⟩ := ih middle _ middleRead later
      exact ⟨by simpa only [retained_cons] using readAfter,
        fun other apart => (others other apart).trans (Effects.erase_read_other erased apart),
        cells.trans (Effects.erase_preserves_cells erased)⟩

def source (spaceName : String) (pattern : Atom) (fields : List Atom) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse",
    .expression [.symbol "match", .var spaceName, pattern, removal spaceName fields]]]

def run (target : Handle) (pattern : Atom) (fields : List Atom) : Body := fun caller before => do
  let rows ← before.read target
  traverse (erase target fields) (choices caller pattern rows) (before, [])

theorem source_returns (program : Program) (spaceName : String) (target : Handle)
    (pattern : Atom) (fields : List Atom)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (location : Subst.lookup caller spaceName = some (Effects.handleValue target))
    (completed : run target pattern fields caller before = some (after, answers)) :
    PureReturns program caller before (source spaceName pattern fields) after (.grounded (.int answers.length)) := by
  obtain ⟨rows, snapshot, traversed⟩ := Option.bind_eq_some_iff.mp completed
  have queried : Returns program caller before
      (.expression [.symbol "match", .var spaceName, pattern, removal spaceName fields]) after answers := by
    apply EffectfulQuerySource.match_returns program caller before after (.var spaceName)
      (Effects.handleValue target) pattern (removal spaceName fields) rows (erase target fields) answers
    · simpa [applySubst, location] using variable_returns program caller before spaceName
    · simp [snapshot]
    · intro bindings member current next values executed
      exact erase_returns program spaceName target fields bindings current next values
        (choices_extend caller pattern rows bindings member spaceName _ location) executed
    · exact traversed
  have collected := collapse_returns program caller before after _ _ queried
  exact native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

theorem run_receipt (target : Handle) (pattern : Atom) (fields : List Atom) (caller : Subst)
    (before after : Effects.State) (rows answers : List Atom) (snapshot : before.read target = some rows)
    (completed : run target pattern fields caller before = some (after, answers)) :
    after.read target = some (retained
      ((choices caller pattern rows).map (fun bindings => applySubst bindings (.expression fields))) rows) ∧
      answers.length = (choices caller pattern rows).length ∧
      (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  simp only [run, snapshot] at completed
  obtain ⟨erased, count⟩ := traverse_erase_receipt target fields _ before after [] answers completed
  obtain ⟨reading, others, cells⟩ := eraseRows_receipt target _ before after rows snapshot erased
  exact ⟨reading, by simpa using count, others, cells⟩

theorem unavailable_space_refuses (target : Handle) (pattern : Atom) (fields : List Atom)
    (caller : Subst) (state : Effects.State) (missing : state.read target = none) :
    run target pattern fields caller state = none := by simp [run, missing]

/-- Declaration edits and dynamically headed payloads require another source
profile. A fact deletion also needs a closed destination candidate domain. -/
def factPayload : Atom → Bool
  | .expression (.symbol head :: fields) =>
      head != "=" && head != ":" &&
        Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom (.expression (.symbol head :: fields))
  | _ => false

theorem factPayload_has_value {pattern : Atom} (admitted : factPayload pattern = true) :
    Effects.removalNeedsValue pattern = false := by
  unfold factPayload at admitted
  split at admitted
  next head _ =>
    simp only [Bool.and_eq_true, bne_iff_ne] at admitted
    have ordinary : head ≠ "=" := admitted.1.1
    unfold Effects.removalNeedsValue
    split <;> simp_all
  next => cases admitted

def execute (spaceName : String) (target : Handle) (pattern : Atom) (fields : List Atom)
    (caller : Subst) (before : Effects.State) : Option (Effects.State × List Atom) := do
  if Subst.lookup caller spaceName = some (Effects.handleValue target) ∧ fields ≠ [] then do
    let rows ← before.read target
    let payloads := (choices caller pattern rows).map (fun bindings => applySubst bindings (.expression fields))
    if ClosedQueryAdmission.capturesReady caller pattern && ClosedQueryAdmission.rowsReady pattern rows &&
        payloads.all factPayload && ClosedQueryAdmission.targetReady before target payloads then
      run target pattern fields caller before
    else none
  else none

theorem execute_source (program : Program) (spaceName : String) (target : Handle)
    (pattern : Atom) (fields : List Atom) (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (completed : execute spaceName target pattern fields caller before = some (after, answers)) :
    PureReturns program caller before (source spaceName pattern fields) after (.grounded (.int answers.length)) := by
  unfold execute at completed
  split at completed
  next valid =>
    obtain ⟨rows, _, rest⟩ := Option.bind_eq_some_iff.mp completed
    dsimp only at rest
    split at rest
    · exact source_returns program spaceName target pattern fields caller before after answers valid.1 rest
    · cases rest
  next => cases completed

theorem execute_meaning (program : Program) (spaceName : String) (target : Handle)
    (pattern : Atom) (fields : List Atom) (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (completed : execute spaceName target pattern fields caller before = some (after, answers)) :
    PureCallPortfolio.sourceMeaning program caller (source spaceName pattern fields) before =
      {PureCallPortfolio.complete after (.grounded (.int answers.length))} := by
  have returned := execute_source program spaceName target pattern fields caller before after answers completed
  ext observed
  change DeclarativeSpec.Runs program {state := before, control := .evaluate caller (source spaceName pattern fields)}
    (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program caller before after _ _ returned]
  cases observed
  simp [PureCallPortfolio.complete, PureCallPortfolio.Completed.mk.injEq]

open Mettapedia.GSLT.Dynamics ObservationQualified in
def region {Regime : Type} (regime : Regime) (program : Program) (spaceName : String)
    (target : Handle) (pattern : Atom) (fields : List Atom) (caller : Subst) :
    CertifiedRegion (PureCallPortfolio.boundary program caller (source spaceName pattern fields)) Regime where
  regime := regime
  Artifact := PureCallPortfolio.Completed
  attempt before := match execute spaceName target pattern fields caller before with
    | none => .declined before
    | some receipt => .committed (PureCallPortfolio.complete receipt.1 (.grounded (.int receipt.2.length)))
  decode observed := {observed}
  restores before restored refused := by
    dsimp only at refused
    split at refused
    · exact (PartialRegionPlan.Attempt.declined.inj refused).symm
    · cases refused
  exact before observed committed := by
    split at committed
    · cases committed
    next receipt completed =>
      cases PartialRegionPlan.Attempt.committed.inj committed
      exact (execute_meaning program spaceName target pattern fields caller before receipt.1 receipt.2 completed).symm

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagErasure
