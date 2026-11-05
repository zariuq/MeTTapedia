import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryMaterialization

/-!
# Fresh insertion through dynamically read nested queries

Successful answers count new rows, even when an inner query observes rows
inserted by an earlier body. Zero progress is equivalent to an unchanged
state and saturation of this complete query schema in that state. It does
not assert that other rules have been visited or that an entire driver has
terminated. Missing access remains refusal, not a zero result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshNestedQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource
open NestedQuerySource (Leg)

def run (target : Handle) (template : Atom) (legs : List Leg) : Body :=
  NestedQuerySource.run (FreshQueryMaterialization.emit target template) legs

#print axioms run.eq_1

def BindingsReady (targetName temporary : String) (target : Handle) (bindings : Subst) : Prop :=
  Subst.lookup bindings targetName = some (Effects.handleValue target) ∧ Subst.lookup bindings temporary = none

theorem bindings_stable (targetName temporary : String) (target : Handle) (pattern : Atom)
    (outside : temporary ∉ atomFreeVars pattern) (bindings bound : Subst) (rows : List Atom)
    (valid : BindingsReady targetName temporary target bindings) (member : bound ∈ choices bindings pattern rows) :
    BindingsReady targetName temporary target bound := by
  exact ⟨choices_extend bindings pattern rows bound member targetName _ valid.1,
    (choices_lookup_outside bindings pattern rows bound member temporary outside).trans valid.2⟩

theorem source_returns (program : Program) (targetName temporary : String) (target : Handle)
    (template : Atom) (legs : List Leg) (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (different : temporary ≠ targetName)
    (outside : ∀ leg ∈ legs, temporary ∉ atomFreeVars leg.2)
    (valid : BindingsReady targetName temporary target caller)
    (completed : run target template legs caller before = some (after, answers)) :
    Returns program caller before
      (NestedQuerySource.source legs (FreshQueryMaterialization.bodySource targetName temporary template)) after answers := by
  apply NestedQuerySource.run_returns program _ _ (BindingsReady targetName temporary target)
  · intro bindings current next values ready returned
    exact FreshQueryMaterialization.emit_returns program bindings current next targetName temporary target
      template values different ready.1 ready.2 returned
  · intro leg member bindings rows bound ready present
    exact bindings_stable targetName temporary target leg.2 (outside leg member) bindings bound rows ready present
  · exact valid
  · exact completed

theorem counted_source_returns (program : Program) (targetName temporary : String) (target : Handle)
    (template : Atom) (legs : List Leg) (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (different : temporary ≠ targetName)
    (outside : ∀ leg ∈ legs, temporary ∉ atomFreeVars leg.2)
    (valid : BindingsReady targetName temporary target caller)
    (completed : run target template legs caller before = some (after, answers)) :
    PureReturns program caller before
      (.expression [.symbol "size-atom", .expression [.symbol "collapse",
        NestedQuerySource.source legs (FreshQueryMaterialization.bodySource targetName temporary template)]])
      after (.grounded (.int answers.length)) := by
  have returned := source_returns program targetName temporary target template legs caller before after answers
    different outside valid completed
  have collected := collapse_returns program caller before after _ _ returned
  exact native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

theorem emit_silent (target : Handle) (template : Atom) :
    NestedQuerySource.silent (FreshQueryMaterialization.emit target template) := by
  intro bindings before after returned
  have traversed : EffectfulQuerySource.traverse (FreshQueryMaterialization.emit target template)
      [bindings] (before, []) = some (after, []) := by
    simp [EffectfulQuerySource.traverse, returned]
  exact FreshQueryMaterialization.empty_traversal_preserves_state target template [bindings] before after traversed

theorem emit_growth (target : Handle) (template : Atom) :
    NestedQuerySource.Growth target (FreshQueryMaterialization.emit target template) := by
  intro bindings before after answers rows snapshot returned
  obtain ⟨receipt, updated, same⟩ := Option.map_eq_some_iff.mp returned
  rcases receipt with ⟨middle, changed⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  obtain ⟨old, result, oldRead, finalRead, growth⟩ := FreshInsertionSource.update_growth updated
  have equalRows : old = rows := Option.some.inj (oldRead.symm.trans snapshot)
  exact ⟨result, finalRead, by simpa [equalRows] using growth⟩

theorem run_growth (target : Handle) (template : Atom) (legs : List Leg) :
    NestedQuerySource.Growth target (run target template legs) :=
  NestedQuerySource.run_growth target _ (emit_growth target template) legs

theorem zero_preserves_state (target : Handle) (template : Atom) (legs : List Leg)
    (caller : Subst) (before after : Effects.State)
    (completed : run target template legs caller before = some (after, [])) : before = after :=
  NestedQuerySource.run_silent _ (emit_silent target template) legs caller before after completed

theorem emit_empty_iff (target : Handle) (template : Atom) (bindings : Subst) (state : Effects.State) :
    FreshQueryMaterialization.emit target template bindings state = some (state, []) ↔
      ∃ rows, state.read target = some rows ∧ applySubst bindings template ∈ rows := by
  cases snapshot : state.read target with
  | none => simp [FreshQueryMaterialization.emit, FreshInsertionSource.update, snapshot]
  | some rows =>
      by_cases present : applySubst bindings template ∈ rows
      · simp [FreshQueryMaterialization.emit, FreshInsertionSource.update, snapshot, present, FreshInsertionSource.answers]
      · obtain ⟨after, inserted⟩ := Effects.insert_exists_of_read_some snapshot (applySubst bindings template)
        simp [FreshQueryMaterialization.emit, FreshInsertionSource.update, snapshot, present, inserted, FreshInsertionSource.answers]

/-- Every reached read is complete, and every full current binding already
has its instantiated head. This is for one schema, not all rules in a store. -/
def SaturatedAt (state : Effects.State) (target : Handle) (template : Atom) : List Leg → Subst → Prop
  | [], bindings => ∃ rows, state.read target = some rows ∧ applySubst bindings template ∈ rows
  | (handle, pattern) :: rest, bindings =>
      ∃ rows, state.read handle = some rows ∧
        ∀ bound ∈ choices bindings pattern rows, SaturatedAt state target template rest bound

theorem quiet_iff_saturated (state : Effects.State) (target : Handle) (template : Atom)
    (legs : List Leg) (caller : Subst) :
    NestedQuerySource.QuietAt (FreshQueryMaterialization.emit target template) state legs caller ↔
      SaturatedAt state target template legs caller := by
  induction legs generalizing caller with
  | nil => exact emit_empty_iff target template caller state
  | cons leg rest ih =>
      rcases leg with ⟨handle, pattern⟩
      simp only [NestedQuerySource.QuietAt, SaturatedAt]
      exact exists_congr fun rows => and_congr_right fun _ =>
        forall_congr' fun bound => imp_congr_right fun _ => ih bound

theorem zero_iff_saturated (target : Handle) (template : Atom) (legs : List Leg)
    (caller : Subst) (before after : Effects.State) :
    run target template legs caller before = some (after, []) ↔
      before = after ∧ SaturatedAt before target template legs caller := by
  constructor
  · intro completed
    have same := zero_preserves_state target template legs caller before after completed
    subst after
    refine ⟨rfl, ?_⟩
    exact (quiet_iff_saturated before target template legs caller).mp
      ((NestedQuerySource.run_empty_iff _ (emit_silent target template) before legs caller).mp completed)
  · rintro ⟨rfl, saturated⟩
    exact (NestedQuerySource.run_empty_iff _ (emit_silent target template) before legs caller).mpr
      ((quiet_iff_saturated before target template legs caller).mpr saturated)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshNestedQuerySource
