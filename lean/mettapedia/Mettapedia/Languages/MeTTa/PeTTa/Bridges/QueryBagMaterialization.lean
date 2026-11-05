import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshConstructorSource

/-!
# Source query materialization into ordinary bag spaces

The source performs one raw `add-atom` per matched occurrence. Every insertion
appends a row and returns true, including duplicate payloads. These laws keep
that behavior distinct from guarded insertion and from a set-space extension.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagMaterialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def insertion (spaceName : String) (template : Atom) : Atom :=
  .expression [.symbol "add-atom", .var spaceName, template]

def emit (target : Handle) (template : Atom) : Body := fun bindings before =>
  (Effects.insert before target (applySubst bindings template)).map (fun after => (after, [Effects.boolean true]))

def installRows (target : Handle) : List Atom → Effects.State → Option Effects.State
  | [], before => some before
  | row :: rest, before => (Effects.insert before target row).bind (installRows target rest)

theorem emit_returns (program : Program) (spaceName : String) (target : Handle) (template : Atom)
    (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue target))
    (completed : emit target template bindings before = some (after, answers)) :
    Returns program bindings before (insertion spaceName template) after answers := by
  obtain ⟨next, inserted, same⟩ := Option.map_eq_some_iff.mp completed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact FreshConstructorSource.insert_returns program bindings before next spaceName template target location inserted

theorem traverse_install_exact (target : Handle) (template : Atom) (captured : List Subst)
    (before : Effects.State) (collected : List Atom) :
    traverse (emit target template) captured (before, collected) =
      (installRows target (captured.map (fun bindings => applySubst bindings template)) before).map
        (fun after => (after, collected ++ List.replicate captured.length (Effects.boolean true))) := by
  induction captured generalizing before collected with
  | nil => simp [EffectfulQuerySource.traverse, installRows]
  | cons bindings rest ih =>
      simp only [EffectfulQuerySource.traverse, emit, List.map_cons, installRows, Option.bind_map, Option.map_bind,
        Function.comp_def, ih]
      apply congrArg ((Effects.insert before target (applySubst bindings template)).bind)
      funext middle
      simp [List.replicate_succ, List.append_assoc]

theorem installRows_exists (target : Handle) (payloads : List Atom) (before : Effects.State) (rows : List Atom)
    (snapshot : before.read target = some rows) : ∃ after, installRows target payloads before = some after := by
  induction payloads generalizing before rows with
  | nil => exact ⟨before, rfl⟩
  | cons payload rest ih =>
      obtain ⟨middle, inserted⟩ := Effects.insert_exists_of_read_some snapshot payload
      obtain ⟨_, _, middleRead⟩ := Effects.insert_reads_back inserted
      obtain ⟨after, later⟩ := ih middle _ middleRead
      exact ⟨after, by simp [installRows, inserted, later]⟩

theorem installRows_receipt (target : Handle) (payloads : List Atom) (before after : Effects.State) (rows : List Atom)
    (snapshot : before.read target = some rows) (completed : installRows target payloads before = some after) :
    after.read target = some (rows ++ payloads) ∧
      (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  induction payloads generalizing before rows with
  | nil =>
      cases Option.some.inj completed
      exact ⟨by simpa using snapshot, fun _ _ => rfl, rfl⟩
  | cons payload rest ih =>
      obtain ⟨middle, inserted, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨old, oldRead, middleRead⟩ := Effects.insert_reads_back inserted
      have same : old = rows := Option.some.inj (oldRead.symm.trans snapshot)
      subst old
      obtain ⟨readAfter, others, cells⟩ := ih middle (rows ++ [payload]) middleRead later
      exact ⟨by simpa only [List.append_assoc, List.singleton_append] using readAfter,
        fun other apart => (others other apart).trans (Effects.insert_read_other inserted apart),
        cells.trans (Effects.insert_preserves_cells inserted)⟩

theorem traverse_receipt (target : Handle) (template : Atom) (captured : List Subst)
    (before after : Effects.State) (rows collected answers : List Atom)
    (snapshot : before.read target = some rows)
    (completed : traverse (emit target template) captured (before, collected) = some (after, answers)) :
    after.read target = some (rows ++ captured.map (fun bindings => applySubst bindings template)) ∧
      answers = collected ++ List.replicate captured.length (Effects.boolean true) ∧
      (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  rw [traverse_install_exact] at completed
  obtain ⟨finish, installed, same⟩ := Option.map_eq_some_iff.mp completed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  obtain ⟨readAfter, others, cells⟩ := installRows_receipt target _ before finish rows snapshot installed
  exact ⟨readAfter, rfl, others, cells⟩

theorem nested_returns (program : Program) (spaceName : String) (target : Handle) (template : Atom)
    (legs : List NestedQuerySource.Leg) (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (location : Subst.lookup caller spaceName = some (Effects.handleValue target))
    (completed : NestedQuerySource.run (emit target template) legs caller before = some (after, answers)) :
    Returns program caller before (NestedQuerySource.source legs (insertion spaceName template)) after answers := by
  apply NestedQuerySource.run_returns program (insertion spaceName template) (emit target template)
    (fun bindings => Subst.lookup bindings spaceName = some (Effects.handleValue target))
    (fun bindings before after answers found executed => emit_returns program spaceName target template bindings before after answers found executed)
    legs _ caller before after answers location completed
  intro leg _ bindings rows bound found member
  exact choices_extend bindings leg.2 rows bound member spaceName _ found

theorem counted_returns (program : Program) (spaceName : String) (target : Handle) (template : Atom)
    (legs : List NestedQuerySource.Leg) (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (location : Subst.lookup caller spaceName = some (Effects.handleValue target))
    (completed : NestedQuerySource.run (emit target template) legs caller before = some (after, answers)) :
    PureReturns program caller before (.expression [.symbol "size-atom", .expression [.symbol "collapse",
      NestedQuerySource.source legs (insertion spaceName template)]]) after (.grounded (.int answers.length)) := by
  have collected := collapse_returns program caller before after _ _
    (nested_returns program spaceName target template legs caller before after answers location completed)
  exact native_unary_call_returns program caller before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagMaterialization
