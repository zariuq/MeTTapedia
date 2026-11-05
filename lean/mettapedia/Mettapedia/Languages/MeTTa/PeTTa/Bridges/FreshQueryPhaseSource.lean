import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshNestedQuerySource

/-!
# Complete authored phases of positive fresh-insertion query schemas

Each schema performs source-ordered nested reads in the current state. Schema
results are counted and added in authored order. The phase's progress equals
destination row growth, not producer occurrences. Zero progress characterizes
saturation of every schema in this phase in one unchanged state.

This does not yet identify an arbitrary recursive driver with the phase or
prove that its possible new heads lie in a finite catalogue.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryPhaseSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open Eval SpaceSemantics NamedSpaces

structure Schema where
  legs : List NestedQuerySource.Leg
  template : Atom

def schemaSource (targetName temporary : String) (schema : Schema) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse",
    NestedQuerySource.source schema.legs (FreshQueryMaterialization.bodySource targetName temporary schema.template)]]

def source (targetName temporary : String) : List Schema → Atom
  | [] => .grounded (.int 0)
  | schema :: rest => .expression [.symbol "+", schemaSource targetName temporary schema, source targetName temporary rest]

def run (target : Handle) (caller : Subst) : List Schema → Effects.State → Option (Effects.State × Nat)
  | [], state => some (state, 0)
  | schema :: rest, state => do
      let first ← FreshNestedQuerySource.run target schema.template schema.legs caller state
      let later ← run target caller rest first.1
      return (later.1, first.2.length + later.2)

theorem source_returns (program : Program) (targetName temporary : String) (target : Handle)
    (caller : Subst) (schemas : List Schema) (before after : Effects.State) (count : Nat)
    (different : temporary ≠ targetName)
    (outside : ∀ schema ∈ schemas, ∀ leg ∈ schema.legs, temporary ∉ atomFreeVars leg.2)
    (valid : FreshNestedQuerySource.BindingsReady targetName temporary target caller)
    (completed : run target caller schemas before = some (after, count)) :
    PureReturns program caller before (source targetName temporary schemas) after (.grounded (.int count)) := by
  induction schemas generalizing before after count with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
      exact grounded_returns program caller before (.int 0)
  | cons schema rest ih =>
      obtain ⟨first, firstRun, remaining⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨later, laterRun, same⟩ := Option.bind_eq_some_iff.mp remaining
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      have firstSource := FreshNestedQuerySource.counted_source_returns program targetName temporary target
        schema.template schema.legs caller before first.1 first.2 different
        (outside schema List.mem_cons_self) valid firstRun
      have laterSource := ih first.1 later.1 later.2
        (fun next member => outside next (List.mem_cons_of_mem _ member)) laterRun
      have sumSource := native_binary_call_returns program caller before first.1 later.1 later.1 "+"
        (schemaSource targetName temporary schema) (source targetName temporary rest)
        (.grounded (.int first.2.length)) (.grounded (.int later.2)) (.grounded (.int (first.2.length + later.2)))
        (by decide) (by decide)
        (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
        (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) firstSource laterSource
        (by simpa only [Int.natCast_add] using
          StdLib.integer_addition later.1 first.2.length later.2) (by decide)
      exact sumSource

theorem growth (target : Handle) (caller : Subst) (schemas : List Schema)
    (before after : Effects.State) (rows : List Atom) (count : Nat)
    (snapshot : before.read target = some rows)
    (completed : run target caller schemas before = some (after, count)) :
    ∃ result, after.read target = some result ∧ result.length = rows.length + count := by
  induction schemas generalizing before rows count with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
      exact ⟨rows, snapshot, by simp⟩
  | cons schema rest ih =>
      obtain ⟨first, firstRun, remaining⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨later, laterRun, same⟩ := Option.bind_eq_some_iff.mp remaining
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      obtain ⟨middleRows, middleRead, firstGrowth⟩ := FreshNestedQuerySource.run_growth target schema.template schema.legs
        caller before first.1 first.2 rows snapshot firstRun
      obtain ⟨result, resultRead, laterGrowth⟩ := ih first.1 middleRows later.2 middleRead laterRun
      exact ⟨result, resultRead, by omega⟩

theorem zero_iff_saturated (target : Handle) (caller : Subst) (schemas : List Schema)
    (before after : Effects.State) :
    run target caller schemas before = some (after, 0) ↔
      before = after ∧ ∀ schema ∈ schemas,
        FreshNestedQuerySource.SaturatedAt before target schema.template schema.legs caller := by
  induction schemas generalizing before after with
  | nil => simp [run]
  | cons schema rest ih =>
      constructor
      · intro completed
        obtain ⟨first, firstRun, remaining⟩ := Option.bind_eq_some_iff.mp completed
        obtain ⟨later, laterRun, same⟩ := Option.bind_eq_some_iff.mp remaining
        have counts := (Prod.mk.inj (Option.some.inj same)).2
        have firstEmpty : first.2 = [] := List.length_eq_zero_iff.mp (by omega)
        have laterZero : later.2 = 0 := by omega
        have unchanged := FreshNestedQuerySource.zero_preserves_state target schema.template schema.legs caller before first.1
          (firstRun.trans (congrArg some (Prod.ext rfl firstEmpty)))
        have firstSat := (FreshNestedQuerySource.zero_iff_saturated target schema.template schema.legs caller before first.1).mp
          (firstRun.trans (congrArg some (Prod.ext rfl firstEmpty)))
        have afterEq : later.1 = after := (Prod.mk.inj (Option.some.inj same)).1
        have tailRun : run target caller rest before = some (after, 0) := by
          rw [unchanged]
          exact laterRun.trans (congrArg some (Prod.ext afterEq laterZero))
        obtain ⟨allSame, restSat⟩ := ih before after |>.mp tailRun
        refine ⟨allSame, ?_⟩
        intro rule member
        rcases List.mem_cons.mp member with equal | member
        · simpa [equal] using firstSat.2
        · exact restSat rule member
      · rintro ⟨rfl, saturated⟩
        have firstRun := (FreshNestedQuerySource.zero_iff_saturated target schema.template schema.legs caller before before).mpr
          ⟨rfl, saturated schema List.mem_cons_self⟩
        have tailRun := (ih before before).mpr ⟨rfl, fun rule member => saturated rule (List.mem_cons_of_mem _ member)⟩
        simp [run, firstRun, tailRun]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshQueryPhaseSource
