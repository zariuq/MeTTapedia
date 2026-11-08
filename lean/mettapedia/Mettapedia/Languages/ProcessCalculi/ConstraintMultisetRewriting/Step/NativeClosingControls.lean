import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeClosing

/-!
# Controls for the native residual and the closing leg

## Reusable outputs are snapshots, so the closing leg fails for them

The closing leg (`LiveFiring.closing`) is proved for live outputs, which are published as shared rows
that later knowledge keeps constraining. A **reusable** output is published differently: its row is a
schema over private copies of the names it mentions, with the information at publication as its
obligations, so its meaning is the set of instances of the output at the solutions of that
information (`ContextualConditionalExecution.Firing.ordinary_matches_source`).

* **A reusable row is a snapshot** (`snapshot_retained`): carried to every later state, it matches at
  every candidate exactly the source instances of the information at publication. Later knowledge
  does not reach it.
* **A live row is not** (`live_retained`): carried to a later state, it matches exactly the output
  read at the candidate, so later knowledge constrains it.
* **Snapshots depend on the information at publication** (`snapshot_order`): one more equation in
  that information can change the snapshot's meaning. In the order `g` then `f`, the meaning of a
  reusable output of `g` is fixed before `f`'s information is known (`snapshot_retained`); in the
  order `f` then `g`, `g`'s output is published with `f`'s information already in the knowledge. When
  `f`'s information constrains a name the output mentions, the two meanings can differ. No solver is
  involved: the meaning of a reusable row is the same for every solver return
  (`ContextualConditionalAnswers.ofUpdate_exact`).

## Closure queries do not determine their residual

A pattern query is read at a later frame by carrying its pattern (`matchingQuery_holds_carried`). A
query given only by its region on the rows of its own frame has to be extended to rows the other
firing publishes, which are not carried rows. Two extensions that agree with the query on every carried
row can disagree on a published row, and with it on admission (`closure_extensions_disagree`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeClosingControls

section Snapshots

variable {s : NativeState S O Γ sort} (G : ContextualConditionalExecution.Firing s.locals s.state)
  (H : ContextualConditionalExecution.Firing (rawTarget G).locals (rawTarget G).state)

/-- **A reusable row is a snapshot**: carried to a later state, a reusable output's row matches, at
every candidate, exactly the source instances of the information at its publication. -/
theorem snapshot_retained {o : O} (made : o ∈ G.selection.made) (reusable : G.reusable o = true)
    (notMade : o ∉ H.selection.made) {W : Type} {next : W → MetaArity S}
    (candidate : Assignment H.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualConditionalRows.Matches (rawTarget H).locals H.target.declarations candidate pattern
        (H.target.rows o) ↔
      ContextualPublication.SourceInstances (problemOf s G.selection G.rule) (G.outputs o) next pattern := by
  refine (Iff.of_eq (congrArg (fun row => ContextualConditionalRows.Matches (rawTarget H).locals
    H.target.declarations candidate pattern row) (rows_of_not_made (s := rawTarget G) H notMade))).trans ?_
  refine (ContextualConditionalPublication.extendPrivate_matches_iff (rawTarget G).locals H.update.declaration
    H.target.declarations candidate _ pattern).trans ?_
  refine (ContextualConditionalRows.matches_map_iff (rawTarget G).locals (rawTarget G).state.declarations
    (change (s := rawTarget G) H) candidate pattern _).trans ?_
  exact G.ordinary_matches_source o made reusable next _ pattern

/-- **A live row is not a snapshot**: carried to a later state, a live output's row matches exactly
the output read at the candidate. -/
theorem live_retained {o : O} (made : o ∈ G.selection.made) (live : G.reusable o = false)
    (notMade : o ∉ H.selection.made) {W : Type} {next : W → MetaArity S}
    (candidate : Assignment H.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualConditionalRows.Matches (rawTarget H).locals H.target.declarations candidate pattern
        (H.target.rows o) ↔
      pattern = instantiate (Assignment.compose (Assignment.compose candidate (change (s := rawTarget G) H))
        (ContextualComputedFreshFrame.includeSource G.update)) (G.outputs o) := by
  refine (Iff.of_eq (congrArg (fun row => ContextualConditionalRows.Matches (rawTarget H).locals
    H.target.declarations candidate pattern row) (rows_of_not_made (s := rawTarget G) H notMade))).trans ?_
  refine (ContextualConditionalPublication.extendPrivate_matches_iff (rawTarget G).locals H.update.declaration
    H.target.declarations candidate _ pattern).trans ?_
  refine (ContextualConditionalRows.matches_map_iff (rawTarget G).locals (rawTarget G).state.declarations
    (change (s := rawTarget G) H) candidate pattern _).trans ?_
  refine (Iff.of_eq (congrArg (fun row => ContextualConditionalRows.Matches (rawTarget G).locals
    (rawTarget G).state.declarations (Assignment.compose candidate (change (s := rawTarget G) H)) pattern row)
    (G.shared_row o made live))).trans ?_
  refine (ContextualConditionalRows.ofStored_matches_iff (rawTarget G).locals (rawTarget G).state.declarations
    (Assignment.compose candidate (change (s := rawTarget G) H)) pattern _).trans ?_
  exact Iff.of_eq (congrArg (fun term => pattern = term)
    (Assignment.instantiate_compose (Assignment.compose candidate (change (s := rawTarget G) H))
      (ContextualComputedFreshFrame.includeSource G.update) (G.outputs o)).symm)

end Snapshots

/-! ### Snapshots depend on the information at publication -/

/-- A signature with one sort and two constants. -/
def bits : Signature where
  Srt := Unit
  Op _ := Bool
  arity _ := []

/-- A frame with one parameterless name. -/
def oneName : Unit → MetaArity bits := fun _ => ([], ())

/-- A frame with no names. -/
def noNames : Empty → MetaArity bits := fun impossible => nomatch impossible

/-- A constant, in any frame. -/
def constant {V : Type} (declaration : V → MetaArity bits) (value : Bool) :
    Term (signature bits declaration) ([] : Ctx bits) () :=
  .op (.inl value) .nil

/-- **Snapshots depend on the order**: the name's value `false` is an instance of the name under no
information, and is not once the information says the name is `true`. -/
theorem snapshot_order :
    ContextualPublication.SourceInstances ([] : ContextualResidual.Problem oneName) (generator oneName ())
        noNames (constant noNames false) ∧
      ¬ ContextualPublication.SourceInstances
        [(observe (generator oneName ()), observe (constant oneName true))] (generator oneName ())
        noNames (constant noNames false) := by
  constructor
  · refine ⟨ContextualGuardMatching.Extension.identity noNames,
      fun _ => constant (ContextualGuardMatching.Extension.identity noNames).declarations false,
      fun _ member => absurd member List.not_mem_nil, ?_⟩
    exact instantiate_generator _ ()
  · rintro ⟨extension, candidate, model, same⟩
    have value : instantiate candidate (generator oneName ()) = instantiate candidate (constant oneName true) :=
      observe_injective (model _ List.mem_cons_self)
    have clash : constant extension.declarations true = constant extension.declarations false :=
      value.symm.trans same
    unfold constant at clash
    cases clash

/-! ## Closure queries do not determine their residual -/

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (PredicateQuery)

/-- Rows at a later frame: the carried rows `0` and `1`, and a published row `2`. -/
def carryRow (row : Bool) : ℕ := if row then 1 else 0

/-- A closure query at the earlier frame: no occurrence may hold the row `true`. -/
def closure : PredicateQuery ℕ (ℕ × Bool) := ⟨fun label => label.2, ∅⟩

/-- One extension to the later frame: it sees the carried `true` row only. -/
def extensionOne : PredicateQuery ℕ (ℕ × ℕ) := ⟨fun label => decide (label.2 = 1), ∅⟩

/-- Another extension: it also sees the published row. -/
def extensionTwo : PredicateQuery ℕ (ℕ × ℕ) := ⟨fun label => decide (label.2 = 1 ∨ label.2 = 2), ∅⟩

/-- **Two extensions of a closure query agree with it on every carried row and disagree on admission
once the other firing has published a row**. -/
theorem closure_extensions_disagree :
    (∀ (o : ℕ) (row : Bool), extensionOne.region (o, carryRow row) = closure.region (o, row) ∧
      extensionTwo.region (o, carryRow row) = closure.region (o, row)) ∧
      extensionOne.Holds (fun o => (o, 2)) {0} ∧ ¬ extensionTwo.Holds (fun o => (o, 2)) {0} := by
  refine ⟨fun o row => ?_, by decide, by decide⟩
  cases row <;> exact ⟨rfl, rfl⟩

end NativeClosingControls

#print axioms NativeClosingControls.snapshot_retained
#print axioms NativeClosingControls.live_retained
#print axioms NativeClosingControls.snapshot_order
#print axioms NativeClosingControls.closure_extensions_disagree

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
