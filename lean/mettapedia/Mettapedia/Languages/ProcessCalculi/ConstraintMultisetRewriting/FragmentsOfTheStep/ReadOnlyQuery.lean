import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.GroundFirings

/-!
# Read-only queries

A rule is in the **read-only fragment** (`ReadOnly`) when it takes nothing and makes nothing; it may
read, tell and check. On the first-order step, for every substitution action:

* `readOnly_present`: **the store is unchanged** by a read-only firing.
* `readOnly_sameUpTo`: when what the query adds to the knowledge is already entailed by it
  (`Entailed`), the configuration is unchanged up to solutions. Over ground terms this always holds
  (`entailed_ground`); for a general action the hypothesis is asked, since a query's matching
  equations may refine shared variables.
* `query_first`: **a query is never a cause**: every firing is admitted before it exactly when after
  it, with the same result up to solutions.
* `query_commutes`: whenever the query is still admitted after another firing, **the two orders
  reach the same configuration** up to solutions.

The order that can fail is the query after the other firing. A firing that takes what the query reads
disables it: reads are in asymmetric conflict with takes, as in contextual nets. A query that also
asks a guard can be refused after a firing that changes what the guard reads.

## Controls (ground terms)

* Positive: `Controls.query_commutes_with_taker`: a query of `A` and a taker of `B`, in both orders.
* Negative, just outside: `Controls.consuming_query_is_a_cause`: a "query" that takes `A` and makes
  `A` again is not read-only; a reader of the old `A` is admitted before it and refused after it, so
  `query_first` fails.
* The direction that fails: `Controls.taker_disables_query`: a taker of `A` disables the query of `A`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReadOnlyQuery

open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **The read-only fragment**: the rule takes nothing and makes nothing. -/
def ReadOnly (rule : RuleInstance T) : Prop := rule.take = [] ∧ rule.produce = []

/-- What a firing adds is entailed by the knowledge it starts from. -/
def Entailed (rule : RuleInstance T) (selection : Selection O) (C : Configuration T O) : Prop :=
  ∀ σ, A.Models σ C.equations → A.Models σ (selection.problem label rule C)

variable {A label}

theorem readOnly_selection {rule : RuleInstance T} {selection : Selection O} {C : Configuration T O}
    (readOnly : ReadOnly rule) (valid : selection.Valid A label rule C) :
    selection.taken = [] ∧ selection.made = [] := by
  refine ⟨?_, ?_⟩
  · have lengths := valid.take_length
    rw [readOnly.1] at lengths
    exact List.length_eq_zero_iff.mp lengths.symm
  · have outputs := valid.outputs
    rw [readOnly.2] at outputs
    exact List.map_eq_nil_iff.mp outputs

/-- **A read-only firing leaves the store unchanged.** -/
theorem readOnly_present {rule : RuleInstance T} {selection : Selection O} {C : Configuration T O}
    (readOnly : ReadOnly rule) (valid : selection.Valid A label rule C) :
    (selection.result label rule C).present = C.present := by
  obtain ⟨taken, made⟩ := readOnly_selection readOnly valid
  simp [Selection.result, fire, Selection.commit, taken, made]

/-- **Unchanged up to solutions**, when what the query adds is entailed. -/
theorem readOnly_sameUpTo {rule : RuleInstance T} {selection : Selection O} {C : Configuration T O}
    (readOnly : ReadOnly rule) (valid : selection.Valid A label rule C)
    (entailed : Entailed A label rule selection C) : SameUpTo A C (selection.result label rule C) :=
  ⟨fun σ => ⟨entailed σ, fun solved => valid.refines σ solved⟩, (readOnly_present readOnly valid).symm⟩

/-- **A query is never a cause**: every firing is admitted before it exactly when after it, with
the same result up to solutions. -/
theorem query_first {rule : RuleInstance T} {selection : Selection O} {C : Configuration T O}
    (readOnly : ReadOnly rule) (valid : selection.Valid A label rule C)
    (entailed : Entailed A label rule selection C) (rule' : RuleInstance T) (selection' : Selection O) :
    (selection'.Valid A label rule' C ↔ selection'.Valid A label rule' (selection.result label rule C)) ∧
      SameUpTo A (selection'.result label rule' C)
        (selection'.result label rule' (selection.result label rule C)) := by
  have same := readOnly_sameUpTo readOnly valid entailed
  exact ⟨GuardFreeProcessOrders.valid_congr A label same,
    GuardFreeProcessOrders.result_congr A label rule' selection' same⟩

/-- **Both orders agree** whenever the query is still admitted after the other firing. -/
theorem query_commutes {rule rule' : RuleInstance T} {selection selection' : Selection O}
    {C : Configuration T O} (readOnly : ReadOnly rule) (valid : selection.Valid A label rule C)
    (entailed : Entailed A label rule selection C)
    (later : selection.Valid A label rule (selection'.result label rule' C))
    (entailedLater : Entailed A label rule selection (selection'.result label rule' C)) :
    SameUpTo A (selection'.result label rule' (selection.result label rule C))
      (selection.result label rule (selection'.result label rule' C)) :=
  GuardFreeProcessOrders.SameUpTo.trans A
    (AnnotatedRuns.sameUpTo_symm A (query_first readOnly valid entailed rule' selection').2)
    (readOnly_sameUpTo readOnly later entailedLater)

end ReadOnlyQuery

/-! ## Ground terms -/

namespace ReadOnlyQuery

open NamesOnTheStep NamesOnTheStep.IssuingControls

/-- **Over ground terms every query's information is entailed.** -/
theorem entailed_ground {rule : RuleInstance Expr} {selection : Selection Occ} {C : Conf}
    (valid : selection.Valid ground Prod.fst rule C) : Entailed ground Prod.fst rule selection C := by
  intro σ _
  cases σ
  exact GroundFirings.solved_of_valid valid

end ReadOnlyQuery

namespace ReadOnlyQuery.Controls

open NamesOnTheStep NamesOnTheStep.IssuingControls GroundFirings
open GuardFreeProcessOrders (SameUpTo)

def factA : Expr := .sym 40
def factB : Expr := .sym 41
def factW : Expr := .sym 42

/-- The store holding one `A` and one `B`. -/
def start : Conf := ⟨[], {(factA, 0), (factB, 0)}⟩

/-- The query of `A`, and its selection. -/
def query : RuleInstance Expr := rule [] [factA] []
def queryAt : Selection Occ := ⟨[], [(factA, 0)], []⟩

/-- A taker of `B`. -/
def takeB : RuleInstance Expr := rule [factB] [] [factW]
def takeBAt : Selection Occ := ⟨[(factB, 0)], [], [(factW, 0)]⟩

/-- A taker of `A`. -/
def takeA : RuleInstance Expr := rule [factA] [] [factW]
def takeAAt : Selection Occ := ⟨[(factA, 0)], [], [(factW, 0)]⟩

/-- Take `A` and make `A` again: a consuming "query". -/
def consume : RuleInstance Expr := rule [factA] [] [factA]
def consumeAt : Selection Occ := ⟨[(factA, 0)], [], [(factA, 1)]⟩

theorem query_readOnly : ReadOnly query := ⟨rfl, rfl⟩

theorem query_valid : queryAt.Valid ground Prod.fst query start :=
  ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)

theorem takeB_valid : takeBAt.Valid ground Prod.fst takeB start :=
  ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)

theorem query_after_takeB :
    queryAt.Valid ground Prod.fst query (takeBAt.result Prod.fst takeB start) :=
  ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (result_knowledge takeB_valid) rfl
    (no_checks rfl)

/-- **Positive control.** The query of `A` and the taker of `B` run in both orders to the same
configuration. -/
theorem query_commutes_with_taker :
    SameUpTo ground (takeBAt.result Prod.fst takeB (queryAt.result Prod.fst query start))
      (queryAt.result Prod.fst query (takeBAt.result Prod.fst takeB start)) :=
  query_commutes query_readOnly query_valid (entailed_ground query_valid) query_after_takeB
    (entailed_ground query_after_takeB)

theorem consume_valid : consumeAt.Valid ground Prod.fst consume start :=
  ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)

/-- **Negative control.** Taking `A` and making `A` again is not read-only, and it is a cause: the
reader of the old `A` is admitted before it and refused after it. -/
theorem consuming_query_is_a_cause :
    ¬ ReadOnly consume ∧ queryAt.Valid ground Prod.fst query start ∧
      ¬ queryAt.Valid ground Prod.fst query (consumeAt.result Prod.fst consume start) := by
  refine ⟨fun readOnly => by simp [ReadOnly, consume, rule] at readOnly, query_valid, fun valid => ?_⟩
  have present := read_present valid (o := (factA, 0)) (by simp [queryAt])
  revert present
  decide

theorem takeA_valid : takeAAt.Valid ground Prod.fst takeA start :=
  ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)

/-- **The order that fails.** A taker of `A` disables the query of `A`: reads are in asymmetric
conflict with takes. -/
theorem taker_disables_query :
    queryAt.Valid ground Prod.fst query start ∧ takeAAt.Valid ground Prod.fst takeA start ∧
      ¬ queryAt.Valid ground Prod.fst query (takeAAt.result Prod.fst takeA start) := by
  refine ⟨query_valid, takeA_valid, fun valid => ?_⟩
  have present := read_present valid (o := (factA, 0)) (by simp [queryAt])
  revert present
  decide

end ReadOnlyQuery.Controls

open ReadOnlyQuery in
#print axioms readOnly_present
open ReadOnlyQuery in
#print axioms query_first
open ReadOnlyQuery in
#print axioms query_commutes
open ReadOnlyQuery in
#print axioms entailed_ground
#print axioms ReadOnlyQuery.Controls.query_commutes_with_taker
#print axioms ReadOnlyQuery.Controls.consuming_query_is_a_cause
#print axioms ReadOnlyQuery.Controls.taker_disables_query

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep
