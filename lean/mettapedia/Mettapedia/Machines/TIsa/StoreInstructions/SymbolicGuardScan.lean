import Mettapedia.Machines.TIsa.StoreInstructions.IndexedGuard
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence

/-!
# Streamable guard decisions under residual knowledge

Presence needs an assured witness. Absence needs every occurrence
to be impossible. Exact count fails as soon as there is an
occurrence that could match but is not assured to match. It also
fails as soon as the requested number of assured matches is
exceeded. None of these decisions needs to materialize a set.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SymbolicGuardScan

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open IndexedGuard (Query)

section Scan

variable {O : Type*} (assured possible : O → Bool)

def countRemaining : ℕ → List O → Bool
  | remaining, [] => remaining == 0
  | remaining, o :: later =>
    if assured o then
      match remaining with
      | 0 => false
      | rest + 1 => countRemaining rest later
    else if possible o then false
    else countRemaining remaining later

theorem countRemaining_correct (remaining : ℕ) (occurrences : List O) :
    countRemaining assured possible remaining occurrences = true ↔
      occurrences.countP assured = remaining ∧
      ∀ o ∈ occurrences, possible o = true → assured o = true := by
  induction occurrences generalizing remaining with
  | nil =>
    have zero : remaining = 0 ↔ 0 = remaining := eq_comm
    simpa [countRemaining] using zero
  | cons o later ih =>
    cases a : assured o <;> cases p : possible o <;> cases remaining <;>
      simp [countRemaining, a, p, ih]

def scan (query : Query) (occurrences : List O) : Bool :=
  match query with
  | .any => occurrences.any assured
  | .absent => !(occurrences.any possible)
  | .count expected => countRemaining assured possible expected occurrences

theorem countRemaining_map {I : Type*} (project : I → O) (occurrences : List I) (remaining : ℕ) :
    countRemaining assured possible remaining (occurrences.map project) =
      countRemaining (assured ∘ project) (possible ∘ project) remaining occurrences := by
  induction occurrences generalizing remaining with
  | nil => rfl
  | cons first rest ih =>
    cases remaining <;> simp [countRemaining, Function.comp_def, ih]

theorem scan_map {I : Type*} (project : I → O) (occurrences : List I) (query : Query) :
    scan assured possible query (occurrences.map project) =
      scan (assured ∘ project) (possible ∘ project) query occurrences := by
  cases query with
  | any => simp [scan, List.any_map]
  | absent => simp [scan, List.any_map]
  | count expected => exact countRemaining_map assured possible project occurrences expected

/-- A single possible-but-not-assured occurrence rules out any
exact count claim, regardless of the unseen suffix. -/
theorem count_refuses_with_open_head (remaining : ℕ) (o : O) (later : List O)
    (openMatch : possible o = true) (notAssured : assured o = false) :
    scan assured possible (.count remaining) (o :: later) = false := by
  simp only [scan, countRemaining, notAssured, Bool.false_eq_true, if_false, openMatch, if_true]

end Scan

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  {O : Type} [DecidableEq O]

def assures (answer : Subst σ) (label : O → Term σ) (pattern : Term σ) (o : O) : Bool :=
  decide (answer.applyTerm pattern = answer.applyTerm (label o))

def permits (answer : Subst σ) (label : O → Term σ) (pattern : Term σ) (o : O) : Bool :=
  (unifyTotal [(answer.applyTerm pattern, answer.applyTerm (label o))]).isSome

private theorem certain_mem (answer : Subst σ) (label : O → Term σ) (pattern : Term σ) (occurrences : List O)
    (o : O) :
    o ∈ FirstOrderLicence.certain answer label occurrences.toFinset pattern ↔
      o ∈ occurrences ∧ assures answer label pattern o = true := by
  simp only [FirstOrderLicence.certain, assures, decide_eq_true_eq, Finset.mem_filter, List.mem_toFinset]

private theorem possible_mem (answer : Subst σ) (label : O → Term σ) (pattern : Term σ) (occurrences : List O)
    (o : O) :
    o ∈ FirstOrderLicence.potential answer label occurrences.toFinset pattern ↔
      o ∈ occurrences ∧ permits answer label pattern o = true := by
  simp only [FirstOrderLicence.potential, permits, Finset.mem_filter, List.mem_toFinset]

private theorem certain_count (answer : Subst σ) (label : O → Term σ) (pattern : Term σ) (occurrences : List O)
    (distinct : occurrences.Nodup) :
    (FirstOrderLicence.certain answer label occurrences.toFinset pattern).card =
      occurrences.countP (assures answer label pattern) :=
  distinct.card_eq_countP

theorem scan_correct (answer : Subst σ) (label : O → Term σ) (pattern : Term σ)
    (occurrences : List O) (distinct : occurrences.Nodup) (query : Query) :
    scan (assures answer label pattern) (permits answer label pattern) query occurrences =
      FirstOrderLicence.check answer label occurrences.toFinset (query.check pattern) := by
  apply Bool.eq_iff_iff.mpr
  cases query with
  | any =>
    simp only [scan, Query.check, FirstOrderLicence.check, decide_eq_true_eq,
      List.any_eq_true, Finset.Nonempty, certain_mem]
  | absent =>
    simp only [scan, Query.check, FirstOrderLicence.check, decide_eq_true_eq,
      Bool.not_eq_true', List.any_eq_false, Finset.eq_empty_iff_forall_notMem, possible_mem, not_and]
  | count expected =>
    simp only [scan, Query.check, FirstOrderLicence.check, decide_eq_true_eq, countRemaining_correct,
      certain_count answer label pattern occurrences distinct]
    refine and_congr_right (fun _ => ⟨?_, ?_⟩)
    · intro settled o maybe
      obtain ⟨found, openMatch⟩ := (possible_mem answer label pattern occurrences o).mp maybe
      exact (certain_mem answer label pattern occurrences o).mpr ⟨found, settled o found openMatch⟩
    · intro stable o found openMatch
      exact ((certain_mem answer label pattern occurrences o).mp
        (stable ((possible_mem answer label pattern occurrences o).mpr ⟨found, openMatch⟩))).2

theorem entails_check {problem : EquationStore (Term σ)} {answer : Subst σ}
    (principal : unifyTotal problem = some answer) (label : O → Term σ) (pattern : Term σ)
    (occurrences : List O) (distinct : occurrences.Nodup) (query : Query) :
    scan (assures answer label pattern) (permits answer label pattern) query occurrences = true ↔
      (FirstOrder.action σ).Entails problem
        (fun assignment => (query.check pattern).Holds (FirstOrder.action σ) assignment label occurrences.toFinset) := by
  rw [scan_correct answer label pattern occurrences distinct query]
  exact FirstOrderLicence.check_correct principal label occurrences.toFinset (query.check pattern)

namespace Examples

private abbrev atoms : LPSignature where
  vars := ℕ
  constants := Bool
  functionSymbols := Empty
  functionArity := fun _ => 0
  relationSymbols := Empty
  relationArity := fun _ => 0

private instance : DecidableEq atoms.vars := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq atoms.constants := inferInstanceAs (DecidableEq Bool)
private instance : DecidableEq atoms.functionSymbols := inferInstanceAs (DecidableEq Empty)

private def label (i : ℕ) : Term atoms := if i < 2 then .const true else .var 0

private def query (mode : Query) (ordinals : List ℕ) : Bool :=
  scan (assures (Subst.id atoms) label (.const true)) (permits (Subst.id atoms) label (.const true)) mode ordinals

theorem two_assured_occurrences_have_constant_count : query (.count 2) [0, 1] = true := by decide +kernel

private theorem variable_is_not_assured : assures (Subst.id atoms) label (.const true) 2 = false := by
  apply decide_eq_false
  change (Term.const true : Term atoms) ≠ (Term.var 0 : Term atoms)
  intro impossible
  cases impossible

private theorem variable_is_possible : permits (Subst.id atoms) label (.const true) 2 = true := by
  unfold permits
  apply (FirstOrderLicence.solver_isSome_iff (signature := atoms) _).mpr
  refine ⟨Subst.single (σ := atoms) 0 (.const true), ?_⟩
  intro equation mem
  obtain rfl := List.mem_singleton.mp mem
  rfl

theorem uncertainty_is_neither_presence_nor_absence :
    query .any [2] = false ∧ query .absent [2] = false ∧
      query (.count 0) [2] = false ∧ query (.count 1) [2] = false := by
  simp [query, scan, countRemaining, variable_is_not_assured, variable_is_possible]

theorem assured_presence_survives_uncertainty :
    query .any [0, 2] = true ∧ query (.count 1) [0, 2] = false := by
  have constant : assures (Subst.id atoms) label (.const true) 0 = true := by decide +kernel
  simp [query, scan, countRemaining, constant, variable_is_not_assured, variable_is_possible]

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.SymbolicGuardScan
