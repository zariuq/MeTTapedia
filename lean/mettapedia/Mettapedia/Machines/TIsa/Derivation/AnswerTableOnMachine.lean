import Mettapedia.Machines.TIsa.Derivation.AnswerTable
import Mettapedia.Machines.TIsa.Derivation.Evaluator
import Mathlib.Data.List.OfFn

/-!
# Positive answer rounds on the Transform evaluator

A clause reads its prerequisite answers and makes one answer. The
reference round reads all clauses against the same previous layer,
and puts the new answers in a fresh layer. The count array evaluates
the same round without enumerating the read selections. In particular,
the rule may read the same available occurrence at two different ports.

The two layers are not a change of the general store discipline.
Consumption, destructive effects, and asks whose truth is not
preserved by extending the answer relation are not table rules.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.AnswerTable

variable {n : ℕ}

def equalityMatcher (n : ℕ) : Matcher (Fin n) (Fin n) Unit where
  empty := ()
  extend _ expected actual := if actual == expected then some () else none
  instantiate _ value := some value

def Clause.asRule (clause : Clause n) : Rule (Fin n) :=
  ⟨PUnit.unit, ⟨[], clause.premises, [], [], [clause.conclusion]⟩, []⟩

def occurrenceCount (s : Store (Fin n)) (key : Fin n) : ℕ :=
  s.occurrences.countP (fun occurrence => occurrence.2 == key)

private theorem flatMap_replicate_count {A B : Type*} (items : List A) (keep : A → Bool)
    (alternatives : ℕ) (output : B) :
    (items.flatMap fun a => if keep a then List.replicate alternatives output else []) =
      List.replicate (items.countP keep * alternatives) output := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    rw [List.flatMap_cons, List.countP_cons]
    cases keep first with
    | false => simp [ih]
    | true => simp [ih, Nat.add_mul, Nat.add_comm]

private theorem read_outputs (s : Store (Fin n)) (requirements : List (Fin n)) (output : Fin n)
    (matched : Match (Fin n) Unit) (noTake : matched.taken = []) :
    (solve (equalityMatcher n) s (requirements.map (Goal.premise .read) ++
      [.determinate (.produce output)]) matched).map Match.made =
      List.replicate ((requirements.map (occurrenceCount s)).prod) (matched.made ++ [output]) := by
  induction requirements generalizing matched with
  | nil => rfl
  | cons key rest ih =>
    simp only [List.map_cons, List.cons_append, solve, List.map_flatMap, List.prod_cons]
    calc
      _ = s.occurrences.flatMap (fun occurrence =>
          if occurrence.2 == key then
            List.replicate ((rest.map (occurrenceCount s)).prod) (matched.made ++ [output])
          else []) := by
        apply List.flatMap_congr
        intro occurrence _
        by_cases available : occurrence.2 = key
        · have allowed : attempt (equalityMatcher n) .read key matched occurrence =
              some (matched.select .read occurrence.1 ()) := by
            simp [attempt, Role.allows, noTake, equalityMatcher, available]
          simpa [allowed, available, Match.select] using ih (matched.select .read occurrence.1 ()) noTake
        · simp [attempt, Role.allows, noTake, equalityMatcher, available]
      _ = _ := flatMap_replicate_count _ _ _ _

private theorem clause_productions (s : Store (Fin n)) (clause : Clause n) :
    (solve (equalityMatcher n) s (goals clause.asRule) (Match.start (equalityMatcher n))).flatMap
      Match.made =
      List.replicate ((clause.premises.map (occurrenceCount s)).prod) clause.conclusion := by
  change ((solve (equalityMatcher n) s (goals clause.asRule) (Match.start (equalityMatcher n))).map
    Match.made).flatten = _
  rw [show goals clause.asRule = clause.premises.map (Goal.premise .read) ++
    [.determinate (.produce clause.conclusion)] by simp [goals, Clause.asRule]]
  have just := read_outputs s clause.premises clause.conclusion (Match.start (equalityMatcher n)) rfl
  rw [just]
  simp only [Match.start, List.nil_append]
  generalize (clause.premises.map (occurrenceCount s)).prod = amount
  induction amount with
  | zero => rfl
  | succ amount ih => simp [List.replicate_succ, ih]

def firingAnswers (program : List (Clause n)) (s : Store (Fin n)) : List (Fin n) :=
  (firings (equalityMatcher n) (program.map Clause.asRule) s).flatMap (fun firing => firing.2.made)

private theorem countRound_clauses (program : List (Clause n)) (previous : Fin n → ℕ) (key : Fin n) :
    countRound program previous key =
      (((program.filter fun clause => clause.conclusion == key).map
        (fun clause => (clause.premises.map previous).prod)).sum) := by
  unfold countRound eligible
  conv_rhs => rw [← List.map_get_finRange program, List.filter_map, List.map_map]
  rfl

private theorem sum_filter_conditional {A : Type*} (witnesses : List A) (keep : A → Bool) (weight : A → ℕ) :
    ((witnesses.filter keep).map weight).sum =
      (witnesses.map (fun a => if keep a then weight a else 0)).sum := by
  induction witnesses with
  | nil => rfl
  | cons first rest ih =>
    cases kept : keep first <;> simp [kept, ih]

theorem firing_count_eq_table_round (program : List (Clause n)) (s : Store (Fin n)) (key : Fin n) :
    (firingAnswers program s).countP (fun answer => answer == key) =
      countRound program (occurrenceCount s) key := by
  unfold firingAnswers firings
  rw [List.flatMap_assoc, List.flatMap_map, List.countP_flatMap, countRound_clauses, sum_filter_conditional]
  congr 1
  apply List.map_congr_left
  intro clause _
  simp only [Function.comp_def, List.flatMap_map]
  rw [clause_productions, List.countP_replicate]

/-- A reference machine store for each answer-table layer. Publication
is into a separate layer, so a read never sees a new answer from its
own layer. No deduplication occurs, even for equal answer values. -/
def materialized (program : List (Clause n)) : ℕ → Store (Fin n)
  | 0 => ⟨[], 0⟩
  | depth + 1 => Store.makeAll ⟨[], 0⟩ (firingAnswers program (materialized program depth))

private theorem empty_make_count (answers : List (Fin n)) (key : Fin n) :
    occurrenceCount (Store.makeAll ⟨[], 0⟩ answers) key = answers.countP (· == key) := by
  unfold occurrenceCount
  rw [(Store.makeAll_occurrences ⟨[], 0⟩ answers).1, List.nil_append, List.countP_map]
  change (answers.zipIdx 0).countP ((· == key) ∘ Prod.fst) = _
  rw [← List.countP_map, List.zipIdx_map_fst]

theorem materialized_count_eq_table (program : List (Clause n)) (limit : ℕ) (key : Fin n) :
    occurrenceCount (materialized program limit) key = (counts program limit)[key.val]'key.isLt := by
  induction limit generalizing key with
  | zero => simp [materialized, occurrenceCount, counts]
  | succ limit ih =>
    simp only [materialized, empty_make_count, firing_count_eq_table_round, counts, Vector.getElem_ofFn]
    rw [show occurrenceCount (materialized program limit) =
      (fun q => (counts program limit)[q.val]'q.isLt) from funext ih]

theorem materialized_count_eq_derivations (program : List (Clause n)) (limit : ℕ) (key : Fin n) :
    occurrenceCount (materialized program limit) key = (enumerate program limit key).length :=
  (materialized_count_eq_table program limit key).trans (counts_exact program limit key)

theorem materialized_presence_eq_table (program : List (Clause n)) (limit : ℕ) (key : Fin n) :
    0 < occurrenceCount (materialized program limit) key ↔ key ∈ presence program limit := by
  rw [materialized_count_eq_derivations, List.length_pos_iff_exists_mem, presence_exact]
  exact exists_congr (mem_enumerate_iff program limit key)

private def four : List (Clause 2) := [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0]⟩]

theorem two_selectors_give_four_publications : occurrenceCount (materialized four 2) 1 = 4 := by
  rw [materialized_count_eq_table]
  decide +kernel

end Mettapedia.Machines.TIsa.Derivation.AnswerTable
