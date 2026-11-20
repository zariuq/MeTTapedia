import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.AbsorptionBack

/-!
# A program of every positive rule hides how many rows `5` there are: the bound is needed

`static_of_congruent` and `congruent_iff_static` assume programs that leave a constant unused
(`Bounded`). This module shows the assumption cannot be dropped, even for positive programs (equation
guards only, no none query or count query, no collect query).

**Beside any program containing every positive rule, one row `5` and two rows `5` are congruent**
(`absorbing_congruent`; `positive_rules_absorb` for the program of every positive rule, which is a
positive program, and `every_rule_absorbs` for the program of every rule), although they are not
statically equivalent (`not_static_fives`); neither program is bounded (`not_bounded_positiveRules`,
`not_bounded_everyRule`). The candidate (`Absorbing`) relates systems with one program containing every
positive rule whose states are equal, or one row `5` apart (`OneMore`):

* the may-barbs do not count (`mayBarb_oneMore`), and every context keeps the relation;
* a firing at the smaller side is answered at the larger side by the same rule, without its checks,
  taking the extra `5` along (`answer_forward`), and a firing at the larger side by the same rule
  without its checks, with its takes and reads of the extra row turned into tells, making one `5` if
  it kept that row (`answer_backward`); both answers are positive rules, the results are statically
  equivalent, and the larger side is reached through `static_fiveMore`.

A probe that counts the rows `5` and makes a row with a fresh constant, added by a context, is answered
by a positive rule of the program making that constant: there is no fresh constant. Hence
(`bounded_needed`) no theorem "congruent systems with positive programs have statically equivalent
states" holds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves fresh_identity extendState_eq_self)

/-- **A positive program**: every rule of it is positive. -/
def PositiveProgram (P : Program Tm) : Prop := ∀ r ∈ P, Positive r

theorem positiveProgram_positiveRules : PositiveProgram positiveRules := fun _ positive => positive

/-- A firing whose rule is in another program, as a firing of that program: the same rule, opening,
selection and seen sets. -/
def moveFiring {P P' : Program Tm} {a : PUnit.{1}} (f : Firing ℕ E P a) (inside : f.rule ∈ P') :
    Firing ℕ E P' a :=
  ⟨f.rule, inside, f.ext, f.opening, f.selection, f.seen⟩

/-- **The candidate**: one program containing every positive rule at both sides, and states equal or
one row `5` apart. -/
def Absorbing (S T : Sys) : Prop :=
  positiveRules ⊆ S.program ∧ T.program = S.program ∧
    (S.state = T.state ∨ OneMore S.state T.state ∨ OneMore T.state S.state)

/-- A context only adds rules. -/
theorem program_apply (c : Basic Tm ℕ E) (P : Program Tm) (s : State Tm ℕ) :
    P ⊆ (c.apply X (⟨P, s⟩ : Sys)).program := by
  cases c with
  | rows ids label => exact fun _ inside => inside
  | rules added => exact Set.subset_union_left
  | tell equations => exact fun _ inside => inside
  | extend extension => exact fun _ inside => inside

/-- Adding rows keeps one more row `5`, the right side choosing its identities afresh. -/
theorem oneMore_rows {a b : State Tm ℕ} (more : OneMore a b) (ids : Finset ℕ)
    (label : (u : PUnit.{1}) → ℕ → Tm u) (apart : Disjoint ids a.present) (π : Equiv.Perm ℕ)
    (apart' : Disjoint (ids.map π.toEmbedding) b.present) :
    OneMore (addRows a ids (label PUnit.unit))
      (addRows b (ids.map π.toEmbedding) (fun o => label PUnit.unit (π.symm o))) := by
  refine oneMore_addRows more _ _ apart.symm apart'.symm ?_
  rw [Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro o _
  simp

/-- The same, with one more row `5` at the left. -/
theorem oneMore_rows' {a b : State Tm ℕ} (more : OneMore a b) (ids : Finset ℕ)
    (label : (u : PUnit.{1}) → ℕ → Tm u) (apart : Disjoint ids b.present) (π : Equiv.Perm ℕ)
    (apart' : Disjoint (ids.map π.toEmbedding) a.present) :
    OneMore (addRows a (ids.map π.toEmbedding) (fun o => label PUnit.unit (π.symm o)))
      (addRows b ids (label PUnit.unit)) := by
  refine oneMore_addRows more _ _ apart'.symm apart.symm ?_
  rw [Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro o _
  simp

/-- The candidate is closed under contexts, for one named program. -/
theorem absorbing_context_at {P : Program Tm} (sub : positiveRules ⊆ P) {Ss Ts : State Tm ℕ}
    (states : Ss = Ts ∨ OneMore Ss Ts ∨ OneMore Ts Ss) (c : Basic Tm ℕ E)
    (applies : c.Applies (⟨P, Ss⟩ : Sys)) :
    ∃ π : Equiv.Perm ℕ, (c.rename π).Applies (⟨P, Ts⟩ : Sys) ∧
      Absorbing (c.apply X ⟨P, Ss⟩) ((c.rename π).apply X ⟨P, Ts⟩) := by
  rcases states with same | more | more
  · rw [← same]
    refine ⟨1, by rw [Basic.rename_one]; exact applies, ?_⟩
    rw [Basic.rename_one]
    exact ⟨sub.trans (program_apply c P Ss), rfl, Or.inl rfl⟩
  · cases c with
    | rows ids label =>
        obtain ⟨π, apart⟩ := exists_perm_avoid Ts.present ids
        exact ⟨π, apart, sub, rfl, Or.inr (Or.inl (oneMore_rows more ids label applies π apart))⟩
    | rules added =>
        exact ⟨1, Basic.applies_of_ids_empty rfl _, sub.trans Set.subset_union_left, rfl,
          Or.inr (Or.inl more)⟩
    | tell equations =>
        exact ⟨1, Basic.applies_of_ids_empty rfl _, sub, rfl,
          Or.inr (Or.inl (oneMore_tell more (equations PUnit.unit)))⟩
    | extend extension =>
        refine ⟨1, Basic.applies_of_ids_empty rfl _, sub, rfl, Or.inr (Or.inl ?_)⟩
        show OneMore (extendState X E Ss (extension Ss.frame)) (extendState X E Ts (extension Ts.frame))
        rw [extendState_eq_self, extendState_eq_self]
        exact more
  · cases c with
    | rows ids label =>
        obtain ⟨π, apart⟩ := exists_perm_avoid Ts.present ids
        exact ⟨π, apart, sub, rfl, Or.inr (Or.inr (oneMore_rows' more ids label applies π apart))⟩
    | rules added =>
        exact ⟨1, Basic.applies_of_ids_empty rfl _, sub.trans Set.subset_union_left, rfl,
          Or.inr (Or.inr more)⟩
    | tell equations =>
        exact ⟨1, Basic.applies_of_ids_empty rfl _, sub, rfl,
          Or.inr (Or.inr (oneMore_tell more (equations PUnit.unit)))⟩
    | extend extension =>
        refine ⟨1, Basic.applies_of_ids_empty rfl _, sub, rfl, Or.inr (Or.inr ?_)⟩
        show OneMore (extendState X E Ts (extension Ts.frame)) (extendState X E Ss (extension Ss.frame))
        rw [extendState_eq_self, extendState_eq_self]
        exact more

/-- **The candidate is closed under contexts.** -/
theorem absorbing_context {S T : Sys} (related : Absorbing S T) (c : Basic Tm ℕ E)
    (applies : c.Applies S) :
    ∃ π : Equiv.Perm ℕ, (c.rename π).Applies T ∧ Absorbing (c.apply X S) ((c.rename π).apply X T) := by
  obtain ⟨SP, Ss⟩ := S
  obtain ⟨TP, Ts⟩ := T
  obtain ⟨sub, programs, states⟩ := related
  simp only at sub programs states
  rw [programs]
  exact absorbing_context_at sub states c applies

/-- Moves of the candidate are answered up to the congruence, for one named program. -/
theorem absorbing_reduces_at {P : Program Tm} (sub : positiveRules ⊆ P) {Ss Ts : State Tm ℕ}
    (states : Ss = Ts ∨ OneMore Ss Ts ∨ OneMore Ts Ss) {S' : Sys}
    (moved : Reduces X ℕ E ⟨P, Ss⟩ S') :
    ∃ T', Reduces X ℕ E ⟨P, Ts⟩ T' ∧ UpTo X ℕ E (MayBarb X) Absorbing S' T' := by
  obtain ⟨programSame, f, admitted, reached⟩ := moved
  obtain ⟨S'P, S's⟩ := S'
  have shape : (⟨S'P, S's⟩ : Sys) = ⟨P, f.result X Ss⟩ := by
    have reached' : f.result X Ss = S's := reached
    simp only at programSame
    rw [programSame, reached']
  rw [shape]
  -- A system whose program contains every positive rule is related to itself.
  have self : ∀ U : Sys, positiveRules ⊆ U.program → Absorbing U U := fun _ inside =>
    ⟨inside, rfl, Or.inl rfl⟩
  rcases states with same | more | more
  · rw [← same]
    exact ⟨_, reduces_of_admits f admitted, _, _, Congruent.refl _, self _ sub, Congruent.refl _⟩
  · -- The left has one row `5` less: answer at the larger state through `fiveMore`.
    obtain ⟨d, freshD⟩ : ∃ d, d ∉ Ss.present ∪ f.selection.made.toFinset := ⟨_, fresh_identity _⟩
    have dNotPresent : d ∉ Ss.present := fun h => freshD (Finset.mem_union_left _ h)
    have dNotMade : d ∉ f.selection.made := fun h =>
      freshD (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
    obtain ⟨g, positive, admittedG, static⟩ :=
      answer_forward (moveFiring f (Set.mem_univ _)) admitted dNotPresent dNotMade
    have toT : Cong ⟨P, fiveMore Ss d⟩ ⟨P, Ts⟩ :=
      congruent_of_static P (static_fiveMore more dNotPresent)
    obtain ⟨T', movedT, relatedT⟩ :=
      candidate_congruent.reduces toT (reduces_of_admits (moveFiring g (sub positive)) admittedG)
    have result : Cong ⟨P, f.result X Ss⟩ T' :=
      (congruent_of_static P static).trans relatedT
    have programT : T'.program = P := movedT.1
    exact ⟨T', movedT, T', T', result, self T' (programT ▸ sub), Congruent.refl _⟩
  · -- The left has one row `5` more: move there through `fiveMore`, then answer at the smaller.
    obtain ⟨d, freshD⟩ : ∃ d, d ∉ Ts.present := ⟨_, fresh_identity _⟩
    have toFive : Cong ⟨P, Ss⟩ ⟨P, fiveMore Ts d⟩ :=
      (congruent_of_static P (static_fiveMore more freshD)).symm
    obtain ⟨B', movedB, relatedB⟩ := candidate_congruent.reduces toFive (reduces_of_admits f admitted)
    obtain ⟨programB, g, admittedG, reachedB⟩ := movedB
    have reachedB' : g.result X (fiveMore Ts d) = B'.state := reachedB
    obtain ⟨f', positive, admittedF, static⟩ :=
      answer_backward freshD (moveFiring g (Set.mem_univ _)) admittedG
    have shapeB : B' = ⟨P, g.result X (fiveMore Ts d)⟩ := by
      obtain ⟨BP, Bs⟩ := B'
      simp only at programB reachedB'
      rw [programB, reachedB']
    rw [shapeB] at relatedB
    have result : Cong ⟨P, f.result X Ss⟩ ⟨P, (moveFiring f' (sub positive)).result X Ts⟩ :=
      relatedB.trans (congruent_of_static P static).symm
    exact ⟨_, reduces_of_admits (moveFiring f' (sub positive)) admittedF, _, _, result, self _ sub,
      Congruent.refl _⟩

/-- **Moves of the candidate are answered up to the congruence.** -/
theorem absorbing_reduces {S T : Sys} (related : Absorbing S T) {S' : Sys}
    (moved : Reduces X ℕ E S S') :
    ∃ T', Reduces X ℕ E T T' ∧ UpTo X ℕ E (MayBarb X) Absorbing S' T' := by
  obtain ⟨SP, Ss⟩ := S
  obtain ⟨TP, Ts⟩ := T
  obtain ⟨sub, programs, states⟩ := related
  simp only at sub programs states
  rw [programs]
  exact absorbing_reduces_at sub states moved

/-- **The candidate relates only congruent systems.** -/
theorem absorbing_congruent {S T : Sys} (related : Absorbing S T) : Cong S T := by
  refine congruent_of_upTo (R := Absorbing) ?_ ?_ (fun r _ moved => absorbing_reduces r moved)
    (fun r c applies => absorbing_context r c applies) related
  · rintro S T ⟨sub, programs, states⟩
    refine ⟨programs ▸ sub, programs.symm, ?_⟩
    rcases states with same | more | more
    · exact Or.inl same.symm
    · exact Or.inr (Or.inr more)
    · exact Or.inr (Or.inl more)
  · rintro S T ⟨-, -, states⟩ β holds
    rcases states with same | more | more
    · rw [← same]
      exact holds
    · exact (mayBarb_oneMore more β).mp holds
    · exact (mayBarb_oneMore more β).mpr holds

/-! ## One row `5` and two rows `5` -/

/-- One row `5`. -/
def oneFive : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 5⟩

/-- Two rows `5`. -/
def twoFives : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, fun _ => c 5⟩

theorem oneMore_fives : OneMore oneFive twoFives := by
  refine ⟨rfl, ⟨0, Finset.mem_singleton_self 0, rfl⟩, ?_⟩
  show (({0, 1} : Finset ℕ).val.map fun _ => c 5) = c 5 ::ₘ ({0} : Finset ℕ).val.map fun _ => c 5
  rw [Multiset.map_const', Multiset.map_const']
  rfl

/-- **Beside the program of every positive rule, one row `5` and two rows `5` are congruent.** -/
theorem positive_rules_absorb : Cong ⟨positiveRules, oneFive⟩ ⟨positiveRules, twoFives⟩ :=
  absorbing_congruent ⟨fun _ inside => inside, rfl, Or.inr (Or.inl oneMore_fives)⟩

/-- **Beside the program of every rule, one row `5` and two rows `5` are congruent.** -/
theorem every_rule_absorbs : Cong ⟨everyRule, oneFive⟩ ⟨everyRule, twoFives⟩ :=
  absorbing_congruent ⟨Set.subset_univ _, rfl, Or.inr (Or.inl oneMore_fives)⟩

/-- They are not statically equivalent. -/
theorem not_static_fives : ¬ Static oneFive twoFives := by
  intro static
  obtain ⟨π, present, -⟩ := present_of_static (solvable_nil rfl) static
  have cards := congrArg Finset.card present
  rw [Finset.card_map] at cards
  exact absurd cards (by decide)

/-- **The program of every positive rule mentions every constant.** -/
theorem not_bounded_positiveRules : ¬ Bounded positiveRules := by
  rintro ⟨B, bound⟩
  have small := bound ⟨PUnit.unit, ⟨[c B], [], [], [], []⟩, []⟩ (positive_of_nil rfl rfl) (c B)
    (by simp [Rule.terms]) B rfl
  omega

/-- **The program of every rule mentions every constant.** -/
theorem not_bounded_everyRule : ¬ Bounded everyRule := fun bounded =>
  not_bounded_positiveRules (let ⟨B, bound⟩ := bounded; ⟨B, fun r _ => bound r (Set.mem_univ r)⟩)

/-- **The bound is needed, even for positive programs**: without it, congruent systems need not have
statically equivalent states, and congruence of states beside one positive program is not the static
equivalence. -/
theorem bounded_needed :
    (¬ ∀ (P P' : Program Tm) (s t : State Tm ℕ), PositiveProgram P → PositiveProgram P' →
        Cong ⟨P, s⟩ ⟨P', t⟩ → Static s t) ∧
      ¬ ∀ s t : State Tm ℕ, Cong ⟨positiveRules, s⟩ ⟨positiveRules, t⟩ ↔ Static s t :=
  ⟨fun claim => not_static_fives (claim _ _ _ _ positiveProgram_positiveRules
      positiveProgram_positiveRules positive_rules_absorb),
    fun claim => not_static_fives ((claim _ _).mp positive_rules_absorb)⟩

#print axioms positiveProgram_positiveRules
#print axioms program_apply
#print axioms oneMore_rows
#print axioms oneMore_rows'
#print axioms absorbing_context_at
#print axioms absorbing_context
#print axioms absorbing_reduces_at
#print axioms absorbing_reduces
#print axioms absorbing_congruent
#print axioms oneMore_fives
#print axioms positive_rules_absorb
#print axioms every_rule_absorbs
#print axioms not_static_fives
#print axioms not_bounded_positiveRules
#print axioms not_bounded_everyRule
#print axioms bounded_needed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
