import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.StepConcepts

/-!
# The boundary of the finitary formulas: a type they cannot denote

On the ground first-order step, take the program with one rule, which takes one `T` (`takesT`,
`countDown`), and observe the knowledge and the bag of labels (`ProgramAdequacy.storeView`, the
observation set of `ProgramAdequacy.ground_program_adequacy`). The program is finite, so the types
of the finitary formulas are exactly the classes closed under bisimilarity
(`StepConcepts.program_isConcept_iff_bisimClosed`).

* **The chain** (`Chain n k`): stores of exactly `n` copies of `T` that have learned `k` equations
  `T = T`. Every successor of a store of the chain with `n + 1` copies is in the chain with `n`
  copies and `k + 1` equations (`succ_chain`), and there is one (`exists_succ`); with no copy there
  is none (`no_succ_of_empty`).
* **What the finitary formulas can see along the chain** (`eventually_constant_of_atoms`): for
  every formula and every `k`, the truth of the formula on the chain with `n` copies and `k`
  equations is constant for all large `n`, whenever each atom is. Conjunction and negation keep
  eventual constancy; the diamond shifts it by one copy. Observing the store
  (`eventually_constant`), an atom of the bag names one bag, so it is eventually false, and an atom
  of the knowledge is constant along the chain.
* **The even counts** (`evenCount`): the stores holding an even number of `T`. They form a type
  (`evenCount_isConcept`), closed under bisimilarity, denoted by an infinitary formula
  (`evenCount_iformula`), and **denoted by no finitary formula** (`evenCount_not_denoted`): along
  the chain they alternate. Equivalently, no finite list of formulas decides them
  (`evenCount_not_finitelyDetermined`).
* **The step does the counting** (`dynamic_parity_boundary`). Observing the knowledge alone
  (`knowledgeView`), no atom sees the bag, and the formulas count steps: `n` steps are possible
  exactly when the reach, the copies of `T` under consistent knowledge, is at least `n`
  (`sat_after_iff_reach`). So every single reach is denoted by a finitary formula
  (`reach_denoted`), the even reaches are a type (`evenReach_isConcept`), and no finitary formula
  denotes them (`evenReach_not_denoted`). Adequacy holds here too
  (`countingKnowledge_isConcept_iff`).

So the boundary is exact: a type of the finitary formulas is denoted by one of them exactly when
finitely many formulas decide it (`StepConcepts.denoted_iff_finitelyDetermined`), and the even
counts are a type that no finite list decides, even when every single count is decided.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ParityBoundary

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open NamesOnTheStep NamesOnTheStep.IssuingControls
open ProgramAdequacy StepSpan InfinitaryAdequacy ObserverConcepts StepConcepts

/-- The rule that takes one `T`. -/
def takesT : RuleInstance Expr := ⟨[factT], [], [], [], []⟩

/-- **The program**: take one `T`. -/
abbrev countDown := program ground (Prod.fst : Occ → Expr) ({takesT} : Set (RuleInstance Expr))

/-- The step under it, observing the knowledge and the bag of labels. -/
abbrev counting := stepSystem countDown storeView

/-- The bag of labels of a store. -/
def bag (C : Conf) : Multiset Expr := C.present.val.map Prod.fst

theorem bag_eq_replicate_iff (F : Finset Occ) (n : ℕ) :
    F.val.map Prod.fst = Multiset.replicate n factT ↔ F.card = n ∧ ∀ o ∈ F, o.1 = factT := by
  rw [Multiset.eq_replicate, Multiset.card_map, Finset.card_val]
  refine and_congr_right fun _ => ⟨fun all o member => ?_, fun all b member => ?_⟩
  · exact all o.1 (Multiset.mem_map_of_mem _ (Finset.mem_val.mpr member))
  · obtain ⟨o, inside, rfl⟩ := Multiset.mem_map.mp member
    exact all o (Finset.mem_val.mp inside)

/-- **The chain**: exactly `n` copies of `T`, with `k` equations `T = T` learned. -/
def Chain (n k : ℕ) (C : Conf) : Prop :=
  bag C = Multiset.replicate n factT ∧ C.equations = List.replicate k (factT, factT)

/-! ## The step along the chain -/

theorem take_problem (C : Conf) (o : Occ) :
    (⟨[o], [], []⟩ : Selection Occ).problem Prod.fst takesT C = C.equations ++ [(factT, o.1)] := by
  simp [Selection.problem, Selection.equations, takesT]

theorem take_result (C : Conf) (o : Occ) :
    (⟨[o], [], []⟩ : Selection Occ).result Prod.fst takesT C =
      ⟨C.equations ++ [(factT, o.1)], C.present \ {o}⟩ := by
  simp only [Selection.result, take_problem, fire, Selection.commit]
  simp

/-- **Every successor of a store of the chain is a store of the chain**, with one copy fewer and
one more equation. -/
theorem succ_chain {n k : ℕ} {C C' : Conf} (chain : Chain n k C) (step : Succ countDown C C') :
    ∃ m, n = m + 1 ∧ Chain m (k + 1) C' := by
  obtain ⟨rule, ⟨taken, read, made⟩, member, valid, rfl⟩ :=
    (program_succ_iff ground Prod.fst _ C C').mp step
  rw [Set.mem_singleton_iff] at member
  subst member
  obtain ⟨o, takenEq, labelled⟩ := match_one (takes_match valid)
  have readNil : read = [] := List.length_eq_zero_iff.mp valid.read_length.symm
  have madeNil : made = [] := List.map_eq_nil_iff.mp valid.outputs
  subst takenEq readNil madeNil
  have present : o ∈ C.present := taken_present valid (List.mem_singleton_self o)
  obtain ⟨card, labels⟩ := (bag_eq_replicate_iff C.present n).mp chain.1
  have positive : 0 < n := card ▸ Finset.card_pos.mpr ⟨o, present⟩
  refine ⟨n - 1, by omega, ?_, ?_⟩
  · rw [take_result]
    refine (bag_eq_replicate_iff _ _).mpr ⟨?_, fun o' member => labels o' (Finset.mem_sdiff.mp member).1⟩
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr present), card,
      Finset.card_singleton]
  · rw [take_result]
    show C.equations ++ [(factT, o.1)] = _
    rw [chain.2, ← labelled, List.replicate_succ']

/-- With no copy there is no successor. -/
theorem no_succ_of_empty {k : ℕ} {C C' : Conf} (chain : Chain 0 k C) : ¬ Succ countDown C C' := by
  intro step
  obtain ⟨m, impossible, _⟩ := succ_chain chain step
  omega

/-- **A store of the chain with a copy has a successor.** -/
theorem exists_succ {m k : ℕ} {C : Conf} (chain : Chain (m + 1) k C) : ∃ C', Succ countDown C C' := by
  obtain ⟨card, labels⟩ := (bag_eq_replicate_iff C.present (m + 1)).mp chain.1
  obtain ⟨o, present⟩ := Finset.card_pos.mp (show 0 < C.present.card by omega)
  have valid : (⟨[o], [], []⟩ : Selection Occ).Valid ground Prod.fst takesT C := by
    refine ⟨List.nodup_singleton o, List.nodup_nil, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · exact ⟨by simpa [Selection.commit] using present, by simp [Selection.commit],
        by simp [Selection.commit], by simp [Selection.commit],
        fun _ member => by simp [Selection.commit] at member⟩
    · refine ⟨(), fun e member => ?_⟩
      rw [take_problem, chain.2] at member
      rcases List.mem_append.mp member with learned | single
      · rw [List.eq_of_mem_replicate learned]
        rfl
      · rw [List.mem_singleton.mp single]
        exact (labels o present).symm
    · intro check member
      simp [takesT] at member
  exact ⟨_, (program_succ_iff ground Prod.fst _ C _).mpr
    ⟨takesT, ⟨[o], [], []⟩, Set.mem_singleton takesT, valid, rfl⟩⟩

/-! ## What the finitary formulas see along the chain -/

/-- **Every finitary formula is eventually constant along the chain**, for each amount of learned
knowledge, whenever every atom is. -/
theorem eventually_constant_of_atoms {Atom : Type} (observes : Atom → Conf → Prop)
    (atoms : ∀ (a : Atom) (k : ℕ), ∃ N, ∃ b : Prop, ∀ n, N ≤ n → ∀ C, Chain n k C →
      (observes a C ↔ b))
    (φ : Formula (stepSystem countDown observes).Atom (stepSystem countDown observes).Label) :
    ∀ k, ∃ N, ∃ b : Prop, ∀ n, N ≤ n → ∀ C, Chain n k C →
      ((stepSystem countDown observes).sat φ C ↔ b) := by
  induction φ with
  | top => exact fun _ => ⟨0, True, fun _ _ _ _ => Iff.rfl⟩
  | atom a => exact atoms a
  | conj left right leftConstant rightConstant =>
      intro k
      obtain ⟨N₁, b₁, first⟩ := leftConstant k
      obtain ⟨N₂, b₂, second⟩ := rightConstant k
      exact ⟨max N₁ N₂, b₁ ∧ b₂, fun n large C chain =>
        and_congr (first n (le_of_max_le_left large) C chain)
          (second n (le_of_max_le_right large) C chain)⟩
  | neg inner constant =>
      intro k
      obtain ⟨N, b, holds⟩ := constant k
      exact ⟨N, ¬ b, fun n large C chain => not_congr (holds n large C chain)⟩
  | dia label inner constant =>
      intro k
      obtain ⟨N, b, holds⟩ := constant (k + 1)
      refine ⟨N + 1, b, fun n large C chain => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      constructor
      · rintro ⟨C', step, there⟩
        obtain ⟨m', same, chain'⟩ := succ_chain chain step
        exact (holds m' (by omega) C' chain').mp there
      · intro hb
        obtain ⟨C', step⟩ := exists_succ chain
        obtain ⟨m', same, chain'⟩ := succ_chain chain step
        exact ⟨C', step, (holds m' (by omega) C' chain').mpr hb⟩

/-- Along the chain, an atom of the bag is eventually false and an atom of the knowledge is
constant. -/
theorem storeView_atoms (a : Multiset Expr ⊕ EquationStore Expr) (k : ℕ) :
    ∃ N, ∃ b : Prop, ∀ n, N ≤ n → ∀ C, Chain n k C → (storeView a C ↔ b) := by
  cases a with
  | inl B =>
      refine ⟨Multiset.card B + 1, False, fun n large C chain => ?_⟩
      show bag C = B ↔ False
      rw [chain.1]
      refine iff_false_intro fun same => ?_
      have cards := congrArg Multiset.card same
      rw [Multiset.card_replicate] at cards
      omega
  | inr K =>
      refine ⟨0, List.replicate k (factT, factT) = K, fun n _ C chain => ?_⟩
      show C.equations = K ↔ _
      rw [chain.2]

/-- **Every finitary formula is eventually constant along the chain**, observing the knowledge and
the bag. -/
theorem eventually_constant (φ : Formula counting.Atom counting.Label) :
    ∀ k, ∃ N, ∃ b : Prop, ∀ n, N ≤ n → ∀ C, Chain n k C → (counting.sat φ C ↔ b) :=
  eventually_constant_of_atoms storeView storeView_atoms φ

/-! ## The even counts -/

/-- **The even counts**: the stores holding an even number of `T`. -/
def evenCount : Set Conf := {C | Even ((bag C).count factT)}

/-- **The even counts are a type of the finitary formulas**: logically equivalent stores have the
same bag. -/
theorem evenCount_isConcept : IsConcept (Apart (formulas counting)) evenCount := by
  refine (isConcept_formulas_iff counting evenCount).mpr ?_
  intro C inside D equivalent
  have sameBag : bag D = bag C := (equivalent (.atom (.inl (bag C)))).mp rfl
  show Even ((bag D).count factT)
  rw [sameBag]
  exact inside

/-- The even counts are closed under bisimilarity. -/
theorem evenCount_bisimClosed : BisimClosed counting evenCount :=
  bisimClosed_of_isConcept counting evenCount_isConcept

/-- Under this finite program the types are exactly the classes closed under bisimilarity. -/
theorem counting_isConcept_iff (X : Set Conf) :
    IsConcept (Apart (formulas counting)) X ↔ BisimClosed counting X :=
  program_isConcept_iff_bisimClosed ground Prod.fst occSupply (Set.finite_singleton takesT)
    storeView storeView_invariant X

/-- **The even counts are denoted by an infinitary formula.** -/
theorem evenCount_iformula :
    ∃ φ : IFormula counting.Atom counting.Label, ∀ C, isat counting φ C ↔ C ∈ evenCount :=
  exists_iformula_of_bisimClosed counting evenCount_bisimClosed

/-- `n` copies of `T`, with no knowledge. -/
def copies (n : ℕ) : Conf := ⟨[], ((List.range n).map fun i => (factT, i)).toFinset⟩

theorem copies_nodup (n : ℕ) : ((List.range n).map fun i => ((factT, i) : Occ)).Nodup :=
  (List.nodup_range).map fun _ _ same => by simpa using congrArg Prod.snd same

theorem copies_chain (n : ℕ) : Chain n 0 (copies n) := by
  refine ⟨(bag_eq_replicate_iff _ n).mpr ⟨?_, ?_⟩, rfl⟩
  · show ((List.range n).map fun i => ((factT, i) : Occ)).toFinset.card = n
    rw [List.toFinset_card_of_nodup (copies_nodup n)]
    simp
  · intro o member
    simp only [copies, List.mem_toFinset, List.mem_map] at member
    obtain ⟨i, _, rfl⟩ := member
    rfl

theorem copies_mem_evenCount (n : ℕ) : copies n ∈ evenCount ↔ Even n := by
  show Even ((bag (copies n)).count factT) ↔ Even n
  rw [(copies_chain n).1, Multiset.count_replicate_self]

/-- **The program runs**: every store of copies with a copy has a successor. -/
theorem copies_step (n : ℕ) : ∃ C', Succ countDown (copies (n + 1)) C' :=
  exists_succ (copies_chain (n + 1))

/-- **No finitary formula denotes the even counts.** -/
theorem evenCount_not_denoted :
    ¬ ∃ φ : Formula counting.Atom counting.Label, ∀ C, counting.sat φ C ↔ C ∈ evenCount := by
  rintro ⟨φ, denotes⟩
  obtain ⟨N, b, constant⟩ := eventually_constant φ 0
  have atN : Even N ↔ b :=
    (copies_mem_evenCount N).symm.trans ((denotes _).symm.trans (constant N le_rfl _ (copies_chain N)))
  have atNext : Even (N + 1) ↔ b :=
    (copies_mem_evenCount (N + 1)).symm.trans
      ((denotes _).symm.trans (constant (N + 1) (Nat.le_succ N) _ (copies_chain (N + 1))))
  exact iff_not_self ((atN.trans atNext.symm).trans Nat.even_add_one)

/-- **No finite list of formulas decides the even counts.** -/
theorem evenCount_not_finitelyDetermined :
    ¬ ∃ F : List (Formula counting.Atom counting.Label),
      ∀ C ∈ evenCount, ∀ D, (∀ φ ∈ F, counting.sat φ C ↔ counting.sat φ D) → D ∈ evenCount :=
  fun determined => evenCount_not_denoted ((denoted_iff_finitelyDetermined counting _).mpr determined)

/-- **The boundary on the step**: under a finite program, a type of the finitary formulas that no
finitary formula denotes and an infinitary formula does. -/
theorem parity_boundary :
    IsConcept (Apart (formulas counting)) evenCount ∧ BisimClosed counting evenCount ∧
      (¬ ∃ φ : Formula counting.Atom counting.Label, ∀ C, counting.sat φ C ↔ C ∈ evenCount) ∧
      ∃ φ : IFormula counting.Atom counting.Label, ∀ C, isat counting φ C ↔ C ∈ evenCount :=
  ⟨evenCount_isConcept, evenCount_bisimClosed, evenCount_not_denoted, evenCount_iformula⟩

/-! ## Observing the knowledge alone: the step does the counting -/

/-- **Observing the knowledge alone.** -/
def knowledgeView (K : EquationStore Expr) (C : Conf) : Prop := C.equations = K

/-- The step under the program, observing the knowledge alone. -/
abbrev countingKnowledge := stepSystem countDown knowledgeView

/-- Ground knowledge is consistent when every equation is between identical terms. -/
def Consistent (C : Conf) : Prop := ∀ e ∈ C.equations, e.1 = e.2

/-- The copies of `T` in a store. -/
def copiesOf (C : Conf) : Finset Occ := C.present.filter fun o => o.1 = factT

open Classical in
/-- **How far a store can run**: its copies of `T` when its knowledge is consistent, else none. -/
noncomputable def reach (C : Conf) : ℕ := if Consistent C then (copiesOf C).card else 0

theorem reach_of_consistent {C : Conf} (consistent : Consistent C) :
    reach C = (copiesOf C).card := by
  unfold reach
  exact if_pos consistent

theorem reach_of_not_consistent {C : Conf} (inconsistent : ¬ Consistent C) : reach C = 0 := by
  unfold reach
  exact if_neg inconsistent

/-- **Every step uses up one copy of `T`.** -/
theorem succ_reach {C C' : Conf} (step : Succ countDown C C') :
    ∃ m, reach C = m + 1 ∧ reach C' = m := by
  obtain ⟨rule, ⟨taken, read, made⟩, member, valid, rfl⟩ :=
    (program_succ_iff ground Prod.fst _ C C').mp step
  rw [Set.mem_singleton_iff] at member
  subst member
  obtain ⟨o, takenEq, labelled⟩ := match_one (takes_match valid)
  have readNil : read = [] := List.length_eq_zero_iff.mp valid.read_length.symm
  have madeNil : made = [] := List.map_eq_nil_iff.mp valid.outputs
  subst takenEq readNil madeNil
  have present : o ∈ C.present := taken_present valid (List.mem_singleton_self o)
  obtain ⟨_, solved⟩ := valid.consistent
  have learned : ∀ e ∈ C.equations ++ [(factT, o.1)], e.1 = e.2 := by
    intro e member
    rw [← take_problem C o] at member
    exact solved e member
  have consistent : Consistent C := fun e member => learned e (List.mem_append_left _ member)
  have copy : o ∈ copiesOf C := Finset.mem_filter.mpr ⟨present, labelled.symm⟩
  have after : copiesOf ⟨C.equations ++ [(factT, o.1)], C.present \ {o}⟩ = (copiesOf C).erase o := by
    ext x
    simp only [copiesOf, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton,
      Finset.mem_erase]
    tauto
  have positive := Finset.card_pos.mpr ⟨o, copy⟩
  refine ⟨(copiesOf C).card - 1, ?_, ?_⟩
  · rw [reach_of_consistent consistent]
    omega
  · rw [take_result, reach_of_consistent (C := ⟨C.equations ++ [(factT, o.1)], C.present \ {o}⟩)
      learned, after, Finset.card_erase_of_mem copy]

/-- **A store that can still run has a successor.** -/
theorem exists_succ_of_reach {C : Conf} {m : ℕ} (positive : reach C = m + 1) :
    ∃ C', Succ countDown C C' := by
  by_cases consistent : Consistent C
  · rw [reach_of_consistent consistent] at positive
    obtain ⟨o, copy⟩ := Finset.card_pos.mp (show 0 < (copiesOf C).card by omega)
    obtain ⟨present, labelled⟩ := Finset.mem_filter.mp copy
    have valid : (⟨[o], [], []⟩ : Selection Occ).Valid ground Prod.fst takesT C := by
      refine ⟨List.nodup_singleton o, List.nodup_nil, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · exact ⟨by simpa [Selection.commit] using present, by simp [Selection.commit],
          by simp [Selection.commit], by simp [Selection.commit],
          fun _ member => by simp [Selection.commit] at member⟩
      · refine ⟨(), fun e member => ?_⟩
        rw [take_problem] at member
        rcases List.mem_append.mp member with known | single
        · exact consistent e known
        · rw [List.mem_singleton.mp single]
          exact labelled.symm
      · intro check member
        simp [takesT] at member
    exact ⟨_, (program_succ_iff ground Prod.fst _ C _).mpr
      ⟨takesT, ⟨[o], [], []⟩, Set.mem_singleton takesT, valid, rfl⟩⟩
  · rw [reach_of_not_consistent consistent] at positive
    omega

/-- **The finitary formulas can count steps**: `n` steps are possible exactly when the reach is at
least `n`. -/
theorem sat_after_iff_reach (n : ℕ) (C : Conf) :
    countingKnowledge.sat (Formula.after (List.replicate n ()) .top) C ↔ n ≤ reach C := by
  induction n generalizing C with
  | zero => exact iff_of_true trivial (Nat.zero_le _)
  | succ n ih =>
      show (∃ C', Succ countDown C C' ∧
          countingKnowledge.sat (Formula.after (List.replicate n ()) .top) C') ↔ n + 1 ≤ reach C
      constructor
      · rintro ⟨C', step, holds⟩
        obtain ⟨m, before, after⟩ := succ_reach step
        have := (ih C').mp holds
        omega
      · intro enough
        obtain ⟨C', step⟩ := exists_succ_of_reach (C := C) (m := reach C - 1) (by omega)
        obtain ⟨m, before, after⟩ := succ_reach step
        exact ⟨C', step, (ih C').mpr (by omega)⟩

/-- **Every single reach is denoted by a finitary formula**: `n` steps and not `n + 1`. -/
theorem reach_denoted (n : ℕ) :
    ∃ φ : Formula countingKnowledge.Atom countingKnowledge.Label,
      ∀ C, countingKnowledge.sat φ C ↔ reach C = n := by
  refine ⟨.conj (Formula.after (List.replicate n ()) .top)
    (.neg (Formula.after (List.replicate (n + 1) ()) .top)), fun C => ?_⟩
  have first := sat_after_iff_reach n C
  have second := sat_after_iff_reach (n + 1) C
  constructor
  · rintro ⟨atLeast, notMore⟩
    have lower := first.mp atLeast
    have upper : ¬ (n + 1 ≤ reach C) := fun more => notMore (second.mpr more)
    omega
  · intro equal
    exact ⟨first.mpr equal.ge, fun more => by have := second.mp more; omega⟩

/-- Logically equivalent stores have the same reach. -/
theorem reach_eq_of_equivalent {C D : Conf} (equivalent : countingKnowledge.LogicallyEquivalent C D) :
    reach C = reach D :=
  le_antisymm
    ((sat_after_iff_reach _ D).mp ((equivalent _).mp ((sat_after_iff_reach _ C).mpr le_rfl)))
    ((sat_after_iff_reach _ C).mp ((equivalent _).mpr ((sat_after_iff_reach _ D).mpr le_rfl)))

/-- **The even reaches**: the stores that can run an even number of steps. -/
def evenReach : Set Conf := {C | Even (reach C)}

/-- **The even reaches are a type of the finitary formulas, observing the knowledge alone.** -/
theorem evenReach_isConcept : IsConcept (Apart (formulas countingKnowledge)) evenReach := by
  refine (isConcept_formulas_iff countingKnowledge evenReach).mpr ?_
  intro C inside D equivalent
  show Even (reach D)
  rw [← reach_eq_of_equivalent equivalent]
  exact inside

theorem reach_copies (n : ℕ) : reach (copies n) = n := by
  have consistent : Consistent (copies n) := fun _ member => absurd member List.not_mem_nil
  rw [reach_of_consistent consistent]
  obtain ⟨card, labels⟩ := (bag_eq_replicate_iff (copies n).present n).mp (copies_chain n).1
  have all : copiesOf (copies n) = (copies n).present := Finset.filter_true_of_mem labels
  rw [all, card]

/-- **No finitary formula denotes the even reaches**, though every single reach is denoted. -/
theorem evenReach_not_denoted :
    ¬ ∃ φ : Formula countingKnowledge.Atom countingKnowledge.Label,
      ∀ C, countingKnowledge.sat φ C ↔ C ∈ evenReach := by
  rintro ⟨φ, denotes⟩
  obtain ⟨N, b, constant⟩ := eventually_constant_of_atoms knowledgeView
    (fun K k => ⟨0, List.replicate k (factT, factT) = K, fun _ _ C chain => by
      show C.equations = K ↔ _
      rw [chain.2]⟩) φ 0
  have member : ∀ n, copies n ∈ evenReach ↔ Even n := fun n => by
    show Even (reach (copies n)) ↔ Even n
    rw [reach_copies]
  have atN : Even N ↔ b :=
    (member N).symm.trans ((denotes _).symm.trans (constant N le_rfl _ (copies_chain N)))
  have atNext : Even (N + 1) ↔ b :=
    (member (N + 1)).symm.trans
      ((denotes _).symm.trans (constant (N + 1) (Nat.le_succ N) _ (copies_chain (N + 1))))
  exact iff_not_self ((atN.trans atNext.symm).trans Nat.even_add_one)

/-- **The boundary, with the step doing the counting**: observing the knowledge alone, under a
finite program, every single reach is a finitary type, the even reaches are a type, and no
finitary formula denotes them. -/
theorem dynamic_parity_boundary :
    (∀ n, ∃ φ : Formula countingKnowledge.Atom countingKnowledge.Label,
        ∀ C, countingKnowledge.sat φ C ↔ reach C = n) ∧
      IsConcept (Apart (formulas countingKnowledge)) evenReach ∧
      ¬ ∃ φ : Formula countingKnowledge.Atom countingKnowledge.Label,
        ∀ C, countingKnowledge.sat φ C ↔ C ∈ evenReach :=
  ⟨reach_denoted, evenReach_isConcept, evenReach_not_denoted⟩

/-- Adequacy holds for it: the program is finite and the knowledge is invariant under renaming. -/
theorem countingKnowledge_isConcept_iff (X : Set Conf) :
    IsConcept (Apart (formulas countingKnowledge)) X ↔ BisimClosed countingKnowledge X :=
  program_isConcept_iff_bisimClosed ground Prod.fst occSupply (Set.finite_singleton takesT)
    knowledgeView (fun _ _ _ _ => Iff.rfl) X

#print axioms succ_chain
#print axioms no_succ_of_empty
#print axioms exists_succ
#print axioms eventually_constant
#print axioms evenCount_isConcept
#print axioms counting_isConcept_iff
#print axioms evenCount_iformula
#print axioms copies_chain
#print axioms copies_step
#print axioms evenCount_not_denoted
#print axioms evenCount_not_finitelyDetermined
#print axioms parity_boundary
#print axioms eventually_constant_of_atoms
#print axioms succ_reach
#print axioms exists_succ_of_reach
#print axioms sat_after_iff_reach
#print axioms reach_denoted
#print axioms evenReach_isConcept
#print axioms reach_copies
#print axioms evenReach_not_denoted
#print axioms dynamic_parity_boundary
#print axioms countingKnowledge_isConcept_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ParityBoundary
