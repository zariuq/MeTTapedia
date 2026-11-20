import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.OneLetterChain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ParityBoundary

/-!
# The ladder on the step: finitary ⊊ fixed-point ⊊ infinitary

On the ground first-order step under the program "take one `T`" (`ParityBoundary.countDown`), with
the knowledge observed (`ParityBoundary.countingKnowledge`), the three logics are strictly ordered,
each inclusion with its witness.

* **The step counts down a chain** (`succ_form`, `succ_length`): every firing takes one present
  occurrence and learns one equation. A store whose knowledge is at least `J` equations long is
  related to its reach on the one-letter chain, and the relation is a simulation both ways
  (`longRelated_forth`, `longRelated_back`). So **on long stores a fixed-point formula reads the
  chain** (`holds_iff_chain`): when the knowledge is longer than every atom the formula names, the
  formula holds exactly when it holds on the chain at the store's reach, its atoms read as empty.
* **Finitary ⊊ fixed-point** (`evenReachFormula_holds`, with `ParityBoundary.evenReach_not_denoted`):
  the even reaches are denoted by the one least fixed point `μX. [·]⊥ ∨ ⟨·⟩⟨·⟩X`, with no atom, and by
  no finitary formula.
* **Fixed-point ⊊ infinitary** (`squareReach_not_fixDenoted`, `squareReach_iformula`): the stores
  whose reach is a perfect square are a type, denoted by an infinitary formula, and by no fixed-point
  formula: on long stores such a formula would denote the squares on the chain
  (`OneLetterChain.squares_not_denoted`).
* **Exactly which classes of reaches** (`reachClass_fixDenoted_iff`): a class of stores given by
  their reach is denoted by a fixed-point formula exactly when its set of reaches is ultimately
  periodic (`OneLetterChain.denoted_iff_periodic`).
* `ladder` collects the inclusions and both witnesses.

**Where the counting comes from.** With the bag of labels observed as well
(`ParityBoundary.counting`), the even counts are **not** denoted by any fixed-point formula
(`evenCount_not_fixDenoted`): a store with inconsistent knowledge cannot fire, so on it a formula
sees only its finitely many atoms, and two dead stores whose bags are longer than every bag the
formula names, one even and one odd, are related by a simulation both ways. On consistent stores the
reach is the number of copies of `T` (`ParityBoundary.reach_of_consistent`), and there the least
fixed point above counts them. So a fixed point counts what the step can unfold, and nothing that the
step leaves still.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Ladder

open Set
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary (fixedPointsPositive)
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open NamesOnTheStep NamesOnTheStep.IssuingControls
open ProgramAdequacy StepSpan InfinitaryAdequacy
open Distinctions.ObserverConcepts Distinctions.StepConcepts Distinctions.ParityBoundary
open FixpointTypes OneLetterChain

/-! ## The firings of "take one `T`" -/

/-- **Every firing takes one present occurrence and learns one equation.** -/
theorem succ_form {C C' : Conf} (step : Succ countDown C C') :
    ∃ o ∈ C.present, C' = ⟨C.equations ++ [(factT, o.1)], C.present \ {o}⟩ := by
  obtain ⟨rule, ⟨taken, read, made⟩, member, valid, rfl⟩ :=
    (program_succ_iff ground Prod.fst _ C C').mp step
  rw [Set.mem_singleton_iff] at member
  subst member
  obtain ⟨o, takenEq, -⟩ := match_one (takes_match valid)
  have readNil : read = [] := List.length_eq_zero_iff.mp valid.read_length.symm
  have madeNil : made = [] := List.map_eq_nil_iff.mp valid.outputs
  subst takenEq readNil madeNil
  exact ⟨o, taken_present valid (List.mem_singleton_self o), take_result C o⟩

theorem succ_length {C C' : Conf} (step : Succ countDown C C') :
    C'.equations.length = C.equations.length + 1 := by
  obtain ⟨o, -, rfl⟩ := succ_form step
  simp

/-! ## Long stores read the chain -/

/-- **A store and its reach**, for stores whose knowledge is at least `J` equations long. -/
def LongRelated (J : ℕ) (C : Conf) (m : ℕ) : Prop := reach C = m ∧ J ≤ C.equations.length

theorem longRelated_forth (J : ℕ) :
    IsSimulation (ltsOf countingKnowledge) (chain ()) (LongRelated J) := by
  rintro C m ⟨reached, long⟩ action C' step
  obtain ⟨m', before, after⟩ := succ_reach step
  refine ⟨m', ⟨rfl, by omega⟩, after, ?_⟩
  rw [succ_length step]
  omega

theorem longRelated_back (J : ℕ) :
    IsSimulation (chain ()) (ltsOf countingKnowledge) fun m C => LongRelated J C m := by
  rintro m C ⟨reached, long⟩ action m' ⟨-, rfl⟩
  obtain ⟨C', step⟩ := exists_succ_of_reach (C := C) (m := m') reached
  obtain ⟨m'', before, after⟩ := succ_reach step
  refine ⟨C', step, by omega, ?_⟩
  rw [succ_length step]
  omega

/-- **On long stores a fixed-point formula reads the chain**: when the knowledge is longer than every
atom the formula names, the formula holds exactly when it holds on the chain at the store's reach,
its atoms read as empty. -/
theorem holds_iff_chain (ψ : FixFormula countingKnowledge) (J : ℕ)
    (short : ∀ i, (ψ.atoms i).length < J) (C : Conf) (long : J ≤ C.equations.length) :
    ψ.Holds C ↔ satisfies (chain ()) (fun _ => ∅) ψ.body (reach C) := by
  refine satisfies_iff_of_bisimulation (longRelated_forth J) (longRelated_back J) ψ.body ψ.positive
    (sourceEnv := atomEnv countingKnowledge ψ.atoms) (targetEnv := fun _ => ∅)
    (fun index D m related => iff_of_false (fun same => ?_) (fun outside => outside)) ⟨rfl, long⟩
  have lengths := congrArg List.length (show D.equations = ψ.atoms index from same)
  have := short index
  have := related.2
  omega

/-! ## Finitary ⊊ fixed-point: the even reaches -/

/-- `[·]⊥ ∨ ⟨·⟩⟨·⟩X`. -/
def evenBody : Formula Unit 1 := .disj (.box () .ff) (.diamond () (.diamond () (.var 0)))

/-- **`μX. [·]⊥ ∨ ⟨·⟩⟨·⟩X`**: the run stops after an even number of steps. -/
def evenFormula : Formula Unit 0 := .mu evenBody

theorem evenFormula_positive : fixedPointsPositive evenFormula = true := by rfl

/-- On the chain it denotes the even numbers. -/
theorem evenFormula_chain (m : ℕ) : satisfies (chain ()) (fun _ => ∅) evenFormula m ↔ Even m := by
  constructor
  · intro holds
    refine holds {m | Even m} fun t body => ?_
    rcases body with dead | ⟨t', ⟨-, rfl⟩, t'', ⟨-, rfl⟩, even⟩
    · cases t with
      | zero => exact ⟨0, rfl⟩
      | succ t => exact (dead t ⟨rfl, rfl⟩).elim
    · obtain ⟨r, half⟩ : Even t'' := even
      exact ⟨r + 1, by omega⟩
  · rintro ⟨k, rfl⟩ X closed
    induction k with
    | zero => exact closed 0 (Or.inl fun _ ⟨_, impossible⟩ => by omega)
    | succ k ih =>
        exact closed (k + 1 + (k + 1))
          (Or.inr ⟨k + 1 + k, ⟨rfl, by omega⟩, k + k, ⟨rfl, by omega⟩, ih⟩)

/-- **The even reaches by one least fixed point**, with no atom. -/
def evenReachFormula : FixFormula countingKnowledge where
  arity := 0
  body := evenFormula
  atoms := Fin.elim0
  positive := evenFormula_positive

theorem evenReachFormula_holds (C : Conf) : evenReachFormula.Holds C ↔ C ∈ evenReach :=
  (holds_iff_chain evenReachFormula 0 (fun i => i.elim0) C (Nat.zero_le _)).trans
    (evenFormula_chain (reach C))

/-! ## Fixed-point ⊊ infinitary: the square reaches -/

/-- **The square reaches**: the stores that can run a perfect square of steps. -/
def squareReach : Set Conf := {C | reach C ∈ squares}

/-- **The square reaches are a type of the finitary formulas.** -/
theorem squareReach_isConcept : IsConcept (Apart (formulas countingKnowledge)) squareReach := by
  refine (isConcept_formulas_iff countingKnowledge squareReach).mpr ?_
  intro C inside D equivalent
  show reach D ∈ squares
  rw [← reach_eq_of_equivalent equivalent]
  exact inside

theorem squareReach_bisimClosed : BisimClosed countingKnowledge squareReach :=
  bisimClosed_of_isConcept countingKnowledge squareReach_isConcept

/-- **The square reaches are denoted by an infinitary formula.** -/
theorem squareReach_iformula :
    ∃ χ : IFormula countingKnowledge.Atom countingKnowledge.Label,
      ∀ C, isat countingKnowledge χ C ↔ C ∈ squareReach :=
  exists_iformula_of_bisimClosed countingKnowledge squareReach_bisimClosed

/-- `n` copies of `T` that have learned `k` equations `T = T`. -/
def longCopies (k n : ℕ) : Conf := ⟨List.replicate k (factT, factT), (copies n).present⟩

theorem longCopies_chain (k n : ℕ) : Chain n k (longCopies k n) := ⟨(copies_chain n).1, rfl⟩

/-- A store of the chain can run as many steps as it holds copies. -/
theorem reach_of_chain {n k : ℕ} {C : Conf} (chain : Chain n k C) : reach C = n := by
  have consistent : Consistent C := fun e member => by
    rw [chain.2] at member
    rw [List.eq_of_mem_replicate member]
  rw [reach_of_consistent consistent]
  obtain ⟨card, labels⟩ := (bag_eq_replicate_iff C.present n).mp chain.1
  have all : copiesOf C = C.present := Finset.filter_true_of_mem labels
  rw [all, card]

/-- A bound above the length of every atom a formula names. -/
def atomBound (ψ : FixFormula countingKnowledge) : ℕ :=
  Finset.univ.sup fun i => (ψ.atoms i).length + 1

theorem atom_short (ψ : FixFormula countingKnowledge) (i : Fin ψ.arity) :
    (ψ.atoms i).length < atomBound ψ :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (Finset.le_sup (f := fun i => (ψ.atoms i).length + 1) (Finset.mem_univ i))

/-- **No fixed-point formula denotes the square reaches**: on stores whose knowledge is longer than
its atoms it would denote the squares on the chain. -/
theorem squareReach_not_fixDenoted :
    ¬ ∃ ψ : FixFormula countingKnowledge, ∀ C, ψ.Holds C ↔ C ∈ squareReach := by
  rintro ⟨ψ, denotes⟩
  apply squares_not_denoted () ψ.body ψ.positive
  intro m
  have long : atomBound ψ ≤ (longCopies (atomBound ψ) m).equations.length := by simp [longCopies]
  have reads := holds_iff_chain ψ (atomBound ψ) (atom_short ψ) (longCopies (atomBound ψ) m) long
  rw [reach_of_chain (longCopies_chain _ m)] at reads
  refine reads.symm.trans ((denotes (longCopies (atomBound ψ) m)).trans ?_)
  show reach (longCopies (atomBound ψ) m) ∈ squares ↔ m ∈ squares
  rw [reach_of_chain (longCopies_chain _ m)]

/-- **On the step, a class of reaches is denoted by a fixed-point formula exactly when its set of
reaches is ultimately periodic.** -/
theorem reachClass_fixDenoted_iff (U : Set ℕ) :
    (∃ ψ : FixFormula countingKnowledge, ∀ C, ψ.Holds C ↔ reach C ∈ U) ↔ UltimatelyPeriodic U := by
  constructor
  · rintro ⟨ψ, denotes⟩
    have onChain : ∀ m, satisfies (chain ()) (fun _ => ∅) ψ.body m ↔ m ∈ U := by
      intro m
      have long : atomBound ψ ≤ (longCopies (atomBound ψ) m).equations.length := by simp [longCopies]
      have reads := holds_iff_chain ψ (atomBound ψ) (atom_short ψ) (longCopies (atomBound ψ) m) long
      rw [reach_of_chain (longCopies_chain _ m)] at reads
      refine reads.symm.trans ((denotes (longCopies (atomBound ψ) m)).trans ?_)
      rw [reach_of_chain (longCopies_chain _ m)]
    obtain ⟨N, p, period, repeats⟩ := sat_periodic () ψ.body ψ.positive
    exact ⟨N, p, period, fun m large =>
      ((onChain (m + p)).symm.trans (repeats m large)).trans (onChain m)⟩
  · intro periodic
    obtain ⟨φ, positive, denotes⟩ := periodic_denoted U periodic
    refine ⟨⟨0, φ, Fin.elim0, positive⟩, fun C => ?_⟩
    exact (holds_iff_chain ⟨0, φ, Fin.elim0, positive⟩ 0 (fun i => i.elim0) C (Nat.zero_le _)).trans
      (denotes (reach C))

/-! ## The ladder -/

/-- **The ladder on the step, each inclusion strict**: every finitary formula is a fixed-point
formula; the even reaches are denoted by a fixed-point formula and by no finitary one; every
fixed-point formula is an infinitary one; the square reaches are denoted by an infinitary formula
and by no fixed-point one. Both witnesses are types of the finitary formulas. -/
theorem ladder :
    (∀ φ : HennessyMilner.Formula countingKnowledge.Atom countingKnowledge.Label,
        ∃ ψ : FixFormula countingKnowledge, ∀ C, ψ.Holds C ↔ countingKnowledge.sat φ C) ∧
      (∃ ψ : FixFormula countingKnowledge, ∀ C, ψ.Holds C ↔ C ∈ evenReach) ∧
      (¬ ∃ φ : HennessyMilner.Formula countingKnowledge.Atom countingKnowledge.Label,
        ∀ C, countingKnowledge.sat φ C ↔ C ∈ evenReach) ∧
      (∀ ψ : FixFormula countingKnowledge,
        ∃ χ : IFormula countingKnowledge.Atom countingKnowledge.Label,
          ∀ C, isat countingKnowledge χ C ↔ ψ.Holds C) ∧
      (∃ χ : IFormula countingKnowledge.Atom countingKnowledge.Label,
        ∀ C, isat countingKnowledge χ C ↔ C ∈ squareReach) ∧
      (¬ ∃ ψ : FixFormula countingKnowledge, ∀ C, ψ.Holds C ↔ C ∈ squareReach) ∧
      IsConcept (Apart (formulas countingKnowledge)) evenReach ∧
      IsConcept (Apart (formulas countingKnowledge)) squareReach :=
  ⟨fun φ => ⟨ofFinitary countingKnowledge φ, ofFinitary_holds φ⟩,
    ⟨evenReachFormula, evenReachFormula_holds⟩, evenReach_not_denoted, fun ψ => ψ.iformula,
    squareReach_iformula, squareReach_not_fixDenoted, evenReach_isConcept, squareReach_isConcept⟩

/-! ## Where the counting comes from: the bag-observed system -/

/-- `n` copies of `T` under the inconsistent knowledge `T = U`. -/
def deadStore (n : ℕ) : Conf := ⟨[(factT, factU)], (copies n).present⟩

/-- **A store with inconsistent knowledge cannot fire.** -/
theorem deadStore_stuck (n : ℕ) (C' : Conf) : ¬ Succ countDown (deadStore n) C' := by
  intro step
  obtain ⟨m, before, -⟩ := succ_reach step
  have inconsistent : ¬ Consistent (deadStore n) := fun consistent =>
    absurd (consistent (factT, factU) (List.mem_singleton_self _)) (by decide)
  rw [reach_of_not_consistent inconsistent] at before
  omega

theorem deadStore_mem_evenCount (n : ℕ) : deadStore n ∈ evenCount ↔ Even n := by
  show Even ((bag (deadStore n)).count factT) ↔ Even n
  rw [show bag (deadStore n) = Multiset.replicate n factT from (copies_chain n).1,
    Multiset.count_replicate_self]

/-- A bound above the size of every bag a formula names. -/
def bagBound (ψ : FixFormula counting) : ℕ :=
  Finset.univ.sup fun i => match ψ.atoms i with
    | .inl B => Multiset.card B + 1
    | .inr _ => 0

theorem bag_short (ψ : FixFormula counting) (i : Fin ψ.arity) {B : Multiset Expr}
    (named : ψ.atoms i = .inl B) : Multiset.card B < bagBound ψ := by
  have bound := Finset.le_sup (f := fun i => match ψ.atoms i with
    | .inl B => Multiset.card B + 1
    | .inr _ => 0) (Finset.mem_univ i)
  simp only [named] at bound
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) bound

/-- **With the bag observed, no fixed-point formula denotes the even counts**: two dead stores with
the same knowledge and bags longer than every bag the formula names, one even and one odd, satisfy
the same fixed-point formulas. -/
theorem evenCount_not_fixDenoted :
    ¬ ∃ ψ : FixFormula counting, ∀ C, ψ.Holds C ↔ C ∈ evenCount := by
  rintro ⟨ψ, denotes⟩
  let N := bagBound ψ
  let related : Conf → Conf → Prop := fun C D => C = deadStore (2 * N) ∧ D = deadStore (2 * N + 1)
  have forth : IsSimulation (ltsOf counting) (ltsOf counting) related := by
    rintro C D ⟨rfl, -⟩ action C' step
    exact (deadStore_stuck _ C' step).elim
  have back : IsSimulation (ltsOf counting) (ltsOf counting) fun D C => related C D := by
    rintro D C ⟨-, rfl⟩ action D' step
    exact (deadStore_stuck _ D' step).elim
  have atoms : ∀ (index : Fin ψ.arity) (C D : Conf), related C D →
      (C ∈ atomEnv counting ψ.atoms index ↔ D ∈ atomEnv counting ψ.atoms index) := by
    rintro index C D ⟨rfl, rfl⟩
    show storeView (ψ.atoms index) (deadStore (2 * N)) ↔ storeView (ψ.atoms index) (deadStore (2 * N + 1))
    cases named : ψ.atoms index with
    | inl B =>
        have short := bag_short ψ index named
        have bagOf : ∀ n, (deadStore n).present.val.map Prod.fst = Multiset.replicate n factT :=
          fun n => (copies_chain n).1
        show (deadStore (2 * N)).present.val.map Prod.fst = B ↔
          (deadStore (2 * N + 1)).present.val.map Prod.fst = B
        rw [bagOf, bagOf]
        refine iff_of_false (fun same => ?_) (fun same => ?_)
        · have cards := congrArg Multiset.card same
          rw [Multiset.card_replicate] at cards
          omega
        · have cards := congrArg Multiset.card same
          rw [Multiset.card_replicate] at cards
          omega
    | inr K => exact Iff.rfl
  have same : ψ.Holds (deadStore (2 * N)) ↔ ψ.Holds (deadStore (2 * N + 1)) :=
    satisfies_iff_of_bisimulation forth back ψ.body ψ.positive atoms ⟨rfl, rfl⟩
  have evenIn : deadStore (2 * N) ∈ evenCount := (deadStore_mem_evenCount _).mpr ⟨N, by omega⟩
  have oddOut : deadStore (2 * N + 1) ∉ evenCount := fun inside =>
    Nat.not_even_two_mul_add_one N ((deadStore_mem_evenCount _).mp inside)
  exact oddOut ((denotes _).mp (same.mp ((denotes _).mpr evenIn)))

#print axioms succ_form
#print axioms holds_iff_chain
#print axioms evenFormula_chain
#print axioms evenReachFormula_holds
#print axioms squareReach_isConcept
#print axioms squareReach_iformula
#print axioms squareReach_not_fixDenoted
#print axioms reachClass_fixDenoted_iff
#print axioms ladder
#print axioms deadStore_stuck
#print axioms evenCount_not_fixDenoted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Ladder
