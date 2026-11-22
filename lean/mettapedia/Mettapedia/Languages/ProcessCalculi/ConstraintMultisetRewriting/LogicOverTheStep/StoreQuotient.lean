import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ContextGrades

/-!
# Adding a store, on the bisimilarity quotient

`ContextGrades.beside D` puts a store beside the current one. Whether it is a map on the quotient by
bisimilarity depends on what the observations see, and on identities, not on absence.

## Where it is well defined

On the ground first-order step under any rule set, observing the knowledge and the bag of labels
(`ProgramAdequacy.storeView`):

* `exists_renaming_of_bag`: stores with the same bag of labels differ by a label-keeping
  permutation of identities;
* **`bisimilar_iff_renamed`**: bisimilarity is renaming, for every rule set, absence-checking or not;
* `beside_renamed`, **`beside_respects_bisimilar`**: putting a store beside two bisimilar stores,
  fresh for both, gives bisimilar stores. So `beside D` is a map on the quotient for every program.

Absence does not break this map; it breaks the map's preservation of steps, exactly outside the
grade (`ContextGrades.absences_union_iff`, `ContextGrades.absence_invalidated_beside`), while positive
firings are always kept (`ContextGrades.positive_possible_beside`).

## Controls

* `collision_breaks`: without freshness, identities collide: one copy of `T` and a renamed copy are
  bisimilar, and beside the first copy one store holds one `T` and the other two.
* `coarse_breaks`: observing the knowledge only, a positive program that reads `T` and `U` makes a
  store of `W` and a store of `T` bisimilar (both dead), and beside a store of `U` only the second
  can fire. On a quotient that forgets labels, adding a store is not well defined, even without
  absence.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StoreQuotient

open Interface
open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open StepSpan ProgramAdequacy ContextGrades
open NamesOnTheStep NamesOnTheStep.IssuingControls
open NullsOnTheStep NullsOnTheStep.Composition
open MeTTaCalculus.OccurrenceCommits (fire)

universe uT uO

/-! ## Same bag, renamed -/

section Bags

variable {T : Type uT} {O : Type uO} [DecidableEq O] [DecidableEq T] (label : O → T)

/-- **Stores with the same bag of labels differ by a label-keeping renaming.** -/
theorem exists_renaming_of_bag (s : Finset O) :
    ∀ t : Finset O, s.val.map label = t.val.map label →
      ∃ π : Equiv.Perm O, Keeps label π ∧ s.map π.toEmbedding = t := by
  induction s using Finset.induction_on with
  | empty =>
      intro t same
      have empty : t = ∅ := by
        have card := congrArg Multiset.card same
        simp only [Finset.empty_val, Multiset.map_zero, Multiset.card_zero, Multiset.card_map,
          Finset.card_val] at card
        exact Finset.card_eq_zero.mp card.symm
      exact ⟨1, fun _ => rfl, by simp [empty]⟩
  | @insert a s outside ih =>
      intro t same
      rw [Finset.insert_val_of_notMem outside, Multiset.map_cons] at same
      have inT : label a ∈ t.val.map label := by rw [← same]; simp
      obtain ⟨b, bIn, labelled⟩ := Multiset.mem_map.mp inT
      have rest : s.val.map label = (t.erase b).val.map label := by
        rw [Finset.erase_val, Multiset.map_erase_of_mem _ _ bIn, ← same, labelled,
          Multiset.erase_cons_head]
      obtain ⟨π₀, keeps₀, mapped₀⟩ := ih (t.erase b) rest
      have cLabel : label (π₀ a) = label b := (keeps₀ a).trans labelled.symm
      refine ⟨Equiv.swap (π₀ a) b * π₀, ?_, ?_⟩
      · intro x
        rw [Equiv.Perm.mul_apply]
        by_cases atC : π₀ x = π₀ a
        · rw [atC, Equiv.swap_apply_left, ← cLabel, ← atC, keeps₀ x]
        · by_cases atB : π₀ x = b
          · rw [atB, Equiv.swap_apply_right, cLabel, ← atB, keeps₀ x]
          · rw [Equiv.swap_apply_of_ne_of_ne atC atB, keeps₀ x]
      · have agree : ∀ x ∈ s, (Equiv.swap (π₀ a) b * π₀) x = π₀ x := by
          intro x inside
          rw [Equiv.Perm.mul_apply]
          have inErase : π₀ x ∈ t.erase b := by
            rw [← mapped₀]
            exact Finset.mem_map_of_mem π₀.toEmbedding inside
          have notB : π₀ x ≠ b := fun same => (Finset.notMem_erase b t) (same ▸ inErase)
          have notC : π₀ x ≠ π₀ a := fun same => outside (π₀.injective same ▸ inside)
          exact Equiv.swap_apply_of_ne_of_ne notC notB
        rw [Finset.map_insert]
        have head : (Equiv.swap (π₀ a) b * π₀).toEmbedding a = b := by
          rw [Equiv.toEmbedding_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have tail : s.map (Equiv.swap (π₀ a) b * π₀).toEmbedding = t.erase b := by
          rw [← mapped₀]
          ext y
          simp only [Finset.mem_map, Equiv.toEmbedding_apply]
          constructor
          · rintro ⟨x, inside, rfl⟩
            exact ⟨x, inside, (agree x inside).symm⟩
          · rintro ⟨x, inside, rfl⟩
            exact ⟨x, inside, agree x inside⟩
        rw [head, tail, Finset.insert_erase bIn]

end Bags

/-! ## On the ground step -/

/-- **Bisimilarity is renaming**, for every rule set, observing the knowledge and the bag of
labels. -/
theorem bisimilar_iff_renamed (R : Set (RuleInstance Expr)) (C D : Conf) :
    (stepSystem (program ground Prod.fst R) storeView).Bisimilar C D ↔ Renamed Prod.fst C D := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    have bags : C.present.val.map Prod.fst = D.present.val.map Prod.fst :=
      (bisimulation.2.2 related (.inl (C.present.val.map Prod.fst))).mp rfl |>.symm
    have knowledge : D.equations = C.equations :=
      (bisimulation.2.2 related (.inr C.equations)).mp rfl
    obtain ⟨π, keeps, mapped⟩ := exists_renaming_of_bag Prod.fst C.present D.present bags
    refine ⟨π, keeps, ?_⟩
    cases D with
    | mk equations present =>
        simp only [renameConf]
        simp only at knowledge mapped
        rw [knowledge, mapped]
  · intro renamed
    exact ⟨Renamed Prod.fst, renamed_isBisimulation ground Prod.fst R storeView storeView_invariant,
      renamed⟩

/-- **Putting a fresh store beside two renamed stores gives renamed stores.** -/
theorem beside_renamed {C C' D : Conf} (renamed : Renamed Prod.fst C C')
    (freshC : Disjoint C.present D.present) (freshC' : Disjoint C'.present D.present) :
    Renamed Prod.fst (beside D C) (beside D C') := by
  obtain ⟨π, keeps, rfl⟩ := renamed
  have kept : ∀ o, (π o).1 = o.1 := keeps
  let m := C.present.toList
  have outsideM : ∀ o ∈ m, o ∉ D.present := fun o inside =>
    Finset.disjoint_left.mp freshC (Finset.mem_toList.mp inside)
  have outsideM' : ∀ o ∈ m.map π, o ∉ D.present := by
    intro o inside
    obtain ⟨x, xIn, rfl⟩ := List.mem_map.mp inside
    exact Finset.disjoint_left.mp freshC'
      (Finset.mem_map_of_mem π.toEmbedding (Finset.mem_toList.mp xIn))
  obtain ⟨π', keeps', fix, mapped⟩ := exists_renaming Prod.fst m (m.map π) (Finset.nodup_toList _)
    ((Finset.nodup_toList _).map π.injective) (by simp only [List.map_map]; congr 1; funext o; exact (kept o).symm)
    D.present outsideM outsideM'
  have agree : ∀ x ∈ C.present, π' x = π x :=
    fun x inside => (List.map_inj_left.mp mapped) x (Finset.mem_toList.mpr inside)
  refine ⟨π', keeps', ?_⟩
  cases C with
  | mk equations present =>
      simp only [beside, union, renameConf]
      congr 1
      rw [Finset.map_union]
      congr 1
      · ext y
        simp only [Finset.mem_map, Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨x, inside, rfl⟩
          exact ⟨x, inside, agree x inside⟩
        · rintro ⟨x, inside, rfl⟩
          exact ⟨x, inside, (agree x inside).symm⟩
      · ext y
        simp only [Finset.mem_map, Equiv.toEmbedding_apply]
        constructor
        · intro inside
          exact ⟨y, inside, fix y inside⟩
        · rintro ⟨x, inside, rfl⟩
          rw [fix x inside]
          exact inside

/-- **Adding a fresh store is a map on the bisimilarity quotient**, for every rule set. -/
theorem beside_respects_bisimilar (R : Set (RuleInstance Expr)) {C C' D : Conf}
    (bisimilar : (stepSystem (program ground Prod.fst R) storeView).Bisimilar C C')
    (freshC : Disjoint C.present D.present) (freshC' : Disjoint C'.present D.present) :
    (stepSystem (program ground Prod.fst R) storeView).Bisimilar (beside D C) (beside D C') :=
  (bisimilar_iff_renamed R _ _).mpr
    (beside_renamed ((bisimilar_iff_renamed R C C').mp bisimilar) freshC freshC')

/-! ## Controls -/

/-- One copy of `T`, numbered `k`. -/
def copyT (k : ℕ) : Conf := ⟨[], {(factT, k)}⟩

/-- **Control: identities collide without freshness.** The copies `0` and `1` are bisimilar; beside
the copy `0`, one side holds one `T` and the other two. -/
theorem collision_breaks (R : Set (RuleInstance Expr)) :
    (stepSystem (program ground Prod.fst R) storeView).Bisimilar (copyT 0) (copyT 1) ∧
      ¬ (stepSystem (program ground Prod.fst R) storeView).Bisimilar
        (beside (copyT 0) (copyT 0)) (beside (copyT 0) (copyT 1)) := by
  constructor
  · refine (bisimilar_iff_renamed R _ _).mpr ⟨Equiv.swap (factT, 0) (factT, 1), ?_, ?_⟩
    · intro o
      by_cases zero : o = (factT, 0)
      · rw [zero, Equiv.swap_apply_left]
      · by_cases one : o = (factT, 1)
        · rw [one, Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne zero one]
    · simp [copyT, renameConf]
  · intro bisimilar
    obtain ⟨π, _, same⟩ := (bisimilar_iff_renamed R _ _).mp bisimilar
    have cards := congrArg (fun C : Conf => C.present.card) same
    simp [beside, union, copyT, renameConf] at cards

/-- The positive program that reads `T` and `U`. -/
def readsTU : RuleInstance Expr := ⟨[], [factT, factU], [], [], []⟩

abbrev tuStep := program ground (Prod.fst : Occ → Expr) {readsTU}

/-- Observing the knowledge only. -/
def knowledgeView (K : EquationStore Expr) (C : Conf) : Prop := C.equations = K

/-- **The program fires only where both `T` and `U` are present.** -/
theorem fires_needs_both {C C' : Conf} (step : Succ tuStep C C') :
    (∃ o ∈ C.present, o.1 = factT) ∧ (∃ o ∈ C.present, o.1 = factU) := by
  obtain ⟨rule, ⟨taken, read, made⟩, member, valid, _⟩ :=
    (program_succ_iff ground Prod.fst {readsTU} C C').mp step
  have isTU : rule = readsTU := member
  subst isTU
  obtain ⟨o₁, o₂, rfl⟩ := List.length_eq_two.mp valid.read_length.symm
  have in₁ : o₁ ∈ C.present := valid.occurrences.kept_subset (by simp [Selection.commit])
  have in₂ : o₂ ∈ C.present := valid.occurrences.kept_subset (by simp [Selection.commit])
  obtain ⟨_, solved⟩ := valid.consistent
  have eq₁ : (factT, o₁.1) ∈ (⟨taken, [o₁, o₂], made⟩ : Selection Occ).problem Prod.fst readsTU C := by
    simp [Selection.problem, Selection.equations, readsTU]
  have eq₂ : (factU, o₂.1) ∈ (⟨taken, [o₁, o₂], made⟩ : Selection Occ).problem Prod.fst readsTU C := by
    simp [Selection.problem, Selection.equations, readsTU]
  have label₁ : factT = o₁.1 := solved _ eq₁
  have label₂ : factU = o₂.1 := solved _ eq₂
  exact ⟨⟨o₁, in₁, label₁.symm⟩, ⟨o₂, in₂, label₂.symm⟩⟩

/-- Without an occurrence of `T`, the program cannot fire. -/
theorem dead_without_T {C C' : Conf} (noT : ∀ o ∈ C.present, o.1 ≠ factT) : ¬ Succ tuStep C C' := by
  intro step
  obtain ⟨o, inside, labelled⟩ := (fires_needs_both step).1
  exact noT o inside labelled

/-- Without an occurrence of `U`, the program cannot fire. -/
theorem dead_without_U {C C' : Conf} (noU : ∀ o ∈ C.present, o.1 ≠ factU) : ¬ Succ tuStep C C' := by
  intro step
  obtain ⟨o, inside, labelled⟩ := (fires_needs_both step).2
  exact noU o inside labelled

/-- The store holding `T` and `U` fires. -/
theorem fires_TU : Succ tuStep ⟨[], {(factT, 0), (factU, 0)}⟩
    ⟨[(factT, factT), (factU, factU)], {(factT, 0), (factU, 0)}⟩ := by
  refine (program_succ_iff ground Prod.fst {readsTU} _ _).mpr
    ⟨readsTU, ⟨[], [(factT, 0), (factU, 0)], []⟩, rfl, ?_, ?_⟩
  · refine ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨(), ?_⟩, ?_⟩
    · simp [Selection.commit]
    · intro o inside
      simp only [Selection.commit, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> simp
    · simp [Selection.commit]
    · simp [Selection.commit]
    · intro _ member
      simp [Selection.commit] at member
    · intro e member
      simp only [Selection.problem, Selection.equations, readsTU, List.zipWith_cons_cons,
        List.zipWith_nil_left, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl <;> rfl
    · intro check member
      simp [readsTU] at member
  · simp [Selection.result, Selection.problem, Selection.equations, readsTU, fire, Selection.commit]

/-- **Control: on a quotient that forgets labels, adding a store is not well defined**, even for a
positive program. A store of `W` and a store of `T` are bisimilar, both dead; beside a store of `U`
the second fires and the first cannot. -/
theorem coarse_breaks :
    (stepSystem tuStep knowledgeView).Bisimilar ⟨[], {(factW, 0)}⟩ ⟨[], {(factT, 0)}⟩ ∧
      ¬ (stepSystem tuStep knowledgeView).Bisimilar
        (beside ⟨[], {(factU, 0)}⟩ ⟨[], {(factW, 0)}⟩) (beside ⟨[], {(factU, 0)}⟩ ⟨[], {(factT, 0)}⟩) := by
  have wDead : ∀ C', ¬ Succ tuStep ⟨[], {(factW, 0)}⟩ C' := fun C' =>
    dead_without_T (by
      intro o inside
      rw [Finset.mem_singleton.mp inside]
      decide)
  have tDead : ∀ C', ¬ Succ tuStep ⟨[], {(factT, 0)}⟩ C' := fun C' =>
    dead_without_U (by
      intro o inside
      rw [Finset.mem_singleton.mp inside]
      decide)
  constructor
  · refine ⟨fun C D => C = ⟨[], {(factW, 0)}⟩ ∧ D = ⟨[], {(factT, 0)}⟩, ⟨?_, ?_, ?_⟩, rfl, rfl⟩
    · rintro C D ⟨rfl, rfl⟩ _ C' step
      exact absurd step (wDead C')
    · rintro C D ⟨rfl, rfl⟩ _ D' step
      exact absurd step (tDead D')
    · rintro C D ⟨rfl, rfl⟩ K
      exact Iff.rfl
  · intro bisimilar
    have possible : (stepSystem tuStep knowledgeView).sat (.dia () .top)
        (beside ⟨[], {(factU, 0)}⟩ ⟨[], {(factT, 0)}⟩) := by
      have same : beside ⟨[], {(factU, 0)}⟩ ⟨[], {(factT, 0)}⟩ = ⟨[], {(factT, 0), (factU, 0)}⟩ := by
        simp [beside, union]
      rw [same]
      exact ⟨_, fires_TU, trivial⟩
    have there := ((stepSystem tuStep knowledgeView).logicallyEquivalent_of_bisimilar bisimilar
      (.dia () .top)).mpr possible
    obtain ⟨C', step, _⟩ := there
    have same : beside ⟨[], {(factU, 0)}⟩ ⟨[], {(factW, 0)}⟩ = ⟨[], {(factW, 0), (factU, 0)}⟩ := by
      simp [beside, union]
    rw [same] at step
    exact dead_without_T (by
      intro o inside
      simp only [Finset.mem_insert, Finset.mem_singleton] at inside
      rcases inside with rfl | rfl <;> decide) step

#print axioms exists_renaming_of_bag
#print axioms bisimilar_iff_renamed
#print axioms beside_renamed
#print axioms beside_respects_bisimilar
#print axioms collision_breaks
#print axioms fires_needs_both
#print axioms fires_TU
#print axioms coarse_breaks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StoreQuotient
