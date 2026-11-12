import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNamesControls
import Mathlib.Data.Set.Finite.List

/-!
# Hennessy–Milner adequacy on the real first-order step

`StepSpan.logicallyEquivalent_iff_bisimilar` gives adequacy for the step through the tree's library,
under finite covers of successor sets up to bisimilarity. This module discharges that hypothesis
for the first-order step (`AnnotatedRuns.firstOrder`) under a finite program, and shows where it
fails without one.

## Renaming issued occurrence identities

A firing chooses fresh identities for what it makes. Choices that differ only there give
successors that differ by a renaming. A **label-keeping permutation** of identities (`Keeps`)
acts on configurations (`renameConf`) and selections (`renameSel`), and the step is equivariant:
validity and results commute with it (`valid_rename`, `result_rename`). So being renamed
(`Renamed`) is a bisimulation of the step under every rule set (`renamed_isBisimulation`), for
observations that cannot see identities.

## Finite programs

Under a rule set `R` (`program`), a firing is a rule of `R`, a choice of taken and read
occurrences among the finitely many present, and fresh made identities. Any two fresh choices are
related by a label-keeping permutation fixing the store (`exists_renaming`). So the successors of
a store are covered, up to renaming, by finitely many representatives (`reps`, `reps_finite`,
`covered`) when `R` is finite, and:

* `program_imageFiniteBisimilar`, **`program_adequacy`**: logical equivalence is bisimilarity on the
  first-order step under every finite program, for every observation set invariant under
  renaming, with a supply of fresh identities for every label;
* `ground_program_adequacy`: the ground instance, observing the knowledge and the bag of labels.

## Where it fails

* `base_not_imageFiniteBisimilar`: the unrestricted first-order step admits every rule instance;
  at the empty store, making `n` copies of one constant gives, for each `n`, a successor with its
  own bag of labels, so no finite set covers the successors up to bisimilarity. The finite-cover
  route to finitary adequacy is unavailable there; the infinitary logic of
  `InfinitaryAdequacy` covers it.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy

open Interface
open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open StepSpan

universe uT uS uO

section Renaming

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **A label-keeping renaming** of occurrence identities. -/
def Keeps (π : Equiv.Perm O) : Prop := ∀ o, label (π o) = label o

omit [DecidableEq O] in
theorem keeps_symm {π : Equiv.Perm O} (keeps : Keeps label π) : Keeps label π.symm := by
  intro o
  have back := keeps (π.symm o)
  rw [Equiv.apply_symm_apply] at back
  exact back.symm

/-- Renaming the present occurrences of a configuration; its knowledge is kept. -/
def renameConf (π : Equiv.Perm O) (C : Configuration T O) : Configuration T O :=
  ⟨C.equations, C.present.map π.toEmbedding⟩

/-- Renaming a selection. -/
def renameSel (π : Equiv.Perm O) (sel : Selection O) : Selection O :=
  ⟨sel.taken.map π, sel.read.map π, sel.made.map π⟩

theorem toFinset_map (π : Equiv.Perm O) (l : List O) :
    (l.map π).toFinset = l.toFinset.map π.toEmbedding := by
  ext o
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_map, Equiv.toEmbedding_apply]

omit [DecidableEq O] in
theorem renameConf_symm (π : Equiv.Perm O) (C : Configuration T O) :
    renameConf π.symm (renameConf π C) = C := by
  cases C with
  | mk equations present =>
      simp only [renameConf]
      congr 1
      ext o
      simp

omit [DecidableEq O] in
theorem renameConf_fix {π : Equiv.Perm O} {C : Configuration T O}
    (fix : ∀ o ∈ C.present, π o = o) : renameConf π C = C := by
  cases C with
  | mk equations present =>
      simp only [renameConf]
      congr 1
      ext o
      simp only [Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨a, member, rfl⟩
        rw [fix a member]
        exact member
      · intro member
        exact ⟨o, member, fix o member⟩

omit [DecidableEq O] in
theorem map_fix {π : Equiv.Perm O} {F : Finset O} (fix : ∀ o ∈ F, π o = o) {l : List O}
    (inside : ∀ o ∈ l, o ∈ F) : l.map π = l :=
  (List.map_congr_left fun o member => fix o (inside o member)).trans (List.map_id l)

omit [DecidableEq O] in
theorem equations_rename {π : Equiv.Perm O} (keeps : Keeps label π) (patterns : List T)
    (selected : List O) :
    Selection.equations label patterns (selected.map π) = Selection.equations label patterns selected := by
  have kept : ∀ o, label (π o) = label o := keeps
  simp only [Selection.equations, List.zipWith_map_right, kept]

omit [DecidableEq O] in
theorem problem_rename {π : Equiv.Perm O} (keeps : Keeps label π) (sel : Selection O)
    (rule : RuleInstance T) (C : Configuration T O) :
    (renameSel π sel).problem label rule (renameConf π C) = sel.problem label rule C := by
  simp only [Selection.problem, renameSel, renameConf, equations_rename label keeps]

omit [DecidableEq O] in
theorem card_matches_rename {π : Equiv.Perm O} (keeps : Keeps label π) (σ : S) (store : Finset O)
    (pattern : T) :
    (Check.«matches» A σ label (store.map π.toEmbedding) pattern).card =
      (Check.«matches» A σ label store pattern).card := by
  classical
  simp only [Check.«matches»]
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro o _
  simp only [Function.comp, Equiv.toEmbedding_apply, keeps o]

omit [DecidableEq O] in
/-- **Checks read labels only.** -/
theorem holds_rename {π : Equiv.Perm O} (keeps : Keeps label π) (σ : S) (store : Finset O) :
    ∀ check : Check T,
      check.Holds A σ label (store.map π.toEmbedding) ↔ check.Holds A σ label store
  | .equal _ _ => Iff.rfl
  | .absent _ => by
      have kept : ∀ o, label (π o) = label o := keeps
      constructor
      · intro clear o member
        have there := clear (π.toEmbedding o) (Finset.mem_map_of_mem π.toEmbedding member)
        rwa [Equiv.toEmbedding_apply, kept o] at there
      · intro clear o member
        obtain ⟨a, inside, rfl⟩ := Finset.mem_map.mp member
        rw [Equiv.toEmbedding_apply, kept a]
        exact clear a inside
  | .count p _ => by
      simp only [Check.Holds]
      rw [card_matches_rename A label keeps]

/-- **Validity is equivariant.** -/
theorem valid_rename {π : Equiv.Perm O} (keeps : Keeps label π) {rule : RuleInstance T}
    {sel : Selection O} {C : Configuration T O} (valid : sel.Valid A label rule C) :
    (renameSel π sel).Valid A label rule (renameConf π C) where
  take_distinct := valid.take_distinct.map π.injective
  output_distinct := valid.output_distinct.map π.injective
  take_length := by simp [renameSel, valid.take_length]
  read_length := by simp [renameSel, valid.read_length]
  outputs := by
    have same : label ∘ ⇑π = label := funext keeps
    simp only [renameSel, List.map_map, same, valid.outputs]
  occurrences := by
    have enabled := valid.occurrences
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (sel.taken.map π).toFinset ⊆ C.present.map π.toEmbedding
      rw [toFinset_map]
      exact Finset.map_subset_map.mpr enabled.taken_subset
    · show (sel.read.map π).toFinset ⊆ C.present.map π.toEmbedding
      rw [toFinset_map]
      exact Finset.map_subset_map.mpr enabled.kept_subset
    · show Disjoint (sel.taken.map π).toFinset (sel.read.map π).toFinset
      rw [toFinset_map, toFinset_map]
      exact (Finset.disjoint_map _).mpr enabled.apart
    · show Disjoint (sel.made.map π).toFinset (C.present.map π.toEmbedding)
      rw [toFinset_map]
      exact (Finset.disjoint_map _).mpr enabled.fresh
    · intro query member
      simp [Selection.commit] at member
  consistent := by
    rw [problem_rename label keeps]
    exact valid.consistent
  checks := by
    intro check member
    rw [problem_rename label keeps]
    intro σ solved
    exact (holds_rename A label keeps σ C.present check).mpr (valid.checks check member σ solved)

/-- **Results are equivariant.** -/
theorem result_rename {π : Equiv.Perm O} (keeps : Keeps label π) (sel : Selection O)
    (rule : RuleInstance T) (C : Configuration T O) :
    (renameSel π sel).result label rule (renameConf π C) = renameConf π (sel.result label rule C) := by
  cases C with
  | mk equations present =>
      simp only [Selection.result, Selection.problem, renameConf, renameSel,
        equations_rename label keeps, fire, Selection.commit, toFinset_map, Finset.map_union,
        Finset.map_sdiff]

/-! ## The step under a rule set -/

/-- **The first-order step under a rule set**: admitted firings whose rule belongs to it. -/
def program (R : Set (RuleInstance T)) :
    Interface.Step (Frames.ofSubstitution A) O (Configuration T O) (fun _ => AnnotatedRuns.Firing T S O) :=
  Interface.Step.ofEffect (AnnotatedRuns.firstOrder A label).toStep.effectCore
    fun {C} f _ => f.Valid A label C ∧ f.rule ∈ R

/-- Its successors: a rule of the set, a valid selection, its result. Predicate queries add no
successor. -/
theorem program_succ_iff (R : Set (RuleInstance T)) (C C' : Configuration T O) :
    Succ (program A label R) C C' ↔
      ∃ (rule : RuleInstance T) (sel : Selection O),
        rule ∈ R ∧ sel.Valid A label rule C ∧ sel.result label rule C = C' := by
  constructor
  · rintro ⟨f, ⟨_, valid, member⟩, reached⟩
    exact ⟨f.rule, f.selection, member, valid.firing, reached⟩
  · rintro ⟨rule, sel, member, valid, reached⟩
    let f : AnnotatedRuns.Firing T S O := ⟨rule, [], sel⟩
    have fValid : f.Valid A label C :=
      (PredicateQueryAdmission.valid_empty_iff A label rule C sel).mpr valid
    exact ⟨f, ⟨(AnnotatedRuns.firstOrder A label).toStep.prepares fValid, fValid, member⟩, reached⟩

/-- **Renamed**: related by a label-keeping permutation of identities. -/
def Renamed (C D : Configuration T O) : Prop :=
  ∃ π : Equiv.Perm O, Keeps label π ∧ D = renameConf π C

omit [DecidableEq O] in
theorem renamed_symm {C D : Configuration T O} (renamed : Renamed label C D) : Renamed label D C := by
  obtain ⟨π, keeps, rfl⟩ := renamed
  exact ⟨π.symm, keeps_symm label keeps, (renameConf_symm π C).symm⟩

/-- **A renamed store steps alike**, under every rule set. -/
theorem renamed_succ {R : Set (RuleInstance T)} {C D C' : Configuration T O}
    (renamed : Renamed label C D) (step : Succ (program A label R) C C') :
    ∃ D', Succ (program A label R) D D' ∧ Renamed label C' D' := by
  obtain ⟨π, keeps, rfl⟩ := renamed
  obtain ⟨rule, sel, member, valid, rfl⟩ := (program_succ_iff A label R C C').mp step
  exact ⟨renameConf π (sel.result label rule C), (program_succ_iff A label R _ _).mpr
      ⟨rule, renameSel π sel, member, valid_rename A label keeps valid,
        result_rename label keeps sel rule C⟩, π, keeps, rfl⟩

/-- **Renaming is a bisimulation of the step**, under every rule set, for observations that
cannot see identities. -/
theorem renamed_isBisimulation (R : Set (RuleInstance T)) {Atom : Type}
    (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C)) :
    (stepSystem (program A label R) observes).IsBisimulation (Renamed label) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C D renamed _ C' step
    exact renamed_succ A label renamed step
  · intro C D renamed _ D' step
    obtain ⟨C', back, renamed'⟩ := renamed_succ A label (renamed_symm label renamed) step
    exact ⟨C', back, renamed_symm label renamed'⟩
  · rintro C D ⟨π, keeps, rfl⟩ a
    exact (invariant a π C keeps).symm

/-! ## Finite programs -/

/-- **Fresh identities for every list of labels.** -/
theorem freshList (supply : ∀ (used : Finset O) (t : T), ∃ o, o ∉ used ∧ label o = t) :
    ∀ (used : Finset O) (ts : List T),
      ∃ m : List O, m.Nodup ∧ (∀ o ∈ m, o ∉ used) ∧ m.map label = ts
  | _, [] => ⟨[], List.nodup_nil, by simp, rfl⟩
  | used, t :: ts => by
      obtain ⟨o, fresh, labelled⟩ := supply used t
      obtain ⟨m, nodup, freshM, labels⟩ := freshList supply (insert o used) ts
      refine ⟨o :: m, List.nodup_cons.mpr
        ⟨fun inM => freshM o inM (Finset.mem_insert_self o used), nodup⟩, ?_, by
          simp [labelled, labels]⟩
      intro x member
      rcases List.mem_cons.mp member with same | inM
      · subst same
        exact fresh
      · exact fun inUsed => freshM x inM (Finset.mem_insert_of_mem inUsed)

/-- **Two fresh choices with the same labels differ by a label-keeping permutation fixing the
store.** -/
theorem exists_renaming : ∀ (m m' : List O), m.Nodup → m'.Nodup → m.map label = m'.map label →
    ∀ (F : Finset O), (∀ o ∈ m, o ∉ F) → (∀ o ∈ m', o ∉ F) →
      ∃ π : Equiv.Perm O, Keeps label π ∧ (∀ o ∈ F, π o = o) ∧ m.map π = m'
  | [], [], _, _, _, _, _, _ => ⟨1, fun _ => rfl, fun _ _ => rfl, rfl⟩
  | [], _ :: _, _, _, same, _, _, _ => by simp at same
  | _ :: _, [], _, _, same, _, _, _ => by simp at same
  | a :: as, b :: bs, nodup, nodup', same, F, fresh, fresh' => by
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨headLabel, tailLabels⟩ := same
      obtain ⟨aOut, asNodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨bOut, bsNodup⟩ := List.nodup_cons.mp nodup'
      obtain ⟨π₀, keeps₀, fix₀, mapped₀⟩ := exists_renaming as bs asNodup bsNodup tailLabels F
        (fun o member => fresh o (List.mem_cons_of_mem a member))
        (fun o member => fresh' o (List.mem_cons_of_mem b member))
      have cLabel : label (π₀ a) = label b := (keeps₀ a).trans headLabel
      refine ⟨Equiv.swap (π₀ a) b * π₀, ?_, ?_, ?_⟩
      · intro x
        rw [Equiv.Perm.mul_apply]
        by_cases atC : π₀ x = π₀ a
        · rw [atC, Equiv.swap_apply_left, ← cLabel, ← atC, keeps₀ x]
        · by_cases atB : π₀ x = b
          · rw [atB, Equiv.swap_apply_right, cLabel, ← atB, keeps₀ x]
          · rw [Equiv.swap_apply_of_ne_of_ne atC atB, keeps₀ x]
      · intro x member
        rw [Equiv.Perm.mul_apply, fix₀ x member]
        have notB : x ≠ b := fun same => fresh' b List.mem_cons_self (same ▸ member)
        have notC : x ≠ π₀ a := by
          intro same
          have back : π₀ x = π₀ a := by rw [fix₀ x member]; exact same
          have equal : x = a := π₀.injective back
          exact fresh a List.mem_cons_self (equal ▸ member)
        exact Equiv.swap_apply_of_ne_of_ne notC notB
      · rw [List.map_cons, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        congr 1
        rw [← mapped₀]
        apply List.map_congr_left
        intro x member
        rw [Equiv.Perm.mul_apply]
        have inMap : π₀ x ∈ as.map π₀ := List.mem_map_of_mem member
        have inBs : π₀ x ∈ bs := mapped₀ ▸ inMap
        have notB : π₀ x ≠ b := fun same => bOut (same ▸ inBs)
        have notC : π₀ x ≠ π₀ a := fun same => aOut (π₀.injective same ▸ member)
        exact Equiv.swap_apply_of_ne_of_ne notC notB

/-- Lists of a given length over a finite store. -/
def listsOver (F : Finset O) (n : ℕ) : Set (List O) := {l | l.length = n ∧ ∀ o ∈ l, o ∈ F}

omit [DecidableEq O] in
theorem listsOver_finite (F : Finset O) (n : ℕ) : (listsOver F n).Finite := by
  refine ((List.finite_length_eq F n).image (List.map Subtype.val)).subset ?_
  rintro l ⟨length, inside⟩
  refine ⟨l.attach.map fun x => ⟨x.1, inside x.1 x.2⟩, by simp [length], ?_⟩
  simp

/-- A supply of fresh identities for every label. -/
def Supply : Prop := ∀ (used : Finset O) (t : T), ∃ o, o ∉ used ∧ label o = t

/-- The canonical fresh choice for a list of labels. -/
def freshFor (supply : Supply label) (used : Finset O) (ts : List T) : List O :=
  Classical.choose (freshList label supply used ts)

theorem freshFor_spec (supply : Supply label) (used : Finset O) (ts : List T) :
    (freshFor label supply used ts).Nodup ∧ (∀ o ∈ freshFor label supply used ts, o ∉ used) ∧
      (freshFor label supply used ts).map label = ts :=
  Classical.choose_spec (freshList label supply used ts)

/-- **The representatives**: per rule, taken and read occurrences among those present, and the
canonical fresh choice. -/
def reps (supply : Supply label) (R : Set (RuleInstance T)) (C : Configuration T O) :
    Set (Configuration T O) :=
  ⋃ rule ∈ R, (fun p : List O × List O =>
    (⟨p.1, p.2, freshFor label supply C.present rule.produce⟩ : Selection O).result label rule C) ''
      (listsOver C.present rule.take.length ×ˢ listsOver C.present rule.read.length)

theorem reps_finite (supply : Supply label) {R : Set (RuleInstance T)} (finite : R.Finite)
    (C : Configuration T O) : (reps label supply R C).Finite :=
  finite.biUnion fun _ _ => ((listsOver_finite _ _).prod (listsOver_finite _ _)).image _

/-- **Every successor is a renaming of a representative.** -/
theorem covered (supply : Supply label) {R : Set (RuleInstance T)} {C C' : Configuration T O}
    (step : Succ (program A label R) C C') : ∃ r ∈ reps label supply R C, Renamed label r C' := by
  obtain ⟨rule, ⟨taken, read, made⟩, member, valid, rfl⟩ := (program_succ_iff A label R C C').mp step
  obtain ⟨canonicalNodup, canonicalFresh, canonicalLabels⟩ :=
    freshFor_spec label supply C.present rule.produce
  have madeFresh : ∀ o ∈ made, o ∉ C.present := by
    intro o member present
    exact Finset.disjoint_left.mp valid.occurrences.fresh (List.mem_toFinset.mpr member) present
  obtain ⟨π, keeps, fix, mapped⟩ := exists_renaming label _ made canonicalNodup
    valid.output_distinct (canonicalLabels.trans valid.outputs.symm) C.present canonicalFresh madeFresh
  have takenInside : ∀ o ∈ taken, o ∈ C.present := fun o member =>
    valid.occurrences.taken_subset (List.mem_toFinset.mpr member)
  have readInside : ∀ o ∈ read, o ∈ C.present := fun o member =>
    valid.occurrences.kept_subset (List.mem_toFinset.mpr member)
  refine ⟨_, Set.mem_biUnion member ⟨(taken, read),
    ⟨⟨valid.take_length.symm, takenInside⟩, ⟨valid.read_length.symm, readInside⟩⟩, rfl⟩, π, keeps, ?_⟩
  rw [← result_rename label keeps, renameConf_fix fix]
  simp only [renameSel, map_fix fix takenInside, map_fix fix readInside, mapped]

/-- **Finite covers up to bisimilarity for every finite program.** -/
theorem program_imageFiniteBisimilar (supply : Supply label) {R : Set (RuleInstance T)}
    (finite : R.Finite) {Atom : Type} (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C)) :
    (stepSystem (program A label R) observes).ImageFiniteBisimilar := by
  intro _ C
  refine ⟨reps label supply R C, reps_finite label supply finite C, ?_⟩
  intro C' step
  obtain ⟨r, member, renamed⟩ := covered A label supply step
  exact ⟨r, member, Renamed label, renamed_isBisimulation A label R observes invariant,
    renamed_symm label renamed⟩

/-- **Hennessy–Milner adequacy on the first-order step under every finite program.** -/
theorem program_adequacy (supply : Supply label) {R : Set (RuleInstance T)} (finite : R.Finite)
    {Atom : Type} (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C))
    (C D : Configuration T O) :
    (stepSystem (program A label R) observes).LogicallyEquivalent C D ↔
      (stepSystem (program A label R) observes).Bisimilar C D :=
  logicallyEquivalent_iff_bisimilar (program A label R) observes
    (program_imageFiniteBisimilar A label supply finite observes invariant) C D

end Renaming

/-! ## The ground instance, and where it fails -/

section Ground

open NamesOnTheStep NamesOnTheStep.IssuingControls

/-- **Observing a store**: its knowledge and its bag of labels, nothing of its identities. -/
def storeView : Multiset Expr ⊕ EquationStore Expr → Conf → Prop
  | .inl bag, C => C.present.val.map Prod.fst = bag
  | .inr knowledge, C => C.equations = knowledge

theorem storeView_invariant (a : Multiset Expr ⊕ EquationStore Expr) (π : Equiv.Perm Occ) (C : Conf)
    (keeps : Keeps Prod.fst π) : storeView a (renameConf π C) ↔ storeView a C := by
  cases a with
  | inl bag =>
      have same : Prod.fst ∘ ⇑π.toEmbedding = (Prod.fst : Occ → Expr) := funext keeps
      simp only [storeView, renameConf, Finset.map_val, Multiset.map_map, same]
  | inr knowledge => exact Iff.rfl

/-- Fresh identities for every label. -/
theorem occSupply (used : Finset Occ) (value : Expr) : ∃ o : Occ, o ∉ used ∧ o.1 = value := by
  obtain ⟨n, unused⟩ := Infinite.exists_notMem_finset (used.image Prod.snd)
  exact ⟨(value, n), fun member => unused (Finset.mem_image.mpr ⟨_, member, rfl⟩), rfl⟩

/-- **Adequacy on the ground first-order step under every finite program**, observing the
knowledge and the bag of labels. -/
theorem ground_program_adequacy {R : Set (RuleInstance Expr)} (finite : R.Finite) (C D : Conf) :
    (stepSystem (program ground Prod.fst R) storeView).LogicallyEquivalent C D ↔
      (stepSystem (program ground Prod.fst R) storeView).Bisimilar C D :=
  program_adequacy ground Prod.fst occSupply finite storeView storeView_invariant C D

/-- The empty store. -/
def emptyStore : Conf := ⟨[], ∅⟩

/-- The rule instance making `n` copies of `T`. -/
def makes (n : ℕ) : RuleInstance Expr := ⟨[], [], [], [], List.replicate n factT⟩

/-- Its selection: copies `0, …, n - 1`. -/
def makesAt (n : ℕ) : Selection Occ := ⟨[], [], (List.range n).map fun k => (factT, k)⟩

theorem makesAt_nodup (n : ℕ) : (makesAt n).made.Nodup :=
  (List.nodup_range).map fun _ _ same => by simpa using congrArg Prod.snd same

theorem makes_valid (n : ℕ) : (makesAt n).Valid ground Prod.fst (makes n) emptyStore where
  take_distinct := List.nodup_nil
  output_distinct := makesAt_nodup n
  take_length := rfl
  read_length := rfl
  outputs := by simp [makesAt, makes]
  occurrences := ⟨by simp [makesAt, Selection.commit], by simp [makesAt, Selection.commit],
    by simp [makesAt, Selection.commit], by simp [emptyStore],
    fun _ member => by simp [Selection.commit] at member⟩
  consistent := ⟨(), by simp [SubstitutionAction.Models, Selection.problem, Selection.equations,
    makesAt, makes, emptyStore]⟩
  checks := by simp [makes]

theorem makes_present (n : ℕ) :
    ((makesAt n).result Prod.fst (makes n) emptyStore).present = (makesAt n).made.toFinset := by
  simp [Selection.result, fire, Selection.commit, emptyStore]

theorem makes_bag (n : ℕ) :
    ((makesAt n).result Prod.fst (makes n) emptyStore).present.val.map Prod.fst =
      Multiset.replicate n factT := by
  rw [makes_present, Multiset.eq_replicate]
  constructor
  · rw [Multiset.card_map, Finset.card_val, List.toFinset_card_of_nodup (makesAt_nodup n)]
    simp [makesAt]
  · intro b member
    rw [Multiset.mem_map] at member
    obtain ⟨o, inside, rfl⟩ := member
    rw [Finset.mem_val, List.mem_toFinset] at inside
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp inside
    rfl

/-- **Where finitary covers fail: the unrestricted first-order step.** At the empty store every
`n` gives a successor with `n` copies of `T`; no finite set covers them up to bisimilarity. -/
theorem base_not_imageFiniteBisimilar : ¬ (stepSystem base storeView).ImageFiniteBisimilar := by
  intro finite
  obtain ⟨representatives, isFinite, covers⟩ := finite () emptyStore
  have reached : ∀ n : ℕ, ∃ r ∈ representatives, r.present.val.map Prod.fst = Multiset.replicate n factT := by
    intro n
    let f : Fir := ⟨makes n, [], makesAt n⟩
    have valid : f.Valid ground Prod.fst emptyStore :=
      (PredicateQueryAdmission.valid_empty_iff ground Prod.fst (makes n) emptyStore (makesAt n)).mpr
        (makes_valid n)
    have step : (stepSystem base storeView).act () emptyStore
        ((makesAt n).result Prod.fst (makes n) emptyStore) := ⟨f, valid, rfl⟩
    obtain ⟨r, member, relation, bisimulation, related⟩ := covers step
    have observed := (bisimulation.2.2 related (.inl (Multiset.replicate n factT))).mp (makes_bag n)
    exact ⟨r, member, observed⟩
  choose r inside bag using reached
  have injective : Function.Injective r := by
    intro n m same
    have bags := (bag n).symm.trans
      ((congrArg (fun C : Conf => C.present.val.map Prod.fst) same).trans (bag m))
    simpa using congrArg Multiset.card bags
  exact (Set.infinite_of_injective_forall_mem injective inside) isFinite

end Ground

#print axioms keeps_symm
#print axioms valid_rename
#print axioms result_rename
#print axioms program_succ_iff
#print axioms renamed_succ
#print axioms renamed_isBisimulation
#print axioms freshList
#print axioms exists_renaming
#print axioms listsOver_finite
#print axioms reps_finite
#print axioms covered
#print axioms program_imageFiniteBisimilar
#print axioms program_adequacy
#print axioms storeView_invariant
#print axioms ground_program_adequacy
#print axioms makes_valid
#print axioms makes_bag
#print axioms base_not_imageFiniteBisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy
