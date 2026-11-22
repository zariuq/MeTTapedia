import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CongruenceBisimilar

/-!
# The probes of the program-free step

The program-free step (`Semantic.ruleOffers`) offers every semantic firing under its rule. This
module lists the firings that test each ingredient of equivalence modulo the knowledge, and what
each one sees.

## Rule labels hide the queries

A firing admitted with predicate queries is admitted without them, under the same rule and with the
same result. So under rule labels the program-free step moves exactly as the occurrence step of the
rule (`moves_iff_step`), and the raw step, which also offers firings whose regions read labels
syntactically, has the same moves (`moves_raw_iff`).

## The probe rules

* **Quiet rules** take, read and make nothing (`Quiet`). Such a rule moves exactly when the
  knowledge with its tells is consistent and entails its checks, and it leaves the rows as they are
  (`moves_quiet_iff`). The guard (`guardRule`: an equation entailed by the knowledge,
  `moves_guard_iff`), the tell (`tellRule`: an equation consistent with it, `moves_tell_iff`), the
  absence check (`absentRule`, `moves_absent_iff`) and the count check (`countRule`,
  `moves_count_iff`) are quiet.
* **Takes** (`takeRule ps`): one row for each pattern, all distinct, with the matching equations
  consistent with the knowledge; the result removes the rows and keeps the matching equations
  (`moves_take_iff`).
* **Multiplicity and absence of a class**: the take of `k` copies of `p` moves to a configuration
  with the same solutions exactly when at least `k` rows carry labels that the knowledge entails
  equal to `p` (`moves_takeCopies_iff`); with `k = 1`, its failure is the absence of the class.

## The step restricted to rule forms

`formOffers A forms` offers the firings of the program-free step whose rule has one of the given
forms. Restricting by a property of labels keeps bisimulations (`bisimilar_formOffers`,
`bisimilar_formOffers_mono`). The **probe step** (`probeOffers`) offers guards and takes only.

## What bisimilar configurations of the probe step share

* the same consistency (`consistent_iff_of_bisimilar`, the take of no pattern);
* the same entailed equations (`entailed_iff_of_bisimilar`, the guard);
* the same solutions (`equivalent_of_bisimilar`: the guards on the equations of the other store);
* the same consistent extensions (`consistent_append_iff_of_bisimilar`, from the solutions);
* the bag of classes of the first inside the bag of the second (`bag_le_of_bisimilar`): the take of
  every row of the first under its own label must be answered by distinct rows of the second whose
  labels the knowledge entails equal, since the two results again have the same solutions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity

open AnnotatedRuns
open Semantic (ruleOffers rawOffers IsSemantic isSemantic_of_queries_nil)
open Observation (Entailed entailedSetoid)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## The probe rules -/

section Forms

/-- **The guard probe**: ask that the knowledge entails `l = r`. -/
def guardRule (l r : T) : RuleInstance T := ⟨[], [], [], [.equal l r], []⟩

/-- **The tell probe**: add `l = r` to the knowledge. -/
def tellRule (l r : T) : RuleInstance T := ⟨[], [], [(l, r)], [], []⟩

/-- **The absence probe**: ask that no row matches `p`, at every solution. -/
def absentRule (p : T) : RuleInstance T := ⟨[], [], [], [.predicate .none p], []⟩

/-- **The count probe**: ask that exactly `n` rows match `p`, at every solution. -/
def countRule (p : T) (n : ℕ) : RuleInstance T := ⟨[], [], [], [.count p n], []⟩

/-- **The take probe**: take one row for each pattern of `ps`. -/
def takeRule (ps : List T) : RuleInstance T := ⟨ps, [], [], [], []⟩

/-- **A quiet rule** takes, reads and makes nothing. -/
def Quiet (ρ : RuleInstance T) : Prop := ρ.take = [] ∧ ρ.read = [] ∧ ρ.produce = []

theorem quiet_guardRule (l r : T) : Quiet (guardRule l r) := ⟨rfl, rfl, rfl⟩
theorem quiet_tellRule (l r : T) : Quiet (tellRule l r) := ⟨rfl, rfl, rfl⟩
theorem quiet_absentRule (p : T) : Quiet (absentRule p) := ⟨rfl, rfl, rfl⟩
theorem quiet_countRule (p : T) (n : ℕ) : Quiet (countRule p n) := ⟨rfl, rfl, rfl⟩
theorem quiet_takeRule_nil : Quiet (takeRule ([] : List T)) := ⟨rfl, rfl, rfl⟩

/-- **The probe forms**: one equality guard, or a take. -/
def ProbeForm (ρ : RuleInstance T) : Prop := (∃ l r, ρ = guardRule l r) ∨ ∃ ps, ρ = takeRule ps

/-- A probe makes nothing. -/
theorem ProbeForm.produce_nil {ρ : RuleInstance T} (form : ProbeForm ρ) : ρ.produce = [] := by
  rcases form with ⟨l, r, rfl⟩ | ⟨ps, rfl⟩ <;> rfl

end Forms

/-! ## Rule labels hide the queries -/

section Moves

variable {A : SubstitutionAction T S} {label : O → T}

/-- **The program-free step moves as the occurrence step of the rule**: the queries of a firing
restrict nothing that its rule label shows. -/
theorem moves_iff_step {C C' : Configuration T O} {ρ : RuleInstance T} :
    Race.Moves A label (ruleOffers A) C ρ C' ↔ ConstraintMultisetRewriting.Step A label ρ C C' := by
  constructor
  · rintro ⟨f, ⟨rfl, -⟩, valid, rfl⟩
    exact ⟨f.selection, valid.firing, rfl⟩
  · rintro ⟨selection, valid, rfl⟩
    exact ⟨⟨ρ, [], selection⟩, ⟨rfl, isSemantic_of_queries_nil rfl⟩,
      PredicateQueryAdmission.regionValid_nil_iff.mpr valid, rfl⟩

/-- **The raw step has the same moves**: under rule labels, a region that reads labels
syntactically restricts nothing either. -/
theorem moves_raw_iff {C C' : Configuration T O} {ρ : RuleInstance T} :
    Race.Moves A label (rawOffers (S := S)) C ρ C' ↔ Race.Moves A label (ruleOffers A) C ρ C' := by
  constructor
  · rintro ⟨f, rfl, valid, rfl⟩
    exact ⟨⟨f.rule, [], f.selection⟩, ⟨rfl, isSemantic_of_queries_nil rfl⟩,
      PredicateQueryAdmission.regionValid_nil_iff.mpr valid.firing, rfl⟩
  · rintro ⟨f, ⟨rfl, -⟩, valid, rfl⟩
    exact ⟨f, rfl, valid, rfl⟩

/-- **Two programs with the same moves have the same bisimilarity.** -/
theorem bisimilar_congr_moves {L : Type*} {offers offers' : L → Firing T S O → Prop}
    (same : ∀ C ℓ C', Race.Moves A label offers C ℓ C' ↔ Race.Moves A label offers' C ℓ C')
    {C D : Configuration T O} :
    Race.Bisimilar A label offers C D ↔ Race.Bisimilar A label offers' C D := by
  constructor
  · rintro ⟨R, ⟨forward, backward, -⟩, related⟩
    refine ⟨R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
    · intro X Y rel ℓ X' moved
      obtain ⟨Y', moved', rel'⟩ := forward rel ℓ ((same X ℓ X').mpr moved)
      exact ⟨Y', (same Y ℓ Y').mp moved', rel'⟩
    · intro X Y rel ℓ Y' moved
      obtain ⟨X', moved', rel'⟩ := backward rel ℓ ((same Y ℓ Y').mpr moved)
      exact ⟨X', (same X ℓ X').mp moved', rel'⟩
  · rintro ⟨R, ⟨forward, backward, -⟩, related⟩
    refine ⟨R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
    · intro X Y rel ℓ X' moved
      obtain ⟨Y', moved', rel'⟩ := forward rel ℓ ((same X ℓ X').mp moved)
      exact ⟨Y', (same Y ℓ Y').mpr moved', rel'⟩
    · intro X Y rel ℓ Y' moved
      obtain ⟨X', moved', rel'⟩ := backward rel ℓ ((same Y ℓ Y').mp moved)
      exact ⟨X', (same X ℓ X').mpr moved', rel'⟩

/-- **Every move ends in consistent knowledge**, for every program: inconsistent configurations are
reached by no firing. -/
theorem consistent_of_moves {L : Type*} {offers : L → Firing T S O → Prop} {C C' : Configuration T O}
    {ℓ : L} (moved : Race.Moves A label offers C ℓ C') : A.Consistent C'.equations := by
  obtain ⟨f, -, valid, rfl⟩ := moved
  exact valid.firing.consistent

end Moves

/-! ## Quiet rules -/

section Quiet

variable {A : SubstitutionAction T S} {label : O → T}

/-- A selection admitted for a quiet rule selects nothing. -/
theorem selection_eq_of_quiet {ρ : RuleInstance T} (quiet : Quiet ρ) {C : Configuration T O}
    {selection : Selection O} (valid : selection.Valid A label ρ C) :
    selection = ⟨[], [], []⟩ := by
  have taken : selection.taken = [] := by
    have lengths := valid.take_length
    rw [quiet.1, List.length_nil] at lengths
    exact List.eq_nil_of_length_eq_zero lengths.symm
  have read : selection.read = [] := by
    have lengths := valid.read_length
    rw [quiet.2.1, List.length_nil] at lengths
    exact List.eq_nil_of_length_eq_zero lengths.symm
  have made : selection.made = [] := by
    have outputs := valid.outputs
    rw [quiet.2.2] at outputs
    exact List.map_eq_nil_iff.mp outputs
  cases selection with
  | mk t r m =>
      simp only at taken read made
      rw [taken, read, made]

omit [DecidableEq O] in
theorem problem_quiet (ρ : RuleInstance T) (C : Configuration T O) :
    (⟨[], [], []⟩ : Selection O).problem label ρ C = C.equations ++ ρ.tell := by
  simp [Selection.problem, Selection.equations]

theorem result_quiet (ρ : RuleInstance T) (C : Configuration T O) :
    (⟨[], [], []⟩ : Selection O).result label ρ C = ⟨C.equations ++ ρ.tell, C.present⟩ := by
  simp [Selection.result, Selection.problem, Selection.equations, fire, Selection.commit]

/-- **Admission of a quiet rule**: the knowledge with its tells is consistent and entails its
checks. -/
theorem valid_quiet_iff {ρ : RuleInstance T} (quiet : Quiet ρ) (C : Configuration T O) :
    (⟨[], [], []⟩ : Selection O).Valid A label ρ C ↔
      A.Consistent (C.equations ++ ρ.tell) ∧
        ∀ check ∈ ρ.checks, A.Entails (C.equations ++ ρ.tell) fun σ => check.Holds A σ label C.present := by
  constructor
  · intro valid
    refine ⟨?_, fun check member => ?_⟩
    · have consistent := valid.consistent
      rwa [problem_quiet] at consistent
    · have entailed := valid.checks check member
      rwa [problem_quiet] at entailed
  · rintro ⟨consistent, checks⟩
    refine ⟨List.nodup_nil, List.nodup_nil, by rw [quiet.1]; rfl, by rw [quiet.2.1]; rfl,
      by rw [quiet.2.2]; rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · rw [problem_quiet]
      exact consistent
    · intro check member
      rw [problem_quiet]
      exact checks check member

/-- **A quiet rule moves** exactly when the knowledge with its tells is consistent and entails its
checks, and it adds its tells and leaves the rows as they are. -/
theorem moves_quiet_iff {ρ : RuleInstance T} (quiet : Quiet ρ) {C C' : Configuration T O} :
    Race.Moves A label (ruleOffers A) C ρ C' ↔
      (A.Consistent (C.equations ++ ρ.tell) ∧
        ∀ check ∈ ρ.checks, A.Entails (C.equations ++ ρ.tell) fun σ => check.Holds A σ label C.present) ∧
      C' = ⟨C.equations ++ ρ.tell, C.present⟩ := by
  rw [moves_iff_step]
  constructor
  · rintro ⟨selection, valid, rfl⟩
    obtain rfl := selection_eq_of_quiet quiet valid
    exact ⟨(valid_quiet_iff quiet C).mp valid, result_quiet ρ C⟩
  · rintro ⟨admits, rfl⟩
    exact ⟨⟨[], [], []⟩, (valid_quiet_iff quiet C).mpr admits, (result_quiet ρ C).symm⟩

/-- **The guard probe** moves exactly at consistent configurations whose knowledge entails `l = r`,
and changes nothing. -/
theorem moves_guard_iff {l r : T} {C C' : Configuration T O} :
    Race.Moves A label (ruleOffers A) C (guardRule l r) C' ↔
      (A.Consistent C.equations ∧ Entailed A C.equations l r) ∧ C' = C := by
  rw [moves_quiet_iff (quiet_guardRule l r)]
  simp only [guardRule, List.append_nil, List.mem_singleton, forall_eq]
  exact Iff.rfl

/-- **The tell probe** moves exactly when `l = r` is consistent with the knowledge, and adds it. -/
theorem moves_tell_iff {l r : T} {C C' : Configuration T O} :
    Race.Moves A label (ruleOffers A) C (tellRule l r) C' ↔
      A.Consistent (C.equations ++ [(l, r)]) ∧ C' = ⟨C.equations ++ [(l, r)], C.present⟩ := by
  rw [moves_quiet_iff (quiet_tellRule l r)]
  simp [tellRule]

/-- **The absence probe** moves exactly at consistent configurations whose knowledge entails that no
row matches `p`, and changes nothing. -/
theorem moves_absent_iff {p : T} {C C' : Configuration T O} :
    Race.Moves A label (ruleOffers A) C (absentRule p) C' ↔
      (A.Consistent C.equations ∧
        A.Entails C.equations fun σ => ∀ o ∈ C.present, ¬ A.E (A.apply σ p) (A.apply σ (label o))) ∧
      C' = C := by
  rw [moves_quiet_iff (quiet_absentRule p)]
  simp only [absentRule, List.append_nil, List.mem_singleton, forall_eq]
  exact Iff.rfl

/-- **The count probe** moves exactly at consistent configurations whose knowledge entails that
exactly `n` rows match `p`, and changes nothing. -/
theorem moves_count_iff {p : T} {n : ℕ} {C C' : Configuration T O} :
    Race.Moves A label (ruleOffers A) C (countRule p n) C' ↔
      (A.Consistent C.equations ∧
        A.Entails C.equations fun σ => (Check.matches A σ label C.present p).card = n) ∧
      C' = C := by
  rw [moves_quiet_iff (quiet_countRule p n)]
  simp only [countRule, List.append_nil, List.mem_singleton, forall_eq]
  exact Iff.rfl

/-- **The empty take** moves exactly at consistent configurations, and changes nothing. -/
theorem moves_takeNil_iff {C C' : Configuration T O} :
    Race.Moves A label (ruleOffers A) C (takeRule []) C' ↔ A.Consistent C.equations ∧ C' = C := by
  rw [moves_quiet_iff quiet_takeRule_nil]
  simp [takeRule]

end Quiet

/-! ## Takes -/

section Takes

variable {A : SubstitutionAction T S} {label : O → T}

omit [DecidableEq O] in
theorem problem_take (ps : List T) (taken : List O) (C : Configuration T O) :
    (⟨taken, [], []⟩ : Selection O).problem label (takeRule ps) C =
      C.equations ++ Selection.equations label ps taken := by
  simp [Selection.problem, Selection.equations, takeRule]

theorem result_take (ps : List T) (taken : List O) (C : Configuration T O) :
    (⟨taken, [], []⟩ : Selection O).result label (takeRule ps) C =
      ⟨C.equations ++ Selection.equations label ps taken, C.present \ taken.toFinset⟩ := by
  simp [Selection.result, Selection.problem, Selection.equations, takeRule, fire, Selection.commit]

/-- **The take probe** moves exactly when distinct present rows, one for each pattern, have matching
equations consistent with the knowledge; it removes them and keeps the matching equations. -/
theorem moves_take_iff {ps : List T} {C C' : Configuration T O} :
    Race.Moves A label (ruleOffers A) C (takeRule ps) C' ↔
      ∃ taken : List O, taken.Nodup ∧ ps.length = taken.length ∧ (∀ o ∈ taken, o ∈ C.present) ∧
        A.Consistent (C.equations ++ Selection.equations label ps taken) ∧
        C' = ⟨C.equations ++ Selection.equations label ps taken, C.present \ taken.toFinset⟩ := by
  rw [moves_iff_step]
  constructor
  · rintro ⟨⟨taken, read, made⟩, valid, rfl⟩
    have readNil : read = [] := by
      have lengths := valid.read_length
      exact List.eq_nil_of_length_eq_zero lengths.symm
    have madeNil : made = [] := List.map_eq_nil_iff.mp valid.outputs
    subst readNil madeNil
    refine ⟨taken, valid.take_distinct, valid.take_length, fun o member =>
      valid.occurrences.taken_subset (List.mem_toFinset.mpr member), ?_, result_take ps taken C⟩
    have consistent := valid.consistent
    rwa [problem_take] at consistent
  · rintro ⟨taken, nodup, lengths, inside, consistent, rfl⟩
    refine ⟨⟨taken, [], []⟩, ⟨nodup, List.nodup_nil, lengths, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩,
      (result_take ps taken C).symm⟩
    · intro o member
      exact inside o (List.mem_toFinset.mp member)
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · rw [problem_take]
      exact consistent
    · intro check member
      simp [takeRule] at member

omit [DecidableEq O] in
/-- **The matching equations of rows under their own labels hold at every substitution**: they have
equal sides (`Race.reflexive_equations`). -/
theorem models_self (σ : S) (l : List O) : A.Models σ (Selection.equations label (l.map label) l) :=
  fun e member => by
    show A.E (A.apply σ e.1) (A.apply σ e.2)
    rw [Race.reflexive_equations label l e member]
    exact A.equivalence.refl _

/-- **Every configuration with consistent knowledge can take all its rows under their own labels.** -/
theorem moves_takeAll {C : Configuration T O} (consistent : A.Consistent C.equations) :
    Race.Moves A label (ruleOffers A) C (takeRule (C.present.toList.map label))
      ⟨C.equations ++ Selection.equations label (C.present.toList.map label) C.present.toList, ∅⟩ := by
  refine moves_take_iff.mpr ⟨C.present.toList, C.present.nodup_toList, List.length_map _,
    fun o member => Finset.mem_toList.mp member, ?_, ?_⟩
  · obtain ⟨σ, solved⟩ := consistent
    exact ⟨σ, (A.models_append _ _ _).mpr ⟨solved, models_self σ _⟩⟩
  · rw [Finset.toList_toFinset, Finset.sdiff_self]

omit [DecidableEq O] in
/-- The matching equations of copies of one pattern. -/
theorem equations_replicate (t : T) : ∀ taken : List O,
    Selection.equations label (List.replicate taken.length t) taken = taken.map fun o => (t, label o)
  | [] => rfl
  | o :: rest => by
      rw [List.length_cons, List.replicate_succ, List.map_cons, ← equations_replicate t rest]
      rfl

open Classical in
/-- **The multiplicity probe**: the take of `k` copies of `t` moves to a configuration with the same
solutions exactly when at least `k` rows carry labels that the knowledge entails equal to `t`. With
`k = 1` it is the absence probe of a class: no such move exactly when no row is in the class of
`t`. -/
theorem moves_takeCopies_iff {t : T} {k : ℕ} {C : Configuration T O}
    (consistent : A.Consistent C.equations) :
    (∃ C', Race.Moves A label (ruleOffers A) C (takeRule (List.replicate k t)) C' ∧
        A.Equivalent C'.equations C.equations) ↔
      k ≤ (C.present.filter fun o => Entailed A C.equations t (label o)).card := by
  constructor
  · rintro ⟨C', moved, same⟩
    obtain ⟨taken, nodup, lengths, inside, -, rfl⟩ := moves_take_iff.mp moved
    rw [List.length_replicate] at lengths
    subst lengths
    have entailed : ∀ o ∈ taken, Entailed A C.equations t (label o) := by
      intro o member σ solved
      have all := ((A.models_append _ _ _).mp ((same σ).mpr solved)).2
      rw [equations_replicate] at all
      exact all _ (List.mem_map_of_mem member)
    calc taken.length = taken.toFinset.card := (List.toFinset_card_of_nodup nodup).symm
      _ ≤ _ := Finset.card_le_card fun o member => Finset.mem_filter.mpr
          ⟨inside o (List.mem_toFinset.mp member), entailed o (List.mem_toFinset.mp member)⟩
  · intro enough
    obtain ⟨s, within, size⟩ := Finset.exists_subset_card_eq enough
    have entailed : ∀ o ∈ s.toList, Entailed A C.equations t (label o) := fun o member =>
      (Finset.mem_filter.mp (within (Finset.mem_toList.mp member))).2
    have solves : ∀ σ, A.Models σ C.equations →
        A.Models σ (Selection.equations label (List.replicate k t) s.toList) := by
      intro σ solved
      rw [← size, ← Finset.length_toList, equations_replicate]
      intro e member
      obtain ⟨o, inList, rfl⟩ := List.mem_map.mp member
      exact entailed o inList σ solved
    refine ⟨_, moves_take_iff.mpr ⟨s.toList, s.nodup_toList,
      by rw [List.length_replicate, Finset.length_toList, size],
      fun o member => (Finset.mem_filter.mp (within (Finset.mem_toList.mp member))).1, ?_, rfl⟩,
      fun σ => ?_⟩
    · obtain ⟨σ, solved⟩ := consistent
      exact ⟨σ, (A.models_append _ _ _).mpr ⟨solved, solves σ solved⟩⟩
    · exact ⟨fun solved => ((A.models_append _ _ _).mp solved).1,
        fun solved => (A.models_append _ _ _).mpr ⟨solved, solves σ solved⟩⟩

omit [DecidableEq O] in
/-- **Rows matched under consistent entailment have entailed-equal labels**: if every solution of
`K` solves the matching equations of `ps` against `taken`, then the patterns and the labels of the
taken rows have the same classes in every equivalence that contains what `K` entails. -/
theorem map_mk_eq_of_entails {K : EquationStore T} {r : Setoid T}
    (coarser : entailedSetoid A K ≤ r) :
    ∀ (ps : List T) (taken : List O), ps.length = taken.length →
      (∀ σ, A.Models σ K → A.Models σ (Selection.equations label ps taken)) →
        ps.map (Quotient.mk r) = taken.map fun o => Quotient.mk r (label o)
  | [], [], _, _ => rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | p :: ps, o :: taken, lengths, entails => by
      have split : ∀ σ, A.Models σ K →
          A.Solves σ (p, label o) ∧ A.Models σ (Selection.equations label ps taken) := by
        intro σ solved
        have both := entails σ solved
        simp only [Selection.equations, List.zipWith_cons_cons, SubstitutionAction.models_cons]
          at both
        exact both
      have head : Entailed A K p (label o) := fun σ solved => (split σ solved).1
      have tail := map_mk_eq_of_entails coarser ps taken (Nat.succ.inj lengths)
        fun σ solved => (split σ solved).2
      rw [List.map_cons, List.map_cons, tail, Quotient.sound (Setoid.le_def.mp coarser head)]

end Takes

/-! ## The step restricted to rule forms -/

section Restrict

variable (A : SubstitutionAction T S)

/-- **The program-free step restricted to rules of the given forms.** -/
def formOffers (forms : RuleInstance T → Prop) (ρ : RuleInstance T) (f : Firing T S O) : Prop :=
  forms ρ ∧ ruleOffers A ρ f

/-- **The probe step**: guards and takes only. -/
abbrev probeOffers : RuleInstance T → Firing T S O → Prop := formOffers A ProbeForm

variable {A} {label : O → T}

theorem moves_formOffers_iff {forms : RuleInstance T → Prop} {C C' : Configuration T O}
    {ρ : RuleInstance T} :
    Race.Moves A label (formOffers A forms) C ρ C' ↔ forms ρ ∧ Race.Moves A label (ruleOffers A) C ρ C' :=
  ⟨fun ⟨f, ⟨form, offered⟩, valid, result⟩ => ⟨form, f, offered, valid, result⟩,
    fun ⟨form, f, offered, valid, result⟩ => ⟨f, ⟨form, offered⟩, valid, result⟩⟩

/-- **Restricting by labels keeps bisimulations**: bisimilar configurations of the program-free
step are bisimilar for every restriction of it to rule forms. -/
theorem bisimilar_formOffers {forms : RuleInstance T → Prop} {C D : Configuration T O}
    (h : Race.Bisimilar A label (ruleOffers A) C D) : Race.Bisimilar A label (formOffers A forms) C D := by
  obtain ⟨R, ⟨forward, backward, -⟩, related⟩ := h
  refine ⟨R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
  · intro X Y rel ρ X' moved
    obtain ⟨form, moved⟩ := moves_formOffers_iff.mp moved
    obtain ⟨Y', moved', rel'⟩ := forward rel ρ moved
    exact ⟨Y', moves_formOffers_iff.mpr ⟨form, moved'⟩, rel'⟩
  · intro X Y rel ρ Y' moved
    obtain ⟨form, moved⟩ := moves_formOffers_iff.mp moved
    obtain ⟨X', moved', rel'⟩ := backward rel ρ moved
    exact ⟨X', moves_formOffers_iff.mpr ⟨form, moved'⟩, rel'⟩

/-- **Fewer forms, coarser bisimilarity.** -/
theorem bisimilar_formOffers_mono {forms forms' : RuleInstance T → Prop}
    (fewer : ∀ ρ, forms' ρ → forms ρ) {C D : Configuration T O}
    (h : Race.Bisimilar A label (formOffers A forms) C D) :
    Race.Bisimilar A label (formOffers A forms') C D := by
  obtain ⟨R, ⟨forward, backward, -⟩, related⟩ := h
  refine ⟨R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
  · intro X Y rel ρ X' moved
    obtain ⟨form, moved⟩ := moves_formOffers_iff.mp moved
    obtain ⟨Y', moved', rel'⟩ := forward rel ρ (moves_formOffers_iff.mpr ⟨fewer ρ form, moved⟩)
    exact ⟨Y', moves_formOffers_iff.mpr ⟨form, (moves_formOffers_iff.mp moved').2⟩, rel'⟩
  · intro X Y rel ρ Y' moved
    obtain ⟨form, moved⟩ := moves_formOffers_iff.mp moved
    obtain ⟨X', moved', rel'⟩ := backward rel ρ (moves_formOffers_iff.mpr ⟨fewer ρ form, moved⟩)
    exact ⟨X', moves_formOffers_iff.mpr ⟨form, (moves_formOffers_iff.mp moved').2⟩, rel'⟩

end Restrict

/-! ## What bisimilar configurations of the probe step share -/

section Shared

variable {A : SubstitutionAction T S} {label : O → T} {C D : Configuration T O}

theorem probe_guard (l r : T) : ProbeForm (guardRule l r) := Or.inl ⟨l, r, rfl⟩
theorem probe_take (ps : List T) : ProbeForm (takeRule ps) := Or.inr ⟨ps, rfl⟩

theorem bisimilar_symm (h : Race.Bisimilar A label (probeOffers A) C D) :
    Race.Bisimilar A label (probeOffers A) D C :=
  (Race.system A label (probeOffers A)).bisimilar_symm h

/-- **Bisimilar configurations are consistent together**: the empty take moves exactly at consistent
configurations. -/
theorem consistent_iff_of_bisimilar (h : Race.Bisimilar A label (probeOffers A) C D) :
    A.Consistent C.equations ↔ A.Consistent D.equations := by
  have transfer : ∀ {X Y : Configuration T O}, Race.Bisimilar A label (probeOffers A) X Y →
      A.Consistent X.equations → A.Consistent Y.equations := by
    intro X Y bisimilar consistent
    obtain ⟨R, ⟨forward, -, -⟩, related⟩ := bisimilar
    obtain ⟨Y', moved, -⟩ := forward related (takeRule [])
      (moves_formOffers_iff.mpr ⟨probe_take [], moves_takeNil_iff.mpr ⟨consistent, rfl⟩⟩)
    exact (moves_takeNil_iff.mp (moves_formOffers_iff.mp moved).2).1
  exact ⟨transfer h, transfer (bisimilar_symm h)⟩

/-- **Bisimilar configurations entail the same equations**: the guard. -/
theorem entailed_iff_of_bisimilar (h : Race.Bisimilar A label (probeOffers A) C D)
    (consistent : A.Consistent C.equations) (l r : T) :
    Entailed A C.equations l r ↔ Entailed A D.equations l r := by
  have transfer : ∀ {X Y : Configuration T O}, Race.Bisimilar A label (probeOffers A) X Y →
      A.Consistent X.equations → Entailed A X.equations l r → Entailed A Y.equations l r := by
    intro X Y bisimilar consistentX entailed
    obtain ⟨R, ⟨forward, -, -⟩, related⟩ := bisimilar
    obtain ⟨Y', moved, -⟩ := forward related (guardRule l r)
      (moves_formOffers_iff.mpr ⟨probe_guard l r, moves_guard_iff.mpr ⟨⟨consistentX, entailed⟩, rfl⟩⟩)
    exact (moves_guard_iff.mp (moves_formOffers_iff.mp moved).2).1.2
  exact ⟨transfer h consistent,
    transfer (bisimilar_symm h) ((consistent_iff_of_bisimilar h).mp consistent)⟩

/-- **Bisimilar configurations have the same solutions**: each side entails the equations of the
other side's knowledge. -/
theorem equivalent_of_bisimilar (h : Race.Bisimilar A label (probeOffers A) C D)
    (consistent : A.Consistent C.equations) : A.Equivalent C.equations D.equations := by
  intro σ
  constructor
  · intro solved e member
    have atD : Entailed A D.equations e.1 e.2 := fun τ solvedτ => solvedτ e member
    exact (entailed_iff_of_bisimilar h consistent e.1 e.2).mpr atD σ solved
  · intro solved e member
    have atC : Entailed A C.equations e.1 e.2 := fun τ solvedτ => solvedτ e member
    exact (entailed_iff_of_bisimilar h consistent e.1 e.2).mp atC σ solved

/-- **Bisimilar configurations have the same consistent extensions**: the tell. -/
theorem consistent_append_iff_of_bisimilar (h : Race.Bisimilar A label (probeOffers A) C D)
    (consistent : A.Consistent C.equations) (K : EquationStore T) :
    A.Consistent (C.equations ++ K) ↔ A.Consistent (D.equations ++ K) :=
  SubstitutionAction.equivalent_consistent A
    (GuardFreeProcessOrders.equivalent_append A (equivalent_of_bisimilar h consistent) K)

/-- **Bisimilar configurations agree on absence**: a consequence of the same solutions and the same
bag, here read directly from the absence check of the program-free step. -/
theorem absent_iff_of_bisimilar (h : Race.Bisimilar A label (ruleOffers A) C D) (p : T) :
    (A.Consistent C.equations ∧
        A.Entails C.equations fun σ => ∀ o ∈ C.present, ¬ A.E (A.apply σ p) (A.apply σ (label o))) ↔
      (A.Consistent D.equations ∧
        A.Entails D.equations fun σ => ∀ o ∈ D.present, ¬ A.E (A.apply σ p) (A.apply σ (label o))) := by
  obtain ⟨R, ⟨forward, backward, -⟩, related⟩ := h
  constructor
  · intro absent
    obtain ⟨D', moved, -⟩ := forward related (absentRule p) (moves_absent_iff.mpr ⟨absent, rfl⟩)
    exact (moves_absent_iff.mp moved).1
  · intro absent
    obtain ⟨C', moved, -⟩ := backward related (absentRule p) (moves_absent_iff.mpr ⟨absent, rfl⟩)
    exact (moves_absent_iff.mp moved).1

/-- **The bag of the first inside the bag of the second.** The first takes every row under its own
label; the second must answer with distinct rows; the two results have the same solutions again, so
every solution of the second solves the matching equations, and the matched labels are entailed
equal. Classes are taken in any equivalence that contains what the second's knowledge entails. -/
theorem bag_le_of_bisimilar (h : Race.Bisimilar A label (probeOffers A) C D)
    (consistent : A.Consistent C.equations) (r : Setoid T)
    (coarser : entailedSetoid A D.equations ≤ r) :
    C.present.val.map (fun o => Quotient.mk r (label o)) ≤
      D.present.val.map (fun o => Quotient.mk r (label o)) := by
  set l := C.present.toList with hl
  have same := equivalent_of_bisimilar h consistent
  obtain ⟨R, bisimulation, related⟩ := h
  obtain ⟨D₁, movedD, related₁⟩ := bisimulation.1 related (takeRule (l.map label))
    (moves_formOffers_iff.mpr ⟨probe_take _, moves_takeAll consistent⟩)
  obtain ⟨taken, nodup, lengths, inside, -, rfl⟩ := moves_take_iff.mp (moves_formOffers_iff.mp movedD).2
  have consistent₁ : A.Consistent (C.equations ++ Selection.equations label (l.map label) l) := by
    obtain ⟨σ, solved⟩ := consistent
    exact ⟨σ, (A.models_append _ _ _).mpr ⟨solved, models_self σ l⟩⟩
  have same₁ := equivalent_of_bisimilar (C := ⟨_, ∅⟩) ⟨R, bisimulation, related₁⟩ consistent₁
  have matched : ∀ σ, A.Models σ D.equations →
      A.Models σ (Selection.equations label (l.map label) taken) := by
    intro σ solvedD
    have solvedC₁ : A.Models σ (C.equations ++ Selection.equations label (l.map label) l) :=
      (A.models_append _ _ _).mpr ⟨(same σ).mpr solvedD, models_self σ l⟩
    exact ((A.models_append _ _ _).mp ((same₁ σ).mp solvedC₁)).2
  have lists := map_mk_eq_of_entails coarser (l.map label) taken lengths matched
  rw [List.map_map] at lists
  have bagC : C.present.val.map (fun o => Quotient.mk r (label o)) =
      (↑(taken.map fun o => Quotient.mk r (label o)) : Multiset (Quotient r)) := by
    rw [← lists, ← Multiset.map_coe, hl, Finset.coe_toList]
    rfl
  rw [bagC, ← Multiset.map_coe]
  refine Multiset.map_le_map ((Multiset.le_iff_subset (Multiset.coe_nodup.mpr nodup)).mpr ?_)
  intro o member
  exact Finset.mem_val.mpr (inside o (Multiset.mem_coe.mp member))

end Shared

#print axioms moves_iff_step
#print axioms moves_raw_iff
#print axioms bisimilar_congr_moves
#print axioms consistent_of_moves
#print axioms moves_quiet_iff
#print axioms moves_guard_iff
#print axioms moves_tell_iff
#print axioms moves_absent_iff
#print axioms moves_count_iff
#print axioms moves_takeNil_iff
#print axioms moves_take_iff
#print axioms moves_takeAll
#print axioms equations_replicate
#print axioms moves_takeCopies_iff
#print axioms map_mk_eq_of_entails
#print axioms bisimilar_formOffers
#print axioms bisimilar_formOffers_mono
#print axioms consistent_iff_of_bisimilar
#print axioms entailed_iff_of_bisimilar
#print axioms equivalent_of_bisimilar
#print axioms consistent_append_iff_of_bisimilar
#print axioms absent_iff_of_bisimilar
#print axioms bag_le_of_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity
