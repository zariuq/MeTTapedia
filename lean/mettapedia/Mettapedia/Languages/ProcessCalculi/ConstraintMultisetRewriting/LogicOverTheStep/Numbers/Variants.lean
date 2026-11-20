import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.OnTheStep

/-!
# Re-storing any numeral, one position at a time

`OnTheStep` re-stores every numeral of a program by one map of storages, labels and made rows
included. This module re-stores numerals position by position: any numeral of the patterns, the
tells and the checks of each rule, of the knowledge, and of the query, each independently, with a
table that respects the value lens.

* **Variants** of stores, checks, rules and programs (`StoreVariant`, `CheckVariant`, `RuleVariant`,
  `ProgramVariant`): the same up to the storage of numerals, position by position. The rows a rule
  makes keep their numerals here: a made row must be the label of the identity it is made at, and
  labels are re-stored together with made rows by `OnTheStep.step_restore`.
* **Every step of a program has a step of each variant program** from each variant configuration,
  to a variant configuration (`step_variant`); variants are symmetric (`RuleVariant.symm`,
  `ProgramVariant.symm`), so this is a bisimulation.
* **Answers are the same** at variant configurations for variant checks, counts and predicate
  queries alike (`answer_variant`), and so are **the answers reachable by runs**
  (`program_answers_variant`, `program_every_answer_variant`).
* **Witness and control**: the rule that takes `(foo $x)`, checks that `(foo 5)` is counted once and
  makes `(bar (+ $x 1))` fires from `(foo 5)` (`countRule_fires`), and its variant that checks
  `(foo 5.0)` instead (`countRule_variant`) fires exactly when it does (`countRule_fires_iff`). With
  the storage-dependent division the one-row control `OnTheStep.division_one_row` shows that the
  respect hypothesis is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Variants

open Distinctions.NumberLens Tower OnTheStep

/-! ## Lists related position by position -/

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List α} {l₄ : List β},
      List.Forall₂ R l₁ l₂ → List.Forall₂ R l₃ l₄ → List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | _, _, _, _, .nil, rest => rest
  | _, _, _, _, .cons related tail, rest => .cons related (forall₂_append tail rest)

theorem forall₂_symm {α : Type} {R : α → α → Prop} (symm : ∀ a b, R a b → R b a) :
    ∀ {l l' : List α}, List.Forall₂ R l l' → List.Forall₂ R l' l
  | _, _, .nil => .nil
  | _, _, .cons related tail => .cons (symm _ _ related) (forall₂_symm symm tail)

theorem exists_left_of_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {b : β}, b ∈ l' → ∃ a ∈ l, R a b
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, .cons related tail, _, member => by
      rcases List.mem_cons.mp member with rfl | inside
      · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), related⟩
      · obtain ⟨a, inA, relatedA⟩ := exists_left_of_mem tail inside
        exact ⟨a, List.mem_cons.mpr (Or.inr inA), relatedA⟩

/-! ## Variants -/

theorem variant_symm {s t : NTerm Stored} (same : Variant s t) : Variant t s :=
  (show s.map value = t.map value from same).symm

/-- **Storage variants of stores**, equation by equation. -/
def StoreVariant (K K' : EquationStore (NTerm Stored)) : Prop :=
  List.Forall₂ (fun e e' => Variant e.1 e'.1 ∧ Variant e.2 e'.2) K K'

/-- **Storage variants of checks.** -/
def CheckVariant : Check (NTerm Stored) → Check (NTerm Stored) → Prop
  | .equal l r, .equal l' r' => Variant l l' ∧ Variant r r'
  | .predicate quantifier p, .predicate quantifier' p' => quantifier = quantifier' ∧ Variant p p'
  | .count p n, .count p' n' => Variant p p' ∧ n = n'
  | _, _ => False

/-- **Storage variants of rules**: patterns, tells and checks, position by position; the made rows
are kept. -/
structure RuleVariant (rule rule' : RuleInstance (NTerm Stored)) : Prop where
  take : List.Forall₂ Variant rule.take rule'.take
  read : List.Forall₂ Variant rule.read rule'.read
  tell : StoreVariant rule.tell rule'.tell
  checks : List.Forall₂ CheckVariant rule.checks rule'.checks
  produce : rule.produce = rule'.produce

/-- **Storage variants of programs**: every rule of each has a variant in the other. -/
def ProgramVariant (R R' : Set (RuleInstance (NTerm Stored))) : Prop :=
  (∀ rule ∈ R, ∃ rule' ∈ R', RuleVariant rule rule') ∧ ∀ rule' ∈ R', ∃ rule ∈ R, RuleVariant rule rule'

theorem storeVariant_symm {K K' : EquationStore (NTerm Stored)} (same : StoreVariant K K') :
    StoreVariant K' K :=
  forall₂_symm (fun _ _ related => ⟨variant_symm related.1, variant_symm related.2⟩) same

theorem checkVariant_symm : ∀ {c c' : Check (NTerm Stored)}, CheckVariant c c' → CheckVariant c' c
  | .equal _ _, .equal _ _, related => ⟨variant_symm related.1, variant_symm related.2⟩
  | .predicate _ _, .predicate _ _, related => ⟨related.1.symm, variant_symm related.2⟩
  | .count _ _, .count _ _, related => ⟨variant_symm related.1, related.2.symm⟩
  | .equal _ _, .predicate _ _, related => related.elim
  | .equal _ _, .count _ _, related => related.elim
  | .predicate _ _, .equal _ _, related => related.elim
  | .predicate _ _, .count _ _, related => related.elim
  | .count _ _, .equal _ _, related => related.elim
  | .count _ _, .predicate _ _, related => related.elim

theorem RuleVariant.symm {rule rule' : RuleInstance (NTerm Stored)} (related : RuleVariant rule rule') :
    RuleVariant rule' rule :=
  ⟨forall₂_symm (fun _ _ same => variant_symm same) related.take,
    forall₂_symm (fun _ _ same => variant_symm same) related.read, storeVariant_symm related.tell,
    forall₂_symm (fun _ _ same => checkVariant_symm same) related.checks, related.produce.symm⟩

theorem ProgramVariant.symm {R R' : Set (RuleInstance (NTerm Stored))} (related : ProgramVariant R R') :
    ProgramVariant R' R :=
  ⟨fun rule' inside => by
      obtain ⟨rule, member, same⟩ := related.2 rule' inside
      exact ⟨rule, member, same.symm⟩,
    fun rule inside => by
      obtain ⟨rule', member, same⟩ := related.1 rule inside
      exact ⟨rule', member, same.symm⟩⟩

/-! ## What the knowledge sees -/

variable {G : Table}

theorem models_variant (respects : TableRespects G) (σ : ℕ → NTerm Stored)
    {K K' : EquationStore (NTerm Stored)} (same : StoreVariant K K') :
    (action G).Models σ K ↔ (action G).Models σ K' := by
  induction same with
  | nil => exact Iff.rfl
  | cons related _ ih =>
      rw [SubstitutionAction.models_cons, SubstitutionAction.models_cons, ih]
      exact and_congr_left' (identified_congr
        (identified_subst (identified_of_variant respects related.1) σ)
        (identified_subst (identified_of_variant respects related.2) σ))

theorem holds_variant {O : Type} (respects : TableRespects G) (σ : ℕ → NTerm Stored)
    (label : O → NTerm Stored) (store : Finset O) {c c' : Check (NTerm Stored)}
    (related : CheckVariant c c') :
    c.Holds (action G) σ label store ↔ c'.Holds (action G) σ label store := by
  cases c with
  | equal l r =>
      cases c' with
      | equal l' r' =>
          exact identified_congr (identified_subst (identified_of_variant respects related.1) σ)
            (identified_subst (identified_of_variant respects related.2) σ)
      | predicate quantifier _ => exact related.elim
      | count _ _ => exact related.elim
  | predicate quantifier p =>
      cases c' with
      | equal _ _ => exact related.elim
      | predicate quantifier' p' =>
          obtain ⟨rfl, related⟩ := related
          have pattern := identified_subst (identified_of_variant respects related) σ
          show quantifier.Holds store _ ↔ quantifier.Holds store _
          exact quantifier.holds_congr fun _ _ => identified_congr pattern fun _ => rfl
      | count _ _ => exact related.elim
  | count p n =>
      cases c' with
      | equal _ _ => exact related.elim
      | predicate quantifier _ => exact related.elim
      | count p' n' =>
          obtain ⟨pattern, rfl⟩ := related
          have equal := matches_congr (store := store) (label := label) (label' := label)
            (identified_subst (identified_of_variant respects pattern) σ) (fun _ _ => rfl)
          show (Check.«matches» (action G) σ label store p).card = n ↔
            (Check.«matches» (action G) σ label store p').card = n
          rw [equal]

theorem equations_variant {O : Type} (label : O → NTerm Stored) :
    ∀ {ps ps' : List (NTerm Stored)}, List.Forall₂ Variant ps ps' → ∀ selected : List O,
      StoreVariant (Selection.equations label ps selected) (Selection.equations label ps' selected)
  | _, _, .nil, selected => by
      cases selected <;> exact List.Forall₂.nil
  | _, _, .cons related tail, selected => by
      cases selected with
      | nil => exact List.Forall₂.nil
      | cons o os => exact List.Forall₂.cons ⟨related, rfl⟩ (equations_variant label tail os)

theorem problem_variant {O : Type} (label : O → NTerm Stored) (sel : Selection O)
    {rule rule' : RuleInstance (NTerm Stored)} (related : RuleVariant rule rule')
    {C C' : Configuration (NTerm Stored) O} (same : StoreVariant C.equations C'.equations) :
    StoreVariant (sel.problem label rule C) (sel.problem label rule' C') :=
  forall₂_append (forall₂_append (forall₂_append same (equations_variant label related.take sel.taken))
    (equations_variant label related.read sel.read)) related.tell

/-- **Answers are the same at variant configurations, for variant checks.** -/
theorem answer_variant {O : Type} (respects : TableRespects G) (label : O → NTerm Stored)
    {C C' : Configuration (NTerm Stored) O} (same : StoreVariant C.equations C'.equations)
    (present : C.present = C'.present) {c c' : Check (NTerm Stored)} (related : CheckVariant c c') :
    Answer G label C c ↔ Answer G label C' c' := by
  constructor
  · intro answered σ solved
    rw [← present]
    exact (holds_variant respects σ label C.present related).mp
      (answered σ ((models_variant respects σ same).mpr solved))
  · intro answered σ solved
    have holds := answered σ ((models_variant respects σ same).mp solved)
    rw [← present] at holds
    exact (holds_variant respects σ label C.present related).mpr holds

/-! ## Steps and runs -/

/-- **Every step has a step of each variant rule from each variant configuration.** -/
theorem step_variant {O : Type} [DecidableEq O] (respects : TableRespects G) {label : O → NTerm Stored}
    {rule rule' : RuleInstance (NTerm Stored)} (related : RuleVariant rule rule')
    {C C' D : Configuration (NTerm Stored) O} (same : StoreVariant C.equations C'.equations)
    (present : C.present = C'.present) (step : Step (action G) label rule C D) :
    ∃ D', Step (action G) label rule' C' D' ∧ StoreVariant D.equations D'.equations ∧
      D.present = D'.present := by
  obtain ⟨sel, valid, rfl⟩ := step
  have problems := problem_variant label sel related same
  refine ⟨sel.result label rule' C',
    ⟨sel, ⟨valid.take_distinct, valid.output_distinct, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩, problems, ?_⟩
  · exact related.take.length_eq.symm.trans valid.take_length
  · exact related.read.length_eq.symm.trans valid.read_length
  · rw [← related.produce]
    exact valid.outputs
  · rw [← present]
    exact valid.occurrences
  · obtain ⟨σ, solved⟩ := valid.consistent
    exact ⟨σ, (models_variant respects σ problems).mp solved⟩
  · intro check' member σ solved
    obtain ⟨check, inside, relatedCheck⟩ := exists_left_of_mem related.checks member
    have holds := valid.checks check inside σ ((models_variant respects σ problems).mpr solved)
    rw [← present]
    exact (holds_variant respects σ label C.present relatedCheck).mp holds
  · show MeTTaCalculus.OccurrenceCommits.fire C.present sel.commit =
      MeTTaCalculus.OccurrenceCommits.fire C'.present sel.commit
    rw [present]

/-- **Every run has a run of each variant program from each variant configuration.** -/
theorem reach_variant {O : Type} [DecidableEq O] (respects : TableRespects G)
    {label : O → NTerm Stored} {R R' : Set (RuleInstance (NTerm Stored))} (related : ProgramVariant R R')
    {C C' D : Configuration (NTerm Stored) O} (same : StoreVariant C.equations C'.equations)
    (present : C.present = C'.present) (reach : Reach G label R C D) :
    ∃ D', Reach G label R' C' D' ∧ StoreVariant D.equations D'.equations ∧ D.present = D'.present := by
  induction reach with
  | refl => exact ⟨C', Relation.ReflTransGen.refl, same, present⟩
  | tail _ fired ih =>
      obtain ⟨E', reachE, sameE, presentE⟩ := ih
      obtain ⟨rule, member, step⟩ := fired
      obtain ⟨rule', member', relatedRule⟩ := related.1 rule member
      obtain ⟨F', stepF, sameF, presentF⟩ := step_variant respects relatedRule sameE presentE step
      exact ⟨F', reachE.tail ⟨rule', member', stepF⟩, sameF, presentF⟩

/-- **The answers reachable by runs are the same for variant programs, configurations and
checks.** -/
theorem program_answers_variant {O : Type} [DecidableEq O] (respects : TableRespects G)
    (label : O → NTerm Stored) {R R' : Set (RuleInstance (NTerm Stored))} (related : ProgramVariant R R')
    {C C' : Configuration (NTerm Stored) O} (same : StoreVariant C.equations C'.equations)
    (present : C.present = C'.present) {c c' : Check (NTerm Stored)} (relatedCheck : CheckVariant c c') :
    (∃ D, Reach G label R C D ∧ Answer G label D c) ↔ ∃ D', Reach G label R' C' D' ∧ Answer G label D' c' := by
  constructor
  · rintro ⟨D, reach, answered⟩
    obtain ⟨D', reach', sameD, presentD⟩ := reach_variant respects related same present reach
    exact ⟨D', reach', (answer_variant respects label sameD presentD relatedCheck).mp answered⟩
  · rintro ⟨D', reach', answered⟩
    obtain ⟨D, reach, sameD, presentD⟩ :=
      reach_variant respects related.symm (storeVariant_symm same) present.symm reach'
    exact ⟨D, reach, (answer_variant respects label sameD presentD (checkVariant_symm relatedCheck)).mp
      answered⟩

/-- **The same for every run.** -/
theorem program_every_answer_variant {O : Type} [DecidableEq O] (respects : TableRespects G)
    (label : O → NTerm Stored) {R R' : Set (RuleInstance (NTerm Stored))} (related : ProgramVariant R R')
    {C C' : Configuration (NTerm Stored) O} (same : StoreVariant C.equations C'.equations)
    (present : C.present = C'.present) {c c' : Check (NTerm Stored)} (relatedCheck : CheckVariant c c') :
    (∀ D, Reach G label R C D → Answer G label D c) ↔ ∀ D', Reach G label R' C' D' → Answer G label D' c' := by
  constructor
  · intro every D' reach'
    obtain ⟨D, reach, sameD, presentD⟩ :=
      reach_variant respects related.symm (storeVariant_symm same) present.symm reach'
    exact (answer_variant respects label sameD presentD (checkVariant_symm relatedCheck)).mpr
      (every D reach)
  · intro every D reach
    obtain ⟨D', reach', sameD, presentD⟩ := reach_variant respects related same present reach
    exact (answer_variant respects label sameD presentD relatedCheck).mpr (every D' reach')

/-! ## Witness -/

/-- The rule `incr` with a check counting the row `(foo 5)`, stored as an integer or as a fraction. -/
def countRule (n : Stored) : RuleInstance (NTerm Stored) :=
  ⟨[foo (.var 0)], [], [], [.count (foo (.num n)) 1], [bar (.op .plus (.var 0) (.num (.int 1)))]⟩

/-- **The two rules are variants**: one numeral of a check re-stored. -/
theorem countRule_variant : RuleVariant (countRule five) (countRule fiveFrac) :=
  ⟨.cons rfl .nil, .nil, .nil,
    .cons (show Variant (foo (.num five)) (foo (.num fiveFrac)) ∧ 1 = 1 from
      ⟨by simp [Variant, foo, NTerm.map, value_five, value_fiveFrac], rfl⟩) .nil, rfl⟩

/-- **The rule checking `5` fires from `(foo 5)`.** -/
theorem countRule_fires : ∃ D, Step (action exactTable) incrLabel (countRule five) start D := by
  refine ⟨incrSelection.result incrLabel (countRule five) start, incrSelection,
    ⟨by simp [incrSelection], by simp [incrSelection], rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
  · exact ⟨by simp [incrSelection, Selection.commit, start],
      by simp [incrSelection, Selection.commit],
      by simp [incrSelection, Selection.commit],
      by simp [incrSelection, Selection.commit, start],
      fun _ member => absurd member List.not_mem_nil⟩
  · refine ⟨fun _ => .num (.int 5), fun e member => ?_⟩
    have problem : incrSelection.problem incrLabel (countRule five) start =
        [(foo (.var 0), foo (.num (.int 5)))] := rfl
    rw [problem] at member
    obtain rfl := List.mem_singleton.mp member
    exact fun _ => rfl
  · intro check member σ _
    obtain rfl := List.mem_singleton.mp member
    show (Check.«matches» (action exactTable) σ incrLabel start.present (foo (.num five))).card = 1
    classical
    unfold Check.«matches»
    rw [show start.present = {0} from rfl, Finset.filter_singleton, if_pos]
    · exact Finset.card_singleton 0
    · exact fun _ => rfl

/-- **Both fire from `(foo 5)` and answer alike**: the rule checking `5` fires exactly when the rule
checking `5.0` does, and they reach variant configurations. -/
theorem countRule_fires_iff :
    (∃ D, Step (action exactTable) incrLabel (countRule five) start D) ↔
      ∃ D', Step (action exactTable) incrLabel (countRule fiveFrac) start D' := by
  have startSame : StoreVariant start.equations start.equations := List.Forall₂.nil
  constructor
  · rintro ⟨D, step⟩
    obtain ⟨D', step', _, _⟩ :=
      step_variant (C := start) (C' := start) exactTable_respects countRule_variant startSame rfl step
    exact ⟨D', step'⟩
  · rintro ⟨D', step'⟩
    obtain ⟨D, step, _, _⟩ :=
      step_variant (C := start) (C' := start) exactTable_respects countRule_variant.symm startSame rfl
        step'
    exact ⟨D, step⟩

#print axioms forall₂_append
#print axioms models_variant
#print axioms holds_variant
#print axioms answer_variant
#print axioms step_variant
#print axioms reach_variant
#print axioms program_answers_variant
#print axioms program_every_answer_variant
#print axioms countRule_variant
#print axioms countRule_fires
#print axioms countRule_fires_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Variants
