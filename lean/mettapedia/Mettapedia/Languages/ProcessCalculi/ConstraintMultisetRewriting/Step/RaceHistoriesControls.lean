import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceHistories

/-!
# Controls for records that carry makes

Every occurrence carries one term `τ`, so all firings are ground and admission is decided on
occurrences (`RaceSpectrum.Ground.valid_iff`), for every term syntax and substitution action.

## Old records identify, extended records separate (`extended_separates`)

The runs `takeA, takeB` and `takeAmakeB, takeB` of `RaceRecords.RecordControls` leave the same
choice-escape records. Their extended records differ, and so do the provenance pasts of their second
firings: empty in the first run, the first firing in the second.

## Matchings keep the causal order, not the records (`matching_not_record_iso`)

Labels are rules. `C₀ = {g₁}` and `D₀ = {g₂, w₂}`:

* `C₀`: `e₀` takes `g₁` and makes `x₁, y₁`; `e₁` takes `x₁` and makes `z₁`; `e₂` takes `y₁, z₁`.
* `D₀`: `d₀` takes `g₂` and makes `x₂, y₂`; `d₁` takes `x₂` and makes `z₂`; `d₂` takes `w₂, z₂`.

Both are single runs `R₀, R₁, R₂` with causal pasts `∅, {0}, {0, 1}`: `e₂` takes from `e₀` and `e₁`,
while `d₂` takes from `d₁` only, and `d₁` from `d₀`. They are history-preserving bisimilar
(`hpBisimilar`), and record bisimilar, since both starts are reuse-free and the program is pure
(`reuseFree_C₀`, `reuseFree_D₀`, `recordBisimilar`). The bisimulation game matches the two complete
runs (`matched`), and their causal orders read off the records agree, yet no renaming carries one
extended record to the other (`records_not_renamed`): `e₂` took something `e₀` made, and `d₂` took
nothing `d₀` made (`direct_provenance_differs`).

## Reuse (`reuse_control`)

A program where `t` takes `a` and makes `b`, and `u` takes `b` and makes `a`, is not reuse-free from
`{a}`: after `t, u`, the identity `a` was taken and is made again.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.HistoryControls

open AnnotatedRuns (Firing StaticIndependent)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uT uS

/-! ## Old records identify, extended records separate -/

section TakeMake

open RecordControls

variable {T : Type uT} {S : Type uS} (τ : T)

/-- **The choice escape identifies two runs that the extended records separate.** -/
theorem extended_separates (A : SubstitutionAction T S) {C D : Configuration T RecordControls.Site} :
    ((AnnotatedRuns.choiceEscape A (RecordControls.label τ)).records (s := C) (takeA (S := S) τ) ++
        (AnnotatedRuns.choiceEscape A (RecordControls.label τ)).records (s := C) (takeB (S := S) τ) =
      (AnnotatedRuns.choiceEscape A (RecordControls.label τ)).records (s := D) (takeAmakeB (S := S) τ) ++
        (AnnotatedRuns.choiceEscape A (RecordControls.label τ)).records (s := D) (takeB (S := S) τ)) ∧
    [Entry.ofFiring (takeA (S := S) τ), Entry.ofFiring (takeB (S := S) τ)] ≠
      [Entry.ofFiring (takeAmakeB (S := S) τ), Entry.ofFiring (takeB (S := S) τ)] ∧
    provPast [(Entry.ofFiring (takeA (S := S) τ), (∅ : Finset ℕ))] (Entry.ofFiring (takeB (S := S) τ)) = ∅ ∧
    0 ∈ provPast [(Entry.ofFiring (takeAmakeB (S := S) τ), (∅ : Finset ℕ))]
      (Entry.ofFiring (takeB (S := S) τ)) := by
  refine ⟨(records_blind_to_causality τ A).1, ?_, ?_, ?_⟩
  · intro same
    simp [Entry.ofFiring, takeA, takeAmakeB, RecordControls.firing] at same
  · have direct : provDirect [(Entry.ofFiring (takeA (S := S) τ), (∅ : Finset ℕ))]
        (Entry.ofFiring (takeB (S := S) τ)) = ∅ := by
      refine Finset.subset_empty.mp fun i member => ?_
      obtain ⟨lt, x, get, overlap⟩ := mem_provDirect.mp member
      have zero : i = 0 := by simpa using lt
      subst zero
      simp only [List.getElem?_cons_zero, Option.some.injEq] at get
      subst get
      exact (overlap (of_decide_eq_true rfl)).elim
    unfold provPast
    rw [direct]
    simp
  · exact Finset.mem_union_left _ (mem_provDirect.mpr ⟨by simp, _, rfl, of_decide_eq_false rfl⟩)

end TakeMake

/-! ## Matchings keep the causal order, not the records -/

/-- Occurrence identities. -/
inductive Site
  | g₁ | x₁ | y₁ | z₁ | g₂ | w₂ | x₂ | y₂ | z₂
  deriving DecidableEq

variable {T : Type uT} {S : Type uS} (τ : T)

/-- Every occurrence carries `τ`. -/
def label : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes `made`. -/
def firing (taken made : List Site) : Firing T S Site :=
  ⟨⟨taken.map (label τ), [], [], [], made.map (label τ)⟩, [], ⟨taken, [], made⟩⟩

def e₀ : Firing T S Site := firing τ [.g₁] [.x₁, .y₁]
def e₁ : Firing T S Site := firing τ [.x₁] [.z₁]
def e₂ : Firing T S Site := firing τ [.y₁, .z₁] []
def d₀ : Firing T S Site := firing τ [.g₂] [.x₂, .y₂]
def d₁ : Firing T S Site := firing τ [.x₂] [.z₂]
def d₂ : Firing T S Site := firing τ [.w₂, .z₂] []

/-- The program's alphabet. -/
def alphabet : List (Firing T S Site) := [e₀ τ, e₁ τ, e₂ τ, d₀ τ, d₁ τ, d₂ τ]

/-- **Labels are rules.** -/
def offers (r : RuleInstance T) (f : Firing T S Site) : Prop := f ∈ alphabet τ ∧ f.rule = r

/-- `n` copies of `(τ, τ)`. -/
def E (n : ℕ) : EquationStore T := List.replicate n (τ, τ)

def C₀ : Configuration T Site := ⟨[], {.g₁}⟩
def C₁ : Configuration T Site := ⟨E τ 1, {.x₁, .y₁}⟩
def C₂ : Configuration T Site := ⟨E τ 2, {.y₁, .z₁}⟩
def C₃ : Configuration T Site := ⟨E τ 4, ∅⟩
def D₀ : Configuration T Site := ⟨[], {.g₂, .w₂}⟩
def D₁ : Configuration T Site := ⟨E τ 1, {.w₂, .x₂, .y₂}⟩
def D₂ : Configuration T Site := ⟨E τ 2, {.w₂, .y₂, .z₂}⟩
def D₃ : Configuration T Site := ⟨E τ 4, {.y₂}⟩

/-- The states of the run from `C₀`, with their histories. -/
def X₀ : Configuration T Site × History T S Site := (C₀, [])
def X₁ : Configuration T Site × History T S Site := (C₁ τ, [(e₀ τ, ∅)])
def X₂ : Configuration T Site × History T S Site := (C₂ τ, [(e₀ τ, ∅), (e₁ τ, {0})])
def X₃ : Configuration T Site × History T S Site :=
  (C₃ τ, [(e₀ τ, ∅), (e₁ τ, {0}), (e₂ τ, {0, 1})])

/-- The states of the run from `D₀`, with their histories. -/
def Y₀ : Configuration T Site × History T S Site := (D₀, [])
def Y₁ : Configuration T Site × History T S Site := (D₁ τ, [(d₀ τ, ∅)])
def Y₂ : Configuration T Site × History T S Site := (D₂ τ, [(d₀ τ, ∅), (d₁ τ, {0})])
def Y₃ : Configuration T Site × History T S Site :=
  (D₃ τ, [(d₀ τ, ∅), (d₁ τ, {0}), (d₂ τ, {0, 1})])

theorem config_eq {C D : Configuration T Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

theorem reflexive_E (n : ℕ) : Reflexive (E τ n) := by
  intro e member
  rw [List.eq_of_mem_replicate member]

theorem ground : ∀ f ∈ alphabet (S := S) τ, Ground (label τ) f := by
  intro f member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem pure_firing (taken made : List Site) : Pure (firing (S := S) τ taken made) := ⟨rfl, rfl, rfl⟩

theorem pureProgram : PureProgram (offers (S := S) τ) := by
  rintro r f ⟨member, -⟩
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact pure_firing τ _ _

variable (A : SubstitutionAction T S)

theorem valid_iff {f : Firing T S Site} (member : f ∈ alphabet τ) {C : Configuration T Site}
    (refl : Reflexive C.equations) :
    f.Valid A (label τ) C ↔ Enabled (label τ) C.present (f.selection.commit (T := T)) :=
  (ground τ f member).valid_iff A refl

theorem result_e₀ : (e₀ (S := S) τ).result (label τ) C₀ = C₁ τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_e₁ : (e₁ (S := S) τ).result (label τ) (C₁ τ) = C₂ τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_e₂ : (e₂ (S := S) τ).result (label τ) (C₂ τ) = C₃ τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_d₀ : (d₀ (S := S) τ).result (label τ) D₀ = D₁ τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_d₁ : (d₁ (S := S) τ).result (label τ) (D₁ τ) = D₂ τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_d₂ : (d₂ (S := S) τ).result (label τ) (D₂ τ) = D₃ τ := config_eq rfl (of_decide_eq_true rfl)

/-! ### Which firings are admitted -/

section Admitted

variable {τ A}
variable {f : Firing T S Site}

theorem at_C₀ (member : f ∈ alphabet τ) (valid : f.Valid A (label τ) C₀) : f = e₀ τ := by
  rw [valid_iff τ A member reflexive_nil] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at_C₁ (member : f ∈ alphabet τ) (valid : f.Valid A (label τ) (C₁ τ)) : f = e₁ τ := by
  rw [valid_iff τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd valid (of_decide_eq_false rfl)
  · rfl
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at_C₂ (member : f ∈ alphabet τ) (valid : f.Valid A (label τ) (C₂ τ)) : f = e₂ τ := by
  rw [valid_iff τ A member (reflexive_E τ 2)] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · rfl
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at_C₃ (member : f ∈ alphabet τ) : ¬ f.Valid A (label τ) (C₃ τ) := by
  intro valid
  rw [valid_iff τ A member (reflexive_E τ 4)] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd valid (of_decide_eq_false rfl)

theorem at_D₀ (member : f ∈ alphabet τ) (valid : f.Valid A (label τ) D₀) : f = d₀ τ := by
  rw [valid_iff τ A member reflexive_nil] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · rfl
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at_D₁ (member : f ∈ alphabet τ) (valid : f.Valid A (label τ) (D₁ τ)) : f = d₁ τ := by
  rw [valid_iff τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · rfl
  · exact absurd valid (of_decide_eq_false rfl)

theorem at_D₂ (member : f ∈ alphabet τ) (valid : f.Valid A (label τ) (D₂ τ)) : f = d₂ τ := by
  rw [valid_iff τ A member (reflexive_E τ 2)] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact absurd valid (of_decide_eq_false rfl)

theorem at_D₃ (member : f ∈ alphabet τ) : ¬ f.Valid A (label τ) (D₃ τ) := by
  intro valid
  rw [valid_iff τ A member (reflexive_E τ 4)] at valid
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd valid (of_decide_eq_false rfl)

end Admitted

/-! ### Dependence and causal pasts -/

include A in
theorem dependent {e f : Firing T S Site} (pe : Pure e) (pf : Pure f)
    (takes : Disjoint e.selection.taken.toFinset f.selection.taken.toFinset)
    (makes : Disjoint e.selection.made.toFinset f.selection.made.toFinset)
    (overlap : ¬ Disjoint e.selection.made.toFinset f.selection.taken.toFinset) :
    ¬ StaticIndependent (label τ) e f := by
  have : Nonempty S := ⟨A.identity⟩
  intro independent
  exact overlap ((staticIndependent_iff_provenance (label τ) pe pf takes makes).mp independent).1

include A in
theorem independent_d₀_d₂ : StaticIndependent (label τ) (d₀ (S := S) τ) (d₂ τ) := by
  have : Nonempty S := ⟨A.identity⟩
  exact (staticIndependent_iff_provenance (label τ) (pure_firing τ _ _) (pure_firing τ _ _)
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mpr ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem past_nil (f : Firing T S Site) : past (label τ) ([] : History T S Site) f = ∅ :=
  Finset.subset_empty.mp (past_subset_range wf_nil)

include A in
theorem past_e₁ : past (label τ) [(e₀ (S := S) τ, (∅ : Finset ℕ))] (e₁ τ) = {0} := by
  have direct : directPast (label τ) [(e₀ (S := S) τ, (∅ : Finset ℕ))] (e₁ τ) = {0} := by
    ext i
    rw [mem_directPast, Finset.mem_singleton]
    constructor
    · rintro ⟨lt, -⟩
      simpa using lt
    · rintro rfl
      exact ⟨by simp, _, rfl, dependent τ A (pure_firing τ _ _) (pure_firing τ _ _)
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_false rfl)⟩
  unfold past
  rw [direct]
  simp

include A in
theorem past_d₁ : past (label τ) [(d₀ (S := S) τ, (∅ : Finset ℕ))] (d₁ τ) = {0} := by
  have direct : directPast (label τ) [(d₀ (S := S) τ, (∅ : Finset ℕ))] (d₁ τ) = {0} := by
    ext i
    rw [mem_directPast, Finset.mem_singleton]
    constructor
    · rintro ⟨lt, -⟩
      simpa using lt
    · rintro rfl
      exact ⟨by simp, _, rfl, dependent τ A (pure_firing τ _ _) (pure_firing τ _ _)
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_false rfl)⟩
  unfold past
  rw [direct]
  simp

include A in
/-- **`e₂` depends directly on `e₀` and `e₁`.** -/
theorem past_e₂ :
    past (label τ) [(e₀ (S := S) τ, (∅ : Finset ℕ)), (e₁ τ, {0})] (e₂ τ) = {0, 1} := by
  have direct : directPast (label τ) [(e₀ (S := S) τ, (∅ : Finset ℕ)), (e₁ τ, {0})] (e₂ τ) =
      {0, 1} := by
    ext i
    rw [mem_directPast, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨lt, -⟩
      simp only [List.length_cons, List.length_nil] at lt
      omega
    · rintro (rfl | rfl)
      · exact ⟨by simp, _, rfl, dependent τ A (pure_firing τ _ _) (pure_firing τ _ _)
          (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_false rfl)⟩
      · exact ⟨by simp, _, rfl, dependent τ A (pure_firing τ _ _) (pure_firing τ _ _)
          (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_false rfl)⟩
  unfold past
  rw [direct]
  exact of_decide_eq_true rfl

include A in
/-- **`d₂` depends directly on `d₁` only, and on `d₀` through it.** -/
theorem past_d₂ :
    past (label τ) [(d₀ (S := S) τ, (∅ : Finset ℕ)), (d₁ τ, {0})] (d₂ τ) = {0, 1} := by
  have direct : directPast (label τ) [(d₀ (S := S) τ, (∅ : Finset ℕ)), (d₁ τ, {0})] (d₂ τ) = {1} := by
    ext i
    rw [mem_directPast, Finset.mem_singleton]
    constructor
    · rintro ⟨lt, e, get, dependentE⟩
      simp only [List.length_cons, List.length_nil] at lt
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at get
        subst get
        exact absurd (independent_d₀_d₂ τ A) dependentE
      · rfl
    · rintro rfl
      exact ⟨by simp, _, rfl, dependent τ A (pure_firing τ _ _) (pure_firing τ _ _)
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_false rfl)⟩
  unfold past
  rw [direct]
  exact of_decide_eq_true rfl

/-! ### The history moves -/

section Moves

variable {τ A}

theorem hmoves_X₀ {lab : RuleInstance T × Finset ℕ} {x : Configuration T Site × History T S Site}
    (moved : HMoves A (label τ) (offers τ) X₀ lab x) :
    lab = ((e₀ (S := S) τ).rule, ∅) ∧ x = X₁ τ := by
  obtain ⟨f, ⟨member, rule⟩, valid, labelled, rfl⟩ := moved
  obtain rfl := at_C₀ member valid
  rw [show (X₀ : Configuration T Site × History T S Site).2 = [] from rfl, past_nil] at labelled
  have same : lab = ((e₀ (S := S) τ).rule, ∅) := Prod.ext rule.symm labelled
  subst same
  refine ⟨rfl, ?_⟩
  show ((e₀ τ).result (label τ) C₀, [] ++ [(e₀ τ, ∅)]) = X₁ τ
  rw [result_e₀]
  rfl

theorem hmoves_X₁ {lab : RuleInstance T × Finset ℕ} {x : Configuration T Site × History T S Site}
    (moved : HMoves A (label τ) (offers τ) (X₁ τ) lab x) :
    lab = ((e₁ (S := S) τ).rule, {0}) ∧ x = X₂ τ := by
  obtain ⟨f, ⟨member, rule⟩, valid, labelled, rfl⟩ := moved
  obtain rfl := at_C₁ member valid
  rw [show ((X₁ τ) : Configuration T Site × History T S Site).2 = [(e₀ τ, ∅)] from rfl, past_e₁ τ A] at labelled
  have same : lab = ((e₁ (S := S) τ).rule, {0}) := Prod.ext rule.symm labelled
  subst same
  refine ⟨rfl, ?_⟩
  show ((e₁ τ).result (label τ) (C₁ τ), [(e₀ τ, ∅)] ++ [(e₁ τ, {0})]) = X₂ τ
  rw [result_e₁]
  rfl

theorem hmoves_X₂ {lab : RuleInstance T × Finset ℕ} {x : Configuration T Site × History T S Site}
    (moved : HMoves A (label τ) (offers τ) (X₂ τ) lab x) :
    lab = ((e₂ (S := S) τ).rule, {0, 1}) ∧ x = X₃ τ := by
  obtain ⟨f, ⟨member, rule⟩, valid, labelled, rfl⟩ := moved
  obtain rfl := at_C₂ member valid
  rw [show ((X₂ τ) : Configuration T Site × History T S Site).2 = [(e₀ τ, ∅), (e₁ τ, {0})] from rfl, past_e₂ τ A] at labelled
  have same : lab = ((e₂ (S := S) τ).rule, {0, 1}) := Prod.ext rule.symm labelled
  subst same
  refine ⟨rfl, ?_⟩
  show ((e₂ τ).result (label τ) (C₂ τ), [(e₀ τ, ∅), (e₁ τ, {0})] ++ [(e₂ τ, {0, 1})]) = X₃ τ
  rw [result_e₂]
  rfl

theorem hmoves_X₃ {lab : RuleInstance T × Finset ℕ} {x : Configuration T Site × History T S Site} :
    ¬ HMoves A (label τ) (offers τ) (X₃ τ) lab x := by
  rintro ⟨f, ⟨member, _⟩, valid, _, _⟩
  exact at_C₃ member valid

theorem hmoves_Y₀ {lab : RuleInstance T × Finset ℕ} {x : Configuration T Site × History T S Site}
    (moved : HMoves A (label τ) (offers τ) Y₀ lab x) :
    lab = ((d₀ (S := S) τ).rule, ∅) ∧ x = Y₁ τ := by
  obtain ⟨f, ⟨member, rule⟩, valid, labelled, rfl⟩ := moved
  obtain rfl := at_D₀ member valid
  rw [show (Y₀ : Configuration T Site × History T S Site).2 = [] from rfl, past_nil] at labelled
  have same : lab = ((d₀ (S := S) τ).rule, ∅) := Prod.ext rule.symm labelled
  subst same
  refine ⟨rfl, ?_⟩
  show ((d₀ τ).result (label τ) D₀, [] ++ [(d₀ τ, ∅)]) = Y₁ τ
  rw [result_d₀]
  rfl

theorem hmoves_Y₁ {lab : RuleInstance T × Finset ℕ} {x : Configuration T Site × History T S Site}
    (moved : HMoves A (label τ) (offers τ) (Y₁ τ) lab x) :
    lab = ((d₁ (S := S) τ).rule, {0}) ∧ x = Y₂ τ := by
  obtain ⟨f, ⟨member, rule⟩, valid, labelled, rfl⟩ := moved
  obtain rfl := at_D₁ member valid
  rw [show ((Y₁ τ) : Configuration T Site × History T S Site).2 = [(d₀ τ, ∅)] from rfl, past_d₁ τ A] at labelled
  have same : lab = ((d₁ (S := S) τ).rule, {0}) := Prod.ext rule.symm labelled
  subst same
  refine ⟨rfl, ?_⟩
  show ((d₁ τ).result (label τ) (D₁ τ), [(d₀ τ, ∅)] ++ [(d₁ τ, {0})]) = Y₂ τ
  rw [result_d₁]
  rfl

theorem hmoves_Y₂ {lab : RuleInstance T × Finset ℕ} {x : Configuration T Site × History T S Site}
    (moved : HMoves A (label τ) (offers τ) (Y₂ τ) lab x) :
    lab = ((d₂ (S := S) τ).rule, {0, 1}) ∧ x = Y₃ τ := by
  obtain ⟨f, ⟨member, rule⟩, valid, labelled, rfl⟩ := moved
  obtain rfl := at_D₂ member valid
  rw [show ((Y₂ τ) : Configuration T Site × History T S Site).2 = [(d₀ τ, ∅), (d₁ τ, {0})] from rfl, past_d₂ τ A] at labelled
  have same : lab = ((d₂ (S := S) τ).rule, {0, 1}) := Prod.ext rule.symm labelled
  subst same
  refine ⟨rfl, ?_⟩
  show ((d₂ τ).result (label τ) (D₂ τ), [(d₀ τ, ∅), (d₁ τ, {0})] ++ [(d₂ τ, {0, 1})]) = Y₃ τ
  rw [result_d₂]
  rfl

theorem hmoves_Y₃ {lab : RuleInstance T × Finset ℕ} {x : Configuration T Site × History T S Site} :
    ¬ HMoves A (label τ) (offers τ) (Y₃ τ) lab x := by
  rintro ⟨f, ⟨member, _⟩, valid, _, _⟩
  exact at_D₃ member valid

end Moves

theorem mem_e₀ : e₀ (S := S) τ ∈ alphabet τ := by simp [alphabet]
theorem mem_e₁ : e₁ (S := S) τ ∈ alphabet τ := by simp [alphabet]
theorem mem_e₂ : e₂ (S := S) τ ∈ alphabet τ := by simp [alphabet]
theorem mem_d₀ : d₀ (S := S) τ ∈ alphabet τ := by simp [alphabet]
theorem mem_d₁ : d₁ (S := S) τ ∈ alphabet τ := by simp [alphabet]
theorem mem_d₂ : d₂ (S := S) τ ∈ alphabet τ := by simp [alphabet]

theorem hmove_X₀ : HMoves A (label τ) (offers τ) X₀ ((e₀ (S := S) τ).rule, ∅) (X₁ τ) := by
  refine ⟨e₀ τ, ⟨mem_e₀ τ, rfl⟩, (valid_iff τ A (mem_e₀ τ) reflexive_nil).mpr (of_decide_eq_true rfl), (past_nil τ _).symm, ?_⟩
  show X₁ τ = ((e₀ τ).result (label τ) C₀, [] ++ [(e₀ τ, ∅)])
  rw [result_e₀]
  rfl

theorem hmove_X₁ : HMoves A (label τ) (offers τ) (X₁ τ) ((e₁ (S := S) τ).rule, {0}) (X₂ τ) := by
  refine ⟨e₁ τ, ⟨mem_e₁ τ, rfl⟩, (valid_iff τ A (mem_e₁ τ) (reflexive_E τ 1)).mpr (of_decide_eq_true rfl), (past_e₁ τ A).symm, ?_⟩
  show X₂ τ = ((e₁ τ).result (label τ) (C₁ τ), [(e₀ τ, ∅)] ++ [(e₁ τ, {0})])
  rw [result_e₁]
  rfl

theorem hmove_X₂ : HMoves A (label τ) (offers τ) (X₂ τ) ((e₂ (S := S) τ).rule, {0, 1}) (X₃ τ) := by
  refine ⟨e₂ τ, ⟨mem_e₂ τ, rfl⟩, (valid_iff τ A (mem_e₂ τ) (reflexive_E τ 2)).mpr (of_decide_eq_true rfl), (past_e₂ τ A).symm, ?_⟩
  show X₃ τ = ((e₂ τ).result (label τ) (C₂ τ), [(e₀ τ, ∅), (e₁ τ, {0})] ++ [(e₂ τ, {0, 1})])
  rw [result_e₂]
  rfl

theorem hmove_Y₀ : HMoves A (label τ) (offers τ) Y₀ ((d₀ (S := S) τ).rule, ∅) (Y₁ τ) := by
  refine ⟨d₀ τ, ⟨mem_d₀ τ, rfl⟩, (valid_iff τ A (mem_d₀ τ) reflexive_nil).mpr (of_decide_eq_true rfl), (past_nil τ _).symm, ?_⟩
  show Y₁ τ = ((d₀ τ).result (label τ) D₀, [] ++ [(d₀ τ, ∅)])
  rw [result_d₀]
  rfl

theorem hmove_Y₁ : HMoves A (label τ) (offers τ) (Y₁ τ) ((d₁ (S := S) τ).rule, {0}) (Y₂ τ) := by
  refine ⟨d₁ τ, ⟨mem_d₁ τ, rfl⟩, (valid_iff τ A (mem_d₁ τ) (reflexive_E τ 1)).mpr (of_decide_eq_true rfl), (past_d₁ τ A).symm, ?_⟩
  show Y₂ τ = ((d₁ τ).result (label τ) (D₁ τ), [(d₀ τ, ∅)] ++ [(d₁ τ, {0})])
  rw [result_d₁]
  rfl

theorem hmove_Y₂ : HMoves A (label τ) (offers τ) (Y₂ τ) ((d₂ (S := S) τ).rule, {0, 1}) (Y₃ τ) := by
  refine ⟨d₂ τ, ⟨mem_d₂ τ, rfl⟩, (valid_iff τ A (mem_d₂ τ) (reflexive_E τ 2)).mpr (of_decide_eq_true rfl), (past_d₂ τ A).symm, ?_⟩
  show Y₃ τ = ((d₂ τ).result (label τ) (D₂ τ), [(d₀ τ, ∅), (d₁ τ, {0})] ++ [(d₂ τ, {0, 1})])
  rw [result_d₂]
  rfl

/-! ### History-preserving and record bisimilarity -/

/-- The matching of the two runs, stage by stage. -/
def Matching (x y : Configuration T Site × History T S Site) : Prop :=
  (x = X₀ ∧ y = Y₀) ∨ (x = X₁ τ ∧ y = Y₁ τ) ∨ (x = X₂ τ ∧ y = Y₂ τ) ∨ (x = X₃ τ ∧ y = Y₃ τ)

theorem matching_bisimulation :
    (histSystem A (label τ) (offers (S := S) τ)).IsBisimulation (Matching τ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) lab x' moved
    · obtain ⟨rfl, rfl⟩ := hmoves_X₀ moved
      exact ⟨Y₁ τ, hmove_Y₀ τ A, .inr (.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨rfl, rfl⟩ := hmoves_X₁ moved
      exact ⟨Y₂ τ, hmove_Y₁ τ A, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
    · obtain ⟨rfl, rfl⟩ := hmoves_X₂ moved
      exact ⟨Y₃ τ, hmove_Y₂ τ A, .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
    · exact absurd moved hmoves_X₃
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) lab y' moved
    · obtain ⟨rfl, rfl⟩ := hmoves_Y₀ moved
      exact ⟨X₁ τ, hmove_X₀ τ A, .inr (.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨rfl, rfl⟩ := hmoves_Y₁ moved
      exact ⟨X₂ τ, hmove_X₁ τ A, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
    · obtain ⟨rfl, rfl⟩ := hmoves_Y₂ moved
      exact ⟨X₃ τ, hmove_X₂ τ A, .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
    · exact absurd moved hmoves_Y₃
  · intro _ _ _ atom
    exact atom.elim

/-- **`C₀` and `D₀` are history-preserving bisimilar.** -/
theorem hpBisimilar : HPBisimilar A (label τ) (offers (S := S) τ) C₀ D₀ :=
  ⟨Matching τ, matching_bisimulation τ A, .inl ⟨rfl, rfl⟩⟩

/-- **The bisimulation game matches the two complete runs.** -/
theorem matched :
    Relation.ReflTransGen (Round A (label τ) (offers (S := S) τ) (Matching τ)) ((C₀, []), (D₀, []))
      (X₃ τ, Y₃ τ) := by
  have r₀ : Round A (label τ) (offers (S := S) τ) (Matching τ) (X₀, Y₀) (X₁ τ, Y₁ τ) :=
    ⟨_, hmove_X₀ τ A, hmove_Y₀ τ A, .inr (.inl ⟨rfl, rfl⟩)⟩
  have r₁ : Round A (label τ) (offers (S := S) τ) (Matching τ) (X₁ τ, Y₁ τ) (X₂ τ, Y₂ τ) :=
    ⟨_, hmove_X₁ τ A, hmove_Y₁ τ A, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
  have r₂ : Round A (label τ) (offers (S := S) τ) (Matching τ) (X₂ τ, Y₂ τ) (X₃ τ, Y₃ τ) :=
    ⟨_, hmove_X₂ τ A, hmove_Y₂ τ A, .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
  exact ((Relation.ReflTransGen.single r₀).tail r₁).tail r₂

theorem reach_C₀ {x : Configuration T Site × History T S Site}
    (reach : HReach A (label τ) (offers τ) C₀ x) : x = X₀ ∨ x = X₁ τ ∨ x = X₂ τ ∨ x = X₃ τ := by
  induction reach with
  | refl => exact .inl rfl
  | tail _ step ih =>
      obtain ⟨lab, moved⟩ := step
      rcases ih with rfl | rfl | rfl | rfl
      · exact .inr (.inl (hmoves_X₀ moved).2)
      · exact .inr (.inr (.inl (hmoves_X₁ moved).2))
      · exact .inr (.inr (.inr (hmoves_X₂ moved).2))
      · exact absurd moved hmoves_X₃

theorem reach_D₀ {x : Configuration T Site × History T S Site}
    (reach : HReach A (label τ) (offers τ) D₀ x) : x = Y₀ ∨ x = Y₁ τ ∨ x = Y₂ τ ∨ x = Y₃ τ := by
  induction reach with
  | refl => exact .inl rfl
  | tail _ step ih =>
      obtain ⟨lab, moved⟩ := step
      rcases ih with rfl | rfl | rfl | rfl
      · exact .inr (.inl (hmoves_Y₀ moved).2)
      · exact .inr (.inr (.inl (hmoves_Y₁ moved).2))
      · exact .inr (.inr (.inr (hmoves_Y₂ moved).2))
      · exact absurd moved hmoves_Y₃

/-- **The run from `C₀` reuses nothing.** -/
theorem reuseFree_C₀ : ReuseFree A (label τ) (offers (S := S) τ) C₀ := by
  intro x reach ℓ f ⟨member, _⟩ valid
  rcases reach_C₀ τ A reach with rfl | rfl | rfl | rfl
  · obtain rfl := at_C₀ member valid
    intro e inHistory
    exact absurd inHistory List.not_mem_nil
  · obtain rfl := at_C₁ member valid
    intro e inHistory
    simp only [X₁, List.mem_singleton] at inHistory
    subst inHistory
    exact of_decide_eq_true rfl
  · obtain rfl := at_C₂ member valid
    intro e _ o made
    simp [e₂, firing] at made
  · exact absurd valid (at_C₃ member)

/-- **The run from `D₀` reuses nothing.** -/
theorem reuseFree_D₀ : ReuseFree A (label τ) (offers (S := S) τ) D₀ := by
  intro x reach ℓ f ⟨member, _⟩ valid
  rcases reach_D₀ τ A reach with rfl | rfl | rfl | rfl
  · obtain rfl := at_D₀ member valid
    intro e inHistory
    exact absurd inHistory List.not_mem_nil
  · obtain rfl := at_D₁ member valid
    intro e inHistory
    simp only [Y₁, List.mem_singleton] at inHistory
    subst inHistory
    exact of_decide_eq_true rfl
  · obtain rfl := at_D₂ member valid
    intro e _ o made
    simp [d₂, firing] at made
  · exact absurd valid (at_D₃ member)

/-- **`C₀` and `D₀` are record bisimilar.** -/
theorem recordBisimilar : RecordBisimilar A (label τ) (offers (S := S) τ) C₀ D₀ :=
  (hpBisimilar_iff_recordBisimilar (pureProgram τ) (reuseFree_C₀ τ A) (reuseFree_D₀ τ A)).mp
    (hpBisimilar τ A)

/-- **No renaming carries one extended record to the other.** -/
theorem records_not_renamed (π : Site ≃ Site) :
    (entries (X₃ (S := S) τ).2).map (Entry.rename π) ≠ entries (Y₃ (S := S) τ).2 := by
  intro same
  have made₀ := congrArg (fun l : List (Entry Site) => l.head?.map Entry.made) same
  have taken₂ := congrArg (fun l : List (Entry Site) => l.getLast?.map Entry.taken) same
  simp [entries, Entry.rename, Entry.ofFiring, X₃, Y₃, e₀, e₂, d₀, d₂, firing] at made₀ taken₂
  rw [made₀.2] at taken₂
  exact absurd taken₂.1 (by decide)

/-- **The direct provenance differs**: `e₂` took something `e₀` made, and `d₂` took nothing `d₀`
made. -/
theorem direct_provenance_differs :
    ¬ Disjoint (e₀ (S := S) τ).selection.made.toFinset (e₂ (S := S) τ).selection.taken.toFinset ∧
      Disjoint (d₀ (S := S) τ).selection.made.toFinset (d₂ (S := S) τ).selection.taken.toFinset :=
  ⟨of_decide_eq_false rfl, of_decide_eq_true rfl⟩

/-- **Matchings keep the causal order, not the records.** `C₀` and `D₀` are history-preserving and
record bisimilar; the bisimulation game matches their complete runs, whose causal orders read off the
records agree; yet no renaming carries one extended record to the other, and the direct provenance
differs. -/
theorem matching_not_record_iso :
    HPBisimilar A (label τ) (offers (S := S) τ) C₀ D₀ ∧
      RecordBisimilar A (label τ) (offers (S := S) τ) C₀ D₀ ∧
      Relation.ReflTransGen (Round A (label τ) (offers (S := S) τ) (Matching τ)) ((C₀, []), (D₀, []))
        (X₃ τ, Y₃ τ) ∧
      (annotate (entries (X₃ (S := S) τ).2)).map Prod.snd =
        (annotate (entries (Y₃ (S := S) τ).2)).map Prod.snd ∧
      (∀ π : Site ≃ Site, (entries (X₃ (S := S) τ).2).map (Entry.rename π) ≠ entries (Y₃ (S := S) τ).2) ∧
      ¬ Disjoint (e₀ (S := S) τ).selection.made.toFinset (e₂ (S := S) τ).selection.taken.toFinset ∧
      Disjoint (d₀ (S := S) τ).selection.made.toFinset (d₂ (S := S) τ).selection.taken.toFinset :=
  ⟨hpBisimilar τ A, recordBisimilar τ A, matched τ A,
    matching_causal_eq (pureProgram τ) (reuseFree_C₀ τ A) (reuseFree_D₀ τ A) (matched τ A),
    records_not_renamed τ, direct_provenance_differs τ⟩

/-! ## Reuse -/

namespace Reuse

/-- Occurrence identities. -/
inductive Site
  | a | b
  deriving DecidableEq

def label : Site → T := fun _ => τ

/-- `t` takes `a` and makes `b`. -/
def t : Firing T S Site := ⟨⟨[τ], [], [], [], [τ]⟩, [], ⟨[.a], [], [.b]⟩⟩
/-- `u` takes `b` and makes `a`. -/
def u : Firing T S Site := ⟨⟨[τ], [], [], [], [τ]⟩, [], ⟨[.b], [], [.a]⟩⟩

def offers (r : RuleInstance T) (f : Firing T S Site) : Prop := (f = t τ ∨ f = u τ) ∧ f.rule = r

theorem ground_t : Ground (label τ) (t (S := S) τ) := ⟨rfl, rfl, rfl, rfl, rfl, rfl,
  of_decide_eq_true rfl, of_decide_eq_true rfl⟩
theorem ground_u : Ground (label τ) (u (S := S) τ) := ⟨rfl, rfl, rfl, rfl, rfl, rfl,
  of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- **A program that remakes what it took is not reuse-free**: from `{a}`, after `t`, the firing `u`
is admitted and makes `a`, which `t` took. -/
theorem reuse_control : ¬ ReuseFree A (label τ) (offers (S := S) τ) ⟨[], {.a}⟩ := by
  intro reuse
  have validT : (t (S := S) τ).Valid A (label τ) ⟨[], {.a}⟩ :=
    ((ground_t τ).valid_iff A reflexive_nil).mpr (of_decide_eq_true rfl)
  have moved : HMoves A (label τ) (offers (S := S) τ) (⟨[], {.a}⟩, [])
      ((t (S := S) τ).rule, past (label τ) [] (t (S := S) τ))
      ((t τ).result (label τ) ⟨[], {.a}⟩, [] ++ [(t τ, past (label τ) [] (t (S := S) τ))]) :=
    ⟨t τ, ⟨.inl rfl, rfl⟩, validT, rfl, rfl⟩
  have reach : HReach A (label τ) (offers (S := S) τ) ⟨[], {.a}⟩
      ((t τ).result (label τ) ⟨[], {.a}⟩, [] ++ [(t τ, past (label τ) [] (t (S := S) τ))]) :=
    Relation.ReflTransGen.single ⟨_, moved⟩
  have validU : (u (S := S) τ).Valid A (label τ) ((t (S := S) τ).result (label τ) ⟨[], {.a}⟩) :=
    ((ground_u τ).valid_iff A (Ground.reflexive_result (ground_t τ) reflexive_nil)).mpr
      (of_decide_eq_true rfl)
  exact reuse _ reach (u τ).rule (u τ) ⟨.inr rfl, rfl⟩ validU (t τ, past (label τ) [] (t (S := S) τ))
    (List.mem_singleton_self _) Site.a (by simp [u]) (by simp [t])

end Reuse

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.HistoryControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.HistoryControls in
#print axioms extended_separates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.HistoryControls in
#print axioms hpBisimilar
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.HistoryControls in
#print axioms recordBisimilar
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.HistoryControls in
#print axioms records_not_renamed
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.HistoryControls in
#print axioms matching_not_record_iso
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.HistoryControls in
#print axioms Reuse.reuse_control
