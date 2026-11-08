import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSteps

/-!
# Controls: both inclusions of the causal spectrum are strict

Programs here name their firings by the actions `a` and `b` (a labelled alphabet: rules with sites,
named). Every occurrence carries one term `τ`, so all firings are ground and admission is decided on
occurrences (`RaceSpectrum.Ground.valid_iff`), for every term syntax and substitution action.

* **`a | b`** (`PAR = {a, b}`): `fa` takes `a`, `fb` takes `b`. They are statically independent
  (`fa_fb_independent`).
* **`a.b + b.a`** (`SEQ = {r}`): `ga₁` takes `r` and makes `s₁`, then `gb₁` takes `s₁`; or `gb₂` takes
  `r` and makes `s₂`, then `ga₂` takes `s₂`. The first firings race for `r`.
* **`(a | b) + a.b`** (`MIX = {i, j}`): `ha` takes `i` and `hb` takes `j`, independently; or `hs` takes
  both and makes `m`, then `ht` takes `m`. `hs` races with both `ha` and `hb`, and `ht` depends on
  `hs` (`hs_ht_dependent`).

## Results

* **Step ⊊ interleaving** (`step_strictly_finer`): `a | b` and `a.b + b.a` are interleaving bisimilar
  (`bisimilar_PAR_SEQ`) and not step bisimilar (`not_stepBisimilar_PAR_SEQ`): only `a | b` fires
  `{a, b}` as one step. The expansion law fails for step bisimilarity.
* **History-preserving ⊊ step** (`hp_strictly_finer`): `a | b` and `(a | b) + a.b` are step bisimilar
  (`stepBisimilar_PAR_MIX`) and not history-preserving bisimilar (`not_hpBisimilar_PAR_MIX`): after
  `hs`, the `b` of `MIX` has the `a` in its causal past, and no `b` of `a | b` does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.StepControls

open AnnotatedRuns (Firing follow Executable StaticIndependent)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uT uS

/-- Occurrence identities. -/
inductive Site
  | a | b | r | s₁ | s₂ | i | j | m
  deriving DecidableEq

/-- Action names. -/
inductive Act
  | a | b
  deriving DecidableEq

variable {T : Type uT} {S : Type uS} (τ : T)

/-- Every occurrence carries `τ`. -/
def label : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes `made`. -/
def firing (taken made : List Site) : Firing T S Site :=
  ⟨⟨taken.map (label τ), [], [], [], made.map (label τ)⟩, [], ⟨taken, [], made⟩⟩

def fa : Firing T S Site := firing τ [.a] []
def fb : Firing T S Site := firing τ [.b] []
def ga₁ : Firing T S Site := firing τ [.r] [.s₁]
def gb₁ : Firing T S Site := firing τ [.s₁] []
def gb₂ : Firing T S Site := firing τ [.r] [.s₂]
def ga₂ : Firing T S Site := firing τ [.s₂] []
def ha : Firing T S Site := firing τ [.i] []
def hb : Firing T S Site := firing τ [.j] []
def hs : Firing T S Site := firing τ [.i, .j] [.m]
def ht : Firing T S Site := firing τ [.m] []

/-- `a | b` beside `a.b + b.a`. -/
def alphabet₃ : List (Act × Firing T S Site) :=
  [(.a, fa τ), (.b, fb τ), (.a, ga₁ τ), (.b, gb₁ τ), (.b, gb₂ τ), (.a, ga₂ τ)]

/-- `a | b` beside `(a | b) + a.b`. -/
def alphabet₄ : List (Act × Firing T S Site) :=
  [(.a, fa τ), (.b, fb τ), (.a, ha τ), (.b, hb τ), (.a, hs τ), (.b, ht τ)]

/-- The program of a named alphabet. -/
def offers (alphabet : List (Act × Firing T S Site)) (ℓ : Act) (f : Firing T S Site) : Prop :=
  (ℓ, f) ∈ alphabet

/-- `n` copies of `(τ, τ)`. -/
def E (n : ℕ) : EquationStore T := List.replicate n (τ, τ)

def PAR : Configuration T Site := ⟨[], {.a, .b}⟩
def PARa : Configuration T Site := ⟨E τ 1, {.b}⟩
def PARb : Configuration T Site := ⟨E τ 1, {.a}⟩
def SEQ : Configuration T Site := ⟨[], {.r}⟩
def SEQa : Configuration T Site := ⟨E τ 1, {.s₁}⟩
def SEQb : Configuration T Site := ⟨E τ 1, {.s₂}⟩
def MIX : Configuration T Site := ⟨[], {.i, .j}⟩
def MIXa : Configuration T Site := ⟨E τ 1, {.j}⟩
def MIXb : Configuration T Site := ⟨E τ 1, {.i}⟩
def MIXs : Configuration T Site := ⟨E τ 2, {.m}⟩
def End₂ : Configuration T Site := ⟨E τ 2, ∅⟩
def End₃ : Configuration T Site := ⟨E τ 3, ∅⟩

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

theorem ground_firing (taken made : List Site) (takenNodup : taken.Nodup) (madeNodup : made.Nodup) :
    Ground (label τ) (firing (S := S) τ taken made) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, takenNodup, madeNodup⟩

theorem ground₃ : ∀ x ∈ alphabet₃ (S := S) τ, Ground (label τ) x.2 := by
  intro x member
  simp only [alphabet₃, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ground_firing τ _ _ (of_decide_eq_true rfl) (of_decide_eq_true rfl)

theorem ground₄ : ∀ x ∈ alphabet₄ (S := S) τ, Ground (label τ) x.2 := by
  intro x member
  simp only [alphabet₄, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ground_firing τ _ _ (of_decide_eq_true rfl) (of_decide_eq_true rfl)

variable (A : SubstitutionAction T S)

theorem valid₃ {ℓ : Act} {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet₃ τ) {C : Configuration T Site}
    (refl : Reflexive C.equations) :
    f.Valid A (label τ) C ↔ Enabled (label τ) C.present (f.selection.commit (T := T)) :=
  (ground₃ τ (ℓ, f) member).valid_iff A refl

theorem valid₄ {ℓ : Act} {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet₄ τ) {C : Configuration T Site}
    (refl : Reflexive C.equations) :
    f.Valid A (label τ) C ↔ Enabled (label τ) C.present (f.selection.commit (T := T)) :=
  (ground₄ τ (ℓ, f) member).valid_iff A refl

/-! ## Results of firings -/

theorem result_fa : (fa (S := S) τ).result (label τ) PAR = PARa τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_fb : (fb (S := S) τ).result (label τ) PAR = PARb τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_fb_a : (fb (S := S) τ).result (label τ) (PARa τ) = End₂ τ :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_fa_b : (fa (S := S) τ).result (label τ) (PARb τ) = End₂ τ :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_ga₁ : (ga₁ (S := S) τ).result (label τ) SEQ = SEQa τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_gb₂ : (gb₂ (S := S) τ).result (label τ) SEQ = SEQb τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_gb₁ : (gb₁ (S := S) τ).result (label τ) (SEQa τ) = End₂ τ :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_ga₂ : (ga₂ (S := S) τ).result (label τ) (SEQb τ) = End₂ τ :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_ha : (ha (S := S) τ).result (label τ) MIX = MIXa τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_hb : (hb (S := S) τ).result (label τ) MIX = MIXb τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_hs : (hs (S := S) τ).result (label τ) MIX = MIXs τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_hb_a : (hb (S := S) τ).result (label τ) (MIXa τ) = End₂ τ :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_ha_b : (ha (S := S) τ).result (label τ) (MIXb τ) = End₂ τ :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_ht : (ht (S := S) τ).result (label τ) (MIXs τ) = End₃ τ :=
  config_eq rfl (of_decide_eq_true rfl)

/-! ## Admitted firings at each configuration -/

section Admitted

variable {τ A}
variable {ℓ : Act} {f : Firing T S Site}

theorem at₃_PAR (member : (ℓ, f) ∈ alphabet₃ τ) (valid : f.Valid A (label τ) PAR) :
    (ℓ = .a ∧ f = fa τ) ∨ (ℓ = .b ∧ f = fb τ) := by
  rw [valid₃ τ A member reflexive_nil] at valid
  simp only [alphabet₃, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₃_PARa (member : (ℓ, f) ∈ alphabet₃ τ) (valid : f.Valid A (label τ) (PARa τ)) :
    ℓ = .b ∧ f = fb τ := by
  rw [valid₃ τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet₃, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₃_PARb (member : (ℓ, f) ∈ alphabet₃ τ) (valid : f.Valid A (label τ) (PARb τ)) :
    ℓ = .a ∧ f = fa τ := by
  rw [valid₃ τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet₃, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₃_SEQ (member : (ℓ, f) ∈ alphabet₃ τ) (valid : f.Valid A (label τ) SEQ) :
    (ℓ = .a ∧ f = ga₁ τ) ∨ (ℓ = .b ∧ f = gb₂ τ) := by
  rw [valid₃ τ A member reflexive_nil] at valid
  simp only [alphabet₃, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact .inl ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact .inr ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)

theorem at₃_SEQa (member : (ℓ, f) ∈ alphabet₃ τ) (valid : f.Valid A (label τ) (SEQa τ)) :
    ℓ = .b ∧ f = gb₁ τ := by
  rw [valid₃ τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet₃, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₃_SEQb (member : (ℓ, f) ∈ alphabet₃ τ) (valid : f.Valid A (label τ) (SEQb τ)) :
    ℓ = .a ∧ f = ga₂ τ := by
  rw [valid₃ τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet₃, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact ⟨rfl, rfl⟩

theorem at₃_End₂ (member : (ℓ, f) ∈ alphabet₃ τ) : ¬ f.Valid A (label τ) (End₂ τ) := by
  intro valid
  rw [valid₃ τ A member (reflexive_E τ 2)] at valid
  simp only [alphabet₃, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact absurd valid (of_decide_eq_false rfl)

theorem at₄_PAR (member : (ℓ, f) ∈ alphabet₄ τ) (valid : f.Valid A (label τ) PAR) :
    (ℓ = .a ∧ f = fa τ) ∨ (ℓ = .b ∧ f = fb τ) := by
  rw [valid₄ τ A member reflexive_nil] at valid
  simp only [alphabet₄, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₄_PARa (member : (ℓ, f) ∈ alphabet₄ τ) (valid : f.Valid A (label τ) (PARa τ)) :
    ℓ = .b ∧ f = fb τ := by
  rw [valid₄ τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet₄, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₄_PARb (member : (ℓ, f) ∈ alphabet₄ τ) (valid : f.Valid A (label τ) (PARb τ)) :
    ℓ = .a ∧ f = fa τ := by
  rw [valid₄ τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet₄, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₄_MIX (member : (ℓ, f) ∈ alphabet₄ τ) (valid : f.Valid A (label τ) MIX) :
    (ℓ = .a ∧ f = ha τ) ∨ (ℓ = .b ∧ f = hb τ) ∨ (ℓ = .a ∧ f = hs τ) := by
  rw [valid₄ τ A member reflexive_nil] at valid
  simp only [alphabet₄, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr (.inl ⟨rfl, rfl⟩)
  · exact .inr (.inr ⟨rfl, rfl⟩)
  · exact absurd valid (of_decide_eq_false rfl)

theorem at₄_MIXa (member : (ℓ, f) ∈ alphabet₄ τ) (valid : f.Valid A (label τ) (MIXa τ)) :
    ℓ = .b ∧ f = hb τ := by
  rw [valid₄ τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet₄, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₄_MIXb (member : (ℓ, f) ∈ alphabet₄ τ) (valid : f.Valid A (label τ) (MIXb τ)) :
    ℓ = .a ∧ f = ha τ := by
  rw [valid₄ τ A member (reflexive_E τ 1)] at valid
  simp only [alphabet₄, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact ⟨rfl, rfl⟩
  all_goals exact absurd valid (of_decide_eq_false rfl)

theorem at₄_MIXs (member : (ℓ, f) ∈ alphabet₄ τ) (valid : f.Valid A (label τ) (MIXs τ)) :
    ℓ = .b ∧ f = ht τ := by
  rw [valid₄ τ A member (reflexive_E τ 2)] at valid
  simp only [alphabet₄, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)
  · exact ⟨rfl, rfl⟩

theorem at₄_End (n : ℕ) (member : (ℓ, f) ∈ alphabet₄ τ) :
    ¬ f.Valid A (label τ) ⟨E τ n, ∅⟩ := by
  intro valid
  rw [valid₄ τ A member (reflexive_E τ n)] at valid
  simp only [alphabet₄, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact absurd valid (of_decide_eq_false rfl)

end Admitted

theorem valid₃_of (ℓ : Act) {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet₃ τ) {C : Configuration T Site}
    (refl : Reflexive C.equations) (enabled : Enabled (label τ) C.present (f.selection.commit (T := T))) :
    f.Valid A (label τ) C :=
  (valid₃ τ A member refl).mpr enabled

theorem valid₄_of (ℓ : Act) {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet₄ τ) {C : Configuration T Site}
    (refl : Reflexive C.equations) (enabled : Enabled (label τ) C.present (f.selection.commit (T := T))) :
    f.Valid A (label τ) C :=
  (valid₄ τ A member refl).mpr enabled

/-! ## Independence -/

theorem pure_firing (taken made : List Site) : Pure (firing (S := S) τ taken made) := ⟨rfl, rfl, rfl⟩

include A in
theorem fa_fb_independent : StaticIndependent (label τ) (fa (S := S) τ) (fb τ) := by
  have : Nonempty S := ⟨A.identity⟩
  exact (staticIndependent_iff_provenance (label τ) (e := fa τ) (f := fb τ) (pure_firing τ _ _) (pure_firing τ _ _)
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mpr ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩

include A in
theorem fb_fa_independent : StaticIndependent (label τ) (fb (S := S) τ) (fa τ) :=
  (fa_fb_independent τ A).symm

include A in
theorem ga₁_gb₁_dependent : ¬ StaticIndependent (label τ) (ga₁ (S := S) τ) (gb₁ τ) := by
  have : Nonempty S := ⟨A.identity⟩
  intro independent
  exact absurd ((staticIndependent_iff_provenance (label τ) (e := ga₁ τ) (f := gb₁ τ) (pure_firing τ _ _)
    (pure_firing τ _ _) (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mp independent).1
    (of_decide_eq_false rfl)

include A in
theorem gb₂_ga₂_dependent : ¬ StaticIndependent (label τ) (gb₂ (S := S) τ) (ga₂ τ) := by
  have : Nonempty S := ⟨A.identity⟩
  intro independent
  exact absurd ((staticIndependent_iff_provenance (label τ) (e := gb₂ τ) (f := ga₂ τ) (pure_firing τ _ _)
    (pure_firing τ _ _) (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mp independent).1
    (of_decide_eq_false rfl)

include A in
theorem hs_ht_dependent : ¬ StaticIndependent (label τ) (hs (S := S) τ) (ht τ) := by
  have : Nonempty S := ⟨A.identity⟩
  intro independent
  exact absurd ((staticIndependent_iff_provenance (label τ) (e := hs τ) (f := ht τ) (pure_firing τ _ _)
    (pure_firing τ _ _) (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mp independent).1
    (of_decide_eq_false rfl)

/-! ## Step ⊊ interleaving: `a | b` against `a.b + b.a` -/

/-- **`a | b` and `a.b + b.a` are interleaving bisimilar.** -/
theorem bisimilar_PAR_SEQ : Bisimilar A (label τ) (offers (alphabet₃ τ)) PAR SEQ := by
  refine ⟨fun C D => (C = PAR ∧ D = SEQ) ∨ (C = PARa τ ∧ D = SEQa τ) ∨ (C = PARb τ ∧ D = SEQb τ) ∨
    (C = End₂ τ ∧ D = End₂ τ), ⟨?_, ?_, ?_⟩, .inl ⟨rfl, rfl⟩⟩
  · rintro C D (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ C' ⟨f, member, valid, rfl⟩
    · rcases at₃_PAR member valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨SEQa τ, ⟨ga₁ τ, by simp [offers, alphabet₃],
          valid₃_of τ A .a (by simp [alphabet₃]) reflexive_nil (of_decide_eq_true rfl), (result_ga₁ τ).symm⟩,
          .inr (.inl ⟨result_fa τ, rfl⟩)⟩
      · exact ⟨SEQb τ, ⟨gb₂ τ, by simp [offers, alphabet₃],
          valid₃_of τ A .b (by simp [alphabet₃]) reflexive_nil (of_decide_eq_true rfl), (result_gb₂ τ).symm⟩,
          .inr (.inr (.inl ⟨result_fb τ, rfl⟩))⟩
    · obtain ⟨rfl, rfl⟩ := at₃_PARa member valid
      exact ⟨End₂ τ, ⟨gb₁ τ, by simp [offers, alphabet₃],
        valid₃_of τ A .b (by simp [alphabet₃]) (reflexive_E τ 1) (of_decide_eq_true rfl),
        (result_gb₁ τ).symm⟩, .inr (.inr (.inr ⟨result_fb_a τ, rfl⟩))⟩
    · obtain ⟨rfl, rfl⟩ := at₃_PARb member valid
      exact ⟨End₂ τ, ⟨ga₂ τ, by simp [offers, alphabet₃],
        valid₃_of τ A .a (by simp [alphabet₃]) (reflexive_E τ 1) (of_decide_eq_true rfl),
        (result_ga₂ τ).symm⟩, .inr (.inr (.inr ⟨result_fa_b τ, rfl⟩))⟩
    · exact absurd valid (at₃_End₂ member)
  · rintro C D (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ D' ⟨f, member, valid, rfl⟩
    · rcases at₃_SEQ member valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨PARa τ, ⟨fa τ, by simp [offers, alphabet₃],
          valid₃_of τ A .a (by simp [alphabet₃]) reflexive_nil (of_decide_eq_true rfl), (result_fa τ).symm⟩,
          .inr (.inl ⟨rfl, result_ga₁ τ⟩)⟩
      · exact ⟨PARb τ, ⟨fb τ, by simp [offers, alphabet₃],
          valid₃_of τ A .b (by simp [alphabet₃]) reflexive_nil (of_decide_eq_true rfl), (result_fb τ).symm⟩,
          .inr (.inr (.inl ⟨rfl, result_gb₂ τ⟩))⟩
    · obtain ⟨rfl, rfl⟩ := at₃_SEQa member valid
      exact ⟨End₂ τ, ⟨fb τ, by simp [offers, alphabet₃],
        valid₃_of τ A .b (by simp [alphabet₃]) (reflexive_E τ 1) (of_decide_eq_true rfl),
        (result_fb_a τ).symm⟩, .inr (.inr (.inr ⟨rfl, result_gb₁ τ⟩))⟩
    · obtain ⟨rfl, rfl⟩ := at₃_SEQb member valid
      exact ⟨End₂ τ, ⟨fa τ, by simp [offers, alphabet₃],
        valid₃_of τ A .a (by simp [alphabet₃]) (reflexive_E τ 1) (of_decide_eq_true rfl),
        (result_fa_b τ).symm⟩, .inr (.inr (.inr ⟨rfl, result_ga₂ τ⟩))⟩
    · exact absurd valid (at₃_End₂ member)
  · intro _ _ _ atom
    exact atom.elim

/-- `a | b` fires `{a, b}` as one step. -/
theorem PAR_steps_both₃ : StepMoves A (label τ) (offers (alphabet₃ τ)) PAR ↑[Act.a, Act.b] (End₂ τ) := by
  refine ⟨[(.a, fa τ), (.b, fb τ)], List.cons_ne_nil _ _, ?_, ?_, ?_, rfl, ?_⟩
  · intro x member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [offers, alphabet₃]
  · exact List.pairwise_pair.mpr (fa_fb_independent τ A)
  · refine ⟨valid₃_of τ A .a (by simp [alphabet₃]) reflexive_nil (of_decide_eq_true rfl), ?_⟩
    show (fb τ).Valid A (label τ) ((fa τ).result (label τ) PAR) ∧ _
    rw [result_fa]
    refine ⟨valid₃_of τ A .b (by simp [alphabet₃]) (reflexive_E τ 1) (of_decide_eq_true rfl), ?_⟩
    rw [result_fb_a]
    exact consistent_of_reflexive A (reflexive_E τ 2)
  · show End₂ τ = (fb τ).result (label τ) ((fa τ).result (label τ) PAR)
    rw [result_fa, result_fb_a]

/-- `a.b + b.a` has no step of two firings: its second firing always takes what its first made. -/
theorem SEQ_no_double_step {M : Multiset Act} {D : Configuration T Site}
    (stepped : StepMoves A (label τ) (offers (alphabet₃ τ)) SEQ M D) : Multiset.card M = 1 := by
  obtain ⟨w, nonempty, offered, pairwise, executable, rfl, rfl⟩ := stepped
  rcases w with _ | ⟨⟨ℓ₁, f₁⟩, _ | ⟨⟨ℓ₂, f₂⟩, rest⟩⟩
  · exact absurd rfl nonempty
  · rfl
  · exfalso
    have first := executable.1
    have second := executable.2.1
    have related := (List.pairwise_cons.mp pairwise).1 f₂ (List.mem_cons_self ..)
    rcases at₃_SEQ (offered _ (List.mem_cons_self ..)) first with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [result_ga₁] at second
      obtain ⟨rfl, rfl⟩ := at₃_SEQa (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
      exact ga₁_gb₁_dependent τ A related
    · rw [result_gb₂] at second
      obtain ⟨rfl, rfl⟩ := at₃_SEQb (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
      exact gb₂_ga₂_dependent τ A related

/-- **`a | b` and `a.b + b.a` are not step bisimilar**: the expansion law fails. -/
theorem not_stepBisimilar_PAR_SEQ : ¬ StepBisimilar A (label τ) (offers (alphabet₃ τ)) PAR SEQ := by
  rintro ⟨R, ⟨forward, _, _⟩, related⟩
  obtain ⟨D, stepped, _⟩ := forward related (↑[Act.a, Act.b] : Multiset Act) (PAR_steps_both₃ τ A)
  have := SEQ_no_double_step τ A stepped
  simp at this

/-- **Step bisimilarity is strictly finer than interleaving bisimilarity.** -/
theorem step_strictly_finer :
    Bisimilar A (label τ) (offers (alphabet₃ τ)) PAR SEQ ∧
      ¬ StepBisimilar A (label τ) (offers (alphabet₃ τ)) PAR SEQ :=
  ⟨bisimilar_PAR_SEQ τ A, not_stepBisimilar_PAR_SEQ τ A⟩

/-! ## History-preserving ⊊ step: `a | b` against `(a | b) + a.b` -/

section Four

theorem mem₄_fa : ((.a, fa τ) : Act × Firing T S Site) ∈ alphabet₄ τ := by simp [alphabet₄]
theorem mem₄_fb : ((.b, fb τ) : Act × Firing T S Site) ∈ alphabet₄ τ := by simp [alphabet₄]
theorem mem₄_ha : ((.a, ha τ) : Act × Firing T S Site) ∈ alphabet₄ τ := by simp [alphabet₄]
theorem mem₄_hb : ((.b, hb τ) : Act × Firing T S Site) ∈ alphabet₄ τ := by simp [alphabet₄]
theorem mem₄_hs : ((.a, hs τ) : Act × Firing T S Site) ∈ alphabet₄ τ := by simp [alphabet₄]
theorem mem₄_ht : ((.b, ht τ) : Act × Firing T S Site) ∈ alphabet₄ τ := by simp [alphabet₄]

include A in
theorem ha_hb_independent : StaticIndependent (label τ) (ha (S := S) τ) (hb τ) := by
  have : Nonempty S := ⟨A.identity⟩
  exact (staticIndependent_iff_provenance (label τ) (e := ha τ) (f := hb τ) (pure_firing τ _ _) (pure_firing τ _ _)
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mpr ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- A one-firing step. -/
theorem single_step {offers' : Act → Firing T S Site → Prop} {C : Configuration T Site} {ℓ : Act}
    {f : Firing T S Site} (offered : offers' ℓ f) (valid : f.Valid A (label τ) C) :
    StepMoves A (label τ) offers' C {ℓ} (f.result (label τ) C) :=
  stepMoves_singleton_iff.mpr ⟨f, offered, valid, rfl⟩

/-- A two-firing step of independent firings. -/
theorem double_step {offers' : Act → Firing T S Site → Prop} {C : Configuration T Site} {ℓ₁ ℓ₂ : Act}
    {f₁ f₂ : Firing T S Site} (offered₁ : offers' ℓ₁ f₁) (offered₂ : offers' ℓ₂ f₂)
    (independent : StaticIndependent (label τ) f₁ f₂) (valid₁ : f₁.Valid A (label τ) C)
    (valid₂ : f₂.Valid A (label τ) (f₁.result (label τ) C)) :
    StepMoves A (label τ) offers' C ↑[ℓ₁, ℓ₂] (f₂.result (label τ) (f₁.result (label τ) C)) := by
  refine ⟨[(ℓ₁, f₁), (ℓ₂, f₂)], List.cons_ne_nil _ _, ?_, List.pairwise_pair.mpr independent,
    ⟨valid₁, valid₂, valid₂.firing.consistent⟩, rfl, rfl⟩
  intro x member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact offered₁
  · exact offered₂

theorem pair_comm : (↑[Act.b, Act.a] : Multiset Act) = ↑[Act.a, Act.b] := by decide

theorem stepMoves_PAR {M : Multiset Act} {D : Configuration T Site} :
    StepMoves A (label τ) (offers (alphabet₄ τ)) PAR M D ↔
      (M = {Act.a} ∧ D = PARa τ) ∨ (M = {Act.b} ∧ D = PARb τ) ∨ (M = ↑[Act.a, Act.b] ∧ D = End₂ τ) := by
  constructor
  · rintro ⟨w, nonempty, offered, pairwise, executable, rfl, rfl⟩
    rcases w with _ | ⟨⟨ℓ₁, f₁⟩, _ | ⟨⟨ℓ₂, f₂⟩, _ | ⟨⟨ℓ₃, f₃⟩, rest⟩⟩⟩
    · exact absurd rfl nonempty
    · rcases at₄_PAR (offered _ (List.mem_cons_self ..)) executable.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl ⟨rfl, result_fa τ⟩
      · exact .inr (.inl ⟨rfl, result_fb τ⟩)
    · have second := executable.2.1
      rcases at₄_PAR (offered _ (List.mem_cons_self ..)) executable.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [result_fa] at second
        obtain ⟨rfl, rfl⟩ := at₄_PARa (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        refine .inr (.inr ⟨rfl, ?_⟩)
        show (fb τ).result (label τ) ((fa τ).result (label τ) PAR) = End₂ τ
        rw [result_fa, result_fb_a]
      · rw [result_fb] at second
        obtain ⟨rfl, rfl⟩ := at₄_PARb (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        refine .inr (.inr ⟨pair_comm, ?_⟩)
        show (fa τ).result (label τ) ((fb τ).result (label τ) PAR) = End₂ τ
        rw [result_fb, result_fa_b]
    · exfalso
      have second := executable.2.1
      have third := executable.2.2.1
      have member₃ := offered _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      rcases at₄_PAR (offered _ (List.mem_cons_self ..)) executable.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [result_fa] at second third
        obtain ⟨rfl, rfl⟩ := at₄_PARa (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        rw [result_fb_a] at third
        exact at₄_End 2 member₃ third
      · rw [result_fb] at second third
        obtain ⟨rfl, rfl⟩ := at₄_PARb (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        rw [result_fa_b] at third
        exact at₄_End 2 member₃ third
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [← result_fa τ]
      exact single_step τ A (mem₄_fa τ) (valid₄_of τ A .a (mem₄_fa τ) reflexive_nil (of_decide_eq_true rfl))
    · rw [← result_fb τ]
      exact single_step τ A (mem₄_fb τ) (valid₄_of τ A .b (mem₄_fb τ) reflexive_nil (of_decide_eq_true rfl))
    · rw [← result_fb_a τ, ← result_fa τ]
      refine double_step τ A (mem₄_fa τ) (mem₄_fb τ) (fa_fb_independent τ A)
        (valid₄_of τ A .a (mem₄_fa τ) reflexive_nil (of_decide_eq_true rfl)) ?_
      rw [result_fa]
      exact valid₄_of τ A .b (mem₄_fb τ) (reflexive_E τ 1) (of_decide_eq_true rfl)

theorem stepMoves_MIX {M : Multiset Act} {D : Configuration T Site} :
    StepMoves A (label τ) (offers (alphabet₄ τ)) MIX M D ↔
      (M = {Act.a} ∧ (D = MIXa τ ∨ D = MIXs τ)) ∨ (M = {Act.b} ∧ D = MIXb τ) ∨
        (M = ↑[Act.a, Act.b] ∧ D = End₂ τ) := by
  constructor
  · rintro ⟨w, nonempty, offered, pairwise, executable, rfl, rfl⟩
    rcases w with _ | ⟨⟨ℓ₁, f₁⟩, _ | ⟨⟨ℓ₂, f₂⟩, _ | ⟨⟨ℓ₃, f₃⟩, rest⟩⟩⟩
    · exact absurd rfl nonempty
    · rcases at₄_MIX (offered _ (List.mem_cons_self ..)) executable.1 with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl ⟨rfl, .inl (result_ha τ)⟩
      · exact .inr (.inl ⟨rfl, result_hb τ⟩)
      · exact .inl ⟨rfl, .inr (result_hs τ)⟩
    · have second := executable.2.1
      have related := (List.pairwise_cons.mp pairwise).1 f₂ (List.mem_cons_self ..)
      rcases at₄_MIX (offered _ (List.mem_cons_self ..)) executable.1 with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [result_ha] at second
        obtain ⟨rfl, rfl⟩ := at₄_MIXa (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        refine .inr (.inr ⟨rfl, ?_⟩)
        show (hb τ).result (label τ) ((ha τ).result (label τ) MIX) = End₂ τ
        rw [result_ha, result_hb_a]
      · rw [result_hb] at second
        obtain ⟨rfl, rfl⟩ := at₄_MIXb (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        refine .inr (.inr ⟨pair_comm, ?_⟩)
        show (ha τ).result (label τ) ((hb τ).result (label τ) MIX) = End₂ τ
        rw [result_hb, result_ha_b]
      · rw [result_hs] at second
        obtain ⟨rfl, rfl⟩ := at₄_MIXs (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        exact absurd related (hs_ht_dependent τ A)
    · exfalso
      have second := executable.2.1
      have third := executable.2.2.1
      have member₃ := offered _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      rcases at₄_MIX (offered _ (List.mem_cons_self ..)) executable.1 with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [result_ha] at second third
        obtain ⟨rfl, rfl⟩ := at₄_MIXa (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        rw [result_hb_a] at third
        exact at₄_End 2 member₃ third
      · rw [result_hb] at second third
        obtain ⟨rfl, rfl⟩ := at₄_MIXb (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        rw [result_ha_b] at third
        exact at₄_End 2 member₃ third
      · rw [result_hs] at second third
        obtain ⟨rfl, rfl⟩ := at₄_MIXs (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
        rw [result_ht] at third
        exact at₄_End 3 member₃ third
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [← result_ha τ]
      exact single_step τ A (mem₄_ha τ) (valid₄_of τ A .a (mem₄_ha τ) reflexive_nil (of_decide_eq_true rfl))
    · rw [← result_hs τ]
      exact single_step τ A (mem₄_hs τ) (valid₄_of τ A .a (mem₄_hs τ) reflexive_nil (of_decide_eq_true rfl))
    · rw [← result_hb τ]
      exact single_step τ A (mem₄_hb τ) (valid₄_of τ A .b (mem₄_hb τ) reflexive_nil (of_decide_eq_true rfl))
    · rw [← result_hb_a τ, ← result_ha τ]
      refine double_step τ A (mem₄_ha τ) (mem₄_hb τ) (ha_hb_independent τ A)
        (valid₄_of τ A .a (mem₄_ha τ) reflexive_nil (of_decide_eq_true rfl)) ?_
      rw [result_ha]
      exact valid₄_of τ A .b (mem₄_hb τ) (reflexive_E τ 1) (of_decide_eq_true rfl)

/-- The steps of a configuration that fires exactly one offered firing, and then halts. -/
theorem stepMoves_one {C C' : Configuration T Site} {ℓ : Act} {f : Firing T S Site}
    (member : (ℓ, f) ∈ alphabet₄ τ) (refl : Reflexive C.equations)
    (enabled : Enabled (label τ) C.present (f.selection.commit (T := T)))
    (only : ∀ {ℓ' f'}, (ℓ', f') ∈ alphabet₄ τ → f'.Valid A (label τ) C → ℓ' = ℓ ∧ f' = f)
    (after : f.result (label τ) C = C') (n : ℕ) (halts : C' = ⟨E τ n, ∅⟩) {M : Multiset Act}
    {D : Configuration T Site} :
    StepMoves A (label τ) (offers (alphabet₄ τ)) C M D ↔ M = {ℓ} ∧ D = C' := by
  constructor
  · rintro ⟨w, nonempty, offered, _, executable, rfl, rfl⟩
    rcases w with _ | ⟨⟨ℓ₁, f₁⟩, _ | ⟨⟨ℓ₂, f₂⟩, rest⟩⟩
    · exact absurd rfl nonempty
    · obtain ⟨rfl, rfl⟩ := only (offered _ (List.mem_cons_self ..)) executable.1
      exact ⟨rfl, after⟩
    · exfalso
      have second := executable.2.1
      obtain ⟨rfl, rfl⟩ := only (offered _ (List.mem_cons_self ..)) executable.1
      rw [after, halts] at second
      exact at₄_End n (offered _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) second
  · rintro ⟨rfl, rfl⟩
    rw [← after]
    exact single_step τ A member ((valid₄ τ A member refl).mpr enabled)

theorem stepMoves_End (n : ℕ) {M : Multiset Act} {D : Configuration T Site} :
    ¬ StepMoves A (label τ) (offers (alphabet₄ τ)) ⟨E τ n, ∅⟩ M D := by
  rintro ⟨w, nonempty, offered, _, executable, _, _⟩
  rcases w with _ | ⟨⟨ℓ₁, f₁⟩, rest⟩
  · exact nonempty rfl
  · exact at₄_End n (offered _ (List.mem_cons_self ..)) executable.1

theorem stepMoves_PARa {M : Multiset Act} {D : Configuration T Site} :
    StepMoves A (label τ) (offers (alphabet₄ τ)) (PARa τ) M D ↔ M = {Act.b} ∧ D = End₂ τ :=
  stepMoves_one τ A (mem₄_fb τ) (reflexive_E τ 1) (of_decide_eq_true rfl) (at₄_PARa · ·)
    (result_fb_a τ) 2 rfl

theorem stepMoves_PARb {M : Multiset Act} {D : Configuration T Site} :
    StepMoves A (label τ) (offers (alphabet₄ τ)) (PARb τ) M D ↔ M = {Act.a} ∧ D = End₂ τ :=
  stepMoves_one τ A (mem₄_fa τ) (reflexive_E τ 1) (of_decide_eq_true rfl) (at₄_PARb · ·)
    (result_fa_b τ) 2 rfl

theorem stepMoves_MIXa {M : Multiset Act} {D : Configuration T Site} :
    StepMoves A (label τ) (offers (alphabet₄ τ)) (MIXa τ) M D ↔ M = {Act.b} ∧ D = End₂ τ :=
  stepMoves_one τ A (mem₄_hb τ) (reflexive_E τ 1) (of_decide_eq_true rfl) (at₄_MIXa · ·)
    (result_hb_a τ) 2 rfl

theorem stepMoves_MIXb {M : Multiset Act} {D : Configuration T Site} :
    StepMoves A (label τ) (offers (alphabet₄ τ)) (MIXb τ) M D ↔ M = {Act.a} ∧ D = End₂ τ :=
  stepMoves_one τ A (mem₄_ha τ) (reflexive_E τ 1) (of_decide_eq_true rfl) (at₄_MIXb · ·)
    (result_ha_b τ) 2 rfl

theorem stepMoves_MIXs {M : Multiset Act} {D : Configuration T Site} :
    StepMoves A (label τ) (offers (alphabet₄ τ)) (MIXs τ) M D ↔ M = {Act.b} ∧ D = End₃ τ :=
  stepMoves_one τ A (mem₄_ht τ) (reflexive_E τ 2) (of_decide_eq_true rfl) (at₄_MIXs · ·)
    (result_ht τ) 3 rfl

/-- **`a | b` and `(a | b) + a.b` are step bisimilar.** -/
theorem stepBisimilar_PAR_MIX : StepBisimilar A (label τ) (offers (alphabet₄ τ)) PAR MIX := by
  refine ⟨fun C D => (C = PAR ∧ D = MIX) ∨ (C = PARa τ ∧ D = MIXa τ) ∨ (C = PARa τ ∧ D = MIXs τ) ∨
    (C = PARb τ ∧ D = MIXb τ) ∨ (C = End₂ τ ∧ D = End₂ τ) ∨ (C = End₂ τ ∧ D = End₃ τ),
    ⟨?_, ?_, ?_⟩, .inl ⟨rfl, rfl⟩⟩
  · rintro C D (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) M C' stepped
    · rcases (stepMoves_PAR τ A).mp stepped with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨MIXa τ, (stepMoves_MIX τ A).mpr (.inl ⟨rfl, .inl rfl⟩), .inr (.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨MIXb τ, (stepMoves_MIX τ A).mpr (.inr (.inl ⟨rfl, rfl⟩)),
          .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))⟩
      · exact ⟨End₂ τ, (stepMoves_MIX τ A).mpr (.inr (.inr ⟨rfl, rfl⟩)),
          .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
    · obtain ⟨rfl, rfl⟩ := (stepMoves_PARa τ A).mp stepped
      exact ⟨End₂ τ, (stepMoves_MIXa τ A).mpr ⟨rfl, rfl⟩, .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
    · obtain ⟨rfl, rfl⟩ := (stepMoves_PARa τ A).mp stepped
      exact ⟨End₃ τ, (stepMoves_MIXs τ A).mpr ⟨rfl, rfl⟩, .inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))⟩
    · obtain ⟨rfl, rfl⟩ := (stepMoves_PARb τ A).mp stepped
      exact ⟨End₂ τ, (stepMoves_MIXb τ A).mpr ⟨rfl, rfl⟩, .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
    · exact absurd stepped (stepMoves_End τ A 2)
    · exact absurd stepped (stepMoves_End τ A 2)
  · rintro C D (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) M D' stepped
    · rcases (stepMoves_MIX τ A).mp stepped with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨PARa τ, (stepMoves_PAR τ A).mpr (.inl ⟨rfl, rfl⟩), .inr (.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨PARa τ, (stepMoves_PAR τ A).mpr (.inl ⟨rfl, rfl⟩), .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨PARb τ, (stepMoves_PAR τ A).mpr (.inr (.inl ⟨rfl, rfl⟩)),
          .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))⟩
      · exact ⟨End₂ τ, (stepMoves_PAR τ A).mpr (.inr (.inr ⟨rfl, rfl⟩)),
          .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
    · obtain ⟨rfl, rfl⟩ := (stepMoves_MIXa τ A).mp stepped
      exact ⟨End₂ τ, (stepMoves_PARa τ A).mpr ⟨rfl, rfl⟩, .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
    · obtain ⟨rfl, rfl⟩ := (stepMoves_MIXs τ A).mp stepped
      exact ⟨End₂ τ, (stepMoves_PARa τ A).mpr ⟨rfl, rfl⟩, .inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))⟩
    · obtain ⟨rfl, rfl⟩ := (stepMoves_MIXb τ A).mp stepped
      exact ⟨End₂ τ, (stepMoves_PARb τ A).mpr ⟨rfl, rfl⟩, .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))⟩
    · exact absurd stepped (stepMoves_End τ A 2)
    · exact absurd stepped (stepMoves_End τ A 3)
  · intro _ _ _ atom
    exact atom.elim

theorem past_nil (f : Firing T S Site) : past (label τ) ([] : History T S Site) f = ∅ :=
  Finset.subset_empty.mp (past_subset_range wf_nil)

/-- **`a | b` and `(a | b) + a.b` are not history-preserving bisimilar.** After `hs`, the `b` of
`(a | b) + a.b` has its `a` in its causal past; no `b` of `a | b` does. -/
theorem not_hpBisimilar_PAR_MIX : ¬ HPBisimilar A (label τ) (offers (alphabet₄ τ)) PAR MIX := by
  rintro ⟨R, bisimulation, related⟩
  -- `MIX` fires `hs`; `PAR` must answer with `fa`.
  obtain ⟨x, moved, related'⟩ := bisimulation.2.1 related ((Act.a : Act), (∅ : Finset ℕ))
    (show HMoves A (label τ) (offers (alphabet₄ τ)) (MIX, []) (Act.a, ∅)
      ((hs τ).result (label τ) MIX, [] ++ [(hs τ, ∅)]) from
      ⟨hs τ, mem₄_hs τ, valid₄_of τ A .a (mem₄_hs τ) reflexive_nil (of_decide_eq_true rfl),
        (past_nil τ _).symm, rfl⟩)
  obtain ⟨f, offered, valid, _, rfl⟩ := moved
  rcases at₄_PAR offered valid with ⟨_, rfl⟩ | ⟨wrong, _⟩
  swap
  · exact absurd wrong (by simp)
  -- `MIX` fires `ht`, which depends on position `0`; `PAR` can only fire `fb`, which does not.
  have dependentPast : 0 ∈ past (label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ) :=
    directPast_subset_past _ _ (mem_directPast.mpr ⟨by simp, _, rfl, hs_ht_dependent τ A⟩)
  obtain ⟨y, moved', _⟩ := bisimulation.2.1 related'
    ((Act.b : Act), past (label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ))
    (show HMoves A (label τ) (offers (alphabet₄ τ)) ((hs τ).result (label τ) MIX, [] ++ [(hs τ, ∅)])
      (Act.b, past (label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ))
      ((ht τ).result (label τ) ((hs τ).result (label τ) MIX), ([] ++ [(hs τ, ∅)]) ++
        [(ht τ, past (label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ))]) from
      ⟨ht τ, mem₄_ht τ, by
        rw [result_hs]
        exact valid₄_of τ A .b (mem₄_ht τ) (reflexive_E τ 2) (of_decide_eq_true rfl), rfl, rfl⟩)
  obtain ⟨g, offered', valid', samePast, _⟩ := moved'
  rw [result_fa] at valid'
  obtain ⟨_, rfl⟩ := at₄_PARa offered' valid'
  have independentPast : past (label τ) ([] ++ [(fa (S := S) τ, (∅ : Finset ℕ))]) (fb τ) ⊆
      Finset.range 0 := by
    refine past_subset_of_independent (wf_concat wf_nil (Finset.empty_subset _)) ?_
    intro i e _ get
    rcases getElem?_concat_eq_some get with ⟨lt, _⟩ | ⟨_, rfl⟩
    · simp at lt
    · exact fa_fb_independent τ A
  have key : past (label τ) [(hs (S := S) τ, (∅ : Finset ℕ))] (ht τ) =
      past (label τ) ([] ++ [(fa (S := S) τ, (∅ : Finset ℕ))]) (fb τ) := samePast
  rw [key] at dependentPast
  have := independentPast dependentPast
  simp at this

/-- **History-preserving bisimilarity is strictly finer than step bisimilarity.** -/
theorem hp_strictly_finer :
    StepBisimilar A (label τ) (offers (alphabet₄ τ)) PAR MIX ∧
      ¬ HPBisimilar A (label τ) (offers (alphabet₄ τ)) PAR MIX :=
  ⟨stepBisimilar_PAR_MIX τ A, not_hpBisimilar_PAR_MIX τ A⟩

end Four

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.StepControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.StepControls in
#print axioms bisimilar_PAR_SEQ
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.StepControls in
#print axioms not_stepBisimilar_PAR_SEQ
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.StepControls in
#print axioms step_strictly_finer
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.StepControls in
#print axioms stepBisimilar_PAR_MIX
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.StepControls in
#print axioms not_hpBisimilar_PAR_MIX
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.StepControls in
#print axioms hp_strictly_finer
