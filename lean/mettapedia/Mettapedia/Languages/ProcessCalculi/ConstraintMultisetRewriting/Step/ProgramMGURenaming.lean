import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEquationsControls

/-!
# Most general unifiers are unique up to renaming

Eder's theorem ("Properties of substitutions and unifications", 1985): two substitutions that are
each more general than the other differ by a renaming. Here the renaming is a pair of
variable-to-variable substitutions, inverse to each other on the variables of the two ranges
(`renaming_of_mutual`).

* **Most general unifiers** (`mgu_unique_up_to_renaming`): any two most general unifiers of one
  problem differ by such a renaming.
* **Answers of pattern equations** (`answer_unique_up_to_renaming`, `answer_is_renamed_answer`):
  the reference step `EqStep` takes any most general unifier, so its result is fixed only up to
  renaming; the answer computed by the total unifier (`ProgramEquations.answers`) is one of them,
  and every other is its image under a renaming.
* **Controls**: the call `(f $y)` against `(= (f $x) (g $x))` has two most general unifiers that
  bind in opposite directions (`two_orientations`); their answers differ syntactically
  (`orientations_differ`) and are renamings of each other (`orientations_rename`). Most
  generality is necessary: a unifier that is not most general is no renaming of the most general
  one (`instance_is_no_renaming`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramMGURenaming

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

section General

variable {σ : LPSignature} [DecidableEq σ.vars]

/-- A substitution mapping every variable to a variable. -/
def IsRenaming (ρ : Subst σ) : Prop := ∀ x, ∃ y, ρ x = .var y

/-- A variable occurring in the range of a substitution. -/
def RangeVar (θ : Subst σ) (x : σ.vars) : Prop := ∃ v, x ∈ (θ v).freeVars

omit [DecidableEq σ.vars] in
theorem var_of_apply_eq_var {β : Subst σ} {t : Term σ} {x : σ.vars}
    (h : β.applyTerm t = .var x) : ∃ y, t = .var y := by
  cases t with
  | var y => exact ⟨y, rfl⟩
  | const c =>
      rw [Subst.applyTerm_const] at h
      cases h
  | app f ts =>
      rw [Subst.applyTerm_app] at h
      cases h

open Classical in
/-- `α` on the range variables of `θ`, the identity elsewhere. -/
noncomputable def restrictTo (θ α : Subst σ) : Subst σ := fun x =>
  if RangeVar θ x then α x else .var x

theorem apply_comp_congr {θ θ' ρ : Subst σ} (factor : ∀ v, θ' v = ρ.applyTerm (θ v)) (t : Term σ) :
    θ'.applyTerm t = ρ.applyTerm (θ.applyTerm t) := by
  rw [← Subst.applyTerm_comp]
  exact Subst.applyTerm_congr fun v _ => factor v

/-- **Mutually more general substitutions differ by a renaming** (Eder): there are
variable-to-variable substitutions `ρ` and `ρ'`, inverse to each other on the range variables,
with `θ' = ρ ∘ θ` and `θ = ρ' ∘ θ'`. -/
theorem renaming_of_mutual {θ θ' : Subst σ} (general : θ.moreGeneral θ')
    (general' : θ'.moreGeneral θ) :
    ∃ ρ ρ' : Subst σ, IsRenaming ρ ∧ IsRenaming ρ' ∧
      (∀ v, θ' v = ρ.applyTerm (θ v)) ∧ (∀ v, θ v = ρ'.applyTerm (θ' v)) ∧
      (∀ x, RangeVar θ x → ρ'.applyTerm (ρ x) = .var x) ∧
      (∀ x, RangeVar θ' x → ρ.applyTerm (ρ' x) = .var x) := by
  obtain ⟨α, hα⟩ := general
  obtain ⟨β, hβ⟩ := general'
  have back : ∀ {θ₁ θ₂ α₁ β₁ : Subst σ}, (∀ v, θ₂ v = α₁.applyTerm (θ₁ v)) →
      (∀ v, θ₁ v = β₁.applyTerm (θ₂ v)) → ∀ x, RangeVar θ₁ x → β₁.applyTerm (α₁ x) = .var x := by
    intro θ₁ θ₂ α₁ β₁ h₁ h₂ x ⟨v, hx⟩
    have fixed : (β₁ ∘ₛ α₁).applyTerm (θ₁ v) = θ₁ v := by
      rw [Subst.applyTerm_comp, ← h₁ v, ← h₂ v]
    exact Subst.var_fixed_of_applyTerm_eq_self fixed x hx
  have toRange : ∀ {θ₁ θ₂ α₁ β₁ : Subst σ}, (∀ v, θ₂ v = α₁.applyTerm (θ₁ v)) →
      (∀ v, θ₁ v = β₁.applyTerm (θ₂ v)) → ∀ x, RangeVar θ₁ x →
        ∃ y, α₁ x = .var y ∧ RangeVar θ₂ y := by
    intro θ₁ θ₂ α₁ β₁ h₁ h₂ x ⟨v, hx⟩
    obtain ⟨y, hy⟩ := var_of_apply_eq_var (back h₁ h₂ x ⟨v, hx⟩)
    refine ⟨y, hy, v, ?_⟩
    rw [h₁ v]
    exact Subst.mem_freeVars_applyTerm.mpr ⟨x, hx, by rw [hy]; exact Term.mem_freeVars_var.mpr rfl⟩
  have isRen : ∀ {θ₁ θ₂ α₁ β₁ : Subst σ}, (∀ v, θ₂ v = α₁.applyTerm (θ₁ v)) →
      (∀ v, θ₁ v = β₁.applyTerm (θ₂ v)) → IsRenaming (restrictTo θ₁ α₁) := by
    intro θ₁ θ₂ α₁ β₁ h₁ h₂ x
    unfold restrictTo
    split_ifs with h
    · obtain ⟨y, hy, -⟩ := toRange h₁ h₂ x h
      exact ⟨y, hy⟩
    · exact ⟨x, rfl⟩
  have factor : ∀ {θ₁ θ₂ α₁ : Subst σ}, (∀ v, θ₂ v = α₁.applyTerm (θ₁ v)) →
      ∀ v, θ₂ v = (restrictTo θ₁ α₁).applyTerm (θ₁ v) := by
    intro θ₁ θ₂ α₁ h₁ v
    rw [h₁ v]
    refine Subst.applyTerm_congr fun x hx => ?_
    unfold restrictTo
    rw [if_pos ⟨v, hx⟩]
  have inverse : ∀ {θ₁ θ₂ α₁ β₁ : Subst σ}, (∀ v, θ₂ v = α₁.applyTerm (θ₁ v)) →
      (∀ v, θ₁ v = β₁.applyTerm (θ₂ v)) → ∀ x, RangeVar θ₁ x →
        (restrictTo θ₂ β₁).applyTerm (restrictTo θ₁ α₁ x) = .var x := by
    intro θ₁ θ₂ α₁ β₁ h₁ h₂ x hx
    obtain ⟨y, hy, hy'⟩ := toRange h₁ h₂ x hx
    have step : restrictTo θ₁ α₁ x = .var y := by
      unfold restrictTo
      rw [if_pos hx, hy]
    rw [step, Subst.applyTerm_var]
    unfold restrictTo
    rw [if_pos hy', show β₁ y = β₁.applyTerm (α₁ x) by rw [hy]; rfl]
    exact back h₁ h₂ x hx
  exact ⟨restrictTo θ α, restrictTo θ' β, isRen hα hβ, isRen hβ hα, factor hα, factor hβ,
    inverse hα hβ, inverse hβ hα⟩

end General

/-! ## Most general unifiers and answers -/

/-- **Most general unifiers are unique up to renaming.** -/
theorem mgu_unique_up_to_renaming {P : List (Tm × Tm)} {θ θ' : Subst rows} (mgu : IsMGU P θ)
    (mgu' : IsMGU P θ') :
    ∃ ρ ρ' : Subst rows, IsRenaming ρ ∧ IsRenaming ρ' ∧
      (∀ v, θ' v = ρ.applyTerm (θ v)) ∧ (∀ v, θ v = ρ'.applyTerm (θ' v)) ∧
      (∀ x, RangeVar θ x → ρ'.applyTerm (ρ x) = .var x) ∧
      (∀ x, RangeVar θ' x → ρ.applyTerm (ρ' x) = .var x) :=
  renaming_of_mutual (mgu.general θ' mgu'.unifies) (mgu'.general θ mgu.unifies)

/-- The answer of an equation to a call, under a unifier: the right-hand side as the thread, and
the unifier applied to every other row. -/
def answerUnder (e : ProgramEquations.Equation) (n : ℕ) (θ : Subst rows) (F : Multiset Tm) : Multiset Tm :=
  thread (θ.applyTerm (e.rhs.at n)) ::ₘ F.map θ.applyTerm

theorem answerUnder_comp {e : ProgramEquations.Equation} {n : ℕ} {θ θ' ρ : Subst rows}
    (factor : ∀ v, θ' v = ρ.applyTerm (θ v)) (F : Multiset Tm) :
    answerUnder e n θ' F = (answerUnder e n θ F).map ρ.applyTerm := by
  rw [answerUnder, answerUnder, Multiset.map_cons, Multiset.map_map]
  congr 1
  · rw [thread, thread, apply_tagged, apply_comp_congr factor]
  · exact Multiset.map_congr rfl fun t _ => apply_comp_congr factor t

/-- **The answer of a call is unique up to renaming**: the answers under any two most general
unifiers of the call with the left-hand side are images of each other under renamings inverse on
the range variables. -/
theorem answer_unique_up_to_renaming {e : ProgramEquations.Equation} {n : ℕ} {t : Tm} {θ θ' : Subst rows}
    (mgu : IsMGU [(e.lhs.at n, t)] θ) (mgu' : IsMGU [(e.lhs.at n, t)] θ') (F : Multiset Tm) :
    ∃ ρ ρ' : Subst rows, IsRenaming ρ ∧ IsRenaming ρ' ∧
      answerUnder e n θ' F = (answerUnder e n θ F).map ρ.applyTerm ∧
      answerUnder e n θ F = (answerUnder e n θ' F).map ρ'.applyTerm := by
  obtain ⟨ρ, ρ', ren, ren', there, back, -, -⟩ := mgu_unique_up_to_renaming mgu mgu'
  exact ⟨ρ, ρ', ren, ren', answerUnder_comp there F, answerUnder_comp back F⟩

/-- **Every reference answer is a renaming of the computed answer**: for any most general unifier,
the result of `EqStep` is the image of the total unifier's answer (`ProgramEquations.answers`)
under a renaming. -/
theorem answer_is_renamed_answer {e : ProgramEquations.Equation} {n : ℕ} {t : Tm} {θ : Subst rows}
    (mgu : IsMGU [(e.lhs.at n, t)] θ) (F : Multiset Tm) :
    ∃ θ₀ ρ, unifyTotal [(e.lhs.at n, t)] = some θ₀ ∧ IsRenaming ρ ∧
      answerUnder e n θ F = (answerUnder e n θ₀ F).map ρ.applyTerm := by
  obtain ⟨θ₀, accepted⟩ := unifyTotal_complete ⟨θ, mgu.unifies⟩
  obtain ⟨ρ, -, ren, -, there, -⟩ := answer_unique_up_to_renaming (isMGU_of_unifyTotal accepted) mgu F
  exact ⟨θ₀, ρ, accepted, ren, there⟩

/-! ## Controls -/

/-- `(= (f $x) (g $x))`. -/
def eqFG : ProgramEquations.Equation := ⟨ptag 50 (.var 0), ptag 51 (.var 0)⟩

/-- The caller's variable `$y`, at scope `0`. -/
def vy : Tm := .var (0, 0)

/-- The equation's variable at scope `1`. -/
def vx : Tm := .var (1, 0)

def bindX : Subst rows := Subst.single (1, 0) vy
def bindY : Subst rows := Subst.single (0, 0) vx

theorem single_relevant {v : ℕ × ℕ} {w : ℕ × ℕ} (ne : v ≠ w) :
    (Subst.single (σ := rows) v (.var w)).RelevantIdempotent {v, w} := by
  refine ⟨fun x notIn => ?_, fun x _ => ?_, fun x y hy => ?_⟩
  · rw [Subst.single_ne (σ := rows) _ fun h => notIn (by simp [h])]
  · by_cases h : x = v
    · rw [h, Subst.single_eq (σ := rows)]
      intro y hy
      rw [Term.mem_freeVars_var (σ := rows)] at hy
      simp [hy]
    · rw [Subst.single_ne (σ := rows) _ h]
      intro y hy
      rw [Term.mem_freeVars_var (σ := rows)] at hy
      subst hy
      assumption
  · by_cases h : x = v
    · rw [h, Subst.single_eq (σ := rows), Term.mem_freeVars_var (σ := rows)] at hy
      rw [hy, Subst.single_ne (σ := rows) _ fun h' => ne h'.symm]
    · rw [Subst.single_ne (σ := rows) _ h, Term.mem_freeVars_var (σ := rows)] at hy
      rw [hy, Subst.single_ne (σ := rows) _ h]

theorem problem_vars : eqVars [(eqFG.lhs.at 1, tagged 50 vy)] = {(1, 0), (0, 0)} := by
  show eqVars [(tagged 50 vx, tagged 50 vy)] = _
  simp [eqVars, freeVars_tagged, vx, vy, Term.freeVars]

theorem problem_unifies_iff (δ : Subst rows) :
    Unifies δ [(eqFG.lhs.at 1, tagged 50 vy)] ↔ δ (1, 0) = δ (0, 0) := by
  show Unifies δ [(tagged 50 vx, tagged 50 vy)] ↔ _
  rw [unifies_tagged_iff, unifies_single]
  rfl

/-- **Two most general unifiers in opposite directions.** -/
theorem two_orientations :
    IsMGU [(eqFG.lhs.at 1, tagged 50 vy)] bindX ∧ IsMGU [(eqFG.lhs.at 1, tagged 50 vy)] bindY := by
  have ne : ((1, 0) : ℕ × ℕ) ≠ (0, 0) := by decide
  refine ⟨⟨(problem_unifies_iff _).mpr ?_, fun δ unifies => ⟨δ, fun v => ?_⟩, ?_⟩,
    ⟨(problem_unifies_iff _).mpr ?_, fun δ unifies => ⟨δ, fun v => ?_⟩, ?_⟩⟩
  · rw [bindX, Subst.single_eq (σ := rows), Subst.single_ne (σ := rows) _ ne.symm]
    rfl
  · rw [problem_unifies_iff] at unifies
    by_cases h : v = (1, 0)
    · rw [h, bindX, Subst.single_eq (σ := rows), unifies]
      rfl
    · rw [bindX, Subst.single_ne (σ := rows) _ h]
      rfl
  · rw [problem_vars]
    exact single_relevant ne
  · rw [bindY, Subst.single_eq (σ := rows), Subst.single_ne (σ := rows) _ ne]
    rfl
  · rw [problem_unifies_iff] at unifies
    by_cases h : v = (0, 0)
    · rw [h, bindY, Subst.single_eq (σ := rows), ← unifies]
      rfl
    · rw [bindY, Subst.single_ne (σ := rows) _ h]
      rfl
  · rw [problem_vars, Finset.pair_comm]
    exact single_relevant ne.symm

/-- **Their answers differ syntactically**: beside the caller's row `(out $y)`, one answer keeps
`$y` and the other renames it. -/
theorem orientations_differ :
    answerUnder eqFG 1 bindX {tagged 70 vy} ≠ answerUnder eqFG 1 bindY {tagged 70 vy} := by
  intro same
  have first : answerUnder eqFG 1 bindX {tagged 70 vy} = {thread (tagged 51 vy), tagged 70 vy} := by
    simp only [answerUnder, Multiset.map_singleton, eqFG, ptag_at, apply_tagged]
    rfl
  have second : answerUnder eqFG 1 bindY {tagged 70 vy} = {thread (tagged 51 vx), tagged 70 vx} := by
    simp only [answerUnder, Multiset.map_singleton, eqFG, ptag_at, apply_tagged]
    rfl
  rw [first, second] at same
  have : tagged 70 vy ∈ ({thread (tagged 51 vx), tagged 70 vx} : Multiset Tm) := by
    rw [← same]
    simp
  simp [thread, tagged_inj, vx, vy] at this

/-- **…and are renamings of each other.** -/
theorem orientations_rename :
    ∃ ρ : Subst rows, IsRenaming ρ ∧
      answerUnder eqFG 1 bindY {tagged 70 vy} = (answerUnder eqFG 1 bindX {tagged 70 vy}).map ρ.applyTerm := by
  obtain ⟨ρ, -, ren, -, there, -⟩ :=
    answer_unique_up_to_renaming two_orientations.1 two_orientations.2 {tagged 70 vy}
  exact ⟨ρ, ren, there⟩

/-- A unifier that is not most general: it binds both variables to `a`. -/
def toA : Subst rows := fun v => if v = (0, 0) ∨ v = (1, 0) then .const 60 else .var v

/-- **Most generality is necessary**: the unifier `toA` is no renaming of `bindX`. -/
theorem instance_is_no_renaming :
    Unifies toA [(eqFG.lhs.at 1, tagged 50 vy)] ∧
      ¬ ∃ ρ : Subst rows, IsRenaming ρ ∧ ∀ v, toA v = ρ.applyTerm (bindX v) := by
  refine ⟨(problem_unifies_iff _).mpr (by simp [toA]), ?_⟩
  rintro ⟨ρ, ren, factor⟩
  have at0 := factor (0, 0)
  obtain ⟨y, hy⟩ := ren (0, 0)
  rw [bindX, Subst.single_ne (σ := rows) _ (by decide), Subst.applyTerm_var, hy] at at0
  simp [toA] at at0

#print axioms renaming_of_mutual
#print axioms mgu_unique_up_to_renaming
#print axioms answerUnder_comp
#print axioms answer_unique_up_to_renaming
#print axioms answer_is_renamed_answer
#print axioms two_orientations
#print axioms orientations_differ
#print axioms orientations_rename
#print axioms instance_is_no_renaming

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramMGURenaming
