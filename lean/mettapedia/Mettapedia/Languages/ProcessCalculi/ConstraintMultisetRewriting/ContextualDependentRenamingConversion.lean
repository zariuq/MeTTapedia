import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRenamingReduction

/-!
# Executable conversion commutes with context embeddings

An **embedding** of contexts is an injective renaming `ρ` with `Δ (ρ i) = ρ (Γ i)` at every
variable. Along an embedding, executable conversion behaves the same on renamed inputs, at every
budget, provided the reduction strategy commutes with renaming:

* type-directed comparison, neutral comparison and type comparison succeed on the renamed inputs
  exactly when they succeed on the originals;
* neutral comparison synthesizes the renamed type.

Injectivity is needed: neutral comparison decides variable equality, and a renaming that
identifies two variables makes distinct neutral terms equal.
-/

set_option autoImplicit false

universe u v w

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRenaming

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion

/-! ## Success of sequenced computations -/

section Sequencing

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type}

theorem isSome_bind₁ (x : Option α) (f : α → β) : (x.bind fun a => pure (f a)).isSome = x.isSome := by
  cases x <;> rfl

theorem isSome_bind₂ (x : Option α) (y : Option β) (f : α → β → γ) :
    (x.bind fun a => y.bind fun b => pure (f a b)).isSome = (x.isSome && y.isSome) := by
  cases x <;> cases y <;> rfl

theorem isSome_bind₃ (x : Option α) (y : Option β) (z : Option γ) (f : α → β → γ → δ) :
    (x.bind fun a => y.bind fun b => z.bind fun c => pure (f a b c)).isSome =
      (x.isSome && y.isSome && z.isSome) := by
  cases x <;> cases y <;> cases z <;> rfl

end Sequencing

/-! ## Embeddings -/

variable {Head : Type}

/-- **An embedding of contexts**: an injective renaming compatible with every declared type. -/
structure Embedding {n m : Nat} (Γ : Ctx Head n) (Δ : Ctx Head m) (ρ : Ren n m) : Prop where
  injective : Function.Injective ρ
  lookup : CtxRen Γ Δ ρ

theorem Embedding.snoc {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (embedding : Embedding Γ Δ ρ)
    (type : Tm Head n) : Embedding (.snoc Γ type) (.snoc Δ (rename ρ type)) (liftRen ρ) :=
  ⟨liftRen_injective embedding.injective, embedding.lookup.snoc type⟩

/-- The identity embeds every context into itself. -/
theorem Embedding.refl {n : Nat} (Γ : Ctx Head n) : Embedding Γ Γ idRen :=
  ⟨fun _ _ same => same, fun _ => (rename_id _).symm⟩

theorem rename_lift_wk {n m : Nat} (ρ : Ren n m) (term : Tm Head n) :
    rename (liftRen ρ) (rename wk term) = rename wk (rename ρ term) := by
  rw [rename_comp, rename_comp]
  exact rename_ext (fun _ => rfl) term

/-- The η-expanded comparison of a function under a binder, renamed. -/
theorem rename_eta {n m : Nat} (ρ : Ren n m) (term : Tm Head n) :
    rename (liftRen ρ) (.app (rename wk term) (.var 0)) = .app (rename wk (rename ρ term)) (.var 0) := by
  change Tm.app (rename (liftRen ρ) (rename wk term)) (.var (liftRen ρ 0)) = _
  rw [rename_lift_wk]
  rfl

theorem rename_inst0_fst {n m : Nat} (ρ : Ren n m) (term : Tm Head n) (body : Tm Head (n + 1)) :
    rename ρ (inst0 (.fst term) body) = inst0 (.fst (rename ρ term)) (rename (liftRen ρ) body) :=
  rename_inst0 ρ (.fst term) body

/-! ## Conversion along an embedding -/

variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq] [∀ head, Decidable (R.isUniverse head)]

/-- **Conversion commutes with embeddings at one budget**: the four executables succeed on renamed
inputs exactly when they succeed on the originals, and neutral comparison synthesizes the renamed
type. -/
def ConversionCommutes (reducer : Reducer R) (fuel : Nat) : Prop :=
  (∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}, Embedding Γ Δ ρ →
    ∀ left right type : Tm Head n,
      (compare R reducer fuel Δ (rename ρ left) (rename ρ right) (rename ρ type)).isSome =
        (compare R reducer fuel Γ left right type).isSome) ∧
  (∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}, Embedding Γ Δ ρ →
    ∀ left right type : Tm Head n,
      (compareNeutral R reducer fuel Δ (rename ρ left) (rename ρ right) (rename ρ type)).isSome =
        (compareNeutral R reducer fuel Γ left right type).isSome) ∧
  (∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}, Embedding Γ Δ ρ →
    ∀ left right : Tm Head n,
      Corr Sigma.fst (fun result => rename ρ result.1)
        (neutral R reducer fuel Δ (rename ρ left) (rename ρ right)) (neutral R reducer fuel Γ left right)) ∧
  (∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}, Embedding Γ Δ ρ →
    ∀ left right : Tm Head n,
      (types R reducer fuel Δ (rename ρ left) (rename ρ right)).isSome =
        (types R reducer fuel Γ left right).isSome)

variable {R} {reducer : Reducer R}

section Step

variable (renames : Renames reducer) {fuel : Nat} (ih : ConversionCommutes R reducer fuel)
include renames ih

theorem compare_step {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (e : Embedding Γ Δ ρ)
    (left right type : Tm Head n) :
    (compare R reducer (fuel + 1) Δ (rename ρ left) (rename ρ right) (rename ρ type)).isSome =
      (compare R reducer (fuel + 1) Γ left right type).isSome := by
  obtain ⟨ihC, ihN, -, ihT⟩ := ih
  rw [ExecutableConversion.compare, ExecutableConversion.compare]
  rcases renames.cases (fuel + 1) ρ type with ⟨h₁, h₂⟩ | ⟨value, p, p', h₁, h₂⟩
  · rw [h₁, h₂]; rfl
  · rw [h₁, h₂]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases value with
    | pi domain body =>
        dsimp only [rename]
        rw [isSome_bind₁, isSome_bind₁, ← rename_eta, ← rename_eta]
        exact ihC (e.snoc domain) _ _ body
    | sigma domain body =>
        dsimp only [rename]
        rw [isSome_bind₂, isSome_bind₂, ← rename_inst0_fst]
        exact congrArg₂ (· && ·) (ihC e (.fst left) (.fst right) domain) (ihC e (.snd left) (.snd right) _)
    | head value =>
        dsimp only [rename]
        by_cases universe' : R.isUniverse value
        · rw [dif_pos universe', dif_pos universe', isSome_bind₁, isSome_bind₁]
          exact ihT e left right
        · rw [dif_neg universe', dif_neg universe']
          exact ihN e left right type
    | id carrier a b =>
        dsimp only [rename]
        rcases renames.cases (fuel + 1) ρ left with ⟨k₁, k₂⟩ | ⟨lv, lp, lp', k₁, k₂⟩
        · rw [k₁, k₂]; rfl
        · rw [k₁, k₂]
          simp only [Option.bind_some]
          rcases renames.cases (fuel + 1) ρ right with ⟨l₁, l₂⟩ | ⟨rv, rp, rp', l₁, l₂⟩
          · rw [l₁, l₂]; rfl
          · rw [l₁, l₂]
            simp only [Option.bind_some]
            have neutralSame := ihN e left right type
            by_cases reflexive : (∃ s, lv = .refl s) ∧ ∃ s', rv = .refl s'
            · obtain ⟨⟨s, rfl⟩, ⟨s', rfl⟩⟩ := reflexive
              dsimp only [rename]
              rw [isSome_bind₁, isSome_bind₁]
              exact ihC e _ _ carrier
            · cases lv <;> cases rv
              all_goals first
                | exact absurd ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩ reflexive
                | (dsimp only [rename]; exact neutralSame)
    | _ => exact ihN e left right type

theorem compareNeutral_step {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (e : Embedding Γ Δ ρ)
    (left right type : Tm Head n) :
    (compareNeutral R reducer (fuel + 1) Δ (rename ρ left) (rename ρ right) (rename ρ type)).isSome =
      (compareNeutral R reducer (fuel + 1) Γ left right type).isSome := by
  obtain ⟨-, -, ihNe, -⟩ := ih
  rw [ExecutableConversion.compareNeutral, ExecutableConversion.compareNeutral]
  rcases renames.cases (fuel + 1) ρ left with ⟨h₁, h₂⟩ | ⟨lv, lp, lp', h₁, h₂⟩
  · rw [h₁, h₂]; rfl
  · rw [h₁, h₂]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rcases renames.cases (fuel + 1) ρ right with ⟨k₁, k₂⟩ | ⟨rv, rp, rp', k₁, k₂⟩
    · rw [k₁, k₂]; rfl
    · rw [k₁, k₂]
      simp only [Option.bind_some]
      rw [isSome_bind₁, isSome_bind₁]
      exact (ihNe e lv rv).isSome

omit renames ih in
/-- Away from the five matching pairs of spines, neutral comparison returns nothing. -/
private theorem neutral_other {n : Nat} {Γ : Ctx Head n} {left right : Tm Head n}
    (notVar : ∀ i j, left = .var i → right = .var j → False)
    (notConst : ∀ c d, left = .const c → right = .const d → False)
    (notApp : ∀ f a f' a', left = .app f a → right = .app f' a' → False)
    (notFst : ∀ p p', left = .fst p → right = .fst p' → False)
    (notSnd : ∀ p p', left = .snd p → right = .snd p' → False) :
    neutral R reducer (fuel + 1) Γ left right = none :=
  neutral.eq_7 R reducer _ Γ left right fuel notVar notConst notApp notFst notSnd

theorem neutral_step {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (e : Embedding Γ Δ ρ)
    (left right : Tm Head n) :
    Corr Sigma.fst (fun result => rename ρ result.1)
      (neutral R reducer (fuel + 1) Δ (rename ρ left) (rename ρ right)) (neutral R reducer (fuel + 1) Γ left right) := by
  obtain ⟨ihC, -, ihNe, -⟩ := ih
  by_cases matching : (∃ i j, left = .var i ∧ right = .var j) ∨ (∃ c d, left = .const c ∧ right = .const d) ∨
      (∃ f a f' a', left = .app f a ∧ right = .app f' a') ∨ (∃ p p', left = .fst p ∧ right = .fst p') ∨
      (∃ p p', left = .snd p ∧ right = .snd p')
  · rcases matching with ⟨i, j, rfl, rfl⟩ | ⟨c, d, rfl, rfl⟩ | ⟨f, a, f', a', rfl, rfl⟩ | ⟨p, p', rfl, rfl⟩ |
      ⟨p, p', rfl, rfl⟩
    · dsimp only [rename]
      rw [neutral, neutral]
      by_cases same : i = j
      · subst same
        rw [dif_pos rfl, dif_pos rfl]
        exact Corr.some_some (e.lookup i)
      · have different : ρ i ≠ ρ j := fun equal => same (e.injective equal)
        rw [dif_neg same, dif_neg different]
        rfl
    · dsimp only [rename]
      rw [neutral, neutral]
      by_cases same : c = d
      · subst same
        rw [dif_pos rfl, dif_pos rfl]
        split
        · exact Corr.some_some (rename_liftClosed ρ _).symm
        · rfl
      · rw [dif_neg same, dif_neg same]
        rfl
    · dsimp only [rename]
      rw [neutral, neutral]
      simp only [Option.bind_eq_bind]
      rcases (ihNe e f f').cases with ⟨h₁, h₂⟩ | ⟨⟨T, c⟩, ⟨T', c'⟩, h₁, h₂, same⟩
      · rw [h₁, h₂]; rfl
      · dsimp only at same
        subst same
        rw [h₁, h₂]
        simp only [Option.bind_some]
        rcases renames.cases (fuel + 1) ρ T' with ⟨k₁, k₂⟩ | ⟨value, q, q', k₁, k₂⟩
        · rw [k₁, k₂]; rfl
        · rw [k₁, k₂]
          simp only [Option.bind_some]
          cases value
          all_goals dsimp only [rename]
          case pi domain body =>
            rcases isSome_cases (ihC e a a' domain) with ⟨l₁, l₂⟩ | ⟨x, y, l₁, l₂⟩
            · rw [l₁, l₂]; rfl
            · rw [l₁, l₂]
              exact Corr.some_some (rename_inst0 ρ a body).symm
          all_goals rfl
    · dsimp only [rename]
      rw [neutral, neutral]
      simp only [Option.bind_eq_bind]
      rcases (ihNe e p p').cases with ⟨h₁, h₂⟩ | ⟨⟨T, c⟩, ⟨T', c'⟩, h₁, h₂, same⟩
      · rw [h₁, h₂]; rfl
      · dsimp only at same
        subst same
        rw [h₁, h₂]
        simp only [Option.bind_some]
        rcases renames.cases (fuel + 1) ρ T' with ⟨k₁, k₂⟩ | ⟨value, q, q', k₁, k₂⟩
        · rw [k₁, k₂]; rfl
        · rw [k₁, k₂]
          simp only [Option.bind_some]
          cases value
          all_goals dsimp only [rename]
          all_goals rfl
    · dsimp only [rename]
      rw [neutral, neutral]
      simp only [Option.bind_eq_bind]
      rcases (ihNe e p p').cases with ⟨h₁, h₂⟩ | ⟨⟨T, c⟩, ⟨T', c'⟩, h₁, h₂, same⟩
      · rw [h₁, h₂]; rfl
      · dsimp only at same
        subst same
        rw [h₁, h₂]
        simp only [Option.bind_some]
        rcases renames.cases (fuel + 1) ρ T' with ⟨k₁, k₂⟩ | ⟨value, q, q', k₁, k₂⟩
        · rw [k₁, k₂]; rfl
        · rw [k₁, k₂]
          simp only [Option.bind_some]
          cases value
          all_goals dsimp only [rename]
          case sigma domain body =>
            exact Corr.some_some (rename_inst0_fst ρ p body).symm
          all_goals rfl
  · have original := neutral_other (R := R) (reducer := reducer) (fuel := fuel) (Γ := Γ)
      (fun i j h₁ h₂ => matching (.inl ⟨i, j, h₁, h₂⟩))
      (fun c d h₁ h₂ => matching (.inr (.inl ⟨c, d, h₁, h₂⟩)))
      (fun f a f' a' h₁ h₂ => matching (.inr (.inr (.inl ⟨f, a, f', a', h₁, h₂⟩))))
      (fun p p' h₁ h₂ => matching (.inr (.inr (.inr (.inl ⟨p, p', h₁, h₂⟩)))))
      (fun p p' h₁ h₂ => matching (.inr (.inr (.inr (.inr ⟨p, p', h₁, h₂⟩)))))
    have renamed := neutral_other (R := R) (reducer := reducer) (fuel := fuel) (Γ := Δ)
      (left := rename ρ left) (right := rename ρ right)
      (fun i j h₁ h₂ => by
        cases left <;> cases right <;> simp only [rename, reduceCtorEq] at h₁ h₂
        exact matching (.inl ⟨_, _, rfl, rfl⟩))
      (fun c d h₁ h₂ => by
        cases left <;> cases right <;> simp only [rename, reduceCtorEq] at h₁ h₂
        exact matching (.inr (.inl ⟨_, _, rfl, rfl⟩)))
      (fun f a f' a' h₁ h₂ => by
        cases left <;> cases right <;> simp only [rename, reduceCtorEq] at h₁ h₂
        exact matching (.inr (.inr (.inl ⟨_, _, _, _, rfl, rfl⟩))))
      (fun p p' h₁ h₂ => by
        cases left <;> cases right <;> simp only [rename, reduceCtorEq] at h₁ h₂
        exact matching (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))))
      (fun p p' h₁ h₂ => by
        cases left <;> cases right <;> simp only [rename, reduceCtorEq] at h₁ h₂
        exact matching (.inr (.inr (.inr (.inr ⟨_, _, rfl, rfl⟩)))))
    rw [original, renamed]
    rfl

theorem types_step {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} (e : Embedding Γ Δ ρ)
    (left right : Tm Head n) :
    (types R reducer (fuel + 1) Δ (rename ρ left) (rename ρ right)).isSome =
      (types R reducer (fuel + 1) Γ left right).isSome := by
  obtain ⟨ihC, -, ihNe, ihT⟩ := ih
  rw [ExecutableConversion.types, ExecutableConversion.types]
  rcases renames.cases (fuel + 1) ρ left with ⟨h₁, h₂⟩ | ⟨lv, lp, lp', h₁, h₂⟩
  · rw [h₁, h₂]; rfl
  · rw [h₁, h₂]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rcases renames.cases (fuel + 1) ρ right with ⟨k₁, k₂⟩ | ⟨rv, rp, rp', k₁, k₂⟩
    · rw [k₁, k₂]; rfl
    · rw [k₁, k₂]
      simp only [Option.bind_some]
      have neutralSame := (ihNe e lv rv).isSome
      by_cases former : (∃ a b, lv = .head a ∧ rv = .head b) ∨
          (∃ d c d' c', lv = .pi d c ∧ rv = .pi d' c') ∨ (∃ d c d' c', lv = .sigma d c ∧ rv = .sigma d' c') ∨
          (∃ A a b A' a' b', lv = .id A a b ∧ rv = .id A' a' b')
      · rcases former with ⟨a, b, rfl, rfl⟩ | ⟨d, c, d', c', rfl, rfl⟩ | ⟨d, c, d', c', rfl, rfl⟩ |
          ⟨A, a, b, A', a', b', rfl, rfl⟩
        · dsimp only [rename]
          split_ifs <;> rfl
        · dsimp only [rename]
          rw [isSome_bind₂, isSome_bind₂, ihT e, ihT (e.snoc _)]
        · dsimp only [rename]
          rw [isSome_bind₂, isSome_bind₂, ihT e, ihT (e.snoc _)]
        · dsimp only [rename]
          rw [isSome_bind₃, isSome_bind₃, ihT e, ihC e, ihC e]
      · cases lv <;> cases rv
        all_goals first
          | exact absurd (.inl ⟨_, _, rfl, rfl⟩) former
          | exact absurd (.inr (.inl ⟨_, _, _, _, rfl, rfl⟩)) former
          | exact absurd (.inr (.inr (.inl ⟨_, _, _, _, rfl, rfl⟩))) former
          | exact absurd (.inr (.inr (.inr ⟨_, _, _, _, _, _, rfl, rfl⟩))) former
          | (dsimp only [rename] at neutralSame ⊢; rw [isSome_bind₁, isSome_bind₁]; exact neutralSame)

end Step

/-- **Executable conversion commutes with embeddings** at every budget, for a strategy that
commutes with renaming. -/
theorem conversion_commutes (renames : Renames reducer) : ∀ fuel, ConversionCommutes R reducer fuel := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ => ?_, fun _ _ _ => ?_⟩
      · (rw [ExecutableConversion.compare, ExecutableConversion.compare]; rfl)
      · (rw [ExecutableConversion.compareNeutral, ExecutableConversion.compareNeutral]; rfl)
      · (rw [Corr, neutral, neutral]; rfl)
      · (rw [ExecutableConversion.types, ExecutableConversion.types]; rfl)
  | succ fuel ih =>
      exact ⟨compare_step renames ih, compareNeutral_step renames ih, neutral_step renames ih, types_step renames ih⟩

end ContextualDependentRenaming
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
