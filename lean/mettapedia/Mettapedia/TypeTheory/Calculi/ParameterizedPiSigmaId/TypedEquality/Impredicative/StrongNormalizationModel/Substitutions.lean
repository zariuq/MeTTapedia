import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Validity

/-!
# Valuations

Related valuations extend by a related pair of values with a realizer of the
first. They follow world morphisms on the value side and renamings on the
realizer side: a renamed type relates the renamed values and has their
realizers (`DenS.rename_real`), and a renamed realizer is a realizer. In a
valid context they form a partial equivalence, since the type of each variable
has one pack under related valuations and related values have the same
realizers.

The *daimon valuation* sends every variable to the daimon on both sides and to
a variable on the realizer side. It is a related valuation of every valid
context: the daimon is a valid value of every pack, and a variable realizes
every value.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization (tailSub subst_rename_wk)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

/-! ## Extension and lookup -/

theorem EqSubstS.cons {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {ς : Sub Head n r} (eq : EqSubstS M Γ ξ σ σ' ς) {A : Tm Head n}
    {P : Pack M.value m} (den : DenS M.value ξ (Presentation.subst σ A) P) {a a' : Tm Head m}
    {u : Tm Head r} (h : P.rel a a') (hu : (P.real a).mem u) :
    EqSubstS M (.snoc Γ A) ξ (consSub a σ) (consSub a' σ') (consSub u ς) :=
  ⟨eq, P, den, h, hu⟩

theorem EqSubstS.lookup : ∀ {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {ς : Sub Head n r}, EqSubstS M Γ ξ σ σ' ς → ∀ i : Fin n,
      ∃ P, DenS M.value ξ (Presentation.subst σ (Ctx.lookup Γ i)) P ∧ P.rel (σ i) (σ' i) ∧
        (P.real (σ i)).mem (ς i)
  | _, _, _, .nil, _, _, _, _, _, i => nomatch i
  | _, _, _, .snoc Γ A, _, σ, _, _, eq, i => by
      obtain ⟨tail, P, den, h⟩ := eq
      refine Fin.cases ?_ (fun j => ?_) i
      · refine ⟨P, ?_, h⟩
        simp only [Ctx.lookup, Fin.cases_zero]
        rw [subst_rename_wk]
        exact den
      · obtain ⟨P', den', h'⟩ := EqSubstS.lookup tail j
        refine ⟨P', ?_, h'⟩
        simp only [Ctx.lookup, Fin.cases_succ]
        rw [subst_rename_wk]
        exact den'

/-! ## Morphisms of worlds and renamings of realizers -/

/-- Related valuations follow renamings of their realizers. -/
theorem EqSubstS.renameReal : ∀ {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {ς : Sub Head n r}, EqSubstS M Γ ξ σ σ' ς →
      ∀ {r' : Nat} (ρr : Ren r r'),
        EqSubstS M Γ ξ σ σ' fun i => Presentation.rename ρr (ς i)
  | _, _, _, .nil, _, _, _, _, _, _, _ => trivial
  | _, _, _, .snoc _ _, _, _, _, _, eq, _, ρr => by
      obtain ⟨tail, P, den, h, hu⟩ := eq
      exact ⟨EqSubstS.renameReal tail ρr, P, den, h, (P.real _).rename ρr hu⟩

section Laws

variable (laws : M.Laws)
include laws

/-- **Related valuations follow world morphisms**, with their realizers: a renamed
type relates the renamed values and has the realizers of each valid value at the
renamed value. -/
theorem EqSubstS.rename : ∀ {n m r : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {ς : Sub Head n r}, EqSubstS M Γ ξ σ σ' ς →
      ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k}, Morph ξ ξ' ρ →
        EqSubstS M Γ ξ' (fun i => Presentation.rename ρ (σ i))
          (fun i => Presentation.rename ρ (σ' i)) ς
  | _, _, _, .nil, _, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, .snoc Γ A, _, σ, _, _, eq, _, _, ρ, w => by
      obtain ⟨tail, P, den, h, hu⟩ := eq
      obtain ⟨P', den', renamed, real⟩ := DenS.rename_real laws den w
      refine ⟨EqSubstS.rename tail w, P', ?_, renamed.rel h,
        real (den.refl_left laws.value h) hu⟩
      rw [rename_subst] at den'
      exact den'

/-- Related valuations of a valid context are symmetric; the realizers of the
first values realize the second. -/
theorem EqSubstS.symm : ∀ {n m r : Nat} {Γ : Ctx Head n}, ValidCtxS M Γ →
    ∀ {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
      EqSubstS M Γ ξ σ σ' ς → EqSubstS M Γ ξ σ' σ ς
  | _, _, _, .nil, _, _, _, _, _, _ => trivial
  | _, _, _, .snoc Γ A, valid, _, _, _, _, eq => by
      obtain ⟨validΓ, validA⟩ := valid
      obtain ⟨tail, P, den, h, hu⟩ := eq
      obtain ⟨Q, den₁, den₂, _⟩ := validA tail
      obtain rfl := DenS.deterministic laws.value den den₁
      refine ⟨EqSubstS.symm validΓ tail, P, den₂, den.symm laws.value h, ?_⟩
      rw [← DenS.real_eq_of_rel laws.value den h]
      exact hu

/-- Related valuations of a valid context compose; the realizers of the first
values are kept. -/
theorem EqSubstS.trans : ∀ {n m r r' : Nat} {Γ : Ctx Head n}, ValidCtxS M Γ →
    ∀ {ξ : World M.reading m} {σ σ' σ'' : Sub Head n m} {ς : Sub Head n r}
      {ς' : Sub Head n r'}, EqSubstS M Γ ξ σ σ' ς → EqSubstS M Γ ξ σ' σ'' ς' →
        EqSubstS M Γ ξ σ σ'' ς
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, _, .snoc Γ A, valid, _, _, _, _, _, _, eq, eq' => by
      obtain ⟨validΓ, validA⟩ := valid
      obtain ⟨tail, P, den, h, hu⟩ := eq
      obtain ⟨tail', P', den', h', _⟩ := eq'
      obtain ⟨Q, den₁, den₂, _⟩ := validA tail
      obtain rfl := DenS.deterministic laws.value den den₁
      obtain rfl := DenS.deterministic laws.value den' den₂
      exact ⟨EqSubstS.trans validΓ tail tail', _, den, den.trans laws.value h h', hu⟩

theorem EqSubstS.refl_left {n m r : Nat} {Γ : Ctx Head n} (valid : ValidCtxS M Γ)
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (eq : EqSubstS M Γ ξ σ σ' ς) : EqSubstS M Γ ξ σ σ ς :=
  EqSubstS.trans laws valid eq (EqSubstS.symm laws valid eq)

theorem EqSubstS.refl_right {n m r : Nat} {Γ : Ctx Head n} (valid : ValidCtxS M Γ)
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (eq : EqSubstS M Γ ξ σ σ' ς) : EqSubstS M Γ ξ σ' σ' ς :=
  EqSubstS.trans laws valid (EqSubstS.symm laws valid eq) eq

/-! ## The daimon valuation -/

/-- The daimon valuation, with variables as realizers, is a related valuation of
every valid context. -/
theorem EqSubstS.daimon : ∀ {n m r : Nat} {Γ : Ctx Head n}, ValidCtxS M Γ →
    ∀ (ξ : World M.reading m) (f : Ren n r),
      EqSubstS M Γ ξ (fun _ => .const M.star) (fun _ => .const M.star) fun i => .var (f i)
  | _, _, _, .nil, _, _, _ => trivial
  | _, _, _, .snoc _ _, valid, ξ, f => by
      obtain ⟨validΓ, validA⟩ := valid
      have tail := EqSubstS.daimon validΓ ξ (fun i => f i.succ)
      obtain ⟨P, den, _, _⟩ := validA tail
      exact ⟨tail, P, den, den.star_val laws.value,
        (P.real _).var_mem (RootShape.spineHeaded M.realizers.shape) (f 0)⟩

end Laws

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
