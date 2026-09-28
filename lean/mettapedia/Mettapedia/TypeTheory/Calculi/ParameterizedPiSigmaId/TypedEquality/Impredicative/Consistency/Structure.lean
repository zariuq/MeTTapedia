import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Substitutions

/-!
# Valid parts of type formers

The partial equivalence of a universe compares interpretations only: two
dependent function types whose codomains relate every pair of terms have the
same interpretation whatever their domains. So the validity of a type written
as a type former does not give the validity of its parts, which λ-introduction
and application need.

The parts come from the derivation instead. A rule that needs the parts of a
type former has that type former written in one of its premises, and the
derivation of that premise gives its parts. The fundamental lemma therefore
carries, with each judgment, the validity of the parts of its subjects and
types: `Structured` below, defined by recursion on the syntax.

Validity and valid parts move along renamings and substitutions between
contexts that send related substitutions to related substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Valid parts -/

/-- The parts of a term written as a type former are valid, recursively: the
domain and codomain of a dependent function or pair type, and the carrier and
endpoints of an identity type. Other terms have no parts to check. -/
def Structured (M : Model Head L) : {n : Nat} → Ctx Head n → Tm Head n → Prop
  | _, Γ, .pi A B =>
      (ValidTy M Γ A ∧ Structured M Γ A) ∧
        ValidTy M (.snoc Γ A) B ∧ Structured M (.snoc Γ A) B
  | _, Γ, .sigma A B =>
      (ValidTy M Γ A ∧ Structured M Γ A) ∧
        ValidTy M (.snoc Γ A) B ∧ Structured M (.snoc Γ A) B
  | _, Γ, .id A a b =>
      (ValidTy M Γ A ∧ Structured M Γ A) ∧ ValidTm M Γ a A ∧ ValidTm M Γ b A
  | _, _, .var _ => True
  | _, _, .const _ => True
  | _, _, .head _ => True
  | _, _, .lam _ => True
  | _, _, .app _ _ => True
  | _, _, .pair _ _ => True
  | _, _, .fst _ => True
  | _, _, .snd _ => True
  | _, _, .refl _ => True

/-- A valid context whose entries have valid parts. -/
def ValidCtxS (M : Model Head L) : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => ValidCtxS M Γ ∧ ValidTy M Γ A ∧ Structured M Γ A

theorem ValidCtxS.valid : ∀ {n : Nat} {Γ : Ctx Head n}, ValidCtxS M Γ → ValidCtx M Γ
  | _, .nil, _ => trivial
  | _, .snoc _ _, valid => by
      obtain ⟨valid, validA, _⟩ := valid
      exact ⟨ValidCtxS.valid valid, validA⟩

/-! ## Renamings between contexts -/

/-- A renaming from the variables of `Γ` to those of `Δ` that sends related
substitutions for `Δ` to related substitutions for `Γ`. -/
def ValidRen (M : Model Head L) {n k : Nat} (Δ : Ctx Head k) (ρ : Ren n k) (Γ : Ctx Head n) :
    Prop :=
  ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head k m}, EqSubst M Δ ξ σ σ' →
    EqSubst M Γ ξ (fun i => σ (ρ i)) (fun i => σ' (ρ i))

theorem ValidRen.wk {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) :
    ValidRen M (.snoc Γ A) wk Γ :=
  fun e => e.1

theorem ValidRen.elim0 {k : Nat} (Δ : Ctx Head k) : ValidRen M Δ Fin.elim0 .nil :=
  fun _ => trivial

theorem ValidTy.rename {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    {A : Tm Head n} (valid : ValidTy M Γ A) (ren : ValidRen M Δ ρ Γ) :
    ValidTy M Δ (Presentation.rename ρ A) := by
  intro m ξ σ σ' e
  rw [subst_rename, subst_rename]
  exact valid (ren e)

theorem ValidTm.rename {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    {t A : Tm Head n} (valid : ValidTm M Γ t A) (ren : ValidRen M Δ ρ Γ) :
    ValidTm M Δ (Presentation.rename ρ t) (Presentation.rename ρ A) := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA.rename ren, fun {_ _ _ _} e {R} den => ?_⟩
  rw [subst_rename] at den
  rw [subst_rename, subst_rename]
  exact rel (ren e) den

theorem ValidRen.lift {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    (ren : ValidRen M Δ ρ Γ) (A : Tm Head n) :
    ValidRen M (.snoc Δ (Presentation.rename ρ A)) (liftRen ρ) (.snoc Γ A) := by
  intro m ξ σ σ' e
  obtain ⟨tail, R, den, h⟩ := e
  rw [subst_rename] at den
  exact ⟨ren tail, R, den, h⟩

theorem Structured.rename : ∀ {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    (t : Tm Head n), Structured M Γ t → ValidRen M Δ ρ Γ →
      Structured M Δ (Presentation.rename ρ t)
  | _, _, _, _, _, .pi A B, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.rename ren, Structured.rename A partsA ren⟩,
        validB.rename (ren.lift A), Structured.rename B partsB (ren.lift A)⟩
  | _, _, _, _, _, .sigma A B, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.rename ren, Structured.rename A partsA ren⟩,
        validB.rename (ren.lift A), Structured.rename B partsB (ren.lift A)⟩
  | _, _, _, _, _, .id A _ _, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validL, validR⟩ := parts
      exact ⟨⟨validA.rename ren, Structured.rename A partsA ren⟩, validL.rename ren,
        validR.rename ren⟩
  | _, _, _, _, _, .var _, _, _ => trivial
  | _, _, _, _, _, .const _, _, _ => trivial
  | _, _, _, _, _, .head _, _, _ => trivial
  | _, _, _, _, _, .lam _, _, _ => trivial
  | _, _, _, _, _, .app _ _, _, _ => trivial
  | _, _, _, _, _, .pair _ _, _, _ => trivial
  | _, _, _, _, _, .fst _, _, _ => trivial
  | _, _, _, _, _, .snd _, _, _ => trivial
  | _, _, _, _, _, .refl _, _, _ => trivial

/-! ## Substitutions between contexts -/

/-- A substitution from the variables of `Γ` to terms over `Δ` that sends
related substitutions for `Δ` to related substitutions for `Γ`. -/
def ValidMor (M : Model Head L) {n k : Nat} (Δ : Ctx Head k) (τ : Sub Head n k)
    (Γ : Ctx Head n) : Prop :=
  ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head k m}, EqSubst M Δ ξ σ σ' →
    EqSubst M Γ ξ (fun i => Presentation.subst σ (τ i)) (fun i => Presentation.subst σ' (τ i))

theorem ValidTy.subst {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k}
    {τ : Sub Head n k} {A : Tm Head n} (valid : ValidTy M Γ A)
    (mor : ValidMor M Δ τ Γ) : ValidTy M Δ (Presentation.subst τ A) := by
  intro m ξ σ σ' e
  rw [subst_comp, subst_comp]
  exact valid (mor e)

theorem ValidTm.subst {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k}
    {τ : Sub Head n k} {t A : Tm Head n} (valid : ValidTm M Γ t A)
    (mor : ValidMor M Δ τ Γ) :
    ValidTm M Δ (Presentation.subst τ t) (Presentation.subst τ A) := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA.subst mor, fun {_ _ _ _} e {R} den => ?_⟩
  rw [subst_comp] at den
  rw [subst_comp, subst_comp]
  exact rel (mor e) den

/-- Substituting after the tail of a substitution for an extended context. -/
theorem tailSub_subst_liftSub {n k m : Nat} (σ : Sub Head (k + 1) m)
    (τ : Sub Head n k) :
    (tailSub fun i => Presentation.subst σ (liftSub τ i)) =
      fun i => Presentation.subst (tailSub σ) (τ i) :=
  funext fun i => subst_rename_wk σ (τ i)

theorem ValidMor.lift {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k}
    {τ : Sub Head n k} (mor : ValidMor M Δ τ Γ) (A : Tm Head n) :
    ValidMor M (.snoc Δ (Presentation.subst τ A)) (liftSub τ) (.snoc Γ A) := by
  intro m ξ σ σ' e
  obtain ⟨tail, R, den, h⟩ := e
  rw [subst_comp] at den
  refine ⟨?_, R, ?_, h⟩
  · rw [tailSub_subst_liftSub, tailSub_subst_liftSub]
    exact mor tail
  · rw [tailSub_subst_liftSub]
    exact den

theorem Structured.subst : ∀ {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k}
    {τ : Sub Head n k} (t : Tm Head n), Structured M Γ t → ValidMor M Δ τ Γ →
      (∀ i, Structured M Δ (τ i)) → Structured M Δ (Presentation.subst τ t)
  | _, _, _, _, _, .var i, _, _, images => images i
  | _, _, _, Δ, τ, .pi A B, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.subst mor, Structured.subst A partsA mor images⟩,
        validB.subst (mor.lift A),
        Structured.subst B partsB (mor.lift A) (Fin.cases trivial fun j =>
          Structured.rename (τ j) (images j) (ValidRen.wk Δ (Presentation.subst τ A)))⟩
  | _, _, _, Δ, τ, .sigma A B, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.subst mor, Structured.subst A partsA mor images⟩,
        validB.subst (mor.lift A),
        Structured.subst B partsB (mor.lift A) (Fin.cases trivial fun j =>
          Structured.rename (τ j) (images j) (ValidRen.wk Δ (Presentation.subst τ A)))⟩
  | _, _, _, _, _, .id A _ _, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validL, validR⟩ := parts
      exact ⟨⟨validA.subst mor, Structured.subst A partsA mor images⟩, validL.subst mor,
        validR.subst mor⟩
  | _, _, _, _, _, .const _, _, _, _ => trivial
  | _, _, _, _, _, .head _, _, _, _ => trivial
  | _, _, _, _, _, .lam _, _, _, _ => trivial
  | _, _, _, _, _, .app _ _, _, _, _ => trivial
  | _, _, _, _, _, .pair _ _, _, _, _ => trivial
  | _, _, _, _, _, .fst _, _, _, _ => trivial
  | _, _, _, _, _, .snd _, _, _, _ => trivial
  | _, _, _, _, _, .refl _, _, _, _ => trivial

/-! ## Instantiation -/

/-- Instantiating the last variable of a context by a valid term. -/
theorem ValidMor.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTm M Γ a A) : ValidMor M Γ (subst0 a) (.snoc Γ A) := by
  intro m ξ σ σ' e
  obtain ⟨validA, rel⟩ := valid
  obtain ⟨R, den, _⟩ := validA e
  exact ⟨e, R, den, rel e den⟩

theorem ValidTy.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} {B : Tm Head (n + 1)}
    (validB : ValidTy M (.snoc Γ A) B) (valid : ValidTm M Γ a A) :
    ValidTy M Γ (Presentation.inst0 a B) :=
  validB.subst (ValidMor.inst0 valid)

theorem ValidTm.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    {t B : Tm Head (n + 1)} (validT : ValidTm M (.snoc Γ A) t B) (valid : ValidTm M Γ a A) :
    ValidTm M Γ (Presentation.inst0 a t) (Presentation.inst0 a B) :=
  validT.subst (ValidMor.inst0 valid)

theorem Structured.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    {B : Tm Head (n + 1)} (parts : Structured M (.snoc Γ A) B) (valid : ValidTm M Γ a A)
    (partsA : Structured M Γ a) : Structured M Γ (Presentation.inst0 a B) :=
  Structured.subst B parts (ValidMor.inst0 valid) (Fin.cases partsA fun _ => trivial)

/-! ## Variables -/

theorem ValidCtxS.lookup : ∀ {n : Nat} {Γ : Ctx Head n}, ValidCtxS M Γ → ∀ i : Fin n,
    ValidTy M Γ (Ctx.lookup Γ i) ∧ Structured M Γ (Ctx.lookup Γ i)
  | _, .nil, _, i => nomatch i
  | _, .snoc Γ A, valid, i => by
      obtain ⟨valid, validA, partsA⟩ := valid
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨validA.rename (ValidRen.wk Γ A), Structured.rename A partsA (ValidRen.wk Γ A)⟩
      · obtain ⟨validJ, partsJ⟩ := ValidCtxS.lookup valid j
        exact ⟨validJ.rename (ValidRen.wk Γ A),
          Structured.rename (Ctx.lookup Γ j) partsJ (ValidRen.wk Γ A)⟩

theorem ValidTm.var (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} (valid : ValidCtxS M Γ)
    (i : Fin n) : ValidTm M Γ (.var i) (Ctx.lookup Γ i) := by
  obtain ⟨validI, _⟩ := valid.lookup i
  refine ⟨validI, fun {_ _ _ _} e {R} den => ?_⟩
  obtain ⟨R', den', h⟩ := EqSubst.lookup e i
  rw [Den.deterministic laws den den']
  exact h

/-- A closed valid type is valid in every context. -/
theorem ValidTy.liftClosed {k : Nat} {A : Tm Head 0} (valid : ValidTy M .nil A)
    (Δ : Ctx Head k) : ValidTy M Δ (Presentation.liftClosed A) :=
  valid.rename (ValidRen.elim0 Δ)

theorem Structured.liftClosed {k : Nat} {A : Tm Head 0} (parts : Structured M .nil A)
    (Δ : Ctx Head k) : Structured M Δ (Presentation.liftClosed A) :=
  Structured.rename A parts (ValidRen.elim0 Δ)

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
