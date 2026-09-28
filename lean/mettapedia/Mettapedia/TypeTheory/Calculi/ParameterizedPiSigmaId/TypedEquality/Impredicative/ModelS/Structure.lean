import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Substitutions

/-!
# Valid parts, renamings and substitutions

A term written as a type former carries the validity of its parts: the domain
and codomain of a dependent function or pair type, the carrier and endpoints
of an identity type. A valid context whose entries carry their valid parts is
*structured*.

A renaming or a substitution between contexts is valid when it sends related
valuations of the target to related valuations of the source; it then keeps
validity. Instantiating the last variable of a context by a valid term is
valid.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization (tailSub subst_rename_wk)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SModel Head L}

/-! ## Valid parts -/

variable (M) in
/-- The parts of a term written as a type former are valid, recursively. Other
terms have no parts to check. -/
def StructuredS : {n : Nat} → Ctx Head n → Tm Head n → Prop
  | _, Γ, .pi A B =>
      (ValidTyS M Γ A ∧ StructuredS Γ A) ∧
        ValidTyS M (.snoc Γ A) B ∧ StructuredS (.snoc Γ A) B
  | _, Γ, .sigma A B =>
      (ValidTyS M Γ A ∧ StructuredS Γ A) ∧
        ValidTyS M (.snoc Γ A) B ∧ StructuredS (.snoc Γ A) B
  | _, Γ, .id A a b =>
      (ValidTyS M Γ A ∧ StructuredS Γ A) ∧ ValidTmS M Γ a A ∧ ValidTmS M Γ b A
  | _, _, .var _ => True
  | _, _, .const _ => True
  | _, _, .head _ => True
  | _, _, .lam _ => True
  | _, _, .app _ _ => True
  | _, _, .pair _ _ => True
  | _, _, .fst _ => True
  | _, _, .snd _ => True
  | _, _, .refl _ => True

variable (M) in
/-- A valid context whose entries have valid parts. -/
def ValidCtxSS : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => ValidCtxSS Γ ∧ ValidTyS M Γ A ∧ StructuredS M Γ A

theorem ValidCtxSS.valid : ∀ {n : Nat} {Γ : Ctx Head n}, ValidCtxSS M Γ → ValidCtxS M Γ
  | _, .nil, _ => trivial
  | _, .snoc _ _, valid => by
      obtain ⟨valid, validA, _⟩ := valid
      exact ⟨ValidCtxSS.valid valid, validA⟩

/-! ## Renamings between contexts -/

variable (M) in
/-- A renaming from the variables of `Γ` to those of `Δ` that sends related
valuations of `Δ` to related valuations of `Γ`. -/
def ValidRenS {n k : Nat} (Δ : Ctx Head k) (ρ : Ren n k) (Γ : Ctx Head n) : Prop :=
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head k m} {ς : Sub Head k r},
    EqSubstS M Δ ξ σ σ' ς →
      EqSubstS M Γ ξ (fun i => σ (ρ i)) (fun i => σ' (ρ i)) fun i => ς (ρ i)

theorem ValidRenS.wk {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) :
    ValidRenS M (.snoc Γ A) wk Γ :=
  fun e => e.1

theorem ValidRenS.elim0 {k : Nat} (Δ : Ctx Head k) : ValidRenS M Δ Fin.elim0 .nil :=
  fun _ => trivial

theorem ValidTyS.rename {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    {A : Tm Head n} (valid : ValidTyS M Γ A) (ren : ValidRenS M Δ ρ Γ) :
    ValidTyS M Δ (Presentation.rename ρ A) := fun e => by
  rw [subst_rename, subst_rename, subst_rename]
  exact valid (ren e)

theorem ValidTmS.rename {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    {t A : Tm Head n} (valid : ValidTmS M Γ t A) (ren : ValidRenS M Δ ρ Γ) :
    ValidTmS M Δ (Presentation.rename ρ t) (Presentation.rename ρ A) := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA.rename ren, fun {_ _ _ _ _ _} e {P} den => ?_⟩
  rw [subst_rename] at den
  rw [subst_rename, subst_rename, subst_rename]
  exact rel (ren e) den

theorem ValidRenS.lift {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    (ren : ValidRenS M Δ ρ Γ) (A : Tm Head n) :
    ValidRenS M (.snoc Δ (Presentation.rename ρ A)) (liftRen ρ) (.snoc Γ A) := by
  intro _ _ _ _ _ _ e
  obtain ⟨tail, P, den, h⟩ := e
  rw [subst_rename] at den
  exact ⟨ren tail, P, den, h⟩

theorem StructuredS.rename : ∀ {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    (t : Tm Head n), StructuredS M Γ t → ValidRenS M Δ ρ Γ →
      StructuredS M Δ (Presentation.rename ρ t)
  | _, _, _, _, _, .pi A B, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.rename ren, StructuredS.rename A partsA ren⟩,
        validB.rename (ren.lift A), StructuredS.rename B partsB (ren.lift A)⟩
  | _, _, _, _, _, .sigma A B, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.rename ren, StructuredS.rename A partsA ren⟩,
        validB.rename (ren.lift A), StructuredS.rename B partsB (ren.lift A)⟩
  | _, _, _, _, _, .id A _ _, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validL, validR⟩ := parts
      exact ⟨⟨validA.rename ren, StructuredS.rename A partsA ren⟩, validL.rename ren,
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

variable (M) in
/-- A substitution from the variables of `Γ` to terms over `Δ` that sends
related valuations of `Δ` to related valuations of `Γ`. -/
def ValidMorS {n k : Nat} (Δ : Ctx Head k) (τ : Sub Head n k) (Γ : Ctx Head n) : Prop :=
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head k m} {ς : Sub Head k r},
    EqSubstS M Δ ξ σ σ' ς →
      EqSubstS M Γ ξ (fun i => Presentation.subst σ (τ i))
        (fun i => Presentation.subst σ' (τ i))
        fun i => Presentation.subst ς (τ i)

theorem ValidTyS.subst {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {τ : Sub Head n k}
    {A : Tm Head n} (valid : ValidTyS M Γ A) (mor : ValidMorS M Δ τ Γ) :
    ValidTyS M Δ (Presentation.subst τ A) := fun e => by
  rw [subst_comp, subst_comp, subst_comp]
  exact valid (mor e)

theorem ValidTmS.subst {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {τ : Sub Head n k}
    {t A : Tm Head n} (valid : ValidTmS M Γ t A) (mor : ValidMorS M Δ τ Γ) :
    ValidTmS M Δ (Presentation.subst τ t) (Presentation.subst τ A) := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA.subst mor, fun {_ _ _ _ _ _} e {P} den => ?_⟩
  rw [subst_comp] at den
  rw [subst_comp, subst_comp, subst_comp]
  exact rel (mor e) den

/-- Substituting after the tail of a substitution for an extended context. -/
theorem tailSub_subst_liftSub {n k m : Nat} (σ : Sub Head (k + 1) m) (τ : Sub Head n k) :
    (tailSub fun i => Presentation.subst σ (liftSub τ i)) =
      fun i => Presentation.subst (tailSub σ) (τ i) :=
  funext fun i => subst_rename_wk σ (τ i)

theorem ValidMorS.lift {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {τ : Sub Head n k}
    (mor : ValidMorS M Δ τ Γ) (A : Tm Head n) :
    ValidMorS M (.snoc Δ (Presentation.subst τ A)) (liftSub τ) (.snoc Γ A) := by
  intro _ _ _ σ σ' ς e
  obtain ⟨tail, P, den, h⟩ := e
  rw [subst_comp] at den
  refine ⟨?_, P, ?_, h⟩
  · rw [tailSub_subst_liftSub, tailSub_subst_liftSub, tailSub_subst_liftSub]
    exact mor tail
  · rw [tailSub_subst_liftSub]
    exact den

theorem StructuredS.subst : ∀ {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k}
    {τ : Sub Head n k} (t : Tm Head n), StructuredS M Γ t → ValidMorS M Δ τ Γ →
      (∀ i, StructuredS M Δ (τ i)) → StructuredS M Δ (Presentation.subst τ t)
  | _, _, _, _, _, .var i, _, _, images => images i
  | _, _, _, Δ, τ, .pi A B, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.subst mor, StructuredS.subst A partsA mor images⟩,
        validB.subst (mor.lift A),
        StructuredS.subst B partsB (mor.lift A) (Fin.cases trivial fun j =>
          StructuredS.rename (τ j) (images j) (ValidRenS.wk Δ (Presentation.subst τ A)))⟩
  | _, _, _, Δ, τ, .sigma A B, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.subst mor, StructuredS.subst A partsA mor images⟩,
        validB.subst (mor.lift A),
        StructuredS.subst B partsB (mor.lift A) (Fin.cases trivial fun j =>
          StructuredS.rename (τ j) (images j) (ValidRenS.wk Δ (Presentation.subst τ A)))⟩
  | _, _, _, _, _, .id A _ _, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validL, validR⟩ := parts
      exact ⟨⟨validA.subst mor, StructuredS.subst A partsA mor images⟩, validL.subst mor,
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

/-- A valid term at a valid type has valid values under related valuations. -/
theorem ValidTmS.val (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (ctx : ValidCtxS M Γ) (valid : ValidTmS M Γ t A) {m r : Nat} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {ς : Sub Head n r} (e : EqSubstS M Γ ξ σ σ' ς)
    {P : Pack M.value m} (den : DenS M.value ξ (Presentation.subst σ A) P) :
    P.Val (Presentation.subst σ t) :=
  (valid.2 (e.refl_left laws ctx) den).1

/-- Instantiating the last variable of a context by a valid term. -/
theorem ValidMorS.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTmS M Γ a A) : ValidMorS M Γ (subst0 a) (.snoc Γ A) := by
  intro _ _ _ σ σ' ς e
  obtain ⟨P, den, -, -⟩ := valid.1 e
  obtain ⟨rel, real⟩ := valid.2 e den
  exact ⟨e, P, den, rel, real⟩

theorem ValidTyS.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} {B : Tm Head (n + 1)}
    (validB : ValidTyS M (.snoc Γ A) B) (valid : ValidTmS M Γ a A) :
    ValidTyS M Γ (Presentation.inst0 a B) :=
  validB.subst (ValidMorS.inst0 valid)

theorem ValidTmS.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    {t B : Tm Head (n + 1)} (validT : ValidTmS M (.snoc Γ A) t B)
    (valid : ValidTmS M Γ a A) :
    ValidTmS M Γ (Presentation.inst0 a t) (Presentation.inst0 a B) :=
  validT.subst (ValidMorS.inst0 valid)

theorem StructuredS.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    {B : Tm Head (n + 1)} (parts : StructuredS M (.snoc Γ A) B)
    (valid : ValidTmS M Γ a A) (partsA : StructuredS M Γ a) :
    StructuredS M Γ (Presentation.inst0 a B) :=
  StructuredS.subst B parts (ValidMorS.inst0 valid) (Fin.cases partsA fun _ => trivial)

/-! ## Variables -/

theorem ValidCtxSS.lookup : ∀ {n : Nat} {Γ : Ctx Head n}, ValidCtxSS M Γ → ∀ i : Fin n,
    ValidTyS M Γ (Ctx.lookup Γ i) ∧ StructuredS M Γ (Ctx.lookup Γ i)
  | _, .nil, _, i => nomatch i
  | _, .snoc Γ A, valid, i => by
      obtain ⟨valid, validA, partsA⟩ := valid
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨validA.rename (ValidRenS.wk Γ A),
          StructuredS.rename A partsA (ValidRenS.wk Γ A)⟩
      · obtain ⟨validJ, partsJ⟩ := ValidCtxSS.lookup valid j
        exact ⟨validJ.rename (ValidRenS.wk Γ A),
          StructuredS.rename (Ctx.lookup Γ j) partsJ (ValidRenS.wk Γ A)⟩

theorem ValidTmS.var (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} (valid : ValidCtxSS M Γ)
    (i : Fin n) : ValidTmS M Γ (.var i) (Ctx.lookup Γ i) := by
  obtain ⟨validI, _⟩ := valid.lookup i
  refine ⟨validI, fun {_ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨P', den', h, hu⟩ := EqSubstS.lookup e i
  obtain rfl := DenS.deterministic laws.value den den'
  exact ⟨h, hu⟩

/-- A closed valid type is valid in every context. -/
theorem ValidTyS.liftClosed {k : Nat} {A : Tm Head 0} (valid : ValidTyS M .nil A)
    (Δ : Ctx Head k) : ValidTyS M Δ (Presentation.liftClosed A) :=
  valid.rename (ValidRenS.elim0 Δ)

theorem StructuredS.liftClosed {k : Nat} {A : Tm Head 0} (parts : StructuredS M .nil A)
    (Δ : Ctx Head k) : StructuredS M Δ (Presentation.liftClosed A) :=
  StructuredS.rename A parts (ValidRenS.elim0 Δ)

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
