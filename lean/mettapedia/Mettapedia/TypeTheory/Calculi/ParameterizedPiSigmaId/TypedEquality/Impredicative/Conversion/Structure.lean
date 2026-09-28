import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Substitutions

/-!
# Valid parts, renamings and substitutions in the conversion model

A term written as a type former carries the validity of its parts: the domain
and codomain of a dependent function or pair type, the carrier and endpoints
of an identity type. A valid context whose entries carry their valid parts is
*structured*.

A renaming or a substitution between contexts is valid when it sends related
valuations of the target to related valuations of the source, on both sides;
it then keeps validity. Instantiating the last variable of a context by a valid
term is valid, and so is every variable of a structured context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization (tailSub subst_rename_wk CtxFormed)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)

variable {Head L : Type} [LevelOrder L] {M : NModel Head L}

/-! ## Valid parts -/

variable (M) in
/-- The parts of a term written as a type former are valid, recursively. Other
terms have no parts to check. -/
def StructuredN : {n : Nat} → Ctx Head n → Tm Head n → Prop
  | _, Γ, .pi A B =>
      (ValidTyN M Γ A ∧ StructuredN Γ A) ∧
        ValidTyN M (.snoc Γ A) B ∧ StructuredN (.snoc Γ A) B
  | _, Γ, .sigma A B =>
      (ValidTyN M Γ A ∧ StructuredN Γ A) ∧
        ValidTyN M (.snoc Γ A) B ∧ StructuredN (.snoc Γ A) B
  | _, Γ, .id A a b =>
      (ValidTyN M Γ A ∧ StructuredN Γ A) ∧ ValidTmN M Γ a A ∧ ValidTmN M Γ b A
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
def ValidCtxNN : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => ValidCtxNN Γ ∧ ValidTyN M Γ A ∧ StructuredN M Γ A

theorem ValidCtxNN.valid : ∀ {n : Nat} {Γ : Ctx Head n}, ValidCtxNN M Γ → ValidCtxN M Γ
  | _, .nil, _ => trivial
  | _, .snoc _ _, valid => by
      obtain ⟨valid, validA, _⟩ := valid
      exact ⟨ValidCtxNN.valid valid, validA⟩

/-! ## Renamings between contexts -/

variable (M) in
/-- A renaming from the variables of `Γ` to those of `Δ` that sends related
valuations of `Δ` to related valuations of `Γ`. -/
def ValidRenN {n k : Nat} (Δ : Ctx Head k) (ρ : Ren n k) (Γ : Ctx Head n) : Prop :=
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head k m} {Θ : Ctx Head r}
    {ς ς' : Sub Head k r}, EqSubstN M Δ ξ σ σ' Θ ς ς' →
      EqSubstN M Γ ξ (fun i => σ (ρ i)) (fun i => σ' (ρ i)) Θ (fun i => ς (ρ i))
        fun i => ς' (ρ i)

theorem ValidRenN.wk {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) :
    ValidRenN M (.snoc Γ A) wk Γ :=
  fun e => e.1

theorem ValidRenN.elim0 {k : Nat} (Δ : Ctx Head k) : ValidRenN M Δ Fin.elim0 .nil :=
  fun e => e.formed

theorem ValidTyN.rename {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    {A : Tm Head n} (valid : ValidTyN M Γ A) (ren : ValidRenN M Δ ρ Γ) :
    ValidTyN M Δ (Presentation.rename ρ A) := fun e => by
  rw [subst_rename, subst_rename, subst_rename, subst_rename]
  exact valid (ren e)

theorem ValidTmN.rename {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    {t A : Tm Head n} (valid : ValidTmN M Γ t A) (ren : ValidRenN M Δ ρ Γ) :
    ValidTmN M Δ (Presentation.rename ρ t) (Presentation.rename ρ A) := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA.rename ren, fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  rw [subst_rename] at den
  rw [subst_rename, subst_rename, subst_rename, subst_rename, subst_rename]
  exact rel (ren e) den

theorem ValidRenN.lift {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    (ren : ValidRenN M Δ ρ Γ) (A : Tm Head n) :
    ValidRenN M (.snoc Δ (Presentation.rename ρ A)) (liftRen ρ) (.snoc Γ A) := by
  intro _ _ _ _ _ _ _ _ e
  obtain ⟨tail, P, den, h⟩ := e
  rw [subst_rename] at den h
  exact ⟨ren tail, P, den, h⟩

theorem StructuredN.rename : ∀ {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {ρ : Ren n k}
    (t : Tm Head n), StructuredN M Γ t → ValidRenN M Δ ρ Γ →
      StructuredN M Δ (Presentation.rename ρ t)
  | _, _, _, _, _, .pi A B, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.rename ren, StructuredN.rename A partsA ren⟩,
        validB.rename (ren.lift A), StructuredN.rename B partsB (ren.lift A)⟩
  | _, _, _, _, _, .sigma A B, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.rename ren, StructuredN.rename A partsA ren⟩,
        validB.rename (ren.lift A), StructuredN.rename B partsB (ren.lift A)⟩
  | _, _, _, _, _, .id A _ _, parts, ren => by
      obtain ⟨⟨validA, partsA⟩, validL, validR⟩ := parts
      exact ⟨⟨validA.rename ren, StructuredN.rename A partsA ren⟩, validL.rename ren,
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
def ValidMorN {n k : Nat} (Δ : Ctx Head k) (τ : Sub Head n k) (Γ : Ctx Head n) : Prop :=
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head k m} {Θ : Ctx Head r}
    {ς ς' : Sub Head k r}, EqSubstN M Δ ξ σ σ' Θ ς ς' →
      EqSubstN M Γ ξ (fun i => Presentation.subst σ (τ i))
        (fun i => Presentation.subst σ' (τ i)) Θ (fun i => Presentation.subst ς (τ i))
        fun i => Presentation.subst ς' (τ i)

theorem ValidTyN.subst {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {τ : Sub Head n k}
    {A : Tm Head n} (valid : ValidTyN M Γ A) (mor : ValidMorN M Δ τ Γ) :
    ValidTyN M Δ (Presentation.subst τ A) := fun e => by
  rw [subst_comp, subst_comp, subst_comp, subst_comp]
  exact valid (mor e)

theorem ValidTmN.subst {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {τ : Sub Head n k}
    {t A : Tm Head n} (valid : ValidTmN M Γ t A) (mor : ValidMorN M Δ τ Γ) :
    ValidTmN M Δ (Presentation.subst τ t) (Presentation.subst τ A) := by
  obtain ⟨validA, rel⟩ := valid
  refine ⟨validA.subst mor, fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  rw [subst_comp] at den
  rw [subst_comp, subst_comp, subst_comp, subst_comp, subst_comp]
  exact rel (mor e) den

/-- Substituting after the tail of a substitution for an extended context. -/
theorem tailSub_subst_liftSub {n k m : Nat} (σ : Sub Head (k + 1) m) (τ : Sub Head n k) :
    (tailSub fun i => Presentation.subst σ (liftSub τ i)) =
      fun i => Presentation.subst (tailSub σ) (τ i) :=
  funext fun i => subst_rename_wk σ (τ i)

theorem ValidMorN.lift {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k} {τ : Sub Head n k}
    (mor : ValidMorN M Δ τ Γ) (A : Tm Head n) :
    ValidMorN M (.snoc Δ (Presentation.subst τ A)) (liftSub τ) (.snoc Γ A) := by
  intro _ _ _ σ σ' _ ς ς' e
  obtain ⟨tail, P, den, h⟩ := e
  rw [subst_comp] at den
  refine ⟨?_, P, ?_, ?_⟩
  · rw [tailSub_subst_liftSub, tailSub_subst_liftSub, tailSub_subst_liftSub,
      tailSub_subst_liftSub]
    exact mor tail
  · rw [tailSub_subst_liftSub]
    exact den
  · rw [tailSub_subst_liftSub, ← subst_comp]
    exact h

theorem StructuredN.subst : ∀ {n k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head k}
    {τ : Sub Head n k} (t : Tm Head n), StructuredN M Γ t → ValidMorN M Δ τ Γ →
      (∀ i, StructuredN M Δ (τ i)) → StructuredN M Δ (Presentation.subst τ t)
  | _, _, _, _, _, .var i, _, _, images => images i
  | _, _, _, Δ, τ, .pi A B, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.subst mor, StructuredN.subst A partsA mor images⟩,
        validB.subst (mor.lift A),
        StructuredN.subst B partsB (mor.lift A) (Fin.cases trivial fun j =>
          StructuredN.rename (τ j) (images j) (ValidRenN.wk Δ (Presentation.subst τ A)))⟩
  | _, _, _, Δ, τ, .sigma A B, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validB, partsB⟩ := parts
      exact ⟨⟨validA.subst mor, StructuredN.subst A partsA mor images⟩,
        validB.subst (mor.lift A),
        StructuredN.subst B partsB (mor.lift A) (Fin.cases trivial fun j =>
          StructuredN.rename (τ j) (images j) (ValidRenN.wk Δ (Presentation.subst τ A)))⟩
  | _, _, _, _, _, .id A _ _, parts, mor, images => by
      obtain ⟨⟨validA, partsA⟩, validL, validR⟩ := parts
      exact ⟨⟨validA.subst mor, StructuredN.subst A partsA mor images⟩, validL.subst mor,
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
theorem ValidTmN.val (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (ctx : ValidCtxN M Γ) (valid : ValidTmN M Γ t A) {m r : Nat} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') {P : NPack M m}
    (den : DenN M ξ (Presentation.subst σ A) P) : P.Val (Presentation.subst σ t) :=
  (valid.2 (e.refl_left laws ctx) den).1

/-- Instantiating the last variable of a context by a valid term. -/
theorem ValidMorN.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTmN M Γ a A) : ValidMorN M Γ (subst0 a) (.snoc Γ A) := by
  intro _ _ _ σ σ' _ ς ς' e
  obtain ⟨P, den, -, -⟩ := valid.1 e
  exact ⟨e, P, den, valid.2 e den⟩

theorem ValidTyN.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} {B : Tm Head (n + 1)}
    (validB : ValidTyN M (.snoc Γ A) B) (valid : ValidTmN M Γ a A) :
    ValidTyN M Γ (Presentation.inst0 a B) :=
  validB.subst (ValidMorN.inst0 valid)

theorem ValidTmN.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    {t B : Tm Head (n + 1)} (validT : ValidTmN M (.snoc Γ A) t B) (valid : ValidTmN M Γ a A) :
    ValidTmN M Γ (Presentation.inst0 a t) (Presentation.inst0 a B) :=
  validT.subst (ValidMorN.inst0 valid)

theorem StructuredN.inst0 {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    {B : Tm Head (n + 1)} (parts : StructuredN M (.snoc Γ A) B)
    (valid : ValidTmN M Γ a A) (partsA : StructuredN M Γ a) :
    StructuredN M Γ (Presentation.inst0 a B) :=
  StructuredN.subst B parts (ValidMorN.inst0 valid) (Fin.cases partsA fun _ => trivial)

/-! ## Variables -/

theorem ValidCtxNN.lookup : ∀ {n : Nat} {Γ : Ctx Head n}, ValidCtxNN M Γ → ∀ i : Fin n,
    ValidTyN M Γ (Ctx.lookup Γ i) ∧ StructuredN M Γ (Ctx.lookup Γ i)
  | _, .nil, _, i => nomatch i
  | _, .snoc Γ A, valid, i => by
      obtain ⟨valid, validA, partsA⟩ := valid
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨validA.rename (ValidRenN.wk Γ A),
          StructuredN.rename A partsA (ValidRenN.wk Γ A)⟩
      · obtain ⟨validJ, partsJ⟩ := ValidCtxNN.lookup valid j
        exact ⟨validJ.rename (ValidRenN.wk Γ A),
          StructuredN.rename (Ctx.lookup Γ j) partsJ (ValidRenN.wk Γ A)⟩

/-- A variable of a structured context is a valid term of its type. -/
theorem ValidTmN.var (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} (valid : ValidCtxNN M Γ)
    (i : Fin n) : ValidTmN M Γ (.var i) (Ctx.lookup Γ i) := by
  obtain ⟨validI, _⟩ := valid.lookup i
  refine ⟨validI, fun {_ _ _ _ _ _ _ _} e {P} den => ?_⟩
  obtain ⟨P', den', h⟩ := EqSubstN.lookup e i
  obtain rfl := ValueSide.DenS.deterministic laws.value den den'
  exact h

/-- A closed valid type is valid in every context. -/
theorem ValidTyN.liftClosed {k : Nat} {A : Tm Head 0} (valid : ValidTyN M .nil A)
    (Δ : Ctx Head k) : ValidTyN M Δ (Presentation.liftClosed A) :=
  valid.rename (ValidRenN.elim0 Δ)

theorem StructuredN.liftClosed {k : Nat} {A : Tm Head 0} (parts : StructuredN M .nil A)
    (Δ : Ctx Head k) : StructuredN M Δ (Presentation.liftClosed A) :=
  StructuredN.rename A parts (ValidRenN.elim0 Δ)

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
