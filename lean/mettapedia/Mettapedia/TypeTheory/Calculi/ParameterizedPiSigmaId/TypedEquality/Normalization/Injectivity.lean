import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Facts

/-!
# The facts about weak-head forms, from the normalization model

In a formed context, derivable typings and equalities escape the model at the
identity substitution. Equal dependent function types have equal domains and
codomains, and likewise for dependent pair types; equal identity types have
equal carriers and endpoints; equal heads are the same up to the rule
package's head equality; equal inductive types are the same constant; and
types with different formers are never equal. Every reducible type reduces to a
weak-head form. Together these are the facts about the weak-head forms of types
(`FormFacts.ofSemantic`), which the consequences of the typed equality are
stated over.

All statements are about the typed equality `Equal` of the rule package, for
a setting whose declared constants are semantic.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

section Escape

variable (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
include laws constants

/-- A derivable typing in a formed context: the term is reducible at the pack of
its type. -/
theorem Typed.reducible {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typed S.R Γ t A) (formed : CtxFormed S.R Γ) :
    Reducible S Γ A (packOf S Γ A) ∧ (packOf S Γ A).redTm t := by
  have valid := CtxFormed.valid laws constants formed
  have ids := (valid.formed_ids laws).2
  have v := Typed.valid laws constants typing valid
  obtain ⟨P, r⟩ := v.type.red ids
  have h := v.red ids r
  rw [subst_ids] at r h
  rw [r.eq_packOf laws] at h r
  exact ⟨r, h⟩

/-- A derivable equality in a formed context: the terms are reducibly equal at
the pack of their type. -/
theorem Equal.reducible {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (equal : Equal S.R Γ a b A) (formed : CtxFormed S.R Γ) :
    Reducible S Γ A (packOf S Γ A) ∧ (packOf S Γ A).eqTm a b := by
  have valid := CtxFormed.valid laws constants formed
  have ids := (valid.formed_ids laws).2
  have v := Equal.valid laws constants equal valid
  obtain ⟨P, r⟩ := v.left.type.red ids
  have h := v.eq ids r
  rw [subst_ids] at r
  rw [subst_ids, subst_ids] at h
  rw [r.eq_packOf laws] at h r
  exact ⟨r, h⟩

/-- Equal types in a formed context: the first is reducibly equal to the
second. -/
theorem TypeEq.reducible {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (equal : TypeEq S.R Γ A B) (formed : CtxFormed S.R Γ) :
    Reducible S Γ A (packOf S Γ A) ∧ (packOf S Γ A).eqTy B := by
  obtain ⟨u, hu, e⟩ := equal
  have valid := CtxFormed.valid laws constants formed
  have ids := (valid.formed_ids laws).2
  have v := (Equal.valid laws constants e valid).tyEq laws hu
  obtain ⟨P, r⟩ := v.left.red ids
  have h := v.eq ids r
  rw [subst_ids] at r h
  rw [r.eq_packOf laws] at h r
  exact ⟨r, h⟩

/-- A valid term of a formed context is typed. -/
theorem ValidTm.typed {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (valid : ValidTm S Γ t A)
    (formed : CtxFormed S.R Γ) : Typed S.R Γ t A := by
  have ids := ((CtxFormed.valid laws constants formed).formed_ids laws).2
  obtain ⟨P, r⟩ := valid.type.red ids
  have h := valid.red ids r
  rw [subst_ids] at r h
  exact ((r.escape laws).redTm h).1

/-- A type of a formed context is reducible. -/
theorem IsType.reducible {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    (formed' : IsType S.R Γ A) (formed : CtxFormed S.R Γ) :
    Reducible S Γ A (packOf S Γ A) :=
  (TypeEq.reducible laws constants formed'.refl formed).1

end Escape

/-! ## Injectivity in the model -/

section Injectivity

variable (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
include laws constants

/-- Injectivity of dependent function types. -/
theorem Reducible.pi_injective {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (equal : TypeEq S.R Γ (.pi A B) (.pi A' B'))
    (formed : CtxFormed S.R Γ) : TypeEq S.R Γ A A' ∧ TypeEq S.R (.snoc Γ A) B B' := by
  obtain ⟨r, eqTy⟩ := equal.reducible laws constants formed
  obtain ⟨parts, same, _⟩ := Reducible.pi_view laws r
  rw [same] at eqTy
  obtain ⟨dom', cod', red', _, domEq, codEq⟩ := eqTy
  obtain ⟨rfl, rfl⟩ := Tm.pi.inj (WhRed.eq_of_whnf (pi_whnf S.shape _ _) red'.red).symm
  have h₁ := domEq (World.refl formed)
  simp only [canonicalPoly_domPack, rename_id] at h₁
  obtain ⟨w, h0, rcod⟩ := parts.fresh laws formed
  have h₂ : (packOf S (.snoc Γ A) B).eqTy B' := by
    have h := codEq w h0
    change (packOf S (.snoc Γ A) (inst0 (.var 0) (Presentation.rename (liftRen wk) B))).eqTy
      (inst0 (.var 0) (Presentation.rename (liftRen wk) B')) at h
    rwa [inst0_var_rename_liftRen_wk, inst0_var_rename_liftRen_wk] at h
  rw [inst0_var_rename_liftRen_wk] at rcod
  exact ⟨laws.convTy_sound (((parts.dom_self formed).escape laws).eqTy h₁),
    laws.convTy_sound ((rcod.escape laws).eqTy h₂)⟩

/-- Injectivity of dependent pair types. -/
theorem Reducible.sigma_injective {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (equal : TypeEq S.R Γ (.sigma A B) (.sigma A' B'))
    (formed : CtxFormed S.R Γ) : TypeEq S.R Γ A A' ∧ TypeEq S.R (.snoc Γ A) B B' := by
  obtain ⟨r, eqTy⟩ := equal.reducible laws constants formed
  obtain ⟨parts, same, _⟩ := Reducible.sigma_view laws r
  rw [same] at eqTy
  obtain ⟨dom', cod', red', _, domEq, codEq⟩ := eqTy
  obtain ⟨rfl, rfl⟩ := Tm.sigma.inj (WhRed.eq_of_whnf (sigma_whnf S.shape _ _) red'.red).symm
  have h₁ := domEq (World.refl formed)
  simp only [canonicalPoly_domPack, rename_id] at h₁
  obtain ⟨w, h0, rcod⟩ := parts.fresh laws formed
  have h₂ : (packOf S (.snoc Γ A) B).eqTy B' := by
    have h := codEq w h0
    change (packOf S (.snoc Γ A) (inst0 (.var 0) (Presentation.rename (liftRen wk) B))).eqTy
      (inst0 (.var 0) (Presentation.rename (liftRen wk) B')) at h
    rwa [inst0_var_rename_liftRen_wk, inst0_var_rename_liftRen_wk] at h
  rw [inst0_var_rename_liftRen_wk] at rcod
  exact ⟨laws.convTy_sound (((parts.dom_self formed).escape laws).eqTy h₁),
    laws.convTy_sound ((rcod.escape laws).eqTy h₂)⟩

/-- Injectivity of identity types. -/
theorem Reducible.id_injective {n : Nat} {Γ : Ctx Head n} {A A' a a' b b' : Tm Head n}
    (equal : TypeEq S.R Γ (.id A a b) (.id A' a' b')) (formed : CtxFormed S.R Γ) :
    TypeEq S.R Γ A A' ∧ Equal S.R Γ a a' A ∧ Equal S.R Γ b b' A := by
  obtain ⟨r, eqTy⟩ := equal.reducible laws constants formed
  obtain ⟨tyPack, same, _, rTy, _, _⟩ := Reducible.id_view r
  rw [same] at eqTy
  obtain ⟨ty', lhs', rhs', red', _, tyEq, lEq, rEq⟩ := eqTy
  obtain ⟨rfl, rfl, rfl⟩ := Tm.id.inj (WhRed.eq_of_whnf (id_whnf S.shape _ _ _) red'.red).symm
  have e := rTy.escape laws
  exact ⟨laws.convTy_sound (e.eqTy tyEq), laws.convTm_sound (e.eqTm lEq),
    laws.convTm_sound (e.eqTm rEq)⟩

/-- No uniqueness of identity proofs by conversion: a neutral proof of an
identity is not equal to a reflexivity proof. -/
theorem Equal.neutral_ne_refl {n : Nat} {Γ : Ctx Head n} {p x A a b : Tm Head n}
    (neutral : Neutral S.roles p) (formed : CtxFormed S.R Γ) :
    ¬ Equal S.R Γ p (.refl x) (.id A a b) := by
  intro equal
  obtain ⟨r, eqTm⟩ := Equal.reducible laws constants equal formed
  obtain ⟨tyPack, same, _, _, _, _⟩ := Reducible.id_view r
  rw [same] at eqTm
  obtain ⟨nf, nf', red, red', _, shapes⟩ := eqTm
  obtain rfl := WhRed.eq_of_whnf (neutral.whnf S.shape) red.red
  obtain rfl := WhRed.eq_of_whnf (refl_whnf S.shape x) red'.red
  rcases shapes with ⟨_, _, first, _⟩ | ⟨_, second, _⟩
  · exact neutral.ne_refl first
  · exact second.ne_refl rfl

omit laws constants in
/-- An equal type of a reducible head reduces to the same head, up to head
equality. -/
theorem LR.head_eqTy_inv {l : L} {rec : L → RedRel Head} {n : Nat} {Γ : Ctx Head n}
    {h : Head} {Q : Pack Head n} (reducible : LR S l rec Γ (.head h) Q) {X : Tm Head n}
    (equal : Q.eqTy X) : ∃ h', RedTy S.R S.roles Γ X (.head h') ∧ HeadSame S.R h h' := by
  have normal : Whnf S.R S.roles (.head h : Tm Head n) := head_whnf S.shape h
  cases reducible with
  | sort _ _ _ red =>
      obtain rfl := Tm.head.inj (WhRed.eq_of_whnf normal red.red)
      exact equal
  | neutral red neutral =>
      exact absurd (WhRed.eq_of_whnf normal red.red) (neutral.not_former.1 _)
  | ground _ red =>
      obtain rfl := Tm.head.inj (WhRed.eq_of_whnf normal red.red)
      exact equal
  | pi red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro e; cases e)
  | sigma red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro e; cases e)
  | ident red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro e; cases e)
  | inductiveType red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro e; cases e)

omit laws constants in
theorem Reducible.head_eqTy_inv {n : Nat} {Γ : Ctx Head n} {h : Head} {Q : Pack Head n}
    (reducible : Reducible S Γ (.head h) Q) {X : Tm Head n} (equal : Q.eqTy X) :
    ∃ h', RedTy S.R S.roles Γ X (.head h') ∧ HeadSame S.R h h' := by
  obtain ⟨l, r⟩ := reducible
  exact LR.head_eqTy_inv r equal

/-- Injectivity of heads: equal heads are the same up to head equality. -/
theorem Reducible.head_injective {n : Nat} {Γ : Ctx Head n} {h h' : Head}
    (equal : TypeEq S.R Γ (.head h) (.head h')) (formed : CtxFormed S.R Γ) :
    HeadSame S.R h h' := by
  obtain ⟨r, eqTy⟩ := equal.reducible laws constants formed
  obtain ⟨h'', red, same⟩ := Reducible.head_eqTy_inv r eqTy
  obtain rfl := Tm.head.inj (WhRed.eq_of_whnf (head_whnf S.shape h') red.red)
  exact same

/-- Injectivity of inductive type constants: equal inductive types are the same
constant. -/
theorem Reducible.inductive_injective {n : Nat} {Γ : Ctx Head n} {T T' : DeclName}
    {ctors ctors' : List (DeclName × List (Field Head))} (role : S.roles T = .inductive ctors)
    (role' : S.roles T' = .inductive ctors')
    (equal : TypeEq S.R Γ (.const T) (.const T')) (formed : CtxFormed S.R Γ) : T = T' := by
  obtain ⟨r, eqTy⟩ := equal.reducible laws constants formed
  obtain ⟨fieldPack, same, _⟩ := Reducible.inductive_view role r
  rw [same] at eqTy
  exact Tm.const.inj (WhRed.eq_of_whnf (inductive_whnf S.shape role') eqTy.red)

end Injectivity

/-! ## Discrimination in the model -/

section Discrimination

variable (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
include laws constants

/-- The formers of a type in weak-head normal form. -/
inductive Former (S : Setting Head L) {n : Nat} : Tm Head n → Type where
  | head (h : Head) : Former S (.head h)
  | pi (A : Tm Head n) (B : Tm Head (n + 1)) : Former S (.pi A B)
  | sigma (A : Tm Head n) (B : Tm Head (n + 1)) : Former S (.sigma A B)
  | id (A a b : Tm Head n) : Former S (.id A a b)
  | inductiveType (T : DeclName) (ctors : List (DeclName × List (Field Head)))
      (role : S.roles T = .inductive ctors) : Former S (.const T)

/-- The kind of a former. -/
def Former.kind {n : Nat} {A : Tm Head n} : Former S A → Nat
  | .head _ => 0
  | .pi _ _ => 1
  | .sigma _ _ => 2
  | .id _ _ _ => 3
  | .inductiveType _ _ _ => 4

/-- The weak-head normal form of an equal type has the former of the first
type. -/
theorem Reducible.former {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (fA : Former S A)
    (fB : Former S B) (equal : TypeEq S.R Γ A B) (formed : CtxFormed S.R Γ) :
    fA.kind = fB.kind := by
  obtain ⟨r, eqTy⟩ := equal.reducible laws constants formed
  have normalB : Whnf S.R S.roles B := by
    cases fB with
    | head h => exact head_whnf S.shape h
    | pi A B => exact pi_whnf S.shape A B
    | sigma A B => exact sigma_whnf S.shape A B
    | id A a b => exact id_whnf S.shape A a b
    | inductiveType T ctors role => exact inductive_whnf S.shape role
  cases fA with
  | head h =>
      obtain ⟨h', red, _⟩ := Reducible.head_eqTy_inv r eqTy
      have e := WhRed.eq_of_whnf normalB red.red
      cases fB <;> first | rfl | cases e
  | pi A₁ B₁ =>
      obtain ⟨parts, same, _⟩ := Reducible.pi_view laws r
      rw [same] at eqTy
      obtain ⟨_, _, red, _⟩ := eqTy
      have e := WhRed.eq_of_whnf normalB red.red
      cases fB <;> first | rfl | cases e
  | sigma A₁ B₁ =>
      obtain ⟨parts, same, _⟩ := Reducible.sigma_view laws r
      rw [same] at eqTy
      obtain ⟨_, _, red, _⟩ := eqTy
      have e := WhRed.eq_of_whnf normalB red.red
      cases fB <;> first | rfl | cases e
  | id A₁ a₁ b₁ =>
      obtain ⟨tyPack, same, _⟩ := Reducible.id_view r
      rw [same] at eqTy
      obtain ⟨_, _, _, red, _⟩ := eqTy
      have e := WhRed.eq_of_whnf normalB red.red
      cases fB <;> first | rfl | cases e
  | inductiveType T ctors role =>
      obtain ⟨fieldPack, same, _⟩ := Reducible.inductive_view role r
      rw [same] at eqTy
      have e := WhRed.eq_of_whnf normalB eqTy.red
      cases fB <;> first | rfl | cases e

end Discrimination

/-! ## Weak-head forms of types in the model -/

/-- The weak-head form a reducible type reduces to. -/
theorem LR.form {l : L} {rec : L → RedRel Head} {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : LR S l rec Γ A P) :
    ∃ A', RedTy S.R S.roles Γ A A' ∧ IsTypeForm S.roles A' := by
  cases reducible with
  | sort _ _ _ red => exact ⟨_, red, .inl ⟨_, rfl⟩⟩
  | neutral red neutral _ _ _ => exact ⟨_, red, .inr (.inr (.inr (.inr (.inl neutral))))⟩
  | ground _ red _ _ => exact ⟨_, red, .inl ⟨_, rfl⟩⟩
  | pi red _ _ _ _ _ _ => exact ⟨_, red, .inr (.inl ⟨_, _, rfl⟩)⟩
  | sigma red _ _ _ _ _ _ => exact ⟨_, red, .inr (.inr (.inl ⟨_, _, rfl⟩))⟩
  | ident red _ _ _ _ _ _ _ _ _ => exact ⟨_, red, .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))⟩
  | inductiveType red role _ _ _ _ =>
      exact ⟨_, red, .inr (.inr (.inr (.inr (.inr ⟨_, _, role, rfl⟩))))⟩

/-- A reducible neutral type has the neutral pack. -/
theorem Reducible.neutral_view {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) (neutral : Neutral S.roles A) : P = neutralPack S Γ A := by
  obtain ⟨_, r⟩ := reducible
  have normal := neutral.whnf S.shape
  cases r with
  | sort _ _ _ red => exact absurd (WhRed.eq_of_whnf normal red.red).symm (neutral.not_former.1 _)
  | neutral red _ _ _ _ =>
      obtain rfl := WhRed.eq_of_whnf normal red.red
      rfl
  | ground _ red _ _ => exact absurd (WhRed.eq_of_whnf normal red.red).symm (neutral.not_former.1 _)
  | pi red _ _ _ _ _ _ =>
      exact absurd (WhRed.eq_of_whnf normal red.red).symm (neutral.not_former.2.1 _ _)
  | sigma red _ _ _ _ _ _ =>
      exact absurd (WhRed.eq_of_whnf normal red.red).symm (neutral.not_former.2.2.1 _ _)
  | ident red _ _ _ _ _ _ _ _ _ =>
      exact absurd (WhRed.eq_of_whnf normal red.red).symm (neutral.not_former.2.2.2 _ _ _)
  | inductiveType red role _ _ _ _ =>
      exact absurd (WhRed.eq_of_whnf normal red.red).symm (neutral.ne_inductive role)

section Forms

variable (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
include laws constants

/-- Every type of a formed context reduces to a weak-head form. -/
theorem Reducible.typeForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (isType : IsType S.R Γ A)
    (formed : CtxFormed S.R Γ) : ∃ A', RedTy S.R S.roles Γ A A' ∧ IsTypeForm S.roles A' := by
  obtain ⟨_, r⟩ := IsType.reducible laws constants isType formed
  exact LR.form r

/-- A type equal to a neutral type has a neutral weak-head form. -/
theorem Reducible.neutral_form {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (equal : TypeEq S.R Γ A B) (formed : CtxFormed S.R Γ) (neutral : Neutral S.roles A)
    (form : IsTypeForm S.roles B) : Neutral S.roles B := by
  obtain ⟨r, eqTy⟩ := equal.reducible laws constants formed
  rw [Reducible.neutral_view r neutral] at eqTy
  obtain ⟨ty', red, neutral', _⟩ := eqTy
  obtain rfl := WhRed.eq_of_whnf form.whnf red.red
  exact neutral'

/-- The weak-head forms of equal types match. -/
theorem Reducible.forms {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (equal : TypeEq S.R Γ A B)
    (formed : CtxFormed S.R Γ) (fA : IsTypeForm S.roles A) (fB : IsTypeForm S.roles B) :
    FormsMatch S.R S.roles Γ A B := by
  have kinds := fun (first : Former S A) (second : Former S B) =>
    Reducible.former laws constants first second equal formed
  have backward := fun (nB : Neutral S.roles B) (fA : IsTypeForm S.roles A) =>
    Reducible.neutral_form laws constants equal.symm formed nB fA
  rcases fA with ⟨h, rfl⟩ | ⟨A₁, B₁, rfl⟩ | ⟨A₁, B₁, rfl⟩ | ⟨C, x, y, rfl⟩ | nA |
      ⟨T, ctors, role, rfl⟩
  · rcases fB with ⟨h', rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨C', x', y', rfl⟩ | nB |
        ⟨T', ctors', role', rfl⟩
    · exact .inl ⟨h, h', rfl, rfl, Reducible.head_injective laws constants equal formed⟩
    · exact absurd (kinds (.head _) (.pi _ _)) (by simp [Former.kind])
    · exact absurd (kinds (.head _) (.sigma _ _)) (by simp [Former.kind])
    · exact absurd (kinds (.head _) (.id _ _ _)) (by simp [Former.kind])
    · exact absurd (backward nB (.inl ⟨_, rfl⟩)) (fun n => n.not_former.1 _ rfl)
    · exact absurd (kinds (.head _) (.inductiveType _ _ role')) (by simp [Former.kind])
  · rcases fB with ⟨h', rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨C', x', y', rfl⟩ | nB |
        ⟨T', ctors', role', rfl⟩
    · exact absurd (kinds (.pi _ _) (.head _)) (by simp [Former.kind])
    · obtain ⟨eA, eB⟩ := Reducible.pi_injective laws constants equal formed
      exact .inr (.inl ⟨A₁, B₁, A₂, B₂, rfl, rfl, eA, eB⟩)
    · exact absurd (kinds (.pi _ _) (.sigma _ _)) (by simp [Former.kind])
    · exact absurd (kinds (.pi _ _) (.id _ _ _)) (by simp [Former.kind])
    · exact absurd (backward nB (.inr (.inl ⟨_, _, rfl⟩))) (fun n => n.not_former.2.1 _ _ rfl)
    · exact absurd (kinds (.pi _ _) (.inductiveType _ _ role')) (by simp [Former.kind])
  · rcases fB with ⟨h', rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨C', x', y', rfl⟩ | nB |
        ⟨T', ctors', role', rfl⟩
    · exact absurd (kinds (.sigma _ _) (.head _)) (by simp [Former.kind])
    · exact absurd (kinds (.sigma _ _) (.pi _ _)) (by simp [Former.kind])
    · obtain ⟨eA, eB⟩ := Reducible.sigma_injective laws constants equal formed
      exact .inr (.inr (.inl ⟨A₁, B₁, A₂, B₂, rfl, rfl, eA, eB⟩))
    · exact absurd (kinds (.sigma _ _) (.id _ _ _)) (by simp [Former.kind])
    · exact absurd (backward nB (.inr (.inr (.inl ⟨_, _, rfl⟩))))
        (fun n => n.not_former.2.2.1 _ _ rfl)
    · exact absurd (kinds (.sigma _ _) (.inductiveType _ _ role')) (by simp [Former.kind])
  · rcases fB with ⟨h', rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨C', x', y', rfl⟩ | nB |
        ⟨T', ctors', role', rfl⟩
    · exact absurd (kinds (.id _ _ _) (.head _)) (by simp [Former.kind])
    · exact absurd (kinds (.id _ _ _) (.pi _ _)) (by simp [Former.kind])
    · exact absurd (kinds (.id _ _ _) (.sigma _ _)) (by simp [Former.kind])
    · obtain ⟨eC, ex, ey⟩ := Reducible.id_injective laws constants equal formed
      exact .inr (.inr (.inr (.inl ⟨C, x, y, C', x', y', rfl, rfl, eC, ex, ey⟩)))
    · exact absurd (backward nB (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))))
        (fun n => n.not_former.2.2.2 _ _ _ rfl)
    · exact absurd (kinds (.id _ _ _) (.inductiveType _ _ role')) (by simp [Former.kind])
  · exact .inr (.inr (.inr (.inr (.inr
      ⟨nA, Reducible.neutral_form laws constants equal formed nA fB⟩))))
  · rcases fB with ⟨h', rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨A₂, B₂, rfl⟩ | ⟨C', x', y', rfl⟩ | nB |
        ⟨T', ctors', role', rfl⟩
    · exact absurd (kinds (.inductiveType _ _ role) (.head _)) (by simp [Former.kind])
    · exact absurd (kinds (.inductiveType _ _ role) (.pi _ _)) (by simp [Former.kind])
    · exact absurd (kinds (.inductiveType _ _ role) (.sigma _ _)) (by simp [Former.kind])
    · exact absurd (kinds (.inductiveType _ _ role) (.id _ _ _)) (by simp [Former.kind])
    · exact absurd (backward nB (.inr (.inr (.inr (.inr (.inr ⟨_, _, role, rfl⟩))))))
        (fun n => n.ne_inductive role rfl)
    · obtain rfl := Reducible.inductive_injective laws constants role role' equal formed
      exact .inr (.inr (.inr (.inr (.inl ⟨T, ctors, role, rfl, rfl⟩))))

/-- **The facts about weak-head forms of types, for a setting whose declared
constants are semantic**, from the normalization model. -/
theorem FormFacts.ofSemantic : FormFacts S.R S.roles where
  typeForm := fun isType formed => Reducible.typeForm laws constants isType formed
  forms := fun equal formed fA fB => Reducible.forms laws constants equal formed fA fB

end Forms

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
