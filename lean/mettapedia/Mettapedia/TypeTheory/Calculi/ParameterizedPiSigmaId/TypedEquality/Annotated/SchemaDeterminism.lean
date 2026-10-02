import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ComputationSchemas

/-!
# Determinism of annotated root steps read off rewrite schemas

The annotated root steps of a presented rule package (`ChurchRules.ofSchemas`) are
the instances of its elaborated schemas. They are deterministic
(`ChurchRules.ofSchemas_deterministic`) when the rule package's root steps are and
the schemas are determined by their left sides (`SchemaDeterminate`): every
metavariable occurs in its schema's left side, and two left sides with a common
instance are one left side. Two schemas with one left side have one right side, by
the determinism of the rule package at the left side itself, and one annotated
instance of a left side fixes the substitution at every metavariable
(`subst_annotateWith_agree`).

**Apart terms** (`Apart`): two first-order terms that differ at a position where
neither has a variable have no common instance (`Apart.subst_ne`). Apartness is
stable under instantiating the second term (`Apart.subst_right`), and it decides the
second condition for finitely many left sides at once (`AllApart`). The first
condition is decided by `coversAll`, for the left sides of declared computations by
`DeclaredComputation.checkCovers`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open AlgebraicSchema (SchemaFamily SchemaStep variableMultiplicity)

variable {Head : Type}

/-! ## Apart terms -/

section Apart

variable [DecidableEq Head]

/-- Two terms that differ at a position where neither has a variable: two different
constants or heads, or two of a constant, a head, an application and a reflexivity
proof of different forms. -/
def Apart : {k₁ k₂ : Nat} → Tm Head k₁ → Tm Head k₂ → Bool
  | _, _, .const c, .const c' => !decide (c = c')
  | _, _, .head h, .head h' => !decide (h = h')
  | _, _, .app f a, .app f' a' => Apart f f' || Apart a a'
  | _, _, .refl a, .refl a' => Apart a a'
  | _, _, .const _, .head _ => true
  | _, _, .const _, .app _ _ => true
  | _, _, .const _, .refl _ => true
  | _, _, .head _, .const _ => true
  | _, _, .head _, .app _ _ => true
  | _, _, .head _, .refl _ => true
  | _, _, .app _ _, .const _ => true
  | _, _, .app _ _, .head _ => true
  | _, _, .app _ _, .refl _ => true
  | _, _, .refl _, .const _ => true
  | _, _, .refl _, .head _ => true
  | _, _, .refl _, .app _ _ => true
  | _, _, _, _ => false

theorem Apart.app_iff {k₁ k₂ : Nat} {f a : Tm Head k₁} {f' a' : Tm Head k₂} :
    Apart (.app f a) (.app f' a') = true ↔ Apart f f' = true ∨ Apart a a' = true := by
  show (Apart f f' || Apart a a') = true ↔ _
  rw [Bool.or_eq_true]

/-- **Apart terms have no common instance.** -/
theorem Apart.subst_ne {n k₁ : Nat} (L₁ : Tm Head k₁) : ∀ {k₂ : Nat} (L₂ : Tm Head k₂),
    Apart L₁ L₂ = true → ∀ (τ₁ : Sub Head k₁ n) (τ₂ : Sub Head k₂ n),
      Presentation.subst τ₁ L₁ ≠ Presentation.subst τ₂ L₂ := by
  induction L₁ with
  | var i => intro k₂ L₂ h; cases L₂ <;> cases h
  | const c =>
      intro k₂ L₂ h τ₁ τ₂ e
      cases L₂ with
      | const c' =>
          cases hd : decide (c = c') with
          | true =>
              rw [show Apart (.const c : Tm Head _) (.const c' : Tm Head _) = !decide (c = c')
                from rfl, hd] at h
              cases h
          | false => exact of_decide_eq_false hd (Tm.const.inj e)
      | var => cases h
      | head => cases e
      | app => cases e
      | refl => cases e
      | pi => cases h
      | sigma => cases h
      | id => cases h
      | lam => cases h
      | pair => cases h
      | fst => cases h
      | snd => cases h
  | head h₀ =>
      intro k₂ L₂ h τ₁ τ₂ e
      cases L₂ with
      | head h₁ =>
          cases hd : decide (h₀ = h₁) with
          | true =>
              rw [show Apart (.head h₀ : Tm Head _) (.head h₁ : Tm Head _) = !decide (h₀ = h₁)
                from rfl, hd] at h
              cases h
          | false => exact of_decide_eq_false hd (Tm.head.inj e)
      | var => cases h
      | const => cases e
      | app => cases e
      | refl => cases e
      | pi => cases h
      | sigma => cases h
      | id => cases h
      | lam => cases h
      | pair => cases h
      | fst => cases h
      | snd => cases h
  | app f a ihf iha =>
      intro k₂ L₂ h τ₁ τ₂ e
      cases L₂ with
      | app f' a' =>
          injection e with _ e₁ e₂
          rcases Apart.app_iff.1 h with hf | ha
          · exact ihf f' hf τ₁ τ₂ e₁
          · exact iha a' ha τ₁ τ₂ e₂
      | var => cases h
      | const => cases e
      | head => cases e
      | refl => cases e
      | pi => cases h
      | sigma => cases h
      | id => cases h
      | lam => cases h
      | pair => cases h
      | fst => cases h
      | snd => cases h
  | refl a iha =>
      intro k₂ L₂ h τ₁ τ₂ e
      cases L₂ with
      | refl a' =>
          injection e with _ e₁
          exact iha a' h τ₁ τ₂ e₁
      | var => cases h
      | const => cases e
      | head => cases e
      | app => cases e
      | pi => cases h
      | sigma => cases h
      | id => cases h
      | lam => cases h
      | pair => cases h
      | fst => cases h
      | snd => cases h
  | pi => intro k₂ L₂ h; cases L₂ <;> cases h
  | sigma => intro k₂ L₂ h; cases L₂ <;> cases h
  | id => intro k₂ L₂ h; cases L₂ <;> cases h
  | lam => intro k₂ L₂ h; cases L₂ <;> cases h
  | pair => intro k₂ L₂ h; cases L₂ <;> cases h
  | fst => intro k₂ L₂ h; cases L₂ <;> cases h
  | snd => intro k₂ L₂ h; cases L₂ <;> cases h

/-- **Apartness survives instantiating the second term**: a position that witnesses
it has no variable in the second term. -/
theorem Apart.subst_right {m k₁ : Nat} (L₁ : Tm Head k₁) : ∀ {k₂ : Nat} (L₂ : Tm Head k₂)
    (τ : Sub Head k₂ m), Apart L₁ L₂ = true → Apart L₁ (Presentation.subst τ L₂) = true := by
  induction L₁ with
  | var i => intro k₂ L₂ τ h; cases L₂ <;> cases h
  | const c =>
      intro k₂ L₂ τ h
      cases L₂ with
      | var => cases h
      | pi => cases h
      | sigma => cases h
      | id => cases h
      | lam => cases h
      | pair => cases h
      | fst => cases h
      | snd => cases h
      | _ => exact h
  | head h₀ =>
      intro k₂ L₂ τ h
      cases L₂ with
      | var => cases h
      | pi => cases h
      | sigma => cases h
      | id => cases h
      | lam => cases h
      | pair => cases h
      | fst => cases h
      | snd => cases h
      | _ => exact h
  | app f a ihf iha =>
      intro k₂ L₂ τ h
      cases L₂ with
      | app f' a' =>
          refine Apart.app_iff.2 ?_
          rcases Apart.app_iff.1 h with hf | ha
          · exact .inl (ihf f' τ hf)
          · exact .inr (iha a' τ ha)
      | var => cases h
      | pi => cases h
      | sigma => cases h
      | id => cases h
      | lam => cases h
      | pair => cases h
      | fst => cases h
      | snd => cases h
      | _ => exact h
  | refl a iha =>
      intro k₂ L₂ τ h
      cases L₂ with
      | refl a' => exact iha a' τ h
      | var => cases h
      | pi => cases h
      | sigma => cases h
      | id => cases h
      | lam => cases h
      | pair => cases h
      | fst => cases h
      | snd => cases h
      | _ => exact h
  | pi => intro k₂ L₂ τ h; cases L₂ <;> cases h
  | sigma => intro k₂ L₂ τ h; cases L₂ <;> cases h
  | id => intro k₂ L₂ τ h; cases L₂ <;> cases h
  | lam => intro k₂ L₂ τ h; cases L₂ <;> cases h
  | pair => intro k₂ L₂ τ h; cases L₂ <;> cases h
  | fst => intro k₂ L₂ τ h; cases L₂ <;> cases h
  | snd => intro k₂ L₂ τ h; cases L₂ <;> cases h

/-- Whether the terms of a list are pairwise apart, each against those after it. -/
def AllApart : List (Σ k : Nat, Tm Head k) → Bool
  | [] => true
  | x :: xs => xs.all (fun y => Apart x.2 y.2) && AllApart xs

/-- Two terms of a pairwise apart list are one term, or apart. -/
theorem AllApart.eq_or_apart : ∀ {l : List (Σ k : Nat, Tm Head k)}, AllApart l = true →
    ∀ {x y : Σ k : Nat, Tm Head k}, x ∈ l → y ∈ l →
      x = y ∨ Apart x.2 y.2 = true ∨ Apart y.2 x.2 = true
  | [], _, _, _, hx, _ => absurd hx List.not_mem_nil
  | z :: zs, h, x, y, hx, hy => by
      rw [AllApart, Bool.and_eq_true, List.all_eq_true] at h
      rcases List.mem_cons.1 hx with ex | hx'
      · rcases List.mem_cons.1 hy with ey | hy'
        · exact .inl (ex.trans ey.symm)
        · subst ex
          exact .inr (.inl (h.1 _ hy'))
      · rcases List.mem_cons.1 hy with ey | hy'
        · subst ey
          exact .inr (.inr (h.1 _ hx'))
        · exact AllApart.eq_or_apart h.2 hx' hy'

end Apart

/-! ## Metavariables that occur -/

/-- Whether every metavariable occurs in a term, by evaluation. -/
def coversAll {k : Nat} (L : Tm Head k) : Bool :=
  (List.finRange k).all fun i => decide (variableMultiplicity i L ≠ 0)

theorem coversAll_spec {k : Nat} {L : Tm Head k} (h : coversAll L = true) (i : Fin k) :
    variableMultiplicity i L ≠ 0 :=
  of_decide_eq_true (List.all_eq_true.1 h i (List.mem_finRange i))

namespace DeclaredComputation

/-- A schema of a declared computation has one of its listed left sides. -/
theorem mem_leftSides (c : DeclaredComputation Head) {k : Nat} {L R : Tm Head k}
    (rule : c.schemas L R) : (⟨k, L⟩ : Σ k : Nat, Tm Head k) ∈ c.leftSides := by
  cases c with
  | definition f Θ rhs =>
      cases rule
      exact List.mem_singleton_self _
  | eliminator J =>
      cases rule
      exact List.mem_singleton_self _
  | iota rec ctors =>
      obtain ⟨i, k', fields, hi, rule⟩ := rule
      cases rule
      exact List.mem_map.mpr ⟨(k', fields), List.mem_of_getElem? hi, rfl⟩
  | recursion f ctors e s d body =>
      obtain ⟨k', fields, mem, rule⟩ := rule
      cases rule
      exact List.mem_map.mpr ⟨(k', fields), mem, rfl⟩

/-- Whether every metavariable occurs in each left side of a declared computation,
by evaluation. -/
def checkCovers (c : DeclaredComputation Head) : Bool :=
  c.leftSides.all fun L => coversAll L.2

theorem covers_of_checkCovers (c : DeclaredComputation Head) (h : c.checkCovers = true)
    {k : Nat} {L R : Tm Head k} (rule : c.schemas L R) (i : Fin k) :
    variableMultiplicity i L ≠ 0 :=
  coversAll_spec (List.all_eq_true.1 h _ (c.mem_leftSides rule)) i

end DeclaredComputation

/-! ## One annotated instance fixes the substitution -/

/-- Two substitutions giving one instance of the annotation of a first-order term
agree at every variable of the term. -/
theorem subst_annotateWith_agree {k n : Nat} {L : Tm Head k} (fo : firstOrder L = true)
    {σ σ' : CSub Head k n}
    (e : (CTm.annotateWith CTm.unknown L).subst σ = (CTm.annotateWith CTm.unknown L).subst σ') :
    ∀ i, variableMultiplicity i L ≠ 0 → σ i = σ' i := by
  induction L with
  | var j =>
      intro i hi
      have hj : j = i := by
        cases h : decide (j = i) with
        | true => exact of_decide_eq_true h
        | false =>
            have hn : ¬ j = i := of_decide_eq_false h
            exact absurd (show (if j = i then 1 else 0) = 0 from if_neg hn) hi
      subst hj
      exact e
  | const => intro i hi; exact absurd rfl hi
  | head => intro i hi; exact absurd rfl hi
  | pi => cases fo
  | sigma => cases fo
  | id => cases fo
  | lam => cases fo
  | pair => cases fo
  | fst => cases fo
  | snd => cases fo
  | app f a ihf iha =>
      rw [firstOrder, Bool.and_eq_true] at fo
      injection e with _ e₁ e₂
      intro i hi
      rw [variableMultiplicity_app] at hi
      cases hf : variableMultiplicity i f with
      | zero =>
          rw [hf, Nat.zero_add] at hi
          exact iha fo.2 e₂ i hi
      | succ m => exact ihf fo.1 e₁ i (by rw [hf]; exact Nat.succ_ne_zero m)
  | refl a ih =>
      injection e with _ e₁
      exact ih fo e₁

/-! ## Schemas determined by their left sides -/

/-- Schemas determined by their left sides: every metavariable occurs in its
schema's left side, and two left sides with a common instance are one left
side. -/
structure SchemaDeterminate (S : SchemaFamily Head) : Prop where
  covers : ∀ {k : Nat} {L R : Tm Head k}, S L R → ∀ i, variableMultiplicity i L ≠ 0
  leftUnique : ∀ {k₁ k₂ n : Nat} {L₁ R₁ : Tm Head k₁} {L₂ R₂ : Tm Head k₂},
    S L₁ R₁ → S L₂ R₂ → ∀ (τ₁ : Sub Head k₁ n) (τ₂ : Sub Head k₂ n),
      Presentation.subst τ₁ L₁ = Presentation.subst τ₂ L₂ →
        (⟨k₁, L₁⟩ : Σ k : Nat, Tm Head k) = ⟨k₂, L₂⟩

/-- An annotated root step, as an instance of an elaborated schema. -/
theorem CSchemaStep.exists_instance {S : CSchemaFamily Head} {n : Nat} {t u : CTm Head n}
    (step : CSchemaStep S t u) :
    ∃ (k : Nat) (left right : CTm Head k) (σ : CSub Head k n),
      S left right ∧ t = left.subst σ ∧ u = right.subst σ := by
  cases step with
  | instantiate rule σ => exact ⟨_, _, _, σ, rule, rfl, rfl⟩

variable {R : Rules Head}

/-- **Determinism of the annotated root steps of a presented rule package**: when
the rule package's root steps are deterministic and its schemas are first-order and
determined by their left sides, an annotated term has at most one annotated root
reduct. -/
theorem ChurchRules.ofSchemas_deterministic (S : SchemaFamily Head)
    (present : Presents R.computation S) (fo : FirstOrderFamily S) (det : SchemaDeterminate S)
    (rootDet : ∀ {n : Nat} {t u u' : Tm Head n}, R.computation.step t u →
      R.computation.step t u' → u = u')
    {n : Nat} {t u u' : CTm Head n}
    (first : (ChurchRules.ofSchemas R S present).computation.step t u)
    (second : (ChurchRules.ofSchemas R S present).computation.step t u') : u = u' := by
  obtain ⟨k₁, left₁, right₁, σ₁, ⟨L₁, R₁, hS₁, rfl, rfl⟩, rfl, rfl⟩ :=
    CSchemaStep.exists_instance ((ChurchRules.ofSchemas_step_iff S present).1 first)
  obtain ⟨k₂, left₂, right₂, σ₂, ⟨L₂, R₂, hS₂, rfl, rfl⟩, e, rfl⟩ :=
    CSchemaStep.exists_instance ((ChurchRules.ofSchemas_step_iff S present).1 second)
  rw [elabLeft_firstOrder _ (fo hS₁).1, elabLeft_firstOrder _ (fo hS₂).1] at e
  have eErase := congrArg CTm.erase e
  rw [CTm.erase_subst, CTm.erase_subst, CTm.erase_annotateWith, CTm.erase_annotateWith] at eErase
  have same := det.leftUnique hS₁ hS₂ _ _ eErase
  cases same
  have hR : R₁ = R₂ := by
    have s₁ := present.2 (SchemaStep.instantiate hS₁ ids)
    have s₂ := present.2 (SchemaStep.instantiate hS₂ ids)
    rw [subst_ids, subst_ids] at s₁ s₂
    exact rootDet s₁ s₂
  subst hR
  have agree := subst_annotateWith_agree (fo hS₁).1 e
  exact CTm.subst_ext (fun i => agree i (det.covers hS₁ i)) _

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
