import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PartialApplications

/-!
# Definitions by structural recursion

A constant

`f : Π (x₀ : E₀) ⋯ (x_{s-1} : E_{s-1}) (t : T) (y₁ : E_{s+1}) ⋯ (y_d : E_{s+d}). C`

defined by one equation for each constructor `k` of a simple inductive type `T`,

`f x₀ ⋯ x_{s-1} (k v₁ ⋯ vₐ) y₁ ⋯ y_d ⟶ rhs_k`,

computes on its argument at position `s`. Its recursive calls apply `f` to the
first `s` arguments and to a recursive field `v`: the partial application
`f x₀ ⋯ x_{s-1} v`, a function of the later arguments. The declaration presents
each right-hand side with these calls abstracted: a term of the equation's
context extended by one hypothesis for each recursive field, typed in the rule
package before `f`. The right-hand side is this term with the recursive calls
substituted for the hypotheses.

Such a constant is semantic. The proof inducts on the reducible equality of the
two scrutinees, in every world:

- a scrutinee reduces to its weak-head normal form, and the application with
  it;
- at a constructor, the application computes to the right-hand side. The
  recursive calls are reducible at their types, by induction and the lemma on
  partial applications, so the right-hand side is valid by the fundamental
  lemma for the earlier package;
- at a neutral scrutinee, the application is stuck and convertible.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Lists -/

theorem getD_of_lt {α : Type} {l : List α} {n : Nat} (d : α) (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem getD_map_rename {n m : Nat} (ρ : Ren n m) :
    ∀ (as : List (Tm Head n)) (l : Nat),
      (as.map (Presentation.rename ρ)).getD l defaultTm =
        Presentation.rename ρ (as.getD l defaultTm)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: as, l + 1 => getD_map_rename ρ as l

/-- The positions of the recursive fields are positions of recursive fields. -/
theorem recPositions_spec :
    ∀ (fields : List (Field Head)) (j : Nat) (hj : j < (recPositions fields).length),
      (recPositions fields)[j] < fields.length ∧
        fields.getD (recPositions fields)[j] .recursive = .recursive
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | .recursive :: _, 0, _ => ⟨by simp [recPositions], rfl⟩
  | .recursive :: fields, j + 1, hj => by
      have hj' : j < (recPositions fields).length := by simpa [recPositions] using hj
      obtain ⟨h₁, h₂⟩ := recPositions_spec fields j hj'
      have e₁ : (recPositions (.recursive :: fields))[j + 1] = (recPositions fields)[j] + 1 := by
        simp [recPositions]
      rw [e₁]
      exact ⟨by simp only [List.length_cons]; omega, h₂⟩
  | .closed F :: fields, j, hj => by
      have hj' : j < (recPositions fields).length := by simpa [recPositions] using hj
      obtain ⟨h₁, h₂⟩ := recPositions_spec fields j hj'
      have e₁ : (recPositions (.closed F :: fields))[j] = (recPositions fields)[j] + 1 := by
        simp [recPositions]
      rw [e₁]
      exact ⟨by simp only [List.length_cons]; omega, h₂⟩

/-! ## Arguments around the scrutinee -/

theorem scrutOf_eq_dropSub {m s : Nat} :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m), scrutOf s d σ = dropSub (s + 1) d σ 0
  | 0, _ => rfl
  | d + 1, σ => scrutOf_eq_dropSub d (tailSub σ)

theorem suffixArgs_length {m s : Nat} :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m), (suffixArgs s d σ).length = d
  | 0, _ => rfl
  | d + 1, σ => by simp [suffixArgs, suffixArgs_length d (tailSub σ)]

/-- A full application to the telescope, split around the scrutinee. -/
theorem applyClosed_split (e : (i : Nat) → Tm Head i) {m s : Nat} (d : Nat)
    (σ : Sub Head (s + 1 + d) m) (g : Tm Head m) :
    applyClosed (ofEntries e (s + 1 + d)) σ g =
      appSpine g (telescopeArgs (ofEntries e s) (prefixSub s d σ) ++
        scrutOf s d σ :: suffixArgs s d σ) := by
  rw [applyClosed_eq_appSpine, telescopeArgs_split]
  simp only [List.append_assoc, List.singleton_append]

/-- The recursive call on the field at position `l`, under the match: `f`
applied to the first arguments and the field's argument. -/
theorem subst_recCall (f : DeclName) (e : (i : Nat) → Tm Head i) {m s a d l : Nat}
    (as : List (Tm Head m)) (σ : Sub Head (s + 1 + d) m) (hl : l < a) :
    Presentation.subst (matchSub s a as d σ) (recCall f e s a d l) =
      applyClosed (ofEntries e (s + 1)) (consSub (as.getD l defaultTm) (prefixSub s d σ))
        (.const f) := by
  rw [recCall, applyClosed_subst]
  exact congrArg (fun τ => applyClosed (ofEntries e (s + 1)) τ (.const f))
    (callSub_matchSub as d σ l hl)

/-- The type of the recursive call on the field at position `l`, under the
match. -/
theorem subst_recCallType (e : (i : Nat) → Tm Head i) {m s a d l : Nat}
    (as : List (Tm Head m)) (σ : Sub Head (s + 1 + d) m) (C : Tm Head (s + 1 + d))
    (hl : l < a) :
    Presentation.subst (matchSub s a as d σ) (recCallType e s a d l C) =
      Presentation.subst (consSub (as.getD l defaultTm) (prefixSub s d σ))
        (piRange e (s + 1) d C) := by
  rw [recCallType, subst_comp]
  exact congrArg (fun τ => Presentation.subst τ (piRange e (s + 1) d C))
    (callSub_matchSub as d σ l hl)

/-- Substituting after the substitution of the hypotheses by the recursive
calls. -/
theorem subst_hypSub (f : DeclName) (e : (i : Nat) → Tm Head i) {m s d : Nat}
    (fields : List (Field Head)) (τ : Sub Head (s + fields.length + d) m)
    (b : Tm Head (s + fields.length + d + (recPositions fields).length)) :
    Presentation.subst τ (Presentation.subst (hypSub f e s d fields) b) =
      Presentation.subst (extendSub τ (fun j => Presentation.subst τ
        (recCall f e s fields.length d ((recPositions fields).getD j 0)))
        (recPositions fields).length) b := by
  rw [subst_comp]
  exact congrArg (fun τ' => Presentation.subst τ' b)
    (subst_extendSub τ _ (recPositions fields).length)

/-! ## Congruence of full applications -/

/-- Applying a function to the telescope at pointwise equal substitutions gives
equal applications. -/
theorem Equal.telescope_apply {R : Rules Head} {n m : Nat} {Θ : Ctx Head n} {Δ : Ctx Head m}
    {σ τ : Sub Head n m} {g : Tm Head m} {X : Tm Head n}
    (equal : ∀ i, Equal R Δ (σ i) (τ i) (Presentation.subst σ (Ctx.lookup Θ i)))
    (function : Typed R Δ g (liftClosed (closeType Θ X))) :
    Equal R Δ (applyClosed Θ σ g) (applyClosed Θ τ g) (Presentation.subst σ X) := by
  induction Θ with
  | nil =>
      show Equal R Δ g g (Presentation.subst σ X)
      rw [subst_closed]
      exact .refl function
  | @snoc n Θ A ih =>
      have equal' : ∀ i, Equal R Δ (tailSub σ i) (tailSub τ i)
          (Presentation.subst (tailSub σ) (Ctx.lookup Θ i)) := by
        intro i
        have h := equal i.succ
        rwa [Ctx.lookup_snoc_succ, subst_rename_wk] at h
      have earlier := ih (σ := tailSub σ) (τ := tailSub τ) (X := .pi A X) equal' function
      have argument := equal 0
      rw [Ctx.lookup_snoc_zero, subst_rename_wk] at argument
      have application := Derivable.appCong earlier argument
      rw [inst0_subst_liftSub, consSub_tailSub] at application
      exact application

/-- Replacing the scrutinee by a term equal to it gives pointwise equal
arguments. -/
theorem Equal.replaceScrut_pointwise (e : (i : Nat) → Tm Head i) {R : Rules Head} {m s : Nat}
    {Δ : Ctx Head m} {x : Tm Head m} :
    ∀ (d : Nat) {σ : Sub Head (s + 1 + d) m}, SubstMor R (ofEntries e (s + 1 + d)) Δ σ →
      Equal R Δ (scrutOf s d σ) x (Presentation.subst (prefixSub s d σ) (e s)) →
      ∀ i, Equal R Δ (σ i) (replaceScrut s x d σ i)
        (Presentation.subst σ (Ctx.lookup (ofEntries e (s + 1 + d)) i))
  | 0, σ, typed, equal, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · show Equal R Δ (σ 0) x
          (Presentation.subst σ (Ctx.lookup (.snoc (ofEntries e s) (e s)) 0))
        rw [Ctx.lookup_snoc_zero, subst_rename_wk]
        exact equal
      · exact .refl (typed j.succ)
  | d + 1, σ, typed, equal, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .refl (typed 0)
      · have h := Equal.replaceScrut_pointwise e d (σ := tailSub σ) (SubstMor.tail typed) equal j
        show Equal R Δ (σ j.succ) (replaceScrut s x d (tailSub σ) j)
          (Presentation.subst σ
            (Ctx.lookup (.snoc (ofEntries e (s + 1 + d)) (e (s + 1 + d))) j.succ))
        rw [Ctx.lookup_snoc_succ, subst_rename_wk]
        exact h

/-! ## Valid substitutions -/

section Substitutions

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- Every context formed in a rule package inside the model's, whose constants
are semantic, is valid. -/
theorem CtxFormed.valid_sub {R' : Rules Head} (sub : RulesSub R' S.R)
    (constants' : SemanticConstantsOf S R') {n : Nat} {Γ : Ctx Head n}
    (formed : CtxFormed R' Γ) : ValidCtx S Γ := by
  induction formed with
  | nil => trivial
  | snoc _ type ih =>
      obtain ⟨u, hu, typing⟩ := type
      exact ⟨ih, (Derivable.valid_sub laws sub constants' typing ih).validTy laws
        (sub.isUniverse hu)⟩

/-- Reducible equality at the canonical pack of a reducible type is kept by
the worlds of the model. -/
theorem Reducible.packOf_weaken_eqTm {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {A : Tm Head n} {ρ : Ren n m} (reducible : Reducible S Γ A (packOf S Γ A))
    (w : World S Γ Δ ρ) {a b : Tm Head n} (equal : (packOf S Γ A).eqTm a b) :
    (packOf S Δ (Presentation.rename ρ A)).eqTm (Presentation.rename ρ a)
      (Presentation.rename ρ b) := by
  obtain ⟨P', reducible', weakened⟩ := reducible.weaken laws w
  rw [← reducible'.eq_packOf laws]
  exact weakened.eqTm equal

/-- Reducible equality of substitutions of a valid context is symmetric. -/
theorem EqSubst.symm {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} (validΓ : ValidCtx S Γ)
    {σ σ' : Sub Head n m} (vσ : ValidSubst S Γ Δ σ) (vσ' : ValidSubst S Γ Δ σ')
    (equal : EqSubst S Γ Δ σ σ') : EqSubst S Γ Δ σ' σ := by
  induction Γ with
  | nil => trivial
  | snoc Γ A ih =>
      obtain ⟨vt, P, rP, _⟩ := vσ
      obtain ⟨vt', Q, rQ, _⟩ := vσ'
      obtain ⟨et, P₁, rP₁, h⟩ := equal
      have same₁ := rP₁.unique laws rP
      have same := validΓ.2.pack_eq laws vt vt' et rP rQ
      subst same₁ same
      exact ⟨ih validΓ.1 vt vt' et, _, rQ, rQ.eqTm_symm laws h⟩

/-- Reducible equality of substitutions of a valid context is transitive. -/
theorem EqSubst.trans {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} (validΓ : ValidCtx S Γ)
    {σ₁ σ₂ σ₃ : Sub Head n m} (v₁ : ValidSubst S Γ Δ σ₁) (v₂ : ValidSubst S Γ Δ σ₂)
    (e₁₂ : EqSubst S Γ Δ σ₁ σ₂) (e₂₃ : EqSubst S Γ Δ σ₂ σ₃) : EqSubst S Γ Δ σ₁ σ₃ := by
  induction Γ with
  | nil => trivial
  | snoc Γ A ih =>
      obtain ⟨vt₁, P, rP, _⟩ := v₁
      obtain ⟨vt₂, Q, rQ, _⟩ := v₂
      obtain ⟨et₁₂, P₁, rP₁, h₁⟩ := e₁₂
      obtain ⟨et₂₃, Q₁, rQ₁, h₂⟩ := e₂₃
      have s₁ := rP₁.unique laws rP
      have s₂ := rQ₁.unique laws rQ
      have same := validΓ.2.pack_eq laws vt₁ vt₂ et₁₂ rP rQ
      subst s₁ s₂ same
      exact ⟨ih validΓ.1 vt₁ vt₂ et₁₂ et₂₃, _, rP₁, rP₁.eqTm_trans laws h₁ h₂⟩

/-- Substitutions extended by reducible arguments for fields, whose types are
closed. -/
theorem ValidSubst.fields {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} (T : DeclName)
    (fields : List (Field Head)) {as as' : List (Tm Head m)}
    (facts : ∀ l, l < fields.length →
      Reducible S Δ (liftClosed ((fields.getD l .recursive).type T))
          (packOf S Δ (liftClosed ((fields.getD l .recursive).type T))) ∧
        (packOf S Δ (liftClosed ((fields.getD l .recursive).type T))).eqTm
          (as.getD l defaultTm) (as'.getD l defaultTm))
    {ρ ρ' : Sub Head n m} (valid : ValidSubst S Γ Δ ρ) (valid' : ValidSubst S Γ Δ ρ')
    (equal : EqSubst S Γ Δ ρ ρ') :
    ∀ (b : Nat), b ≤ fields.length →
      ValidSubst S (extendEntries Γ (fun l => liftClosed ((fields.getD l .recursive).type T)) b)
          Δ (extendSub ρ (fun l => as.getD l defaultTm) b) ∧
        ValidSubst S
          (extendEntries Γ (fun l => liftClosed ((fields.getD l .recursive).type T)) b)
          Δ (extendSub ρ' (fun l => as'.getD l defaultTm) b) ∧
        EqSubst S (extendEntries Γ (fun l => liftClosed ((fields.getD l .recursive).type T)) b)
          Δ (extendSub ρ (fun l => as.getD l defaultTm) b)
          (extendSub ρ' (fun l => as'.getD l defaultTm) b)
  | 0, _ => ⟨valid, valid', equal⟩
  | b + 1, hb => by
      obtain ⟨i₁, i₂, i₃⟩ := ValidSubst.fields T fields facts valid valid' equal b (by omega)
      obtain ⟨r, h⟩ := facts b (by omega)
      obtain ⟨ha, ha'⟩ := r.eqTm_redTm laws h
      have r₁ : ∀ τ : Sub Head (n + b) m, Reducible S Δ
          (Presentation.subst τ (liftClosed ((fields.getD b .recursive).type T)))
          (packOf S Δ (liftClosed ((fields.getD b .recursive).type T))) := by
        intro τ
        rw [subst_liftClosed]
        exact r
      exact ⟨⟨i₁, _, r₁ _, ha⟩, ⟨i₂, _, r₁ _, ha'⟩, ⟨i₃, _, r₁ _, h⟩⟩

omit laws in
/-- Substitutions extended by values for entries weakened past the earlier
extensions. -/
theorem ValidSubst.hyps {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} (X : Nat → Tm Head n)
    {τ τ' : Sub Head n m} {vals vals' : Nat → Tm Head m}
    (valid : ValidSubst S Γ Δ τ) (valid' : ValidSubst S Γ Δ τ') (equal : EqSubst S Γ Δ τ τ') :
    ∀ (b : Nat),
      (∀ j, j < b → ∃ P, Reducible S Δ (Presentation.subst τ (X j)) P ∧ P.redTm (vals j) ∧
        P.eqTm (vals j) (vals' j)) →
      (∀ j, j < b → ∃ P, Reducible S Δ (Presentation.subst τ' (X j)) P ∧ P.redTm (vals' j)) →
      ValidSubst S (extendEntries Γ (fun j => Presentation.rename (wkN j) (X j)) b) Δ
          (extendSub τ vals b) ∧
        ValidSubst S (extendEntries Γ (fun j => Presentation.rename (wkN j) (X j)) b) Δ
          (extendSub τ' vals' b) ∧
        EqSubst S (extendEntries Γ (fun j => Presentation.rename (wkN j) (X j)) b) Δ
          (extendSub τ vals b) (extendSub τ' vals' b)
  | 0, _, _ => ⟨valid, valid', equal⟩
  | b + 1, hyps, hyps' => by
      obtain ⟨i₁, i₂, i₃⟩ := ValidSubst.hyps X valid valid' equal b
        (fun j hj => hyps j (by omega)) (fun j hj => hyps' j (by omega))
      obtain ⟨P, r, h, hh⟩ := hyps b (by omega)
      obtain ⟨P', r', h'⟩ := hyps' b (by omega)
      have e₁ : Presentation.subst (extendSub τ vals b) (Presentation.rename (wkN b) (X b)) =
          Presentation.subst τ (X b) := subst_extendSub_wkN τ vals b (X b)
      have e₂ : Presentation.subst (extendSub τ' vals' b) (Presentation.rename (wkN b) (X b)) =
          Presentation.subst τ' (X b) := subst_extendSub_wkN τ' vals' b (X b)
      have r₁ : Reducible S Δ
          (Presentation.subst (extendSub τ vals b) (Presentation.rename (wkN b) (X b))) P := by
        rw [e₁]; exact r
      have r₂ : Reducible S Δ
          (Presentation.subst (extendSub τ' vals' b) (Presentation.rename (wkN b) (X b))) P' := by
        rw [e₂]; exact r'
      exact ⟨⟨i₁, P, r₁, h⟩, ⟨i₂, P', r₂, h'⟩, ⟨i₃, P, r₁, hh⟩⟩

end Substitutions

/-! ## Substitutions of the telescope -/

section Telescope

variable (e : (i : Nat) → Tm Head i) {s m : Nat} {Δ : Ctx Head m}

theorem ValidSubst.prefixSub : ∀ (d : Nat) {σ : Sub Head (s + 1 + d) m},
    ValidSubst S (ofEntries e (s + 1 + d)) Δ σ → ValidSubst S (ofEntries e s) Δ (prefixSub s d σ)
  | 0, _, valid => valid.1
  | d + 1, _, valid => ValidSubst.prefixSub d valid.1

theorem EqSubst.prefixSub : ∀ (d : Nat) {σ σ' : Sub Head (s + 1 + d) m},
    EqSubst S (ofEntries e (s + 1 + d)) Δ σ σ' →
      EqSubst S (ofEntries e s) Δ (prefixSub s d σ) (prefixSub s d σ')
  | 0, _, _, equal => equal.1
  | d + 1, _, _, equal => EqSubst.prefixSub d equal.1

/-- The match of reducible constructor forms is valid for the pattern
context. -/
theorem ValidSubst.pattern (laws : S.E.Laws S.R S.roles) {T k : DeclName}
    (fields : List (Field Head)) {as as' : List (Tm Head m)}
    (facts : ∀ l, l < fields.length →
      Reducible S Δ (liftClosed ((fields.getD l .recursive).type T))
          (packOf S Δ (liftClosed ((fields.getD l .recursive).type T))) ∧
        (packOf S Δ (liftClosed ((fields.getD l .recursive).type T))).eqTm
          (as.getD l defaultTm) (as'.getD l defaultTm))
    (length : as.length = fields.length) (length' : as'.length = fields.length) :
    ∀ (d : Nat) {τ τ' : Sub Head (s + 1 + d) m},
      ValidSubst S (ofEntries e (s + 1 + d)) Δ τ → ValidSubst S (ofEntries e (s + 1 + d)) Δ τ' →
      EqSubst S (ofEntries e (s + 1 + d)) Δ τ τ' →
      scrutOf s d τ = appSpine (.const k) as → scrutOf s d τ' = appSpine (.const k) as' →
      ValidSubst S (patternCtx T k e s d fields) Δ (matchSub s fields.length as d τ) ∧
        ValidSubst S (patternCtx T k e s d fields) Δ (matchSub s fields.length as' d τ') ∧
        EqSubst S (patternCtx T k e s d fields) Δ (matchSub s fields.length as d τ)
          (matchSub s fields.length as' d τ')
  | 0, _, _, valid, valid', equal, _, _ =>
      ValidSubst.fields laws T fields facts (ValidSubst.prefixSub e 0 valid)
        (ValidSubst.prefixSub e 0 valid') (EqSubst.prefixSub e 0 equal) fields.length
        (Nat.le_refl _)
  | d + 1, τ, τ', valid, valid', equal, h, h' => by
      obtain ⟨vt, Q, rQ, hQ⟩ : ValidSubst S (ofEntries e (s + 1 + d)) Δ (tailSub τ) ∧
          ∃ Q, Reducible S Δ (Presentation.subst (tailSub τ) (e (s + 1 + d))) Q ∧
            Q.redTm (τ 0) := valid
      obtain ⟨vt', Q', rQ', hQ'⟩ : ValidSubst S (ofEntries e (s + 1 + d)) Δ (tailSub τ') ∧
          ∃ Q, Reducible S Δ (Presentation.subst (tailSub τ') (e (s + 1 + d))) Q ∧
            Q.redTm (τ' 0) := valid'
      obtain ⟨et, Q₁, rQ₁, hQQ⟩ : EqSubst S (ofEntries e (s + 1 + d)) Δ (tailSub τ) (tailSub τ') ∧
          ∃ Q, Reducible S Δ (Presentation.subst (tailSub τ) (e (s + 1 + d))) Q ∧
            Q.eqTm (τ 0) (τ' 0) := equal
      obtain ⟨i₁, i₂, i₃⟩ := ValidSubst.pattern laws fields facts length length' d vt vt' et h h'
      have entry : ∀ (σ : Sub Head (s + 1 + d) m) (bs : List (Tm Head m)),
          scrutOf s d σ = appSpine (.const k) bs → bs.length = fields.length →
          Presentation.subst (matchSub s fields.length bs d σ)
              (Presentation.subst (liftSubN (patSub s fields.length k) d) (e (s + 1 + d))) =
            Presentation.subst σ (e (s + 1 + d)) := by
        intro σ bs hσ hbs
        rw [subst_comp]
        have key : (fun ι => Presentation.subst (matchSub s fields.length bs d σ)
              (liftSubN (patSub s fields.length k) d ι)) =
            replaceScrut s (appSpine (.const k) bs) d σ :=
          funext fun ι => subst_matchSub_patternSub k bs hbs d σ ι
        rw [key, ← hσ, replaceScrut_self]
      have r₁ : Reducible S Δ (Presentation.subst (matchSub s fields.length as d (tailSub τ))
          (Presentation.subst (liftSubN (patSub s fields.length k) d) (e (s + 1 + d)))) Q := by
        rw [entry _ _ h length]; exact rQ
      have r₂ : Reducible S Δ (Presentation.subst (matchSub s fields.length as' d (tailSub τ'))
          (Presentation.subst (liftSubN (patSub s fields.length k) d) (e (s + 1 + d)))) Q' := by
        rw [entry _ _ h' length']; exact rQ'
      have r₃ : Reducible S Δ (Presentation.subst (matchSub s fields.length as d (tailSub τ))
          (Presentation.subst (liftSubN (patSub s fields.length k) d) (e (s + 1 + d)))) Q₁ := by
        rw [entry _ _ h length]; exact rQ₁
      exact ⟨⟨i₁, Q, r₁, hQ⟩, ⟨i₂, Q', r₂, hQ'⟩, ⟨i₃, Q₁, r₃, hQQ⟩⟩

variable {T : DeclName} (scrutinee : e s = .const T)
include scrutinee

theorem subst_scrutinee {k : Nat} (τ : Sub Head s k) :
    Presentation.subst τ (e s) = (.const T : Tm Head k) := by
  rw [scrutinee]
  rfl

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The scrutinees of reducibly equal substitutions are reducibly equal. -/
theorem EqSubst.scrut : ∀ (d : Nat) {σ σ' : Sub Head (s + 1 + d) m},
    EqSubst S (ofEntries e (s + 1 + d)) Δ σ σ' →
      (packOf S Δ (.const T)).eqTm (scrutOf s d σ) (scrutOf s d σ')
  | 0, σ, σ', equal => by
      obtain ⟨_, P, r, h⟩ : EqSubst S (ofEntries e s) Δ (tailSub σ) (tailSub σ') ∧
          ∃ P, Reducible S Δ (Presentation.subst (tailSub σ) (e s)) P ∧
            P.eqTm (σ 0) (σ' 0) := equal
      rw [subst_scrutinee e scrutinee] at r
      rw [← r.eq_packOf laws]
      exact h
  | d + 1, _, _, equal => EqSubst.scrut d equal.1

/-- Replacing the scrutinee of a valid substitution by a reducibly equal term
gives a valid, reducibly equal substitution. -/
theorem ValidSubst.replaceScrut (rT : Reducible S Δ (.const T) (packOf S Δ (.const T))) :
    ∀ (d : Nat), ValidCtx S (ofEntries e (s + 1 + d)) →
      ∀ {σ : Sub Head (s + 1 + d) m} {x : Tm Head m},
      ValidSubst S (ofEntries e (s + 1 + d)) Δ σ →
      (packOf S Δ (.const T)).eqTm (scrutOf s d σ) x →
      ValidSubst S (ofEntries e (s + 1 + d)) Δ (replaceScrut s x d σ) ∧
        EqSubst S (ofEntries e (s + 1 + d)) Δ σ (replaceScrut s x d σ)
  | 0, _, σ, x, valid, equal => by
      obtain ⟨tail, _, _, _⟩ : ValidSubst S (ofEntries e s) Δ (tailSub σ) ∧
          ∃ P, Reducible S Δ (Presentation.subst (tailSub σ) (e s)) P ∧ P.redTm (σ 0) := valid
      have r' : Reducible S Δ (Presentation.subst (tailSub σ) (e s)) (packOf S Δ (.const T)) := by
        rw [subst_scrutinee e scrutinee]
        exact rT
      have hx := (rT.eqTm_redTm laws equal).2
      exact ⟨⟨tail, _, r', hx⟩, ⟨tail.refl, _, r', equal⟩⟩
  | d + 1, validΘ, σ, x, valid, equal => by
      obtain ⟨tail, Q, rQ, hQ⟩ : ValidSubst S (ofEntries e (s + 1 + d)) Δ (tailSub σ) ∧
          ∃ Q, Reducible S Δ (Presentation.subst (tailSub σ) (e (s + 1 + d))) Q ∧
            Q.redTm (σ 0) := valid
      have validΘ' : ValidCtx S (ofEntries e (s + 1 + d)) ∧
          ValidTy S (ofEntries e (s + 1 + d)) (e (s + 1 + d)) := validΘ
      obtain ⟨v₂, e₂⟩ := ValidSubst.replaceScrut rT d validΘ'.1 tail equal
      obtain ⟨Q', rQ'⟩ := validΘ'.2.red v₂
      have same := validΘ'.2.pack_eq laws tail v₂ e₂ rQ rQ'
      subst same
      exact ⟨⟨v₂, _, rQ', hQ⟩, ⟨e₂, _, rQ, rQ.reflexive.eqTm hQ⟩⟩

end Telescope

/-! ## Arguments of constructor forms -/

/-- Reducibly equal arguments for the fields of a constructor, at the
canonical packs of the field types. -/
theorem IndEqFields.getD_packOf {n : Nat} {Γ : Ctx Head n} {T : DeclName}
    {ctors : List (DeclName × List (Field Head))}
    (hT : packOf S Γ (.const T) = indPack S Γ T ctors fun F => packOf S Γ (liftClosed F)) :
    ∀ {fields : List (Field Head)} {as as' : List (Tm Head n)},
      IndEqFields S Γ T ctors (fun F => packOf S Γ (liftClosed F)) fields as as' →
      ∀ l, l < fields.length →
        (packOf S Γ (liftClosed ((fields.getD l .recursive).type T))).eqTm
          (as.getD l defaultTm) (as'.getD l defaultTm)
  | _, _, _, .nil, _, hl => absurd hl (Nat.not_lt_zero _)
  | _, _, _, .recursive head _, 0, _ => by
      show (packOf S Γ (.const T)).eqTm _ _
      rw [hT]
      exact head
  | _, _, _, .recursive _ tail, l + 1, hl =>
      IndEqFields.getD_packOf hT tail l (Nat.lt_of_succ_lt_succ hl)
  | _, _, _, .closed head _, 0, _ => head
  | _, _, _, .closed _ tail, l + 1, hl =>
      IndEqFields.getD_packOf hT tail l (Nat.lt_of_succ_lt_succ hl)

/-- The field types of a declared simple inductive type are reducible at their
canonical packs. -/
theorem DeclaresInductive.fieldType_reducible {R₀ R₁ R₂ : Rules Head} {T : DeclName} {u : Head}
    {ctors : List (DeclName × List (Field Head))} {rec : DeclName} {v : Head}
    (ind : DeclaresInductive S R₀ R₁ R₂ T u ctors rec v) (laws : S.E.Laws S.R S.roles)
    {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ) {k : DeclName}
    {fields : List (Field Head)} (mem : (k, fields) ∈ ctors) {l : Nat} (hl : l < fields.length) :
    Reducible S Δ (liftClosed ((fields.getD l .recursive).type T))
      (packOf S Δ (liftClosed ((fields.getD l .recursive).type T))) := by
  have hmem : fields.getD l .recursive ∈ fields := by
    rw [getD_of_lt _ hl]
    exact List.getElem_mem hl
  revert hmem
  cases fields.getD l .recursive with
  | recursive =>
      intro _
      exact ind.type_reducible laws formed
  | closed F =>
      intro hmem
      exact (ind.field_logRel laws formed mem hmem).reducible

/-! ## The declaration -/

/-- The rule package declares `f : Π Θ. C`, with `Θ` the telescope of the
entries `e`, by structural recursion on its argument at position `s`, of the
simple inductive type `T` with constructors `ctors`. For each constructor, the
right-hand side is `body k fields` with the recursive calls substituted for the
hypotheses; `body` is typed, in the rule package `R₀` before `f`, in the
equation's context extended by the hypotheses. -/
structure DeclaresRecursion (S : Setting Head L) (R₀ : Rules Head) (f T : DeclName)
    (ctors : List (DeclName × List (Field Head))) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (C : Tm Head (s + 1 + d))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) : Prop where
  role : S.roles f = .computes (s + 1 + d) (.split s .constructor fun _ => .leaf)
  scrutinee : e s = .const T
  declared : S.R.constantType f = some (closeType (ofEntries e (s + 1 + d)) C)
  sub₀ : RulesSub R₀ S.R
  semantic₀ : AllSemantic S R₀
  typed : ∃ w, S.R.isUniverse w ∧
    Typed R₀ .nil (closeType (ofEntries e (s + 1 + d)) C) (.head w)
  formed : ∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ ctors →
    CtxFormed R₀ (hypCtx T k e s d fields C)
  bodyTyped : ∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ ctors →
    Typed R₀ (hypCtx T k e s d fields C) (body k fields)
      (Presentation.rename (wkN (recPositions fields).length)
        (Presentation.subst (patternSub s fields.length d k) C))
  rule : ∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ ctors →
    ∀ {m : Nat} (σ : Sub Head (s + 1 + d) m) (as : List (Tm Head m)),
      as.length = fields.length →
      S.R.computation.step
        (applyClosed (ofEntries e (s + 1 + d)) (replaceScrut s (appSpine (.const k) as) d σ)
          (.const f))
        (Presentation.subst (matchSub s fields.length as d σ)
          (Presentation.subst (hypSub f e s d fields) (body k fields)))

/-- The full applications of `f` at validly equal arguments whose scrutinees
are `t` and `t'`, renamed into a world, are reducibly equal. -/
def RecursionClaim (S : Setting Head L) (f : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (C : Tm Head (s + 1 + d)) {m : Nat} (Δ : Ctx Head m) (t t' : Tm Head m) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃Δ' : Ctx Head k⦄ ⦃ρ : Ren m k⦄, World S Δ Δ' ρ →
    ∀ {σ σ' : Sub Head (s + 1 + d) k},
      ValidSubst S (ofEntries e (s + 1 + d)) Δ' σ →
      ValidSubst S (ofEntries e (s + 1 + d)) Δ' σ' →
      EqSubst S (ofEntries e (s + 1 + d)) Δ' σ σ' →
      scrutOf s d σ = Presentation.rename ρ t → scrutOf s d σ' = Presentation.rename ρ t' →
      ∀ {P : Pack Head k}, Reducible S Δ' (Presentation.subst σ C) P →
        P.eqTm (applyClosed (ofEntries e (s + 1 + d)) σ (.const f))
          (applyClosed (ofEntries e (s + 1 + d)) σ' (.const f))

section Semantics

variable {R₀ : Rules Head} {f T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {e : (i : Nat) → Tm Head i} {s d : Nat} {C : Tm Head (s + 1 + d)}
  {body : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (s + fields.length + d + (recPositions fields).length)}
  (decl : DeclaresRecursion S R₀ f T ctors e s d C body)
include decl

/-- The defined constant at its declared type, in every context. -/
theorem DeclaresRecursion.typing {n : Nat} {Γ : Ctx Head n} :
    Typed S.R Γ (.const f) (liftClosed (closeType (ofEntries e (s + 1 + d)) C)) := by
  obtain ⟨w, hw, typed⟩ := decl.typed
  exact .const decl.declared (Derivable.mono decl.sub₀ typed) hw

/-- A full application of the defined constant at a neutral scrutinee is
neutral. -/
theorem DeclaresRecursion.neutral {m : Nat} {σ : Sub Head (s + 1 + d) m}
    (neutral : Neutral S.roles (scrutOf s d σ)) :
    Neutral S.roles (applyClosed (ofEntries e (s + 1 + d)) σ (.const f)) := by
  rw [applyClosed_split]
  have role : S.roles f = .computes (s + 1 + d)
      (.split (telescopeArgs (ofEntries e s) (prefixSub s d σ)).length .constructor fun _ => .leaf) := by
    rw [telescopeArgs_length]
    exact decl.role
  exact .stuck_single role (by rw [telescopeArgs_length, suffixArgs_length]) neutral

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- The declared type is valid. -/
theorem DeclaresRecursion.validType :
    ValidTy S .nil (closeType (ofEntries e (s + 1 + d)) C) := by
  obtain ⟨w, hw, typed⟩ := decl.typed
  exact (Derivable.valid_sub laws decl.sub₀ (AllSemantic.semanticConstantsOf decl.semantic₀)
    typed trivial).validTy laws hw

/-- The abstracted right-hand sides are valid. -/
theorem DeclaresRecursion.body_valid {k : DeclName} {fields : List (Field Head)}
    (mem : (k, fields) ∈ ctors) :
    ValidTm S (hypCtx T k e s d fields C) (body k fields)
      (Presentation.rename (wkN (recPositions fields).length)
        (Presentation.subst (patternSub s fields.length d k) C)) :=
  Derivable.valid_sub laws decl.sub₀ (AllSemantic.semanticConstantsOf decl.semantic₀)
    (decl.bodyTyped mem)
    (CtxFormed.valid_sub laws decl.sub₀ (AllSemantic.semanticConstantsOf decl.semantic₀)
      (decl.formed mem))

/-- Reducing the scrutinee of a full application. -/
theorem DeclaresRecursion.scrutinee_red {m : Nat} {Δ : Ctx Head m}
    {σ : Sub Head (s + 1 + d) m} (vσ : ValidSubst S (ofEntries e (s + 1 + d)) Δ σ)
    {x : Tm Head m} (red : RedTm S.R S.roles Δ (scrutOf s d σ) x (.const T))
    (vσ₂ : ValidSubst S (ofEntries e (s + 1 + d)) Δ (replaceScrut s x d σ))
    (e₂ : EqSubst S (ofEntries e (s + 1 + d)) Δ σ (replaceScrut s x d σ)) :
    RedTm S.R S.roles Δ (applyClosed (ofEntries e (s + 1 + d)) σ (.const f))
      (applyClosed (ofEntries e (s + 1 + d)) (replaceScrut s x d σ) (.const f))
      (Presentation.subst σ C) := by
  obtain ⟨_, validC⟩ := ValidTy.telescope laws (ofEntries e (s + 1 + d)) (decl.validType laws)
  have typed := vσ.substMor laws
  refine ⟨?_, Typed.telescope_apply typed decl.typing,
    Typed.convType (Typed.telescope_apply (vσ₂.substMor laws) decl.typing)
      (validC.typeEq_at laws vσ vσ₂ e₂).symm, ?_⟩
  · have role : S.roles f = .computes (s + 1 + d)
        (.split (telescopeArgs (ofEntries e s) (prefixSub s d σ)).length .constructor fun _ => .leaf) := by
      rw [telescopeArgs_length]
      exact decl.role
    rw [applyClosed_split, applyClosed_split, prefixSub_replaceScrut, scrutOf_replaceScrut,
      suffixArgs_replaceScrut]
    exact WhRed.scrutinee role (by rw [telescopeArgs_length, suffixArgs_length]) red.red
  · refine Equal.telescope_apply (fun i => Equal.replaceScrut_pointwise e d typed ?_ i)
      decl.typing
    rw [subst_scrutinee e decl.scrutinee]
    exact red.equal

variable {R₀' R₁' R₂' : Rules Head} {u : Head} {rec : DeclName} {v : Head}
  (ind : DeclaresInductive S R₀' R₁' R₂' T u ctors rec v)
include ind

/-- At reducibly equal scrutinees, in every world, the full applications at
validly equal arguments are reducibly equal. -/
theorem DeclaresRecursion.claim {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed S.R Δ)
    {t t' : Tm Head m}
    (equal : IndEqTm S Δ T ctors (fun F => packOf S Δ (liftClosed F)) t t') :
    RecursionClaim S f e s d C Δ t t' := by
  have validType := decl.validType laws
  obtain ⟨validΘ, validC⟩ := ValidTy.telescope laws (ofEntries e (s + 1 + d)) validType
  have validPi : ValidTy S (ofEntries e (s + 1)) (piRange e (s + 1) d C) := by
    have h : ValidTy S .nil (closeType (ofEntries e (s + 1)) (piRange e (s + 1) d C)) := by
      rw [← closeType_ofEntries_add]
      exact validType
    exact (ValidTy.telescope laws (ofEntries e (s + 1)) h).2
  have hT := ind.packOf_type laws formed
  have rT := ind.type_reducible laws formed
  have fieldEnds : ∀ {F}, IsClosedField ctors F → ∀ {a b},
      (packOf S Δ (liftClosed F)).eqTm a b →
      (packOf S Δ (liftClosed F)).redTm a ∧ (packOf S Δ (liftClosed F)).redTm b :=
    fun ⟨_, _, mem, closed⟩ _ _ h =>
      (ind.field_logRel laws formed mem closed).reducible.eqTm_redTm laws h
  refine IndEqTm.rec
    (motive_1 := fun t t' _ => RecursionClaim S f e s d C Δ t t')
    (motive_2 := fun nf nf' _ => RecursionClaim S f e s d C Δ nf nf')
    (motive_3 := fun fs as as' _ => ∀ j (hj : j < (recPositions fs).length),
      RecursionClaim S f e s d C Δ (as.getD (recPositions fs)[j] defaultTm)
        (as'.getD (recPositions fs)[j] defaultTm))
    ?mk ?ctor ?neutral ?nil ?recursive ?closed equal
  case mk =>
    intro t t' nf nf' red red' conv normal ih k Δ' ρ w σ σ' vσ vσ' eσ hσ hσ' P r
    obtain ⟨nfNormal, nfNormal'⟩ := IndEqNf.ends laws fieldEnds normal
    have hnf : (packOf S Δ (.const T)).redTm nf := by
      rw [hT]
      exact .mk (RedTm.refl red.target) (laws.convTm_trans conv (laws.convTm_symm conv)) nfNormal
    have hnf' : (packOf S Δ (.const T)).redTm nf' := by
      rw [hT]
      exact .mk (RedTm.refl red'.target) (laws.convTm_trans (laws.convTm_symm conv) conv)
        nfNormal'
    obtain ⟨_, htnf⟩ := rT.redTm_expand red hnf
    obtain ⟨_, htnf'⟩ := rT.redTm_expand red' hnf'
    have rT' := ind.type_reducible laws w.2
    have wt : (packOf S Δ' (.const T)).eqTm (Presentation.rename ρ t) (Presentation.rename ρ nf) :=
      rT.packOf_weaken_eqTm laws w htnf
    have wt' : (packOf S Δ' (.const T)).eqTm (Presentation.rename ρ t')
        (Presentation.rename ρ nf') :=
      rT.packOf_weaken_eqTm laws w htnf'
    rw [← hσ] at wt
    rw [← hσ'] at wt'
    obtain ⟨vσ₂, eσ₂⟩ := ValidSubst.replaceScrut e decl.scrutinee laws rT' d validΘ vσ wt
    obtain ⟨vσ₂', eσ₂'⟩ := ValidSubst.replaceScrut e decl.scrutinee laws rT' d validΘ vσ' wt'
    have e₂₂ := EqSubst.trans laws validΘ vσ₂ vσ (EqSubst.symm laws validΘ vσ vσ₂ eσ₂)
      (EqSubst.trans laws validΘ vσ vσ' eσ eσ₂')
    obtain ⟨P₂, r₂⟩ := validC.red vσ₂
    have same := validC.pack_eq laws vσ vσ₂ eσ₂ r r₂
    subst same
    have inner := ih w vσ₂ vσ₂' e₂₂ (scrutOf_replaceScrut _ d σ) (scrutOf_replaceScrut _ d σ') r₂
    have redρ : RedTm S.R S.roles Δ' (scrutOf s d σ) (Presentation.rename ρ nf) (.const T) := by
      rw [hσ]
      exact red.rename w.1
    have redρ' : RedTm S.R S.roles Δ' (scrutOf s d σ') (Presentation.rename ρ nf')
        (.const T) := by
      rw [hσ']
      exact red'.rename w.1
    have redL := decl.scrutinee_red laws vσ redρ vσ₂ eσ₂
    have redR := decl.scrutinee_red laws vσ' redρ' vσ₂' eσ₂'
    have toσ : TypeEq S.R Δ' (Presentation.subst σ' C) (Presentation.subst σ C) :=
      (validC.typeEq_at laws vσ vσ' eσ).symm
    exact r.eqTm_expand laws redL (redR.conv toσ) inner
  case ctor =>
    intro kc fields as as' mem arguments ih k Δ' ρ w σ σ' vσ vσ' eσ hσ hσ' P r
    have formed' := w.2
    have rT' := ind.type_reducible laws formed'
    obtain ⟨lenAs, lenAs'⟩ := arguments.length
    have lenR : (as.map (Presentation.rename ρ)).length = fields.length := by
      rw [List.length_map, lenAs]
    have lenR' : (as'.map (Presentation.rename ρ)).length = fields.length := by
      rw [List.length_map, lenAs']
    rw [rename_appSpine] at hσ hσ'
    change scrutOf s d σ = appSpine (.const kc) (as.map (Presentation.rename ρ)) at hσ
    change scrutOf s d σ' = appSpine (.const kc) (as'.map (Presentation.rename ρ)) at hσ'
    /- The arguments for the fields, in the world. -/
    have fieldFacts : ∀ l, l < fields.length →
        Reducible S Δ' (liftClosed ((fields.getD l .recursive).type T))
            (packOf S Δ' (liftClosed ((fields.getD l .recursive).type T))) ∧
          (packOf S Δ' (liftClosed ((fields.getD l .recursive).type T))).eqTm
            ((as.map (Presentation.rename ρ)).getD l defaultTm)
            ((as'.map (Presentation.rename ρ)).getD l defaultTm) := by
      intro l hl
      refine ⟨ind.fieldType_reducible laws formed' mem hl, ?_⟩
      have h := (ind.fieldType_reducible laws formed mem hl).packOf_weaken_eqTm laws w
        (IndEqFields.getD_packOf hT arguments l hl)
      rw [rename_liftClosed, ← getD_map_rename, ← getD_map_rename] at h
      exact h
    obtain ⟨vm, vm', em⟩ := ValidSubst.pattern e laws fields fieldFacts lenR lenR' d vσ vσ' eσ
      hσ hσ'
    /- The recursive calls, reducible at their types. -/
    have calls : ∀ j, j < (recPositions fields).length →
        (∃ P₀, Reducible S Δ' (Presentation.subst (matchSub s fields.length
            (as.map (Presentation.rename ρ)) d σ)
            (recCallType e s fields.length d ((recPositions fields).getD j 0) C)) P₀ ∧
          P₀.redTm (Presentation.subst (matchSub s fields.length (as.map (Presentation.rename ρ)) d σ)
            (recCall f e s fields.length d ((recPositions fields).getD j 0))) ∧
          P₀.eqTm (Presentation.subst (matchSub s fields.length (as.map (Presentation.rename ρ)) d σ)
              (recCall f e s fields.length d ((recPositions fields).getD j 0)))
            (Presentation.subst (matchSub s fields.length (as'.map (Presentation.rename ρ)) d σ')
              (recCall f e s fields.length d ((recPositions fields).getD j 0)))) ∧
        (∃ P₀, Reducible S Δ' (Presentation.subst (matchSub s fields.length
            (as'.map (Presentation.rename ρ)) d σ')
            (recCallType e s fields.length d ((recPositions fields).getD j 0) C)) P₀ ∧
          P₀.redTm (Presentation.subst (matchSub s fields.length
              (as'.map (Presentation.rename ρ)) d σ')
            (recCall f e s fields.length d ((recPositions fields).getD j 0)))) := by
      intro j hj
      obtain ⟨hl, hrec⟩ := recPositions_spec fields j hj
      have hpos : (recPositions fields).getD j 0 = (recPositions fields)[j] := getD_of_lt 0 hj
      rw [hpos, subst_recCallType e _ σ C hl, subst_recCallType e _ σ' C hl,
        subst_recCall f e _ σ hl, subst_recCall f e _ σ' hl]
      have hfe : (packOf S Δ' (.const T)).eqTm
          ((as.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm)
          ((as'.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm) := by
        have h := (fieldFacts _ hl).2
        rw [hrec] at h
        exact h
      obtain ⟨ha, ha'⟩ := rT'.eqTm_redTm laws hfe
      have rScrut : ∀ τ : Sub Head s k, Reducible S Δ' (Presentation.subst τ (e s))
          (packOf S Δ' (.const T)) := by
        intro τ
        rw [subst_scrutinee e decl.scrutinee]
        exact rT'
      have vσ₀ : ValidSubst S (ofEntries e (s + 1)) Δ'
          (consSub ((as.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm)
            (prefixSub s d σ)) :=
        ValidSubst.cons (A := e s) (ValidSubst.prefixSub e d vσ) (rScrut _) ha
      have vσ₀' : ValidSubst S (ofEntries e (s + 1)) Δ'
          (consSub ((as'.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm)
            (prefixSub s d σ')) :=
        ValidSubst.cons (A := e s) (ValidSubst.prefixSub e d vσ') (rScrut _) ha'
      have eσ₀ : EqSubst S (ofEntries e (s + 1)) Δ'
          (consSub ((as.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm)
            (prefixSub s d σ))
          (consSub ((as'.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm)
            (prefixSub s d σ')) :=
        EqSubst.cons (A := e s) (EqSubst.prefixSub e d eσ) (rScrut _) hfe
      have full : ∀ {k₃ : Nat} {Δ'' : Ctx Head k₃} {ρ₃ : Ren k k₃}, World S Δ' Δ'' ρ₃ →
          ∀ {σ₃ σ₃' : Sub Head (s + 1 + d) k₃},
          ValidSubst S (ofEntries e (s + 1 + d)) Δ'' σ₃ →
          ValidSubst S (ofEntries e (s + 1 + d)) Δ'' σ₃' →
          EqSubst S (ofEntries e (s + 1 + d)) Δ'' σ₃ σ₃' →
          dropSub (s + 1) d σ₃ = (fun i => Presentation.rename ρ₃
            (consSub ((as.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm)
              (prefixSub s d σ) i)) →
          dropSub (s + 1) d σ₃' = (fun i => Presentation.rename ρ₃
            (consSub ((as'.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm)
              (prefixSub s d σ') i)) →
          ∀ {P₃ : Pack Head k₃}, Reducible S Δ'' (Presentation.subst σ₃ C) P₃ →
            P₃.eqTm (applyClosed (ofEntries e (s + 1 + d)) σ₃ (.const f))
              (applyClosed (ofEntries e (s + 1 + d)) σ₃' (.const f)) := by
        intro k₃ Δ'' ρ₃ w₃ σ₃ σ₃' v₃ v₃' e₃ d₃ d₃' P₃ r₃
        refine ih j hj (w.comp w₃) v₃ v₃' e₃ ?_ ?_ r₃
        · rw [scrutOf_eq_dropSub, d₃]
          show Presentation.rename ρ₃
              ((as.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm) = _
          rw [getD_map_rename, rename_rename]
        · rw [scrutOf_eq_dropSub, d₃']
          show Presentation.rename ρ₃
              ((as'.map (Presentation.rename ρ)).getD (recPositions fields)[j] defaultTm) = _
          rw [getD_map_rename, rename_rename]
      obtain ⟨P₀, r₀⟩ := validPi.red vσ₀
      obtain ⟨P₀', r₀'⟩ := validPi.red vσ₀'
      have eq₀ := partial_eqTm laws (.inr ⟨_, decl.role⟩) e (s + 1) d (Nat.le_refl _) C
        validType decl.typing full vσ₀ vσ₀' eσ₀ r₀
      have same₀ := validPi.pack_eq laws vσ₀ vσ₀' eσ₀ r₀ r₀'
      obtain ⟨h₀, h₀'⟩ := r₀.eqTm_redTm laws eq₀
      subst same₀
      exact ⟨⟨_, r₀, h₀, eq₀⟩, ⟨_, r₀', h₀'⟩⟩
    obtain ⟨vτ, vτ', eτ⟩ := ValidSubst.hyps
      (fun j => recCallType e s fields.length d ((recPositions fields).getD j 0) C)
      vm vm' em (recPositions fields).length (fun j hj => (calls j hj).1)
      (fun j hj => (calls j hj).2)
    /- The right-hand sides, at the type of the application. -/
    have tyEq : Presentation.subst (extendSub (matchSub s fields.length
          (as.map (Presentation.rename ρ)) d σ)
          (fun j => Presentation.subst (matchSub s fields.length
            (as.map (Presentation.rename ρ)) d σ)
            (recCall f e s fields.length d ((recPositions fields).getD j 0)))
          (recPositions fields).length)
        (Presentation.rename (wkN (recPositions fields).length)
          (Presentation.subst (patternSub s fields.length d kc) C)) =
        Presentation.subst σ C := by
      rw [subst_extendSub_wkN, subst_comp]
      have key : (fun ι => Presentation.subst (matchSub s fields.length
            (as.map (Presentation.rename ρ)) d σ) (patternSub s fields.length d kc ι)) =
          replaceScrut s (appSpine (.const kc) (as.map (Presentation.rename ρ))) d σ :=
        funext fun ι => subst_matchSub_patternSub kc _ lenR d σ ι
      rw [key, ← hσ, replaceScrut_self]
    have rB : Reducible S Δ' (Presentation.subst (extendSub (matchSub s fields.length
          (as.map (Presentation.rename ρ)) d σ)
          (fun j => Presentation.subst (matchSub s fields.length
            (as.map (Presentation.rename ρ)) d σ)
            (recCall f e s fields.length d ((recPositions fields).getD j 0)))
          (recPositions fields).length)
        (Presentation.rename (wkN (recPositions fields).length)
          (Presentation.subst (patternSub s fields.length d kc) C))) P := by
      rw [tyEq]
      exact r
    have inner := (decl.body_valid laws mem).ext vτ vτ' eτ rB
    /- The two applications compute to the right-hand sides. -/
    have step := decl.rule mem σ (as.map (Presentation.rename ρ)) lenR
    rw [← hσ, replaceScrut_self, subst_hypSub] at step
    have step' := decl.rule mem σ' (as'.map (Presentation.rename ρ)) lenR'
    rw [← hσ', replaceScrut_self, subst_hypSub] at step'
    have toσ : TypeEq S.R Δ' (Presentation.subst σ' C) (Presentation.subst σ C) :=
      (validC.typeEq_at laws vσ vσ' eσ).symm
    obtain ⟨hres, hres'⟩ := r.eqTm_redTm laws inner
    have red₁ := RedTm.of_root step (Typed.telescope_apply (vσ.substMor laws) decl.typing)
      ((r.escape laws).redTm hres).1
    have red₁' := RedTm.of_root step'
      (Typed.convType (Typed.telescope_apply (vσ'.substMor laws) decl.typing) toσ)
      ((r.escape laws).redTm hres').1
    exact r.eqTm_expand laws red₁ red₁' inner
  case neutral =>
    intro nf nf' nN nN' _ k Δ' ρ w σ σ' vσ vσ' eσ hσ hσ' P r
    have neutralL := decl.neutral (σ := σ) (by rw [hσ]; exact nN.rename ρ)
    have neutralR := decl.neutral (σ := σ') (by rw [hσ']; exact nN'.rename ρ)
    have conv : ∀ i, S.E.convTm Δ' (σ i) (σ' i)
        (Presentation.subst σ (Ctx.lookup (ofEntries e (s + 1 + d)) i)) := by
      intro i
      obtain ⟨Q, rQ, eQ⟩ := eσ.lookup i
      exact (rQ.escape laws).eqTm eQ
    have spine := convNe_telescope_apply laws conv (laws.convNe_const f decl.typing)
    have toσ : TypeEq S.R Δ' (Presentation.subst σ' C) (Presentation.subst σ C) :=
      (validC.typeEq_at laws vσ vσ' eσ).symm
    exact (r.reflects laws).eqTm neutralL neutralR
      (Typed.telescope_apply (vσ.substMor laws) decl.typing)
      (Typed.convType (Typed.telescope_apply (vσ'.substMor laws) decl.typing) toσ) spine
  case nil =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  case recursive =>
    intro fields as as' a a' _ _ ih₁ ih₃ j hj
    cases j with
    | zero => exact ih₁
    | succ j =>
        have hj' : j < (recPositions fields).length := by simpa [recPositions] using hj
        have e₁ : (recPositions (.recursive :: fields))[j + 1] = (recPositions fields)[j] + 1 := by
          simp [recPositions]
        rw [e₁]
        exact ih₃ j hj'
  case closed =>
    intro fields as as' F a a' _ _ ih₃ j hj
    have hj' : j < (recPositions fields).length := by simpa [recPositions] using hj
    have e₁ : (recPositions (.closed F :: fields))[j] = (recPositions fields)[j] + 1 := by
      simp [recPositions]
    rw [e₁]
    exact ih₃ j hj'

/-- The full application of the defined constant is valid in its telescope. -/
theorem DeclaresRecursion.full :
    ValidTm S (ofEntries e (s + 1 + d)) (applyClosed (ofEntries e (s + 1 + d)) ids (.const f))
      C := by
  obtain ⟨_, validC⟩ := ValidTy.telescope laws (ofEntries e (s + 1 + d)) (decl.validType laws)
  have apply : ∀ {m : Nat} (σ : Sub Head (s + 1 + d) m),
      Presentation.subst σ (applyClosed (ofEntries e (s + 1 + d)) ids (.const f)) =
        applyClosed (ofEntries e (s + 1 + d)) σ (.const f) := by
    intro m σ
    rw [applyClosed_subst]
    rfl
  have core : ∀ {m : Nat} {Δ : Ctx Head m} {σ σ' : Sub Head (s + 1 + d) m},
      ValidSubst S (ofEntries e (s + 1 + d)) Δ σ → ValidSubst S (ofEntries e (s + 1 + d)) Δ σ' →
      EqSubst S (ofEntries e (s + 1 + d)) Δ σ σ' →
      ∀ {P : Pack Head m}, Reducible S Δ (Presentation.subst σ C) P →
        P.eqTm (applyClosed (ofEntries e (s + 1 + d)) σ (.const f))
          (applyClosed (ofEntries e (s + 1 + d)) σ' (.const f)) := by
    intro m Δ σ σ' vσ vσ' eσ P r
    have formed := vσ.formed
    have scrut := EqSubst.scrut e decl.scrutinee laws d eσ
    rw [ind.packOf_type laws formed] at scrut
    exact decl.claim laws ind formed scrut (World.refl formed) vσ vσ' eσ
      (rename_id _).symm (rename_id _).symm r
  refine ⟨validC, fun {m Δ σ} vσ P r => ?_, fun {m Δ σ σ'} vσ vσ' eσ P r => ?_⟩
  · rw [apply]
    exact (r.eqTm_redTm laws (core vσ vσ vσ.refl r)).1
  · rw [apply, apply]
    exact core vσ vσ' eσ r

/-- The defined constant is semantic. -/
theorem DeclaresRecursion.semantic :
    SemanticConstant S f (closeType (ofEntries e (s + 1 + d)) C) := by
  have typing : Typed S.R .nil (.const f) (closeType (ofEntries e (s + 1 + d)) C) := by
    have h := decl.typing (Γ := .nil)
    rwa [liftClosed_zero] at h
  intro m Δ formed P r
  exact SemanticConstant.of_telescope laws (.inr ⟨_, decl.role⟩)
    (Θ := ofEntries e (s + 1 + d)) (C := C) typing (decl.validType laws) (decl.full laws ind)
    formed r

end Semantics

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
