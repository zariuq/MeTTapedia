import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Package
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Algorithm

/-!
# The new constants are inert: the kernel's conversion is unchanged

The extension adds no root computation (`Signature.rules_computation`), so
untyped conversion is literally the base package's (`Signature.conv_iff`).
This file shows the same for the kernel's type-directed conversion algorithm
(`TypedEquality.Algorithm`): on every problem whose context and terms avoid the
two new names, the algorithm derives exactly what it derives in the base
package (`algorithm_iff`). The recursor and its unfolding are never reached,
because reduction of a term that avoids them stays clear of them
(`Avoids.reduces`), and the neutral types the algorithm computes come from the
context and from declared types that avoid them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Normalization (DecoderStep)

variable {Head : Type}

/-! ## Terms that avoid a set of names -/

/-- A term mentions no name satisfying `N`. -/
def Avoids (N : DeclName → Prop) : {n : Nat} → Tm Head n → Prop
  | _, .var _ => True
  | _, .const c => ¬ N c
  | _, .head _ => True
  | _, .pi A B => Avoids N A ∧ Avoids N B
  | _, .sigma A B => Avoids N A ∧ Avoids N B
  | _, .id A a b => Avoids N A ∧ Avoids N a ∧ Avoids N b
  | _, .lam body => Avoids N body
  | _, .app g a => Avoids N g ∧ Avoids N a
  | _, .pair a b => Avoids N a ∧ Avoids N b
  | _, .fst p => Avoids N p
  | _, .snd p => Avoids N p
  | _, .refl a => Avoids N a

/-- A context mentions no name satisfying `N`. -/
def CtxAvoids (N : DeclName → Prop) : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => CtxAvoids N Γ ∧ Avoids N A

variable {N : DeclName → Prop}

theorem Avoids.rename {n m : Nat} {t : Tm Head n} (ρ : Ren n m) (h : Avoids N t) :
    Avoids N (Presentation.rename ρ t) := by
  induction t generalizing m with
  | var => trivial
  | const => exact h
  | head => trivial
  | pi A B ihA ihB => exact ⟨ihA ρ h.1, ihB (liftRen ρ) h.2⟩
  | sigma A B ihA ihB => exact ⟨ihA ρ h.1, ihB (liftRen ρ) h.2⟩
  | id A a b ihA iha ihb => exact ⟨ihA ρ h.1, iha ρ h.2.1, ihb ρ h.2.2⟩
  | lam body ih => exact ih (liftRen ρ) h
  | app g a ihg iha => exact ⟨ihg ρ h.1, iha ρ h.2⟩
  | pair a b iha ihb => exact ⟨iha ρ h.1, ihb ρ h.2⟩
  | fst p ih => exact ih ρ h
  | snd p ih => exact ih ρ h
  | refl a ih => exact ih ρ h

theorem Avoids.liftSub {n m : Nat} {σ : Sub Head n m} (hσ : ∀ i, Avoids N (σ i)) :
    ∀ i, Avoids N (Presentation.liftSub σ i) := fun i =>
  Fin.cases (motive := fun i => Avoids N (Presentation.liftSub σ i)) trivial
    (fun j => Avoids.rename wk (hσ j)) i

theorem Avoids.subst {n m : Nat} {t : Tm Head n} {σ : Sub Head n m} (h : Avoids N t)
    (hσ : ∀ i, Avoids N (σ i)) : Avoids N (Presentation.subst σ t) := by
  induction t generalizing m with
  | var i => exact hσ i
  | const => exact h
  | head => trivial
  | pi A B ihA ihB => exact ⟨ihA h.1 hσ, ihB h.2 (Avoids.liftSub hσ)⟩
  | sigma A B ihA ihB => exact ⟨ihA h.1 hσ, ihB h.2 (Avoids.liftSub hσ)⟩
  | id A a b ihA iha ihb => exact ⟨ihA h.1 hσ, iha h.2.1 hσ, ihb h.2.2 hσ⟩
  | lam body ih => exact ih h (Avoids.liftSub hσ)
  | app g a ihg iha => exact ⟨ihg h.1 hσ, iha h.2 hσ⟩
  | pair a b iha ihb => exact ⟨iha h.1 hσ, ihb h.2 hσ⟩
  | fst p ih => exact ih h hσ
  | snd p ih => exact ih h hσ
  | refl a ih => exact ih h hσ

theorem Avoids.inst0 {n : Nat} {a : Tm Head n} {body : Tm Head (n + 1)}
    (ha : Avoids N a) (hb : Avoids N body) : Avoids N (inst0 a body) :=
  Avoids.subst hb fun i => Fin.cases (motive := fun i => Avoids N (subst0 a i)) ha
    (fun _ => trivial) i

theorem Avoids.liftClosed {n : Nat} {t : Tm Head 0} (h : Avoids N t) :
    Avoids N (liftClosed t : Tm Head n) :=
  Avoids.rename _ h

/-- One contextual step keeps a term clear of `N`, when every root step does. -/
theorem Avoids.step {root : RootComputation Head} {headEq : Head → Head → Prop}
    (rootAvoids : ∀ {n : Nat} {l r : Tm Head n}, root.step l r → Avoids N l → Avoids N r)
    {n : Nat} {l r : Tm Head n} (step : StepCore root headEq l r) (h : Avoids N l) :
    Avoids N r := by
  induction step with
  | betaPi body a => exact Avoids.inst0 h.2 h.1
  | betaSigmaFst a b => exact h.1
  | betaSigmaSnd a b => exact h.2
  | head _ => trivial
  | root step => exact rootAvoids step h
  | congPiDom _ ih => exact ⟨ih h.1, h.2⟩
  | congPiCod _ ih => exact ⟨h.1, ih h.2⟩
  | congSigmaDom _ ih => exact ⟨ih h.1, h.2⟩
  | congSigmaCod _ ih => exact ⟨h.1, ih h.2⟩
  | congIdTy _ ih => exact ⟨ih h.1, h.2⟩
  | congIdLeft _ ih => exact ⟨h.1, ih h.2.1, h.2.2⟩
  | congIdRight _ ih => exact ⟨h.1, h.2.1, ih h.2.2⟩
  | congLam _ ih => exact ih h
  | congAppFun _ ih => exact ⟨ih h.1, h.2⟩
  | congAppArg _ ih => exact ⟨h.1, ih h.2⟩
  | congPairFst _ ih => exact ⟨ih h.1, h.2⟩
  | congPairSnd _ ih => exact ⟨h.1, ih h.2⟩
  | congFst _ ih => exact ih h
  | congSnd _ ih => exact ih h
  | congRefl _ ih => exact ih h

/-- Reduction keeps a term clear of `N`, when every root step does. -/
theorem Avoids.reduces {R : Rules Head}
    (rootAvoids : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r → Avoids N l → Avoids N r)
    {n : Nat} {l r : Tm Head n} (red : Reduces R l r) (h : Avoids N l) : Avoids N r := by
  induction red with
  | refl => exact h
  | tail _ step ih => exact Avoids.step rootAvoids step ih

theorem CtxAvoids.lookup : ∀ {n : Nat} {Γ : Ctx Head n}, CtxAvoids N Γ → ∀ i : Fin n,
    Avoids N (Ctx.lookup Γ i)
  | _, .nil, _, i => i.elim0
  | _, .snoc Γ A, h, i => Fin.cases (motive := fun i => Avoids N (Ctx.lookup (.snoc Γ A) i))
      (Avoids.rename wk h.2) (fun j => Avoids.rename wk (CtxAvoids.lookup h.1 j)) i

/-! ## The kernel's conversion on problems that avoid the new names -/

/-- A problem of the conversion algorithm whose context and terms avoid `N`;
at a neutral problem, the computed type is not constrained. -/
def AlgorithmAvoids (N : DeclName → Prop) : AlgorithmStatement Head → Prop
  | .compare Γ a b T => CtxAvoids N Γ ∧ Avoids N a ∧ Avoids N b ∧ Avoids N T
  | .neutral Γ a b _ => CtxAvoids N Γ ∧ Avoids N a ∧ Avoids N b
  | .types Γ A B => CtxAvoids N Γ ∧ Avoids N A ∧ Avoids N B

/-- The conclusion of the transfer: the base package derives the problem, and at
a neutral problem the computed type avoids `N` too. -/
def AlgorithmTransfer (N : DeclName → Prop) (R : Rules Head) : AlgorithmStatement Head → Prop
  | .compare Γ a b T => Algorithm R (.compare Γ a b T)
  | .neutral Γ a b U => Avoids N U ∧ Algorithm R (.neutral Γ a b U)
  | .types Γ A B => Algorithm R (.types Γ A B)

/-- **Transfer of the conversion algorithm.** If two packages share their
universe rules and computation, the computation keeps terms clear of `N`, and
every constant outside `N` declared by the first is declared by the second at a
type that avoids `N`, then every derivation of the first on a problem that
avoids `N` is a derivation of the second. -/
theorem algorithm_transfer {R R' : Rules Head}
    (headEq : R.headEq = R'.headEq) (isUniverse : R.isUniverse = R'.isUniverse)
    (computation : R.computation = R'.computation)
    (rootAvoids : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r → Avoids N l → Avoids N r)
    (declared : ∀ {c : DeclName} {T : Tm Head 0}, ¬ N c → R.constantType c = some T →
      R'.constantType c = some T ∧ Avoids N T)
    {st : AlgorithmStatement Head} (d : Algorithm R st) (h : AlgorithmAvoids N st) :
    AlgorithmTransfer N R' st := by
  have red : ∀ {n : Nat} {l r : Tm Head n}, Reduces R l r → Reduces R' l r := by
    intro n l r d
    unfold Reduces at d ⊢
    rw [← computation, ← headEq]
    exact d
  induction d with
  | pi hT _ ih =>
      obtain ⟨hΓ, ha, hb, hT'⟩ := h
      have hAB := Avoids.reduces rootAvoids hT hT'
      exact .pi (red hT) (ih ⟨⟨hΓ, hAB.1⟩, ⟨Avoids.rename wk ha, trivial⟩,
        ⟨Avoids.rename wk hb, trivial⟩, hAB.2⟩)
  | sigma hT _ _ ih₁ ih₂ =>
      obtain ⟨hΓ, ha, hb, hT'⟩ := h
      have hAB := Avoids.reduces rootAvoids hT hT'
      exact .sigma (red hT) (ih₁ ⟨hΓ, ha, hb, hAB.1⟩)
        (ih₂ ⟨hΓ, ha, hb, Avoids.inst0 ha hAB.2⟩)
  | sort hT hu _ ih =>
      obtain ⟨hΓ, ha, hb, -⟩ := h
      exact .sort (red hT) (isUniverse ▸ hu) (ih ⟨hΓ, ha, hb⟩)
  | reflexivity hT ha hb _ ih =>
      obtain ⟨hΓ, ha', hb', hT'⟩ := h
      have hA := Avoids.reduces rootAvoids hT hT'
      have ha'' : Avoids N _ := Avoids.reduces rootAvoids ha ha'
      have hb'' : Avoids N _ := Avoids.reduces rootAvoids hb hb'
      exact .reflexivity (red hT) (red ha) (red hb) (ih ⟨hΓ, ha'', hb'', hA.1⟩)
  | neutralAt ha hb _ ih =>
      obtain ⟨hΓ, ha', hb', -⟩ := h
      exact .neutralAt (red ha) (red hb)
        (ih ⟨hΓ, Avoids.reduces rootAvoids ha ha', Avoids.reduces rootAvoids hb hb'⟩).2
  | var i =>
      exact ⟨CtxAvoids.lookup h.1 i, .var i⟩
  | const known =>
      obtain ⟨-, hc, -⟩ := h
      obtain ⟨known', hT⟩ := declared hc known
      exact ⟨Avoids.liftClosed hT, .const known'⟩
  | app _ hU _ ihf iha =>
      obtain ⟨hΓ, hf, ha⟩ := h
      obtain ⟨hU', df⟩ := ihf ⟨hΓ, hf.1, ha.1⟩
      have hAB := Avoids.reduces rootAvoids hU hU'
      exact ⟨Avoids.inst0 hf.2 hAB.2, .app df (red hU) (iha ⟨hΓ, hf.2, ha.2, hAB.1⟩)⟩
  | fst _ hU ih =>
      obtain ⟨hΓ, hp, hq⟩ := h
      obtain ⟨hU', dp⟩ := ih ⟨hΓ, hp, hq⟩
      have hAB := Avoids.reduces rootAvoids hU hU'
      exact ⟨hAB.1, .fst dp (red hU)⟩
  | snd _ hU ih =>
      obtain ⟨hΓ, hp, hq⟩ := h
      obtain ⟨hU', dp⟩ := ih ⟨hΓ, hp, hq⟩
      have hAB := Avoids.reduces rootAvoids hU hU'
      exact ⟨Avoids.inst0 hp hAB.2, .snd dp (red hU)⟩
  | heads hA hB same =>
      exact .heads (red hA) (red hB) (headEq ▸ same)
  | piTypes hA hB _ _ ih₁ ih₂ =>
      obtain ⟨hΓ, hA', hB'⟩ := h
      have h₁ := Avoids.reduces rootAvoids hA hA'
      have h₂ := Avoids.reduces rootAvoids hB hB'
      exact .piTypes (red hA) (red hB) (ih₁ ⟨hΓ, h₁.1, h₂.1⟩) (ih₂ ⟨⟨hΓ, h₁.1⟩, h₁.2, h₂.2⟩)
  | sigmaTypes hA hB _ _ ih₁ ih₂ =>
      obtain ⟨hΓ, hA', hB'⟩ := h
      have h₁ := Avoids.reduces rootAvoids hA hA'
      have h₂ := Avoids.reduces rootAvoids hB hB'
      exact .sigmaTypes (red hA) (red hB) (ih₁ ⟨hΓ, h₁.1, h₂.1⟩) (ih₂ ⟨⟨hΓ, h₁.1⟩, h₁.2, h₂.2⟩)
  | idTypes hA hB _ _ _ ih₁ ih₂ ih₃ =>
      obtain ⟨hΓ, hA', hB'⟩ := h
      have h₁ := Avoids.reduces rootAvoids hA hA'
      have h₂ := Avoids.reduces rootAvoids hB hB'
      exact .idTypes (red hA) (red hB) (ih₁ ⟨hΓ, h₁.1, h₂.1⟩) (ih₂ ⟨hΓ, h₁.2.1, h₂.2.1, h₁.1⟩)
        (ih₃ ⟨hΓ, h₁.2.2, h₂.2.2, h₁.1⟩)
  | neutralTypes hA hB _ ih =>
      obtain ⟨hΓ, hA', hB'⟩ := h
      exact .neutralTypes (red hA) (red hB)
        (ih ⟨hΓ, Avoids.reduces rootAvoids hA hA', Avoids.reduces rootAvoids hB hB'⟩).2

/-! ## The accessibility package -/

namespace Signature

variable (S : Signature Head)

/-- The two new names. -/
def New (c : DeclName) : Prop := c = S.recursor ∨ c = S.unfold

/-- What the base package must satisfy for the two new names to be inert in the
kernel's conversion: its root steps keep terms clear of them, its declared types
avoid them, and so do the carriers of the codes. -/
structure InertLaws : Prop where
  base_step : ∀ {n : Nat} {l r : Tm Head n}, S.base.computation.step l r →
    Avoids S.New l → Avoids S.New r
  base_types : ∀ {c : DeclName} {T : Tm Head 0}, S.base.constantType c = some T →
    Avoids S.New T
  quantifiers : ∀ {a : DeclName} {A : Tm Head 0}, S.codes.quantifiers a = some A →
    Avoids S.New A
  equations : ∀ {e : DeclName} {A : Tm Head 0}, S.codes.equationCarrier e = some A →
    Avoids S.New A

variable {S}

theorem Laws.code_names_old (L : S.Laws) {c : DeclName} (h : (S.codes.codeType c).isSome) :
    ¬ S.New c := by
  rintro (rfl | rfl)
  · rw [L.recursor_fresh.1] at h
    cases h
  · rw [L.unfold_fresh.1] at h
    cases h

theorem Laws.prop_old (L : S.Laws) : ¬ S.New S.codes.prop :=
  L.code_names_old (by simp [Codes.codeType])

theorem codeType_avoids (L : S.Laws) (I : S.InertLaws) {c : DeclName} {T : Tm Head 0}
    (h : S.codes.codeType c = some T) : Avoids S.New T := by
  have hp : Avoids S.New (S.codes.propT : Tm Head 0) := L.prop_old
  unfold Codes.codeType at h
  split at h
  · cases h; trivial
  split at h
  · cases h
    exact ⟨hp, trivial⟩
  split at h
  · cases h
    exact ⟨hp, hp, hp⟩
  cases hq : S.codes.quantifiers c with
  | some A =>
      rw [hq] at h
      cases h
      exact ⟨⟨I.quantifiers hq, hp⟩, hp⟩
  | none =>
      rw [hq] at h
      cases he : S.codes.equationCarrier c with
      | none => rw [he] at h; cases h
      | some A =>
          rw [he] at h
          cases h
          exact ⟨I.equations he, Avoids.rename wk (I.equations he), hp⟩

theorem rootAvoids (I : S.InertLaws) {n : Nat} {l r : Tm Head n}
    (step : S.baseRules.computation.step l r) (h : Avoids S.New l) : Avoids S.New r := by
  rcases step with step | step
  · exact I.base_step step h
  · cases step with
    | imp p q => exact ⟨⟨h.1, h.2.1.2⟩, ⟨h.1, Avoids.rename wk h.2.2⟩⟩
    | all carrier f =>
        exact ⟨Avoids.liftClosed (I.quantifiers carrier), h.1, Avoids.rename wk h.2.2, trivial⟩
    | eq carrier x y =>
        exact ⟨Avoids.liftClosed (I.equations carrier), h.2.1.2, h.2.2⟩

/-- **The kernel's conversion is unchanged by the extension.** On every problem
whose context and terms avoid the recursor and its unfolding, the conversion
algorithm of the extended package derives exactly what the base package's
derives. -/
theorem algorithm_iff (L : S.Laws) (I : S.InertLaws) {st : AlgorithmStatement Head}
    (h : AlgorithmAvoids S.New st) : Algorithm S.rules st ↔ Algorithm S.baseRules st := by
  have base_declared : ∀ {c : DeclName} {T : Tm Head 0}, S.baseRules.constantType c = some T →
      Avoids S.New T := by
    intro c T declared
    change (S.codes.codeType c).orElse (fun _ => S.base.constantType c) = some T at declared
    cases e : S.codes.codeType c with
    | some T' =>
        rw [e] at declared
        cases declared
        exact codeType_avoids L I e
    | none =>
        rw [e] at declared
        exact I.base_types declared
  have fwd : ∀ {c : DeclName} {T : Tm Head 0}, ¬ S.New c → S.rules.constantType c = some T →
      S.baseRules.constantType c = some T ∧ Avoids S.New T := by
    intro c T hc declared
    have e : S.rules.constantType c = S.baseRules.constantType c := by
      have hr : c ≠ S.recursor := fun h => hc (.inl h)
      have hu : c ≠ S.unfold := fun h => hc (.inr h)
      simp [Codes.extend, accBase, hr, hu]
    rw [e] at declared
    exact ⟨declared, base_declared declared⟩
  have bwd : ∀ {c : DeclName} {T : Tm Head 0}, ¬ S.New c → S.baseRules.constantType c = some T →
      S.rules.constantType c = some T ∧ Avoids S.New T :=
    fun _ declared => ⟨(L.base_accBase.codes S.codes).constantType declared, base_declared declared⟩
  constructor
  · intro d
    have t := algorithm_transfer (R := S.rules) (R' := S.baseRules) rfl rfl rfl
      (fun step h => rootAvoids I step h) fwd d h
    cases st <;> first | exact t | exact t.2
  · intro d
    have t := algorithm_transfer (R := S.baseRules) (R' := S.rules) rfl rfl rfl
      (fun step h => rootAvoids I step h) bwd d h
    cases st <;> first | exact t | exact t.2

end Signature

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
