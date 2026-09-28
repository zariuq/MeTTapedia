import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Judgment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws

/-!
# Renaming and substitution for typed equality

Both judgments are stable under context renaming and under simultaneous
substitution by a typed substitution. The proofs are one induction over the
shared derivation family, so typing and equality are treated together; the
conversion rule, the extensionality rules and the declared root computations
need no additional hypothesis beyond the rule package's own stability of root
steps under renaming and substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

variable {Head : Type}

/-- Weakening past one binder commutes with lifting a renaming. -/
theorem rename_liftRen_wk {n m : Nat} (ρ : Ren n m) (t : Tm Head n) :
    rename (liftRen ρ) (rename wk t) = rename wk (rename ρ t) := by
  simp only [rename_comp]
  rfl

/-! ## Renaming -/

/-- What renaming along a compatible context map gives for a statement. -/
abbrev Statement.Renames (R : Rules Head) : Statement Head → Prop
  | .typing Γ t A => ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren _ m},
      CtxRen Γ Δ ρ → Typed R Δ (rename ρ t) (rename ρ A)
  | .equality Γ a b A => ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren _ m},
      CtxRen Γ Δ ρ → Equal R Δ (rename ρ a) (rename ρ b) (rename ρ A)
  | .sub Γ A B => ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren _ m},
      CtxRen Γ Δ ρ → Below R Δ (rename ρ A) (rename ρ B)

theorem Derivable.renames {R : Rules Head} {statement : Statement Head}
    (derivation : Derivable R statement) : statement.Renames R := by
  induction derivation with
  | headType head =>
      intro m Δ ρ compatible
      exact .headType head
  | var index =>
      intro m Δ ρ compatible
      simpa only [rename, compatible index] using
        (Derivable.var (R := R) (Γ := Δ) (ρ index))
  | const known formed universeWitness _ =>
      intro m Δ ρ compatible
      simpa only [rename, rename_liftClosed] using
        (Derivable.const (Γ := Δ) known formed universeWitness)
  | piForm _ universeA _ universeB join ihA ihB =>
      intro m Δ ρ compatible
      exact .piForm (ihA compatible) universeA (ihB (compatible.snoc _))
        universeB join
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      intro m Δ ρ compatible
      exact .sigmaForm (ihA compatible) universeA (ihB (compatible.snoc _))
        universeB join
  | lamIntro _ universeWitness _ ihPi ihBody =>
      intro m Δ ρ compatible
      exact .lamIntro (ihPi compatible) universeWitness
        (ihBody (compatible.snoc _))
  | appElim _ _ ihFunction ihArgument =>
      intro m Δ ρ compatible
      simpa only [rename, rename_inst0] using
        (Derivable.appElim (ihFunction compatible) (ihArgument compatible))
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ ρ compatible
      have second := ihSecond compatible
      rw [rename_inst0] at second
      exact .pairIntro (ihSigma compatible) universeWitness
        (ihFirst compatible) second
  | fstElim _ ihPair =>
      intro m Δ ρ compatible
      exact .fstElim (ihPair compatible)
  | sndElim _ ihPair =>
      intro m Δ ρ compatible
      simpa only [rename, rename_inst0] using
        (Derivable.sndElim (ihPair compatible))
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      intro m Δ ρ compatible
      exact .idForm (ihA compatible) universeWitness (ihLeft compatible)
        (ihRight compatible)
  | reflIntro _ ihTerm =>
      intro m Δ ρ compatible
      exact .reflIntro (ihTerm compatible)
  | conv _ _ universeWitness ihTerm ihEquality =>
      intro m Δ ρ compatible
      exact .conv (ihTerm compatible) (ihEquality compatible) universeWitness
  | refl _ ih =>
      intro m Δ ρ compatible
      exact .refl (ih compatible)
  | symm _ ih =>
      intro m Δ ρ compatible
      exact .symm (ih compatible)
  | trans _ _ ihFirst ihSecond =>
      intro m Δ ρ compatible
      exact .trans (ihFirst compatible) (ihSecond compatible)
  | convEq _ _ universeWitness ihEquality ihType =>
      intro m Δ ρ compatible
      exact .convEq (ihEquality compatible) (ihType compatible) universeWitness
  | headEq equal _ _ ihLeft ihRight =>
      intro m Δ ρ compatible
      exact .headEq equal (ihLeft compatible) (ihRight compatible)
  | piCong _ universeA _ universeB join ihA ihB =>
      intro m Δ ρ compatible
      exact .piCong (ihA compatible) universeA (ihB (compatible.snoc _))
        universeB join
  | sigmaCong _ universeA _ universeB join ihA ihB =>
      intro m Δ ρ compatible
      exact .sigmaCong (ihA compatible) universeA (ihB (compatible.snoc _))
        universeB join
  | idCong _ universeWitness _ _ ihA ihLeft ihRight =>
      intro m Δ ρ compatible
      exact .idCong (ihA compatible) universeWitness (ihLeft compatible)
        (ihRight compatible)
  | lamCong _ universeWitness _ ihPi ihBody =>
      intro m Δ ρ compatible
      exact .lamCong (ihPi compatible) universeWitness
        (ihBody (compatible.snoc _))
  | appCong _ _ ihFunction ihArgument =>
      intro m Δ ρ compatible
      simpa only [rename, rename_inst0] using
        (Derivable.appCong (ihFunction compatible) (ihArgument compatible))
  | pairCong _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ ρ compatible
      have second := ihSecond compatible
      rw [rename_inst0] at second
      exact .pairCong (ihSigma compatible) universeWitness
        (ihFirst compatible) second
  | fstCong _ ihPair =>
      intro m Δ ρ compatible
      exact .fstCong (ihPair compatible)
  | sndCong _ ihPair =>
      intro m Δ ρ compatible
      simpa only [rename, rename_inst0] using
        (Derivable.sndCong (ihPair compatible))
  | reflCong _ ih =>
      intro m Δ ρ compatible
      exact .reflCong (ih compatible)
  | betaPi _ universeWitness _ _ ihPi ihBody ihArgument =>
      intro m Δ ρ compatible
      simpa only [rename, rename_inst0] using
        (Derivable.betaPi (ihPi compatible) universeWitness
          (ihBody (compatible.snoc _)) (ihArgument compatible))
  | betaFst _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ ρ compatible
      have second := ihSecond compatible
      rw [rename_inst0] at second
      exact .betaFst (ihSigma compatible) universeWitness
        (ihFirst compatible) second
  | betaSnd _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ ρ compatible
      have second := ihSecond compatible
      rw [rename_inst0] at second
      simpa only [rename, rename_inst0] using
        (Derivable.betaSnd (ihSigma compatible) universeWitness
          (ihFirst compatible) second)
  | root step _ _ ihLeft ihRight =>
      intro m Δ ρ compatible
      exact .root (R.computation.rename ρ step) (ihLeft compatible)
        (ihRight compatible)
  | etaPi _ _ _ ihLeft ihRight ihBody =>
      intro m Δ ρ compatible
      have body := ihBody (compatible.snoc _)
      simp only [rename, rename_liftRen_wk] at body
      exact .etaPi (ihLeft compatible) (ihRight compatible) body
  | etaSigma _ _ _ _ ihLeft ihRight ihFirst ihSecond =>
      intro m Δ ρ compatible
      have second := ihSecond compatible
      simp only [rename, rename_inst0] at second
      exact .etaSigma (ihLeft compatible) (ihRight compatible)
        (ihFirst compatible) second
  | sub _ _ ihTerm ihLe =>
      intro m Δ ρ compatible
      exact .sub (ihTerm compatible) (ihLe compatible)
  | subEq _ _ ih ihLe =>
      intro m Δ ρ compatible
      exact .subEq (ih compatible) (ihLe compatible)
  | subEqual _ universeWitness ih =>
      intro m Δ ρ compatible
      exact .subEqual (ih compatible) universeWitness
  | subUniv order =>
      intro m Δ ρ compatible
      exact .subUniv order
  | subPi _ universeA _ universeB _ universeW _ ihPi ihPi' ihA ihB =>
      intro m Δ ρ compatible
      exact .subPi (ihPi compatible) universeA (ihPi' compatible) universeB
        (ihA compatible) universeW (ihB (compatible.snoc _))
  | subSigma _ universeA _ universeB _ _ ihSigma ihSigma' ihA ihB =>
      intro m Δ ρ compatible
      exact .subSigma (ihSigma compatible) universeA (ihSigma' compatible) universeB
        (ihA compatible) (ihB (compatible.snoc _))
  | subTrans _ _ ihFirst ihSecond =>
      intro m Δ ρ compatible
      exact .subTrans (ihFirst compatible) (ihSecond compatible)

theorem Typed.rename {R : Rules Head} {n m : Nat} {Γ : Ctx Head n}
    {Δ : Ctx Head m} {ρ : Ren n m} {t A : Tm Head n}
    (typing : Typed R Γ t A) (compatible : CtxRen Γ Δ ρ) :
    Typed R Δ (Presentation.rename ρ t) (Presentation.rename ρ A) :=
  Derivable.renames typing compatible

theorem Equal.rename {R : Rules Head} {n m : Nat} {Γ : Ctx Head n}
    {Δ : Ctx Head m} {ρ : Ren n m} {a b A : Tm Head n}
    (equality : Equal R Γ a b A) (compatible : CtxRen Γ Δ ρ) :
    Equal R Δ (Presentation.rename ρ a) (Presentation.rename ρ b)
      (Presentation.rename ρ A) :=
  Derivable.renames equality compatible

theorem Typed.weaken {R : Rules Head} {n : Nat} {Γ : Ctx Head n}
    {t A extension : Tm Head n} (typing : Typed R Γ t A) :
    Typed R (.snoc Γ extension) (Presentation.rename wk t)
      (Presentation.rename wk A) :=
  typing.rename (fun _ => rfl)

theorem Equal.weaken {R : Rules Head} {n : Nat} {Γ : Ctx Head n}
    {a b A extension : Tm Head n} (equality : Equal R Γ a b A) :
    Equal R (.snoc Γ extension) (Presentation.rename wk a)
      (Presentation.rename wk b) (Presentation.rename wk A) :=
  equality.rename (fun _ => rfl)

/-! ## Substitution -/

/-- A simultaneous substitution typed by the new judgment. -/
def SubstMor (R : Rules Head) {n m : Nat} (Γ : Ctx Head n) (Δ : Ctx Head m)
    (σ : Sub Head n m) : Prop :=
  ∀ index, Typed R Δ (σ index) (subst σ (Ctx.lookup Γ index))

theorem SubstMor.lift {R : Rules Head} {n m : Nat} {Γ : Ctx Head n}
    {Δ : Ctx Head m} {σ : Sub Head n m} (typed : SubstMor R Γ Δ σ)
    (A : Tm Head n) :
    SubstMor R (.snoc Γ A) (.snoc Δ (subst σ A)) (liftSub σ) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [liftSub_zero, Ctx.lookup_snoc_zero, subst_liftSub_wk] using
      (Derivable.var (R := R) (Γ := .snoc Δ (subst σ A)) (0 : Fin (m + 1)))
  · intro prior
    simpa only [liftSub_succ, Ctx.lookup_snoc_succ, subst_liftSub_wk] using
      (Typed.weaken (extension := subst σ A) (typed prior))

/-- What substitution along a typed substitution gives for a statement. -/
abbrev Statement.Substitutes (R : Rules Head) : Statement Head → Prop
  | .typing Γ t A => ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head _ m},
      SubstMor R Γ Δ σ → Typed R Δ (subst σ t) (subst σ A)
  | .equality Γ a b A => ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head _ m},
      SubstMor R Γ Δ σ → Equal R Δ (subst σ a) (subst σ b) (subst σ A)
  | .sub Γ A B => ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head _ m},
      SubstMor R Γ Δ σ → Below R Δ (subst σ A) (subst σ B)

theorem Derivable.substitutes {R : Rules Head} {statement : Statement Head}
    (derivation : Derivable R statement) : statement.Substitutes R := by
  induction derivation with
  | headType head =>
      intro m Δ σ typed
      exact .headType head
  | var index =>
      intro m Δ σ typed
      exact typed index
  | const known formed universeWitness _ =>
      intro m Δ σ typed
      simpa only [subst, subst_liftClosed] using
        (Derivable.const (Γ := Δ) known formed universeWitness)
  | piForm _ universeA _ universeB join ihA ihB =>
      intro m Δ σ typed
      exact .piForm (ihA typed) universeA (ihB (typed.lift _)) universeB join
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      intro m Δ σ typed
      exact .sigmaForm (ihA typed) universeA (ihB (typed.lift _)) universeB join
  | lamIntro _ universeWitness _ ihPi ihBody =>
      intro m Δ σ typed
      exact .lamIntro (ihPi typed) universeWitness (ihBody (typed.lift _))
  | appElim _ _ ihFunction ihArgument =>
      intro m Δ σ typed
      simpa only [subst, subst_inst0] using
        (Derivable.appElim (ihFunction typed) (ihArgument typed))
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ σ typed
      have second := ihSecond typed
      rw [subst_inst0] at second
      exact .pairIntro (ihSigma typed) universeWitness (ihFirst typed) second
  | fstElim _ ihPair =>
      intro m Δ σ typed
      exact .fstElim (ihPair typed)
  | sndElim _ ihPair =>
      intro m Δ σ typed
      simpa only [subst, subst_inst0] using (Derivable.sndElim (ihPair typed))
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      intro m Δ σ typed
      exact .idForm (ihA typed) universeWitness (ihLeft typed) (ihRight typed)
  | reflIntro _ ihTerm =>
      intro m Δ σ typed
      exact .reflIntro (ihTerm typed)
  | conv _ _ universeWitness ihTerm ihEquality =>
      intro m Δ σ typed
      exact .conv (ihTerm typed) (ihEquality typed) universeWitness
  | refl _ ih =>
      intro m Δ σ typed
      exact .refl (ih typed)
  | symm _ ih =>
      intro m Δ σ typed
      exact .symm (ih typed)
  | trans _ _ ihFirst ihSecond =>
      intro m Δ σ typed
      exact .trans (ihFirst typed) (ihSecond typed)
  | convEq _ _ universeWitness ihEquality ihType =>
      intro m Δ σ typed
      exact .convEq (ihEquality typed) (ihType typed) universeWitness
  | headEq equal _ _ ihLeft ihRight =>
      intro m Δ σ typed
      exact .headEq equal (ihLeft typed) (ihRight typed)
  | piCong _ universeA _ universeB join ihA ihB =>
      intro m Δ σ typed
      exact .piCong (ihA typed) universeA (ihB (typed.lift _)) universeB join
  | sigmaCong _ universeA _ universeB join ihA ihB =>
      intro m Δ σ typed
      exact .sigmaCong (ihA typed) universeA (ihB (typed.lift _)) universeB join
  | idCong _ universeWitness _ _ ihA ihLeft ihRight =>
      intro m Δ σ typed
      exact .idCong (ihA typed) universeWitness (ihLeft typed) (ihRight typed)
  | lamCong _ universeWitness _ ihPi ihBody =>
      intro m Δ σ typed
      exact .lamCong (ihPi typed) universeWitness (ihBody (typed.lift _))
  | appCong _ _ ihFunction ihArgument =>
      intro m Δ σ typed
      simpa only [subst, subst_inst0] using
        (Derivable.appCong (ihFunction typed) (ihArgument typed))
  | pairCong _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ σ typed
      have second := ihSecond typed
      rw [subst_inst0] at second
      exact .pairCong (ihSigma typed) universeWitness (ihFirst typed) second
  | fstCong _ ihPair =>
      intro m Δ σ typed
      exact .fstCong (ihPair typed)
  | sndCong _ ihPair =>
      intro m Δ σ typed
      simpa only [subst, subst_inst0] using (Derivable.sndCong (ihPair typed))
  | reflCong _ ih =>
      intro m Δ σ typed
      exact .reflCong (ih typed)
  | betaPi _ universeWitness _ _ ihPi ihBody ihArgument =>
      intro m Δ σ typed
      simpa only [subst, subst_inst0] using
        (Derivable.betaPi (ihPi typed) universeWitness (ihBody (typed.lift _))
          (ihArgument typed))
  | betaFst _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ σ typed
      have second := ihSecond typed
      rw [subst_inst0] at second
      exact .betaFst (ihSigma typed) universeWitness (ihFirst typed) second
  | betaSnd _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m Δ σ typed
      have second := ihSecond typed
      rw [subst_inst0] at second
      simpa only [subst, subst_inst0] using
        (Derivable.betaSnd (ihSigma typed) universeWitness (ihFirst typed) second)
  | root step _ _ ihLeft ihRight =>
      intro m Δ σ typed
      exact .root (R.computation.substitute σ step) (ihLeft typed) (ihRight typed)
  | etaPi _ _ _ ihLeft ihRight ihBody =>
      intro m Δ σ typed
      have body := ihBody (typed.lift _)
      simp only [subst, subst_liftSub_wk, liftSub_zero] at body
      exact .etaPi (ihLeft typed) (ihRight typed) body
  | etaSigma _ _ _ _ ihLeft ihRight ihFirst ihSecond =>
      intro m Δ σ typed
      have second := ihSecond typed
      simp only [subst, subst_inst0] at second
      exact .etaSigma (ihLeft typed) (ihRight typed) (ihFirst typed) second
  | sub _ _ ihTerm ihLe =>
      intro m Δ σ typed
      exact .sub (ihTerm typed) (ihLe typed)
  | subEq _ _ ih ihLe =>
      intro m Δ σ typed
      exact .subEq (ih typed) (ihLe typed)
  | subEqual _ universeWitness ih =>
      intro m Δ σ typed
      exact .subEqual (ih typed) universeWitness
  | subUniv order =>
      intro m Δ σ typed
      exact .subUniv order
  | subPi _ universeA _ universeB _ universeW _ ihPi ihPi' ihA ihB =>
      intro m Δ σ typed
      exact .subPi (ihPi typed) universeA (ihPi' typed) universeB
        (ihA typed) universeW (ihB (typed.lift _))
  | subSigma _ universeA _ universeB _ _ ihSigma ihSigma' ihA ihB =>
      intro m Δ σ typed
      exact .subSigma (ihSigma typed) universeA (ihSigma' typed) universeB
        (ihA typed) (ihB (typed.lift _))
  | subTrans _ _ ihFirst ihSecond =>
      intro m Δ σ typed
      exact .subTrans (ihFirst typed) (ihSecond typed)

theorem Typed.substitute {R : Rules Head} {n m : Nat} {Γ : Ctx Head n}
    {Δ : Ctx Head m} {σ : Sub Head n m} {t A : Tm Head n}
    (typing : Typed R Γ t A) (typed : SubstMor R Γ Δ σ) :
    Typed R Δ (subst σ t) (subst σ A) :=
  Derivable.substitutes typing typed

theorem Equal.substitute {R : Rules Head} {n m : Nat} {Γ : Ctx Head n}
    {Δ : Ctx Head m} {σ : Sub Head n m} {a b A : Tm Head n}
    (equality : Equal R Γ a b A) (typed : SubstMor R Γ Δ σ) :
    Equal R Δ (subst σ a) (subst σ b) (subst σ A) :=
  Derivable.substitutes equality typed

/-- The substitution opening one binder at a typed argument. -/
theorem SubstMor.single {R : Rules Head} {n : Nat} {Γ : Ctx Head n}
    {A argument : Tm Head n} (typing : Typed R Γ argument A) :
    SubstMor R (.snoc Γ A) Γ (subst0 argument) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · change Typed R Γ argument (inst0 argument (Presentation.rename wk A))
    rw [inst0_rename_wk]
    exact typing
  · intro prior
    change Typed R Γ (.var prior)
      (inst0 argument (Presentation.rename wk (Ctx.lookup Γ prior)))
    rw [inst0_rename_wk]
    exact .var prior

theorem Typed.instantiate {R : Rules Head} {n : Nat} {Γ : Ctx Head n}
    {A argument : Tm Head n} {body B : Tm Head (n + 1)}
    (bodyTyping : Typed R (.snoc Γ A) body B)
    (argumentTyping : Typed R Γ argument A) :
    Typed R Γ (inst0 argument body) (inst0 argument B) :=
  bodyTyping.substitute (SubstMor.single argumentTyping)

theorem Equal.instantiate {R : Rules Head} {n : Nat} {Γ : Ctx Head n}
    {A argument : Tm Head n} {left right B : Tm Head (n + 1)}
    (equality : Equal R (.snoc Γ A) left right B)
    (argumentTyping : Typed R Γ argument A) :
    Equal R Γ (inst0 argument left) (inst0 argument right) (inst0 argument B) :=
  equality.substitute (SubstMor.single argumentTyping)

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
