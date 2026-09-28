import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural

/-!
# Functionality of typing

A typed term, substituted by two pointwise equal substitutions, gives equal
terms. The first substitution must be typed; the second needs no typing of its
own. The proof is one induction over typing derivations and uses only the
substitution law, so it holds for every rule package.

The main use is opening a binder at two equal arguments: `B[x] ≡ B[y]` when
`x ≡ y`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

variable {Head : Type}

/-- Two substitutions into `Δ` that agree up to equality at the types the first
one assigns. -/
def SubstEq (R : Rules Head) {n m : Nat} (Γ : Ctx Head n) (Δ : Ctx Head m)
    (σ τ : Sub Head n m) : Prop :=
  SubstMor R Γ Δ σ ∧ ∀ index, Equal R Δ (σ index) (τ index) (subst σ (Ctx.lookup Γ index))

theorem SubstEq.lift {R : Rules Head} {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ τ : Sub Head n m} (equal : SubstEq R Γ Δ σ τ) (A : Tm Head n) :
    SubstEq R (.snoc Γ A) (.snoc Δ (subst σ A)) (liftSub σ) (liftSub τ) := by
  refine ⟨equal.1.lift A, ?_⟩
  intro index
  refine Fin.cases ?_ ?_ index
  · have := equal.1.lift A 0
    simp only [liftSub_zero] at this ⊢
    exact .refl this
  · intro prior
    simpa only [liftSub_succ, Ctx.lookup_snoc_succ, subst_liftSub_wk] using
      (Equal.weaken (extension := subst σ A) (equal.2 prior))

/-- What functionality gives for a statement. -/
abbrev Statement.Functional (R : Rules Head) : Statement Head → Prop
  | .typing Γ t A => ∀ {m : Nat} {Δ : Ctx Head m} {σ τ : Sub Head _ m},
      SubstEq R Γ Δ σ τ → Equal R Δ (subst σ t) (subst τ t) (subst σ A)
  | .equality _ _ _ _ => True
  | .sub _ _ _ => True

theorem Derivable.functional {R : Rules Head} {statement : Statement Head}
    (derivation : Derivable R statement) : statement.Functional R := by
  induction derivation with
  | headType head =>
      intro m Δ σ τ equal
      exact .refl (.headType head)
  | var index =>
      intro m Δ σ τ equal
      exact equal.2 index
  | const known formed universeWitness _ =>
      intro m Δ σ τ equal
      simpa only [subst, subst_liftClosed] using
        (Derivable.refl (Derivable.const (Γ := Δ) known formed universeWitness))
  | piForm typeA universeA typeB universeB join ihA ihB =>
      intro m Δ σ τ equal
      exact .piCong (ihA equal) universeA (ihB (equal.lift _)) universeB join
  | sigmaForm typeA universeA typeB universeB join ihA ihB =>
      intro m Δ σ τ equal
      exact .sigmaCong (ihA equal) universeA (ihB (equal.lift _)) universeB join
  | lamIntro pi universeWitness body _ ihBody =>
      intro m Δ σ τ equal
      exact .lamCong (Typed.substitute pi equal.1) universeWitness (ihBody (equal.lift _))
  | appElim _ _ ihFunction ihArgument =>
      intro m Δ σ τ equal
      simpa only [subst, subst_inst0] using
        (Derivable.appCong (ihFunction equal) (ihArgument equal))
  | pairIntro sigma universeWitness _ _ _ ihFirst ihSecond =>
      intro m Δ σ τ equal
      have second := ihSecond equal
      rw [subst_inst0] at second
      exact .pairCong (Typed.substitute sigma equal.1) universeWitness (ihFirst equal) second
  | fstElim _ ihPair =>
      intro m Δ σ τ equal
      exact .fstCong (ihPair equal)
  | sndElim _ ihPair =>
      intro m Δ σ τ equal
      simpa only [subst, subst_inst0] using (Derivable.sndCong (ihPair equal))
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      intro m Δ σ τ equal
      exact .idCong (ihA equal) universeWitness (ihLeft equal) (ihRight equal)
  | reflIntro _ ihTerm =>
      intro m Δ σ τ equal
      exact .reflCong (ihTerm equal)
  | sub _ le ihTerm _ =>
      intro m Δ σ τ equal
      exact .subEq (ihTerm equal) (Derivable.substitutes le equal.1)
  | conv _ typeEquality universeWitness ihTerm _ =>
      intro m Δ σ τ equal
      exact .convEq (ihTerm equal) (Equal.substitute typeEquality equal.1) universeWitness
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | convEq => trivial
  | headEq => trivial
  | piCong => trivial
  | sigmaCong => trivial
  | idCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | pairCong => trivial
  | fstCong => trivial
  | sndCong => trivial
  | reflCong => trivial
  | betaPi => trivial
  | betaFst => trivial
  | betaSnd => trivial
  | root => trivial
  | etaPi => trivial
  | etaSigma => trivial
  | subEq => trivial
  | subEqual => trivial
  | subUniv => trivial
  | subPi => trivial
  | subSigma => trivial
  | subTrans => trivial

theorem Typed.functional {R : Rules Head} {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ τ : Sub Head n m} {t A : Tm Head n} (typing : Typed R Γ t A)
    (equal : SubstEq R Γ Δ σ τ) : Equal R Δ (subst σ t) (subst τ t) (subst σ A) :=
  Derivable.functional typing equal

/-- Opening a binder at two equal arguments gives equal results. -/
theorem Typed.instantiateEq {R : Rules Head} {n : Nat} {Γ : Ctx Head n}
    {A x y : Tm Head n} {body B : Tm Head (n + 1)}
    (typing : Typed R (.snoc Γ A) body B) (argument : Typed R Γ x A)
    (equal : Equal R Γ x y A) :
    Equal R Γ (inst0 x body) (inst0 y body) (inst0 x B) := by
  apply typing.functional
  refine ⟨SubstMor.single argument, ?_⟩
  intro index
  refine Fin.cases ?_ ?_ index
  · change Equal R Γ x y (inst0 x (Presentation.rename wk A))
    rw [inst0_rename_wk]
    exact equal
  · intro prior
    change Equal R Γ (.var prior) (.var prior)
      (inst0 x (Presentation.rename wk (Ctx.lookup Γ prior)))
    rw [inst0_rename_wk]
    exact .refl (.var prior)

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
