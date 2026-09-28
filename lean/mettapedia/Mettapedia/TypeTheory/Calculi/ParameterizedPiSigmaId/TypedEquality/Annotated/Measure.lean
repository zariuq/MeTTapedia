import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Reduction

/-!
# Normalization of annotated terms, through their erasures

Coherence of annotations is proved by well-founded induction on the order that
takes a term to its head reducts and to its immediate subterms, the domain of an
abstraction excepted (`CSmaller`). That order is accessible from every term
whose erasure is strongly normalizing for the rule package's directed reduction
(`CSmaller.acc_of_sn`):

* for unannotated terms, reduction together with the immediate-subterm order is
  well founded on strongly normalizing terms (`Smaller.acc_of_sn`): a step of a
  subterm is a step of the whole term, and subterms are smaller;
* an annotated head step erases to a step of the directed reduction, and an
  annotated immediate subterm other than a domain erases to an immediate
  subterm (`CSmaller.erase`).

So normalization of the annotated calculus, in the form coherence uses, is
normalization of the rule package. Annotations are never reduced and never
recursed into.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open StrongNormalization (SN Reduces)

variable {Head : Type}

/-! ## Unannotated terms -/

/-- Immediate subterms, in their own contexts. -/
inductive ImmSub : (Σ n, Tm Head n) → (Σ n, Tm Head n) → Prop
  | piDom {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) : ImmSub ⟨n, A⟩ ⟨n, .pi A B⟩
  | piCod {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) : ImmSub ⟨n + 1, B⟩ ⟨n, .pi A B⟩
  | sigmaDom {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) : ImmSub ⟨n, A⟩ ⟨n, .sigma A B⟩
  | sigmaCod {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) :
      ImmSub ⟨n + 1, B⟩ ⟨n, .sigma A B⟩
  | idType {n : Nat} (A a b : Tm Head n) : ImmSub ⟨n, A⟩ ⟨n, .id A a b⟩
  | idLeft {n : Nat} (A a b : Tm Head n) : ImmSub ⟨n, a⟩ ⟨n, .id A a b⟩
  | idRight {n : Nat} (A a b : Tm Head n) : ImmSub ⟨n, b⟩ ⟨n, .id A a b⟩
  | lamBody {n : Nat} (b : Tm Head (n + 1)) : ImmSub ⟨n + 1, b⟩ ⟨n, .lam b⟩
  | appFun {n : Nat} (f a : Tm Head n) : ImmSub ⟨n, f⟩ ⟨n, .app f a⟩
  | appArg {n : Nat} (f a : Tm Head n) : ImmSub ⟨n, a⟩ ⟨n, .app f a⟩
  | pairFst {n : Nat} (a b : Tm Head n) : ImmSub ⟨n, a⟩ ⟨n, .pair a b⟩
  | pairSnd {n : Nat} (a b : Tm Head n) : ImmSub ⟨n, b⟩ ⟨n, .pair a b⟩
  | fst {n : Nat} (p : Tm Head n) : ImmSub ⟨n, p⟩ ⟨n, .fst p⟩
  | snd {n : Nat} (p : Tm Head n) : ImmSub ⟨n, p⟩ ⟨n, .snd p⟩
  | refl {n : Nat} (a : Tm Head n) : ImmSub ⟨n, a⟩ ⟨n, .refl a⟩

/-- A reduct or an immediate subterm. -/
inductive Smaller (R : Rules Head) : (Σ n, Tm Head n) → (Σ n, Tm Head n) → Prop
  | reduct {n : Nat} {t u : Tm Head n} : Reduces R t u → Smaller R ⟨n, u⟩ ⟨n, t⟩
  | sub {x y : Σ n, Tm Head n} : ImmSub x y → Smaller R x y

/-- The number of formers of a term. -/
def termSize {n : Nat} : Tm Head n → Nat
  | .var _ => 1
  | .const _ => 1
  | .head _ => 1
  | .pi A B => termSize A + termSize B + 1
  | .sigma A B => termSize A + termSize B + 1
  | .id A a b => termSize A + termSize a + termSize b + 1
  | .lam b => termSize b + 1
  | .app f a => termSize f + termSize a + 1
  | .pair a b => termSize a + termSize b + 1
  | .fst p => termSize p + 1
  | .snd p => termSize p + 1
  | .refl a => termSize a + 1

theorem ImmSub.size_lt {x y : Σ n, Tm Head n} (sub : ImmSub x y) :
    termSize x.2 < termSize y.2 := by
  cases sub <;> simp only [termSize] <;> omega

variable {R : Rules Head}

/-- A step of an immediate subterm is a step of the term. -/
theorem ImmSub.lift {x y : Σ n, Tm Head n} (sub : ImmSub x y) {s : Tm Head x.1}
    (step : Reduces R x.2 s) : ∃ t', Reduces R y.2 t' ∧ ImmSub ⟨x.1, s⟩ ⟨y.1, t'⟩ := by
  cases sub with
  | piDom A B => exact ⟨_, .congPiDom step, .piDom s B⟩
  | piCod A B => exact ⟨_, .congPiCod step, .piCod A s⟩
  | sigmaDom A B => exact ⟨_, .congSigmaDom step, .sigmaDom s B⟩
  | sigmaCod A B => exact ⟨_, .congSigmaCod step, .sigmaCod A s⟩
  | idType A a b => exact ⟨_, .congIdTy step, .idType s a b⟩
  | idLeft A a b => exact ⟨_, .congIdLeft step, .idLeft A s b⟩
  | idRight A a b => exact ⟨_, .congIdRight step, .idRight A a s⟩
  | lamBody b => exact ⟨_, .congLam step, .lamBody s⟩
  | appFun f a => exact ⟨_, .congAppFun step, .appFun s a⟩
  | appArg f a => exact ⟨_, .congAppArg step, .appArg f s⟩
  | pairFst a b => exact ⟨_, .congPairFst step, .pairFst s b⟩
  | pairSnd a b => exact ⟨_, .congPairSnd step, .pairSnd a s⟩
  | fst p => exact ⟨_, .congFst step, .fst s⟩
  | snd p => exact ⟨_, .congSnd step, .snd s⟩
  | refl a => exact ⟨_, .congRefl step, .refl s⟩

/-- A step of a subterm is a step of the term. -/
theorem subterm_lift {x y : Σ n, Tm Head n} (sub : Relation.ReflTransGen ImmSub x y)
    {s : Tm Head x.1} (step : Reduces R x.2 s) :
    ∃ t', Reduces R y.2 t' ∧ Relation.ReflTransGen ImmSub ⟨x.1, s⟩ ⟨y.1, t'⟩ := by
  induction sub with
  | refl => exact ⟨s, step, .refl⟩
  | tail _ last ih =>
      obtain ⟨b', stepB, subB⟩ := ih
      obtain ⟨c', stepC, subC⟩ := last.lift stepB
      exact ⟨c', stepC, .tail subB subC⟩

/-- **Reduction and immediate subterms are well founded on strongly
normalizing terms.** -/
theorem Smaller.acc_of_sn {n : Nat} {t : Tm Head n} (sn : SN R t) :
    Acc (Smaller R) ⟨n, t⟩ := by
  suffices key : ∀ x, Relation.ReflTransGen ImmSub x ⟨n, t⟩ → Acc (Smaller R) x from
    key _ .refl
  induction sn with
  | intro t _ ihSN =>
      suffices ∀ k (x : Σ m, Tm Head m), termSize x.2 < k →
          Relation.ReflTransGen ImmSub x ⟨n, t⟩ → Acc (Smaller R) x from
        fun x hx => this _ x (Nat.lt_succ_self _) hx
      intro k
      induction k with
      | zero => exact fun x hk => absurd hk (Nat.not_lt_zero _)
      | succ k ihk =>
          intro x hk hx
          constructor
          intro y hy
          cases hy with
          | reduct step =>
              obtain ⟨t', stepT, hy'⟩ := subterm_lift hx step
              exact ihSN t' stepT _ hy'
          | sub sub =>
              have := sub.size_lt
              exact ihk y (by omega) (.head sub hx)

/-! ## Annotated terms -/

/-- Immediate subterms of an annotated term, except the domain of an
abstraction. -/
inductive CImmSub : (Σ n, CTm Head n) → (Σ n, CTm Head n) → Prop
  | piDom {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) : CImmSub ⟨n, A⟩ ⟨n, .pi A B⟩
  | piCod {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) : CImmSub ⟨n + 1, B⟩ ⟨n, .pi A B⟩
  | sigmaDom {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) :
      CImmSub ⟨n, A⟩ ⟨n, .sigma A B⟩
  | sigmaCod {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) :
      CImmSub ⟨n + 1, B⟩ ⟨n, .sigma A B⟩
  | idType {n : Nat} (A a b : CTm Head n) : CImmSub ⟨n, A⟩ ⟨n, .id A a b⟩
  | idLeft {n : Nat} (A a b : CTm Head n) : CImmSub ⟨n, a⟩ ⟨n, .id A a b⟩
  | idRight {n : Nat} (A a b : CTm Head n) : CImmSub ⟨n, b⟩ ⟨n, .id A a b⟩
  | lamBody {n : Nat} (A : CTm Head n) (b : CTm Head (n + 1)) : CImmSub ⟨n + 1, b⟩ ⟨n, .lam A b⟩
  | appFun {n : Nat} (f a : CTm Head n) : CImmSub ⟨n, f⟩ ⟨n, .app f a⟩
  | appArg {n : Nat} (f a : CTm Head n) : CImmSub ⟨n, a⟩ ⟨n, .app f a⟩
  | pairFst {n : Nat} (a b : CTm Head n) : CImmSub ⟨n, a⟩ ⟨n, .pair a b⟩
  | pairSnd {n : Nat} (a b : CTm Head n) : CImmSub ⟨n, b⟩ ⟨n, .pair a b⟩
  | fst {n : Nat} (p : CTm Head n) : CImmSub ⟨n, p⟩ ⟨n, .fst p⟩
  | snd {n : Nat} (p : CTm Head n) : CImmSub ⟨n, p⟩ ⟨n, .snd p⟩
  | refl {n : Nat} (a : CTm Head n) : CImmSub ⟨n, a⟩ ⟨n, .refl a⟩

/-- A head reduct or an immediate subterm other than a domain. -/
inductive CSmaller : (Σ n, CTm Head n) → (Σ n, CTm Head n) → Prop
  | step {n : Nat} {t u : CTm Head n} : CWhStep t u → CSmaller ⟨n, u⟩ ⟨n, t⟩
  | sub {x y : Σ n, CTm Head n} : CImmSub x y → CSmaller x y

/-- Erasure of a term of any context length. -/
def eraseAny (x : Σ n, CTm Head n) : Σ n, Tm Head n := ⟨x.1, x.2.erase⟩

theorem CImmSub.erase {x y : Σ n, CTm Head n} (sub : CImmSub x y) :
    ImmSub (eraseAny x) (eraseAny y) := by
  cases sub with
  | piDom A B => exact .piDom _ _
  | piCod A B => exact .piCod _ _
  | sigmaDom A B => exact .sigmaDom _ _
  | sigmaCod A B => exact .sigmaCod _ _
  | idType A a b => exact .idType _ _ _
  | idLeft A a b => exact .idLeft _ _ _
  | idRight A a b => exact .idRight _ _ _
  | lamBody A b => exact .lamBody _
  | appFun f a => exact .appFun _ _
  | appArg f a => exact .appArg _ _
  | pairFst a b => exact .pairFst _ _
  | pairSnd a b => exact .pairSnd _ _
  | fst p => exact .fst _
  | snd p => exact .snd _
  | refl a => exact .refl _

theorem CSmaller.erase {x y : Σ n, CTm Head n} (smaller : CSmaller x y) :
    Smaller R (eraseAny x) (eraseAny y) := by
  cases smaller with
  | step step => exact .reduct step.erase_reduces
  | sub sub => exact .sub sub.erase

/-- **Normalization through erasure**: the order of head reducts and
immediate subterms is accessible from every annotated term whose erasure is
strongly normalizing. -/
theorem CSmaller.acc_of_sn {n : Nat} {t : CTm Head n} (sn : SN R t.erase) :
    Acc CSmaller ⟨n, t⟩ :=
  Subrelation.accessible (fun smaller => CSmaller.erase (R := R) smaller)
    (InvImage.accessible eraseAny (Smaller.acc_of_sn sn))

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
