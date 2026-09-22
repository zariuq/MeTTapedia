import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction

/-!
# Regular judgments for the two-sort Pi/Sigma/Id fragment

This module defines declaration-free conversion, regular typing, and context
formation directly on the scoped intrinsic syntax. Its rules use one ground
type `u0` and one untyped formation marker `u1`; they do not provide a universe
hierarchy, quantification over types, or identity elimination.

The complete judgment pairs typing with a regular-context derivation.
Quotation into Pattern syntax and comparisons with more permissive typing
relations are separate adapters, not prerequisites of these definitions.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution

/-! ## Declaration-free syntax -/

/-- The intrinsic terms containing no global declaration constants.

This structural restriction is independent of any external presentation or
choice of declaration environment. -/
inductive ConstantFree : ScopedTerm n → Prop where
  | var (i : Fin n) : ConstantFree (.var i)
  | u0 : ConstantFree .u0
  | u1 : ConstantFree .u1
  | pi : ConstantFree A → ConstantFree B → ConstantFree (.pi A B)
  | sigma : ConstantFree A → ConstantFree B → ConstantFree (.sigma A B)
  | id : ConstantFree A → ConstantFree a → ConstantFree b → ConstantFree (.id A a b)
  | lam : ConstantFree body → ConstantFree (.lam body)
  | app : ConstantFree f → ConstantFree a → ConstantFree (.app f a)
  | pair : ConstantFree a → ConstantFree b → ConstantFree (.pair a b)
  | fst : ConstantFree p → ConstantFree (.fst p)
  | snd : ConstantFree p → ConstantFree (.snd p)
  | refl : ConstantFree a → ConstantFree (.refl a)

/-- Renaming cannot introduce a declaration constant. -/
theorem ConstantFree.rename {t : ScopedTerm n} (h : ConstantFree t) (ρ : Ren n m) :
    ConstantFree (rename ρ t) := by
  induction h generalizing m with
  | var i => exact .var (ρ i)
  | u0 => exact .u0
  | u1 => exact .u1
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB (liftRen ρ))
  | sigma _ _ ihA ihB => exact .sigma (ihA ρ) (ihB (liftRen ρ))
  | id _ _ _ ihA iha ihb => exact .id (ihA ρ) (iha ρ) (ihb ρ)
  | lam _ ih => exact .lam (ih (liftRen ρ))
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | pair _ _ iha ihb => exact .pair (iha ρ) (ihb ρ)
  | fst _ ih => exact .fst (ih ρ)
  | snd _ ih => exact .snd (ih ρ)
  | refl _ ih => exact .refl (ih ρ)

/-- Every type stored in a declaration-free telescope is declaration-free. -/
def ConstantFreeCtx : Ctx n → Prop
  | .nil => True
  | .snoc Γ A => ConstantFreeCtx Γ ∧ ConstantFree A

theorem ConstantFreeCtx.lookup {Γ : Ctx n} (hΓ : ConstantFreeCtx Γ) (i : Fin n) :
    ConstantFree (lookup Γ i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A ih =>
      rcases hΓ with ⟨hΓ, hA⟩
      refine Fin.cases ?_ ?_ i
      · exact hA.rename wk
      · intro j
        exact (ih hΓ j).rename wk

/-! `inst0` is substitution, not application.  These lemmas keep the syntax
boundary proof honest without conflating those operations. -/

theorem ConstantFree.subst {t : ScopedTerm n} {σ : Sub n m} (ht : ConstantFree t)
    (hσ : ∀ i, ConstantFree (σ i)) : ConstantFree (subst σ t) := by
  induction ht generalizing m with
  | var i => exact hσ i
  | u0 => exact .u0
  | u1 => exact .u1
  | pi _ _ ihA ihB =>
      exact .pi (ihA hσ) (ihB (fun i => Fin.cases (.var 0) (fun j => (hσ j).rename wk) i))
  | sigma _ _ ihA ihB =>
      exact .sigma (ihA hσ) (ihB (fun i => Fin.cases (.var 0) (fun j => (hσ j).rename wk) i))
  | id _ _ _ ihA iha ihb => exact .id (ihA hσ) (iha hσ) (ihb hσ)
  | lam _ ih => exact .lam (ih (fun i => Fin.cases (.var 0) (fun j => (hσ j).rename wk) i))
  | app _ _ ihf iha => exact .app (ihf hσ) (iha hσ)
  | pair _ _ iha ihb => exact .pair (iha hσ) (ihb hσ)
  | fst _ ih => exact .fst (ih hσ)
  | snd _ ih => exact .snd (ih hσ)
  | refl _ ih => exact .refl (ih hσ)

theorem ConstantFree.inst0 {a : ScopedTerm n} {B : ScopedTerm (n + 1)}
    (ha : ConstantFree a) (hB : ConstantFree B) :
    ConstantFree (inst0 a B) := by
  exact hB.subst (fun i => Fin.cases ha (fun j => .var j) i)

/-! ## The regular intensional typing spine -/

/-- One intrinsic reduction step between declaration-free terms. -/
def ConstantFreeRed (t u : ScopedTerm n) : Prop :=
  Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red t u ∧
    ConstantFree t ∧ ConstantFree u

/-- Definitional equality internal to the exact common fragment.

Every constructor carries enough evidence to keep the whole proof object in
the fragment, including reflexivity.  Merely applying `Relation.EqvGen` to a
restricted edge relation would make reflexivity available for arbitrary
constant-bearing terms. -/
inductive ConstantFreeConv : ScopedTerm n → ScopedTerm n → Prop where
  | rel {t u : ScopedTerm n} : ConstantFreeRed t u → ConstantFreeConv t u
  | refl (t : ScopedTerm n) : ConstantFree t → ConstantFreeConv t t
  | symm {t u : ScopedTerm n} : ConstantFreeConv t u → ConstantFreeConv u t
  | trans {t u v : ScopedTerm n} :
      ConstantFreeConv t u → ConstantFreeConv u v → ConstantFreeConv t v

/-- Fragment-internal conversion implies the equivalence closure of reduction. -/
theorem ConstantFreeConv.toConv {t u : ScopedTerm n} (h : ConstantFreeConv t u) :
    Relation.EqvGen
      (@Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red n) t u := by
  induction h with
  | rel hred => exact .rel _ _ hred.1
  | refl x _ => exact .refl x
  | symm hxy ih => exact .symm _ _ ih
  | trans hxy hyz ihxy ihyz => exact .trans _ _ _ ihxy ihyz

/-- Both endpoints of a fragment-internal conversion remain in the common
syntax.  This is stronger than endpoint-only filtering of a raw conversion:
the induction also certifies every intermediate term carried by the proof
object. -/
theorem ConstantFreeConv.constantFree_both {t u : ScopedTerm n}
    (h : ConstantFreeConv t u) : ConstantFree t ∧ ConstantFree u := by
  induction h with
  | rel hred => exact hred.2
  | refl _ ht => exact ⟨ht, ht⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ihxy ihyz => exact ⟨ihxy.1, ihyz.2⟩

/-- Regular intrinsic typing with explicit formation presuppositions.

Rules consuming a dependent codomain retain its formation derivation.
Conversion targets are formed types or the distinguished untyped top sort.
Context formation is supplied separately by `RegularJudgment`. -/
inductive RegularHasType : Ctx n → ScopedTerm n → ScopedTerm n → Prop where
  | u0_type (Γ : Ctx n) : RegularHasType Γ .u0 .u1
  | var {Γ : Ctx n} (i : Fin n) : RegularHasType Γ (.var i) (lookup Γ i)
  | pi_form {Γ : Ctx n} {A : ScopedTerm n} {B : ScopedTerm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.pi A B) .u1
  | sigma_form {Γ : Ctx n} {A : ScopedTerm n} {B : ScopedTerm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.sigma A B) .u1
  | lam_intro {Γ : Ctx n} {A : ScopedTerm n} {body B : ScopedTerm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType (.snoc Γ A) body B →
      RegularHasType Γ (.lam body) (.pi A B)
  | app_elim {Γ : Ctx n} {f a A : ScopedTerm n} {B : ScopedTerm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ f (.pi A B) →
      RegularHasType Γ a A →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.app f a) (inst0 a B)
  | pair_intro {Γ : Ctx n} {a b A : ScopedTerm n} {B : ScopedTerm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ a A →
      RegularHasType Γ b (inst0 a B) →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.pair a b) (.sigma A B)
  | fst_elim {Γ : Ctx n} {p A : ScopedTerm n} {B : ScopedTerm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ p (.sigma A B) →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.fst p) A
  | snd_elim {Γ : Ctx n} {p A : ScopedTerm n} {B : ScopedTerm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ p (.sigma A B) →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.snd p) (inst0 (.fst p) B)
  | id_form {Γ : Ctx n} {A a b : ScopedTerm n} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ a A →
      RegularHasType Γ b A →
      RegularHasType Γ (.id A a b) .u1
  | refl_intro {Γ : Ctx n} {a A : ScopedTerm n} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ a A →
      RegularHasType Γ (.refl a) (.id A a a)
  /-- Conversion into an independently formed ordinary type. -/
  | conv_type {Γ : Ctx n} {t A B : ScopedTerm n} :
      RegularHasType Γ t A →
      RegularHasType Γ B .u1 →
      ConstantFreeConv A B →
      RegularHasType Γ t B
  /-- Conversion into the top sort is separated because `U1` has no type in
  this two-sort fragment. -/
  | conv_sort {Γ : Ctx n} {t A : ScopedTerm n} :
      RegularHasType Γ t A →
      ConstantFreeConv A .u1 →
      RegularHasType Γ t .u1

/-- In a declaration-free context, the whole regular typing derivation stays
inside the declaration-free syntax. -/
theorem RegularHasType.constantFree_both (h : RegularHasType Γ t A)
    (hΓ : ConstantFreeCtx Γ) : ConstantFree t ∧ ConstantFree A := by
  induction h with
  | u0_type => exact ⟨.u0, .u1⟩
  | var i => exact ⟨.var i, hΓ.lookup i⟩
  | pi_form hA hB ihA ihB =>
      have pA := ihA hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      exact ⟨.pi pA.1 pB.1, .u1⟩
  | sigma_form hA hB ihA ihB =>
      have pA := ihA hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      exact ⟨.sigma pA.1 pB.1, .u1⟩
  | lam_intro hA hB hBody ihA ihB ihBody =>
      have pA := ihA hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      have pBody := ihBody ⟨hΓ, pA.1⟩
      exact ⟨.lam pBody.1, .pi pA.1 pB.1⟩
  | app_elim hA hf ha hB ihA ihf iha ihB =>
      have pA := ihA hΓ
      have pf := ihf hΓ
      have pa := iha hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      exact ⟨.app pf.1 pa.1, ConstantFree.inst0 pa.1 pB.1⟩
  | pair_intro hA ha hb hB ihA iha ihb ihB =>
      have pA := ihA hΓ
      have pa := iha hΓ
      have pb := ihb hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      exact ⟨.pair pa.1 pb.1, .sigma pA.1 pB.1⟩
  | fst_elim hA hp hB ihA ihp ihB =>
      have pp := ihp hΓ
      cases pp.2 with
      | sigma hA hCod => exact ⟨.fst pp.1, hA⟩
  | snd_elim hA hp hB ihA ihp ihB =>
      have pA := ihA hΓ
      have pp := ihp hΓ
      cases pp.2 with
      | sigma hA hCod =>
          have pB := ihB ⟨hΓ, pA.1⟩
          exact ⟨.snd pp.1, ConstantFree.inst0 (.fst pp.1) pB.1⟩
  | id_form hA ha hb ihA iha ihb =>
      have pA := ihA hΓ
      have pa := iha hΓ
      have pb := ihb hΓ
      exact ⟨.id pA.1 pa.1 pb.1, .u1⟩
  | refl_intro hA ha ihA iha =>
      have pA := ihA hΓ
      have pa := iha hΓ
      exact ⟨.refl pa.1, .id pA.1 pa.1 pa.1⟩
  | conv_type ht hB hconv iht ihB =>
      have pt := iht hΓ
      have pB := ihB hΓ
      exact ⟨pt.1, pB.1⟩
  | conv_sort ht hconv iht =>
      have pt := iht hΓ
      exact ⟨pt.1, .u1⟩

/-! ### Context formation and the actual judgment boundary

`Ctx` remains useful raw syntax.  A kernel context is a telescope together
with a derivation that every extension is a type in the preceding context.
This blocks malformed assumptions before variable lookup can turn them into
apparently typed terms. -/

/-- Presupposition-closed context formation for the regular spine. -/
inductive RegularCtx : {n : Nat} → Ctx n → Prop where
  | nil : RegularCtx (.nil : Ctx 0)
  | snoc {Γ : Ctx n} {A : ScopedTerm n} :
      RegularCtx Γ →
      RegularHasType Γ A .u1 →
      RegularCtx (.snoc Γ A)

/-- Every type stored in a regular context belongs to the declaration-free syntax.
The result follows from the context-formation derivations, rather than being
an independent side condition. -/
theorem RegularCtx.constantFreeCtx {Γ : Ctx n} (hΓ : RegularCtx Γ) :
    ConstantFreeCtx Γ := by
  induction hΓ with
  | nil => trivial
  | snoc hΓ hA ih =>
      exact ⟨ih, (hA.constantFree_both ih).1⟩

/-- A regular judgment carries context formation, rather than accepting an
arbitrary raw telescope by convention. -/
structure RegularJudgment (Γ : Ctx n) (t A : ScopedTerm n) : Prop where
  context : RegularCtx Γ
  typing : RegularHasType Γ t A

/-! ### Least rule closure, not a greatest fixpoint

The finite proof objects generated by the rules form an inductive least
closure.  Calling this a greatest fixpoint would incorrectly admit cyclic or
infinite derivations.  Calling it a coreflection additionally requires a
category of presentations and an adjunction; no such claim is made here. -/

/-- An intrinsic typing relation indexed by the context length. -/
abbrev TypingRelation :=
  {n : Nat} → Ctx n → ScopedTerm n → ScopedTerm n → Prop

/-- Pointwise inclusion between intrinsic typing relations. -/
def TypingRelation.LE (R S : TypingRelation) : Prop :=
  ∀ {n : Nat} {Γ : Ctx n} {t A : ScopedTerm n}, R Γ t A → S Γ t A

/-- Closure under exactly the presupposition-complete regular rules. -/
structure RegularRuleModel (R : TypingRelation) where
  u0_type : ∀ {n : Nat} (Γ : Ctx n), R Γ .u0 .u1
  var : ∀ {n : Nat} {Γ : Ctx n} (i : Fin n), R Γ (.var i) (lookup Γ i)
  pi_form : ∀ {n : Nat} {Γ : Ctx n} {A : ScopedTerm n} {B : ScopedTerm (n + 1)},
    R Γ A .u1 → R (.snoc Γ A) B .u1 → R Γ (.pi A B) .u1
  sigma_form : ∀ {n : Nat} {Γ : Ctx n} {A : ScopedTerm n} {B : ScopedTerm (n + 1)},
    R Γ A .u1 → R (.snoc Γ A) B .u1 → R Γ (.sigma A B) .u1
  lam_intro : ∀ {n : Nat} {Γ : Ctx n} {A : ScopedTerm n}
      {body B : ScopedTerm (n + 1)},
    R Γ A .u1 → R (.snoc Γ A) B .u1 → R (.snoc Γ A) body B →
      R Γ (.lam body) (.pi A B)
  app_elim : ∀ {n : Nat} {Γ : Ctx n} {f a A : ScopedTerm n}
      {B : ScopedTerm (n + 1)},
    R Γ A .u1 → R Γ f (.pi A B) → R Γ a A → R (.snoc Γ A) B .u1 →
      R Γ (.app f a) (inst0 a B)
  pair_intro : ∀ {n : Nat} {Γ : Ctx n} {a b A : ScopedTerm n}
      {B : ScopedTerm (n + 1)},
    R Γ A .u1 → R Γ a A → R Γ b (inst0 a B) →
      R (.snoc Γ A) B .u1 →
      R Γ (.pair a b) (.sigma A B)
  fst_elim : ∀ {n : Nat} {Γ : Ctx n} {p A : ScopedTerm n}
      {B : ScopedTerm (n + 1)},
    R Γ A .u1 → R Γ p (.sigma A B) → R (.snoc Γ A) B .u1 →
      R Γ (.fst p) A
  snd_elim : ∀ {n : Nat} {Γ : Ctx n} {p A : ScopedTerm n}
      {B : ScopedTerm (n + 1)},
    R Γ A .u1 → R Γ p (.sigma A B) → R (.snoc Γ A) B .u1 →
      R Γ (.snd p) (inst0 (.fst p) B)
  id_form : ∀ {n : Nat} {Γ : Ctx n} {A a b : ScopedTerm n},
    R Γ A .u1 → R Γ a A → R Γ b A → R Γ (.id A a b) .u1
  refl_intro : ∀ {n : Nat} {Γ : Ctx n} {a A : ScopedTerm n},
    R Γ A .u1 → R Γ a A → R Γ (.refl a) (.id A a a)
  conv_type : ∀ {n : Nat} {Γ : Ctx n} {t A B : ScopedTerm n},
    R Γ t A → R Γ B .u1 →
      ConstantFreeConv A B → R Γ t B
  conv_sort : ∀ {n : Nat} {Γ : Ctx n} {t A : ScopedTerm n},
    R Γ t A →
      ConstantFreeConv A .u1 → R Γ t .u1

/-- The regular judgment is contained in every relation closed under its
rules. This is the least inductive rule closure. -/
theorem RegularHasType.least {R : TypingRelation} (model : RegularRuleModel R) :
    TypingRelation.LE (fun Γ t A => RegularHasType Γ t A) R := by
  intro n Γ t A derivation
  induction derivation with
  | u0_type Γ => exact model.u0_type Γ
  | var i => exact model.var i
  | pi_form hA hB ihA ihB => exact model.pi_form ihA ihB
  | sigma_form hA hB ihA ihB => exact model.sigma_form ihA ihB
  | lam_intro hA hB hBody ihA ihB ihBody =>
      exact model.lam_intro ihA ihB ihBody
  | app_elim hA hf ha hB ihA ihf iha ihB =>
      exact model.app_elim ihA ihf iha ihB
  | pair_intro hA ha hb hB ihA iha ihb ihB =>
      exact model.pair_intro ihA iha ihb ihB
  | fst_elim hA hp hB ihA ihp ihB => exact model.fst_elim ihA ihp ihB
  | snd_elim hA hp hB ihA ihp ihB => exact model.snd_elim ihA ihp ihB
  | id_form hA ha hb ihA iha ihb => exact model.id_form ihA iha ihb
  | refl_intro hA ha ihA iha => exact model.refl_intro ihA iha
  | conv_type ht hB hconv iht ihB => exact model.conv_type iht ihB hconv
  | conv_sort ht hconv iht => exact model.conv_sort iht hconv

/-! ## Positive and negative typing witnesses -/

/-- The regular spine contains the ordinary identity function. -/
theorem regular_identity :
    RegularHasType (.nil : Ctx 0) (.lam (.var 0)) (.pi .u0 .u0) := by
  exact .lam_intro (.u0_type .nil) (.u0_type _) (.var 0)

theorem RegularHasType.subject_ne_u1 (h : RegularHasType Γ t A) : t ≠ .u1 := by
  induction h <;> simp_all

theorem no_regular_u1_term {Γ : Ctx n} {A : ScopedTerm n}
    (h : RegularHasType Γ .u1 A) : False :=
  h.subject_ne_u1 rfl

/-- A Pi whose domain is the untyped top sort cannot itself be assigned any
type by the regular rules.  Conversion cannot conceal the missing premise:
its source derivation is structurally smaller, and conversion into an
ordinary target separately requires target formation. -/
theorem RegularHasType.subject_ne_pi_u1_domain
    (h : RegularHasType Γ t A) : t ≠ (.pi .u1 .u1) := by
  induction h with
  | pi_form hDom hCod ihDom ihCod =>
      intro equal
      cases equal
      exact hDom.subject_ne_u1 rfl
  | conv_type ht hB hconv iht ihB => exact iht
  | conv_sort ht hconv iht => exact iht
  | u0_type => simp
  | var => simp
  | sigma_form => simp
  | lam_intro => simp
  | app_elim => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

theorem no_regular_pi_u1_domain {Γ : Ctx n} {A : ScopedTerm n}
    (h : RegularHasType Γ (.pi .u1 .u1) A) : False :=
  h.subject_ne_pi_u1_domain rfl

/-- A lambda whose body is the untyped top sort cannot be assigned a type by
the regular rules. -/
theorem RegularHasType.subject_ne_lam_u1
    (h : RegularHasType Γ t A) : t ≠ (.lam .u1) := by
  induction h with
  | lam_intro hDom hCod hBody ihDom ihCod ihBody =>
      intro equal
      cases equal
      exact hBody.subject_ne_u1 rfl
  | conv_type ht hB hconv iht ihB => exact iht
  | conv_sort ht hconv iht => exact iht
  | u0_type => simp
  | var => simp
  | pi_form => simp
  | sigma_form => simp
  | app_elim => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

/-- Consequently the beta-redex whose function is that malformed lambda
cannot itself be assigned a type by the regular rules. -/
theorem RegularHasType.subject_ne_untyped_beta_redex
    (h : RegularHasType Γ t A) :
    t ≠ (.app (.lam .u1) .u0) := by
  induction h with
  | app_elim hA hf ha hB ihA ihf iha ihB =>
      intro equal
      cases equal
      exact hf.subject_ne_lam_u1 rfl
  | conv_type ht hB hconv iht ihB => exact iht
  | conv_sort ht hconv iht => exact iht
  | u0_type => simp
  | var => simp
  | pi_form => simp
  | sigma_form => simp
  | lam_intro => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

/-- An exact common-fragment term which is definitionally equal to `U1`, but
is not itself a well-formed type. -/
def untypedBetaType : ScopedTerm 0 :=
  .app (.lam .u1) .u0

theorem untypedBetaType_not_formed :
    ¬ RegularHasType (.nil : Ctx 0) untypedBetaType .u1 := by
  intro h
  exact h.subject_ne_untyped_beta_redex rfl

/-- The regular kernel cannot type `U0` at the unformed beta-redex type. -/
theorem regular_rejects_conversion_to_unformed_type :
    ¬ RegularHasType (.nil : Ctx 0) .u0 untypedBetaType := by
  intro h
  cases h with
  | conv_type ht hB hconv => exact untypedBetaType_not_formed hB

/-- The regular rules reject a lambda whose domain is the untyped top sort. -/
theorem regular_rejects_untyped_lambda_domain :
    ¬ RegularHasType (.nil : Ctx 0) (.lam (.var 0)) (.pi .u1 .u1) := by
  intro h
  cases h with
  | lam_intro hA hB hBody => exact no_regular_u1_term hA
  | conv_type ht hB hconv => exact no_regular_pi_u1_domain hB

/-- The smallest nonempty regular context. -/
theorem regularCtx_u0 : RegularCtx (.snoc .nil .u0) :=
  .snoc .nil (.u0_type .nil)

/-- Positive nondegeneracy witness at the full judgment boundary. -/
theorem regular_identity_judgment :
    RegularJudgment (.nil : Ctx 0) (.lam (.var 0)) (.pi .u0 .u0) :=
  ⟨.nil, regular_identity⟩

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular

