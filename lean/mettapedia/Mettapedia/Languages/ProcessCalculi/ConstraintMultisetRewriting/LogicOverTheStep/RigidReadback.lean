import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPrograms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.TypedInterpreter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.RecursiveRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.SigmaIdentity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Readback

/-!
# Readback for the dependent programs: rigid spines determine their arguments

Programs of `ProgrammingOnTheStep` read their answers off at one exhibited solution:

* the vector lookup `lookup (succ n) (cons n x xs) (fz n) = x`, fired on `lookup 1 [2] (fz 0)`,
  reads the made row `x` as `2` (`VectorPrograms.lookup_answer`);
* the typed interpreter's `eval tnat (lit n) = n`, fired on `eval tnat (lit 3)`, reads the made row
  `n` as `3` (`TypedInterpreter.eval_answer`);
* the recursive lookup, a run of two firings on `lookup 2 [1, 2] (fs 1 (fz 0))`, reads its answer
  row `x'` as `2` (`RecursiveRun.lookupRun_answer`).

Here these answers are **determined**: every solution of the knowledge, at every later frame,
reads them as `2`, `3` and `2` (`lookup_readback`, `eval_readback`, `lookupRun_readback`). For the
run, the answer is fixed jointly by the equation the first firing leaves in the knowledge and the
equation of the second (`lookupRun_x_determined`); `cons_third` reads the tail of a vector.

Two more programs read off answers that the knowledge then determines:

* **append with implicit lengths** (`VectorPrograms.append_solution_lengths`): the heterogeneous
  knowledge `(xs : vec m) ≐ (nil : vec 0)`, `(ys : vec k) ≐ ([2] : vec 1)` determines `m` as `0`
  and `k` as `1` (`append_lengths_readback`), because equal vector types have equal lengths
  (`vec_injective`, from the algorithmic equality of types); with the rule's left side it determines
  the made row `ys'` as `[2]` and its length `p` as `1` (`append_readback`). The call itself is not
  determined as `[2]` (`append_call_undetermined`): `append` never computes in the knowledge, so
  the answer is read from the made row;
* **taking a dependent pair apart** (`SigmaIdentity.pair_answer`): `pair y q ≐ pair a (refl a)` at
  `Σ (x : A). Id A x a` determines `y` as `a` and the made row `q` as `refl a`, by projecting and
  computing (`pair_determined`, `pair_readback`); no completeness is needed here.

## Argument injectivity of rigid spines, from the algorithmic equality

In both packages every constant is rigid, and the tree's algorithmic equality is complete
(`VectorPackage.complete`, `TypedInterpreter.complete`) and sound (`Algorithm.sound`). Inverting its
derivations (`terms_inv`, `termsW_app_inv`, `termsW_const_inv`, `spinesW_inv`, `spines_app_inv`,
`spines_const_inv`, and `peel`) shows how two equal spines with one rigid head are compared:
argument by argument, at the domains of the head's declared type, a dependent function type in
weak-head normal form (`head_type`). So:

* `lookup_second`, `cons_second`: equal calls of `lookup` have equal vectors, at `vec` of the first
  argument; equal vectors built by `cons` have equal heads, at `nat`;
* `eval_second`, `lit_first`: equal evaluations have equal expressions, at `exp` of the type; equal
  literals have equal numbers, at `nat`;
* `lookup_x_determined`, `eval_n_determined`: the equation of a call with a left side determines the
  matched variable.

The tree already refutes equal rigid spines with different heads (`not_equal_of_rigid_heads`); this
module supplies the same-head, argument-wise half for the constants these programs match.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RigidReadback

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull
open ProgrammingOnTheStep.VectorPackage ProgrammingOnTheStep.VectorPrograms

/-! ## Inverting the algorithmic equality -/

section Inversion

variable {Head : Type} {R : Rules Head} {roles : Roles Head} {n : Nat} {Γ : Ctx Head n}

theorem terms_inv {t u A : Tm Head n} (h : Algorithmic R roles (.terms Γ t u A)) :
    ∃ A' t' u', RedTy R roles Γ A A' ∧ RedTm R roles Γ t t' A' ∧ RedTm R roles Γ u u' A' ∧
      Algorithmic R roles (.termsW Γ t' u' A') := by
  cases h with
  | terms rA _ rt ru w => exact ⟨_, _, _, rA, rt, ru, w⟩

theorem spinesW_inv {t u U' : Tm Head n} (h : Algorithmic R roles (.spinesW Γ t u U')) :
    ∃ U, Algorithmic R roles (.spines Γ t u U) ∧ RedTy R roles Γ U U' := by
  cases h with
  | spinesW s red _ => exact ⟨_, s, red⟩

theorem spines_app_inv {f g a b U : Tm Head n}
    (h : Algorithmic R roles (.spines Γ (.app f a) (.app g b) U)) :
    ∃ (A : Tm Head n) (B : Tm Head (n + 1)), Algorithmic R roles (.spinesW Γ f g (.pi A B)) ∧
      Algorithmic R roles (.terms Γ a b A) ∧ U = inst0 a B := by
  cases h with
  | app hf ha => exact ⟨_, _, hf, ha, rfl⟩

theorem spines_const_inv {c c' : DeclName} {U : Tm Head n}
    (h : Algorithmic R roles (.spines Γ (.const c) (.const c') U)) :
    c = c' ∧ ∃ type, R.constantType c = some type ∧ U = liftClosed type := by
  cases h with
  | const declared _ => exact ⟨rfl, _, declared, rfl⟩

theorem termsW_app_inv {t u F M : Tm Head n} (h : Algorithmic R roles (.termsW Γ t u (.app F M))) :
    ∃ U, Algorithmic R roles (.spinesW Γ t u U) := by
  cases h with
  | spine _ _ _ _ _ s => exact ⟨_, s⟩

theorem termsW_const_inv {t u : Tm Head n} {T : DeclName}
    (h : Algorithmic R roles (.termsW Γ t u (.const T))) :
    ∃ U, Algorithmic R roles (.spinesW Γ t u U) := by
  cases h with
  | spine _ _ _ _ _ s => exact ⟨_, s⟩

theorem types_inv {A B : Tm Head n} (h : Algorithmic R roles (.types Γ A B)) :
    ∃ A' B', RedTy R roles Γ A A' ∧ RedTy R roles Γ B B' ∧ Algorithmic R roles (.typesW Γ A' B') := by
  cases h with
  | types rA rB _ _ w => exact ⟨_, _, rA, rB, w⟩

/-- Two applied types in weak-head normal form are compared as spines at a universe. -/
theorem typesW_app_inv {F M G N : Tm Head n}
    (h : Algorithmic R roles (.typesW Γ (.app F M) (.app G N))) :
    ∃ u, Algorithmic R roles (.spinesW Γ (.app F M) (.app G N) (.head u)) := by
  cases h with
  | neutralTypes _ _ _ s => exact ⟨_, s⟩

/-- **Peel the last argument** off two compared application spines. -/
theorem peel {f g a b U' : Tm Head n} (h : Algorithmic R roles (.spinesW Γ (.app f a) (.app g b) U')) :
    ∃ (A : Tm Head n) (B : Tm Head (n + 1)), Algorithmic R roles (.spinesW Γ f g (.pi A B)) ∧
      Algorithmic R roles (.terms Γ a b A) ∧ RedTy R roles Γ (inst0 a B) U' := by
  obtain ⟨U, spines, red⟩ := spinesW_inv h
  obtain ⟨A, B, heads, args, rfl⟩ := spines_app_inv spines
  exact ⟨A, B, heads, args, red⟩

theorem const_neutral {roles : Roles Head} (c : DeclName) (rigid : roles c = .rigid) :
    Neutral roles (.const c : Tm Head n) :=
  Neutral.rigid (c := c) [] rigid

end Inversion

/-! ## Weak-head normal forms in a setting -/

section Setting

variable (S : Setting Tower.Head Nat) {n : Nat} {Γ : Ctx Tower.Head n}

theorem whnf_of_neutral {t : Tower.Tm n} (neutral : Neutral S.roles t) : Whnf S.R S.roles t :=
  Neutral.whnf S.shape neutral

theorem pi_normal (A : Tower.Tm n) (B : Tower.Tm (n + 1)) : Whnf S.R S.roles (.pi A B) :=
  pi_whnf S.shape A B

/-- A typed weak-head reduction of a type from a weak-head normal form stays put. -/
theorem redTy_stays {A A' : Tower.Tm n} (normal : Whnf S.R S.roles A)
    (red : RedTy S.R S.roles Γ A A') : A' = A :=
  WhRed.eq_of_whnf normal red.red

/-- A typed weak-head reduction of a term from a weak-head normal form stays put. -/
theorem redTm_stays {t t' A : Tower.Tm n} (normal : Whnf S.R S.roles t)
    (red : RedTm S.R S.roles Γ t t' A) : t' = t :=
  WhRed.eq_of_whnf normal red.red

/-- A typed weak-head reduction from a dependent function type stays put. -/
theorem redTy_pi_stays {A : Tower.Tm n} {B : Tower.Tm (n + 1)} {T : Tower.Tm n}
    (red : RedTy S.R S.roles Γ (.pi A B) T) : T = .pi A B :=
  WhRed.eq_of_whnf (pi_normal S A B) red.red

/-- **A comparison of spines headed by a declared constant starts at its declared type**, when
that type is in weak-head normal form. -/
theorem head_type {c : DeclName} {type : Tower.Tm 0} (declaredC : S.R.constantType c = some type)
    (normal : Whnf S.R S.roles (liftClosed type : Tower.Tm n)) {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    (h : Algorithmic S.R S.roles (.spinesW Γ (.const c) (.const c) (.pi A B))) :
    Tm.pi A B = liftClosed type := by
  obtain ⟨U, spines, red⟩ := spinesW_inv h
  obtain ⟨_, type', declared', rfl⟩ := spines_const_inv spines
  rw [declaredC] at declared'
  obtain rfl := Option.some.inj declared'
  exact WhRed.eq_of_whnf normal red.red

end Setting

/-! ## The vector lookup program -/

section Lookup

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- **Equal calls of `lookup` have algorithmically equal vectors**, at `vec` of the first
argument. -/
theorem lookup_second {k v i k' v' i' U : Tower.Tm n}
    (h : Algorithmic rules roles (.spinesW Γ (lookupC k v i) (lookupC k' v' i') U)) :
    Algorithmic rules roles (.terms Γ v v' (vecC k)) := by
  obtain ⟨A₃, B₃, h₃, _, _⟩ := peel h
  obtain ⟨A₂, B₂, h₂, args₂, _⟩ := peel h₃
  obtain ⟨A₁, B₁, h₁, _, red₁⟩ := peel h₂
  have first : Tm.pi A₁ B₁ = liftClosed lookupTy :=
    head_type setting declared_lookup (pi_normal setting _ _) h₁
  injection first with _ _ sameB₁
  subst sameB₁
  have second := redTy_pi_stays setting red₁
  injection second with _ sameA₂ _
  rw [sameA₂] at args₂
  exact args₂

/-- **Equal vectors built by `cons` have algorithmically equal heads**, at `nat`. -/
theorem cons_second {a x xs a' x' xs' U : Tower.Tm n}
    (h : Algorithmic rules roles (.spinesW Γ (consC a x xs) (consC a' x' xs') U)) :
    Algorithmic rules roles (.terms Γ x x' natC) := by
  obtain ⟨A₃, B₃, h₃, _, _⟩ := peel h
  obtain ⟨A₂, B₂, h₂, args₂, _⟩ := peel h₃
  obtain ⟨A₁, B₁, h₁, _, red₁⟩ := peel h₂
  have first : Tm.pi A₁ B₁ = liftClosed consTy :=
    head_type setting declared_cons (pi_normal setting _ _) h₁
  injection first with _ _ sameB₁
  subst sameB₁
  have second := redTy_pi_stays setting red₁
  injection second with _ sameA₂ _
  rw [sameA₂] at args₂
  exact args₂

/-- **The equation of the call with the left side determines `x` as `2`.** -/
theorem lookup_x_determined {Θ : Context rules} (σ : Sub Tower.Head 3 Θ.arity)
    (equal : Equal rules Θ.raw (lookupC (succC (σ 2)) (consC (σ 2) (σ 1) (σ 0)) (fzC (σ 2)))
      (lookupC one oneVec (fzC zeroC)) natC) :
    Equal rules Θ.raw (σ 1) two natC := by
  obtain ⟨A, t, u, rA, rt, ru, w⟩ :=
    terms_inv (ProgrammingOnTheStep.VectorPackage.complete Θ.formed equal)
  obtain rfl := redTy_stays setting (whnf_of_neutral setting (const_neutral natN rfl)) rA
  obtain rfl := redTm_stays setting
    (whnf_of_neutral setting (.app (.app (.app (const_neutral lookupN rfl))))) rt
  obtain rfl := redTm_stays setting
    (whnf_of_neutral setting (.app (.app (.app (const_neutral lookupN rfl))))) ru
  obtain ⟨U, spines⟩ := termsW_const_inv w
  obtain ⟨B, v, v', rB, rv, rv', w'⟩ := terms_inv (lookup_second spines)
  obtain rfl := redTy_stays setting (whnf_of_neutral setting (.app (const_neutral vecN rfl))) rB
  obtain rfl := redTm_stays setting
    (whnf_of_neutral setting (.app (.app (.app (const_neutral consN rfl))))) rv
  obtain rfl := redTm_stays setting
    (whnf_of_neutral setting (.app (.app (.app (const_neutral consN rfl))))) rv'
  obtain ⟨U', spines'⟩ := termsW_app_inv w'
  have heads := cons_second spines'
  obtain ⟨C, y, y', rC, ry, ry', _⟩ := terms_inv heads
  obtain rfl := redTy_stays setting (whnf_of_neutral setting (const_neutral natN rfl)) rC
  exact Algorithm.sound (S := setting) ProgrammingOnTheStep.VectorPackage.facts
    ProgrammingOnTheStep.VectorPackage.roots ProgrammingOnTheStep.VectorPackage.heads
    ProgrammingOnTheStep.VectorPackage.algebra heads.refines Θ.formed ry.source ry'.source

/-- **The lookup program's answer is determined**: every solution of the firing's information, at
every later frame, reads the made row `x` as `2`. -/
theorem lookup_readback {Θ : Context rules} (τ : Θ ⟶ lookupFiring.helpers.frame)
    (solved : (frames levels).Models τ lookupFiring.information) :
    Equal rules Θ.raw (subst τ.substitution (.var 1 : Tower.Tm 3)) two natC := by
  rw [lookupFiring_information] at solved
  have equation := solved _ (List.mem_singleton_self _)
  have equal : Equal rules Θ.raw
      (lookupC (succC (subst τ.substitution (.var 2 : Tower.Tm 3)))
        (consC (subst τ.substitution (.var 2 : Tower.Tm 3)) (subst τ.substitution (.var 1 : Tower.Tm 3))
          (subst τ.substitution (.var 0 : Tower.Tm 3)))
        (fzC (subst τ.substitution (.var 2 : Tower.Tm 3))))
      (lookupC one oneVec (fzC zeroC)) natC := equation.2
  exact lookup_x_determined (σ := τ.substitution) equal

end Lookup

/-! ## The typed interpreter's evaluation -/

section Interpreter

open ProgrammingOnTheStep

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- **Equal evaluations have algorithmically equal expressions**, at `exp` of the type. -/
theorem eval_second {t e t' e' U : Tower.Tm n}
    (h : Algorithmic TypedInterpreter.rules TypedInterpreter.roles
      (.spinesW Γ (TypedInterpreter.evalC t e) (TypedInterpreter.evalC t' e') U)) :
    Algorithmic TypedInterpreter.rules TypedInterpreter.roles
      (.terms Γ e e' (TypedInterpreter.expC t)) := by
  obtain ⟨A₂, B₂, h₂, args₂, _⟩ := peel h
  obtain ⟨A₁, B₁, h₁, _, red₁⟩ := peel h₂
  have first : Tm.pi A₁ B₁ = liftClosed TypedInterpreter.evalTy :=
    head_type TypedInterpreter.setting TypedInterpreter.declared_eval
      (pi_normal TypedInterpreter.setting _ _) h₁
  injection first with _ _ sameB₁
  subst sameB₁
  have second := redTy_pi_stays TypedInterpreter.setting red₁
  injection second with _ sameA₂ _
  rw [sameA₂] at args₂
  exact args₂

/-- **Equal literals have algorithmically equal numbers**, at `nat`. -/
theorem lit_first {k k' U : Tower.Tm n}
    (h : Algorithmic TypedInterpreter.rules TypedInterpreter.roles
      (.spinesW Γ (TypedInterpreter.litC k) (TypedInterpreter.litC k') U)) :
    Algorithmic TypedInterpreter.rules TypedInterpreter.roles (.terms Γ k k' natC) := by
  obtain ⟨A₁, B₁, h₁, args₁, _⟩ := peel h
  have first : Tm.pi A₁ B₁ = liftClosed TypedInterpreter.litTy :=
    head_type TypedInterpreter.setting TypedInterpreter.declared_lit
      (pi_normal TypedInterpreter.setting _ _) h₁
  injection first with _ sameA₁ _
  rw [sameA₁] at args₁
  exact args₁

/-- **The equation of the call with the left side determines `n` as `3`.** -/
theorem eval_n_determined {Θ : Context TypedInterpreter.rules} (σ : Sub Tower.Head 1 Θ.arity)
    (equal : Equal TypedInterpreter.rules Θ.raw
      (TypedInterpreter.evalC TypedInterpreter.tnatC (TypedInterpreter.litC (σ 0)))
      (TypedInterpreter.evalC TypedInterpreter.tnatC (TypedInterpreter.litC TypedInterpreter.three))
      (TypedInterpreter.valC TypedInterpreter.tnatC)) :
    Equal TypedInterpreter.rules Θ.raw (σ 0) TypedInterpreter.three natC := by
  obtain ⟨A, t, u, rA, rt, ru, w⟩ := terms_inv (TypedInterpreter.complete Θ.formed equal)
  obtain rfl := redTy_stays TypedInterpreter.setting
    (whnf_of_neutral TypedInterpreter.setting (.app (const_neutral TypedInterpreter.valN rfl))) rA
  obtain rfl := redTm_stays TypedInterpreter.setting
    (whnf_of_neutral TypedInterpreter.setting (.app (.app (const_neutral TypedInterpreter.evalN rfl)))) rt
  obtain rfl := redTm_stays TypedInterpreter.setting
    (whnf_of_neutral TypedInterpreter.setting (.app (.app (const_neutral TypedInterpreter.evalN rfl)))) ru
  obtain ⟨U, spines⟩ := termsW_app_inv w
  obtain ⟨B, e, e', rB, re, re', w'⟩ := terms_inv (eval_second spines)
  obtain rfl := redTy_stays TypedInterpreter.setting
    (whnf_of_neutral TypedInterpreter.setting (.app (const_neutral TypedInterpreter.expN rfl))) rB
  obtain rfl := redTm_stays TypedInterpreter.setting
    (whnf_of_neutral TypedInterpreter.setting (.app (const_neutral TypedInterpreter.litN rfl))) re
  obtain rfl := redTm_stays TypedInterpreter.setting
    (whnf_of_neutral TypedInterpreter.setting (.app (const_neutral TypedInterpreter.litN rfl))) re'
  obtain ⟨U', spines'⟩ := termsW_app_inv w'
  have numbers := lit_first spines'
  obtain ⟨C, y, y', rC, ry, ry', _⟩ := terms_inv numbers
  obtain rfl := redTy_stays TypedInterpreter.setting
    (whnf_of_neutral TypedInterpreter.setting (const_neutral natN rfl)) rC
  exact Algorithm.sound (S := TypedInterpreter.setting) TypedInterpreter.facts TypedInterpreter.roots
    TypedInterpreter.heads TypedInterpreter.algebra numbers.refines Θ.formed ry.source ry'.source

/-- **The interpreter's answer is determined**: every solution of the firing's information, at every
later frame, reads the made row `n` as `3`. -/
theorem eval_readback {Θ : Context TypedInterpreter.rules}
    (τ : Θ ⟶ TypedInterpreter.evalFiring.helpers.frame)
    (solved : (frames TypedInterpreter.levels).Models τ TypedInterpreter.evalFiring.information) :
    Equal TypedInterpreter.rules Θ.raw (subst τ.substitution (.var 0 : Tower.Tm 1))
      TypedInterpreter.three natC := by
  rw [TypedInterpreter.evalFiring_information] at solved
  have equation := solved _ (List.mem_singleton_self _)
  have equal : Equal TypedInterpreter.rules Θ.raw
      (TypedInterpreter.evalC TypedInterpreter.tnatC
        (TypedInterpreter.litC (subst τ.substitution (.var 0 : Tower.Tm 1))))
      (TypedInterpreter.evalC TypedInterpreter.tnatC (TypedInterpreter.litC TypedInterpreter.three))
      (TypedInterpreter.valC TypedInterpreter.tnatC) := equation.2
  exact eval_n_determined (σ := τ.substitution) equal

end Interpreter

/-! ## The recursive lookup run -/

section Recursive

open ProgrammingOnTheStep.RecursiveRun

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- **Equal vectors built by `cons` have algorithmically equal tails**, at `vec` of the length. -/
theorem cons_third {a x xs a' x' xs' U : Tower.Tm n}
    (h : Algorithmic rules roles (.spinesW Γ (consC a x xs) (consC a' x' xs') U)) :
    Algorithmic rules roles (.terms Γ xs xs' (vecC a)) := by
  obtain ⟨A₃, B₃, h₃, args₃, _⟩ := peel h
  obtain ⟨A₂, B₂, h₂, _, red₂⟩ := peel h₃
  obtain ⟨A₁, B₁, h₁, _, red₁⟩ := peel h₂
  have first : Tm.pi A₁ B₁ = liftClosed consTy :=
    head_type setting declared_cons (pi_normal setting _ _) h₁
  injection first with _ _ sameB₁
  subst sameB₁
  have second := redTy_pi_stays setting red₁
  injection second with _ _ sameB₂
  subst sameB₂
  have third := redTy_pi_stays setting red₂
  injection third with _ sameA₃ _
  have domain : A₃ = vecC a := by
    rw [sameA₃]
    show vecC (inst0 x (rename wk a)) = vecC a
    rw [inst0_rename_wk]
  rw [domain] at args₃
  exact args₃

/-- Equal neutral terms at a constant type are compared as spines. -/
theorem spines_at_const {Θ : Context rules} {t u : Tower.Tm Θ.arity} {T : DeclName}
    (neutralT : Neutral roles t) (neutralU : Neutral roles u) (equal : Equal rules Θ.raw t u (.const T)) :
    ∃ U, Algorithmic rules roles (.spinesW Θ.raw t u U) := by
  obtain ⟨A, t', u', rA, rt, ru, w⟩ := terms_inv (ProgrammingOnTheStep.VectorPackage.complete Θ.formed equal)
  obtain rfl := redTy_stays setting (whnf_of_neutral setting (const_neutral T rfl)) rA
  obtain rfl := redTm_stays setting (whnf_of_neutral setting neutralT) rt
  obtain rfl := redTm_stays setting (whnf_of_neutral setting neutralU) ru
  exact termsW_const_inv w

/-- Algorithmically equal neutral terms at a neutral applied type are compared as spines. -/
theorem spines_at_app {Θ : Context rules} {t u F M : Tower.Tm Θ.arity}
    (neutralA : Neutral roles (.app F M)) (neutralT : Neutral roles t) (neutralU : Neutral roles u)
    (h : Algorithmic rules roles (.terms Θ.raw t u (.app F M))) :
    ∃ U, Algorithmic rules roles (.spinesW Θ.raw t u U) := by
  obtain ⟨A, t', u', rA, rt, ru, w⟩ := terms_inv h
  obtain rfl := redTy_stays setting (whnf_of_neutral setting neutralA) rA
  obtain rfl := redTm_stays setting (whnf_of_neutral setting neutralT) rt
  obtain rfl := redTm_stays setting (whnf_of_neutral setting neutralU) ru
  exact termsW_app_inv w

/-- Algorithmic equality at a weak-head normal type is the typed equality. -/
theorem sound_at_normal {Θ : Context rules} {a b A : Tower.Tm Θ.arity} (normal : Whnf rules roles A)
    (h : Algorithmic rules roles (.terms Θ.raw a b A)) : Equal rules Θ.raw a b A := by
  obtain ⟨A', a', b', rA, ra, rb, _⟩ := terms_inv h
  obtain rfl := redTy_stays setting normal rA
  exact Algorithm.sound (S := setting) ProgrammingOnTheStep.VectorPackage.facts
    ProgrammingOnTheStep.VectorPackage.roots ProgrammingOnTheStep.VectorPackage.heads
    ProgrammingOnTheStep.VectorPackage.algebra h.refines Θ.formed ra.source rb.source

/-- **The two equations of the run determine the answer `x'` as `2`**: the carried equation of the
recursive call, and the base equation on its result. -/
theorem lookupRun_x_determined {Θ : Context rules} (σ : Sub Tower.Head 7 Θ.arity)
    (carried : Equal rules Θ.raw (lookupC (succC (σ 6)) (consC (σ 6) (σ 5) (σ 4)) (fsC (σ 6) (σ 3)))
      (lookupC two vec2 idx) natC)
    (head : Equal rules Θ.raw (lookupC (succC (σ 2)) (consC (σ 2) (σ 1) (σ 0)) (fzC (σ 2)))
      (lookupC (σ 6) (σ 4) (σ 3)) natC) :
    Equal rules Θ.raw (σ 1) two natC := by
  have lookupNeutral : ∀ k v i : Tower.Tm Θ.arity, Neutral roles (lookupC k v i) :=
    fun _ _ _ => .app (.app (.app (const_neutral lookupN rfl)))
  have consNeutral : ∀ k x xs : Tower.Tm Θ.arity, Neutral roles (consC k x xs) :=
    fun _ _ _ => .app (.app (.app (const_neutral consN rfl)))
  have vecNeutral : ∀ k : Tower.Tm Θ.arity, Neutral roles (vecC k) :=
    fun _ => .app (const_neutral vecN rfl)
  -- The carried equation: the call's tail is `[2]`.
  obtain ⟨U₁, spines₁⟩ := spines_at_const (lookupNeutral _ _ _) (lookupNeutral _ _ _) carried
  obtain ⟨U₂, spines₂⟩ := spines_at_app (vecNeutral _) (consNeutral _ _ _) (consNeutral _ _ _)
    (lookup_second spines₁)
  have tail : Equal rules Θ.raw (σ 4) (consC zeroC two nilC) (vecC (σ 6)) :=
    sound_at_normal (whnf_of_neutral setting (vecNeutral _)) (cons_third spines₂)
  -- The base equation, read from the recursive call: its tail is `cons n' x' xs'`.
  obtain ⟨U₃, spines₃⟩ := spines_at_const (lookupNeutral _ _ _) (lookupNeutral _ _ _) head.symm
  have recursive : Equal rules Θ.raw (σ 4) (consC (σ 2) (σ 1) (σ 0)) (vecC (σ 6)) :=
    sound_at_normal (whnf_of_neutral setting (vecNeutral _)) (lookup_second spines₃)
  -- So `cons n' x' xs'` is `[2]`, and its head `x'` is `2`.
  have joined : Equal rules Θ.raw (consC (σ 2) (σ 1) (σ 0)) (consC zeroC two nilC) (vecC (σ 6)) :=
    .trans recursive.symm tail
  obtain ⟨U₄, spines₄⟩ := spines_at_app (vecNeutral _) (consNeutral _ _ _) (consNeutral _ _ _)
    (ProgrammingOnTheStep.VectorPackage.complete Θ.formed joined)
  exact sound_at_normal (whnf_of_neutral setting (const_neutral natN rfl)) (cons_second spines₄)

/-- **The recursive run's answer is determined**: every solution of the run's last knowledge, at
every later frame, reads the answer row `x'` as `2`. -/
theorem lookupRun_readback {Θ : Context rules} (τ : Θ ⟶ lookupRun.last.frame)
    (solved : (frames levels).Models τ lookupRun.last.knowledge) :
    Equal rules Θ.raw (subst τ.substitution (.var 1 : Tower.Tm 7)) two natC := by
  have solvedHead : (frames levels).Models τ headFiring.information := solved
  rw [headFiring_information] at solvedHead
  have first := solvedHead _ List.mem_cons_self
  have second := solvedHead _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have carried : Equal rules Θ.raw
      (lookupC (succC (subst τ.substitution (.var 6 : Tower.Tm 7)))
        (consC (subst τ.substitution (.var 6 : Tower.Tm 7)) (subst τ.substitution (.var 5 : Tower.Tm 7))
          (subst τ.substitution (.var 4 : Tower.Tm 7)))
        (fsC (subst τ.substitution (.var 6 : Tower.Tm 7)) (subst τ.substitution (.var 3 : Tower.Tm 7))))
      (lookupC two vec2 idx) natC := first.2
  have head : Equal rules Θ.raw
      (lookupC (succC (subst τ.substitution (.var 2 : Tower.Tm 7)))
        (consC (subst τ.substitution (.var 2 : Tower.Tm 7)) (subst τ.substitution (.var 1 : Tower.Tm 7))
          (subst τ.substitution (.var 0 : Tower.Tm 7)))
        (fzC (subst τ.substitution (.var 2 : Tower.Tm 7))))
      (lookupC (subst τ.substitution (.var 6 : Tower.Tm 7)) (subst τ.substitution (.var 4 : Tower.Tm 7))
        (subst τ.substitution (.var 3 : Tower.Tm 7))) natC := second.2
  exact lookupRun_x_determined (σ := τ.substitution) carried head

end Recursive

/-! ## Append: the knowledge determines the implicit lengths and the answer -/

section Append

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- **Equal vector types have equal lengths**: `vec a ≡ vec b` gives `a ≡ b : nat`. -/
theorem vec_injective {Θ : Context rules} {a b : Tower.Tm Θ.arity}
    (equal : TypeEq rules Θ.raw (vecC a) (vecC b)) : Equal rules Θ.raw a b natC := by
  obtain ⟨A, B, rA, rB, w⟩ := types_inv (AlgorithmicComplete.types (S := setting)
    ProgrammingOnTheStep.VectorPackage.complete equal Θ.formed)
  obtain rfl := redTy_stays setting (whnf_of_neutral setting (.app (const_neutral vecN rfl))) rA
  obtain rfl := redTy_stays setting (whnf_of_neutral setting (.app (const_neutral vecN rfl))) rB
  obtain ⟨u, spines⟩ := typesW_app_inv w
  obtain ⟨A₁, B₁, h₁, args, _⟩ := peel spines
  have first : Tm.pi A₁ B₁ = liftClosed vecTy :=
    head_type setting declared_vec (pi_normal setting _ _) h₁
  injection first with _ sameA _
  rw [sameA] at args
  exact sound_at_normal (whnf_of_neutral setting (const_neutral natN rfl)) args

/-- Equal lengths give equal vector types. -/
theorem vec_congr {Θ : Context rules} {a b : Tower.Tm Θ.arity} (equal : Equal rules Θ.raw a b natC) :
    TypeEq rules Θ.raw (vecC a) (vecC b) := by
  have head : Equal rules Θ.raw (.const vecN) (.const vecN) (liftClosed vecTy) :=
    .refl (.const declared_vec vecTy_typed (.sort _))
  exact ⟨u0, .sort _, .appCong head equal⟩

/-- **Equal calls of `append` have algorithmically equal second arguments**, at `nat`. -/
theorem append_second {a b c d a' b' c' d' U : Tower.Tm n}
    (h : Algorithmic rules roles (.spinesW Γ (appendC a b c d) (appendC a' b' c' d') U)) :
    Algorithmic rules roles (.terms Γ b b' natC) := by
  obtain ⟨A₄, B₄, h₄, _, _⟩ := peel h
  obtain ⟨A₃, B₃, h₃, _, _⟩ := peel h₄
  obtain ⟨A₂, B₂, h₂, args₂, _⟩ := peel h₃
  obtain ⟨A₁, B₁, h₁, _, red₁⟩ := peel h₂
  have first : Tm.pi A₁ B₁ = liftClosed appendTy :=
    head_type setting declared_append (pi_normal setting _ _) h₁
  injection first with _ _ sameB₁
  subst sameB₁
  have second := redTy_pi_stays setting red₁
  injection second with _ sameA₂ _
  rw [sameA₂] at args₂
  exact args₂

/-- **Equal calls of `append` have algorithmically equal last arguments**, at `vec` of the second
argument. -/
theorem append_fourth {a b c d a' b' c' d' U : Tower.Tm n}
    (h : Algorithmic rules roles (.spinesW Γ (appendC a b c d) (appendC a' b' c' d') U)) :
    Algorithmic rules roles (.terms Γ d d' (vecC b)) := by
  obtain ⟨A₄, B₄, h₄, args₄, _⟩ := peel h
  obtain ⟨A₃, B₃, h₃, _, red₃⟩ := peel h₄
  obtain ⟨A₂, B₂, h₂, _, red₂⟩ := peel h₃
  obtain ⟨A₁, B₁, h₁, _, red₁⟩ := peel h₂
  have first : Tm.pi A₁ B₁ = liftClosed appendTy :=
    head_type setting declared_append (pi_normal setting _ _) h₁
  injection first with _ _ sameB₁
  subst sameB₁
  have second := redTy_pi_stays setting red₁
  injection second with _ _ sameB₂
  subst sameB₂
  have third := redTy_pi_stays setting red₂
  injection third with _ _ sameB₃
  subst sameB₃
  have fourth := redTy_pi_stays setting red₃
  injection fourth with _ sameA₄ _
  have domain : A₄ = vecC b := by
    rw [sameA₄]
    show vecC (inst0 c (rename wk b)) = vecC b
    rw [inst0_rename_wk]
  rw [domain] at args₄
  exact args₄

/-- **The knowledge determines the implicit lengths**: every solution of the append firing's
information, at every later frame, reads `m` as `0` and `k` as `1`. -/
theorem append_lengths_readback {Θ : Context rules} (τ : Θ ⟶ appendFiring.helpers.frame)
    (solved : (frames levels).Models τ appendFiring.information) :
    Equal rules Θ.raw (subst τ.substitution (.var 5 : Tower.Tm 6)) zeroC natC ∧
      Equal rules Θ.raw (subst τ.substitution (.var 4 : Tower.Tm 6)) one natC := by
  rw [appendFiring_information] at solved
  have xs := solved _ List.mem_cons_self
  have ys := solved _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have xsType : TypeEq rules Θ.raw (vecC (subst τ.substitution (.var 5 : Tower.Tm 6))) (vecC zeroC) :=
    xs.1
  have ysType : TypeEq rules Θ.raw (vecC (subst τ.substitution (.var 4 : Tower.Tm 6))) (vecC one) :=
    ys.1
  exact ⟨vec_injective xsType, vec_injective ysType⟩

/-- **The equations determine the answer**: the knowledge `ys ≐ [2]` of the call's last argument
and the equation of the rule's left side with the call determine the made row `ys'` as `[2]`, and
its length `p` as `1`. -/
theorem append_answer_determined {Θ : Context rules} (σ : Sub Tower.Head 6 Θ.arity)
    (ys : TypeEq rules Θ.raw (vecC (σ 4)) (vecC one) ∧ Equal rules Θ.raw (σ 2) oneVec (vecC (σ 4)))
    (call : Equal rules Θ.raw (appendC zeroC (σ 1) nilC (σ 0)) (appendC (σ 5) (σ 4) (σ 3) (σ 2))
      (vecC (addC zeroC (σ 1)))) :
    Equal rules Θ.raw (σ 1) one natC ∧ Equal rules Θ.raw (σ 0) oneVec (vecC one) := by
  have appendNeutral : ∀ m k xs ys : Tower.Tm Θ.arity, Neutral roles (appendC m k xs ys) :=
    fun _ _ _ _ => .app (.app (.app (.app (const_neutral appendN rfl))))
  obtain ⟨U, spines⟩ := spines_at_app (.app (const_neutral vecN rfl)) (appendNeutral _ _ _ _)
    (appendNeutral _ _ _ _) (ProgrammingOnTheStep.VectorPackage.complete Θ.formed call)
  have length : Equal rules Θ.raw (σ 1) one natC :=
    .trans (sound_at_normal (whnf_of_neutral setting (const_neutral natN rfl)) (append_second spines))
      (vec_injective ys.1)
  have answer : Equal rules Θ.raw (σ 0) (σ 2) (vecC (σ 1)) :=
    sound_at_normal (whnf_of_neutral setting (.app (const_neutral vecN rfl))) (append_fourth spines)
  exact ⟨length, .trans (TypedEquality.Normalization.Equal.convType answer (vec_congr length))
    (TypedEquality.Normalization.Equal.convType ys.2 ys.1)⟩

/-- **The append program's answer is determined**: every solution of the firing's information, at
every later frame, reads the made row `ys'` as `[2]` and its length `p` as `1`. -/
theorem append_readback {Θ : Context rules} (τ : Θ ⟶ appendFiring.helpers.frame)
    (solved : (frames levels).Models τ appendFiring.information) :
    Equal rules Θ.raw (subst τ.substitution (.var 1 : Tower.Tm 6)) one natC ∧
      Equal rules Θ.raw (subst τ.substitution (.var 0 : Tower.Tm 6)) oneVec (vecC one) := by
  rw [appendFiring_information] at solved
  have ys := solved _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have call := solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have ysEquation : TypeEq rules Θ.raw (vecC (subst τ.substitution (.var 4 : Tower.Tm 6))) (vecC one) ∧
      Equal rules Θ.raw (subst τ.substitution (.var 2 : Tower.Tm 6)) oneVec
        (vecC (subst τ.substitution (.var 4 : Tower.Tm 6))) := ys
  have callEquation : Equal rules Θ.raw
      (appendC zeroC (subst τ.substitution (.var 1 : Tower.Tm 6)) nilC
        (subst τ.substitution (.var 0 : Tower.Tm 6)))
      (appendC (subst τ.substitution (.var 5 : Tower.Tm 6)) (subst τ.substitution (.var 4 : Tower.Tm 6))
        (subst τ.substitution (.var 3 : Tower.Tm 6)) (subst τ.substitution (.var 2 : Tower.Tm 6)))
      (vecC (addC zeroC (subst τ.substitution (.var 1 : Tower.Tm 6)))) := call.2
  exact append_answer_determined (σ := τ.substitution) ysEquation callEquation

/-- The exhibited solution solves the append firing's information. -/
theorem append_solved : (frames levels).Models appendSolution appendFiring.information := by
  rw [appendFiring_information]
  intro e member
  rcases List.mem_cons.mp member with rfl | member
  · show (frames levels).E (((frames levels).act appendFiring.helpers.weaken xsRow).reindex appendSolution)
      (((frames levels).act appendFiring.helpers.weaken nilRow).reindex appendSolution)
    rw [append_xs]
    exact ((frames levels).equivalence _).refl _
  rcases List.mem_cons.mp member with rfl | member
  · show (frames levels).E (((frames levels).act appendFiring.helpers.weaken ysRow).reindex appendSolution)
      (((frames levels).act appendFiring.helpers.weaken oneVecRow).reindex appendSolution)
    rw [append_ys]
    exact ((frames levels).equivalence _).refl _
  obtain rfl := List.mem_singleton.mp member
  show (frames levels).E (appendPattern.reindex appendSolution) ((appendFiring.row 0).reindex appendSolution)
  rw [append_identifies]
  exact ((frames levels).equivalence _).refl _

/-- **Control: the knowledge determines the made row, not the call.** `append` never computes in
the knowledge, so the call `append m k xs ys` is not determined as the value `[2]` that the made row
reads: at the exhibited solution it reads `append 0 1 nil [2]`, a spine with another rigid head. -/
theorem append_call_undetermined :
    ¬ Readback.Determined (frames levels) appendFiring.information (appendFiring.row 0)
      ((frames levels).act appendFiring.helpers.weaken oneVecRow) := by
  intro determined
  have reads := determined (empty rules) appendSolution append_solved
  refine absurd reads.2 ?_
  exact not_equal_of_rigid_heads (S := setting) ProgrammingOnTheStep.VectorPackage.complete
    (empty rules).formed (by decide : appendN ≠ consN) rfl rfl rfl rfl

end Append

/-! ## Taking a dependent pair apart -/

section Sigma

open ProgrammingOnTheStep.SigmaIdentity

/-- The family `Id A x a` over `x : A`. -/
abbrev idFamily {n : Nat} (A a : Tower.Tm n) : Tower.Tm (n + 1) :=
  .id (rename wk A) (.var 0) (rename wk a)

theorem inst0_idFamily {n : Nat} (A a t : Tower.Tm n) : inst0 t (idFamily A a) = .id A t a := by
  show Tm.id (inst0 t (rename wk A)) t (inst0 t (rename wk a)) = .id A t a
  rw [inst0_rename_wk, inst0_rename_wk]

/-- **Equal pairs have equal components**: `pair y q ≡ pair a (refl a) : Σ (x : A). Id A x a`
gives `y ≡ a : A` and `q ≡ refl a : Id A a a`, by projecting and computing. -/
theorem pair_determined {Θ : Context Tower.rules} {A a y q : Tower.Tm Θ.arity}
    (sigmaTyped : Typed Tower.rules Θ.raw (sigmaCode A a) (.head small))
    (typeTyped : Typed Tower.rules Θ.raw A (.head small)) (aTyped : Typed Tower.rules Θ.raw a A)
    (yTyped : Typed Tower.rules Θ.raw y A) (qTyped : Typed Tower.rules Θ.raw q (.id A y a))
    (equal : Equal Tower.rules Θ.raw (.pair y q) (.pair a (.refl a)) (sigmaCode A a)) :
    Equal Tower.rules Θ.raw y a A ∧ Equal Tower.rules Θ.raw q (.refl a) (.id A a a) := by
  have qFamily : Typed Tower.rules Θ.raw q (inst0 y (idFamily A a)) := by
    rw [inst0_idFamily]
    exact qTyped
  have reflFamily : Typed Tower.rules Θ.raw (.refl a) (inst0 a (idFamily A a)) := by
    rw [inst0_idFamily]
    exact .reflIntro aTyped
  have fstLeft : Equal Tower.rules Θ.raw (.fst (.pair y q)) y A :=
    .betaFst sigmaTyped (.sort _) yTyped qFamily
  have fstRight : Equal Tower.rules Θ.raw (.fst (.pair a (.refl a))) a A :=
    .betaFst sigmaTyped (.sort _) aTyped reflFamily
  have first : Equal Tower.rules Θ.raw y a A :=
    .trans fstLeft.symm (.trans (.fstCong equal) fstRight)
  have sndLeft : Equal Tower.rules Θ.raw (.snd (.pair y q)) q (inst0 y (idFamily A a)) :=
    .betaSnd sigmaTyped (.sort _) yTyped qFamily
  have sndRight : Equal Tower.rules Θ.raw (.snd (.pair a (.refl a))) (.refl a)
      (inst0 a (idFamily A a)) :=
    .betaSnd sigmaTyped (.sort _) aTyped reflFamily
  have sndBoth : Equal Tower.rules Θ.raw (.snd (.pair y q)) (.snd (.pair a (.refl a)))
      (inst0 (.fst (.pair y q)) (idFamily A a)) :=
    .sndCong equal
  rw [inst0_idFamily] at sndLeft sndRight sndBoth
  have idEq : ∀ {t : Tower.Tm Θ.arity}, Equal Tower.rules Θ.raw t a A →
      TypeEq Tower.rules Θ.raw (.id A t a) (.id A a a) :=
    fun same => ⟨small, .sort _, .idCong (.refl typeTyped) (.sort _) same (.refl aTyped)⟩
  have toFst : Equal Tower.rules Θ.raw (.fst (.pair y q)) a A := .trans fstLeft first
  exact ⟨first, .trans (TypedEquality.Normalization.Equal.convType sndLeft (idEq first)).symm
    (.trans (TypedEquality.Normalization.Equal.convType sndBoth (idEq toFst)) sndRight)⟩

/-- **Taking the pair apart has a determined answer**: every solution of the firing's information,
at every later frame, reads `y` as `a` and the made row `q` as `refl a`. -/
theorem pair_readback {Θ : Context Tower.rules} (τ : Θ ⟶ pairFiring.helpers.frame)
    (solved : (frames Interface.DependentFull.Controls.setting.levels).Models τ pairFiring.information) :
    Equal Tower.rules Θ.raw (subst τ.substitution (.var 1 : Tower.Tm 4))
        (subst τ.substitution (.var 2 : Tower.Tm 4)) (subst τ.substitution (.var 3 : Tower.Tm 4)) ∧
      Equal Tower.rules Θ.raw (subst τ.substitution (.var 0 : Tower.Tm 4))
        (.refl (subst τ.substitution (.var 2 : Tower.Tm 4)))
        (.id (subst τ.substitution (.var 3 : Tower.Tm 4)) (subst τ.substitution (.var 2 : Tower.Tm 4))
          (subst τ.substitution (.var 2 : Tower.Tm 4))) := by
  rw [pairFiring_information] at solved
  have equation := solved _ (List.mem_singleton_self _)
  have equal : Equal Tower.rules Θ.raw
      (.pair (subst τ.substitution (.var 1 : Tower.Tm 4)) (subst τ.substitution (.var 0 : Tower.Tm 4)))
      (.pair (subst τ.substitution (.var 2 : Tower.Tm 4)) (.refl (subst τ.substitution (.var 2 : Tower.Tm 4))))
      (sigmaCode (subst τ.substitution (.var 3 : Tower.Tm 4)) (subst τ.substitution (.var 2 : Tower.Tm 4))) :=
    equation.2
  exact pair_determined (A := subst τ.substitution (.var 3 : Tower.Tm 4))
    (a := subst τ.substitution (.var 2 : Tower.Tm 4)) (y := subst τ.substitution (.var 1 : Tower.Tm 4))
    (q := subst τ.substitution (.var 0 : Tower.Tm 4)) (pairPattern.1.formed.substitute τ.typed)
    (τ.typed (3 : Fin 4)) (τ.typed (2 : Fin 4)) (τ.typed (1 : Fin 4)) (τ.typed (0 : Fin 4)) equal

end Sigma

#print axioms terms_inv
#print axioms spines_app_inv
#print axioms peel
#print axioms head_type
#print axioms lookup_second
#print axioms cons_second
#print axioms lookup_x_determined
#print axioms lookup_readback
#print axioms eval_second
#print axioms lit_first
#print axioms eval_n_determined
#print axioms eval_readback
#print axioms cons_third
#print axioms lookupRun_x_determined
#print axioms lookupRun_readback
#print axioms types_inv
#print axioms typesW_app_inv
#print axioms vec_injective
#print axioms vec_congr
#print axioms append_second
#print axioms append_fourth
#print axioms append_lengths_readback
#print axioms append_answer_determined
#print axioms append_readback
#print axioms append_solved
#print axioms append_call_undetermined
#print axioms inst0_idFamily
#print axioms pair_determined
#print axioms pair_readback

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RigidReadback
