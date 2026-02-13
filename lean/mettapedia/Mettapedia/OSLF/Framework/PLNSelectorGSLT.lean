import Mathlib.Logic.Relation
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.Logic.PremiseSelectionExternalBayesianity

/-!
# PLN Selector Rules as a GSLT/OSLF Rewrite System

This module packages the core PLN selector rules we use in premise selection as an
explicit one-step rewrite relation, then instantiates that relation as an OSLF
`RewriteSystem`.

The encoded rules are:

1. Two-expert external-Bayesian commutation:
   `update (fuse p q) l  ↦  fuse (update p l) (update q l)`
2. Finite-family commutation:
   `update (fuseFamily xs) l  ↦  fuseFamily (map (update · l) xs)`
3. Normalization strength projection:
   `normalize t e  ↦  e` in strength semantics (for finite nonzero `t`)

We then prove:

- each rewrite step preserves `toStrength` pointwise,
- reflexive-transitive closure also preserves `toStrength`,
- and the relation is directly consumable by OSLF via `RewriteSystem`/`OSLFTypeSystem`.
-/

namespace Mettapedia.OSLF.Framework.PLNSelectorGSLT

open scoped ENNReal
open Mettapedia.Logic.PremiseSelection
open Mettapedia.Logic.EvidenceQuantale

universe u v

/-- Single-process sort for selector-expression rewriting. -/
inductive PLNSelectorSort where
  | Proc
deriving DecidableEq

/-- Core selector-expression language for PLN rule rewrites. -/
inductive PLNSelectorExpr (Goal : Type u) (Fact : Type v) where
  | atom : Scorer Goal Fact → PLNSelectorExpr Goal Fact
  | fuse : PLNSelectorExpr Goal Fact → PLNSelectorExpr Goal Fact → PLNSelectorExpr Goal Fact
  | update : PLNSelectorExpr Goal Fact → PLNSelectorExpr Goal Fact → PLNSelectorExpr Goal Fact
  | normalize : ℝ≥0∞ → PLNSelectorExpr Goal Fact → PLNSelectorExpr Goal Fact
  | fuseFamily : List (PLNSelectorExpr Goal Fact) → PLNSelectorExpr Goal Fact
deriving Inhabited

namespace PLNSelectorExpr

variable {Goal : Type u} {Fact : Type v}

mutual

  /-- Denotation into concrete premise scorers. -/
  noncomputable def eval : PLNSelectorExpr Goal Fact → Scorer Goal Fact
    | .atom s => s
    | .fuse a b =>
        Mettapedia.Logic.PremiseSelection.fuse (eval a) (eval b)
    | .update p l =>
        Mettapedia.Logic.PremiseSelection.update (eval p) (eval l)
    | .normalize t e => normalizeScorer t (eval e)
    | .fuseFamily xs => evalFamily xs

  /-- Denotation of a finite family as left-associated `fuse` over `zeroScorer`. -/
  noncomputable def evalFamily : List (PLNSelectorExpr Goal Fact) → Scorer Goal Fact
    | [] => zeroScorer
    | x :: xs =>
        Mettapedia.Logic.PremiseSelection.fuse (eval x) (evalFamily xs)

end

/-- Strength semantics used for rewrite soundness. -/
noncomputable def strengthAt (e : PLNSelectorExpr Goal Fact) (g : Goal) (f : Fact) : ℝ≥0∞ :=
  Evidence.toStrength ((eval e).score g f)

@[simp] theorem eval_update (p l : PLNSelectorExpr Goal Fact) :
    eval (.update p l) =
      Mettapedia.Logic.PremiseSelection.update (eval p) (eval l) := by
  rfl

@[simp] theorem eval_fuse (a b : PLNSelectorExpr Goal Fact) :
    eval (.fuse a b) =
      Mettapedia.Logic.PremiseSelection.fuse (eval a) (eval b) := by
  rfl

@[simp] theorem eval_normalize (t : ℝ≥0∞) (e : PLNSelectorExpr Goal Fact) :
    eval (.normalize t e) = normalizeScorer t (eval e) := by rfl

@[simp] theorem eval_fuseFamily (xs : List (PLNSelectorExpr Goal Fact)) :
    eval (.fuseFamily xs) = evalFamily xs := by rfl

@[simp] theorem evalFamily_nil :
    evalFamily ([] : List (PLNSelectorExpr Goal Fact)) = zeroScorer := by
  rfl

@[simp] theorem evalFamily_cons (x : PLNSelectorExpr Goal Fact) (xs : List (PLNSelectorExpr Goal Fact)) :
    evalFamily (x :: xs) =
      Mettapedia.Logic.PremiseSelection.fuse (eval x) (evalFamily xs) := by
  rfl

/-- Updating a fused family equals fusing updates (list form). -/
theorem evalFamily_map_update
    (xs : List (PLNSelectorExpr Goal Fact)) (l : PLNSelectorExpr Goal Fact) :
    evalFamily (xs.map (fun e => PLNSelectorExpr.update e l)) =
      Mettapedia.Logic.PremiseSelection.update (evalFamily xs) (eval l) := by
  induction xs with
  | nil =>
      apply Scorer.ext
      intro g f
      apply Evidence.ext'
      · simp [evalFamily, Mettapedia.Logic.PremiseSelection.update,
          zeroScorer, Evidence.tensor_def, Evidence.zero]
      · simp [evalFamily, Mettapedia.Logic.PremiseSelection.update,
          zeroScorer, Evidence.tensor_def, Evidence.zero]
  | cons x xs ih =>
      calc
        evalFamily ((x :: xs).map (fun e => PLNSelectorExpr.update e l))
            =
            Mettapedia.Logic.PremiseSelection.fuse
              (Mettapedia.Logic.PremiseSelection.update (eval x) (eval l))
              (Mettapedia.Logic.PremiseSelection.update (evalFamily xs) (eval l)) := by
                simp [ih]
        _ =
            Mettapedia.Logic.PremiseSelection.update
              (Mettapedia.Logic.PremiseSelection.fuse (eval x) (evalFamily xs))
              (eval l) := by
              simpa using
                (externalBayesianity_hplus_tensor
                  (s₁ := eval x) (s₂ := evalFamily xs) (likelihood := eval l))
        _ =
            Mettapedia.Logic.PremiseSelection.update (evalFamily (x :: xs)) (eval l) := by
              simp [evalFamily]

/-- One-step rewrite relation for the selector-rule DSL. -/
inductive Reduces : PLNSelectorExpr Goal Fact → PLNSelectorExpr Goal Fact → Prop where
  /-- Two-expert external-Bayesianity rewrite. -/
  | extBayes2 (p q l : PLNSelectorExpr Goal Fact) :
      Reduces (.update (.fuse p q) l) (.fuse (.update p l) (.update q l))
  /-- Finite-family external-Bayesianity rewrite. -/
  | extBayesFamily (xs : List (PLNSelectorExpr Goal Fact)) (l : PLNSelectorExpr Goal Fact) :
      Reduces (.update (.fuseFamily xs) l)
        (.fuseFamily (xs.map (fun e => PLNSelectorExpr.update e l)))
  /-- Normalization rewrite in strength semantics (finite nonzero total). -/
  | normalizeStrength (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ⊤) (e : PLNSelectorExpr Goal Fact) :
      Reduces (.normalize t e) e

/-- Every one-step rewrite preserves the pointwise strength denotation. -/
theorem reduces_sound_strength {e e' : PLNSelectorExpr Goal Fact}
    (h : Reduces e e') :
    ∀ g f, strengthAt e g f = strengthAt e' g f := by
  intro g f
  cases h with
  | extBayes2 p q l =>
      have hEq :
          eval (.update (.fuse p q) l) =
            eval (.fuse (.update p l) (.update q l)) := by
        simpa [eval] using
          (externalBayesianity_hplus_tensor
            (s₁ := eval p) (s₂ := eval q) (likelihood := eval l)).symm
      simpa [strengthAt] using congrArg (fun s : Scorer Goal Fact => Evidence.toStrength (s.score g f)) hEq
  | extBayesFamily xs l =>
      have hEq :
          eval (.update (.fuseFamily xs) l) =
            eval (.fuseFamily (xs.map (fun e => PLNSelectorExpr.update e l))) := by
        simpa [eval] using (evalFamily_map_update (xs := xs) (l := l)).symm
      simpa [strengthAt] using congrArg (fun s : Scorer Goal Fact => Evidence.toStrength (s.score g f)) hEq
  | normalizeStrength t ht htop =>
      simpa [strengthAt, eval] using
        (normalizeScorer_toStrength
          (t := t) (s := eval e') (g := g) (f := f) ht htop)

/-- Strength soundness lifts to reflexive-transitive closure of rewrites. -/
theorem rtc_reduces_sound_strength {e e' : PLNSelectorExpr Goal Fact}
    (h : Relation.ReflTransGen Reduces e e') :
    ∀ g f, strengthAt e g f = strengthAt e' g f := by
  induction h with
  | refl =>
      intro g f
      rfl
  | tail htail hstep ih =>
      intro g f
      exact (ih g f).trans (reduces_sound_strength hstep g f)

end PLNSelectorExpr

open PLNSelectorExpr

variable (Goal : Type u) (Fact : Type v)

/-- OSLF `RewriteSystem` instance for PLN selector-rule rewriting. -/
def plnSelectorRewriteSystem : RewriteSystem where
  Sorts := PLNSelectorSort
  procSort := .Proc
  Term := fun _ => PLNSelectorExpr Goal Fact
  Reduces := PLNSelectorExpr.Reduces

/-- OSLF type-system instance induced by the PLN selector rewrite relation. -/
def plnSelectorOSLF : OSLFTypeSystem (plnSelectorRewriteSystem (Goal := Goal) (Fact := Fact)) where
  Pred := fun _ => PLNSelectorExpr Goal Fact → Prop
  frame := fun _ => inferInstance
  satisfies := fun t φ => φ t
  diamond := fun φ p => ∃ q, PLNSelectorExpr.Reduces p q ∧ φ q
  diamond_spec := by
    intro φ p
    rfl
  box := fun φ p => ∀ q, PLNSelectorExpr.Reduces q p → φ q
  box_spec := by
    intro φ p
    rfl
  galois := by
    intro φ ψ
    constructor
    · intro h p hp q hqp
      exact h q ⟨p, hqp, hp⟩
    · intro h p hp
      rcases hp with ⟨q, hpq, hq⟩
      exact h q hq p hpq

/-- OSLF diamond sees the two-expert external-Bayesian rewrite edge. -/
theorem oslf_diamond_extBayes2
    (p q l : PLNSelectorExpr Goal Fact) :
    (plnSelectorOSLF (Goal := Goal) (Fact := Fact)).satisfies
      (.update (.fuse p q) l)
      ((plnSelectorOSLF (Goal := Goal) (Fact := Fact)).diamond
        (fun e => e = .fuse (.update p l) (.update q l))) := by
  refine ⟨.fuse (.update p l) (.update q l), ?_, rfl⟩
  exact PLNSelectorExpr.Reduces.extBayes2 p q l

/-- OSLF diamond sees finite-family external-Bayesian rewrite edges. -/
theorem oslf_diamond_extBayesFamily
    (xs : List (PLNSelectorExpr Goal Fact)) (l : PLNSelectorExpr Goal Fact) :
    (plnSelectorOSLF (Goal := Goal) (Fact := Fact)).satisfies
      (.update (.fuseFamily xs) l)
      ((plnSelectorOSLF (Goal := Goal) (Fact := Fact)).diamond
        (fun e => e = .fuseFamily (xs.map (fun x => PLNSelectorExpr.update x l)))) := by
  refine ⟨.fuseFamily (xs.map (fun x => PLNSelectorExpr.update x l)), ?_, rfl⟩
  exact PLNSelectorExpr.Reduces.extBayesFamily xs l

end Mettapedia.OSLF.Framework.PLNSelectorGSLT
