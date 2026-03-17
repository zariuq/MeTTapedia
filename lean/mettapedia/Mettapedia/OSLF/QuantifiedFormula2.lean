import Mettapedia.OSLF.Formula
import Mettapedia.Logic.OSLFEvidenceSemantics

/-!
# Quantified OSLF Formula v2: Argument-Aware Atom Semantics

Upgrade from `QuantifiedFormula.lean`: variables live in **terms**, not atom names.

## Motivation

In v1, `envAtomSem` resolves a bound variable by checking whether the **atom name**
matches a variable name in the environment. This conflates binding structure with
the atom vocabulary. In v2:

- **`QTerm`** represents term syntax with variables, constants, and application.
- **`QAtom`** bundles a predicate name with term arguments: `loves(x, y)`.
- **`QFormula2`** uses `qatom QAtom` instead of `base (atom name)`.
- **`QEvidenceAtomSem`** takes `String → List Pattern → Pattern → BinaryEvidence`:
  predicate name, evaluated arguments, evaluation point.

## Design

```
QTerm     ::= var String | const Pattern | app String (List QTerm)
QAtom     ::= { pred : String, args : List QTerm }
QFormula2 ::= top | bot | qatom QAtom | and | or | imp | dia | box
            | qforall String QFormula2 | qexists String QFormula2
```

Quantifier semantics is the same infimum/supremum over a domain as v1,
but atom evaluation now passes **evaluated argument patterns** instead
of wrapping the atom name in `⊛var`.

## What This File Contains (core only)

- `QTerm`, `QAtom`, `QFormula2` inductive types
- `VarEnv2`, `extendEnv2`, `evalTerm`, `evalTerms` for term evaluation
- `QEvidenceAtomSem` — argument-aware atom interpretation
- `qsemE2` — evidence semantics
- 4 proven base lemmas (no sorry)

Bridge theorems to PLN/weakness live in a separate file.
-/

namespace Mettapedia.OSLF.QuantifiedFormula2

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.EvidenceQuantale

/-! ## Term Syntax -/

/-- Term syntax with variables, constants (patterns), and named application. -/
inductive QTerm where
  | var : String → QTerm
  | const : Pattern → QTerm
  | app : String → List QTerm → QTerm
  deriving Repr

/-- Atom with a predicate name and term arguments. -/
structure QAtom where
  pred : String
  args : List QTerm
  deriving Repr

/-! ## Quantified Formula v2 -/

/-- Quantified OSLF formula with argument-aware atoms and modalities. -/
inductive QFormula2 where
  | top : QFormula2
  | bot : QFormula2
  | qatom : QAtom → QFormula2
  | qand : QFormula2 → QFormula2 → QFormula2
  | qor : QFormula2 → QFormula2 → QFormula2
  | qimp : QFormula2 → QFormula2 → QFormula2
  | dia : QFormula2 → QFormula2
  | box : QFormula2 → QFormula2
  | qforall : String → QFormula2 → QFormula2
  | qexists : String → QFormula2 → QFormula2
  deriving Repr

/-! ## Variable Environment -/

/-- Variable environment v2: same type as v1 but semantically distinct
    (used to evaluate QTerms, not to hack atom names). -/
abbrev VarEnv2 := String → Option Pattern

/-- Empty environment. -/
def emptyEnv2 : VarEnv2 := fun _ => none

/-- Extend environment with a binding x ↦ d. -/
def extendEnv2 (env : VarEnv2) (x : String) (d : Pattern) : VarEnv2 :=
  fun y => if y == x then some d else env y

/-! ## Term Evaluation -/

mutual
/-- Evaluate a term under a variable environment.
    Returns `none` if any variable is unbound. -/
def evalTerm (env : VarEnv2) : QTerm → Option Pattern
  | .var x => env x
  | .const p => some p
  | .app f ts =>
    match evalTerms env ts with
    | some args => some (Pattern.apply f args)
    | none => none

/-- Evaluate a list of terms. Returns `none` if any term fails. -/
def evalTerms (env : VarEnv2) : List QTerm → Option (List Pattern)
  | [] => some []
  | t :: ts =>
    match evalTerm env t, evalTerms env ts with
    | some v, some vs => some (v :: vs)
    | _, _ => none
end

/-! ## Argument-Aware Atom Interpretation -/

/-- Atom semantics that receives the predicate name, evaluated arguments,
    and the evaluation point (world/pattern). -/
def QEvidenceAtomSem := String → List Pattern → Pattern → BinaryEvidence

/-- Domain: set of patterns over which quantifiers range. -/
abbrev Domain2 := Set Pattern

/-! ## BinaryEvidence Semantics v2

The key difference from v1: atoms are evaluated by passing the **evaluated argument
patterns** to the atom interpretation, rather than hacking the atom name via the
environment. -/

/-- BinaryEvidence semantics for quantified formulas v2.

    `qsemE2 R I Dom env φ p` evaluates formula `φ` at pattern `p`, with:
    - `R` : accessibility relation (for dia/box)
    - `I` : argument-aware atom interpretation
    - `Dom` : quantifier domain
    - `env` : current variable bindings -/
noncomputable def qsemE2 (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2) : QFormula2 → Pattern → BinaryEvidence
  | .top, _ => ⊤
  | .bot, _ => ⊥
  | .qatom a, p =>
    match evalTerms env a.args with
    | some args => I a.pred args p
    | none => ⊥  -- unbound variable → no evidence
  | .qand φ ψ, p => qsemE2 R I Dom env φ p ⊓ qsemE2 R I Dom env ψ p
  | .qor φ ψ, p => qsemE2 R I Dom env φ p ⊔ qsemE2 R I Dom env ψ p
  | .qimp φ ψ, p => qsemE2 R I Dom env φ p ⇨ qsemE2 R I Dom env ψ p
  | .dia φ, p => ⨆ (q : {q // R p q}), qsemE2 R I Dom env φ q.val
  | .box φ, p => ⨅ (q : {q // R q p}), qsemE2 R I Dom env φ q.val
  | .qforall x φ, p => ⨅ (d : Dom), qsemE2 R I Dom (extendEnv2 env x d.val) φ p
  | .qexists x φ, p => ⨆ (d : Dom), qsemE2 R I Dom (extendEnv2 env x d.val) φ p

/-! ## Basic Structural Lemmas -/

/-- Variable lookup in extended environment hits the bound variable. -/
theorem evalTerm_var_hit (env : VarEnv2) (x : String) (p : Pattern) :
    evalTerm (extendEnv2 env x p) (.var x) = some p := by
  simp [evalTerm, extendEnv2]

/-- Extending the environment shadows the variable. -/
theorem evalTerm_extend_shadow (env : VarEnv2) (x : String) (p1 p2 : Pattern) :
    evalTerm (extendEnv2 (extendEnv2 env x p1) x p2) (.var x) = some p2 := by
  simp [evalTerm, extendEnv2]

/-- Constant terms are independent of the environment. -/
theorem evalTerm_const (env : VarEnv2) (p : Pattern) :
    evalTerm env (.const p) = some p := rfl

/-- Universal quantifier projects to any domain element. -/
theorem qsemE2_forall_le (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2) (x : String) (φ : QFormula2) (p : Pattern)
    (d : Pattern) (hd : d ∈ Dom) :
    qsemE2 R I Dom env (.qforall x φ) p ≤
    qsemE2 R I Dom (extendEnv2 env x d) φ p :=
  iInf_le (fun (d : Dom) => qsemE2 R I Dom (extendEnv2 env x d.val) φ p) ⟨d, hd⟩

/-- Existential quantifier injects from any domain element. -/
theorem qsemE2_exists_le (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2) (x : String) (φ : QFormula2) (p : Pattern)
    (d : Pattern) (hd : d ∈ Dom) :
    qsemE2 R I Dom (extendEnv2 env x d) φ p ≤
    qsemE2 R I Dom env (.qexists x φ) p :=
  le_iSup (fun (d : Dom) => qsemE2 R I Dom (extendEnv2 env x d.val) φ p) ⟨d, hd⟩

/-- ∀ ≤ ∃ when domain is nonempty (fundamental quantifier strength ordering). -/
theorem qsemE2_forall_le_exists (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2) (x : String) (φ : QFormula2) (p : Pattern)
    (hne : Dom.Nonempty) :
    qsemE2 R I Dom env (.qforall x φ) p ≤
    qsemE2 R I Dom env (.qexists x φ) p := by
  obtain ⟨d, hd⟩ := hne
  exact le_trans (qsemE2_forall_le R I Dom env x φ p d hd)
                 (qsemE2_exists_le R I Dom env x φ p d hd)

/-- Quantifier-free fragment: no qforall or qexists. -/
def quantifierFree : QFormula2 → Prop
  | .top | .bot | .qatom _ => True
  | .qand φ ψ | .qor φ ψ | .qimp φ ψ => quantifierFree φ ∧ quantifierFree ψ
  | .dia φ | .box φ => quantifierFree φ
  | .qforall _ _ | .qexists _ _ => False

/-- Quantifier-free formulas have domain-independent semantics,
    since the domain only appears in quantifier evaluation. -/
theorem qsemE2_quantifierFree_domain_irrel (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom₁ Dom₂ : Domain2) (env : VarEnv2) {φ : QFormula2} (hqf : quantifierFree φ)
    (p : Pattern) :
    qsemE2 R I Dom₁ env φ p = qsemE2 R I Dom₂ env φ p := by
  induction φ generalizing p env with
  | top => rfl
  | bot => rfl
  | qatom _ => simp [qsemE2]
  | qand φ ψ ihφ ihψ =>
    simp only [qsemE2]; congr 1 <;> [exact ihφ env hqf.1 p; exact ihψ env hqf.2 p]
  | qor φ ψ ihφ ihψ =>
    simp only [qsemE2]; congr 1 <;> [exact ihφ env hqf.1 p; exact ihψ env hqf.2 p]
  | qimp φ ψ ihφ ihψ =>
    simp only [qsemE2]; congr 1 <;> [exact ihφ env hqf.1 p; exact ihψ env hqf.2 p]
  | dia φ ih =>
    simp only [qsemE2]
    exact iSup_congr fun ⟨q, _⟩ => ih env hqf q
  | box φ ih =>
    simp only [qsemE2]
    exact iInf_congr fun ⟨q, _⟩ => ih env hqf q
  | qforall _ _ => exact absurd hqf (by simp [quantifierFree])
  | qexists _ _ => exact absurd hqf (by simp [quantifierFree])

/-- Base formulas (top, bot) are independent of the domain. -/
theorem qsemE2_top_domain_irrel (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom₁ Dom₂ : Domain2) (env : VarEnv2) (p : Pattern) :
    qsemE2 R I Dom₁ env .top p = qsemE2 R I Dom₂ env .top p := rfl

theorem qsemE2_bot_domain_irrel (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom₁ Dom₂ : Domain2) (env : VarEnv2) (p : Pattern) :
    qsemE2 R I Dom₁ env .bot p = qsemE2 R I Dom₂ env .bot p := rfl

/-- Atom semantics depends only on the environment (not the domain). -/
theorem qsemE2_qatom_domain_irrel (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom₁ Dom₂ : Domain2) (env : VarEnv2) (a : QAtom) (p : Pattern) :
    qsemE2 R I Dom₁ env (.qatom a) p = qsemE2 R I Dom₂ env (.qatom a) p := by
  simp [qsemE2]

/-! ## Free Variables

Proper free-variable computation: `.var x` contributes `{x}` to the free set,
and `qforall x φ` / `qexists x φ` remove `x` (since `x` is bound).

This fixes the naive `closedQF2` that rejected ALL `.var` nodes — even bound
ones like `x` in `∀x. P(x)`. The corrected `closedQF2` is `freeVarsQF2 φ = ∅`,
which correctly classifies `∀x. P(x)` as closed. -/

mutual
/-- Free variables of a term. -/
def freeVarsTerm : QTerm → Finset String
  | .var x => {x}
  | .const _ => ∅
  | .app _ ts => freeVarsTerms ts

/-- Free variables of a term list (union). -/
def freeVarsTerms : List QTerm → Finset String
  | [] => ∅
  | t :: ts => freeVarsTerm t ∪ freeVarsTerms ts
end

/-- Free variables of an atom (union over argument terms). -/
def freeVarsAtom (a : QAtom) : Finset String := freeVarsTerms a.args

/-- Free variables of a quantified formula.

    Quantifier binders (`qforall x`, `qexists x`) remove `x` from the
    free set, correctly handling bound variables. -/
def freeVarsQF2 : QFormula2 → Finset String
  | .top | .bot => ∅
  | .qatom a => freeVarsAtom a
  | .qand φ ψ | .qor φ ψ | .qimp φ ψ => freeVarsQF2 φ ∪ freeVarsQF2 ψ
  | .dia φ | .box φ => freeVarsQF2 φ
  | .qforall x φ | .qexists x φ => freeVarsQF2 φ \ {x}

/-- A formula is closed if it has no free variables.

    Unlike the naive version that rejected all `.var` nodes, this correctly
    classifies `∀x. P(x)` as closed (since `x` is bound by `∀x`). -/
def closedQF2 (φ : QFormula2) : Prop := freeVarsQF2 φ = ∅

/-! ## Environment Agreement and Irrelevance

The fundamental theorem: `qsemE2` depends only on the environment's values
at free variables. Closed formulas (no free variables) are a corollary. -/

mutual
/-- Term evaluation depends only on the environment at free variables. -/
theorem evalTerm_env_agree (env1 env2 : VarEnv2) :
    ∀ {t : QTerm}, (∀ x ∈ freeVarsTerm t, env1 x = env2 x) →
      evalTerm env1 t = evalTerm env2 t
  | .var x, h => h x (Finset.mem_singleton_self x)
  | .const _, _ => rfl
  | .app _ ts, h => by
    simp only [evalTerm]
    rw [evalTerms_env_agree env1 env2 h]

/-- Term-list evaluation depends only on the environment at free variables. -/
theorem evalTerms_env_agree (env1 env2 : VarEnv2) :
    ∀ {ts : List QTerm}, (∀ x ∈ freeVarsTerms ts, env1 x = env2 x) →
      evalTerms env1 ts = evalTerms env2 ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [evalTerms]
    have ht : ∀ x ∈ freeVarsTerm t, env1 x = env2 x :=
      fun x hx => h x (Finset.mem_union_left _ hx)
    have hts : ∀ x ∈ freeVarsTerms ts, env1 x = env2 x :=
      fun x hx => h x (Finset.mem_union_right _ hx)
    rw [evalTerm_env_agree env1 env2 ht, evalTerms_env_agree env1 env2 hts]
end

/-- **Environment agreement theorem**: `qsemE2` gives the same evidence
    when two environments agree on all free variables of the formula.

    This is the fundamental semantic locality principle: the meaning of a
    formula depends only on the values of its free variables.

    Subsumes the old `qsemE2_closed_env_irrel` (where agreement is vacuous)
    and properly handles quantifiers: `qforall x φ` only requires agreement
    on `freeVarsQF2 φ \ {x}`, since `extendEnv2` makes both envs agree on `x`. -/
theorem qsemE2_env_agree_on_free
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2)
    {φ : QFormula2} (env1 env2 : VarEnv2)
    (hagree : ∀ x ∈ freeVarsQF2 φ, env1 x = env2 x)
    (p : Pattern) :
    qsemE2 R I Dom env1 φ p = qsemE2 R I Dom env2 φ p := by
  induction φ generalizing p env1 env2 with
  | top => rfl
  | bot => rfl
  | qatom a =>
    simp only [qsemE2]
    rw [evalTerms_env_agree env1 env2 hagree]
  | qand φ ψ ihφ ihψ =>
    simp only [qsemE2]
    have hφ : ∀ x ∈ freeVarsQF2 φ, env1 x = env2 x :=
      fun x hx => hagree x (Finset.mem_union_left _ hx)
    have hψ : ∀ x ∈ freeVarsQF2 ψ, env1 x = env2 x :=
      fun x hx => hagree x (Finset.mem_union_right _ hx)
    exact congr_arg₂ _ (ihφ env1 env2 hφ p) (ihψ env1 env2 hψ p)
  | qor φ ψ ihφ ihψ =>
    simp only [qsemE2]
    have hφ : ∀ x ∈ freeVarsQF2 φ, env1 x = env2 x :=
      fun x hx => hagree x (Finset.mem_union_left _ hx)
    have hψ : ∀ x ∈ freeVarsQF2 ψ, env1 x = env2 x :=
      fun x hx => hagree x (Finset.mem_union_right _ hx)
    exact congr_arg₂ _ (ihφ env1 env2 hφ p) (ihψ env1 env2 hψ p)
  | qimp φ ψ ihφ ihψ =>
    simp only [qsemE2]
    have hφ : ∀ x ∈ freeVarsQF2 φ, env1 x = env2 x :=
      fun x hx => hagree x (Finset.mem_union_left _ hx)
    have hψ : ∀ x ∈ freeVarsQF2 ψ, env1 x = env2 x :=
      fun x hx => hagree x (Finset.mem_union_right _ hx)
    exact congr_arg₂ _ (ihφ env1 env2 hφ p) (ihψ env1 env2 hψ p)
  | dia φ ih =>
    simp only [qsemE2]
    exact iSup_congr fun ⟨q, _⟩ => ih env1 env2 hagree q
  | box φ ih =>
    simp only [qsemE2]
    exact iInf_congr fun ⟨q, _⟩ => ih env1 env2 hagree q
  | qforall x φ ih =>
    simp only [qsemE2]
    exact iInf_congr fun ⟨d, _⟩ => ih (extendEnv2 env1 x d) (extendEnv2 env2 x d)
      (fun y hy => by
        simp only [extendEnv2]
        by_cases hyx : y == x
        · simp [hyx]
        · simp [hyx]
          exact hagree y (Finset.mem_sdiff.mpr ⟨hy, by simp [Finset.mem_singleton]; exact fun h => by simp [h] at hyx⟩)) p
  | qexists x φ ih =>
    simp only [qsemE2]
    exact iSup_congr fun ⟨d, _⟩ => ih (extendEnv2 env1 x d) (extendEnv2 env2 x d)
      (fun y hy => by
        simp only [extendEnv2]
        by_cases hyx : y == x
        · simp [hyx]
        · simp [hyx]
          exact hagree y (Finset.mem_sdiff.mpr ⟨hy, by simp [Finset.mem_singleton]; exact fun h => by simp [h] at hyx⟩)) p

/-- **Closed formula environment irrelevance** (corollary of `qsemE2_env_agree_on_free`).

    A closed formula (`freeVarsQF2 φ = ∅`) gives the same evidence under any
    two environments. This correctly handles bound variables: `∀x. P(x)` is
    closed and satisfies this theorem. -/
theorem qsemE2_closed_env_irrel
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2)
    {φ : QFormula2} (hclosed : closedQF2 φ)
    (env1 env2 : VarEnv2) (p : Pattern) :
    qsemE2 R I Dom env1 φ p = qsemE2 R I Dom env2 φ p :=
  qsemE2_env_agree_on_free R I Dom env1 env2
    (fun x hx => absurd (hclosed ▸ hx : x ∈ (∅ : Finset String)) (Finset.notMem_empty x)) p

/-- Positive example: `∀x. P(x)` is correctly classified as closed. -/
example : closedQF2 (.qforall "x" (.qatom ⟨"P", [.var "x"]⟩)) := by
  simp [closedQF2, freeVarsQF2, freeVarsAtom, freeVarsTerms, freeVarsTerm]

/-- Positive example: `P(c)` with a constant argument is closed. -/
example : closedQF2 (.qatom ⟨"P", [.const (.apply "c" [])]⟩) := by
  simp [closedQF2, freeVarsQF2, freeVarsAtom, freeVarsTerms, freeVarsTerm]

/-- Negative example: `P(x)` with a free variable is NOT closed. -/
example : ¬ closedQF2 (.qatom ⟨"P", [.var "x"]⟩) := by
  simp [closedQF2, freeVarsQF2, freeVarsAtom, freeVarsTerms, freeVarsTerm]

end Mettapedia.OSLF.QuantifiedFormula2
