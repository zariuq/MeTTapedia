import Mettapedia.OSLF.Formula
import Mettapedia.Logic.OSLFEvidenceSemantics

/-!
# Quantified OSLF Formula Extension

First-order extension of `OSLFFormula` with universal and existential quantifiers.
Created as a separate type to avoid blast radius on the propositional core.

## Design

`QFormula` extends `OSLFFormula` with:
- `qforall x φ` : ∀x. φ   — variable x ranges over a domain
- `qexists x φ` : ∃x. φ   — variable x ranges over a domain

Variables are strings.  Quantifier semantics uses an environment (binding map)
from variable names to patterns.  When evaluating ∀x.φ, we take the infimum
over all domain elements d, evaluating φ with x→d added to the environment.

## Semantics (environment-based)

| Formula   | BinaryEvidence semantics                                    |
|-----------|-------------------------------------------------------|
| base φ    | semE R (I_env) φ p  (atoms resolved via environment)  |
| ∀x. φ    | ⨅ d ∈ Domain, qsemE(env[x:=d], φ, p)                |
| ∃x. φ    | ⨆ d ∈ Domain, qsemE(env[x:=d], φ, p)                |

## References

- Goertzel et al., "Probabilistic Logic Networks" (Ch. 7, Quantifier PLN)
- Meredith & Stay, "OSLF" — propositional fragment
- PLNFirstOrder/QuantifierSemantics.lean — weakness-based evaluation
-/

namespace Mettapedia.OSLF.QuantifiedFormula

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.EvidenceQuantale

/-! ## Quantified Formula AST -/

/-- First-order extension of OSLF formulas.

    Adds universal (∀) and existential (∃) quantifiers over Pattern domains.
    The base case embeds propositional `OSLFFormula` unchanged. -/
inductive QFormula where
  | base : OSLFFormula → QFormula
  | qand : QFormula → QFormula → QFormula
  | qor : QFormula → QFormula → QFormula
  | qimp : QFormula → QFormula → QFormula
  | qforall : String → QFormula → QFormula
  | qexists : String → QFormula → QFormula
  deriving Repr

/-! ## Variable Environment

Quantifiers bind variables to patterns via an environment.  When an atom is
evaluated, the environment is used to resolve variable references. -/

/-- Variable environment: maps bound variable names to patterns. -/
abbrev VarEnv := String → Option Pattern

/-- Empty environment (no bindings). -/
def emptyEnv : VarEnv := fun _ => none

/-- Extend an environment with a new binding. -/
def extendEnv (env : VarEnv) (x : String) (d : Pattern) : VarEnv :=
  fun y => if y == x then some d else env y

/-- Resolve an atom using the environment: if the atom name is bound, use
    the pattern from the environment as part of the query. -/
def envAtomSem (baseI : EvidenceAtomSem) (env : VarEnv) : EvidenceAtomSem :=
  fun a p =>
    match env a with
    | some d => baseI a (Pattern.apply "⊛var" [d, p])
    | none => baseI a p

/-! ## Domain -/

/-- Domain type: a set of patterns over which quantifiers range. -/
abbrev Domain := Set Pattern

/-! ## BinaryEvidence-Valued Semantics for Quantified Formulas

The semantics is structurally recursive on the formula, using environments
to track variable bindings instead of substitution. -/

/-- BinaryEvidence-valued semantics of quantified formulas.

    `qsemE R baseI Dom env φ p` evaluates formula φ at pattern p, with
    quantifiers ranging over domain Dom, variable bindings in env,
    and atom meaning from baseI (modulo env resolution).

    - Base formulas use the propositional `semE` with environment-resolved atoms
    - ∀x.φ = ⨅ over domain elements (env extended with x→d)
    - ∃x.φ = ⨆ over domain elements (env extended with x→d) -/
noncomputable def qsemE (R : Pattern → Pattern → Prop) (baseI : EvidenceAtomSem)
    (Dom : Domain) (env : VarEnv) : QFormula → Pattern → BinaryEvidence
  | .base φ, p => semE R (envAtomSem baseI env) φ p
  | .qand φ ψ, p => qsemE R baseI Dom env φ p ⊓ qsemE R baseI Dom env ψ p
  | .qor φ ψ, p => qsemE R baseI Dom env φ p ⊔ qsemE R baseI Dom env ψ p
  | .qimp φ ψ, p => qsemE R baseI Dom env φ p ⇨ qsemE R baseI Dom env ψ p
  | .qforall x φ, p => ⨅ (d : Dom), qsemE R baseI Dom (extendEnv env x d.val) φ p
  | .qexists x φ, p => ⨆ (d : Dom), qsemE R baseI Dom (extendEnv env x d.val) φ p

/-! ## Structural Properties -/

/-- Universal quantifier projects to any domain element. -/
theorem qsemE_forall_le (R : Pattern → Pattern → Prop) (baseI : EvidenceAtomSem)
    (Dom : Domain) (env : VarEnv) (x : String) (φ : QFormula) (p : Pattern)
    (d : Pattern) (hd : d ∈ Dom) :
    qsemE R baseI Dom env (.qforall x φ) p ≤
    qsemE R baseI Dom (extendEnv env x d) φ p :=
  iInf_le (fun (d : Dom) => qsemE R baseI Dom (extendEnv env x d.val) φ p) ⟨d, hd⟩

/-- Existential quantifier injects from any domain element. -/
theorem qsemE_exists_le (R : Pattern → Pattern → Prop) (baseI : EvidenceAtomSem)
    (Dom : Domain) (env : VarEnv) (x : String) (φ : QFormula) (p : Pattern)
    (d : Pattern) (hd : d ∈ Dom) :
    qsemE R baseI Dom (extendEnv env x d) φ p ≤
    qsemE R baseI Dom env (.qexists x φ) p :=
  le_iSup (fun (d : Dom) => qsemE R baseI Dom (extendEnv env x d.val) φ p) ⟨d, hd⟩

/-- ∀ ≤ ∃ when domain is nonempty (evidence version of logical strength ordering). -/
theorem qsemE_forall_le_exists (R : Pattern → Pattern → Prop) (baseI : EvidenceAtomSem)
    (Dom : Domain) (env : VarEnv) (x : String) (φ : QFormula) (p : Pattern)
    (hne : Dom.Nonempty) :
    qsemE R baseI Dom env (.qforall x φ) p ≤
    qsemE R baseI Dom env (.qexists x φ) p := by
  obtain ⟨d, hd⟩ := hne
  exact le_trans (qsemE_forall_le R baseI Dom env x φ p d hd)
                 (qsemE_exists_le R baseI Dom env x φ p d hd)

/-- Base formula semantics is independent of the domain. -/
theorem qsemE_base_eq (R : Pattern → Pattern → Prop) (baseI : EvidenceAtomSem)
    (Dom₁ Dom₂ : Domain) (env : VarEnv) (φ : OSLFFormula) (p : Pattern) :
    qsemE R baseI Dom₁ env (.base φ) p = qsemE R baseI Dom₂ env (.base φ) p := rfl

/-! ## Scope Ambiguity

The key motivation for quantified formulas: different scopings of quantifiers
give different truth values, and this can be expressed as different `QFormula`
structures over the same atoms. -/

/-- Wide-scope ∀ reading: ∀x. man(x) → ∃y. woman(y) ∧ loves(x,y)
    "Every man loves some woman (possibly different)" -/
def scopeWide (man woman loves : String) : QFormula :=
  .qforall "x" (.qimp (.base (.atom man))
    (.qexists "y" (.qand (.base (.atom woman)) (.base (.atom loves)))))

/-- Wide-scope ∃ reading: ∃y. woman(y) ∧ ∀x. man(x) → loves(x,y)
    "There is a specific woman that every man loves" -/
def scopeNarrow (man woman loves : String) : QFormula :=
  .qexists "y" (.qand (.base (.atom woman))
    (.qforall "x" (.qimp (.base (.atom man)) (.base (.atom loves)))))

/-- The narrow-scope (specific) reading entails the wide-scope (non-specific)
    reading.  This is the fundamental scope ordering, at the abstract level:

    For any family of evidence values `f : Dom → Dom → BinaryEvidence`,
    `⨆ y, ⨅ x, f x y ≤ ⨅ x, ⨆ y, f x y`

    (Specific witness uniformly works vs. each x picks its own witness.)
    In quantifier terms: `(∃y. ∀x. P(x,y)) → (∀x. ∃y. P(x,y))`. -/
theorem iSup_iInf_le_iInf_iSup {α : Type*} {ι κ : Type*}
    [CompleteLattice α] (f : ι → κ → α) :
    (⨆ j, ⨅ i, f i j) ≤ (⨅ i, ⨆ j, f i j) := by
  apply le_iInf
  intro i
  apply iSup_le
  intro j
  exact le_trans (iInf_le _ i) (le_iSup _ j)

/-! ## Three-Valued Checker Extension

The bounded model checker returns `.unknown` for quantified formulas,
since it cannot enumerate the (potentially infinite) domain. -/

/-- Three-valued check result for quantified formulas. -/
inductive QCheckResult where
  | sat : QCheckResult
  | unsat : QCheckResult
  | unknown : QCheckResult
  deriving DecidableEq, Repr

/-- Conservative checker: quantifiers always return unknown.
    Base formulas delegate to the propositional checker. -/
def qcheck (atomCheck : AtomCheck)
    (lang : LanguageDef) (fuel : Nat) : QFormula → Pattern → QCheckResult
  | .base φ, p =>
    match checkLangUsing .empty lang atomCheck fuel p φ with
    | .sat => .sat
    | .unsat => .unsat
    | .unknown => .unknown
  | .qand φ ψ, p =>
    match qcheck atomCheck lang fuel φ p, qcheck atomCheck lang fuel ψ p with
    | .sat, .sat => .sat
    | .unsat, _ | _, .unsat => .unsat
    | _, _ => .unknown
  | .qor φ ψ, p =>
    match qcheck atomCheck lang fuel φ p, qcheck atomCheck lang fuel ψ p with
    | .sat, _ | _, .sat => .sat
    | .unsat, .unsat => .unsat
    | _, _ => .unknown
  | .qimp _ _, _ => .unknown  -- conservative for implication
  | .qforall _ _, _ => .unknown
  | .qexists _ _, _ => .unknown

end Mettapedia.OSLF.QuantifiedFormula
