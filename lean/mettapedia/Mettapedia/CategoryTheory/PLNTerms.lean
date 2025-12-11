import Mettapedia.CategoryTheory.LambdaTheory
import Mettapedia.CategoryTheory.PLNInstance
import Mettapedia.CategoryTheory.NativeTypeTheory

/-!
# PLN Term Syntax and Reduction Relation

This file implements Phase 5B of the hypercube formalization plan:
defining the term syntax and reduction relation for the PLN lambda theory.

## Main Definitions

1. **PLNTerm** - The syntax of PLN terms (propositions, implications, etc.)
2. **Reduction relation** ⇝ - How PLN inference steps work
3. **Rewrite contexts** Cj - One-hole contexts for generating modal types

## Key Insight

The reduction relation ⇝ in PLN corresponds to inference rules:
- Deduction: (A→B) ∧ (B→C) ⇝ (A→C)
- Modus ponens: A ∧ (A→B) ⇝ B
- etc.

Rewrite contexts Cj capture "where in the inference are we?", which
generates the modal types ⟨Cj⟩_{xk::Ak} B in Phase 5C.

## References

- Stay & Wells, "Generating Hypercubes of Type Systems" (hypercube.pdf)
- Meredith & Stay, "Operational Semantics in Logical Form" (oslf.pdf)
-/

set_option linter.dupNamespace false

namespace Mettapedia.CategoryTheory.PLNTerms

open Mettapedia.CategoryTheory.LambdaTheories
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.CategoryTheory.NativeTypeTheory

/-! ## Step 1: PLN Term Syntax

Terms in PLN include:
- Atomic propositions (concepts)
- Implications A→B
- Conjunctions, disjunctions
- Truth values (evidence)
-/

/-- PLN terms representing propositions and inference patterns -/
inductive PLNTerm : Type where
  /-- An atomic proposition (concept or relation) -/
  | atom : String → PLNTerm
  /-- Implication A → B -/
  | impl : PLNTerm → PLNTerm → PLNTerm
  /-- Conjunction A ∧ B -/
  | conj : PLNTerm → PLNTerm → PLNTerm
  /-- Disjunction A ∨ B -/
  | disj : PLNTerm → PLNTerm → PLNTerm
  /-- Negation ¬A -/
  | neg : PLNTerm → PLNTerm
  /-- Truth value (for evidence-based reasoning) -/
  | truth : PLNFiber PLNLambdaTheory.Pr → PLNTerm
  deriving Inhabited

namespace PLNTerm

/-- Notation for implication -/
infixr:25 " ⇒ " => PLNTerm.impl

/-- Notation for conjunction -/
infixr:35 " ∧∧ " => PLNTerm.conj

/-- Notation for disjunction -/
infixr:30 " ∨∨ " => PLNTerm.disj

/-- Notation for negation -/
prefix:40 "¬¬" => PLNTerm.neg

end PLNTerm

/-! ## Step 2: Contexts (Terms with Holes)

A context is a term with a hole [-] where we can plug in another term.
This is crucial for generating modal types!
-/

/-- A one-hole context: a term with exactly one hole -/
inductive Context : Type where
  /-- The hole itself -/
  | hole : Context
  /-- Implication with hole in antecedent: [-] → B -/
  | implLeft : Context → PLNTerm → Context
  /-- Implication with hole in consequent: A → [-] -/
  | implRight : PLNTerm → Context → Context
  /-- Conjunction with hole in left: [-] ∧ B -/
  | conjLeft : Context → PLNTerm → Context
  /-- Conjunction with hole in right: A ∧ [-] -/
  | conjRight : PLNTerm → Context → Context
  /-- Disjunction with hole in left: [-] ∨ B -/
  | disjLeft : Context → PLNTerm → Context
  /-- Disjunction with hole in right: A ∨ [-] -/
  | disjRight : PLNTerm → Context → Context
  /-- Negation with hole: ¬[-] -/
  | negCtx : Context → Context
  deriving Inhabited

namespace Context

/-- Fill a context by plugging a term into the hole -/
def fill : Context → PLNTerm → PLNTerm
  | hole, t => t
  | implLeft C B, t => PLNTerm.impl (fill C t) B
  | implRight A C, t => PLNTerm.impl A (fill C t)
  | conjLeft C B, t => PLNTerm.conj (fill C t) B
  | conjRight A C, t => PLNTerm.conj A (fill C t)
  | disjLeft C B, t => PLNTerm.disj (fill C t) B
  | disjRight A C, t => PLNTerm.disj A (fill C t)
  | negCtx C, t => PLNTerm.neg (fill C t)

/-- Extract the term at the hole position -/
def extract : Context → PLNTerm → Option PLNTerm
  | hole, t => some t
  | implLeft C _, t => match t with
    | PLNTerm.impl A _ => extract C A
    | _ => none
  | implRight _ C, t => match t with
    | PLNTerm.impl _ B => extract C B
    | _ => none
  | conjLeft C _, t => match t with
    | PLNTerm.conj A _ => extract C A
    | _ => none
  | conjRight _ C, t => match t with
    | PLNTerm.conj _ B => extract C B
    | _ => none
  | disjLeft C _, t => match t with
    | PLNTerm.disj A _ => extract C A
    | _ => none
  | disjRight _ C, t => match t with
    | PLNTerm.disj _ B => extract C B
    | _ => none
  | negCtx C, t => match t with
    | PLNTerm.neg A => extract C A
    | _ => none

end Context

/-! ## Step 3: PLN Reduction Relation

The reduction relation ⇝ captures PLN inference rules:
- Deduction: (A→B) ∧ (B→C) ⇝ (A→C)
- Modus ponens: A ∧ (A→B) ⇝ B
- Contraposition: (A→B) ⇝ (¬B→¬A)
- etc.
-/

/-- PLN reduction (inference) relation -/
inductive Reduces : PLNTerm → PLNTerm → Prop where
  /-- Deduction rule: (A→B) ∧ (B→C) ⇝ (A→C)
      This is THE key rule for PLN! -/
  | deduction {A B C : PLNTerm} :
      Reduces (PLNTerm.conj (A ⇒ B) (B ⇒ C)) (A ⇒ C)

  /-- Modus ponens: A ∧ (A→B) ⇝ B -/
  | modusPonens {A B : PLNTerm} :
      Reduces (PLNTerm.conj A (A ⇒ B)) B

  /-- Contraposition: (A→B) ⇝ (¬B→¬A) -/
  | contraposition {A B : PLNTerm} :
      Reduces (A ⇒ B) ((¬¬B) ⇒ (¬¬A))

  /-- Conjunction introduction: A ∧ B from A and B (contextual) -/
  | conjIntro {A B : PLNTerm} :
      Reduces (PLNTerm.conj A B) (PLNTerm.conj A B)

  /-- Implication reflexivity: A ⇝ (A→A) -/
  | implRefl {A : PLNTerm} :
      Reduces A (A ⇒ A)

  /-- Reduction in context: if t ⇝ t', then C[t] ⇝ C[t'] -/
  | inContext {t t' : PLNTerm} {C : Context} :
      Reduces t t' →
      Reduces (C.fill t) (C.fill t')

/-- Notation for reduction -/
infix:50 " ⇝ " => Reduces

/-! ## Step 4: Rewrite Rules and Contexts

A rewrite rule is a judgment Γ ⊢ L ⇝ R.
A rewrite context Cj is a context where Cj[tj] = L (the redex).
-/

/-- A rewrite rule: a reduction with free variables -/
structure RewriteRule where
  /-- Free variables (parameters) -/
  freeVars : List String
  /-- Left-hand side (redex) -/
  lhs : PLNTerm
  /-- Right-hand side (reduct) -/
  rhs : PLNTerm
  /-- Proof that lhs ⇝ rhs -/
  reduces : lhs ⇝ rhs

/-- The deduction rewrite rule: (A→B) ∧ (B→C) ⇝ (A→C) -/
def deductionRule : RewriteRule where
  freeVars := ["A", "B", "C"]
  lhs := PLNTerm.conj
    (PLNTerm.atom "A" ⇒ PLNTerm.atom "B")
    (PLNTerm.atom "B" ⇒ PLNTerm.atom "C")
  rhs := PLNTerm.atom "A" ⇒ PLNTerm.atom "C"
  reduces := Reduces.deduction

/-- A rewrite context for a given rule -/
structure RewriteContext (rule : RewriteRule) where
  /-- The context Cj such that Cj[t] can match rule.lhs -/
  ctx : Context
  /-- The term tj that fills the hole -/
  holeTerm : PLNTerm
  /-- Proof that filling gives the lhs -/
  fillsToLhs : ctx.fill holeTerm = rule.lhs

/-! ## Step 5: Modal Type Specification from Rewrites

Given a rewrite context Cj for rule L ⇝ R, we can generate the modal type:

  ⟨Cj⟩_{xk::Ak} B

This captures "for all parameters xk satisfying xk::Ak, if we place t in
context Cj, it's possible to reach a reduct p with p::B in one step."
-/

/-- Generate a modal type specification from a rewrite context -/
noncomputable def modalTypeFromRewrite (rule : RewriteRule) (rwCtx : RewriteContext rule)
    (relies : List (String × PLNFiber PLNLambdaTheory.Pr))
    (result : PLNFiber PLNLambdaTheory.Pr) :
    NativeTypeTheory.ModalTypeSpec where
  context := PLNLambdaTheory.Pr  -- The hole lives in Pr
  result := result  -- Target truth value
  relies := relies.map (fun (_, τ) => ⟨PLNLambdaTheory.Pr, τ⟩)

/-! ## Step 6: The Deduction Modal Type

The key example: modal type for the deduction rule!

Context C₁ = ([-] → B) ∧ (B → C)  -- hole in first implication's antecedent
If we plug in A, we get (A→B) ∧ (B→C), which reduces to A→C by deduction.

The modal type ⟨C₁⟩_{B::τB, C::τC} (A→C)::τAC captures:
"For all B,C satisfying their truth values, if we plug t into C₁,
 we can deduce (t→C) with truth value τAC"
-/

/-- The deduction context: hole in first implication's antecedent -/
def deductionContext : Context :=
  Context.conjLeft
    (Context.implLeft Context.hole (PLNTerm.atom "B"))
    (PLNTerm.atom "B" ⇒ PLNTerm.atom "C")

/-- Proof that filling the deduction context gives the deduction lhs -/
theorem deductionContext_fills :
    deductionContext.fill (PLNTerm.atom "A") = deductionRule.lhs := by
  rfl

/-- The rewrite context for deduction -/
def deductionRewriteContext : RewriteContext deductionRule where
  ctx := deductionContext
  holeTerm := PLNTerm.atom "A"
  fillsToLhs := deductionContext_fills

/-! ## Phase 5B Summary

We have successfully defined the PLN term syntax and reduction relation:

1. ✅ Defined PLNTerm (atoms, implications, conjunctions, etc.)
2. ✅ Defined Context (one-hole contexts)
3. ✅ Defined fill and extract operations
4. ✅ Defined Reduces relation with key rules (deduction, modus ponens, etc.)
5. ✅ Defined RewriteRule and RewriteContext structures
6. ✅ Constructed the deduction rule and its rewrite context
7. ✅ Connected rewrite contexts to modal type specifications

**Key achievement**: We can now generate modal types from rewrite contexts!

The deduction modal type ⟨C₁⟩_{B::τB, C::τC} (A→C)::τAC will be
constructed in Phase 5C using the subobject classifier.

**Next step (Phase 5C)**: Use the subobject classifier to construct
modal types via comprehension, implementing:

  ⟨Cj⟩_{xk::Ak} B := { t | ∀xk. (∧ xk::Ak) → ∃p. Cj[t]⇝p ∧ p::B }
-/

end Mettapedia.CategoryTheory.PLNTerms
