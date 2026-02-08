import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.Lists.SetFold
import Mathlib.Data.Set.Basic

/-!
# Contexts and Labeled Transitions for ρ-Calculus (Locally Nameless)

This file formalizes evaluation contexts and labeled transitions for the ρ-calculus,
as described in Section 4.2.1 of Meredith's "How the Agents Got Their Present Moment".

In locally nameless, input contexts `for(<-n)K` use `lambda` with no binder name.
BVar 0 represents the bound variable.

## Paper Reference

Meredith (2026): "How the Agents Got Their Present Moment", Section 4.2.1, page 5
-/

namespace Mettapedia.OSLF.RhoCalculus.Context

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Evaluation Contexts -/

/-- Evaluation contexts for the rho calculus.

    Paper notation: K ::= □ | for(<-x)K | x!(K) | P|K

    In locally nameless, the input context drops the binder name.
-/
inductive EvalContext : Type where
  | hole : EvalContext
  | input : Pattern → EvalContext → EvalContext  -- for(<-x)K (x is channel pattern)
  | output : Pattern → EvalContext → EvalContext  -- x!(K)
  | par : Pattern → EvalContext → EvalContext    -- P|K
deriving Repr

notation "□" => EvalContext.hole

/-! ## Context Operations -/

/-- Fill a context with a pattern (plug the hole). -/
def fillEvalContext : EvalContext → Pattern → Pattern
  | .hole, p => p
  | .input chan k, p =>
      .apply "PInput" [chan, .lambda (fillEvalContext k p)]
  | .output chan k, p =>
      .apply "POutput" [chan, fillEvalContext k p]
  | .par q k, p =>
      .collection .hashBag [q, fillEvalContext k p] none

/-! ## Free Names -/

/-- Free names of a pattern (channels available for communication). -/
def freeNames : Pattern → Set Pattern
  | .apply "PInput" [n, _] => {n}
  | .apply "POutput" [n, _] => {n}
  | .collection _ elems _ => elems.foldl (fun acc p => acc ∪ freeNames p) ∅
  | .lambda body => freeNames body
  | .apply _ args => args.foldl (fun acc p => acc ∪ freeNames p) ∅
  | _ => ∅

notation:50 "FN(" p ")" => freeNames p

/-- All names in a pattern (including bound names). -/
def allNames : Pattern → Set Pattern
  | .apply "PInput" [n, .lambda body] => {n} ∪ allNames body
  | .apply "POutput" [n, q] => {n} ∪ allNames q
  | .collection _ elems _ => elems.foldl (fun acc p => acc ∪ allNames p) ∅
  | .lambda body => allNames body
  | .apply _ args => args.foldl (fun acc p => acc ∪ allNames p) ∅
  | _ => ∅

notation:50 "N(" p ")" => allNames p

/-! ## Interaction Capability -/

/-- Check if a pattern can interact on a given channel.

    P ↓ₓ just when P = for(<-x)P' | x!(Q) | R, for some R
-/
def canInteract (p : Pattern) (x : Pattern) : Prop :=
  match p with
  | .collection .hashBag elems none =>
      (∃ body, .apply "PInput" [x, .lambda body] ∈ elems) ∧
      (∃ q, .apply "POutput" [x, q] ∈ elems)
  | _ => False

notation:50 p " ↓ " x => canInteract p x

/-! ## Labeled Transitions -/

/-- Labeled transition: P ⇝ᴷ P' -/
inductive LabeledTransition : Pattern → EvalContext → Pattern → Type where
  /-- Input transitions via output context. -/
  | comm_input {p q : Pattern} {x : Pattern} :
      LabeledTransition
        (.apply "PInput" [x, .lambda p])
        (.par (.apply "POutput" [x, q]) .hole)
        (commSubst p q)

  /-- Output transitions via input context. -/
  | comm_output {p q : Pattern} {x : Pattern} :
      LabeledTransition
        (.apply "POutput" [x, q])
        (.par (.apply "PInput" [x, .lambda p]) .hole)
        (commSubst p q)

  /-- General labeled transition from reduction. -/
  | from_reduction {p q : Pattern} {k : EvalContext} :
      Nonempty (Reduces (fillEvalContext k p) q) →
      LabeledTransition p k q

notation:20 p " ⇝[" K "] " q => LabeledTransition p K q

/-! ## Basic Properties -/

/-- Filling a hole is the identity. -/
theorem fillEvalContext_hole (p : Pattern) :
    fillEvalContext □ p = p := by
  rfl

/-- A reduction context is an eval context that only uses hole and parallel. -/
def EvalContext.isReductionCtx : EvalContext → Prop
  | .hole => True
  | .par _ k => k.isReductionCtx
  | .input _ _ => False
  | .output _ _ => False

/-- Reduction contexts preserve reductions through parallel composition. -/
noncomputable def fillEvalContext_preserves_reduces (k : EvalContext) (p p' r : Pattern)
    (h_red : Reduces p p') (h_ctx : k.isReductionCtx) :
    Reduces (fillEvalContext k (.collection .hashBag [p, r] none))
            (fillEvalContext k (.collection .hashBag [p', r] none)) :=
  match k, h_ctx with
  | .hole, _ =>
      Reduces.par h_red
  | .par env k_inner, h_inner =>
      show Reduces
        (.collection .hashBag ([env] ++ [fillEvalContext k_inner (.collection .hashBag [p, r] none)] ++ []) none)
        (.collection .hashBag ([env] ++ [fillEvalContext k_inner (.collection .hashBag [p', r] none)] ++ []) none)
      from Reduces.par_any (fillEvalContext_preserves_reduces k_inner p p' r h_red h_inner)

/-- Free names of parallel composition is the union. -/
theorem freeNames_par (p q : Pattern) :
  freeNames (.collection .hashBag [p, q] none) = freeNames p ∪ freeNames q := by
  simp only [freeNames]
  exact Mettapedia.Lists.SetFold.List.foldl_union_pair freeNames p q

/-- canInteract for parallel composition is symmetric in the list order. -/
theorem canInteract_par_comm (a b : Pattern) (x : Pattern) :
    canInteract (.collection .hashBag [a, b] none) x ↔
    canInteract (.collection .hashBag [b, a] none) x := by
  unfold canInteract
  constructor
  · intro ⟨hinput, houtput⟩
    constructor
    · obtain ⟨body, hmem⟩ := hinput
      refine ⟨body, ?_⟩
      exact (Mettapedia.Lists.SetFold.List.mem_of_mem_cons_cons a b _).mp hmem
    · obtain ⟨q, hmem⟩ := houtput
      refine ⟨q, ?_⟩
      exact (Mettapedia.Lists.SetFold.List.mem_of_mem_cons_cons a b _).mp hmem
  · intro ⟨hinput, houtput⟩
    constructor
    · obtain ⟨body, hmem⟩ := hinput
      refine ⟨body, ?_⟩
      exact (Mettapedia.Lists.SetFold.List.mem_of_mem_cons_cons b a _).mp hmem
    · obtain ⟨q, hmem⟩ := houtput
      refine ⟨q, ?_⟩
      exact (Mettapedia.Lists.SetFold.List.mem_of_mem_cons_cons b a _).mp hmem

/-- If a pattern can interact on x, then x is in its free names. -/
theorem canInteract_implies_freeNames {p x : Pattern} :
    canInteract p x → x ∈ freeNames p := by
  intro h
  simp only [canInteract] at h
  split at h
  · obtain ⟨hinput, _houtput⟩ := h
    obtain ⟨body, hmem⟩ := hinput
    simp only [freeNames]
    rw [Mettapedia.Lists.SetFold.Set.mem_foldl_union]
    refine ⟨.apply "PInput" [x, .lambda body], hmem, ?_⟩
    simp [freeNames]
  · exact False.elim h

/-- canInteract is preserved under list permutation. -/
theorem canInteract_perm {elems₁ elems₂ : List Pattern}
    (h : elems₁.Perm elems₂) (x : Pattern) :
    canInteract (.collection .hashBag elems₁ none) x ↔
    canInteract (.collection .hashBag elems₂ none) x := by
  simp only [canInteract]
  constructor
  · intro ⟨⟨body, hi⟩, ⟨q, ho⟩⟩
    exact ⟨⟨body, h.mem_iff.mp hi⟩, ⟨q, h.mem_iff.mp ho⟩⟩
  · intro ⟨⟨body, hi⟩, ⟨q, ho⟩⟩
    exact ⟨⟨body, h.mem_iff.mpr hi⟩, ⟨q, h.mem_iff.mpr ho⟩⟩

/-- If a bag has both input and output on the same channel, COMM fires. -/
theorem reduces_of_canInteract {elems : List Pattern} {x : Pattern}
    (hcan : canInteract (.collection .hashBag elems none) x) :
    ∃ q, Nonempty (Reduces (.collection .hashBag elems none) q) := by
  simp only [canInteract] at hcan
  obtain ⟨⟨p_body, h_input⟩, ⟨q_payload, h_output⟩⟩ := hcan
  let input_proc := Pattern.apply "PInput" [x, .lambda p_body]
  let output_proc := Pattern.apply "POutput" [x, q_payload]
  have h_ne : output_proc ≠ input_proc := by
    intro h; injection h with h_name _; exact absurd h_name (by decide)
  obtain ⟨before₁, after₁, h_split₁⟩ := List.mem_iff_append.mp h_output
  have h_input_rest : input_proc ∈ before₁ ++ after₁ := by
    rw [h_split₁] at h_input
    simp only [List.mem_append, List.mem_cons] at h_input
    rcases h_input with h_b | h_eq | h_a
    · exact List.mem_append_left after₁ h_b
    · exact absurd h_eq h_ne.symm
    · exact List.mem_append_right before₁ h_a
  obtain ⟨before₂, after₂, h_split₂⟩ := List.mem_iff_append.mp h_input_rest
  let other_rest := before₂ ++ after₂
  have h_perm : elems.Perm (output_proc :: input_proc :: other_rest) := by
    rw [h_split₁]
    exact List.perm_middle.trans (List.Perm.cons output_proc
      (by rw [h_split₂]; exact List.perm_middle))
  have h_comm : Reduces
      (.collection .hashBag (output_proc :: input_proc :: other_rest) none)
      (.collection .hashBag (commSubst p_body q_payload :: other_rest) none) :=
    @Reduces.comm x q_payload p_body other_rest
  use .collection .hashBag (commSubst p_body q_payload :: other_rest) none
  exact ⟨Reduces.equiv
    (StructuralCongruence.par_perm _ _ h_perm)
    h_comm
    (StructuralCongruence.refl _)⟩

/-- Labeled transitions correspond to reductions in filled contexts. -/
theorem labeled_implies_reduces {p q : Pattern} {k : EvalContext} :
    Nonempty (p ⇝[k] q) → Nonempty (fillEvalContext k p ⇝ q) := by
  intro ⟨h⟩
  cases h with
  | @comm_input p_body q_payload x =>
      simp only [fillEvalContext]
      constructor
      have comm_rule := @Reduces.comm x q_payload p_body ([] : List Pattern)
      simp only [List.append_nil] at comm_rule
      exact Reduces.equiv
        (StructuralCongruence.refl _)
        comm_rule
        (StructuralCongruence.par_singleton _)
  | @comm_output p_body q_payload x =>
      unfold fillEvalContext
      constructor
      have comm_rule := @Reduces.comm x q_payload p_body ([] : List Pattern)
      simp only [List.append_nil] at comm_rule
      exact Reduces.equiv
        (StructuralCongruence.par_comm _ _)
        comm_rule
        (StructuralCongruence.par_singleton _)
  | from_reduction h_reduces =>
      exact h_reduces

/-! ## Parallel Components -/

/-- Extract top-level parallel components of a pattern. -/
def parComponents : Pattern → List Pattern
  | .collection .hashBag elems none => elems
  | p => [p]

/-- parComponents p is either [p] (non-bag) or p's elements (bag). -/
theorem parComponentsSpec (p : Pattern) :
    (parComponents p = [p]) ∨
    (∃ elems, p = .collection .hashBag elems none ∧ parComponents p = elems) := by
  unfold parComponents; split
  · next elems => exact .inr ⟨elems, rfl, rfl⟩
  · exact .inl rfl

/-- Flattening a bag at the head of parallel composition. -/
theorem par_flatten_head (elems rest : List Pattern) :
    StructuralCongruence
      (.collection .hashBag (.collection .hashBag elems none :: rest) none)
      (.collection .hashBag (elems ++ rest) none) := by
  have perm1 : ([Pattern.collection .hashBag elems none] ++ rest).Perm
      (rest ++ [Pattern.collection .hashBag elems none]) := List.perm_append_comm
  have step1 := StructuralCongruence.par_perm _ _ perm1
  have step2 := StructuralCongruence.par_flatten rest elems
  have perm3 : (rest ++ elems).Perm (elems ++ rest) := List.perm_append_comm
  have step3 := StructuralCongruence.par_perm _ _ perm3
  exact StructuralCongruence.trans _ _ _ step1
    (StructuralCongruence.trans _ _ _ step2 step3)

/-- Both-bags flattening -/
theorem par_sc_flatten_bags (as es : List Pattern) :
    StructuralCongruence
      (.collection .hashBag [.collection .hashBag as none, .collection .hashBag es none] none)
      (.collection .hashBag (as ++ es) none) :=
  StructuralCongruence.trans _ _ _
    (StructuralCongruence.par_flatten [.collection .hashBag as none] es)
    (par_flatten_head as es)

/-- Left-bag flattening -/
theorem par_sc_flatten_left (as : List Pattern) (e : Pattern) :
    StructuralCongruence
      (.collection .hashBag [.collection .hashBag as none, e] none)
      (.collection .hashBag (as ++ [e]) none) :=
  par_flatten_head as [e]

/-- Right-bag flattening -/
theorem par_sc_flatten_right (a : Pattern) (es : List Pattern) :
    StructuralCongruence
      (.collection .hashBag [a, .collection .hashBag es none] none)
      (.collection .hashBag (a :: es) none) :=
  StructuralCongruence.par_flatten [a] es

/-- General flattening -/
theorem par_sc_flatten (a e : Pattern) :
    StructuralCongruence
      (.collection .hashBag [a, e] none)
      (.collection .hashBag (parComponents a ++ parComponents e) none) := by
  rcases parComponentsSpec a with ha | ⟨as, ha_eq, ha_pc⟩
  · rw [ha]
    rcases parComponentsSpec e with he | ⟨es, he_eq, he_pc⟩
    · rw [he]; exact StructuralCongruence.refl _
    · rw [he_pc, he_eq]; exact StructuralCongruence.par_flatten [a] es
  · rw [ha_pc, ha_eq]
    rcases parComponentsSpec e with he | ⟨es, he_eq, he_pc⟩
    · rw [he]; exact par_flatten_head as [e]
    · rw [he_pc, he_eq]
      exact StructuralCongruence.trans _ _ _
        (StructuralCongruence.par_flatten [.collection .hashBag as none] es)
        (par_flatten_head as es)

end Mettapedia.OSLF.RhoCalculus.Context
