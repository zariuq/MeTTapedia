import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.PeanoAdd

/-!
# Verified MeTTa, entry 02 -- list append and length over LeaTTa

This entry verifies a small MeTTa list program against LeaTTa's certified
MOPS/KernelStep relation.  Lists are ordinary `Cons`/`Nil` atoms whose elements
are Peano numerals, so the theorem is a genuine all-input computation theorem:
append computes Lean list append, length computes Lean list length, and the
length of an append reaches the Peano sum of the input lengths.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.ListAppendLength

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ContextualStep

def mSym (s : String) : Metta.Atom := .sym s
def mVar (s : String) : Metta.Atom := .var s
def mE (head : String) (args : List Metta.Atom) : Metta.Atom := .expr (.sym head :: args)

def peano : Nat → Metta.Atom
  | 0 => mSym "Z"
  | n + 1 => mE "S" [peano n]

/-! ## §1  The MeTTa program -/

def listAppendLengthRules : List Metta.Atom :=
  [ .expr [mSym "=", mE "listAppend" [mSym "Nil", mVar "ys"], mVar "ys"]
  , .expr [mSym "=", mE "listAppend" [mE "Cons" [mVar "x", mVar "xs"], mVar "ys"],
      mE "Cons" [mVar "x", mE "listAppend" [mVar "xs", mVar "ys"]]]
  , .expr [mSym "=", mE "len" [mSym "Nil"], mSym "Z"]
  , .expr [mSym "=", mE "len" [mE "Cons" [mVar "x", mVar "xs"]],
      mE "S" [mE "len" [mVar "xs"]]] ]

def listAtom : List Nat → Metta.Atom
  | [] => mSym "Nil"
  | x :: xs => mE "Cons" [peano x, listAtom xs]

def appendQuery (xs ys : List Nat) : Metta.Atom :=
  mE "listAppend" [listAtom xs, listAtom ys]

def lenQuery (xs : Metta.Atom) : Metta.Atom :=
  mE "len" [xs]

/-! ## §2  Matcher facts for the root rules -/

private theorem peano_not_var (n : Nat) (v : String) :
    peano n ≠ Metta.Atom.var v := by
  cases n <;> simp [peano, mSym, mE]

private theorem listAtom_not_var (xs : List Nat) (v : String) :
    listAtom xs ≠ Metta.Atom.var v := by
  cases xs <;> simp [listAtom, mSym, mE]

private theorem match_var_nonvar_atom (v : String) (target : Metta.Atom)
    (h : ∀ w, target ≠ Metta.Atom.var w) :
    Metta.matchAtomsWith none (Metta.Atom.var v) target =
      [[Metta.BindingRel.val v target]] := by
  cases target with
  | var w => exact (h w rfl).elim
  | sym _ => simp [Metta.matchAtomsWith]
  | gnd _ => simp [Metta.matchAtomsWith]
  | expr _ => simp [Metta.matchAtomsWith]

private theorem match_cons_vars (head tail : Metta.Atom)
    (hHead : ∀ w, head ≠ Metta.Atom.var w)
    (hTail : ∀ w, tail ≠ Metta.Atom.var w) :
    Metta.matchAtomsWith none (mE "Cons" [mVar "x", mVar "xs"]) (mE "Cons" [head, tail]) =
      [[Metta.BindingRel.val "xs" tail, Metta.BindingRel.val "x" head]] := by
  simp only [mE, mVar, Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith, Metta.Bindings.merge]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom "x" head hHead]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom "xs" tail hTail]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  rfl

private theorem match_cons_vars_raw (head tail : Metta.Atom)
    (hHead : ∀ w, head ≠ Metta.Atom.var w)
    (hTail : ∀ w, tail ≠ Metta.Atom.var w) :
    Metta.matchAtomsWith none
        (Metta.Atom.expr [Metta.Atom.sym "Cons", Metta.Atom.var "x", Metta.Atom.var "xs"])
        (Metta.Atom.expr [Metta.Atom.sym "Cons", head, tail]) =
      [[Metta.BindingRel.val "xs" tail, Metta.BindingRel.val "x" head]] := by
  simpa [mE, mVar] using match_cons_vars head tail hHead hTail

private theorem append_nil_mops_readout (ys : List Nat) :
    listAtom ys ∈ Metta.equalityReductions ⟨listAppendLengthRules⟩ (appendQuery [] ys) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(mE "listAppend" [mSym "Nil", mVar "ys"], mVar "ys"), ?_, ?_⟩
  · simp [listAppendLengthRules, Metta.Space.equalityRules, mE, mSym, mVar]
  · refine ⟨[Metta.BindingRel.val "ys" (listAtom ys)], ?_, ?_⟩
    · simp only [appendQuery, listAtom, mE, mSym, mVar, Metta.matchAtoms,
        Metta.matchAtomsWith]
      unfold Metta.matchAll
      change [Metta.BindingRel.val "ys" (listAtom ys)] ∈
        Metta.matchAll none [[]] [Metta.Atom.var "ys"] [listAtom ys]
      unfold Metta.matchAll
      rw [match_var_nonvar_atom "ys" (listAtom ys) (listAtom_not_var ys)]
      simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
      unfold Metta.matchAll
      simp
    · simp [Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
        Metta.Subst.lookup, mVar]

private theorem append_nil_mops_step (ys : List Nat) :
    Metta.MopsStep listAppendLengthRules (appendQuery [] ys) (listAtom ys) := by
  constructor
  · refine ⟨"listAppend", ?_⟩
    simp [Metta.Minimal.headKey, appendQuery, listAtom, mE, mSym]
  · exact append_nil_mops_readout ys

private theorem append_cons_mops_readout (x : Nat) (xs ys : List Nat) :
    mE "Cons" [peano x, appendQuery xs ys] ∈
      Metta.equalityReductions ⟨listAppendLengthRules⟩ (appendQuery (x :: xs) ys) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(mE "listAppend" [mE "Cons" [mVar "x", mVar "xs"], mVar "ys"],
      mE "Cons" [mVar "x", mE "listAppend" [mVar "xs", mVar "ys"]]), ?_, ?_⟩
  · simp [listAppendLengthRules, Metta.Space.equalityRules, mE, mSym, mVar]
  · refine ⟨[Metta.BindingRel.val "ys" (listAtom ys),
        Metta.BindingRel.val "x" (peano x),
        Metta.BindingRel.val "xs" (listAtom xs)], ?_, ?_⟩
    · simp only [appendQuery, listAtom, mE, mVar, Metta.matchAtoms, Metta.matchAtomsWith]
      unfold Metta.matchAll
      simp [Metta.matchAtomsWith, Metta.Bindings.merge]
      unfold Metta.matchAll
      rw [match_cons_vars_raw (peano x) (listAtom xs)
        (peano_not_var x) (listAtom_not_var xs)]
      simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
      unfold Metta.matchAll
      rw [match_var_nonvar_atom "ys" (listAtom ys) (listAtom_not_var ys)]
      simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
      unfold Metta.matchAll
      simp
    · simp [appendQuery, mE, mVar, Metta.instantiate, Metta.bindingsToSubst,
        Metta.Subst.apply, Metta.Subst.lookup]

private theorem append_cons_mops_step (x : Nat) (xs ys : List Nat) :
    Metta.MopsStep listAppendLengthRules (appendQuery (x :: xs) ys)
      (mE "Cons" [peano x, appendQuery xs ys]) := by
  constructor
  · refine ⟨"listAppend", ?_⟩
    simp [Metta.Minimal.headKey, appendQuery, listAtom, mE]
  · exact append_cons_mops_readout x xs ys

private theorem len_nil_mops_readout :
    mSym "Z" ∈ Metta.equalityReductions ⟨listAppendLengthRules⟩ (lenQuery (listAtom [])) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(mE "len" [mSym "Nil"], mSym "Z"), ?_, ?_⟩
  · simp [listAppendLengthRules, Metta.Space.equalityRules, mE, mSym, mVar]
  · refine ⟨[], ?_, ?_⟩
    · simp only [lenQuery, listAtom, mE, mSym, Metta.matchAtoms, Metta.matchAtomsWith]
      unfold Metta.matchAll
      simp [Metta.matchAtomsWith, Metta.Bindings.merge]
      unfold Metta.matchAll
      simp [Metta.matchAtomsWith, Metta.Bindings.merge]
      unfold Metta.matchAll
      simp
    · simp [Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply, mSym]

private theorem len_nil_mops_step :
    Metta.MopsStep listAppendLengthRules (lenQuery (listAtom [])) (peano 0) := by
  constructor
  · refine ⟨"len", ?_⟩
    simp [Metta.Minimal.headKey, lenQuery, listAtom, mE, mSym]
  · simpa [peano, mSym] using len_nil_mops_readout

private theorem len_cons_mops_readout (x : Nat) (xs : List Nat) :
    mE "S" [lenQuery (listAtom xs)] ∈
      Metta.equalityReductions ⟨listAppendLengthRules⟩ (lenQuery (listAtom (x :: xs))) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(mE "len" [mE "Cons" [mVar "x", mVar "xs"]],
      mE "S" [mE "len" [mVar "xs"]]), ?_, ?_⟩
  · simp [listAppendLengthRules, Metta.Space.equalityRules, mE, mSym, mVar]
  · refine ⟨[Metta.BindingRel.val "x" (peano x),
        Metta.BindingRel.val "xs" (listAtom xs)], ?_, ?_⟩
    · simp only [lenQuery, listAtom, mE, mVar, Metta.matchAtoms, Metta.matchAtomsWith]
      unfold Metta.matchAll
      simp [Metta.matchAtomsWith, Metta.Bindings.merge]
      unfold Metta.matchAll
      rw [match_cons_vars_raw (peano x) (listAtom xs)
        (peano_not_var x) (listAtom_not_var xs)]
      simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
      unfold Metta.matchAll
      simp
    · simp [lenQuery, mE, mVar, Metta.instantiate, Metta.bindingsToSubst,
        Metta.Subst.apply, Metta.Subst.lookup]

private theorem len_cons_mops_step (x : Nat) (xs : List Nat) :
    Metta.MopsStep listAppendLengthRules (lenQuery (listAtom (x :: xs)))
      (mE "S" [lenQuery (listAtom xs)]) := by
  constructor
  · refine ⟨"len", ?_⟩
    simp [Metta.Minimal.headKey, lenQuery, listAtom, mE]
  · exact len_cons_mops_readout x xs

/-! ## §3  Contextual computation theorems -/

inductive CtxMopsStep : Metta.Atom → Metta.Atom → Prop
  | root {a b : Metta.Atom} :
      Metta.MopsStep listAppendLengthRules a b → CtxMopsStep a b
  | consTail {x a b : Metta.Atom} :
      CtxMopsStep a b → CtxMopsStep (mE "Cons" [x, a]) (mE "Cons" [x, b])
  | lenArg {a b : Metta.Atom} :
      CtxMopsStep a b → CtxMopsStep (lenQuery a) (lenQuery b)
  | succ {a b : Metta.Atom} :
      CtxMopsStep a b → CtxMopsStep (mE "S" [a]) (mE "S" [b])

private theorem ctx_step_to_expr_ctx {a b : Metta.Atom} (h : CtxMopsStep a b) :
    ExprCtxMopsStep listAppendLengthRules a b := by
  induction h with
  | root h => exact ExprCtxMopsStep.root h
  | consTail _ ih =>
      exact ExprCtxMopsStep.expr
        (ExprListCtxMopsStep.tail
          (ExprListCtxMopsStep.tail (ExprListCtxMopsStep.head ih)))
  | lenArg _ ih =>
      exact ExprCtxMopsStep.expr (ExprListCtxMopsStep.tail (ExprListCtxMopsStep.head ih))
  | succ _ ih =>
      exact ExprCtxMopsStep.expr (ExprListCtxMopsStep.tail (ExprListCtxMopsStep.head ih))

private theorem ctx_chain_to_expr_ctx {a b : Metta.Atom}
    (h : Relation.ReflTransGen CtxMopsStep a b) :
    Relation.ReflTransGen (ExprCtxMopsStep listAppendLengthRules) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ctx_step_to_expr_ctx step)

private theorem reflTransGen_map_cons_tail {a b x : Metta.Atom}
    (h : Relation.ReflTransGen CtxMopsStep a b) :
    Relation.ReflTransGen CtxMopsStep (mE "Cons" [x, a]) (mE "Cons" [x, b]) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (CtxMopsStep.consTail step)

private theorem reflTransGen_map_len {a b : Metta.Atom}
    (h : Relation.ReflTransGen CtxMopsStep a b) :
    Relation.ReflTransGen CtxMopsStep (lenQuery a) (lenQuery b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (CtxMopsStep.lenArg step)

private theorem reflTransGen_map_succ {a b : Metta.Atom}
    (h : Relation.ReflTransGen CtxMopsStep a b) :
    Relation.ReflTransGen CtxMopsStep (mE "S" [a]) (mE "S" [b]) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (CtxMopsStep.succ step)

private theorem append_reaches_mopsCtx (xs ys : List Nat) :
    Relation.ReflTransGen CtxMopsStep (appendQuery xs ys) (listAtom (xs ++ ys)) := by
  induction xs with
  | nil =>
      simpa [appendQuery, listAtom] using
        Relation.ReflTransGen.single (CtxMopsStep.root (append_nil_mops_step ys))
  | cons x xs ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (CtxMopsStep.root (append_cons_mops_step x xs ys)))
        (by
          simpa [appendQuery, listAtom, List.cons_append] using
            reflTransGen_map_cons_tail (x := peano x) ih)

private theorem len_reaches_mopsCtx (xs : List Nat) :
    Relation.ReflTransGen CtxMopsStep (lenQuery (listAtom xs)) (peano xs.length) := by
  induction xs with
  | nil =>
      simpa [lenQuery, listAtom, peano] using
        Relation.ReflTransGen.single (CtxMopsStep.root len_nil_mops_step)
  | cons x xs ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (CtxMopsStep.root (len_cons_mops_step x xs)))
        (by
          simpa [lenQuery, listAtom, peano] using reflTransGen_map_succ ih)

/-- The append program computes Lean list append over contextual MOPS. -/
theorem appendReachesMopsContext (xs ys : List Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep listAppendLengthRules)
      (appendQuery xs ys) (listAtom (xs ++ ys)) :=
  ctx_chain_to_expr_ctx (append_reaches_mopsCtx xs ys)

/-- The length program computes Lean list length over contextual MOPS. -/
theorem lengthReachesMopsContext (xs : List Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep listAppendLengthRules)
      (lenQuery (listAtom xs)) (peano xs.length) :=
  ctx_chain_to_expr_ctx (len_reaches_mopsCtx xs)

/-- The verified MeTTa append/length program computes the length of an append as Peano addition. -/
theorem appendLengthMopsContext (xs ys : List Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep listAppendLengthRules)
      (lenQuery (appendQuery xs ys)) (peano (xs.length + ys.length)) := by
  have happ : Relation.ReflTransGen CtxMopsStep
      (lenQuery (appendQuery xs ys)) (lenQuery (listAtom (xs ++ ys))) :=
    reflTransGen_map_len (append_reaches_mopsCtx xs ys)
  have hlen : Relation.ReflTransGen CtxMopsStep
      (lenQuery (listAtom (xs ++ ys))) (peano (xs.length + ys.length)) := by
    simpa [List.length_append] using len_reaches_mopsCtx (xs ++ ys)
  exact ctx_chain_to_expr_ctx (Relation.ReflTransGen.trans happ hlen)

/-- KernelStep form, transported by LeaTTa's certified KernelStep/MOPS correspondence. -/
theorem appendLengthKernelContext (xs ys : List Nat) :
    Relation.ReflTransGen (ExprCtxKernelStep listAppendLengthRules stdGroundings)
      (lenQuery (appendQuery xs ys)) (peano (xs.length + ys.length)) :=
  exprCtxMopsChain_to_kernel (gt := stdGroundings) (appendLengthMopsContext xs ys)

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.ListAppendLength
