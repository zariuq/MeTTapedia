import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.ListAppendLength

/-!
# Verified MeTTa, entry 03 -- reverse involution over LeaTTa

This entry extends the verified append program with two `rev` rules and proves
that the runnable MeTTa reverse program computes Lean list reverse.  The
involution theorem follows by running the verified reverse program twice.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.ReverseInvolution

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ContextualStep

open Mettapedia.Languages.MeTTa.LeaTTa.Corpus.ListAppendLength

def reverseOnlyRules : List Metta.Atom :=
  [ .expr [mSym "=", mE "rev" [mSym "Nil"], mSym "Nil"]
  , .expr [mSym "=", mE "rev" [mE "Cons" [mVar "x", mVar "xs"]],
      mE "listAppend" [mE "rev" [mVar "xs"],
        mE "Cons" [mVar "x", mSym "Nil"]]] ]

def reverseRules : List Metta.Atom :=
  listAppendLengthRules ++ reverseOnlyRules

def revQueryAtom (xs : Metta.Atom) : Metta.Atom :=
  mE "rev" [xs]

def revQuery (xs : List Nat) : Metta.Atom :=
  revQueryAtom (listAtom xs)

/-! ## §1  Rule-set monotonicity -/

private theorem equalityReductions_append_left {rules extra : List Metta.Atom}
    {a b : Metta.Atom}
    (h : b ∈ Metta.equalityReductions ⟨rules⟩ a) :
    b ∈ Metta.equalityReductions ⟨rules ++ extra⟩ a := by
  unfold Metta.equalityReductions at h ⊢
  rw [show (⟨rules ++ extra⟩ : Metta.Space).equalityRules =
      (⟨rules⟩ : Metta.Space).equalityRules ++ (⟨extra⟩ : Metta.Space).equalityRules by
        simp [Metta.Space.equalityRules, List.filterMap_append]]
  simp [List.flatMap_append, h]

private theorem mopsStep_append_left {rules extra : List Metta.Atom}
    {a b : Metta.Atom}
    (h : Metta.MopsStep rules a b) :
    Metta.MopsStep (rules ++ extra) a b :=
  ⟨h.1, equalityReductions_append_left h.2⟩

mutual

private theorem exprCtxMopsStep_append_left {rules extra : List Metta.Atom}
    {a b : Metta.Atom}
    (h : ExprCtxMopsStep rules a b) :
    ExprCtxMopsStep (rules ++ extra) a b := by
  cases h with
  | root hroot => exact ExprCtxMopsStep.root (mopsStep_append_left (extra := extra) hroot)
  | expr hlist => exact ExprCtxMopsStep.expr (exprListMopsStep_append_left hlist)

private theorem exprListMopsStep_append_left {rules extra : List Metta.Atom}
    {xs ys : List Metta.Atom}
    (h : ExprListCtxMopsStep rules xs ys) :
    ExprListCtxMopsStep (rules ++ extra) xs ys := by
  cases h with
  | head hhead => exact ExprListCtxMopsStep.head (exprCtxMopsStep_append_left hhead)
  | tail htail => exact ExprListCtxMopsStep.tail (exprListMopsStep_append_left htail)

end

private theorem exprCtxMopsChain_append_left {rules extra : List Metta.Atom}
    {a b : Metta.Atom}
    (h : Relation.ReflTransGen (ExprCtxMopsStep rules) a b) :
    Relation.ReflTransGen (ExprCtxMopsStep (rules ++ extra)) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (exprCtxMopsStep_append_left step)

private theorem appendReachesReverseRules (xs ys : List Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep reverseRules)
      (appendQuery xs ys) (listAtom (xs ++ ys)) := by
  simpa [reverseRules] using
    (exprCtxMopsChain_append_left
      (extra := reverseOnlyRules) (appendReachesMopsContext xs ys))

/-! ## §2  Root reverse rules -/

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

private theorem match_cons_vars_raw (head tail : Metta.Atom)
    (hHead : ∀ w, head ≠ Metta.Atom.var w)
    (hTail : ∀ w, tail ≠ Metta.Atom.var w) :
    Metta.matchAtomsWith none
        (Metta.Atom.expr [Metta.Atom.sym "Cons", Metta.Atom.var "x", Metta.Atom.var "xs"])
        (Metta.Atom.expr [Metta.Atom.sym "Cons", head, tail]) =
      [[Metta.BindingRel.val "xs" tail, Metta.BindingRel.val "x" head]] := by
  simp only [Metta.matchAtomsWith]
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

private theorem rev_nil_mops_readout :
    listAtom [] ∈ Metta.equalityReductions ⟨reverseRules⟩ (revQuery []) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(mE "rev" [mSym "Nil"], mSym "Nil"), ?_, ?_⟩
  · simp [reverseRules, reverseOnlyRules, listAppendLengthRules,
      Metta.Space.equalityRules, mE, mSym, mVar]
  · refine ⟨[], ?_, ?_⟩
    · simp only [revQuery, revQueryAtom, listAtom, mE, mSym, Metta.matchAtoms,
        Metta.matchAtomsWith]
      unfold Metta.matchAll
      simp [Metta.matchAtomsWith, Metta.Bindings.merge]
      unfold Metta.matchAll
      simp [Metta.matchAtomsWith, Metta.Bindings.merge]
      unfold Metta.matchAll
      simp
    · simp [listAtom, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
        mSym]

private theorem rev_nil_mops_step :
    Metta.MopsStep reverseRules (revQuery []) (listAtom []) := by
  constructor
  · refine ⟨"rev", ?_⟩
    simp [Metta.Minimal.headKey, revQuery, revQueryAtom, listAtom, mE, mSym]
  · exact rev_nil_mops_readout

private theorem rev_cons_mops_readout (x : Nat) (xs : List Nat) :
    mE "listAppend" [revQuery xs, listAtom [x]] ∈
      Metta.equalityReductions ⟨reverseRules⟩ (revQuery (x :: xs)) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(mE "rev" [mE "Cons" [mVar "x", mVar "xs"]],
      mE "listAppend" [mE "rev" [mVar "xs"],
        mE "Cons" [mVar "x", mSym "Nil"]]), ?_, ?_⟩
  · simp [reverseRules, reverseOnlyRules, listAppendLengthRules,
      Metta.Space.equalityRules, mE, mSym, mVar]
  · refine ⟨[Metta.BindingRel.val "x" (peano x),
        Metta.BindingRel.val "xs" (listAtom xs)], ?_, ?_⟩
    · simp only [revQuery, revQueryAtom, listAtom, mE, mVar,
        Metta.matchAtoms, Metta.matchAtomsWith]
      unfold Metta.matchAll
      simp [Metta.matchAtomsWith, Metta.Bindings.merge]
      unfold Metta.matchAll
      rw [match_cons_vars_raw (peano x) (listAtom xs)
        (peano_not_var x) (listAtom_not_var xs)]
      simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
      unfold Metta.matchAll
      simp
    · simp [revQuery, revQueryAtom, listAtom, mE, mVar, mSym,
        Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply, Metta.Subst.lookup]

private theorem rev_cons_mops_step (x : Nat) (xs : List Nat) :
    Metta.MopsStep reverseRules (revQuery (x :: xs))
      (mE "listAppend" [revQuery xs, listAtom [x]]) := by
  constructor
  · refine ⟨"rev", ?_⟩
    simp [Metta.Minimal.headKey, revQuery, revQueryAtom, listAtom, mE]
  · exact rev_cons_mops_readout x xs

/-! ## §3  Reverse computes reverse, hence reverse is involutive -/

theorem reverseReachesMopsContext (xs : List Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep reverseRules)
      (revQuery xs) (listAtom xs.reverse) := by
  induction xs with
  | nil =>
      simpa [revQuery, revQueryAtom, listAtom] using
        Relation.ReflTransGen.single (ExprCtxMopsStep.root rev_nil_mops_step)
  | cons x xs ih =>
      let singleton := listAtom [x]
      have hroot : Relation.ReflTransGen (ExprCtxMopsStep reverseRules)
          (revQuery (x :: xs)) (mE "listAppend" [revQuery xs, singleton]) :=
        Relation.ReflTransGen.single (ExprCtxMopsStep.root (rev_cons_mops_step x xs))
      have hinner : Relation.ReflTransGen (ExprCtxMopsStep reverseRules)
          (mE "listAppend" [revQuery xs, singleton])
          (mE "listAppend" [listAtom xs.reverse, singleton]) := by
        simpa [singleton, appendQuery, mE] using
          (exprCtxMopsChain_at (rules := reverseRules)
            [Metta.Atom.sym "listAppend"] [singleton] ih)
      have happ : Relation.ReflTransGen (ExprCtxMopsStep reverseRules)
          (mE "listAppend" [listAtom xs.reverse, singleton])
          (listAtom (xs.reverse ++ [x])) := by
        simpa [singleton, appendQuery] using appendReachesReverseRules xs.reverse [x]
      exact Relation.ReflTransGen.trans hroot (Relation.ReflTransGen.trans hinner
        (by simpa [List.reverse_cons] using happ))

/-- Running the verified MeTTa reverse program twice returns the original list. -/
theorem reverseInvolutionMopsContext (xs : List Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep reverseRules)
      (revQueryAtom (revQuery xs)) (listAtom xs) := by
  have hinner : Relation.ReflTransGen (ExprCtxMopsStep reverseRules)
      (revQueryAtom (revQuery xs)) (revQuery xs.reverse) := by
    simpa [revQueryAtom, revQuery, mE] using
      (exprCtxMopsChain_at (rules := reverseRules)
        [Metta.Atom.sym "rev"] [] (reverseReachesMopsContext xs))
  have houter := reverseReachesMopsContext xs.reverse
  exact Relation.ReflTransGen.trans hinner (by simpa using houter)

/-- KernelStep form, transported by LeaTTa's certified KernelStep/MOPS correspondence. -/
theorem reverseInvolutionKernelContext (xs : List Nat) :
    Relation.ReflTransGen (ExprCtxKernelStep reverseRules stdGroundings)
      (revQueryAtom (revQuery xs)) (listAtom xs) :=
  exprCtxMopsChain_to_kernel (gt := stdGroundings) (reverseInvolutionMopsContext xs)

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.ReverseInvolution
