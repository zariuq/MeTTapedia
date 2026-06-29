import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ContextualStep
import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness
import MettaHyperonFull.Minimal.Stdlib
import MettaHyperonFull.Operational.Properties
import MettaHyperonFull.Proofs.Correspondence

/-!
# Verified MeTTa, entry 0 — Peano addition over LeaTTa

## What this corpus is
The first entry in the **verified-MeTTa corpus** is a small MeTTa program checked at two layers:
1. a MeTTa program as LeaTTa equation rules (`addRules`);
2. an execution demonstration over the evaluator (`mettaEval`, `#eval` below — it really runs);
3. a closed proof over LeaTTa's relation semantics (`MopsStep`, transported to contextual
   closure for constructor results).

The canonical corpus theorem is `addCommMopsContext`: Peano addition commutes over the contextual
closure of LeaTTa's MOPS relation.

## Why entry 0 is `add`, and why it sets the stage for SR-2d
This entry keeps the layers separate. The proof uses the certified relation that LeaTTa actually
publishes. The `#eval`s demonstrate the running evaluator on the same rules. Exact-fuel evaluator
equalities for the full `add` computation are intentionally not the proof object. Exact evaluator
equalities appear only at the root-rule boundary; the full outer evaluator loop must be connected
by generic interpreter-correctness lemmas, not by per-numeral fuel arithmetic.

## Discipline (same gates as SR-2d)
Properties are proven hypothesis-free; the IH is earned by induction, never assumed; and the
argument avoids `interpretFuel` trace grinding. Each entry stays small and standalone.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.PeanoAdd

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ContextualStep
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness

/-! ## §1  Atom builders -/

def mSym (s : String) : Metta.Atom := .sym s
def mVar (s : String) : Metta.Atom := .var s
def mE (head : String) (args : List Metta.Atom) : Metta.Atom := .expr (.sym head :: args)

/-! ## §2  The MeTTa program: Peano addition

    (= (add Z $n) $n)
    (= (add (S $m) $n) (S (add $m $n))) -/

def addRules : List Metta.Atom :=
  [ .expr [mSym "=", mE "add" [mSym "Z", mVar "n"], mVar "n"]
  , .expr [mSym "=", mE "add" [mE "S" [mVar "m"], mVar "n"], mE "S" [mE "add" [mVar "m", mVar "n"]]] ]

def addEnv : MinEnv := MinEnv.ofAtomsGT addRules stdGroundings

/-- Peano numerals as atoms. -/
def peano : Nat → Metta.Atom
  | 0 => mSym "Z"
  | n + 1 => mE "S" [peano n]

def addQuery (a b : Nat) : Metta.Atom := mE "add" [peano a, peano b]

private theorem peano_not_var (n : Nat) (v : String) :
    peano n ≠ Metta.Atom.var v := by
  cases n <;> simp [peano, mSym, mE]

private theorem match_var_nonvar_atom (v : String) (target : Metta.Atom)
    (h : ∀ w, target ≠ Metta.Atom.var w) :
    Metta.matchAtomsWith none (Metta.Atom.var v) target =
      [[Metta.BindingRel.val v target]] := by
  cases target with
  | var w => exact (h w rfl).elim
  | sym _ => simp [Metta.matchAtomsWith]
  | gnd _ => simp [Metta.matchAtomsWith]
  | expr _ => simp [Metta.matchAtomsWith]

private theorem match_unary_expr_var
    (head var : String) (target : Metta.Atom)
    (h : ∀ w, target ≠ Metta.Atom.var w) :
    Metta.matchAtomsWith none
      (Metta.Atom.expr [Metta.Atom.sym head, Metta.Atom.var var])
      (Metta.Atom.expr [Metta.Atom.sym head, target]) =
    [[Metta.BindingRel.val var target]] := by
  simp only [Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith, Metta.Bindings.merge]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom var target h]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  rfl

private theorem peano_symbolicClosed (n : Nat) : SymbolicClosed (peano n) := by
  induction n with
  | zero => exact SymbolicClosed.sym "Z"
  | succ n ih =>
      change SymbolicClosed (Metta.Atom.expr [Metta.Atom.sym "S", peano n])
      exact SymbolicClosed.expr (by
        intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact SymbolicClosed.sym "S"
        · rcases ha with rfl | hnil
          · exact ih
          · cases hnil)

private theorem peano_vars_nil (n : Nat) : (peano n).vars = [] :=
  SymbolicClosed.vars_nil (peano_symbolicClosed n)

private theorem addQuery_symbolicClosed (a b : Nat) : SymbolicClosed (addQuery a b) := by
  change SymbolicClosed (Metta.Atom.expr [Metta.Atom.sym "add", peano a, peano b])
  exact SymbolicClosed.expr (by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact SymbolicClosed.sym "add"
    · rcases hx with rfl | hx
      · exact peano_symbolicClosed a
      · rcases hx with rfl | hnil
        · exact peano_symbolicClosed b
        · cases hnil)

private theorem addQuery_vars_nil (a b : Nat) : (addQuery a b).vars = [] :=
  SymbolicClosed.vars_nil (addQuery_symbolicClosed a b)

private theorem addArgs_vars_nil (a b : Nat) :
    ([peano a, peano b].flatMap Metta.Atom.vars) = [] := by
  simp [peano_vars_nil a, peano_vars_nil b]

theorem restrictBnd_addArgs (a b : Nat) (bindings : Metta.Bindings) :
    restrictBnd ([peano a, peano b].flatMap Metta.Atom.vars) bindings = [] := by
  rw [addArgs_vars_nil]
  exact restrictBnd_nil_vars bindings

private theorem succAddQuery_vars_nil (a b : Nat) :
    (mE "S" [addQuery a b]).vars = [] :=
  SymbolicClosed.vars_nil
    (SymbolicClosed.expr (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact SymbolicClosed.sym "S"
      · rcases hx with rfl | hnil
        · exact addQuery_symbolicClosed a b
        · cases hnil))

private theorem peano_not_function (n : Nat) : isFunctionResult (peano n) = false := by
  cases n <;> simp [peano, mSym, mE, isFunctionResult]

private theorem peano_isError_false (n : Nat) : (peano n).isError = false := by
  induction n with
  | zero => simp [peano, mSym, Metta.Atom.isError]
  | succ n _ih => simp [peano, mE, Metta.Atom.isError]

private theorem peano_atom_beq_self_true (n : Nat) :
    Metta.Atom.beq (peano n) (peano n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold peano mE
      simp [Metta.Atom.beq, Metta.Atom.beqList, ih]

private theorem peano_beq_self_true (n : Nat) : (peano n == peano n) = true := by
  change Metta.Atom.beq (peano n) (peano n) = true
  exact peano_atom_beq_self_true n

private theorem peano_bne_self_false (n : Nat) : (peano n != peano n) = false := by
  unfold bne
  rw [peano_beq_self_true n]
  rfl

private theorem peano_beq_notReducible_false (n : Nat) :
    (peano n == notReducibleA) = false := by
  change Metta.Atom.beq (peano n) notReducibleA = false
  cases n <;> rfl

private theorem peano_beq_addZero_false (n : Nat) :
    (peano n == addQuery 0 n) = false := by
  change Metta.Atom.beq (peano n) (addQuery 0 n) = false
  cases n <;> rfl

private theorem addArgs_errorGuard_none (a b : Nat) :
    (([peano a, peano b].zip [peano a, peano b]).find?
      (fun ho => ho.1.isError && ho.1 != ho.2)) = none := by
  simp [peano_isError_false, peano_bne_self_false]

private theorem callGrounded_add_noReduce (args : List Metta.Atom) :
    callGrounded (MinEnv.ofAtomsGT addRules stdGroundings).gt "add" args =
      ReduceResult.noReduce := by
  rfl

private theorem addEnv_add_sigs : addEnv.sigs.get? "add" = none := by
  simp only [addEnv, MinEnv.ofAtomsGT, addRules, mE, mSym, mVar]
  simp

private theorem addEnv_Z_candidates : addEnv.candidates (mSym "Z") = [] := by
  simp [addEnv, addRules, mE, mSym, mVar, MinEnv.candidates, extractRules, headKey,
    ruleIndex_getD, ofAtomsGT_varRules]

private theorem argMask_add (arity : Nat) :
    argMask addEnv "add" arity = List.replicate arity true := by
  rw [argMask, addEnv_add_sigs]

private theorem typeMismatch_add (args : List Metta.Atom) :
    typeMismatch addEnv St.init.world "add" args = none := by
  rw [typeMismatch, addEnv_add_sigs]

private theorem typeMismatch_add_world (w : World) (args : List Metta.Atom) :
    typeMismatch addEnv w "add" args = none := by
  rw [typeMismatch, addEnv_add_sigs]

private theorem returnsAtom_addQuery (a b : Nat) :
    returnsAtom addEnv (addQuery a b) = false := by
  simp only [returnsAtom, addQuery, mE, headKey]
  rw [addEnv_add_sigs]
  rfl

private theorem returnsAtom_add_expr (x y : Metta.Atom) :
    returnsAtom addEnv (mE "add" [x, y]) = false := by
  simp only [returnsAtom, mE, headKey]
  rw [addEnv_add_sigs]
  rfl

private theorem addEnv_S_sigs : addEnv.sigs.get? "S" = none := by
  simp only [addEnv, MinEnv.ofAtomsGT, addRules, mE, mSym, mVar]
  simp

private theorem addEnv_S_candidates (a : Metta.Atom) :
    addEnv.candidates (mE "S" [a]) = [] := by
  simp [addEnv, addRules, mE, mSym, mVar, MinEnv.candidates, extractRules, headKey,
    ruleIndex_getD, ofAtomsGT_varRules]

private theorem addEnv_S_candidates_list (args : List Metta.Atom) :
    addEnv.candidates (Metta.Atom.expr (mSym "S" :: args)) = [] := by
  simp [addEnv, addRules, mE, mSym, mVar, MinEnv.candidates, extractRules, headKey,
    ruleIndex_getD, ofAtomsGT_varRules]

private theorem argMask_S (arity : Nat) :
    argMask addEnv "S" arity = List.replicate arity true := by
  rw [argMask, addEnv_S_sigs]

private theorem callGrounded_S_noReduce (a : Metta.Atom) :
    callGrounded addEnv.gt "S" [resolveStates St.init.world (subTokens St.init.world a)] =
      ReduceResult.noReduce := by
  rfl

private theorem callGrounded_S_noReduce_world (w : World) (a : Metta.Atom) :
    callGrounded addEnv.gt "S" [resolveStates w (subTokens w a)] = ReduceResult.noReduce := by
  rfl

private theorem callGrounded_S_noReduce_world_list (w : World) (args : List Metta.Atom) :
    callGrounded addEnv.gt "S" (args.map (fun a => resolveStates w (subTokens w a))) =
      ReduceResult.noReduce := by
  rfl

private theorem typeMismatch_S (args : List Metta.Atom) :
    typeMismatch addEnv St.init.world "S" args = none := by
  rw [typeMismatch, addEnv_S_sigs]

private theorem typeMismatch_S_world (w : World) (args : List Metta.Atom) :
    typeMismatch addEnv w "S" args = none := by
  rw [typeMismatch, addEnv_S_sigs]

private theorem returnsAtom_S (a : Metta.Atom) :
    returnsAtom addEnv (mE "S" [a]) = false := by
  simp only [returnsAtom, mE, headKey]
  rw [addEnv_S_sigs]
  rfl

private theorem atomToStack_eval (a : Metta.Atom) :
    atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", a]) [] =
      [{ atom := Metta.Atom.expr [Metta.Atom.sym "eval", a] }] := by
  rfl

private theorem addZeroCandidateSplit (n : Nat) :
    (MinEnv.ofAtomsGT addRules stdGroundings).candidates (addQuery 0 n) =
      [] ++ (mE "add" [mSym "Z", mVar "n"], mVar "n") ::
        [(mE "add" [mE "S" [mVar "m"], mVar "n"],
          mE "S" [mE "add" [mVar "m", mVar "n"]])] := by
  unfold MinEnv.candidates
  have hk : headKey (addQuery 0 n) = some "add" := by
    simp [headKey, addQuery, peano, mE, mSym]
  rw [hk]
  change (MinEnv.ofAtomsGT addRules stdGroundings).ruleIndex.getD "add" [] ++
      (MinEnv.ofAtomsGT addRules stdGroundings).varRules = _
  rw [ruleIndex_getD, ofAtomsGT_varRules]
  simp [addRules, mE, mSym, mVar, extractRules, headKey]

private theorem addSuccCandidateSplit (m n : Nat) :
    (MinEnv.ofAtomsGT addRules stdGroundings).candidates (addQuery (m + 1) n) =
      [(mE "add" [mSym "Z", mVar "n"], mVar "n")] ++
        (mE "add" [mE "S" [mVar "m"], mVar "n"],
          mE "S" [mE "add" [mVar "m", mVar "n"]]) :: [] := by
  unfold MinEnv.candidates
  have hk : headKey (addQuery (m + 1) n) = some "add" := by
    simp [headKey, addQuery, peano, mE]
  rw [hk]
  change (MinEnv.ofAtomsGT addRules stdGroundings).ruleIndex.getD "add" [] ++
      (MinEnv.ofAtomsGT addRules stdGroundings).varRules = _
  rw [ruleIndex_getD, ofAtomsGT_varRules]
  simp [addRules, mE, mSym, mVar, extractRules, headKey]

private theorem addZeroMatchCore (n : Nat) :
    [Metta.BindingRel.val "n" (peano n)] ∈
      Metta.matchAtoms (mE "add" [mSym "Z", mVar "n"]) (addQuery 0 n) := by
  simp only [addQuery, peano, mE, mSym, mVar, Metta.matchAtoms,
    Metta.matchAtomsWith]
  unfold Metta.matchAll
  change [Metta.BindingRel.val "n" (peano n)] ∈
    Metta.matchAll none [[]] [Metta.Atom.var "n"] [peano n]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom "n" (peano n) (peano_not_var n)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  simp

private theorem addZeroMatchFresh (n : Nat) :
    [Metta.BindingRel.val (counterSuffix 0 "n") (peano n)] ∈
      Metta.matchAtoms
        (freshenRule 0 (mE "add" [mSym "Z", mVar "n"]) (mVar "n")).1
        (addQuery 0 n) := by
  simp only [addQuery, peano, mE, mSym, mVar, Metta.matchAtoms]
  unfold freshenRule
  simp [Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, Metta.matchAtomsWith]
  change [Metta.BindingRel.val (counterSuffix 0 "n") (peano n)] ∈
    Metta.matchAll none [[]]
      [Metta.Atom.sym "add", Metta.Atom.sym "Z", Metta.Atom.var (counterSuffix 0 "n")]
      [Metta.Atom.sym "add", Metta.Atom.sym "Z", peano n]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom (counterSuffix 0 "n") (peano n) (peano_not_var n)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  simp

private theorem addZeroMatchFreshAt (c n : Nat) :
    [Metta.BindingRel.val (counterSuffix c "n") (peano n)] ∈
      Metta.matchAtoms
        (freshenRule c (mE "add" [mSym "Z", mVar "n"]) (mVar "n")).1
        (addQuery 0 n) := by
  simp only [addQuery, peano, mE, mSym, mVar, Metta.matchAtoms]
  unfold freshenRule
  simp [Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, Metta.matchAtomsWith]
  change [Metta.BindingRel.val (counterSuffix c "n") (peano n)] ∈
    Metta.matchAll none [[]]
      [Metta.Atom.sym "add", Metta.Atom.sym "Z", Metta.Atom.var (counterSuffix c "n")]
      [Metta.Atom.sym "add", Metta.Atom.sym "Z", peano n]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom (counterSuffix c "n") (peano n) (peano_not_var n)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  simp

private theorem addZeroMatchFreshAt_eq (c n : Nat) :
    Metta.matchAtoms
      (freshenRule c (mE "add" [mSym "Z", mVar "n"]) (mVar "n")).1
      (addQuery 0 n) =
    [[Metta.BindingRel.val (counterSuffix c "n") (peano n)]] := by
  simp only [addQuery, peano, mE, mSym, mVar, Metta.matchAtoms]
  unfold freshenRule
  simp [Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, Metta.matchAtomsWith]
  change Metta.matchAll none [[]]
      [Metta.Atom.sym "add", Metta.Atom.sym "Z", Metta.Atom.var (counterSuffix c "n")]
      [Metta.Atom.sym "add", Metta.Atom.sym "Z", peano n] = _
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  cases n <;> simp [peano, mSym, mE, Metta.matchAtomsWith, Metta.Bindings.merge,
    Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  all_goals
    unfold Metta.matchAll
    simp

private theorem addSuccMatchCore (m n : Nat) :
    [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)] ∈
      Metta.matchAtoms (mE "add" [mE "S" [mVar "m"], mVar "n"])
        (addQuery (m + 1) n) := by
  simp only [addQuery, peano, mE, mVar, Metta.matchAtoms, Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith, Metta.Bindings.merge]
  unfold Metta.matchAll
  rw [match_unary_expr_var "S" "m" (peano m) (peano_not_var m)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom "n" (peano n) (peano_not_var n)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  simp

private theorem addSuccMatchFresh (m n : Nat) :
    renameBindings (counterSuffix 1)
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)] ∈
      Metta.matchAtoms
        (freshenRule 1
          (mE "add" [mE "S" [mVar "m"], mVar "n"])
          (mE "S" [mE "add" [mVar "m", mVar "n"]])).1
        (addQuery (m + 1) n) := by
  simp only [addQuery, peano, mE, mVar, Metta.matchAtoms]
  unfold freshenRule
  simp [Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, Metta.matchAtomsWith,
    renameBindings]
  change [Metta.BindingRel.val (counterSuffix 1 "n") (peano n),
          Metta.BindingRel.val (counterSuffix 1 "m") (peano m)] ∈
    Metta.matchAll none [[]]
      [Metta.Atom.sym "add",
        Metta.Atom.expr [Metta.Atom.sym "S", Metta.Atom.var (counterSuffix 1 "m")],
        Metta.Atom.var (counterSuffix 1 "n")]
      [Metta.Atom.sym "add", Metta.Atom.expr [Metta.Atom.sym "S", peano m], peano n]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  rw [match_unary_expr_var "S" (counterSuffix 1 "m") (peano m) (peano_not_var m)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom (counterSuffix 1 "n") (peano n) (peano_not_var n)]
  have hnm : counterSuffix 1 "n" ≠ counterSuffix 1 "m" := by decide
  have hmn : counterSuffix 1 "m" ≠ counterSuffix 1 "n" := fun h => hnm h.symm
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal, hnm]
  unfold Metta.matchAll
  simp [hmn]

private theorem addSuccMatchFreshAt (c m n : Nat) :
    renameBindings (counterSuffix c)
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)] ∈
      Metta.matchAtoms
        (freshenRule c
          (mE "add" [mE "S" [mVar "m"], mVar "n"])
          (mE "S" [mE "add" [mVar "m", mVar "n"]])).1
        (addQuery (m + 1) n) := by
  simp only [addQuery, peano, mE, mVar, Metta.matchAtoms]
  unfold freshenRule
  simp [Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, Metta.matchAtomsWith,
    renameBindings]
  change [Metta.BindingRel.val (counterSuffix c "n") (peano n),
          Metta.BindingRel.val (counterSuffix c "m") (peano m)] ∈
    Metta.matchAll none [[]]
      [Metta.Atom.sym "add",
        Metta.Atom.expr [Metta.Atom.sym "S", Metta.Atom.var (counterSuffix c "m")],
        Metta.Atom.var (counterSuffix c "n")]
      [Metta.Atom.sym "add", Metta.Atom.expr [Metta.Atom.sym "S", peano m], peano n]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  rw [match_unary_expr_var "S" (counterSuffix c "m") (peano m) (peano_not_var m)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom (counterSuffix c "n") (peano n) (peano_not_var n)]
  have hnm : counterSuffix c "n" ≠ counterSuffix c "m" := by
    intro h
    have h' : "n".toList ++ ("#" ++ toString c).toList =
        "m".toList ++ ("#" ++ toString c).toList := by
      simpa [counterSuffix, String.toList_append, List.append_assoc] using congrArg String.toList h
    have hchars := (List.append_left_inj (("#" ++ toString c).toList)).mp h'
    simp at hchars
  have hmn : counterSuffix c "m" ≠ counterSuffix c "n" := fun h => hnm h.symm
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal, hnm]
  unfold Metta.matchAll
  simp [hmn]

private theorem addSuccMatchFreshAt_eq (c m n : Nat) :
    Metta.matchAtoms
        (freshenRule c
          (mE "add" [mE "S" [mVar "m"], mVar "n"])
          (mE "S" [mE "add" [mVar "m", mVar "n"]])).1
        (addQuery (m + 1) n) =
      [renameBindings (counterSuffix c)
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]] := by
  simp only [addQuery, peano, mE, mVar, Metta.matchAtoms]
  unfold freshenRule
  simp [Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, Metta.matchAtomsWith,
    renameBindings]
  change Metta.matchAll none [[]]
      [Metta.Atom.sym "add",
        Metta.Atom.expr [Metta.Atom.sym "S", Metta.Atom.var (counterSuffix c "m")],
        Metta.Atom.var (counterSuffix c "n")]
      [Metta.Atom.sym "add", Metta.Atom.expr [Metta.Atom.sym "S", peano m], peano n] =
    [[Metta.BindingRel.val (counterSuffix c "n") (peano n),
      Metta.BindingRel.val (counterSuffix c "m") (peano m)]]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  rw [match_unary_expr_var "S" (counterSuffix c "m") (peano m) (peano_not_var m)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom (counterSuffix c "n") (peano n) (peano_not_var n)]
  have hnm : counterSuffix c "n" ≠ counterSuffix c "m" := by
    intro h
    have h' : "n".toList ++ ("#" ++ toString c).toList =
        "m".toList ++ ("#" ++ toString c).toList := by
      simpa [counterSuffix, String.toList_append, List.append_assoc] using congrArg String.toList h
    have hchars := (List.append_left_inj (("#" ++ toString c).toList)).mp h'
    simp at hchars
  have hmn : counterSuffix c "m" ≠ counterSuffix c "n" := fun h => hnm h.symm
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal, hnm]
  unfold Metta.matchAll
  simp [hmn]

private theorem addZeroMatchFreshAt_addSucc_eq (c m n : Nat) :
    Metta.matchAtoms
      (freshenRule c (mE "add" [mSym "Z", mVar "n"]) (mVar "n")).1
      (addQuery (m + 1) n) = [] := by
  simp only [addQuery, peano, mE, mSym, mVar, Metta.matchAtoms]
  unfold freshenRule
  simp [Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  have h :
      (Metta.Atom.sym "Z" ==
        Metta.Atom.expr [Metta.Atom.sym "S", peano m]) = false := rfl
  simp [Metta.matchAtomsWith, h, Metta.Bindings.merge]
  unfold Metta.matchAll
  simp
  unfold Metta.matchAll
  simp

private theorem addSuccMatchFreshAt_addZero_eq (c n : Nat) :
    Metta.matchAtoms
      (freshenRule c
        (mE "add" [mE "S" [mVar "m"], mVar "n"])
        (mE "S" [mE "add" [mVar "m", mVar "n"]])).1
      (addQuery 0 n) = [] := by
  simp only [addQuery, peano, mE, mSym, mVar, Metta.matchAtoms]
  unfold freshenRule
  simp [Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup, Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith]
  unfold Metta.matchAll
  have h :
      (Metta.Atom.expr [Metta.Atom.sym "S", Metta.Atom.var ("m#" ++ c.repr)] ==
        Metta.Atom.sym "Z") = false := rfl
  simp [Metta.matchAtomsWith, h, Metta.Bindings.merge]
  unfold Metta.matchAll
  simp
  unfold Metta.matchAll
  simp

/-! ## §3  Declarative execution relation

`MopsStep addRules` is the top-level equation-rule step exported by LeaTTa.  Full `mettaEval`
also recursively evaluates expression children after a top-level rule produces a constructor such
as `(S (add m n))`, so the reusable bridge cannot target bare top-level `MopsStep` alone.  The
small contextual closure below records exactly the extra context that Peano addition needs.
-/

inductive CtxMopsStep : Metta.Atom → Metta.Atom → Prop
  | root {a b : Metta.Atom} :
      Metta.MopsStep addRules a b → CtxMopsStep a b
  | succ {a b : Metta.Atom} :
      CtxMopsStep a b → CtxMopsStep (mE "S" [a]) (mE "S" [b])

private theorem ctx_step_to_expr_ctx {a b : Metta.Atom} (h : CtxMopsStep a b) :
    ExprCtxMopsStep addRules a b := by
  induction h with
  | root h => exact ExprCtxMopsStep.root h
  | succ _ ih =>
      exact ExprCtxMopsStep.expr (ExprListCtxMopsStep.tail (ExprListCtxMopsStep.head ih))

private theorem ctx_chain_to_expr_ctx {a b : Metta.Atom}
    (h : Relation.ReflTransGen CtxMopsStep a b) :
    Relation.ReflTransGen (ExprCtxMopsStep addRules) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ctx_step_to_expr_ctx step)

private theorem add_zero_mops_readout (n : Nat) :
    peano n ∈ Metta.equalityReductions ⟨addRules⟩ (addQuery 0 n) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(mE "add" [mSym "Z", mVar "n"], mVar "n"), ?_, ?_⟩
  · simp [addRules, Metta.Space.equalityRules, mE, mSym, mVar]
  · refine ⟨[Metta.BindingRel.val "n" (peano n)], ?_, ?_⟩
    · simp only [addQuery, peano, mE, mSym, mVar, Metta.matchAtoms,
        Metta.matchAtomsWith]
      unfold Metta.matchAll
      change [Metta.BindingRel.val "n" (peano n)] ∈
        Metta.matchAll none [[]] [Metta.Atom.var "n"] [peano n]
      unfold Metta.matchAll
      rw [match_var_nonvar_atom "n" (peano n) (peano_not_var n)]
      simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
      unfold Metta.matchAll
      simp
    · simp [Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
        Metta.Subst.lookup, mVar]

/-- Top-level MOPS fires the base Peano addition rule. -/
private theorem add_zero_mops_step (n : Nat) :
    Metta.MopsStep addRules (addQuery 0 n) (peano n) := by
  constructor
  · refine ⟨"add", ?_⟩
    simp [Metta.Minimal.headKey, addQuery, peano, mE, mSym]
  · exact add_zero_mops_readout n

private theorem add_succ_mops_readout (m n : Nat) :
    mE "S" [addQuery m n] ∈ Metta.equalityReductions ⟨addRules⟩ (addQuery (m + 1) n) := by
  rw [Metta.mem_equalityReductions]
  refine ⟨(mE "add" [mE "S" [mVar "m"], mVar "n"],
      mE "S" [mE "add" [mVar "m", mVar "n"]]), ?_, ?_⟩
  · simp [addRules, Metta.Space.equalityRules, mE, mSym, mVar]
  · refine ⟨[Metta.BindingRel.val "n" (peano n),
        Metta.BindingRel.val "m" (peano m)], ?_, ?_⟩
    · simp only [addQuery, peano, mE, mVar, Metta.matchAtoms,
        Metta.matchAtomsWith]
      unfold Metta.matchAll
      simp [Metta.matchAtomsWith, Metta.Bindings.merge]
      unfold Metta.matchAll
      rw [match_unary_expr_var "S" "m" (peano m) (peano_not_var m)]
      simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
      unfold Metta.matchAll
      rw [match_var_nonvar_atom "n" (peano n) (peano_not_var n)]
      simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
      unfold Metta.matchAll
      simp
    · simp [addQuery, mE, mVar, Metta.instantiate, Metta.bindingsToSubst,
        Metta.Subst.apply, Metta.Subst.lookup]

/-- Top-level MOPS fires the recursive Peano addition rule once. -/
private theorem add_succ_mops_step (m n : Nat) :
    Metta.MopsStep addRules (addQuery (m + 1) n) (mE "S" [addQuery m n]) := by
  constructor
  · refine ⟨"add", ?_⟩
    simp [Metta.Minimal.headKey, addQuery, peano, mE]
  · exact add_succ_mops_readout m n

private theorem reflTransGen_map_succ {a b : Metta.Atom}
    (h : Relation.ReflTransGen CtxMopsStep a b) :
    Relation.ReflTransGen CtxMopsStep (mE "S" [a]) (mE "S" [b]) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h step ih => exact Relation.ReflTransGen.tail ih (CtxMopsStep.succ step)

/-- Internal contextual MOPS evaluation of the Peano add program computes the numeric sum. -/
private theorem add_reaches_sum_mopsCtx (a b : Nat) :
    Relation.ReflTransGen CtxMopsStep (addQuery a b) (peano (a + b)) := by
  induction a with
  | zero =>
      simpa [Nat.zero_add] using
        Relation.ReflTransGen.single (CtxMopsStep.root (add_zero_mops_step b))
  | succ a ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (CtxMopsStep.root (add_succ_mops_step a b)))
        (by
          simpa [addQuery, peano, Nat.succ_add] using reflTransGen_map_succ ih)

private theorem add_reaches_sum_exprCtx (a b : Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep addRules) (addQuery a b) (peano (a + b)) :=
  ctx_chain_to_expr_ctx (add_reaches_sum_mopsCtx a b)

/-- Peano computation over the corrected contextual MOPS relation. This is the MOPS-side theorem
the deferred evaluator-correctness bridge should target; bare top-level `MopsStep` is too weak for
recursive constructor results. -/
theorem addReachesSumMopsContext (a b : Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep addRules) (addQuery a b) (peano (a + b)) :=
  add_reaches_sum_exprCtx a b

/-- Peano computation over contextual `KernelStep`, obtained from LeaTTa's certified
`KernelStep ↔ MopsStep` correspondence. -/
theorem addReachesSumKernelContext (a b : Nat) :
    Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
      (addQuery a b) (peano (a + b)) :=
  exprCtxMopsChain_to_kernel (gt := stdGroundings) (addReachesSumMopsContext a b)

/-- The base Peano-addition rule as one contextual MOPS step. -/
theorem addZeroStepMopsContext (n : Nat) :
    ExprCtxMopsStep addRules (addQuery 0 n) (peano n) :=
  ExprCtxMopsStep.root (add_zero_mops_step n)

/-- The base Peano-addition rule as one contextual `KernelStep`. -/
theorem addZeroStepKernelContext (n : Nat) :
    ExprCtxKernelStep addRules stdGroundings (addQuery 0 n) (peano n) :=
  exprCtxMopsStep_to_kernel (gt := stdGroundings) (addZeroStepMopsContext n)

theorem interpretFuelAddZeroKernelReadout (fuel n : Nat) :
    (peano n, (renameBindings (counterSuffix 0)
        [Metta.BindingRel.val "n" (peano n)]).reverse) ∈
        (interpretFuel addEnv (fuel + 1) St.init
          [{ stack := [{ atom := Metta.Atom.expr [Metta.Atom.sym "eval", addQuery 0 n] }],
             bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep addRules stdGroundings) (addQuery 0 n) (peano n) := by
  have hclosedB :
      ClosedValueBindings [Metta.BindingRel.val "n" (peano n)] :=
    ClosedValueBindings.val (peano_vars_nil n) ClosedValueBindings.nil
  have hnodup :
      (bindingValueKeys [Metta.BindingRel.val "n" (peano n)]).Nodup := by
    simp [bindingValueKeys]
  have hinst :
      Metta.instantiate [] (addQuery 0 n) =
        Metta.Atom.expr (Metta.Atom.sym "add" :: [peano 0, peano n]) := by
    simp [addQuery, mE, Metta.instantiate_nil]
  have hbound :
      ∀ v ∈ (mVar "n").vars,
        ∃ t, Metta.Bindings.lookupVal [Metta.BindingRel.val "n" (peano n)] v = some t := by
    intro v hv
    simp [mVar, Metta.Atom.vars] at hv
    subst hv
    exact ⟨peano n, by simp [Metta.Bindings.lookupVal]⟩
  have hclosedResult :
      (Metta.instantiate [Metta.BindingRel.val "n" (peano n)] (mVar "n")).vars = [] := by
    simp [mVar, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
      Metta.Subst.lookup, peano_vars_nil n]
  have hnotFunction :
      isFunctionResult (Metta.instantiate [Metta.BindingRel.val "n" (peano n)] (mVar "n")) =
        false := by
    simpa [mVar, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
      Metta.Subst.lookup] using peano_not_function n
  have h :=
    interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed
      (atoms := addRules) (gt := stdGroundings) (st := St.init) (fuel := fuel)
      (x := addQuery 0 n) (lhs := mE "add" [mSym "Z", mVar "n"]) (rhs := mVar "n")
      (coreB := [Metta.BindingRel.val "n" (peano n)]) (op := "add")
      (args := [peano 0, peano n]) (pre := []) hclosedB hnodup rfl hinst
      (callGrounded_add_noReduce [peano 0, peano n]) rfl (addZeroCandidateSplit n)
      (addZeroMatchFresh n) (addZeroMatchCore n) hbound hclosedResult hnotFunction
  simpa [addEnv, addQuery, mE, mSym, mVar, St.init, Metta.instantiate,
    Metta.bindingsToSubst, Metta.Subst.apply, Metta.Subst.lookup] using h

theorem interpretFuelAddZeroKernelReadoutStack (fuel n : Nat) :
    (peano n, (renameBindings (counterSuffix 0)
        [Metta.BindingRel.val "n" (peano n)]).reverse) ∈
        (interpretFuel addEnv (fuel + 1) St.init
          [{ stack := atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", addQuery 0 n]) [],
             bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep addRules stdGroundings) (addQuery 0 n) (peano n) := by
  simpa [atomToStack_eval] using interpretFuelAddZeroKernelReadout fuel n

/-- Exact executable query surface for the base Peano rule over a static world. The base rule
contributes the only item; the recursive rule's LHS does not match `(add Z n)`. The query scan
still advances the fresh-name counter across both static candidates. -/
theorem queryOpAddZeroEqOfStatic (n : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    queryOp addEnv st [] (addQuery 0 n) [] =
      ([evalResult [] (peano n)
          (renameBindings (counterSuffix st.counter)
            [Metta.BindingRel.val "n" (peano n)]).reverse],
       { st with counter := st.counter + 2 }) := by
  unfold queryOp
  have hvar : isVariableHeaded (addQuery 0 n) = false := by
    simp [addQuery, peano, mE, mSym, isVariableHeaded]
  rw [hvar]
  rw [candidatesW_eq_candidates_of_no_selfExtra addEnv st.world (addQuery 0 n) hstatic]
  unfold addEnv
  rw [addZeroCandidateSplit n]
  have hloop :
      Metta.Bindings.hasLoop
        [Metta.BindingRel.val (counterSuffix st.counter "n") (peano n)] = false :=
    hasLoop_singleton_val_closed_false _ _ (peano_vars_nil n)
  have hboundRhs :
      ∀ v ∈ (mVar "n").vars,
        ∃ t, Metta.Bindings.lookupVal [Metta.BindingRel.val "n" (peano n)] v = some t := by
    intro v hv
    simp [mVar, Metta.Atom.vars] at hv
    subst hv
    exact ⟨peano n, by simp [Metta.Bindings.lookupVal]⟩
  have hinstRhs :
      Metta.instantiate [Metta.BindingRel.val (counterSuffix st.counter "n") (peano n)]
        (freshenRule st.counter (mE "add" [mSym "Z", mVar "n"]) (mVar "n")).2 =
        peano n := by
    have h := instantiate_freshenRule_rhs_of_renamed_bindings
      st.counter (mE "add" [mSym "Z", mVar "n"]) (mVar "n")
      [Metta.BindingRel.val "n" (peano n)] hboundRhs
    simpa [renameBindings, mVar, Metta.instantiate, Metta.bindingsToSubst,
      Metta.Subst.apply, Metta.Subst.lookup] using h
  have hbnd :
      List.reverse (renameBindings (counterSuffix st.counter)
          [Metta.BindingRel.val "n" (peano n)]) =
        [Metta.BindingRel.val (counterSuffix st.counter "n") (peano n)] := by
    simp [renameBindings]
  simp [addZeroMatchFreshAt_eq, addSuccMatchFreshAt_addZero_eq, Metta.Bindings.merge,
    Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal, Metta.Bindings.lookupVal, hloop, hinstRhs, hbnd,
    Nat.add_comm, Nat.add_left_comm]

/-- Exact scheduler surface for the base Peano rule. This packages the `evalOp → queryOp`
dispatch around `queryOpAddZeroEqOfStatic`; it is still a one-step symbolic rule boundary, not a
full evaluator trace. -/
theorem interpretStack1AddZeroKernelReadoutOfStaticEq (fuel n : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    interpretStack1 addEnv fuel st
        { stack := atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", addQuery 0 n]) [],
          bnd := [] } =
      ([evalResult [] (peano n)
          (renameBindings (counterSuffix st.counter)
            [Metta.BindingRel.val "n" (peano n)]).reverse],
       { st with counter := st.counter + 2 }) := by
  have hinst :
      Metta.instantiate [] (addQuery 0 n) =
        Metta.Atom.expr (Metta.Atom.sym "add" :: [peano 0, peano n]) := by
    simp [addQuery, mE, Metta.instantiate_nil]
  have hdispatch :=
    interpretStack1_eval_queryOp_of_instantiated_noReduce
      addEnv fuel st [] (addQuery 0 n) [] "add" [peano 0, peano n]
      hinst
      (callGrounded_add_noReduce
        ([peano 0, peano n].map (fun a => resolveStates st.world (subTokens st.world a))))
      rfl
  change interpretStack1 addEnv fuel st
      { stack := [{ atom := Metta.Atom.expr [Metta.Atom.sym "eval", addQuery 0 n] }],
        bnd := [] } =
    ([evalResult [] (peano n)
        (renameBindings (counterSuffix st.counter)
          [Metta.BindingRel.val "n" (peano n)]).reverse],
     { st with counter := st.counter + 2 })
  rw [hdispatch]
  exact queryOpAddZeroEqOfStatic n st hstatic

/-- Exact one-step fuel-driver harvest for the base Peano rule. The surrounding fuel driver
harvests the final `evalResult` emitted by `interpretStack1AddZeroKernelReadoutOfStaticEq`. -/
theorem interpretFuelAddZeroKernelReadoutOfStaticEq (fuel n : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    interpretFuel addEnv (fuel + 1) st
        [{ stack := atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", addQuery 0 n]) [],
           bnd := [] }] [] =
      ([(peano n, (renameBindings (counterSuffix st.counter)
          [Metta.BindingRel.val "n" (peano n)]).reverse)],
       { st with counter := st.counter + 2 }) := by
  have hstep := interpretStack1AddZeroKernelReadoutOfStaticEq fuel n st hstatic
  have heval :
      evalResult [] (peano n)
          (renameBindings (counterSuffix st.counter)
            [Metta.BindingRel.val "n" (peano n)]).reverse =
        finItem [] (peano n)
          (renameBindings (counterSuffix st.counter)
            [Metta.BindingRel.val "n" (peano n)]).reverse :=
    evalResult_nil_eq_finItem_of_not_function (peano_not_function n)
  have hclosed :
      Metta.instantiate
          (renameBindings (counterSuffix st.counter)
            [Metta.BindingRel.val "n" (peano n)]).reverse
          (peano n) =
        peano n :=
    instantiate_eq_self_of_vars_nil _ (peano_vars_nil n)
  simp [interpretFuel, hstep, heval, finItem, isFinal, finalPair, hclosed]

/-- Exact executable query surface for the recursive Peano rule over a static world. The base rule
misses `(add (S m) n)`, and the recursive rule contributes the only item. -/
theorem queryOpAddSuccEqOfStatic (m n : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    queryOp addEnv st [] (addQuery (m + 1) n) [] =
      ([evalResult [] (mE "S" [addQuery m n])
          (renameBindings (counterSuffix (st.counter + 1))
            [Metta.BindingRel.val "n" (peano n),
             Metta.BindingRel.val "m" (peano m)]).reverse],
       { st with counter := st.counter + 2 }) := by
  unfold queryOp
  have hvar : isVariableHeaded (addQuery (m + 1) n) = false := by
    simp [addQuery, peano, mE, isVariableHeaded]
  rw [hvar]
  rw [candidatesW_eq_candidates_of_no_selfExtra addEnv st.world (addQuery (m + 1) n) hstatic]
  unfold addEnv
  rw [addSuccCandidateSplit m n]
  let coreB : Metta.Bindings :=
    [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]
  let rb := (renameBindings (counterSuffix (st.counter + 1)) coreB).reverse
  have hclosedB : ClosedValueBindings coreB :=
    ClosedValueBindings.val (peano_vars_nil n)
      (ClosedValueBindings.val (peano_vars_nil m) ClosedValueBindings.nil)
  have hloop : Metta.Bindings.hasLoop rb = false := by
    exact ClosedValueBindings.hasLoop_false
      (ClosedValueBindings.reverse (ClosedValueBindings.rename hclosedB))
  have hboundRhs :
      ∀ v ∈ (mE "S" [mE "add" [mVar "m", mVar "n"]]).vars,
        ∃ t, Metta.Bindings.lookupVal coreB v = some t := by
    intro v hv
    simp [mE, mVar, Metta.Atom.vars] at hv
    rcases hv with rfl | rfl
    · exact ⟨peano m, by simp [Metta.Bindings.lookupVal, coreB]⟩
    · exact ⟨peano n, by simp [Metta.Bindings.lookupVal, coreB]⟩
  have hrenInst := instantiate_freshenRule_rhs_of_renamed_bindings
    (st.counter + 1)
    (mE "add" [mE "S" [mVar "m"], mVar "n"])
    (mE "S" [mE "add" [mVar "m", mVar "n"]])
    coreB hboundRhs
  have hnm : counterSuffix (st.counter + 1) "n" ≠ counterSuffix (st.counter + 1) "m" := by
    intro h
    have h' : "n".toList ++ ("#" ++ toString (st.counter + 1)).toList =
        "m".toList ++ ("#" ++ toString (st.counter + 1)).toList := by
      simpa [counterSuffix, String.toList_append, List.append_assoc] using congrArg String.toList h
    have hchars := (List.append_left_inj (("#" ++ toString (st.counter + 1)).toList)).mp h'
    simp at hchars
  have hmn : counterSuffix (st.counter + 1) "m" ≠ counterSuffix (st.counter + 1) "n" :=
    fun h => hnm h.symm
  have hmergeEq :
      List.foldl Metta.Bindings.mergeOne [[]]
          (renameBindings (counterSuffix (st.counter + 1)) coreB) = [rb] := by
    unfold rb coreB
    simp [renameBindings, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
      Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal, hnm, hmn]
  have hnodupRen :
      (bindingValueKeys (renameBindings (counterSuffix (st.counter + 1)) coreB)).Nodup := by
    simp [bindingValueKeys, renameBindings, coreB, hnm]
  have hrevInst :
      Metta.instantiate rb
          (freshenRule (st.counter + 1)
            (mE "add" [mE "S" [mVar "m"], mVar "n"])
            (mE "S" [mE "add" [mVar "m", mVar "n"]])).2 =
        Metta.instantiate (renameBindings (counterSuffix (st.counter + 1)) coreB)
          (freshenRule (st.counter + 1)
            (mE "add" [mE "S" [mVar "m"], mVar "n"])
            (mE "S" [mE "add" [mVar "m", mVar "n"]])).2 := by
    unfold rb
    exact instantiate_reverse_closed_nodup (ClosedValueBindings.rename hclosedB) hnodupRen _
  have hinstRhs :
      Metta.instantiate rb
          (freshenRule (st.counter + 1)
            (mE "add" [mE "S" [mVar "m"], mVar "n"])
            (mE "S" [mE "add" [mVar "m", mVar "n"]])).2 =
        mE "S" [addQuery m n] := by
    rw [hrevInst, hrenInst]
    simp [coreB, mE, mVar, addQuery, Metta.instantiate, Metta.bindingsToSubst,
      Metta.Subst.apply, Metta.Subst.lookup]
  simp [addZeroMatchFreshAt_addSucc_eq, addSuccMatchFreshAt_eq, Metta.Bindings.merge,
    hmergeEq, hloop, hinstRhs, rb, coreB, Nat.add_comm, Nat.add_left_comm]

/-- Static-world version of `interpretFuelAddZeroKernelReadout`. The executable root readout for
the base Peano rule composes with the same certified `KernelStep` at any state whose `&self`
extension is empty. -/
theorem interpretFuelAddZeroKernelReadoutOfStatic (fuel n : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    (peano n, (renameBindings (counterSuffix st.counter)
        [Metta.BindingRel.val "n" (peano n)]).reverse) ∈
        (interpretFuel addEnv (fuel + 1) st
          [{ stack := atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", addQuery 0 n]) [],
             bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep addRules stdGroundings) (addQuery 0 n) (peano n) := by
  have hclosedB :
      ClosedValueBindings [Metta.BindingRel.val "n" (peano n)] :=
    ClosedValueBindings.val (peano_vars_nil n) ClosedValueBindings.nil
  have hnodup :
      (bindingValueKeys [Metta.BindingRel.val "n" (peano n)]).Nodup := by
    simp [bindingValueKeys]
  have hinst :
      Metta.instantiate [] (addQuery 0 n) =
        Metta.Atom.expr (Metta.Atom.sym "add" :: [peano 0, peano n]) := by
    simp [addQuery, mE, Metta.instantiate_nil]
  have hbound :
      ∀ v ∈ (mVar "n").vars,
        ∃ t, Metta.Bindings.lookupVal [Metta.BindingRel.val "n" (peano n)] v = some t := by
    intro v hv
    simp [mVar, Metta.Atom.vars] at hv
    subst hv
    exact ⟨peano n, by simp [Metta.Bindings.lookupVal]⟩
  have hclosedResult :
      (Metta.instantiate [Metta.BindingRel.val "n" (peano n)] (mVar "n")).vars = [] := by
    simp [mVar, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
      Metta.Subst.lookup, peano_vars_nil n]
  have hnotFunction :
      isFunctionResult (Metta.instantiate [Metta.BindingRel.val "n" (peano n)] (mVar "n")) =
        false := by
    simpa [mVar, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
      Metta.Subst.lookup] using peano_not_function n
  have hfresh :
      renameBindings (counterSuffix (st.counter + ([] : List (Metta.Atom × Metta.Atom)).length))
          [Metta.BindingRel.val "n" (peano n)] ∈
        Metta.matchAtoms
          (freshenRule (st.counter + ([] : List (Metta.Atom × Metta.Atom)).length)
            (mE "add" [mSym "Z", mVar "n"]) (mVar "n")).1
          (Metta.Atom.expr (Metta.Atom.sym "add" :: [peano 0, peano n])) := by
    simpa [renameBindings, addQuery, peano, mE, mSym] using addZeroMatchFreshAt st.counter n
  have h :=
    interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed
      (atoms := addRules) (gt := stdGroundings) (st := st) (fuel := fuel)
      (x := addQuery 0 n) (lhs := mE "add" [mSym "Z", mVar "n"]) (rhs := mVar "n")
      (coreB := [Metta.BindingRel.val "n" (peano n)]) (op := "add")
      (args := [peano 0, peano n]) (pre := []) hclosedB hnodup hstatic hinst
      (callGrounded_add_noReduce
        ([peano 0, peano n].map (fun a => resolveStates st.world (subTokens st.world a))))
      rfl (addZeroCandidateSplit n) hfresh (addZeroMatchCore n) hbound hclosedResult
      hnotFunction
  simpa [addEnv, addQuery, peano, mE, mSym, mVar, atomToStack_eval, Metta.instantiate,
    Metta.bindingsToSubst, Metta.Subst.apply, Metta.Subst.lookup] using h

/-- The recursive Peano-addition rule as one contextual MOPS step. -/
theorem addSuccStepMopsContext (m n : Nat) :
    ExprCtxMopsStep addRules (addQuery (m + 1) n) (mE "S" [addQuery m n]) :=
  ExprCtxMopsStep.root (add_succ_mops_step m n)

/-- The recursive Peano-addition rule as one contextual `KernelStep`. -/
theorem addSuccStepKernelContext (m n : Nat) :
    ExprCtxKernelStep addRules stdGroundings (addQuery (m + 1) n) (mE "S" [addQuery m n]) :=
  exprCtxMopsStep_to_kernel (gt := stdGroundings) (addSuccStepMopsContext m n)

theorem interpretFuelAddSuccKernelReadout (fuel m n : Nat) :
    (mE "S" [addQuery m n], (renameBindings (counterSuffix 1)
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]).reverse) ∈
        (interpretFuel addEnv (fuel + 1) St.init
          [{ stack := [{ atom := Metta.Atom.expr [Metta.Atom.sym "eval", addQuery (m + 1) n] }],
             bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep addRules stdGroundings)
        (addQuery (m + 1) n) (mE "S" [addQuery m n]) := by
  have hclosedB :
      ClosedValueBindings
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)] :=
    ClosedValueBindings.val (peano_vars_nil n)
      (ClosedValueBindings.val (peano_vars_nil m) ClosedValueBindings.nil)
  have hnodup :
      (bindingValueKeys
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]).Nodup := by
    simp [bindingValueKeys]
  have hinst :
      Metta.instantiate [] (addQuery (m + 1) n) =
        Metta.Atom.expr (Metta.Atom.sym "add" :: [peano (m + 1), peano n]) := by
    simp [addQuery, mE, Metta.instantiate_nil]
  have hbound :
      ∀ v ∈ (mE "S" [mE "add" [mVar "m", mVar "n"]]).vars,
        ∃ t, Metta.Bindings.lookupVal
          [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)] v =
            some t := by
    intro v hv
    simp [mE, mVar, Metta.Atom.vars] at hv
    rcases hv with rfl | rfl
    · exact ⟨peano m, by simp [Metta.Bindings.lookupVal]⟩
    · exact ⟨peano n, by simp [Metta.Bindings.lookupVal]⟩
  have hclosedResult :
      (Metta.instantiate
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]
        (mE "S" [mE "add" [mVar "m", mVar "n"]])).vars = [] := by
    simp [mE, mVar, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
      Metta.Subst.lookup]
    change (mE "S" [addQuery m n]).vars = []
    exact succAddQuery_vars_nil m n
  have hnotFunction :
      isFunctionResult (Metta.instantiate
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]
        (mE "S" [mE "add" [mVar "m", mVar "n"]])) = false := by
    simp [mE, mVar, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
      Metta.Subst.lookup, isFunctionResult]
  have h :=
    interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed
      (atoms := addRules) (gt := stdGroundings) (st := St.init) (fuel := fuel)
      (x := addQuery (m + 1) n)
      (lhs := mE "add" [mE "S" [mVar "m"], mVar "n"])
      (rhs := mE "S" [mE "add" [mVar "m", mVar "n"]])
      (coreB := [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)])
      (op := "add") (args := [peano (m + 1), peano n])
      (pre := [(mE "add" [mSym "Z", mVar "n"], mVar "n")])
      hclosedB hnodup rfl hinst (callGrounded_add_noReduce [peano (m + 1), peano n])
      rfl (addSuccCandidateSplit m n) (addSuccMatchFresh m n) (addSuccMatchCore m n)
      hbound hclosedResult hnotFunction
  simpa [addEnv, addQuery, peano, mE, mSym, mVar, St.init, Metta.instantiate,
    Metta.bindingsToSubst, Metta.Subst.apply, Metta.Subst.lookup] using h

theorem interpretFuelAddSuccKernelReadoutStack (fuel m n : Nat) :
    (mE "S" [addQuery m n], (renameBindings (counterSuffix 1)
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]).reverse) ∈
        (interpretFuel addEnv (fuel + 1) St.init
          [{ stack := atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", addQuery (m + 1) n]) [],
             bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep addRules stdGroundings)
        (addQuery (m + 1) n) (mE "S" [addQuery m n]) := by
  simpa [atomToStack_eval] using interpretFuelAddSuccKernelReadout fuel m n

/-- Static-world version of `interpretFuelAddSuccKernelReadout`. The executable root readout for
the recursive Peano rule composes with the same certified `KernelStep` after previous pure
argument evaluation has threaded the state. -/
theorem interpretFuelAddSuccKernelReadoutOfStatic (fuel m n : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    (mE "S" [addQuery m n], (renameBindings (counterSuffix (st.counter + 1))
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]).reverse) ∈
        (interpretFuel addEnv (fuel + 1) st
          [{ stack := atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", addQuery (m + 1) n]) [],
             bnd := [] }] []).1 ∧
      Relation.ReflTransGen (KernelStep addRules stdGroundings)
        (addQuery (m + 1) n) (mE "S" [addQuery m n]) := by
  have hclosedB :
      ClosedValueBindings
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)] :=
    ClosedValueBindings.val (peano_vars_nil n)
      (ClosedValueBindings.val (peano_vars_nil m) ClosedValueBindings.nil)
  have hnodup :
      (bindingValueKeys
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]).Nodup := by
    simp [bindingValueKeys]
  have hinst :
      Metta.instantiate [] (addQuery (m + 1) n) =
        Metta.Atom.expr (Metta.Atom.sym "add" :: [peano (m + 1), peano n]) := by
    simp [addQuery, mE, Metta.instantiate_nil]
  have hbound :
      ∀ v ∈ (mE "S" [mE "add" [mVar "m", mVar "n"]]).vars,
        ∃ t, Metta.Bindings.lookupVal
          [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)] v =
            some t := by
    intro v hv
    simp [mE, mVar, Metta.Atom.vars] at hv
    rcases hv with rfl | rfl
    · exact ⟨peano m, by simp [Metta.Bindings.lookupVal]⟩
    · exact ⟨peano n, by simp [Metta.Bindings.lookupVal]⟩
  have hclosedResult :
      (Metta.instantiate
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]
        (mE "S" [mE "add" [mVar "m", mVar "n"]])).vars = [] := by
    simp [mE, mVar, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
      Metta.Subst.lookup]
    change (mE "S" [addQuery m n]).vars = []
    exact succAddQuery_vars_nil m n
  have hnotFunction :
      isFunctionResult (Metta.instantiate
        [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)]
        (mE "S" [mE "add" [mVar "m", mVar "n"]])) = false := by
    simp [mE, mVar, Metta.instantiate, Metta.bindingsToSubst, Metta.Subst.apply,
      Metta.Subst.lookup, isFunctionResult]
  have hfresh :
      renameBindings (counterSuffix (st.counter +
          [(mE "add" [mSym "Z", mVar "n"], mVar "n")].length))
          [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)] ∈
        Metta.matchAtoms
          (freshenRule (st.counter +
              [(mE "add" [mSym "Z", mVar "n"], mVar "n")].length)
            (mE "add" [mE "S" [mVar "m"], mVar "n"])
            (mE "S" [mE "add" [mVar "m", mVar "n"]])).1
          (Metta.Atom.expr (Metta.Atom.sym "add" :: [peano (m + 1), peano n])) := by
    simpa [renameBindings, addQuery, peano, mE, mSym, mVar] using
      addSuccMatchFreshAt (st.counter + 1) m n
  have h :=
    interpretFuel_eval_renamed_closed_coreBinding_reverse_contains_closed
      (atoms := addRules) (gt := stdGroundings) (st := st) (fuel := fuel)
      (x := addQuery (m + 1) n)
      (lhs := mE "add" [mE "S" [mVar "m"], mVar "n"])
      (rhs := mE "S" [mE "add" [mVar "m", mVar "n"]])
      (coreB := [Metta.BindingRel.val "n" (peano n), Metta.BindingRel.val "m" (peano m)])
      (op := "add") (args := [peano (m + 1), peano n])
      (pre := [(mE "add" [mSym "Z", mVar "n"], mVar "n")])
      hclosedB hnodup hstatic hinst
      (callGrounded_add_noReduce
        ([peano (m + 1), peano n].map (fun a => resolveStates st.world (subTokens st.world a))))
      rfl (addSuccCandidateSplit m n) hfresh (addSuccMatchCore m n) hbound hclosedResult
      hnotFunction
  simpa [addEnv, addQuery, peano, mE, mSym, mVar, atomToStack_eval, Metta.instantiate,
    Metta.bindingsToSubst, Metta.Subst.apply, Metta.Subst.lookup,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Exact scheduler surface for the recursive Peano rule, using
`queryOpAddSuccEqOfStatic` after the `evalOp → queryOp` dispatch. -/
theorem interpretStack1AddSuccKernelReadoutOfStaticEq (fuel m n : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    interpretStack1 addEnv fuel st
        { stack := atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", addQuery (m + 1) n]) [],
          bnd := [] } =
      ([evalResult [] (mE "S" [addQuery m n])
          (renameBindings (counterSuffix (st.counter + 1))
            [Metta.BindingRel.val "n" (peano n),
             Metta.BindingRel.val "m" (peano m)]).reverse],
       { st with counter := st.counter + 2 }) := by
  have hinst :
      Metta.instantiate [] (addQuery (m + 1) n) =
        Metta.Atom.expr (Metta.Atom.sym "add" :: [peano (m + 1), peano n]) := by
    simp [addQuery, mE, Metta.instantiate_nil]
  have hdispatch :=
    interpretStack1_eval_queryOp_of_instantiated_noReduce
      addEnv fuel st [] (addQuery (m + 1) n) [] "add" [peano (m + 1), peano n]
      hinst
      (callGrounded_add_noReduce
        ([peano (m + 1), peano n].map
          (fun a => resolveStates st.world (subTokens st.world a))))
      rfl
  change interpretStack1 addEnv fuel st
      { stack := [{ atom := Metta.Atom.expr [Metta.Atom.sym "eval", addQuery (m + 1) n] }],
        bnd := [] } =
    ([evalResult [] (mE "S" [addQuery m n])
        (renameBindings (counterSuffix (st.counter + 1))
          [Metta.BindingRel.val "n" (peano n),
           Metta.BindingRel.val "m" (peano m)]).reverse],
     { st with counter := st.counter + 2 })
  rw [hdispatch]
  exact queryOpAddSuccEqOfStatic m n st hstatic

/-- Exact one-step fuel-driver harvest for the recursive Peano rule. -/
theorem interpretFuelAddSuccKernelReadoutOfStaticEq (fuel m n : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    interpretFuel addEnv (fuel + 1) st
        [{ stack := atomToStack (Metta.Atom.expr [Metta.Atom.sym "eval", addQuery (m + 1) n]) [],
           bnd := [] }] [] =
      ([(mE "S" [addQuery m n], (renameBindings (counterSuffix (st.counter + 1))
          [Metta.BindingRel.val "n" (peano n),
           Metta.BindingRel.val "m" (peano m)]).reverse)],
       { st with counter := st.counter + 2 }) := by
  have hstep := interpretStack1AddSuccKernelReadoutOfStaticEq fuel m n st hstatic
  have hnotFunction : isFunctionResult (mE "S" [addQuery m n]) = false := by
    simp [mE, isFunctionResult]
  have heval :
      evalResult [] (mE "S" [addQuery m n])
          (renameBindings (counterSuffix (st.counter + 1))
            [Metta.BindingRel.val "n" (peano n),
             Metta.BindingRel.val "m" (peano m)]).reverse =
        finItem [] (mE "S" [addQuery m n])
          (renameBindings (counterSuffix (st.counter + 1))
            [Metta.BindingRel.val "n" (peano n),
             Metta.BindingRel.val "m" (peano m)]).reverse :=
    evalResult_nil_eq_finItem_of_not_function hnotFunction
  have hclosed :
      Metta.instantiate
          (renameBindings (counterSuffix (st.counter + 1))
            [Metta.BindingRel.val "n" (peano n),
             Metta.BindingRel.val "m" (peano m)]).reverse
          (mE "S" [addQuery m n]) =
        mE "S" [addQuery m n] :=
    instantiate_eq_self_of_vars_nil _ (succAddQuery_vars_nil m n)
  simp [interpretFuel, hstep, heval, finItem, isFinal, finalPair, hclosed]

/-- After the recursive Peano rule fires, the already-proven sub-computation lifts under `S`.
This is the decomposition point an evaluator bridge should hand to the induction hypothesis. -/
theorem addSuccTailMopsContext (m n : Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep addRules)
      (mE "S" [addQuery m n]) (mE "S" [peano (m + n)]) := by
  simpa [mE] using
    (exprCtxMopsChain_at (rules := addRules) [Metta.Atom.sym "S"] []
      (addReachesSumMopsContext m n))

/-- The recursive Peano-addition computation decomposes into one root rule step followed by the
sub-computation under the `S` constructor. -/
theorem addSuccDecomposeMopsContext (m n : Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep addRules)
        (addQuery (m + 1) n) (mE "S" [addQuery m n]) ∧
      Relation.ReflTransGen (ExprCtxMopsStep addRules)
        (mE "S" [addQuery m n]) (mE "S" [peano (m + n)]) :=
  ⟨Relation.ReflTransGen.single (addSuccStepMopsContext m n),
    addSuccTailMopsContext m n⟩

/-- Right-zero for Peano addition over contextual MOPS. This is the MOPS-side theorem that an
eventual evaluator bridge can compose with directly. -/
theorem addZeroRightMopsContext (n : Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep addRules) (addQuery n 0) (peano n) := by
  simpa using addReachesSumMopsContext n 0

/-- Both orders of addition reach the same numeral over contextual MOPS. -/
theorem addCommMopsContext (a b : Nat) :
    Relation.ReflTransGen (ExprCtxMopsStep addRules) (addQuery a b) (peano (a + b)) ∧
    Relation.ReflTransGen (ExprCtxMopsStep addRules) (addQuery b a) (peano (a + b)) := by
  constructor
  · exact addReachesSumMopsContext a b
  · simpa [Nat.add_comm] using addReachesSumMopsContext b a

/-- Both orders of addition reach the same numeral over contextual `KernelStep`. -/
theorem addCommKernelContext (a b : Nat) :
    Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) (addQuery a b) (peano (a + b)) ∧
    Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) (addQuery b a) (peano (a + b)) := by
  constructor
  · exact addReachesSumKernelContext a b
  · simpa [Nat.add_comm] using addReachesSumKernelContext b a

/-! ## §4  Execution over LeaTTa's verified evaluator (it really runs) -/

/-- LeaTTa's minimal evaluator wrapper exposes the base Peano-addition rule readout, and that
readout is paired with the certified `KernelStep` reduct for the same rule. -/
theorem evalAtomMinAddZeroKernelReadout (fuel n : Nat) :
    peano n ∈ evalAtomMin addEnv (fuel + 1) (addQuery 0 n) ∧
      Relation.ReflTransGen (KernelStep addRules stdGroundings) (addQuery 0 n) (peano n) := by
  have h := interpretFuelAddZeroKernelReadoutStack fuel n
  constructor
  · unfold evalAtomMin interpretAtom
    exact List.mem_map.mpr ⟨
      (peano n,
        (renameBindings (counterSuffix 0)
          [Metta.BindingRel.val "n" (peano n)]).reverse),
      h.1, rfl⟩
  · exact h.2

/-- Contextual form of `evalAtomMinAddZeroKernelReadout`, aligned with the Peano corpus theorem. -/
theorem evalAtomMinAddZeroExprKernelReadout (fuel n : Nat) :
    peano n ∈ evalAtomMin addEnv (fuel + 1) (addQuery 0 n) ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (addQuery 0 n) (peano n) := by
  have h := evalAtomMinAddZeroKernelReadout fuel n
  exact ⟨h.1, kernelChain_to_exprCtxKernelChain h.2⟩

/-- LeaTTa's minimal evaluator wrapper exposes the recursive Peano-addition rule readout, and that
readout is paired with the certified `KernelStep` reduct for the same rule. -/
theorem evalAtomMinAddSuccKernelReadout (fuel m n : Nat) :
    mE "S" [addQuery m n] ∈ evalAtomMin addEnv (fuel + 1) (addQuery (m + 1) n) ∧
      Relation.ReflTransGen (KernelStep addRules stdGroundings)
        (addQuery (m + 1) n) (mE "S" [addQuery m n]) := by
  have h := interpretFuelAddSuccKernelReadoutStack fuel m n
  constructor
  · unfold evalAtomMin interpretAtom
    exact List.mem_map.mpr ⟨
      (mE "S" [addQuery m n],
        (renameBindings (counterSuffix 1)
          [Metta.BindingRel.val "n" (peano n),
            Metta.BindingRel.val "m" (peano m)]).reverse),
      h.1, rfl⟩
  · exact h.2

/-- Contextual form of `evalAtomMinAddSuccKernelReadout`, aligned with the Peano corpus theorem. -/
theorem evalAtomMinAddSuccExprKernelReadout (fuel m n : Nat) :
    mE "S" [addQuery m n] ∈ evalAtomMin addEnv (fuel + 1) (addQuery (m + 1) n) ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (addQuery (m + 1) n) (mE "S" [addQuery m n]) := by
  have h := evalAtomMinAddSuccKernelReadout fuel m n
  exact ⟨h.1, kernelChain_to_exprCtxKernelChain h.2⟩

/-- Exact root-minimal evaluator output for the base Peano rule. This is a one-step
`evalAtomMin` boundary, not a full `mettaEval` trace theorem. -/
theorem evalAtomMinAddZeroEq (fuel n : Nat) :
    evalAtomMin addEnv (fuel + 1) (addQuery 0 n) = [peano n] := by
  unfold evalAtomMin interpretAtom
  have hroot := interpretFuelAddZeroKernelReadoutOfStaticEq fuel n St.init rfl
  simpa [atomToStack_eval] using congrArg (fun p => p.1.map (·.1)) hroot

/-- Exact root-minimal evaluator output for the recursive Peano rule. This is the runnable
counterpart of the certified one-step relation `addSuccStepKernelContext`. -/
theorem evalAtomMinAddSuccEq (fuel m n : Nat) :
    evalAtomMin addEnv (fuel + 1) (addQuery (m + 1) n) = [mE "S" [addQuery m n]] := by
  unfold evalAtomMin interpretAtom
  have hroot := interpretFuelAddSuccKernelReadoutOfStaticEq fuel m n St.init rfl
  simpa [atomToStack_eval] using congrArg (fun p => p.1.map (·.1)) hroot

/-- Soundness of the running minimal evaluator's root Peano readout: every atom returned by
`evalAtomMin` for an `add` query is reachable by the contextual `KernelStep` relation.

This is the root-rule evaluator bridge that the full `mettaEval` capstone must iterate under
constructor contexts; it deliberately stops before proving a fuel-exact full evaluator result. -/
theorem evalAtomMinAddRootSound (fuel a b : Nat) {out : Metta.Atom}
    (hout : out ∈ evalAtomMin addEnv (fuel + 1) (addQuery a b)) :
    Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) (addQuery a b) out := by
  cases a with
  | zero =>
      rw [evalAtomMinAddZeroEq fuel b] at hout
      have houtEq : out = peano b := by simpa using hout
      subst houtEq
      simpa using addReachesSumKernelContext 0 b
  | succ a =>
      rw [evalAtomMinAddSuccEq fuel a b] at hout
      have houtEq : out = mE "S" [addQuery a b] := by simpa using hout
      subst houtEq
      exact Relation.ReflTransGen.single (addSuccStepKernelContext a b)

/-- Every root-minimal evaluator output for `add a b` is a relation intermediate that continues
to the canonical Peano sum. This is the evaluator/relation handshake needed by the outer
`mettaEval` capstone: runtime root readout supplies the midpoint, contextual `KernelStep` supplies
the rest of the computation. -/
theorem evalAtomMinAddRootCompletesToSum (fuel a b : Nat) {out : Metta.Atom}
    (hout : out ∈ evalAtomMin addEnv (fuel + 1) (addQuery a b)) :
    Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) out (peano (a + b)) := by
  cases a with
  | zero =>
      rw [evalAtomMinAddZeroEq fuel b] at hout
      have houtEq : out = peano b := by simpa using hout
      subst houtEq
      simpa using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) (peano b) (peano b))
  | succ a =>
      rw [evalAtomMinAddSuccEq fuel a b] at hout
      have houtEq : out = mE "S" [addQuery a b] := by simpa using hout
      subst houtEq
      have htail : Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
          (mE "S" [addQuery a b]) (mE "S" [peano (a + b)]) :=
        exprCtxMopsChain_to_kernel (gt := stdGroundings) (addSuccTailMopsContext a b)
      simpa [peano, Nat.succ_add] using htail

/-- Paired root-minimal evaluator soundness/completion for Peano addition. -/
theorem evalAtomMinAddRootSoundAndCompletes (fuel a b : Nat) {out : Metta.Atom}
    (hout : out ∈ evalAtomMin addEnv (fuel + 1) (addQuery a b)) :
    Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) (addQuery a b) out ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) out (peano (a + b)) :=
  ⟨evalAtomMinAddRootSound fuel a b hout,
    evalAtomMinAddRootCompletesToSum fuel a b hout⟩

/-! ## §4.1  Peano instantiation of the generic closed-binary outer-loop fold -/

/-- Closed two-argument `add` outer-loop fold for the executable evaluator.

This is the Peano-facing wrapper around
`RuntimeCorrectness.mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval`.  It does not know
whether the root rule was the base or recursive rule: callers provide the two actual argument
evaluations, the root minimal-interpreter readout, and the recursive evaluation of that root readout.
The closed-argument hypotheses keep query-variable binding retention out of this first corpus entry. -/
private theorem mettaEvalAddClosed_eq_of_arg_singletons_and_root_eval
    (fuel : Nat) (st st₁ st₂ stRoot stOut : St)
    (x y x' y' root final : Metta.Atom) (rootBnd : Bindings)
    (hxClosed : x.vars = []) (hyClosed : y.vars = [])
    (hx : mettaEval addEnv fuel st [] x = ([(x', [])], st₁))
    (hy : mettaEval addEnv fuel st₁ [] y = ([(y', [])], st₂))
    (hNoErr : (([x', y'].zip [x, y]).find? (fun ho => ho.1.isError && ho.1 != ho.2)) = none)
    (hRoot : interpretFuel addEnv (fuel + 1) st₂ [evalItemNil (mE "add" [x', y'])] [] =
      ([(root, rootBnd)], stRoot))
    (hRootNotNotReducible : (root == notReducibleA) = false)
    (hRootNotSelf : (root == mE "add" [x', y']) = false)
    (hFinal : mettaEval addEnv fuel stRoot [] root = ([(final, [])], stOut)) :
    mettaEval addEnv (fuel + 1) st [] (mE "add" [x, y]) = ([(final, [])], stOut) := by
  exact
    mettaEval_binary_expr_eq_of_arg_singletons_and_root_eval
      (env := addEnv) (fuel := fuel) (st := st) (st₁ := st₁) (st₂ := st₂)
      (stRoot := stRoot) (stOut := stOut) (op := "add") (x := x) (y := y)
      (x' := x') (y' := y') (root := root) (final := final) (rootBnd := rootBnd)
      hxClosed hyClosed hx hy (typeMismatch_add_world st.world [x, y]) (argMask_add 2)
      hNoErr (by simpa [mE] using hRoot) hRootNotNotReducible (by simpa [mE] using hRootNotSelf)
      (by simpa [mE] using returnsAtom_add_expr x' y') hFinal

/-- Static root-normal-form readout for Peano's `S` constructor.

The minimal root evaluator reports `NotReducible` for `(S out)` in a static `addEnv` world: `S`
has no grounded implementation and no equation-rule candidates. This is the root fact consumed by
the full evaluator's constructor-congruence rung. -/
theorem mettaEvalS_root_notReducible_static
    (fuel : Nat) (out : Metta.Atom) (stArg : St)
    (hstatic : stArg.world.selfExtra = []) :
    (notReducibleA, []) ∈
      (interpretFuel addEnv (fuel + 1) stArg
        [evalItemNil (mE "S" [out])] []).1 := by
  refine interpretFuel_eval_notReducible_of_no_candidates
    addEnv stArg fuel (mE "S" [out]) [] "S" [out] ?_ ?_ ?_ ?_ ?_
  · simpa [mE] using (instantiate_nil (mE "S" [out]))
  · simpa [mE] using callGrounded_S_noReduce_world stArg.world out
  · simp [isEmbeddedOp]
  · simp [isVariableHeaded]
  · change candidatesW addEnv stArg.world (mE "S" [out]) = []
    rw [candidatesW_eq_candidates_of_no_selfExtra addEnv stArg.world (mE "S" [out]) hstatic]
    exact addEnv_S_candidates out

/-- Exact static root-normal-form readout for Peano's `S` constructor. -/
theorem mettaEvalS_root_notReducible_static_eq
    (fuel : Nat) (out : Metta.Atom) (stArg : St)
    (hstatic : stArg.world.selfExtra = []) :
    interpretFuel addEnv (fuel + 1) stArg
        [evalItemNil (mE "S" [out])] [] =
      ([(notReducibleA, [])], stArg) := by
  refine interpretFuel_eval_notReducible_of_no_candidates_eq
    addEnv stArg fuel (mE "S" [out]) [] "S" [out] ?_ ?_ ?_ ?_ ?_
  · simpa [mE] using (instantiate_nil (mE "S" [out]))
  · simpa [mE] using callGrounded_S_noReduce_world stArg.world out
  · simp [isEmbeddedOp]
  · simp [isVariableHeaded]
  · change candidatesW addEnv stArg.world (mE "S" [out]) = []
    rw [candidatesW_eq_candidates_of_no_selfExtra addEnv stArg.world (mE "S" [out]) hstatic]
    exact addEnv_S_candidates out

/-- Arity-polymorphic static root-normal-form readout for Peano's `S` constructor.

The outer evaluator fold is list-based, so its state-invariant proof needs the root fact for every
partial argument list it may thread, not only the selected unary readout. -/
theorem mettaEvalS_root_notReducible_static_eq_list
    (fuel : Nat) (args : List Metta.Atom) (stArg : St)
    (hstatic : stArg.world.selfExtra = []) :
    interpretFuel addEnv (fuel + 1) stArg
        [evalItemNil (Metta.Atom.expr (mSym "S" :: args))] [] =
      ([(notReducibleA, [])], stArg) := by
  refine interpretFuel_eval_notReducible_of_no_candidates_eq
    addEnv stArg fuel (Metta.Atom.expr (mSym "S" :: args)) [] "S" args ?_ ?_ ?_ ?_ ?_
  · simpa [mSym] using (instantiate_nil (Metta.Atom.expr (mSym "S" :: args)))
  · simpa [mSym] using callGrounded_S_noReduce_world_list stArg.world args
  · simp [isEmbeddedOp]
  · simp [isVariableHeaded]
  · change candidatesW addEnv stArg.world (Metta.Atom.expr (mSym "S" :: args)) = []
    rw [candidatesW_eq_candidates_of_no_selfExtra addEnv stArg.world
      (Metta.Atom.expr (mSym "S" :: args)) hstatic]
    exact addEnv_S_candidates_list args

/-- First clean `S`-constructor congruence rung for the full evaluator.

If the argument has already evaluated to a single non-error readout `out`, then the full evaluator
keeps `(S out)` after the generic no-candidate root check for `S`. This is the Peano-facing
instance of `RuntimeCorrectness.mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout`;
it is deliberately generic in `arg` and does not inspect one Peano layer at a time. -/
theorem mettaEvalS_keeps_of_arg_singleton_static
    (fuel : Nat) (arg out : Metta.Atom) (stArg : St)
    (hArg : mettaEval addEnv fuel St.init [] arg = ([(out, [])], stArg))
    (hNotError : out.isError = false)
    (hstatic : stArg.world.selfExtra = []) :
    (mE "S" [out], restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval addEnv (fuel + 1) St.init [] (mE "S" [arg])).1 := by
  have hroot := mettaEvalS_root_notReducible_static fuel out stArg hstatic
  simpa [mE] using
    mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout
      addEnv fuel St.init stArg "S" arg out hArg (typeMismatch_S [arg])
      (argMask_S 1) hNotError hroot

/-- State-parametric `S` constructor congruence for the full evaluator.

This is the form needed after a root equation query has advanced LeaTTa's fresh-name counter: as
long as the world remains static, the constructor proof does not depend on the concrete counter. -/
theorem mettaEvalS_keeps_of_arg_singleton_static_from
    (fuel : Nat) (st stArg : St) (arg out : Metta.Atom)
    (hArg : mettaEval addEnv fuel st [] arg = ([(out, [])], stArg))
    (hNotError : out.isError = false)
    (hstatic : stArg.world.selfExtra = []) :
    (mE "S" [out], restrictBnd arg.vars ((Bindings.merge [] []).head?.getD [])) ∈
      (mettaEval addEnv (fuel + 1) st [] (mE "S" [arg])).1 := by
  have hroot := mettaEvalS_root_notReducible_static fuel out stArg hstatic
  simpa [mE] using
    mettaEval_unary_expr_keeps_of_arg_singleton_and_notReducible_readout
      addEnv fuel st stArg "S" arg out hArg (typeMismatch_S_world st.world [arg])
      (argMask_S 1) hNotError hroot

/-- State-parametric exact `S` constructor congruence. -/
theorem mettaEvalS_eq_of_arg_singleton_static_from
    (fuel : Nat) (st stArg : St) (arg out : Metta.Atom)
    (hArg : mettaEval addEnv fuel st [] arg = ([(out, [])], stArg))
    (hNotError : out.isError = false)
    (hstatic : stArg.world.selfExtra = []) :
    mettaEval addEnv (fuel + 1) st [] (mE "S" [arg]) =
      ([(mE "S" [out], restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []))],
        stArg) := by
  have hroot := mettaEvalS_root_notReducible_static_eq fuel out stArg hstatic
  simpa [mE] using
    mettaEval_unary_expr_eq_of_arg_singleton_and_notReducible_eq
      addEnv fuel st stArg stArg "S" arg out hArg (typeMismatch_S_world st.world [arg])
      (argMask_S 1) hNotError hroot

/-- Peano zero self-evaluates from any static evaluator state and preserves that state. -/
theorem mettaEvalZ_sufficient_static (fuel : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    mettaEval addEnv (fuel + 1) st [] (mSym "Z") =
      ([(mSym "Z", [])], st) := by
  have hroot : interpretFuel addEnv (fuel + 1) st
      [evalItemNil (mSym "Z")] [] = ([(notReducibleA, [])], st) := by
    refine interpretFuel_eval_symbol_notReducible_of_no_candidates_eq
      addEnv st fuel (mSym "Z") [] "Z" ?_ ?_ ?_
    · simpa [mSym] using (instantiate_nil (mSym "Z"))
    · simp [isEmbeddedOp]
    · change candidatesW addEnv st.world (mSym "Z") = []
      rw [candidatesW_eq_candidates_of_no_selfExtra addEnv st.world (mSym "Z") hstatic]
      exact addEnv_Z_candidates
  simpa [mSym, evalItemNil] using
    mettaEval_symbol_eq_of_notReducible_eq addEnv fuel st [] "Z" hroot

/-- Peano zero self-evaluates for any positive fuel budget. -/
theorem mettaEvalZ_sufficient (fuel : Nat) :
    mettaEval addEnv (fuel + 1) St.init [] (mSym "Z") =
      ([(mSym "Z", [])], St.init) := by
  exact mettaEvalZ_sufficient_static fuel St.init rfl

/-- State-parametric sufficient-fuel self-evaluation for Peano numerals. -/
theorem mettaEvalPeanoSelf_sufficient_static (n extra : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    mettaEval addEnv (extra + n + 1) st [] (peano n) =
      ([(peano n, [])], st) := by
  induction n generalizing extra st with
  | zero =>
      simpa [peano, mSym] using mettaEvalZ_sufficient_static extra st hstatic
  | succ n ih =>
      have hArg :
          mettaEval addEnv (extra + n + 1) st [] (peano n) =
            ([(peano n, [])], st) := ih extra st hstatic
      have hS :=
        mettaEvalS_eq_of_arg_singleton_static_from (extra + n + 1) st st
          (peano n) (peano n) hArg (peano_isError_false n) hstatic
      have hrestrict :
          restrictBnd (peano n).vars ((Bindings.merge [] []).head?.getD []) = [] := by
        rw [peano_vars_nil n]
        exact restrictBnd_nil_vars ((Bindings.merge [] []).head?.getD [])
      simpa [peano, mE, hrestrict, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hS

/-- Peano numerals self-evaluate for every syntactically sufficient fuel budget. -/
theorem mettaEvalPeanoSelf_sufficient (n extra : Nat) :
    mettaEval addEnv (extra + n + 1) St.init [] (peano n) =
      ([(peano n, [])], St.init) := by
  exact mettaEvalPeanoSelf_sufficient_static n extra St.init rfl

/-- Executable/certified `S`-congruence for one already-certified subterm readout.

This is the reusable outer-loop shape needed by the Peano and SR-style recursive rules: the
subterm's actual evaluator result supplies the executable readout, while the subterm's contextual
`KernelStep` chain is lifted under the constructor. The theorem is intentionally hypothesis-driven
and generic in the subterm; it does not choose or compute a Peano-specific fuel formula. -/
theorem mettaEvalS_readout_sound_of_arg_singleton_static_from
    (fuel : Nat) (st stArg : St) (arg out : Metta.Atom)
    (hArg : mettaEval addEnv fuel st [] arg = ([(out, [])], stArg))
    (hArgSound : Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) arg out)
    (hArgClosed : arg.vars = [])
    (hNotError : out.isError = false)
    (hstatic : stArg.world.selfExtra = []) :
    (mE "S" [out], []) ∈ (mettaEval addEnv (fuel + 1) st [] (mE "S" [arg])).1 ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (mE "S" [arg]) (mE "S" [out]) := by
  have hreadout :=
    mettaEvalS_keeps_of_arg_singleton_static_from fuel st stArg arg out
      hArg hNotError hstatic
  have hrestrict :
      restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []) = [] := by
    rw [hArgClosed]
    exact restrictBnd_nil_vars ((Bindings.merge [] []).head?.getD [])
  have hReach :
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (Metta.Atom.expr [Metta.Atom.sym "S", arg])
        (Metta.Atom.expr [Metta.Atom.sym "S", out]) := by
    have hctx :=
      exprCtxKernelChain_at (rules := addRules) (gt := stdGroundings)
        [mSym "S"] [] hArgSound
    simpa [mE, mSym] using hctx
  have hsound :=
    mettaEval_unary_expr_readout_sound_of_arg_singleton_and_notReducible_readout
      addEnv fuel st stArg "S" arg out
      (ExprCtxKernelStep addRules stdGroundings)
      hArg (typeMismatch_S_world st.world [arg]) (argMask_S 1) hNotError
      (mettaEvalS_root_notReducible_static fuel out stArg hstatic) hReach
  constructor
  · simpa [mE, mSym, hrestrict] using hsound.1
  · simpa [mE, mSym] using hsound.2

/-- Recursive Peano-addition instance of the executable/certified `S`-congruence.

This is the reusable handoff for the recursive add rule: once the induction hypothesis supplies the
actual evaluator result for `(add m n)`, the evaluator readout for `(S (add m n))` and the certified
contextual `KernelStep` chain under `S` are obtained by one generic constructor-congruence step. -/
theorem mettaEvalS_readout_sound_of_addQuery_singleton_static_from
    (fuel : Nat) (st stArg : St) (m n : Nat)
    (hArg : mettaEval addEnv fuel st [] (addQuery m n) =
      ([(peano (m + n), [])], stArg))
    (hstatic : stArg.world.selfExtra = []) :
    (mE "S" [peano (m + n)], []) ∈
        (mettaEval addEnv (fuel + 1) st [] (mE "S" [addQuery m n])).1 ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (mE "S" [addQuery m n]) (mE "S" [peano (m + n)]) := by
  exact
    mettaEvalS_readout_sound_of_arg_singleton_static_from fuel st stArg
      (addQuery m n) (peano (m + n)) hArg (addReachesSumKernelContext m n)
      (addQuery_vars_nil m n) (peano_isError_false (m + n)) hstatic

/-- Selected-readout `S` constructor congruence for the full evaluator.

This is the non-singleton form needed by the runtime-correctness capstone. If the actual argument
evaluation returns a list containing `out`, then the actual evaluation of `(S arg)` contains
`(S out)`, and the certified contextual `KernelStep` chain lifts under the same constructor. The
proof uses the generic state-predicate fold lemmas plus the arity-polymorphic static `S` root
readout, not a Peano-layer exact fuel trace. -/
theorem mettaEvalS_readout_sound_of_arg_member_static_from
    (fuel : Nat) (st stArg : St) (arg out : Metta.Atom)
    (argPairs : List (Metta.Atom × Bindings))
    (hArg : mettaEval addEnv fuel st [] arg = (argPairs, stArg))
    (hmemArg : (out, []) ∈ argPairs)
    (hArgSound : Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings) arg out)
    (hArgClosed : arg.vars = [])
    (hNotError : out.isError = false)
    (hstatic : stArg.world.selfExtra = []) :
    (mE "S" [out], []) ∈ (mettaEval addEnv (fuel + 1) st [] (mE "S" [arg])).1 ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (mE "S" [arg]) (mE "S" [out]) := by
  let P : St → Prop := fun st => st.world.selfExtra = []
  have hstep :
      ∀ acc part,
        P acc.2 →
          P (mettaEvalExprPartFoldStep addEnv fuel arg.vars "S" [arg] [] acc part).2 := by
    intro acc part hacc
    unfold mettaEvalExprPartFoldStep
    split
    · exact hacc
    · let w : Metta.Atom := Metta.Atom.expr (mSym "S" :: part.1)
      have hrootEq :
          interpretFuel addEnv (fuel + 1) acc.2 [evalItemNil w] [] =
            ([(notReducibleA, [])], acc.2) := by
        simpa [w] using mettaEvalS_root_notReducible_static_eq_list fuel part.1 acc.2 hacc
      change
        P
          (match interpretFuel addEnv (fuel + 1) acc.2 [evalItemNil w] [] with
          | (pairs, st') =>
            match List.foldl (mettaEvalExprRootFoldStep addEnv fuel arg.vars w part.2)
                ([], st') pairs with
            | (out, st'') => (acc.1 ++ out, st'')).2
      rw [hrootEq]
      simp [mettaEvalExprRootFoldStep]
      exact hacc
  have hroot :
      ∀ st0 : St,
        P st0 →
          (notReducibleA, []) ∈
            (interpretFuel addEnv (fuel + 1) st0
              [evalItemNil (Metta.Atom.expr [Metta.Atom.sym "S", out])] []).1 := by
    intro st0 hst0
    simpa [mE] using mettaEvalS_root_notReducible_static fuel out st0 hst0
  have hReach :
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (Metta.Atom.expr [Metta.Atom.sym "S", arg])
        (Metta.Atom.expr [Metta.Atom.sym "S", out]) := by
    have hctx :=
      exprCtxKernelChain_at (rules := addRules) (gt := stdGroundings)
        [mSym "S"] [] hArgSound
    simpa [mE, mSym] using hctx
  have hsound :=
    mettaEval_unary_expr_readout_sound_of_arg_member_and_notReducible_state_pred
      addEnv fuel st stArg "S" arg out argPairs P
      (ExprCtxKernelStep addRules stdGroundings)
      hArg hmemArg (typeMismatch_S_world st.world [arg]) (argMask_S 1) hNotError
      hstatic hstep hroot hReach
  have hrestrict :
      restrictBnd arg.vars ((Bindings.merge [] []).head?.getD []) = [] := by
    rw [hArgClosed]
    exact restrictBnd_nil_vars ((Bindings.merge [] []).head?.getD [])
  constructor
  · simpa [mE, mSym, hrestrict] using hsound.1
  · simpa [mE, mSym] using hsound.2

theorem mettaEvalS_readout_sound_of_addQuery_member_static_from
    (fuel : Nat) (st stArg : St) (m n : Nat)
    (argPairs : List (Metta.Atom × Bindings))
    (hArg : mettaEval addEnv fuel st [] (addQuery m n) = (argPairs, stArg))
    (hmemArg : (peano (m + n), []) ∈ argPairs)
    (hstatic : stArg.world.selfExtra = []) :
    (mE "S" [peano (m + n)], []) ∈
        (mettaEval addEnv (fuel + 1) st [] (mE "S" [addQuery m n])).1 ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (mE "S" [addQuery m n]) (mE "S" [peano (m + n)]) := by
  exact
    mettaEvalS_readout_sound_of_arg_member_static_from fuel st stArg
      (addQuery m n) (peano (m + n)) argPairs hArg hmemArg
      (addReachesSumKernelContext m n) (addQuery_vars_nil m n)
      (peano_isError_false (m + n)) hstatic

/-- Recursive Peano `add` step for the full evaluator, in induction-handoff form.

The caller supplies the actual recursive readout for `(add m n)`. This theorem composes that
readout through the `S` constructor and then through the outer binary `add` evaluator fold, yielding
both a real executable readout and the matching contextual `KernelStep` chain. It is deliberately
not a closed-form fuel theorem. -/
theorem mettaEvalAddSucc_readout_sound_of_recursive_member_static_from
    (fuel : Nat) (st st₁ st₂ stRoot stArg : St) (m n : Nat)
    (rootBnd : Bindings) (argPairs : List (Metta.Atom × Bindings))
    (hLeft : mettaEval addEnv (fuel + 1) st [] (peano (m + 1)) =
      ([(peano (m + 1), [])], st₁))
    (hRight : mettaEval addEnv (fuel + 1) st₁ [] (peano n) =
      ([(peano n, [])], st₂))
    (hRoot : interpretFuel addEnv ((fuel + 1) + 1) st₂
        [evalItemNil (addQuery (m + 1) n)] [] =
      ([(mE "S" [addQuery m n], rootBnd)], stRoot))
    (hArg : mettaEval addEnv fuel stRoot [] (addQuery m n) = (argPairs, stArg))
    (hmemArg : (peano (m + n), []) ∈ argPairs)
    (hstaticArg : stArg.world.selfExtra = []) :
    (mE "S" [peano (m + n)], []) ∈
        (mettaEval addEnv ((fuel + 1) + 1) st [] (addQuery (m + 1) n)).1 ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (addQuery (m + 1) n) (mE "S" [peano (m + n)]) := by
  have hFinal :=
    mettaEvalS_readout_sound_of_addQuery_member_static_from
      fuel stRoot stArg m n argPairs hArg hmemArg hstaticArg
  have hRootReach :
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (mE "add" [peano (m + 1), peano n]) (mE "S" [addQuery m n]) :=
    Relation.ReflTransGen.single (addSuccStepKernelContext m n)
  have hBin :=
    mettaEval_binary_expr_readout_sound_of_arg_singletons_and_root_eval_member
      addEnv (fuel + 1) st st₁ st₂ stRoot "add" (peano (m + 1)) (peano n)
      (peano (m + 1)) (peano n) (mE "S" [addQuery m n]) (mE "S" [peano (m + n)])
      rootBnd (ExprCtxKernelStep addRules stdGroundings)
      (peano_vars_nil (m + 1)) (peano_vars_nil n)
      hLeft hRight (typeMismatch_add_world st.world [peano (m + 1), peano n])
      (argMask_add 2) (addArgs_errorGuard_none (m + 1) n)
      (by simpa [addQuery, mE] using hRoot)
      (by rfl) (by rfl) (by simpa [mE] using returnsAtom_add_expr (peano (m + 1)) (peano n))
      hRootReach hFinal.1 hFinal.2
  simpa [addQuery, mE] using hBin

/-- Private sufficient-fuel induction for executable Peano addition.

The public theorem below hides the budget existentially. This helper is only the induction measure
that lets the recursive rule reuse the generic closed-add fold and the `S` constructor congruence. -/
private theorem mettaEvalAdd_eq_sufficient_static (a b extra : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    ∃ stOut,
      mettaEval addEnv (extra + b + 2 * a + 3) st [] (addQuery a b) =
        ([(peano (a + b), [])], stOut) ∧
        stOut.world.selfExtra = [] := by
  induction a generalizing extra st with
  | zero =>
      let stRoot : St := { st with counter := st.counter + 2 }
      have hZ :
          mettaEval addEnv (extra + b + 2) st [] (mSym "Z") =
            ([(mSym "Z", [])], st) := by
        simpa [peano, mSym, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          mettaEvalPeanoSelf_sufficient_static 0 (extra + b + 1) st hstatic
      have hb :
          mettaEval addEnv (extra + b + 2) st [] (peano b) =
            ([(peano b, [])], st) := by
        have hb0 := mettaEvalPeanoSelf_sufficient_static b (extra + 1) st hstatic
        rw [show extra + b + 2 = (extra + 1) + b + 1 by omega]
        exact hb0
      have hRoot :
          interpretFuel addEnv (extra + b + 2 + 1) st [evalItemNil (addQuery 0 b)] [] =
          ([(peano b, (renameBindings (counterSuffix st.counter)
              [Metta.BindingRel.val "n" (peano b)]).reverse)], stRoot) := by
        simpa [stRoot, evalItemNil] using
          interpretFuelAddZeroKernelReadoutOfStaticEq (extra + b + 2) b st hstatic
      have hstaticRoot : stRoot.world.selfExtra = [] := by
        simpa [stRoot] using hstatic
      have hFinal :
          mettaEval addEnv (extra + b + 2) stRoot [] (peano b) =
            ([(peano b, [])], stRoot) := by
        have hb0 := mettaEvalPeanoSelf_sufficient_static b (extra + 1) stRoot hstaticRoot
        rw [show extra + b + 2 = (extra + 1) + b + 1 by omega]
        exact hb0
      have hNoErr :
          (([mSym "Z", peano b].zip [mSym "Z", peano b]).find?
            (fun ho => ho.1.isError && ho.1 != ho.2)) = none := by
        simpa [mSym, peano] using addArgs_errorGuard_none 0 b
      have hFold :
          mettaEval addEnv (extra + b + 2 + 1) st [] (mE "add" [mSym "Z", peano b]) =
            ([(peano b, [])], stRoot) :=
        mettaEvalAddClosed_eq_of_arg_singletons_and_root_eval
          (fuel := extra + b + 2) (st := st) (st₁ := st) (st₂ := st)
          (stRoot := stRoot) (stOut := stRoot) (x := mSym "Z") (y := peano b)
          (x' := mSym "Z") (y' := peano b) (root := peano b) (final := peano b)
          (rootBnd := (renameBindings (counterSuffix st.counter)
            [Metta.BindingRel.val "n" (peano b)]).reverse)
          (hxClosed := by simp [mSym, Metta.Atom.vars]) (hyClosed := peano_vars_nil b)
          hZ hb hNoErr (by simpa [addQuery, peano, mSym] using hRoot)
          (peano_beq_notReducible_false b)
          (by simpa [addQuery, peano, mSym] using peano_beq_addZero_false b)
          hFinal
      refine ⟨stRoot, ?_, hstaticRoot⟩
      rw [show extra + b + 2 * 0 + 3 = extra + b + 2 + 1 by omega]
      simpa [addQuery, peano, mSym, Nat.zero_add] using hFold
  | succ a ih =>
      let stRoot : St := { st with counter := st.counter + 2 }
      have hx :
          mettaEval addEnv (extra + b + 2 * a + 4) st [] (peano (a + 1)) =
            ([(peano (a + 1), [])], st) := by
        have hx0 :=
          mettaEvalPeanoSelf_sufficient_static (a + 1) (extra + b + a + 2) st hstatic
        rw [show extra + b + 2 * a + 4 = (extra + b + a + 2) + (a + 1) + 1 by omega]
        exact hx0
      have hy :
          mettaEval addEnv (extra + b + 2 * a + 4) st [] (peano b) =
            ([(peano b, [])], st) := by
        have hy0 :=
          mettaEvalPeanoSelf_sufficient_static b (extra + 2 * a + 3) st hstatic
        rw [show extra + b + 2 * a + 4 = (extra + 2 * a + 3) + b + 1 by omega]
        exact hy0
      have hRoot :
          interpretFuel addEnv (extra + b + 2 * a + 4 + 1) st
            [evalItemNil (addQuery (a + 1) b)] [] =
          ([(mE "S" [addQuery a b],
              (renameBindings (counterSuffix (st.counter + 1))
                [Metta.BindingRel.val "n" (peano b),
                  Metta.BindingRel.val "m" (peano a)]).reverse)], stRoot) := by
        simpa [stRoot, evalItemNil] using
          interpretFuelAddSuccKernelReadoutOfStaticEq (extra + b + 2 * a + 4) a b st hstatic
      have hstaticRoot : stRoot.world.selfExtra = [] := by
        simpa [stRoot] using hstatic
      rcases ih extra stRoot hstaticRoot with ⟨stIH, hIH, hstaticIH⟩
      have hFinal :
          mettaEval addEnv (extra + b + 2 * a + 4) stRoot [] (mE "S" [addQuery a b]) =
            ([(mE "S" [peano (a + b)], [])], stIH) := by
        have hS :=
          mettaEvalS_eq_of_arg_singleton_static_from (extra + b + 2 * a + 3)
            stRoot stIH (addQuery a b) (peano (a + b)) hIH
            (peano_isError_false (a + b)) hstaticIH
        have hrestrict :
            restrictBnd (addQuery a b).vars ((Bindings.merge [] []).head?.getD []) = [] := by
          rw [addQuery_vars_nil a b]
          exact restrictBnd_nil_vars ((Bindings.merge [] []).head?.getD [])
        have hS' :
            mettaEval addEnv (extra + b + 2 * a + 3 + 1) stRoot [] (mE "S" [addQuery a b]) =
              ([(mE "S" [peano (a + b)], [])], stIH) := by
          simpa [hrestrict] using hS
        rw [show extra + b + 2 * a + 4 = extra + b + 2 * a + 3 + 1 by omega]
        exact hS'
      have hNoErr :
          (([peano (a + 1), peano b].zip [peano (a + 1), peano b]).find?
            (fun ho => ho.1.isError && ho.1 != ho.2)) = none := by
        simpa using addArgs_errorGuard_none (a + 1) b
      have hRootNotSelf :
          (mE "S" [addQuery a b] == mE "add" [peano (a + 1), peano b]) = false := by
        rfl
      have hRootNotNR :
          (mE "S" [addQuery a b] == notReducibleA) = false := by
        rfl
      have hFold :
          mettaEval addEnv (extra + b + 2 * a + 4 + 1) st []
              (mE "add" [peano (a + 1), peano b]) =
            ([(mE "S" [peano (a + b)], [])], stIH) :=
        mettaEvalAddClosed_eq_of_arg_singletons_and_root_eval
          (fuel := extra + b + 2 * a + 4) (st := st) (st₁ := st) (st₂ := st)
          (stRoot := stRoot) (stOut := stIH) (x := peano (a + 1)) (y := peano b)
          (x' := peano (a + 1)) (y' := peano b) (root := mE "S" [addQuery a b])
          (final := mE "S" [peano (a + b)])
          (rootBnd := (renameBindings (counterSuffix (st.counter + 1))
            [Metta.BindingRel.val "n" (peano b), Metta.BindingRel.val "m" (peano a)]).reverse)
          (hxClosed := peano_vars_nil (a + 1)) (hyClosed := peano_vars_nil b)
          hx hy hNoErr (by simpa [addQuery, peano, mE] using hRoot)
          hRootNotNR hRootNotSelf hFinal
      refine ⟨stIH, ?_, hstaticIH⟩
      rw [show extra + b + 2 * (a + 1) + 3 = extra + b + 2 * a + 4 + 1 by omega]
      have hPeanoSucc : peano ((a + 1) + b) = mE "S" [peano (a + b)] := by
        rw [Nat.succ_add]
        rfl
      change
        mettaEval addEnv (extra + b + 2 * a + 4 + 1) st []
            (mE "add" [peano (a + 1), peano b]) =
          ([(peano ((a + 1) + b), [])], stIH)
      rw [hPeanoSucc]
      exact hFold

/-- The executable evaluator computes Peano addition with some sufficient fuel. -/
theorem mettaEvalAdd_exists_static (a b : Nat) (st : St)
    (hstatic : st.world.selfExtra = []) :
    ∃ fuel stOut,
      mettaEval addEnv fuel st [] (addQuery a b) = ([(peano (a + b), [])], stOut) ∧
        stOut.world.selfExtra = [] := by
  rcases mettaEvalAdd_eq_sufficient_static a b 0 st hstatic with ⟨stOut, hEval, hStatic⟩
  exact ⟨b + 2 * a + 3, stOut, by simpa [Nat.zero_add] using hEval, hStatic⟩

/-- Initial-state executable Peano-addition theorem. -/
theorem mettaEvalAdd_exists (a b : Nat) :
    ∃ fuel stOut,
      mettaEval addEnv fuel St.init [] (addQuery a b) =
        ([(peano (a + b), [])], stOut) ∧
        stOut.world.selfExtra = [] :=
  mettaEvalAdd_exists_static a b St.init rfl

/-- The executable evaluator computes Peano addition, and every readout from the chosen sufficient
fuel run is justified by the certified contextual `KernelStep` relation. -/
theorem mettaEvalAdd_exists_kernelSound (a b : Nat) :
    ∃ fuel stOut,
      mettaEval addEnv fuel St.init [] (addQuery a b) =
        ([(peano (a + b), [])], stOut) ∧
      (∀ out bnd,
        (out, bnd) ∈ (mettaEval addEnv fuel St.init [] (addQuery a b)).1 →
          bnd = [] ∧
            Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
              (addQuery a b) out) ∧
      stOut.world.selfExtra = [] := by
  rcases mettaEvalAdd_exists a b with ⟨fuel, stOut, hEval, hStatic⟩
  refine ⟨fuel, stOut, hEval, ?_, hStatic⟩
  exact
    mettaEval_singleton_readout_sound addEnv fuel St.init [] (addQuery a b)
      (peano (a + b)) [] stOut (ExprCtxKernelStep addRules stdGroundings)
      hEval (addReachesSumKernelContext a b)

/-- Executable Peano addition commutes: both orders have sufficient-fuel evaluator runs whose
singleton readouts are the same Peano numeral, and both are justified by the certified contextual
`KernelStep` relation. -/
theorem mettaEvalAdd_comm_exists_kernelSound (a b : Nat) :
    ∃ fuelAB stAB fuelBA stBA,
      mettaEval addEnv fuelAB St.init [] (addQuery a b) =
        ([(peano (a + b), [])], stAB) ∧
      mettaEval addEnv fuelBA St.init [] (addQuery b a) =
        ([(peano (a + b), [])], stBA) ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (addQuery a b) (peano (a + b)) ∧
      Relation.ReflTransGen (ExprCtxKernelStep addRules stdGroundings)
        (addQuery b a) (peano (a + b)) ∧
      stAB.world.selfExtra = [] ∧
      stBA.world.selfExtra = [] := by
  rcases mettaEvalAdd_exists a b with ⟨fuelAB, stAB, hAB, hStaticAB⟩
  rcases mettaEvalAdd_exists b a with ⟨fuelBA, stBA, hBA, hStaticBA⟩
  refine ⟨fuelAB, stAB, fuelBA, stBA, hAB, ?_, addReachesSumKernelContext a b, ?_,
    hStaticAB, hStaticBA⟩
  · simpa [Nat.add_comm] using hBA
  · simpa [Nat.add_comm] using addReachesSumKernelContext b a

/-- The executable evaluator computes Peano addition, and every readout from the chosen sufficient
fuel run is justified by contextual MOPS reachability. -/
theorem mettaEvalAdd_exists_mopsSound (a b : Nat) :
    ∃ fuel stOut,
      mettaEval addEnv fuel St.init [] (addQuery a b) =
        ([(peano (a + b), [])], stOut) ∧
      (∀ out bnd,
        (out, bnd) ∈ (mettaEval addEnv fuel St.init [] (addQuery a b)).1 →
          bnd = [] ∧
            Relation.ReflTransGen (ExprCtxMopsStep addRules)
              (addQuery a b) out) ∧
      stOut.world.selfExtra = [] := by
  rcases mettaEvalAdd_exists_kernelSound a b with
    ⟨fuel, stOut, hEval, hSound, hStatic⟩
  refine ⟨fuel, stOut, hEval, ?_, hStatic⟩
  intro out bnd hout
  rcases hSound out bnd hout with ⟨hbnd, hReach⟩
  exact ⟨hbnd, exprCtxKernelChain_to_mops hReach⟩

/-- Executable Peano addition commutes, and both evaluator runs are justified by contextual MOPS
reachability. -/
theorem mettaEvalAdd_comm_exists_mopsSound (a b : Nat) :
    ∃ fuelAB stAB fuelBA stBA,
      mettaEval addEnv fuelAB St.init [] (addQuery a b) =
        ([(peano (a + b), [])], stAB) ∧
      mettaEval addEnv fuelBA St.init [] (addQuery b a) =
        ([(peano (a + b), [])], stBA) ∧
      Relation.ReflTransGen (ExprCtxMopsStep addRules)
        (addQuery a b) (peano (a + b)) ∧
      Relation.ReflTransGen (ExprCtxMopsStep addRules)
        (addQuery b a) (peano (a + b)) ∧
      stAB.world.selfExtra = [] ∧
      stBA.world.selfExtra = [] := by
  rcases mettaEvalAdd_comm_exists_kernelSound a b with
    ⟨fuelAB, stAB, fuelBA, stBA, hAB, hBA, hKAB, hKBA, hStaticAB, hStaticBA⟩
  refine ⟨fuelAB, stAB, fuelBA, stBA, hAB, hBA, ?_, ?_, hStaticAB, hStaticBA⟩
  · exact exprCtxKernelChain_to_mops hKAB
  · exact exprCtxKernelChain_to_mops hKBA

/-- Executable Peano addition commutes, and every readout from both chosen evaluator runs is
justified by contextual MOPS reachability from the corresponding query. -/
theorem mettaEvalAdd_comm_exists_mopsReadoutSound (a b : Nat) :
    ∃ fuelAB stAB fuelBA stBA,
      mettaEval addEnv fuelAB St.init [] (addQuery a b) =
        ([(peano (a + b), [])], stAB) ∧
      mettaEval addEnv fuelBA St.init [] (addQuery b a) =
        ([(peano (a + b), [])], stBA) ∧
      (∀ out bnd,
        (out, bnd) ∈ (mettaEval addEnv fuelAB St.init [] (addQuery a b)).1 →
          bnd = [] ∧
            Relation.ReflTransGen (ExprCtxMopsStep addRules)
              (addQuery a b) out) ∧
      (∀ out bnd,
        (out, bnd) ∈ (mettaEval addEnv fuelBA St.init [] (addQuery b a)).1 →
          bnd = [] ∧
            Relation.ReflTransGen (ExprCtxMopsStep addRules)
              (addQuery b a) out) ∧
      stAB.world.selfExtra = [] ∧
      stBA.world.selfExtra = [] := by
  rcases mettaEvalAdd_exists_mopsSound a b with
    ⟨fuelAB, stAB, hAB, hSoundAB, hStaticAB⟩
  rcases mettaEvalAdd_exists_mopsSound b a with
    ⟨fuelBA, stBA, hBA, hSoundBA, hStaticBA⟩
  refine ⟨fuelAB, stAB, fuelBA, stBA, hAB, ?_, hSoundAB, hSoundBA,
    hStaticAB, hStaticBA⟩
  simpa [Nat.add_comm] using hBA

-- add 2 3 ⇒ S(S(S(S(S Z)))) ;  add 0 1 ⇒ S Z
#eval (mettaEval addEnv 200 St.init [] (addQuery 2 3)).1.map (·.1)
#eval (mettaEval addEnv 200 St.init [] (addQuery 0 1)).1.map (·.1)
#eval peano 5

/-! ## §5  Runtime interpreter-correctness capstone

This section records how the executable evidence is being connected to the certified relation
semantics. The root-rule boundary is closed for both Peano rules:
`interpretFuelAddZeroKernelReadout` and `interpretFuelAddSuccKernelReadout` show that one real
fuel-driver call on the corresponding `(eval (add ...))` frame harvests the rule readout and
returns the same certified `KernelStep` reduct. `evalAtomMinAddZeroKernelReadout` and
`evalAtomMinAddSuccKernelReadout` expose the same facts through LeaTTa's public minimal-evaluator
wrapper.

The implication-shaped root soundness theorem is `evalAtomMinAddRootSound`: an actual
`evalAtomMin` readout determines the contextual `KernelStep` target. The constructor side of the
outer-loop obligation is factored by `mettaEvalS_readout_sound_of_arg_member_static_from` and
`mettaEvalS_readout_sound_of_addQuery_member_static_from`: once an induction hypothesis has earned
an actual evaluator readout for a subterm, the outer evaluator readout and the contextual
`KernelStep` chain under `S` are obtained by one generic constructor step.

The remaining full-runtime obligation is not a Peano exact-fuel arithmetic trace. It is the general
static-fragment theorem:

`mettaEval_static_symbol_fragment_sound`:
for every `(out, bnd)` in `mettaEval env fuel st [] q`, with `q` in the static symbol-headed
equation-rule fragment and adequate fuel/non-overflow premises, `out` is reachable from `q` by
`ReflTransGen KernelStep` (or the corresponding contextual closure) and `bnd` is the retained
ambient binding.

That theorem should be proved by fuel/work-list induction in `RuntimeCorrectness.lean`, composing
the single-step `queryOp`/`firedReducts`/`KernelStep` bridge. The executable face here remains the
`#eval` demonstration; this file no longer claims a full Peano soundness theorem by computing a
closed-form fuel trace.

Build/run check: `lake build Mettapedia.Languages.MeTTa.LeaTTa.Corpus.PeanoAdd` (the `#eval`s print the runs).
-/

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.PeanoAdd
