import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Premises
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedCongruence
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedControls

/-!
# MeTTa-calculus premise adequacy

Bridge from the IR premise contract (`Premises.lean`) to a runtime that answers
it with the corrected COMM.

* All declared relation and builtin names are implemented by the runtime
  dispatch.
* The COMM witness `correctedCommWitness` is the corrected COMM of the two
  inputs: each is closed, the two are opened apart with names fresh for the
  four arguments, their patterns are unified by `Corrected.unify`, and the dot
  is applied once to each continuation (`comm_witness_adapter_spec`).
* At a root redex every witness is a step of the corrected relational
  semantics, on any channel (`comm_witness_sound`).
* `stepViaPremiseContract` runs the authored rules with this environment. Its
  REFL premise is the declared COMM-only lookahead. On the canaries it gives
  the corrected reducts, in both orders of the bag, and not the capturing one.
* **Soundness**: every reduct of `stepViaPremiseContract` of a calculus process
  is a step of the corrected relational semantics modulo the bag laws
  (`stepViaPremiseContract_sound`, through the engine's relational
  specification of its fuel-bounded run, `engine_sound`).
* **Completeness for COMM between two elements of one bag**, on the closing
  fragment, up to the bag laws (`stepViaPremiseContract_complete_comm`).
* Outside that fragment the step stops short: inputs in different bags and
  nested reflection have no reduct (`EngineControls.nested_bag_missed`,
  `EngineControls.nested_reflection_missed`).

A rule sees only its own bag, so the names a residual must avoid cannot come
from the rule. The runtime supplies them: `stepViaPremiseContract p` answers the
contract with the free names of `p`, the discipline of `Corrected.cstep`.
Without that supply a residual name is fresh for the redex only and can be a
free name of the surrounding bag (`EngineControls.supply_keeps_residuals_fresh`).
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Adequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Premises
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm (pvars)

private def runtimeImplementsRel (rel : String) : Bool :=
  rel == relMettaComm || rel == relMettaStepNoReflect

private def runtimeImplementsBuiltin (name : String) : Bool :=
  name == builtinMettaCommWitness || name == builtinMettaCommOnlyStep

theorem runtime_covers_declared_relations :
    (mettaCalcPremises.relations.map (·.name)).all runtimeImplementsRel = true := by
  decide +kernel

theorem runtime_covers_declared_builtins :
    (mettaCalcPremises.builtins.map (·.name)).all runtimeImplementsBuiltin = true := by
  decide +kernel

/-! ## The corrected COMM witness -/

/-- The names a witness avoids: the free names of the two inputs, on a
placeholder channel. -/
def witnessAvoid (t u p q : Pattern) : List String :=
  pvars (Corrected.close (par (pFor t pZero p) (pFor u pZero q)))

/-- A COMM reduct `P' | Q'` as the contract's witness value `MRef(P', Q')`. -/
def witnessOf : Pattern → Option Pattern
  | .collection .hashBag [pOut, qOut] none => some (.apply "MRef" [pOut, qOut])
  | _ => none

/-- **The corrected runtime adapter** for premise builtin `mettaCommWitness`:
the corrected COMM of the two inputs, opened apart with names that avoid the
`supply` and the inputs' own free names. The runtime supplies the free names
of the process being stepped, so that a residual name is fresh for the whole
process, as in `Corrected.cstep`. -/
def correctedCommWitness (supply : List String) : List Pattern → List Pattern
  | [t, u, p, q] =>
      (Corrected.commClosed (supply ++ witnessAvoid t u p q) (Corrected.close (pFor t pZero p))
        (Corrected.close (pFor u pZero q))).filterMap witnessOf
  | _ => []

private def commTuples (supply : List String) : List Pattern → List (List Pattern)
  | [t, u, p, q, _, _] =>
      (correctedCommWitness supply [t, u, p, q]).filterMap fun witness =>
        match witness with
        | .apply "MRef" [pOut, qOut] => some [t, u, p, q, pOut, qOut]
        | _ => none
  | _ => []

private def commOnlyRelEnv (supply : List String) : RelationEnv where
  tuples := fun rel args =>
    if rel == relMettaComm then commTuples supply args else []

/-- The corrected COMM-only lookahead, for premise builtin `mettaCommOnlyStep`. -/
def correctedCommOnlyStep (supply : List String) (p : Proc) : List Proc :=
  reductsUsing (commOnlyRelEnv supply) mettaCalcCommOnly executableContextFuel p

/-- The corrected builtin dispatch for the MeTTa-calculus premise builtins. -/
def correctedBuiltinMany (supply : List String) (builtin : String) (args : List Pattern) : List Pattern :=
  if builtin == builtinMettaCommWitness then
    correctedCommWitness supply args
  else if builtin == builtinMettaCommOnlyStep then
    match args with
    | [src] => correctedCommOnlyStep supply src
    | _ => []
  else
    []

private def stepNoReflectTuples (supply : List String) : List Pattern → List (List Pattern)
  | [src, _] => (correctedBuiltinMany supply builtinMettaCommOnlyStep [src]).map fun tgt => [src, tgt]
  | _ => []

/-- The corrected relation environment answering the premise contract, for a
supply of names to avoid. -/
def correctedRelEnv (supply : List String) : RelationEnv where
  tuples := fun rel args =>
    if rel == relMettaComm then
      commTuples supply args
    else if rel == relMettaStepNoReflect then
      stepNoReflectTuples supply args
    else
      []

theorem comm_witness_adapter_spec (supply : List String) (t u p q : Pattern) :
    correctedBuiltinMany supply builtinMettaCommWitness [t, u, p, q] =
      (Corrected.commClosed (supply ++ witnessAvoid t u p q) (Corrected.close (pFor t pZero p))
        (Corrected.close (pFor u pZero q))).filterMap witnessOf := by
  simp [correctedBuiltinMany, correctedCommWitness]

theorem comm_only_step_adapter_spec (supply : List String) (src : Proc) :
    correctedBuiltinMany supply builtinMettaCommOnlyStep [src] = correctedCommOnlyStep supply src := by
  have hneq : (builtinMettaCommOnlyStep == builtinMettaCommWitness) = false := by
    decide +kernel
  simp [correctedBuiltinMany, hneq]

/-- The channel does not change the corrected COMM, once both inputs are on
the same one. -/
theorem commClosed_channel (avoid : List String) (t c c' A u B : Pattern) :
    Corrected.commClosed avoid (pFor t c A) (pFor u c B) =
      Corrected.commClosed avoid (pFor t c' A) (pFor u c' B) := by
  simp [Corrected.commClosed, Corrected.asGuard_pFor]

theorem mem_witnessOf {r w : Pattern} (found : witnessOf r = some w) :
    ∃ pOut qOut, r = par pOut qOut ∧ w = .apply "MRef" [pOut, qOut] := by
  unfold witnessOf at found
  split at found
  · rename_i pOut qOut
    exact ⟨pOut, qOut, rfl, (Option.some.inj found).symm⟩
  · cases found

/-- **Root soundness of the witness.** At a root redex of calculus terms, on
any channel and for any supply of names, every witness is a step of the
corrected relational semantics. The channel is outside both scopes, so the
names a witness avoids need not contain its free names. -/
theorem comm_witness_sound (supply : List String) {t u x p q pOut qOut : Pattern}
    (calcT : Corrected.calcTerm t = true) (calcU : Corrected.calcTerm u = true)
    (calcP : Corrected.calcTerm p = true) (calcQ : Corrected.calcTerm q = true)
    (witness : .apply "MRef" [pOut, qOut] ∈ correctedCommWitness supply [t, u, p, q]) :
    Corrected.Step Corrected.conventional (par (pFor t x p) (pFor u x q)) (par pOut qOut) := by
  simp only [correctedCommWitness, List.mem_filterMap] at witness
  obtain ⟨r, member, found⟩ := witness
  obtain ⟨a, b, rfl, same⟩ := mem_witnessOf found
  simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨rfl, rfl⟩ := same
  have closeL := Corrected.closeIn_pFor [] t pZero p
  have closeR := Corrected.closeIn_pFor [] u pZero q
  have closeL' := Corrected.closeIn_pFor [] t x p
  have closeR' := Corrected.closeIn_pFor [] u x q
  unfold Corrected.close at member
  rw [closeL, closeR, commClosed_channel _ _ _ (Corrected.closeIn [] x), ← closeL', ← closeR'] at member
  have sound := Corrected.commClosed_sound_bodies (supply ++ witnessAvoid t u p q) t x p u x q
    calcT calcU calcP calcQ
    (fun z occurs => List.mem_append_right _ (by
      unfold witnessAvoid
      exact Corrected.mem_pvars_close_redex occurs)) member
  exact sound.mono Corrected.uniform_conventional

/-! ## The premise-contract step -/

/-- The authored rules run with the corrected premise environment, supplied
with the free names of the process being stepped. -/
def stepViaPremiseContract (p : Proc) : List Proc :=
  reductsUsing (correctedRelEnv (pvars (Corrected.close p))) mettaCalc executableContextFuel p

/-- The corrected reduct of the canary, in the two orders of its bag. -/
def commCanaryReducts : List Proc :=
  [pPar [nQuote pZero, .fvar "a"], pPar [.fvar "a", nQuote pZero]]

theorem premise_contract_comm_canary :
    stepViaPremiseContract demoCommSource = commCanaryReducts := by
  decide +kernel

/-- The premise-contract step does not capture: the naive reading's reduct
`@0 | @0` is not among its reducts. -/
theorem premise_contract_no_capture :
    demoCommCapture ∉ stepViaPremiseContract demoCommSource := by
  rw [premise_contract_comm_canary]; decide +kernel

/-- Each premise-contract reduct of the canary is the corrected step's reduct
up to the bag laws. -/
theorem premise_contract_comm_bagEq :
    ∀ r ∈ stepViaPremiseContract demoCommSource,
      ∃ r' ∈ Corrected.cstep demoCommSource, Corrected.BagEq r r' := by
  rw [premise_contract_comm_canary]
  unfold Corrected.BagEq
  decide +kernel

theorem premise_contract_refl_canary :
    stepViaPremiseContract demoReflectSource =
      commCanaryReducts.map fun reduct => pFor (tProc reduct) demoChan pZero := by
  decide +kernel

theorem premise_contract_blocked :
    stepViaPremiseContract demoBlocked = [] := by
  decide +kernel

/-! ## The premise-contract step is sound for the bag-law semantics

The engine fires the authored rules on the process as written: COMM on two
elements of one bag, keeping the others; PAR into one element; and REFL over
the COMM-only lookahead. Every reduct it produces is a step of the corrected
relational semantics modulo the bag laws (`stepViaPremiseContract_sound`). -/

section Engine

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- The authored REFL rule, read off `mettaCalc`. -/
def reflRuleSpec : RewriteRule := {
  name := "Refl"
  typeContext := [("x", .base "Name"), ("p", .base "Proc"), ("pNext", .base "Proc")]
  premises := [.relationQuery relMettaStepNoReflect [.fvar "p", .fvar "pNext"]]
  left := .apply "MRef" [.fvar "x", .fvar "p"]
  right := .apply "MFor" [.apply "MTermProc" [.fvar "pNext"], .fvar "x", .apply "MZero" []] }

/-- The authored parallel rule, read off `mettaCalc`. -/
def parCongRuleSpec : RewriteRule := {
  name := "ParCong"
  typeContext := [("p", .base "Proc"), ("pNext", .base "Proc")]
  premises := [.congruence (.fvar "p") (.fvar "pNext")]
  left := .collection .hashBag [.fvar "p"] (some "rest")
  right := .collection .hashBag [.fvar "pNext"] (some "rest") }

theorem mettaCalc_rewrites : mettaCalc.rewrites = [commSymRule, reflRuleSpec, parCongRuleSpec] := rfl

theorem mettaCalcCommOnly_rewrites : mettaCalcCommOnly.rewrites = [commSymRule, parCongRuleSpec] := rfl

theorem applyBindingsForRule_eq (lang : LanguageDef) (rule : RewriteRule) (bindings : Bindings)
    (aligned : ruleDepthAligned rule = true) :
    applyBindingsForRule lang rule bindings = applyBindings bindings rule.right :=
  applyBindingsForRuleUsing_empty_eq_applyBindings rule bindings aligned

/-- A guard pattern matches a guard, binding its three parts. -/
theorem matchRel_guard {a b c : String} {telem : Pattern} {hb : Bindings}
    (h : MatchRel (.apply "MFor" [.fvar a, .fvar b, .fvar c]) telem hb) :
    ∃ T X K, telem = pFor T X K ∧
      mergeBindings [(a, T)] [] = some [(a, T)] ∧
      ∃ tb, mergeBindings [(b, X)] [(c, K)] = some tb ∧ mergeBindings [(a, T)] tb = some hb := by
  cases h with
  | apply args _ =>
      cases args with
      | cons hT rest₁ merge₁ =>
          cases hT
          cases rest₁ with
          | cons hX rest₂ merge₂ =>
              cases hX
              cases rest₂ with
              | cons hK rest₃ merge₃ =>
                  cases hK
                  cases rest₃
                  simp [mergeBindings] at merge₃
                  subst merge₃
                  exact ⟨_, _, _, rfl, rfl, _, merge₂, merge₁⟩

/-- The left side of COMM matches a bag with two guards on one channel. -/
theorem matchPattern_commLeft {P : Pattern} {bs : Bindings} (h : bs ∈ matchPattern commSymRule.left P) :
    ∃ elems r i j, P = .collection .hashBag elems r ∧ ∃ (hi : i < elems.length)
      (hj : j < (elems.eraseIdx i).length), ∃ T X K U V,
        elems[i] = pFor T X K ∧ (elems.eraseIdx i)[j] = pFor U X V ∧
        bs = [("u", U), ("q", V), ("rest", .collection .hashBag ((elems.eraseIdx i).eraseIdx j) none),
          ("x", X), ("p", K), ("t", T)] := by
  have rel := matchPattern_sound h
  generalize hpat : commSymRule.left = pat at rel
  cases rel with
  | collection _ bag =>
      simp only [commSymRule, Pattern.collection.injEq] at hpat
      obtain ⟨rfl, rfl, rfl⟩ := hpat
      generalize hpats : [Pattern.apply "MFor" [.fvar "t", .fvar "x", .fvar "p"],
        Pattern.apply "MFor" [.fvar "u", .fvar "x", .fvar "q"]] = pats at bag
      cases bag with
      | nilRest => cases hpats
      | cons i hi first restBag merged =>
          simp only [List.cons.injEq] at hpats
          obtain ⟨rfl, rfl⟩ := hpats
          generalize hsecond : [Pattern.apply "MFor" [.fvar "u", .fvar "x", .fvar "q"]] = later at restBag
          cases restBag with
          | nilRest => cases hsecond
          | cons j hj second last mergedRest =>
              simp only [List.cons.injEq] at hsecond
              obtain ⟨rfl, rfl⟩ := hsecond
              generalize hnone : ([] : List Pattern) = none' at last
              cases last with
              | cons _ _ _ _ _ => cases hnone
              | nilRest =>
                  obtain ⟨T, X, K, eqT, -, tb, mergeXK, mergeT⟩ := matchRel_guard first
                  obtain ⟨U, X', V, eqU, -, tb', mergeXV, mergeU⟩ := matchRel_guard second
                  simp [mergeBindings] at mergeXK mergeXV
                  subst mergeXK mergeXV
                  simp [mergeBindings] at mergeT mergeU
                  subst mergeT mergeU
                  simp [mergeBindings] at mergedRest
                  subst mergedRest
                  simp [mergeBindings] at merged
                  by_cases sameX : X = X'
                  · subst sameX
                    simp at merged
                    subst merged
                    exact ⟨_, _, i, j, rfl, hi, hj, T, X, K, U, V, eqT, eqU, rfl⟩
                  · simp [sameX] at merged
  | _ => simp [commSymRule] at hpat

/-- The left side of the parallel rule matches a bag, singling out one element. -/
theorem matchPattern_parLeft {P : Pattern} {bs : Bindings} (h : bs ∈ matchPattern parCongRuleSpec.left P) :
    ∃ elems r i, P = .collection .hashBag elems r ∧ ∃ (hi : i < elems.length),
      bs = [("rest", .collection .hashBag (elems.eraseIdx i) none), ("p", elems[i])] := by
  have rel := matchPattern_sound h
  generalize hpat : parCongRuleSpec.left = pat at rel
  cases rel with
  | collection _ bag =>
      simp only [parCongRuleSpec, Pattern.collection.injEq] at hpat
      obtain ⟨rfl, rfl, rfl⟩ := hpat
      generalize hpats : [Pattern.fvar "p"] = pats at bag
      cases bag with
      | nilRest => cases hpats
      | cons i hi first restBag merged =>
          simp only [List.cons.injEq] at hpats
          obtain ⟨rfl, rfl⟩ := hpats
          generalize hnone : ([] : List Pattern) = none' at restBag
          cases restBag with
          | cons _ _ _ _ _ => cases hnone
          | nilRest =>
              cases first
              simp [mergeBindings] at merged
              subst merged
              exact ⟨_, _, i, rfl, hi, rfl⟩
  | _ => simp [parCongRuleSpec] at hpat

/-- The left side of REFL matches a reflection. -/
theorem matchPattern_reflLeft {P : Pattern} {bs : Bindings} (h : bs ∈ matchPattern reflRuleSpec.left P) :
    ∃ X S, P = pReflect X S ∧ bs = [("p", S), ("x", X)] := by
  have rel := matchPattern_sound h
  generalize hpat : reflRuleSpec.left = pat at rel
  cases rel with
  | apply args _ =>
      simp only [reflRuleSpec, Pattern.apply.injEq] at hpat
      obtain ⟨rfl, rfl⟩ := hpat
      cases args with
      | cons hX rest₁ merge₁ =>
          cases hX
          cases rest₁ with
          | cons hS rest₂ merge₂ =>
              cases hS
              cases rest₂
              simp [mergeBindings] at merge₂
              subst merge₂
              simp [mergeBindings] at merge₁
              subst merge₁
              exact ⟨_, _, rfl, rfl⟩
  | _ => simp [reflRuleSpec] at hpat

/-- The COMM premise reads the corrected witness, and the reduct keeps the
other elements of the bag. -/
theorem comm_premise {lang : LanguageDef} {env : RelationEnv} {supply : List String}
    (rows : ∀ args, env.tuples relMettaComm args = commTuples supply args)
    {T X K U V : Pattern} {rem : List Pattern} {final : Bindings}
    (member : final ∈ relationQueryStep env lang
      [("u", U), ("q", V), ("rest", .collection .hashBag rem none), ("x", X), ("p", K), ("t", T)]
      relMettaComm [.fvar "t", .fvar "u", .fvar "p", .fvar "q", .fvar "pOut", .fvar "qOut"]) :
    ∃ a b, .apply "MRef" [a, b] ∈ correctedCommWitness supply [T, U, K, V] ∧
      applyBindings final commSymRule.right = .collection .hashBag (a :: b :: rem) none := by
  simp only [relationQueryStep, List.mem_flatMap, List.mem_filterMap] at member
  obtain ⟨tuple, provided, extension, matched, merged⟩ := member
  simp only [rows] at provided
  simp [applyBindings, builtinRelationTuples, relMettaComm, commTuples] at provided
  obtain ⟨w, inWitness, shape⟩ := provided
  split at shape
  · rename_i a b
    simp only [Option.some.injEq] at shape
    subst shape
    refine ⟨a, b, inWitness, ?_⟩
    simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings] at matched
    subst matched
    simp [mergeBindings] at merged
    subst merged
    simp [commSymRule, applyBindings]
  · cases shape

/-- The REFL premise reads a row of the COMM-only lookahead. -/
theorem refl_premise {lang : LanguageDef} {env : RelationEnv} {X S : Pattern} {final : Bindings}
    (member : final ∈ relationQueryStep env lang [("p", S), ("x", X)] relMettaStepNoReflect
      [.fvar "p", .fvar "pNext"]) :
    ∃ tgt, [S, tgt] ∈ env.tuples relMettaStepNoReflect [S, .fvar "pNext"] ∧
      applyBindings final reflRuleSpec.right = pFor (tProc tgt) X pZero := by
  simp only [relationQueryStep, List.mem_flatMap, List.mem_filterMap] at member
  obtain ⟨tuple, provided, extension, matched, merged⟩ := member
  simp [applyBindings, builtinRelationTuples, relMettaStepNoReflect] at provided
  rcases tuple with _ | ⟨s, _ | ⟨tgt, _ | ⟨extra, more⟩⟩⟩
  · simp [matchRelationArgs] at matched
  · simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings] at matched
  · simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings] at matched
    obtain ⟨rfl, rfl⟩ := matched
    simp [mergeBindings] at merged
    subst merged
    exact ⟨tgt, provided, by simp [reflRuleSpec, applyBindings, pFor, tProc, pZero]⟩
  · simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings] at matched

theorem perm_getElem_eraseIdx {α : Type} [DecidableEq α] (l : List α) (i : ℕ) (hi : i < l.length) :
    l.Perm (l[i] :: l.eraseIdx i) :=
  (List.perm_cons_erase (List.getElem_mem hi)).trans ((List.erase_getElem hi).cons _)

theorem calcList_of_collection {elems : List Pattern} {r : Option String}
    (inCalc : Corrected.calcTerm (.collection .hashBag elems r) = true) :
    r = none ∧ ∀ e ∈ elems, Corrected.calcTerm e = true := by
  simp only [Corrected.calcTerm, Bool.and_eq_true, Option.isNone_iff_eq_none,
    Corrected.calcList_iff] at inCalc
  exact inCalc

/-- A bag is the bag laws' rearrangement of its elements. -/
theorem bagEq_bag_perm {elems elems' : List Pattern} (perm : elems.Perm elems') :
    Corrected.BagEq (pPar elems) (pPar elems') := by
  rw [Corrected.bagEq_iff]
  simp only [pPar, Corrected.components, Corrected.componentsList_eq_flatMap]
  exact (perm.flatMap_right Corrected.components).map _

theorem components_pPar_cons2 (a b : Pattern) (rest : List Pattern) :
    Corrected.components (pPar (a :: b :: rest)) = Corrected.components (par (par a b) (pPar rest)) := by
  simp [pPar, par, Corrected.components, Corrected.componentsList, List.append_assoc]

theorem components_pPar_cons1 (a : Pattern) (rest : List Pattern) :
    Corrected.components (pPar (a :: rest)) = Corrected.components (par a (pPar rest)) := by
  simp [pPar, par, Corrected.components, Corrected.componentsList]

/-- A composition of two with a bag is the bag with two more elements. -/
theorem bagEq_par_cons2 (a b : Pattern) (rest : List Pattern) :
    Corrected.BagEq (par (par a b) (pPar rest)) (.collection .hashBag (a :: b :: rest) none) := by
  rw [Corrected.bagEq_iff]
  show List.Perm _ ((Corrected.components (pPar (a :: b :: rest))).map _)
  rw [components_pPar_cons2]

/-- A composition with a bag is the bag with one more element. -/
theorem bagEq_par_cons (a : Pattern) (rest : List Pattern) :
    Corrected.BagEq (par a (pPar rest)) (.collection .hashBag (a :: rest) none) := by
  rw [Corrected.bagEq_iff]
  show List.Perm _ ((Corrected.components (pPar (a :: rest))).map _)
  rw [components_pPar_cons1]

/-- **Engine soundness.** A step of the authored COMM, REFL and parallel rules,
answered by an environment whose COMM rows are the corrected witness and whose
REFL rows are sound steps, is a step of the corrected relational semantics
modulo the bag laws. -/
theorem engine_sound (lang : LanguageDef) (env : RelationEnv) (supply : List String)
    (rules : ∀ rule ∈ lang.rewrites, rule = commSymRule ∨ rule = reflRuleSpec ∨ rule = parCongRuleSpec)
    (commRows : ∀ args, env.tuples relMettaComm args = commTuples supply args)
    (reflRows : ∀ S tgt, [S, tgt] ∈ env.tuples relMettaStepNoReflect [S, .fvar "pNext"] →
      Corrected.calcTerm S = true → Corrected.BagStep Corrected.conventional S tgt) :
    ∀ fuel P Q, StepAt (engineBasePremises env) lang fuel P Q → Corrected.calcTerm P = true →
      Corrected.BagStep Corrected.conventional P Q := by
  intro fuel
  induction fuel with
  | zero => intro P Q step; cases step
  | succ fuel ih =>
      intro P Q step inCalc
      cases step with
      | rule ruleMem matched premises applied =>
          rw [matchPatternForRule_eq_syntactic] at matched
          rcases rules _ ruleMem with rfl | rfl | rfl
          · -- COMM on two elements of a bag
            obtain ⟨elems, r, i, j, rfl, hi, hj, T, X, K, U, V, eqFirst, eqSecond, rfl⟩ :=
              matchPattern_commLeft matched
            simp only [commSymRule] at premises
            cases premises with
            | cons premise rest =>
                cases rest
                cases premise with
                | relationQuery member =>
                    simp only [engineBasePremises, premiseStepWithEnv] at member
                    obtain ⟨a, b, witness, reduct⟩ := comm_premise commRows member
                    rw [applyBindingsForRule_eq _ _ _ (by decide +kernel), reduct] at applied
                    subst applied
                    obtain ⟨rNone, calcElems⟩ := calcList_of_collection inCalc
                    subst rNone
                    have firstMem : elems[i] ∈ elems := List.getElem_mem hi
                    have secondMem : (elems.eraseIdx i)[j] ∈ elems :=
                      List.mem_of_mem_eraseIdx (List.getElem_mem hj)
                    have calcFirst := calcElems _ firstMem
                    have calcSecond := calcElems _ secondMem
                    rw [eqFirst] at calcFirst
                    rw [eqSecond] at calcSecond
                    obtain ⟨calcT, _, calcK⟩ := Corrected.calcTerm_pFor calcFirst
                    obtain ⟨calcU, _, calcV⟩ := Corrected.calcTerm_pFor calcSecond
                    have root := comm_witness_sound supply (x := X) calcT calcU calcK calcV witness
                    have perm : elems.Perm (pFor T X K :: pFor U X V :: (elems.eraseIdx i).eraseIdx j) := by
                      have first := perm_getElem_eraseIdx elems i hi
                      have second := perm_getElem_eraseIdx (elems.eraseIdx i) j hj
                      rw [eqFirst] at first
                      rw [eqSecond] at second
                      exact first.trans (second.cons _)
                    have before : Corrected.BagEq (.collection .hashBag elems none)
                        (par (par (pFor T X K) (pFor U X V)) (pPar ((elems.eraseIdx i).eraseIdx j))) := by
                      have := bagEq_bag_perm perm
                      rw [Corrected.bagEq_iff] at this ⊢
                      rw [← components_pPar_cons2]
                      exact this
                    have after : Corrected.BagEq (par (par a b) (pPar ((elems.eraseIdx i).eraseIdx j)))
                        (.collection .hashBag (a :: b :: (elems.eraseIdx i).eraseIdx j) none) := by
                      rw [Corrected.bagEq_iff]
                      show List.Perm _ ((Corrected.components (pPar (a :: b :: _))).map _)
                      rw [components_pPar_cons2]
                    exact .congruence before (.parallel _ root.toBagStep) after
          · -- REFL over the COMM-only lookahead
            obtain ⟨X, S, rfl, rfl⟩ := matchPattern_reflLeft matched
            simp only [reflRuleSpec] at premises
            cases premises with
            | cons premise rest =>
                cases rest
                cases premise with
                | relationQuery member =>
                    simp only [engineBasePremises, premiseStepWithEnv] at member
                    obtain ⟨tgt, row, reduct⟩ := refl_premise member
                    rw [applyBindingsForRule_eq _ _ _ (by decide +kernel), reduct] at applied
                    subst applied
                    have calcS := (Corrected.calcTerm_pReflect inCalc).2
                    exact .reflect X (reflRows S tgt row calcS)
          · -- PAR into one element of a bag
            obtain ⟨elems, r, i, rfl, hi, rfl⟩ := matchPattern_parLeft matched
            simp only [parCongRuleSpec] at premises
            cases premises with
            | cons premise rest =>
                cases rest
                cases premise with
                | congruence inner matchedNext merged =>
                    simp only [matchPattern, List.mem_singleton] at matchedNext
                    subst matchedNext
                    simp [mergeBindings] at merged
                    subst merged
                    rw [applyBindingsForRule_eq _ _ _ (by decide +kernel)] at applied
                    simp [parCongRuleSpec, applyBindings] at applied inner
                    subst applied
                    obtain ⟨rNone, calcElems⟩ := calcList_of_collection inCalc
                    subst rNone
                    have step := ih _ _ inner (calcElems _ (List.getElem_mem hi))
                    have before : Corrected.BagEq (.collection .hashBag elems none)
                        (par elems[i] (pPar (elems.eraseIdx i))) := by
                      have := bagEq_bag_perm (perm_getElem_eraseIdx elems i hi)
                      rw [Corrected.bagEq_iff] at this ⊢
                      rw [← components_pPar_cons1]
                      exact this
                    exact .congruence before (.parallel _ step) (bagEq_par_cons _ _)

/-- **The COMM-only lookahead is sound** for the bag-law semantics. -/
theorem correctedCommOnlyStep_sound (supply : List String) {S T : Pattern} (inCalc : Corrected.calcTerm S = true)
    (member : T ∈ correctedCommOnlyStep supply S) : Corrected.BagStep Corrected.conventional S T := by
  refine engine_sound mettaCalcCommOnly (commOnlyRelEnv supply) supply ?_ ?_ ?_ executableContextFuel S T
    (mem_rewriteAt_iff_stepAt.mp member) inCalc
  · intro rule member
    rw [mettaCalcCommOnly_rewrites] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr rfl)
  · intro args
    simp [commOnlyRelEnv]
  · intro S tgt row _
    simp [commOnlyRelEnv, relMettaStepNoReflect, relMettaComm] at row

/-- **The premise-contract step is sound for the bag-law semantics.** Every
reduct of `stepViaPremiseContract` of a calculus process is a step of the
corrected relational semantics modulo the bag laws. -/
theorem stepViaPremiseContract_sound {P Q : Pattern} (inCalc : Corrected.calcTerm P = true)
    (member : Q ∈ stepViaPremiseContract P) : Corrected.BagStep Corrected.conventional P Q := by
  refine engine_sound mettaCalc (correctedRelEnv (pvars (Corrected.close P))) (pvars (Corrected.close P))
    ?_ ?_ ?_ executableContextFuel P Q
    (mem_rewriteAt_iff_stepAt.mp member) inCalc
  · intro rule member
    rw [mettaCalc_rewrites] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
  · intro args
    simp [correctedRelEnv]
  · intro S tgt row calcS
    have notComm : (relMettaStepNoReflect == relMettaComm) = false := by decide +kernel
    simp only [correctedRelEnv, notComm, if_true, Bool.false_eq_true, if_false, beq_self_eq_true] at row
    simp only [stepNoReflectTuples, comm_only_step_adapter_spec, List.mem_map, List.cons.injEq,
      and_true, true_and] at row
    obtain ⟨tgt', member, rfl⟩ := row
    exact correctedCommOnlyStep_sound _ calcS member

/-! ### Completeness for COMM between two elements of one bag -/

/-- Pick an element out of a list by position, keeping the others in order. -/
theorem exists_eraseIdx_of_perm {α : Type} [DecidableEq α] {l rest : List α} {a : α}
    (perm : l.Perm (a :: rest)) : ∃ (i : ℕ) (hi : i < l.length), l[i] = a ∧ (l.eraseIdx i).Perm rest := by
  have member : a ∈ l := perm.symm.subset (List.mem_cons_self ..)
  obtain ⟨i, hi, found⟩ := List.getElem_of_mem member
  refine ⟨i, hi, found, ?_⟩
  have split := perm_getElem_eraseIdx l i hi
  rw [found] at split
  exact (split.symm.trans perm).cons_inv

/-- The corrected witness produces the corrected COMM of two inputs. -/
theorem witness_of_commClosed (supply : List String) {t u A B a b : Pattern}
    (member : par a b ∈ Corrected.commClosed (supply ++ witnessAvoid t u A B) (Corrected.close (pFor t pZero A))
      (Corrected.close (pFor u pZero B))) :
    .apply "MRef" [a, b] ∈ correctedCommWitness supply [t, u, A, B] := by
  simp only [correctedCommWitness, List.mem_filterMap]
  exact ⟨par a b, member, rfl⟩

/-- **Completeness for COMM between two elements of one bag.** If two
elements of a bag of calculus processes communicate on the closing fragment,
the premise-contract step produces the reduct, with the other elements kept,
up to the bag laws. -/
theorem stepViaPremiseContract_complete_comm {elems rest : List Pattern} {t u x A B : Pattern} {bs : Bindings}
    (perm : elems.Perm (pFor t x A :: pFor u x B :: rest)) (principal : Corrected.Principal t u bs)
    (admitted : Corrected.closing t A u B bs) :
    ∃ Q' ∈ stepViaPremiseContract (pPar elems),
      Corrected.BagEq Q' (par (par (applyDot bs A) (applyDot bs B)) (pPar rest)) := by
  obtain ⟨i, hi, first, perm₁⟩ := exists_eraseIdx_of_perm perm
  obtain ⟨j, hj, second, perm₂⟩ := exists_eraseIdx_of_perm perm₁
  -- the witness
  have fresh : ∀ z ∈ pvars (Corrected.close (par (pFor t pZero A) (pFor u pZero B))),
      z ∈ pvars (Corrected.close (pPar elems)) ++ witnessAvoid t u A B := fun _ occurs =>
    List.mem_append_right _ occurs
  obtain ⟨Q₀, fired, alpha⟩ :=
    Corrected.commClosed_complete (pvars (Corrected.close (pPar elems)) ++ witnessAvoid t u A B) t u pZero A B
      bs principal admitted fresh
  have shape : ∃ a b, Q₀ = par a b := by
    have closeT := Corrected.closeIn_pFor [] t pZero A
    have closeU := Corrected.closeIn_pFor [] u pZero B
    unfold Corrected.close at fired
    rw [closeT, closeU] at fired
    simp only [Corrected.commClosed, Corrected.asGuard_pFor] at fired
    split at fired
    · split at fired
      · simp only [List.mem_singleton] at fired
        exact ⟨_, _, fired⟩
      · cases fired
    · cases fired
  obtain ⟨a, b, rfl⟩ := shape
  have witness := witness_of_commClosed _ fired
  -- the engine's run
  let rem := (elems.eraseIdx i).eraseIdx j
  let initial : Bindings :=
    [("u", u), ("q", B), ("rest", .collection .hashBag rem none), ("x", x), ("p", A), ("t", t)]
  have matched : initial ∈ matchPattern commSymRule.left (pPar elems) := by
    apply matchPattern_iff_matchRel.mpr
    have guard : ∀ (n₁ n₂ n₃ : String) (T X K : Pattern) (hb : Bindings),
        mergeBindings [(n₂, X)] [(n₃, K)] = some [(n₃, K), (n₂, X)] →
        mergeBindings [(n₁, T)] [(n₃, K), (n₂, X)] = some hb →
        MatchRel (.apply "MFor" [.fvar n₁, .fvar n₂, .fvar n₃]) (pFor T X K) hb := by
      intro n₁ n₂ n₃ T X K hb merge₂ merge₁
      exact .apply (.cons .fvar (.cons .fvar (.cons .fvar .nil (by simp [mergeBindings])) merge₂) merge₁) rfl
    have firstRel := guard "t" "x" "p" t x A [("x", x), ("p", A), ("t", t)]
      (by simp [mergeBindings]) (by simp [mergeBindings])
    have secondRel := guard "u" "x" "q" u x B [("x", x), ("q", B), ("u", u)]
      (by simp [mergeBindings]) (by simp [mergeBindings])
    rw [← first] at firstRel
    rw [← second] at secondRel
    refine .collection (by decide) (.cons (bs := initial)
      (restB := [("rest", .collection .hashBag rem none), ("x", x), ("q", B), ("u", u)]) i hi firstRel
      (.cons (restB := [("rest", .collection .hashBag rem none)]) j hj secondRel .nilRest ?_) ?_)
    · simp [mergeBindings]
    · simp [mergeBindings, initial, rem]
  have queried : [("pOut", a), ("qOut", b), ("u", u), ("q", B), ("rest", .collection .hashBag rem none),
      ("x", x), ("p", A), ("t", t)] ∈ engineBasePremises (correctedRelEnv (pvars (Corrected.close (pPar elems))))
        mettaCalc initial
        (.relationQuery relMettaComm [.fvar "t", .fvar "u", .fvar "p", .fvar "q", .fvar "pOut", .fvar "qOut"]) := by
    simp only [engineBasePremises, premiseStepWithEnv, relationQueryStep, List.mem_flatMap, List.mem_filterMap]
    refine ⟨[t, u, A, B, a, b], ?_, [("qOut", b), ("pOut", a)], ?_, ?_⟩
    · simp only [List.mem_append]
      refine .inr ?_
      simp [correctedRelEnv, initial, applyBindings, commTuples]
      exact ⟨_, witness, rfl⟩
    · simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings, initial]
    · simp [mergeBindings, initial]
  refine ⟨.collection .hashBag (a :: b :: rem) none, ?_, ?_⟩
  · apply mem_rewriteAt_iff_stepAt.mpr
    refine StepAt.rule (rule := commSymRule) (initialBindings := initial) (by simp [mettaCalc_rewrites])
      (by rw [matchPatternForRule_eq_syntactic]; exact matched)
      (.cons (.relationQuery queried) (.nil _)) ?_
    rw [applyBindingsForRule_eq _ _ _ (by decide +kernel)]
    simp [commSymRule, applyBindings]
  · refine (bagEq_par_cons2 a b rem).symm.trans ?_
    exact Corrected.BagEq.par (.of_alphaEq alpha) (bagEq_bag_perm perm₂)

end Engine

/-! ### Where the premise-contract step stops -/

namespace EngineControls

def g1 : Proc := pFor (.fvar "a") demoChan (.fvar "a")
def g2 : Proc := pFor pZero demoChan (.fvar "a")

/-- The canary's two inputs, one bag apart. -/
def nestedBag : Proc := pPar [pPar [g1], g2]

/-- **Outside the fragment: inputs in different bags.** The engine matches
COMM among the elements of one bag; the bag laws bring the two inputs
together. -/
theorem nested_bag_missed :
    stepViaPremiseContract nestedBag = [] ∧
      Corrected.BagStep Corrected.conventional nestedBag (pPar [pPar [nQuote pZero, .fvar "a"]]) :=
  ⟨by decide +kernel, Corrected.cstepBag_sound (by decide +kernel) (by decide +kernel)⟩

/-- **Outside the fragment: nested reflection.** The REFL premise is the
COMM-only lookahead, so a reflection whose process is itself a reflection has
no reduct. -/
theorem nested_reflection_missed :
    stepViaPremiseContract Corrected.Controls.nestedSource = [] ∧
      Corrected.BagStep Corrected.conventional Corrected.Controls.nestedSource
        (pFor (tProc (pFor (tProc (par (nQuote pZero) (.fvar "a"))) demoChan pZero)) demoChan pZero) :=
  ⟨by decide +kernel, Corrected.Controls.corrected_nested_sound.toBagStep⟩

def h1 : Proc := pFor (.fvar "X") demoChan (.fvar "X")
def h2 : Proc := pFor (.fvar "Y") demoChan pZero

/-- A bag with a free name `##`, which a witness without a supply takes as a
fresh name. -/
def contextBag : Proc := pPar [h1, h2, .fvar "##"]

/-- **The supply keeps residual names fresh for the whole process.** Without a
supply the witness is fresh for the redex only, and its residual name is the
free name `##` of the surrounding bag. Supplied with the process's free names,
as `stepViaPremiseContract` is, it reads a name fresh for the whole process,
as the corrected step does. -/
theorem supply_keeps_residuals_fresh :
    pPar [nQuote (.fvar "##"), pZero, .fvar "##"] ∈
        reductsUsing (correctedRelEnv []) mettaCalc executableContextFuel contextBag ∧
      pPar [nQuote (.fvar "####"), pZero, .fvar "##"] ∈ stepViaPremiseContract contextBag ∧
      pPar [nQuote (.fvar "##"), pZero, .fvar "##"] ∉ stepViaPremiseContract contextBag ∧
      pPar [pPar [nQuote (.fvar "####"), pZero], .fvar "##"] ∈ Corrected.cstepBag contextBag := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end EngineControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Adequacy
