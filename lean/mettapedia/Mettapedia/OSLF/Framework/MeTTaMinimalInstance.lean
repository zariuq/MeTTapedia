import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.Formula

/-!
# MeTTa Minimal State Client (OSLF)

First concrete OSLF client that models a MeTTa-style machine state with a
spec-facing minimal instruction set:

1. `Eval`
2. `Unify`
3. `Chain`
4. `CollapseBind`
5. `SuperposeBind`
6. `Return`/`Done`

This is intentionally minimal and executable in the current `LanguageDef`
pipeline, so it can serve as the starting point for fuller MeTTa/OSLF lifting.
-/

namespace Mettapedia.OSLF.Framework.MeTTaMinimalInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Formula

/-- Minimal MeTTa-like state language with spec-facing instruction-tagged states. -/
def mettaMinimal : LanguageDef := {
  name := "MeTTaMinimalState",
  types := ["State", "Instr", "Atom"],
  terms := [
    { label := "State", category := "State",
      params := [.simple "instr" (.base "Instr"),
                 .simple "x" (.base "Atom"),
                 .simple "y" (.base "Atom")],
      syntaxPattern := [.terminal "<", .nonTerminal "instr", .terminal "|",
                        .nonTerminal "x", .terminal "|", .nonTerminal "y", .terminal ">"] },
    { label := "Eval", category := "Instr",
      params := [.simple "a" (.base "Atom")],
      syntaxPattern := [.terminal "eval", .terminal "(", .nonTerminal "a", .terminal ")"] },
    { label := "Unify", category := "Instr",
      params := [.simple "lhs" (.base "Atom"), .simple "rhs" (.base "Atom")],
      syntaxPattern := [.terminal "unify", .terminal "(", .nonTerminal "lhs", .terminal ",",
                        .nonTerminal "rhs", .terminal ")"] },
    { label := "Chain", category := "Instr",
      params := [.simple "src" (.base "Atom"), .simple "tmpl" (.base "Atom")],
      syntaxPattern := [.terminal "chain", .terminal "(", .nonTerminal "src", .terminal ",",
                        .nonTerminal "tmpl", .terminal ")"] },
    { label := "CollapseBind", category := "Instr",
      params := [.simple "src" (.base "Atom")],
      syntaxPattern := [.terminal "collapse-bind", .terminal "(", .nonTerminal "src", .terminal ")"] },
    { label := "SuperposeBind", category := "Instr",
      params := [.simple "packed" (.base "Atom")],
      syntaxPattern := [.terminal "superpose-bind", .terminal "(", .nonTerminal "packed", .terminal ")"] },
    { label := "Return", category := "Instr",
      params := [.simple "a" (.base "Atom")],
      syntaxPattern := [.terminal "return", .terminal "(", .nonTerminal "a", .terminal ")"] },
    { label := "Done", category := "Instr", params := [],
      syntaxPattern := [.terminal "done"] },
    { label := "ATrue", category := "Atom", params := [],
      syntaxPattern := [.terminal "true"] },
    { label := "AFalse", category := "Atom", params := [],
      syntaxPattern := [.terminal "false"] }
  ],
  equations := [],
  rewrites := [
    -- eval(a) transitions to return(a)
    { name := "StepEval",
      typeContext := [("a", .base "Atom"), ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [],
      left := .apply "State" [.apply "Eval" [.fvar "a"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.fvar "a"], .fvar "x", .fvar "y"] },

    -- unify(lhs, rhs) hit branch, premise-checked via built-in eq relation
    { name := "StepUnifyHit",
      typeContext := [("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [.relationQuery "eq" [.fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Unify" [.fvar "lhs", .fvar "rhs"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.apply "ATrue" []], .fvar "x", .fvar "y"] },

    -- unify(lhs, rhs) miss branch, supplied via external relation env
    { name := "StepUnifyMiss",
      typeContext := [("lhs", .base "Atom"), ("rhs", .base "Atom"),
                      ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [.relationQuery "neq" [.fvar "lhs", .fvar "rhs"]],
      left := .apply "State" [.apply "Unify" [.fvar "lhs", .fvar "rhs"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.apply "AFalse" []], .fvar "x", .fvar "y"] },

    -- chain(src, tmpl) executes one explicit substitution oracle step
    { name := "StepChain",
      typeContext := [("src", .base "Atom"), ("tmpl", .base "Atom"),
                      ("out", .base "Atom"), ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [.relationQuery "chain" [.fvar "src", .fvar "tmpl", .fvar "out"]],
      left := .apply "State" [.apply "Chain" [.fvar "src", .fvar "tmpl"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.fvar "out"], .fvar "x", .fvar "out"] },

    -- collapse-bind(src) packs non-deterministic results via external relation env
    { name := "StepCollapseBind",
      typeContext := [("src", .base "Atom"), ("packed", .base "Atom"),
                      ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [.relationQuery "collapseBind" [.fvar "src", .fvar "packed"]],
      left := .apply "State" [.apply "CollapseBind" [.fvar "src"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.fvar "packed"], .fvar "x", .fvar "packed"] },

    -- superpose-bind(packed) resumes from packed choices via external relation env
    { name := "StepSuperposeBind",
      typeContext := [("packed", .base "Atom"), ("unpacked", .base "Atom"),
                      ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [.relationQuery "superposeBind" [.fvar "packed", .fvar "unpacked"]],
      left := .apply "State" [.apply "SuperposeBind" [.fvar "packed"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Return" [.fvar "unpacked"], .fvar "x", .fvar "unpacked"] },

    -- return(a) commits observable result into state tail and marks done
    { name := "StepReturn",
      typeContext := [("a", .base "Atom"), ("x", .base "Atom"), ("y", .base "Atom")],
      premises := [],
      left := .apply "State" [.apply "Return" [.fvar "a"], .fvar "x", .fvar "y"],
      right := .apply "State" [.apply "Done" [], .fvar "x", .fvar "a"] }
  ]
}

/-- OSLF synthesis for the minimal MeTTa client (`State` process sort). -/
def mettaMinimalOSLF := langOSLF mettaMinimal "State"

/-- Automatic modal Galois connection for the minimal MeTTa client. -/
theorem mettaMinimalGalois :
    GaloisConnection (langDiamond mettaMinimal) (langBox mettaMinimal) :=
  langGalois mettaMinimal

/-- The `State` process sort in the constructor-category view of `mettaMinimal`. -/
def mettaState : LangSort mettaMinimal := ⟨"State", by decide⟩

/-- Example state constructor for executable smoke checks. -/
private def mkState (instr x y : Pattern) : Pattern :=
  .apply "State" [instr, x, y]

/-- `eval` instruction builder. -/
private def iEval (a : Pattern) : Pattern := .apply "Eval" [a]

/-- `unify` instruction builder. -/
private def iUnify (a b : Pattern) : Pattern := .apply "Unify" [a, b]

/-- `chain` instruction builder. -/
private def iChain (src tmpl : Pattern) : Pattern := .apply "Chain" [src, tmpl]

/-- `collapse-bind` instruction builder. -/
private def iCollapseBind (src : Pattern) : Pattern := .apply "CollapseBind" [src]

/-- `superpose-bind` instruction builder. -/
private def iSuperposeBind (packed : Pattern) : Pattern := .apply "SuperposeBind" [packed]

/-- External relation environment for spec-facing relationQuery premises. -/
private def mettaMinimalRelEnv : RelationEnv where
  tuples := fun rel _args =>
    let t : Pattern := Pattern.apply "ATrue" []
    let f : Pattern := Pattern.apply "AFalse" []
    if rel = "neq" then
      [ [t, f], [f, t] ]
    else if rel = "chain" then
      [ [t, f, t], [f, t, f] ]
    else if rel = "collapseBind" then
      [ [t, t], [f, f] ]
    else if rel = "superposeBind" then
      [ [t, t], [f, f] ]
    else []

-- Smoke check 1: eval state has a one-step reduct.
#eval! do
  let a : Pattern := Pattern.apply "ATrue" []
  let s := mkState (iEval a) (Pattern.apply "AFalse" []) a
  let reducts := rewriteWithContextWithPremises mettaMinimal s
  IO.println s!"MeTTaMinimal demo (eval): reduct count = {reducts.length}"

-- Smoke check 2: unify(a,a) state has at least one reduct (hit branch).
#eval! do
  let a : Pattern := Pattern.apply "ATrue" []
  let s := mkState (iUnify a a) (Pattern.apply "AFalse" []) a
  let reducts := rewriteWithContextWithPremises mettaMinimal s
  IO.println s!"MeTTaMinimal demo (unify hit): reduct count = {reducts.length}"

-- Smoke check 3: unify(true,false) miss branch via external `neq` relation env.
#eval! do
  let t : Pattern := Pattern.apply "ATrue" []
  let f : Pattern := Pattern.apply "AFalse" []
  let s := mkState (iUnify t f) f t
  let reducts := rewriteWithContextWithPremisesUsing mettaMinimalRelEnv mettaMinimal s
  IO.println s!"MeTTaMinimal demo (unify miss via env): reduct count = {reducts.length}"

-- Smoke check 4: chain(src, tmpl) via external chain relation.
#eval! do
  let t : Pattern := Pattern.apply "ATrue" []
  let f : Pattern := Pattern.apply "AFalse" []
  let s := mkState (iChain t f) f t
  let reducts := rewriteWithContextWithPremisesUsing mettaMinimalRelEnv mettaMinimal s
  IO.println s!"MeTTaMinimal demo (chain via env): reduct count = {reducts.length}"

-- Smoke check 5: collapse-bind(src) via external collapse relation.
#eval! do
  let t : Pattern := Pattern.apply "ATrue" []
  let s := mkState (iCollapseBind t) t t
  let reducts := rewriteWithContextWithPremisesUsing mettaMinimalRelEnv mettaMinimal s
  IO.println s!"MeTTaMinimal demo (collapse-bind via env): reduct count = {reducts.length}"

-- Smoke check 6: superpose-bind(packed) via external superpose relation.
#eval! do
  let f : Pattern := Pattern.apply "AFalse" []
  let s := mkState (iSuperposeBind f) f f
  let reducts := rewriteWithContextWithPremisesUsing mettaMinimalRelEnv mettaMinimal s
  IO.println s!"MeTTaMinimal demo (superpose-bind via env): reduct count = {reducts.length}"

-- Verify instance and theorem are available.
#check mettaMinimalOSLF
#check mettaMinimalGalois
#check mettaState

/-- Concrete unary sort-crossings extracted from `mettaMinimal`. -/
private theorem mettaMinimal_unaryCrossings :
    unaryCrossings mettaMinimal =
      [("Eval", "Atom", "Instr"),
       ("CollapseBind", "Atom", "Instr"),
       ("SuperposeBind", "Atom", "Instr"),
       ("Return", "Atom", "Instr")] := by
  native_decide

/-- No unary sort-crossing arrow can target `State` in `mettaMinimal`. -/
private theorem mettaMinimal_noArrowToState
    {d : LangSort mettaMinimal}
    (arr : SortArrow mettaMinimal d mettaState) : False := by
  have hmem : (arr.label, d.val, "State") ∈ unaryCrossings mettaMinimal := by
    simpa [mettaState] using arr.valid
  rw [mettaMinimal_unaryCrossings] at hmem
  simp at hmem

/-- Concrete path-order law for the `mettaMinimal` `State` sort. -/
theorem mettaMinimal_pathOrder
    (seed : Pattern) :
    ∀ {a b : LangSort mettaMinimal}
      (g : SortPath mettaMinimal a b) (h : SortPath mettaMinimal b mettaState),
        pathSem mettaMinimal g (pathSem mettaMinimal h seed) =
          pathSem mettaMinimal (g.comp h) seed := by
  intro a b g h
  cases h with
  | nil =>
      simp [pathSem, SortPath.comp]
  | cons h' arr =>
      exfalso
      exact mettaMinimal_noArrowToState arr

/-! ## End-to-End Bridge (Checker → Fiber → PathSemClosed BC+Graph) -/

/-- End-to-end MeTTaMinimal bridge, parallel to TinyML:

`checkLangUsing` soundness at a concrete `State` is lifted to representable-fiber
`satisfies`, embedded into `PathSemClosedPred`, and paired with the COMM
substitution/rewrite BC + graph-`◇` square through the package path.
-/
theorem mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv mettaMinimal I_check fuel p φf = .sat)
    (seed q : Pattern)
    (hPkg :
      Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
        mettaMinimal mettaState seed q)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        mettaMinimal mettaState seed
        (sem (langReducesUsing relEnv mettaMinimal) I_sem φf))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj mettaMinimal)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    {X : Opposite (ConstructorObj mettaMinimal)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState).obj X)
    (hp : pathSem mettaMinimal hArrow seed = p) :
    let ψ := sem (langReducesUsing relEnv mettaMinimal) I_sem φf
    (langOSLF mettaMinimal "State").satisfies (S := "State")
      (pathSem mettaMinimal hArrow seed) ψ
    ∧ Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ
        (pathSem mettaMinimal hArrow seed)
    ∧
      ((CategoryTheory.Subobject.map pi2).obj
          ((CategoryTheory.Subobject.pullback pi1).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ hPkg)))
        =
      (CategoryTheory.Subobject.pullback g).obj
          ((CategoryTheory.Subobject.map f).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ hPkg))))
    ∧
      (langDiamondUsing relEnv mettaMinimal
        (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
          (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ)) p ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).source.app X e).down = p ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).target.app X e).down ∧
            Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ u) := by
  let ψ : Pattern → Prop := sem (langReducesUsing relEnv mettaMinimal) I_sem φf
  have hSatFiber :
      (langOSLF mettaMinimal "State").satisfies (S := "State")
        (pathSem mettaMinimal hArrow seed) ψ :=
    checkLangUsing_sat_sound_sort_fiber_mem_iff
      (relEnv := relEnv) (lang := mettaMinimal) (procSort := "State")
      (I_check := I_check) (I_sem := I_sem)
      h_atoms hSat mettaState seed hNat hArrow hp
  have hClosedBase :
      Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ
        (pathSem mettaMinimal hArrow seed) :=
    Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred.base hSatFiber
  have hBCGraph :
      ((CategoryTheory.Subobject.map pi2).obj
          ((CategoryTheory.Subobject.pullback pi1).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ hPkg)))
        =
      (CategoryTheory.Subobject.pullback g).obj
          ((CategoryTheory.Subobject.map f).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ hPkg))))
      ∧
      (langDiamondUsing relEnv mettaMinimal
        (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
          (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ)) p ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).source.app X e).down = p ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).target.app X e).down ∧
            Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ u) :=
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg
      (lang := mettaMinimal) (s := mettaState) (seed := seed) (q := q) (φ := ψ)
      (hPkg := hPkg)
      (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
      (hpb := hpb) (hf := hf) (hpi2 := hpi2)
      (relEnv := relEnv) (X := X) (p := p)
  exact ⟨hSatFiber, hClosedBase, hBCGraph.1, hBCGraph.2⟩

/-- MeTTaMinimal concrete package constructor from a named `liftEq` theorem. -/
theorem mettaMinimal_commDiPathSemLiftPkg_of_liftEq
    (seed q : Pattern)
    (hLiftEq :
      ∀ {a b : LangSort mettaMinimal}
        (g : SortPath mettaMinimal a b) (h : SortPath mettaMinimal b mettaState)
        {u : Pattern},
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem mettaMinimal h seed →
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem mettaMinimal g u) q =
            pathSem mettaMinimal (g.comp h) seed) :
    Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
      mettaMinimal mettaState seed q := by
  exact
    Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_liftEq
      mettaMinimal mettaState seed q hLiftEq

/-- No-`hPkg` wrapper: consumes a named MeTTaMinimal `liftEq` law directly. -/
theorem mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv mettaMinimal I_check fuel p φf = .sat)
    (seed q : Pattern)
    (hLiftEq :
      ∀ {a b : LangSort mettaMinimal}
        (g : SortPath mettaMinimal a b) (h : SortPath mettaMinimal b mettaState)
        {u : Pattern},
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem mettaMinimal h seed →
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem mettaMinimal g u) q =
            pathSem mettaMinimal (g.comp h) seed)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        mettaMinimal mettaState seed
        (sem (langReducesUsing relEnv mettaMinimal) I_sem φf))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj mettaMinimal)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    {X : Opposite (ConstructorObj mettaMinimal)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState).obj X)
    (hp : pathSem mettaMinimal hArrow seed = p) :
    let ψ := sem (langReducesUsing relEnv mettaMinimal) I_sem φf
    (langOSLF mettaMinimal "State").satisfies (S := "State")
      (pathSem mettaMinimal hArrow seed) ψ
    ∧ Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ
        (pathSem mettaMinimal hArrow seed)
    ∧
      ((CategoryTheory.Subobject.map pi2).obj
          ((CategoryTheory.Subobject.pullback pi1).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ
                (mettaMinimal_commDiPathSemLiftPkg_of_liftEq seed q hLiftEq))))
        =
      (CategoryTheory.Subobject.pullback g).obj
          ((CategoryTheory.Subobject.map f).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ
                (mettaMinimal_commDiPathSemLiftPkg_of_liftEq seed q hLiftEq)))))
    ∧
      (langDiamondUsing relEnv mettaMinimal
        (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
          (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ)) p ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).source.app X e).down = p ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).target.app X e).down ∧
            Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ u) := by
  let hPkg :
      Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
        mettaMinimal mettaState seed q :=
    mettaMinimal_commDiPathSemLiftPkg_of_liftEq seed q hLiftEq
  exact mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph
    (relEnv := relEnv) (I_check := I_check) (I_sem := I_sem)
    h_atoms hSat seed q hPkg hNat
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (X := X) (hArrow := hArrow) (hp := hp)

/-- Internal helper theorem (retained for compatibility):
checker soundness + package instantiation from an explicit `hPathOrder`
law + BC/graph square. Prefer
`mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto` for public use. -/
theorem mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_autoPkg
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv mettaMinimal I_check fuel p φf = .sat)
    (seed q : Pattern)
    (hPathOrder :
      ∀ {a b : LangSort mettaMinimal}
        (g : SortPath mettaMinimal a b) (h : SortPath mettaMinimal b mettaState),
          pathSem mettaMinimal g (pathSem mettaMinimal h seed) =
            pathSem mettaMinimal (g.comp h) seed)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        mettaMinimal mettaState seed
        (sem (langReducesUsing relEnv mettaMinimal) I_sem φf))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj mettaMinimal)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    {X : Opposite (ConstructorObj mettaMinimal)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState).obj X)
    (hp : pathSem mettaMinimal hArrow seed = p) :
    let ψ := sem (langReducesUsing relEnv mettaMinimal) I_sem φf
    (langOSLF mettaMinimal "State").satisfies (S := "State")
      (pathSem mettaMinimal hArrow seed) ψ
    ∧ Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ
        (pathSem mettaMinimal hArrow seed)
    ∧
      ((CategoryTheory.Subobject.map pi2).obj
          ((CategoryTheory.Subobject.pullback pi1).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ
                (Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                  mettaMinimal mettaState seed q hPathOrder))))
        =
      (CategoryTheory.Subobject.pullback g).obj
          ((CategoryTheory.Subobject.map f).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ
                (Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                  mettaMinimal mettaState seed q hPathOrder)))))
    ∧
      (langDiamondUsing relEnv mettaMinimal
        (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
          (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ)) p ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).source.app X e).down = p ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).target.app X e).down ∧
            Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ u) := by
  let hPkg :
      Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
        mettaMinimal mettaState seed q :=
    Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
      mettaMinimal mettaState seed q hPathOrder
  exact mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph
    (relEnv := relEnv) (I_check := I_check) (I_sem := I_sem)
    h_atoms hSat seed q hPkg hNat
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (X := X) (hArrow := hArrow) (hp := hp)

/-- Public no-`hPathOrder` wrapper: `mettaMinimal` discharges package
instantiation through the concrete path-order law `mettaMinimal_pathOrder`. -/
theorem mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv mettaMinimal I_check fuel p φf = .sat)
    (seed q : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        mettaMinimal mettaState seed
        (sem (langReducesUsing relEnv mettaMinimal) I_sem φf))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj mettaMinimal)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    {X : Opposite (ConstructorObj mettaMinimal)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaMinimal mettaState).obj X)
    (hp : pathSem mettaMinimal hArrow seed = p) :
    let ψ := sem (langReducesUsing relEnv mettaMinimal) I_sem φf
    (langOSLF mettaMinimal "State").satisfies (S := "State")
      (pathSem mettaMinimal hArrow seed) ψ
    ∧ Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ
        (pathSem mettaMinimal hArrow seed)
    ∧
      ((CategoryTheory.Subobject.map pi2).obj
          ((CategoryTheory.Subobject.pullback pi1).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ
                (Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                  mettaMinimal mettaState seed q (mettaMinimal_pathOrder seed)))))
        =
      (CategoryTheory.Subobject.pullback g).obj
          ((CategoryTheory.Subobject.map f).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaMinimal mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaMinimal mettaState seed q ψ
                (Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                  mettaMinimal mettaState seed q (mettaMinimal_pathOrder seed))))))
    ∧
      (langDiamondUsing relEnv mettaMinimal
        (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
          (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ)) p ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).source.app X e).down = p ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj mettaMinimal) relEnv mettaMinimal).target.app X e).down ∧
            Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaMinimal ψ u) := by
  exact mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_autoPkg
    (relEnv := relEnv) (I_check := I_check) (I_sem := I_sem)
    h_atoms hSat seed q (mettaMinimal_pathOrder seed) hNat
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (X := X) (hArrow := hArrow) (hp := hp)

attribute [deprecated mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  (since := "2026-02-13")] mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_autoPkg

/-- Spec-facing atom checker for MeTTaMinimal machine states. -/
def mettaSpecAtomCheck : AtomCheck
  | "isEvalState", .apply "State" [.apply "Eval" [_], _, _] => true
  | "isUnifyState", .apply "State" [.apply "Unify" [_, _], _, _] => true
  | "isChainState", .apply "State" [.apply "Chain" [_, _], _, _] => true
  | "isCollapseState", .apply "State" [.apply "CollapseBind" [_], _, _] => true
  | "isSuperposeState", .apply "State" [.apply "SuperposeBind" [_], _, _] => true
  | "isReturnState", .apply "State" [.apply "Return" [_], _, _] => true
  | "isDoneState", .apply "State" [.apply "Done" [], _, _] => true
  | _, _ => false

/-- Semantics for spec-facing state atoms (decidable/classifier-aligned). -/
def mettaSpecAtomSem : AtomSem :=
  fun a p => mettaSpecAtomCheck a p = true

/-- Soundness of the spec-facing atom checker by construction. -/
theorem mettaSpecAtomCheck_sound :
    ∀ a p, mettaSpecAtomCheck a p = true → mettaSpecAtomSem a p := by
  intro a p h
  simpa [mettaSpecAtomSem] using h

/-- Public API theorem for spec-facing MeTTa atoms:
`checkLangUsing ... = sat` implies denotational formula semantics. -/
theorem mettaMinimal_checkLangUsing_sat_sound_specAtoms
    {relEnv : RelationEnv}
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLangUsing relEnv mettaMinimal mettaSpecAtomCheck fuel p φ = .sat) :
    sem (langReducesUsing relEnv mettaMinimal) mettaSpecAtomSem φ p := by
  exact checkLangUsing_sat_sound
    (relEnv := relEnv) (lang := mettaMinimal)
    (I_check := mettaSpecAtomCheck) (I_sem := mettaSpecAtomSem)
    mettaSpecAtomCheck_sound hSat

/-- Default-environment specialization of spec-facing checker soundness. -/
theorem mettaMinimal_checkLang_sat_sound_specAtoms
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLang mettaMinimal mettaSpecAtomCheck fuel p φ = .sat) :
    sem (langReduces mettaMinimal) mettaSpecAtomSem φ p := by
  simpa [checkLang, langReduces] using
    (mettaMinimal_checkLangUsing_sat_sound_specAtoms
      (relEnv := RelationEnv.empty) (fuel := fuel) (p := p) (φ := φ) hSat)

#check mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph
#check mettaMinimal_commDiPathSemLiftPkg_of_liftEq
#check mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
#check mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_autoPkg
#check mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
#check mettaMinimal_pathOrder
#check mettaSpecAtomCheck
#check mettaSpecAtomSem
#check mettaMinimal_checkLangUsing_sat_sound_specAtoms

end Mettapedia.OSLF.Framework.MeTTaMinimalInstance
