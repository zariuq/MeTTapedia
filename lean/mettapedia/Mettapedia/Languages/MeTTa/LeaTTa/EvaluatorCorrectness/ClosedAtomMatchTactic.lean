import Lean.Elab.Tactic.ElabTerm
import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ClosedAtomMatching

/-! # Elaborating an ordered closed match -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ClosedAtomMatching

open Lean Meta Elab Tactic

private def prove (goal : Expr) (proofTerm : TSyntax `term) : TermElabM Expr := do
  let proof ← Term.elabTermEnsuringType proofTerm goal
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

private def closedValue (proof : TSyntax `term) (value : Expr) :
    TermElabM Expr := do
  let freeNames ← mkAppM ``Metta.Atom.vars #[value]
  let nil ← mkListLit (mkConst ``String) []
  let obligation ← mkEq freeNames nil
  prove obligation proof

/-- Read one actual match, leaving closure and distinctness to checked proofs. -/
private partial def readMatch (closure : TSyntax `term) (pattern target : Expr) :
    TermElabM Expr := do
  let left ← whnf pattern
  if left.isAppOfArity ``Metta.Atom.var 1 then
    return ← mkAppM ``AtomMatch.bind #[left.getAppArgs[0]!, target, ← closedValue closure target]
  if left.isAppOfArity ``Metta.Atom.sym 1 && (← isDefEq pattern target) then
    return ← mkAppM ``AtomMatch.symbol #[left.getAppArgs[0]!]
  let right ← whnf target
  if left.isAppOfArity ``Metta.Atom.expr 1 && right.isAppOfArity ``Metta.Atom.expr 1 then
    let rec readList (ps ts : Expr) : TermElabM (List Expr) := do
      let p ← whnf ps
      let t ← whnf ts
      if p.isAppOfArity ``List.nil 1 && t.isAppOfArity ``List.nil 1 then
        return []
      unless p.isAppOfArity ``List.cons 3 && t.isAppOfArity ``List.cons 3 do
        throwError "closed matching requires two exposed spines of equal length"
      let first ← readMatch closure p.getAppArgs[1]! t.getAppArgs[1]!
      return first :: (← readList p.getAppArgs[2]! t.getAppArgs[2]!)
    let rows ← mkListLit (mkConst ``AtomMatch) (← readList left.getAppArgs[0]! right.getAppArgs[0]!)
    let bindings ← mkAppM ``AtomMatch.captured #[rows]
    let keys ← mkAppM ``QueryOpBridge.bindingValueKeys #[bindings]
    let keys ← withTransparency .all (reduce keys)
    let obligation ← mkAppM ``List.Nodup #[keys]
    let distinct ← prove obligation (← `(term| by decide))
    return ← mkAppM ``AtomMatch.expression #[rows, distinct]
  unless ← isDefEq pattern target do
    throwError "closed literal {left} differs from {right}"
  let observed ← mkAppM ``Metta.matchAtomsWith #[← mkNone (mkConst ``Metta.GroundMatcher),
    pattern, target]
  let empty ← mkListLit (mkConst ``Metta.BindingRel) []
  let result ← mkListLit (mkConst ``Metta.Bindings) [empty]
  let obligation ← mkEq observed result
  let proof ← prove obligation (← `(term| by
    first | rfl | simp [Metta.matchAtomsWith]))
  mkAppM ``AtomMatch.literal #[pattern, proof]

elab "closed_atom_match " "using " closure:term : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  unless goal.isAppOfArity ``Eq 3 do
    throwError "expected an equality of ordered matches"
  let observable := goal.getAppArgs[1]!
  unless observable.isAppOfArity ``Metta.matchAtoms 2 do
    throwError "expected a matchAtoms observation"
  let operands := observable.getAppArgs
  let row ← readMatch closure operands[0]! operands[1]!
  closeMainGoal `closed_atom_match (← mkAppM ``AtomMatch.checked #[row])

end Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ClosedAtomMatching
