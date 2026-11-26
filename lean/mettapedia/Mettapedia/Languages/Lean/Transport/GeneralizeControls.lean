import Mettapedia.Languages.Lean.Transport.Generalize

/-!
# Controls for the least general generalization of Lean terms

Each control generalizes terms, adds the lemma through the kernel, compares its statement with the
one expected (up to definitional equality), and checks that every term is the lemma at its own
levels and arguments.  Binders before the terms are hypotheses outside the fragment.
-/

open Lean Meta Elab Command Term
open Mettapedia.Languages.Lean.Transport.Generalize

namespace Mettapedia.Languages.Lean.Transport.GeneralizeControls

syntax (name := generalizeControl)
  "#generalize_control " ident (ppSpace bracketedBinder)* " ⟪" term,* "⟫" " : " term : command

syntax (name := generalizeTrivial) "#generalize_trivial " "⟪" term,* "⟫" : command

/-- The terms, elaborated closed or under the given hypotheses. -/
def elabTerms (ts : Array Term) : TermElabM (Array Expr) :=
  ts.mapM fun t => do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

@[command_elab generalizeControl] def elabGeneralizeControl : CommandElab := fun stx =>
  match stx with
  | `(#generalize_control $n:ident $bs:bracketedBinder* ⟪$ts,*⟫ : $T) => liftTermElabM do
    elabBinders bs fun _ => do
      let es ← elabTerms ts.getElems
      let l ← generalize es
      if l.trivial then throwError "the generalization kept nothing"
      addLemma n.getId l
      let expected ← withLevelNames l.levelParams (elabType T)
      unless ← isDefEq l.type expected do
        throwError "the statement {← ppExpr l.type} is not {← ppExpr expected}"
      for j in [0:es.size] do
        let cited := mkAppN (mkConst n.getId l.levels[j]!) l.args[j]!
        unless ← isDefEq cited es[j]! do throwError "term {j} is not the lemma at its arguments"
      logInfo m!"{n.getId} : {← ppExpr l.type}"
  | _ => throwUnsupportedSyntax

@[command_elab generalizeTrivial] def elabGeneralizeTrivial : CommandElab := fun stx =>
  match stx with
  | `(#generalize_trivial ⟪$ts,*⟫) => liftTermElabM do
    let l ← generalize (← elabTerms ts.getElems)
    unless l.trivial do throwError "expected a generalization that keeps nothing: {← ppExpr l.type}"
    logInfo m!"trivial: {← ppExpr l.type}"
  | _ => throwUnsupportedSyntax

/-! Positive: values become parameters. -/
#generalize_control gen_le_refl ⟪Nat.le_refl 3, Nat.le_refl 5⟫ : ∀ x : Nat, x ≤ x

/-! Positive: the same tuple of values is one parameter. -/
#generalize_control gen_shared
    ⟪Nat.le_trans (Nat.le_refl 3) (Nat.le_refl 3), Nat.le_trans (Nat.le_refl 5) (Nat.le_refl 5)⟫ :
  ∀ x : Nat, x ≤ x

/-! Positive: a parameter's type is generalized with the same parameters (a type, then a value of
it). -/
#generalize_control gen_dependent ⟪@List.length_singleton Nat 1, @List.length_singleton Bool true⟫ :
  ∀ (α : Type) (a : α), [a].length = 1

/-! Positive: universe levels are generalized as level parameters. -/
#generalize_control gen_level ⟪@List.length_singleton.{0} Nat 1, @List.length_singleton.{1} Type Nat⟫ :
  ∀ (α : Type u_1) (a : α), [a].length = 1

/-! Positive: a term that uses the fragment's own binder is a function of it. -/
#generalize_control gen_pattern
    ⟪fun n : Nat => Nat.le_refl (n + 1), fun n : Nat => Nat.le_refl (n * 2)⟫ :
  ∀ (f : Nat → Nat) (n : Nat), f n ≤ f n

/-! Positive: hypotheses bound outside the fragment become parameters, their types generalized with
the values they share. -/
#generalize_control gen_outer (h₁ : 3 ≤ 4) (h₂ : 5 ≤ 6)
    ⟪Nat.le_trans h₁ (Nat.le_refl 4), Nat.le_trans h₂ (Nat.le_refl 6)⟫ :
  ∀ (a b : Nat), a ≤ b → a ≤ b

/-! Negative: terms with different heads keep nothing; the lemma would be an identity. -/
#generalize_trivial ⟪Nat.le_refl 3, Nat.zero_le 3⟫

/-- Negative: a statement the generalized proof does not prove is refused by the kernel. -/
def forgedRefused : MetaM Bool := do
  let l ← generalize #[mkApp (mkConst ``Nat.le_refl) (mkNatLit 3), mkApp (mkConst ``Nat.le_refl) (mkNatLit 5)]
  let forged := { l with type := ← mkArrow (mkConst ``Nat) (mkConst ``False) }
  try addLemma `gen_forged forged; return false catch _ => return true

/-- info: true -/
#guard_msgs in
#eval forgedRefused

end Mettapedia.Languages.Lean.Transport.GeneralizeControls
