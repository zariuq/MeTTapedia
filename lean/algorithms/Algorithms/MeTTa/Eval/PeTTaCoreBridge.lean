import Algorithms.MeTTa.Eval.Eval
import Algorithms.MeTTa.Simple.Semantics.PeTTaCore

/-! # LeanPeTTa ↔ PeTTaCore Bridge

Instantiates `PeTTaCore.Interface` for the verified evaluator,
connecting it to the existing PeTTa specification infrastructure.
-/

namespace Algorithms.MeTTa.Eval

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match hiding applyBindings
open Algorithms.MeTTa.Simple.Semantics.PeTTaCore (Interface Preservation)

/-- Instantiate `PeTTaCore.Interface` for the verified evaluator. -/
def evalPeTTaInterface (maxFuel : Nat) : Interface Session where
  eval := fun s t =>
    let out := evalWith maxFuel s [] t
    (out.s, out.results.map ResultBind.term)
  evalDeterministic := fun s fuel t =>
    let out := evalWith fuel s [] t
    (out.s, (out.results.head?.map ResultBind.term).getD t)
  evalCallableApply := fun s fn args =>
    let call := match fn with
      | .apply name fnArgs => Pattern.apply name (fnArgs ++ args)
      | _ => Pattern.apply "" (fn :: args)
    let out := evalWith maxFuel s [] call
    (out.s, out.results.map ResultBind.term)
  applyBindings := applyBinds
  matchPattern := matchPattern
  findBindingsInSpace := fun s pat _tmpl =>
    s.space.flatMap (matchPattern pat)
  dedupPatterns := List.eraseDups
  typeCandidates := fun s x =>
    s.space.filterMap (fun atom =>
      match atom with
      | .apply ":" [name, ty] => if name == x then some ty else none
      | _ => none)

/-- The verified evaluator preserves any session predicate that is
    closed under `evalWith` at any fuel level. -/
theorem evalPeTTaInterface_preserves (maxFuel : Nat) (P : Session → Prop)
    (hEval : ∀ fuel s binds t, P s → P (evalWith fuel s binds t).s) :
    Preservation (evalPeTTaInterface maxFuel) P where
  eval_preserves := by
    intro s term s' out h hP
    simp only [evalPeTTaInterface] at h
    have := hEval maxFuel s [] term hP
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact this
  evalDeterministic_preserves := by
    intro s fuel term s' out h hP
    simp only [evalPeTTaInterface] at h
    have := hEval fuel s [] term hP
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact this
  evalCallableApply_preserves := by
    intro s fn args s' out h hP
    unfold evalPeTTaInterface at h
    cases fn with
    | apply name fnArgs =>
      simp at h; exact h.1 ▸ hEval maxFuel s [] _ hP
    | fvar x =>
      simp at h; exact h.1 ▸ hEval maxFuel s [] _ hP
    | bvar n =>
      simp at h; exact h.1 ▸ hEval maxFuel s [] _ hP
    | lambda body =>
      simp at h; exact h.1 ▸ hEval maxFuel s [] _ hP
    | multiLambda n body =>
      simp at h; exact h.1 ▸ hEval maxFuel s [] _ hP
    | subst body repl =>
      simp at h; exact h.1 ▸ hEval maxFuel s [] _ hP
    | collection ct elems rest =>
      simp at h; exact h.1 ▸ hEval maxFuel s [] _ hP

end Algorithms.MeTTa.Eval
