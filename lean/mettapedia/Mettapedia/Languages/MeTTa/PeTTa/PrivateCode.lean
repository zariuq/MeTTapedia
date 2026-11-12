import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec

/-!
# Translator-installed clauses outside the public atomspace

Generated lambda clauses are callable without being `&self` atoms. The
existing unifying machine now carries that private code inventory separately
from its store. Installation belongs to translation; ordinary execution and
every suspended prefix retain the same inventory. This module connects that
distinction to actual source transitions, without defining another evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)

@[simp] theorem codeEquations_empty (state : Effects.State) :
    codeEquations state [] = LiveEquations.liveEquations state := rfl

@[simp] theorem codeRegistry_empty (registry : Program) : codeRegistry registry [] = registry := by
  cases registry; rfl

@[simp] theorem runtimeRegistry_empty (registry : Program) (state : Effects.State) :
    runtimeRegistry registry state [] = LiveEquations.atState registry state := rfl

theorem codeEquations_mem (state : Effects.State) (code : List Equation) (equation : Equation) :
    equation ∈ codeEquations state code ↔
      equation ∈ code ∨ equation ∈ LiveEquations.liveEquations state := by
  simp [codeEquations]

/-- Installation changes callable metadata, not public store contents or
the current evaluation/continuation and I/O state. -/
def installCode (base : Configuration) (code : List Equation) : Configuration :=
  {base with privateCode := base.privateCode ++ code}

theorem installCode_keeps_public_state (base : Configuration) (code : List Equation) :
    (installCode base code).state = base.state ∧
      (installCode base code).control = base.control ∧
      (installCode base code).frames = base.frames ∧
      (installCode base code).input = base.input ∧
      (installCode base code).output = base.output := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem Transition.privateCode_eq {registry : Program} {before after : Configuration}
    (edge : Transition registry before after) : after.privateCode = before.privateCode := by
  cases edge <;> rfl

theorem transitions_keep_privateCode {registry : Program} {before after : Configuration}
    (path : Relation.ReflTransGen (Transition registry) before after) :
    after.privateCode = before.privateCode := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head edge _ ih => exact ih.trans edge.privateCode_eq

theorem step_keeps_privateCode {registry : Program} {before after : Configuration}
    (computed : step registry before = some after) : after.privateCode = before.privateCode :=
  (step_transition computed).privateCode_eq

theorem private_head_callable (state : Effects.State) (code : List Equation) (equation : Equation)
    (installed : equation ∈ code) : runtimeCallable state (.symbol equation.head) code = true := by
  have found : (codeEquations state code).any (·.head == equation.head) = true :=
    List.any_eq_true.mpr ⟨equation,(codeEquations_mem state code equation).mpr (Or.inl installed),by simp⟩
  simp [runtimeCallable,found]

/-- Private dispatch uses the ordinary equation selector and error scope.
There is no private implementation of matching, effects or body evaluation. -/
theorem private_dispatch_step (registry : Program) (base : Configuration)
    (bindings : Subst) (equation : Equation) (values : List Atom) (control : Control) (used : Nat)
    (installed : equation ∈ base.privateCode)
    (notNative : (Eval.ioHead equation.head || StdLib.known equation.head) = false)
    (selected : application (runtimeRegistry registry base.state base.privateCode)
      (codeEquations base.state base.privateCode) equation.head (values.map (resolve bindings))
      bindings base.uses = some (control,used)) :
    step registry {base with control := .dynamic bindings (.symbol equation.head) values} =
      some {base with control,uses := base.uses + used,frames := invocationFrames control base.frames} := by
  apply transition_step
  apply Transition.dynamic_equations rfl rfl notNative
  · exact List.any_eq_true.mpr ⟨equation,
      (codeEquations_mem base.state base.privateCode equation).mpr (Or.inl installed),by simp⟩
  · exact selected

/-- A request prepared with private code shares the ordinary initial store,
bindings and use counter. The caller retains the inventory across requests. -/
def startWithCode (code : List Equation) (state : Effects.State) (expression : Atom) : Configuration :=
  {start state expression with privateCode := code}

@[simp] theorem startWithCode_empty (state : Effects.State) (expression : Atom) :
    startWithCode [] state expression = start state expression := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
