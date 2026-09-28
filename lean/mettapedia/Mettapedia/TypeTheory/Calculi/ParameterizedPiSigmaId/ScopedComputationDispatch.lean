import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationSemantics
import Mettapedia.TypeTheory.BindingDispatch

/-!
# Callable-head specialization in scoped dependent computations

This connects occurrence-role preservation to the existing native Pi/Sigma/Id
term and scoped computation grammar. Specialization rewrites operation heads,
never value terms or sequencing constructors. It commutes with the actual
capture-avoiding value substitution and preserves the contextual effect
program, not merely its final answers.

The handler is arbitrary. This proves no type formation judgment, no native
C correspondence, and no termination or completeness result for the full
language. The finite computation grammar and its native term scopes are the
existing ones, rather than a replacement Prime calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ScopedComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.BindingDispatch (Agrees)

abbrev CallHead := Mettapedia.TypeTheory.BindingDispatch.Head

variable {Head Name : Type} {n m : Nat}

namespace Code

def specializeHeads (known : Nat → Option Name) :
    {n : Nat} → Code Head (CallHead Name) n → Code Head (CallHead Name) n
  | _, .returnValue value => .returnValue value
  | _, .sequence first body => .sequence (first.specializeHeads known) (body.specializeHeads known)
  | _, .sequenceSigma first body =>
      .sequenceSigma (first.specializeHeads known) (body.specializeHeads known)
  | _, .choose left right => .choose (left.specializeHeads known) (right.specializeHeads known)
  | _, .call head argument => .call (head.specialize known) argument

theorem specializeHeads_idempotent (known : Nat → Option Name)
    (code : Code Head (CallHead Name) n) :
    (code.specializeHeads known).specializeHeads known = code.specializeHeads known := by
  induction code <;> simp_all only [specializeHeads,
    Mettapedia.TypeTheory.BindingDispatch.Head.specialize_idempotent]

theorem specializeHeads_substitute (known : Nat → Option Name)
    (environment : Sub Head n m) (code : Code Head (CallHead Name) n) :
    (code.substitute environment).specializeHeads known =
      (code.specializeHeads known).substitute environment := by
  induction code generalizing m <;> simp_all only [substitute, specializeHeads]

theorem specializeHeads_instantiate (known : Nat → Option Name)
    (argument : Tm Head n) (body : Code Head (CallHead Name) (n + 1)) :
    (body.instantiate argument).specializeHeads known =
      (body.specializeHeads known).instantiate argument :=
  specializeHeads_substitute known _ _

universe uState uIntent

/-- Specialization preserves the full effect program under every resolver
whose dynamic-name environment agrees with the specialization input. -/
theorem interpret_specializeHeads {State : Type uState} {Intent : Type uIntent}
    (handler : Name → Tm Head m → Program State (Tm Head m) Intent)
    (known : Nat → Option Name) (names : Nat → Name) (agrees : Agrees known names)
    (environment : Sub Head n m) (code : Code Head (CallHead Name) n) :
    interpret (fun head => handler (head.resolve names)) environment (code.specializeHeads known) =
      interpret (fun head => handler (head.resolve names)) environment code := by
  induction code with
  | returnValue value => rfl
  | sequence first body ihFirst ihBody =>
      simp only [specializeHeads, interpret, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody =>
      simp only [specializeHeads, interpret, ihFirst, ihBody]
  | choose left right ihLeft ihRight =>
      simp only [specializeHeads, interpret, ihLeft, ihRight]
  | call head argument =>
      simp only [specializeHeads, interpret,
        Mettapedia.TypeTheory.BindingDispatch.Head.resolve_specialize known names agrees]

/-- Keeping the effect program also keeps ordered worlds, selected states,
branch occurrence traces and deferred intents in the existing observer. -/
theorem worlds_specializeHeads {State : Type uState} {Intent : Type uIntent}
    (handler : Name → Tm Head m → Program State (Tm Head m) Intent)
    (known : Nat → Option Name) (names : Nat → Name) (agrees : Agrees known names)
    (environment : Sub Head n m) (code : Code Head (CallHead Name) n)
    (state : State) (branch : BranchTrace) :
    runWorldsAt
      (interpret (fun head => handler (head.resolve names)) environment
        (code.specializeHeads known)) state branch =
    runWorldsAt (interpret (fun head => handler (head.resolve names)) environment code) state branch := by
  rw [interpret_specializeHeads handler known names agrees]

end Code

namespace Controls

/-- An effectful user operation with the same spelling as binding syntax.
The state and intent changes make an accidental extra invocation observable. -/
def handler (name : String) (argument : Tm String 0) :
    Program Nat (Tm String 0) String :=
  if name = "let" then .write 42 (.intent "user-let" (.pure (.const `user)))
  else .pure argument

def names : Nat → String := fun _ => "let"
def known : Nat → Option String := fun _ => some "let"
def environment : Sub String 0 0 := Fin.elim0

def binding : Code String (CallHead String) 0 :=
  .sequence (.returnValue (.const `input)) (.returnValue (.var 0))

def invocation : Code String (CallHead String) 0 :=
  .call (.dynamic 0) (.const `input)

theorem binding_does_not_call_user_let :
    runWorldsAt (Code.interpret (fun head => handler (head.resolve names)) environment binding)
      3 [] = [{ branch := [], answer := .const `input, state := 3, intents := [] }] := rfl

theorem invocation_calls_user_let :
    runWorldsAt (Code.interpret (fun head => handler (head.resolve names)) environment invocation)
      3 [] = [{ branch := [], answer := .const `user, state := 42, intents := ["user-let"] }] := rfl

theorem specialization_keeps_user_effect :
    runWorldsAt
      (Code.interpret (fun head => handler (head.resolve names)) environment
        (invocation.specializeHeads known)) 3 [] =
      [{ branch := [], answer := .const `user, state := 42, intents := ["user-let"] }] := rfl

/-- Opening the sequence underneath a returned lambda must retain its own
new binder while replacing the captured outer variable. -/
def returnsClosure : Code String (CallHead String) 0 :=
  .sequence (.returnValue (.const `captured)) (.returnValue (.lam (.var 1)))

theorem returned_lambda_keeps_capture :
    runWorldsAt (Code.interpret (fun head => handler (head.resolve names)) environment returnsClosure)
      3 [] = [{ branch := [], answer := .lam (.const `captured), state := 3, intents := [] }] := rfl

end Controls

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ScopedComputation
