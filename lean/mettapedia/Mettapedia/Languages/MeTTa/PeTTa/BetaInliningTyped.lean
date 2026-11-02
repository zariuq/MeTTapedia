import Mettapedia.Languages.MeTTa.PeTTa.TypedCallLowering

/-!
# A typed call is not its body

With a type declaration, PeTTa's call protocol (`TypedCallLowering.sourceCall`) runs an
activation, each argument's raw, translated or checked action, the body (held when a
signature of the family has a literal `Atom` codomain), the result guard for a checked
codomain, and publication; a family of signatures is a list of ordered alternatives
(`TypedCallLowering.sourceFamily`). Inlining the body alone drops these actions.

Controls on services that answer once per success:

* a failing argument guard: the typed call has no answer, the body alone one
  (`guard_drops_answer`);
* two signatures for one function: the body runs once per signature
  (`two_signatures_answer_twice`);
* a literal `Atom` codomain holds the body (`atom_codomain_holds_body`).

Inlining the emitted actions instead of the body alone is the source protocol, by
`TypedCallLowering.compileCall_exact` and `TypedCallLowering.compileFamily_exact`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BetaInliningTyped

open Mettapedia.Machines.OrderedProtocol
open TypedCallLowering
open CallGuardOptimization
open OSLFCore (Atom)

/-- The answers of a protocol run whose successes each answer `1`. -/
def answers (kernel : Kernel Unit Unit Unit Unit (List Nat)) : List Nat :=
  kernel () (fun _ pending world => 1 :: pending world) (fun _ => []) (fun _ => [])
    (fun _ _ => []) (fun _ _ => []) ()

/-- Every action succeeds once. -/
def passing : Services Unit Unit Unit Unit (List Nat) := fun _ => done

/-- Every action succeeds once, except the guard of the first argument, which fails. -/
def failingGuard : Services Unit Unit Unit Unit (List Nat)
  | .guardArgument 1 => fun _ _ pending _ _ _ world => pending world
  | _ => done

/-- `(-> Number %Undefined%)`: a checked domain and an unchecked codomain. -/
def numberDomain : Signature := ⟨[.symbol "Number"], .symbol "%Undefined%"⟩

/-- `(-> Number Atom)`: a checked domain and a literal `Atom` codomain. -/
def atomCodomain : Signature := ⟨[.symbol "Number"], .symbol "Atom"⟩

theorem number_domain_is_checked : demand (.symbol "Number") = .checked := by decide

/-- A failing argument guard: the typed call has no answer, the body alone one. -/
theorem guard_drops_answer :
    answers (sourceCall failingGuard (holdBody [numberDomain]) numberDomain) = [] ∧
      answers (failingGuard (.body (holdBody [numberDomain]))) = [1] := by
  constructor <;> decide

/-- Two signatures for one function: the body runs once per signature, so the typed call
answers twice where the body alone answers once. -/
theorem two_signatures_answer_twice :
    answers (sourceFamily passing [numberDomain, atomCodomain]) = [1, 1] ∧
      answers (passing (.body false)) = [1] := by
  constructor <;> decide

/-- A literal `Atom` codomain holds the body of every signature of the family. -/
theorem atom_codomain_holds_body :
    holdBody [numberDomain, atomCodomain] = true ∧
      compileCall (holdBody [numberDomain, atomCodomain]) numberDomain =
        [.activate numberDomain, .translate 1, .guardArgument 1, .body true, .publish] := by
  constructor <;> decide

end Mettapedia.Languages.MeTTa.PeTTa.BetaInliningTyped
