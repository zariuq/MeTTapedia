import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarSource

/-!
# Program evidence required by a scalar certificate

Revalidation checks the primitive and inert-symbol heads actually used by
the extracted expression. A change to an unrelated equation need not discard
the certificate. This is a checked semantic dependency test, not a proof that
a particular native revision counter implements it. Live tuple-head checks
belong to the body evaluator and are not erased by this scalar cache law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarDependencies

open Mettapedia.Machines.TypedScalar
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ScalarSource

inductive Need
  | primitive (head : String)
  | inert (head : String)
  deriving DecidableEq

def Need.Holds (program : SpaceSemantics.Program) : Need → Prop
  | .primitive head => Clear program head
  | .inert head => Inert program head

instance (program : SpaceSemantics.Program) (need : Need) : Decidable (need.Holds program) :=
  match need with
  | .primitive _ => inferInstanceAs (Decidable (Clear _ _))
  | .inert _ => inferInstanceAs (Decidable (Inert _ _))

def needs {Slot : Type} : {kind : Kind} → Expr Slot kind → List Need
  | _, .literal (.integer _) | _, .boolean _ | _, .read _ => []
  | _, .literal (.symbol name) => [.inert name]
  | _, .binary op left right => .primitive op.name :: (needs left ++ needs right)
  | _, .branch test yes no => .primitive "if" :: (needs test ++ needs yes ++ needs no)

def Supported {Slot : Type} {kind : Kind} (program : SpaceSemantics.Program) (expression : Expr Slot kind) : Prop :=
  ∀ need ∈ needs expression, need.Holds program

theorem supported_of_elaborated {Slot : Type} {program : SpaceSemantics.Program} {environment : Environment Slot}
    {source : Atom} {kind : Kind} {expression : Expr Slot kind}
    (elaborated : Elaborates program environment source expression) : Supported program expression := by
  induction elaborated with
  | integer => simp [Supported, needs]
  | boolean => simp [Supported, needs]
  | bound => simp [Supported, needs]
  | symbol name inert => simpa [Supported, needs, Need.Holds] using inert
  | binary op clear _ _ ihl ihr => simpa [Supported, needs, Need.Holds, or_imp, forall_and] using And.intro clear (And.intro ihl ihr)
  | branch clear _ _ _ iht ihy ihn => simpa [Supported, needs, Need.Holds, or_imp, forall_and, and_assoc] using And.intro clear (And.intro iht (And.intro ihy ihn))

theorem transport {Slot : Type} {first : SpaceSemantics.Program} {environment : Environment Slot}
    {source : Atom} {kind : Kind} {expression : Expr Slot kind}
    (elaborated : Elaborates first environment source expression) (second : SpaceSemantics.Program)
    (supported : Supported second expression) : Elaborates second environment source expression := by
  induction elaborated with
  | integer value => exact .integer value
  | boolean value => exact .boolean value
  | bound name slot found => exact .bound name slot found
  | symbol name _ => exact .symbol name (supported (.inert name) (by simp [needs]))
  | binary op _ left right ihl ihr =>
      apply Elaborates.binary op (supported (.primitive op.name) (by simp [needs]))
      · exact ihl (fun need member => supported need (by simp [needs, member]))
      · exact ihr (fun need member => supported need (by simp [needs, member]))
  | branch _ test yes no iht ihy ihn =>
      apply Elaborates.branch (supported (.primitive "if") (by simp [needs]))
      · exact iht (fun need member => supported need (by simp [needs, member]))
      · exact ihy (fun need member => supported need (by simp [needs, member]))
      · exact ihn (fun need member => supported need (by simp [needs, member]))

def check {Slot : Type} {kind : Kind} (program : SpaceSemantics.Program) (expression : Expr Slot kind) : Bool :=
  (needs expression).all (fun need => decide (need.Holds program))

theorem check_iff {Slot : Type} {kind : Kind} (program : SpaceSemantics.Program) (expression : Expr Slot kind) :
    check program expression = true ↔ Supported program expression := by
  simp [check, Supported]

def revalidate {Slot : Type} {first : SpaceSemantics.Program} {environment : Environment Slot}
    {source : Atom} (certificate : Extracted first environment source) (second : SpaceSemantics.Program) :
    Option (Extracted second environment source) :=
  if accepted : check second certificate.expression then
    some ⟨certificate.kind, certificate.expression,
      transport certificate.derivation second ((check_iff second certificate.expression).mp accepted)⟩
  else none

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarDependencies
