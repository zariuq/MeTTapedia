import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax
import Mathlib.Data.Nat.BinaryRec

/-!
# Compact closed naturals in declaration syntax

Binary digits use the existing Nat.mul and Nat.succ operations. The syntax
contains one recursive numeral subtree per digit; it does not duplicate that
subtree for addition. Zero and one retain their constructor presentation.
The interpretation theorem checks the mathematical value of every encoding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.NaturalSyntax

open Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax (Term)

def zero : Term := .name "Nat.zero"
def successor (term : Term) : Term := .app (.name "Nat.succ") term
def two : Term := successor (successor zero)
def twice (term : Term) : Term := .app (.app (.name "Nat.mul") two) term
def digit (bit : Bool) (term : Term) : Term := if bit then successor (twice term) else twice term

def evaluate (environment : String → Option Nat) : Term → Option Nat
  | .name "Nat.zero" => some 0
  | .name name => environment name
  | .app (.name "Nat.succ") argument => (evaluate environment argument).map Nat.succ
  | .app (.app (.name "Nat.mul") left) right =>
      do return (← evaluate environment left) * (← evaluate environment right)
  | .app (.app (.name "Nat.add") left) right =>
      do return (← evaluate environment left) + (← evaluate environment right)
  | _ => none

def value : Term → Option Nat := evaluate (fun _ => none)

def checked : (n : Nat) → { term : Term // ∀ environment, evaluate environment term = some n } :=
  Nat.binaryRecFromOne ⟨zero, fun _ => rfl⟩ ⟨successor zero, fun _ => rfl⟩ fun bit n _ previous =>
    ⟨digit bit previous.val, by
      intro environment
      cases bit <;> simp [digit, twice, two, successor, zero, evaluate, previous.property, Nat.bit]⟩

def encode (n : Nat) : Term := (checked n).val

theorem evaluate_encode (environment : String → Option Nat) (n : Nat) :
    evaluate environment (encode n) = some n := (checked n).property environment

theorem value_encode (n : Nat) : value (encode n) = some n := evaluate_encode _ n

theorem offset_value (environment : String → Option Nat) (term : Term) (n offset : Nat)
    (given : evaluate environment term = some n) :
    evaluate environment (.app (.app (.name "Nat.add") term) (encode offset)) = some (n + offset) := by
  simp [evaluate, given, evaluate_encode]

theorem zero_unchanged : encode 0 = .name "Nat.zero" := rfl
theorem one_unchanged : encode 1 = .app (.name "Nat.succ") (.name "Nat.zero") := rfl

def nodes : Term → Nat
  | .name _ => 1
  | .app function argument => 1 + nodes function + nodes argument
  | .arrow domain codomain => 1 + nodes domain + nodes codomain
  | .pi _ domain codomain => 1 + nodes domain + nodes codomain
  | .project _ _ record => 1 + nodes record

/-- The Unicode scalar upper bound is compact rather than a million successors. -/
theorem unicode_bound_is_compact : nodes (encode 1114112) < 200 := by decide

/-- A compact decimal-sized bound still denotes its exact natural value. -/
theorem word_bound_has_exact_value : value (encode 4294967296) = some 4294967296 := value_encode _

end Mettapedia.Languages.Lean.Declarations.NaturalSyntax
