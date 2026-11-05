import Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping
import Mettapedia.Logic.ConstraintTypes.UnsharedParameters

/-!
# Every ground PeTTa value has a canonical type

The runtime gives each value a type without consulting any function
declaration:
- numbers, strings and booleans have their primitive types;
- a custom host value has its grounded type;
- an unannotated symbol is a `Symbol`, and a symbol with nominal declarations
  has each declared type;
- an expression has the structural tuple of its elements' types.

So every ground atom belongs to at least one proper type. Any membership
relation that contains these canonical facts therefore satisfies the
hypothesis of the unshared-parameter law, and an unshared parameter imposes no
check on a ground argument. A variable belongs to no closed type; an open value
is covered by its ground completions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.CanonicalTypes

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Proper type names of the canonical fragment. -/
inductive Name where
  | number | string | bool | symbol
  | grounded (typeName : String)
  | nominal (typeName : String)
  deriving DecidableEq

/-- The structural tuple type former, one per length. -/
inductive Former where
  | tuple (length : Nat)
  deriving DecidableEq

def typeArity : Former → Nat
  | .tuple length => length

abbrev PType := SymbolicTypes.Closed Name Former typeArity

/-- Canonical membership, given which nominal types each symbol is declared to have. -/
inductive Member (declared : String → String → Prop) : Atom → PType → Prop where
  | number (n : Int) : Member declared (.grounded (.int n)) (.closed .number)
  | string (s : String) : Member declared (.grounded (.string s)) (.closed .string)
  | bool (b : Bool) : Member declared (.grounded (.bool b)) (.closed .bool)
  | grounded (typeName data : String) :
      Member declared (.grounded (.custom typeName data)) (.closed (.grounded typeName))
  | symbol (s : String) (unannotated : ∀ typeName, ¬ declared s typeName) :
      Member declared (.symbol s) (.closed .symbol)
  | nominal (s typeName : String) (annotation : declared s typeName) :
      Member declared (.symbol s) (.closed (.nominal typeName))
  | tuple (elements : List Atom) (types : Fin elements.length → PType)
      (each : ∀ i, Member declared (elements.get i) (types i)) :
      Member declared (.expression elements) (.app (.tuple elements.length) types)

mutual
/-- An atom without variables. -/
def Ground : Atom → Prop
  | .var _ => False
  | .expression elements => GroundList elements
  | _ => True

def GroundList : List Atom → Prop
  | [] => True
  | atom :: rest => Ground atom ∧ GroundList rest
end

mutual
theorem ground_typed (declared : String → String → Prop) :
    (atom : Atom) → Ground atom → ∃ type, Member declared atom type
  | .symbol s, _ => by
      by_cases annotated : ∃ typeName, declared s typeName
      · obtain ⟨typeName, annotation⟩ := annotated
        exact ⟨_, .nominal s typeName annotation⟩
      · exact ⟨_, .symbol s (fun typeName annotation => annotated ⟨typeName, annotation⟩)⟩
  | .var _, ground => False.elim ground
  | .grounded (.int n), _ => ⟨_, .number n⟩
  | .grounded (.string s), _ => ⟨_, .string s⟩
  | .grounded (.bool b), _ => ⟨_, .bool b⟩
  | .grounded (.custom typeName data), _ => ⟨_, .grounded typeName data⟩
  | .expression elements, ground => by
      obtain ⟨types, each⟩ := ground_typed_list declared elements ground
      exact ⟨_, .tuple elements types each⟩

theorem ground_typed_list (declared : String → String → Prop) :
    (elements : List Atom) → GroundList elements →
      ∃ types : Fin elements.length → PType, ∀ i, Member declared (elements.get i) (types i)
  | [], _ => ⟨Fin.elim0, fun i => i.elim0⟩
  | atom :: rest, ⟨ground, groundRest⟩ => by
      obtain ⟨type, member⟩ := ground_typed declared atom ground
      obtain ⟨types, each⟩ := ground_typed_list declared rest groundRest
      refine ⟨Fin.cons type types, fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using member
      · simpa using each j
end

theorem variable_untyped (declared : String → String → Prop) (name : String) (type : PType) :
    ¬ Member declared (.var name) type := nofun

open CheckingPatterns PatternContracts UnsharedParameters

/-- The unshared-parameter law holds for every PeTTa model whose membership
contains the canonical facts: a parameter that is the whole check of one input
and occurs nowhere else imposes no check on a ground argument. -/
theorem waive_entry_iff_on_ground {Kind : Type} {sig : CheckingPatterns.Signature Kind}
    {Context P : Type} [DecidableEq P] {valueKind : Kind} {n : Nat}
    (model : Model sig (fun _ => Atom) Context Name Former typeArity)
    (declared : Context → String → String → Prop)
    (canonical : ∀ context atom type, Member (declared context) atom type →
      model.member (s := valueKind) context atom type)
    (context : Context) (arguments : Fin n → Atom)
    (declaration : Declaration sig P Name Former typeArity valueKind n) (slot : Fin n) (parameter : P)
    (unshared : UnsharedInput declaration slot parameter) (ground : Ground (arguments slot)) :
    Entry model context arguments (waive declaration slot) ↔ Entry model context arguments declaration := by
  obtain ⟨type, member⟩ := ground_typed (declared context) (arguments slot) ground
  exact waive_entry_iff model context arguments declaration slot parameter unshared
    ⟨type, canonical context (arguments slot) type member⟩

theorem waive_joint_iff_on_ground {Kind : Type} {sig : CheckingPatterns.Signature Kind}
    {Context P : Type} [DecidableEq P] {valueKind : Kind} {n : Nat}
    (model : Model sig (fun _ => Atom) Context Name Former typeArity)
    (declared : Context → String → String → Prop)
    (canonical : ∀ context atom type, Member (declared context) atom type →
      model.member (s := valueKind) context atom type)
    (before after : Context) (arguments : Fin n → Atom) (value : Atom)
    (declaration : Declaration sig P Name Former typeArity valueKind n) (slot : Fin n) (parameter : P)
    (unshared : Unshared declaration slot parameter) (ground : Ground (arguments slot)) :
    Joint model before after arguments value (waive declaration slot) ↔
      Joint model before after arguments value declaration := by
  obtain ⟨type, member⟩ := ground_typed (declared before) (arguments slot) ground
  exact waive_joint_iff model before after arguments value declaration slot parameter unshared
    ⟨type, canonical before (arguments slot) type member⟩

end Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.CanonicalTypes
