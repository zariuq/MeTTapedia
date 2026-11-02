import Mettapedia.Languages.Maude.ConditionalMaxNormalization
import Mettapedia.Languages.Maude.EquationalInterpretation

/-! The BOOL prelude instantiated at the Nat and Bool sorts of conditional
max. Boolean-ring equations and AC attributes remain explicit. Polymorphic
branch and equality symbols have separate declaration identities per sort;
equality hooks compare constructor normal forms, not an assumed equivalence.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude

abbrev Value := SemanticValue

def binary (label : String) (left right : Term) : Term := .app label [left, right]
def unary (label : String) (source : Term) : Term := .app label [source]
def branch (sort : String) (guard first second : Term) : Term :=
  .app ("BOOL.if." ++ sort) [guard, first, second]

def booleanBinary (id name : String) (ac : Bool := false) : Operator :=
  ⟨id, name, ["Bool", "Bool"], "Bool", {associative := ac, commutative := ac}⟩

def extraOperators : List Operator := [
  booleanBinary "BOOL.and" "_and_" true,
  booleanBinary "BOOL.or" "_or_" true,
  booleanBinary "BOOL.xor" "_xor_" true,
  ⟨"BOOL.not", "not_", ["Bool"], "Bool", {}⟩,
  booleanBinary "BOOL.implies" "_implies_",
  ⟨"BOOL.if.Nat", "if_then_else_fi", ["Bool", "Nat", "Nat"], "Nat", {}⟩,
  ⟨"BOOL.if.Bool", "if_then_else_fi", ["Bool", "Bool", "Bool"], "Bool", {}⟩,
  ⟨"BOOL.eq.Nat", "_==_", ["Nat", "Nat"], "Bool", {}⟩,
  booleanBinary "BOOL.eq.Bool" "_==_",
  ⟨"BOOL.ne.Nat", "_=/=_", ["Nat", "Nat"], "Bool", {}⟩,
  booleanBinary "BOOL.ne.Bool" "_=/=_"]

def signature : Signature :=
  ⟨Examples.conditional.signature.sorts, Examples.conditional.signature.operators ++ extraOperators⟩

def a : Term := .var "A"
def b : Term := .var "B"
def c : Term := .var "C"
def and (left right : Term) := binary "BOOL.and" left right
def xor (left right : Term) := binary "BOOL.xor" left right
def not (source : Term) := unary "BOOL.not" source

def booleanRows : List Row :=
  let formals :=  [("A", "Bool"), ("B", "Bool"), ("C", "Bool")]
  [⟨"BOOL.and-true", formals, [], and truth a, a⟩,
   ⟨"BOOL.and-false", formals, [], and falsehood a, falsehood⟩,
   ⟨"BOOL.and-idempotent", formals, [], and a a, a⟩,
   ⟨"BOOL.xor-false", formals, [], xor falsehood a, a⟩,
   ⟨"BOOL.xor-cancel", formals, [], xor a a, falsehood⟩,
   ⟨"BOOL.and-distributes", formals, [], and a (xor b c), xor (and a b) (and a c)⟩,
   ⟨"BOOL.not", formals, [], not a, xor a truth⟩,
   ⟨"BOOL.or", formals, [], binary "BOOL.or" a b, xor (xor (and a b) a) b⟩,
   ⟨"BOOL.implies", formals, [], binary "BOOL.implies" a b, not (xor a (and a b))⟩]

def branchRows (sort : String) : List Row :=
  [⟨"BOOL.if-true." ++ sort, [("A", sort), ("B", sort)], [], branch sort truth a b, a⟩,
   ⟨"BOOL.if-false." ++ sort, [("A", sort), ("B", sort)], [], branch sort falsehood a b, b⟩]

def theory : Theory :=
  ⟨"GOLD-MAX+BOOL", signature,
    Examples.conditional.equations ++ booleanRows ++ branchRows "Nat" ++ branchRows "Bool", []⟩

def finish (label : String) (arguments : List (Option Value)) : Option Value :=
  match label, arguments with
  | "BOOL.and", [some (.boolean first), some (.boolean second)] => some (.boolean (first && second))
  | "BOOL.or", [some (.boolean first), some (.boolean second)] => some (.boolean (first || second))
  | "BOOL.xor", [some (.boolean first), some (.boolean second)] => some (.boolean (Bool.xor first second))
  | "BOOL.not", [some (.boolean value)] => some (.boolean (!value))
  | "BOOL.implies", [some (.boolean first), some (.boolean second)] => some (.boolean (!first || second))
  | "BOOL.if.Nat", [some (.boolean guard), some (.natural first), some (.natural second)] =>
      some (.natural (if guard then first else second))
  | "BOOL.if.Bool", [some (.boolean guard), some (.boolean first), some (.boolean second)] =>
      some (.boolean (if guard then first else second))
  | "BOOL.eq.Nat", [some (.natural first), some (.natural second)] => some (.boolean (decide (first = second)))
  | "BOOL.eq.Bool", [some (.boolean first), some (.boolean second)] => some (.boolean (decide (first = second)))
  | "BOOL.ne.Nat", [some (.natural first), some (.natural second)] => some (.boolean (decide (first ≠ second)))
  | "BOOL.ne.Bool", [some (.boolean first), some (.boolean second)] => some (.boolean (decide (first ≠ second)))
  | _, _ => finishValue label arguments

private theorem finish_sorted (declaration : Operator) (member : declaration ∈ signature.operators)
    (arguments : List (Option Value)) (typed : List.Forall₂ FitsSort arguments declaration.arguments) :
    FitsSort (finish declaration.id arguments) declaration.result := by
  rcases List.mem_append.mp member with original | imported
  · rcases operators original with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases typed
    all_goals first
      | exact True.intro
      | rename_i first rest firstTyped restTyped
        obtain ⟨number, rfl⟩ := (fits_natural_iff _).mp firstTyped
        cases restTyped
        first
        | exact True.intro
        | rename_i second tail secondTyped tailTyped
          obtain ⟨other, rfl⟩ := (fits_natural_iff _).mp secondTyped
          cases tailTyped
          exact True.intro
  · simp only [extraOperators, List.mem_cons, List.not_mem_nil, or_false] at imported
    rcases imported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases typed with
    | cons firstTyped restTyped =>
      first
      | obtain ⟨first, rfl⟩ := (fits_boolean_iff _).mp firstTyped
        cases restTyped
        first
        | exact True.intro
        | rename_i second tail secondTyped tailTyped
          first
          | obtain ⟨second, rfl⟩ := (fits_boolean_iff _).mp secondTyped
            cases tailTyped
            first
            | exact True.intro
            | rename_i third rest thirdTyped restTyped
              obtain ⟨third, rfl⟩ := (fits_boolean_iff _).mp thirdTyped
              cases restTyped
              exact True.intro
          | obtain ⟨second, rfl⟩ := (fits_natural_iff _).mp secondTyped
            cases tailTyped with
            | cons thirdTyped restTyped =>
              obtain ⟨third, rfl⟩ := (fits_natural_iff _).mp thirdTyped
              cases restTyped
              exact True.intro
      | obtain ⟨first, rfl⟩ := (fits_natural_iff _).mp firstTyped
        cases restTyped with
        | cons secondTyped tailTyped =>
          obtain ⟨second, rfl⟩ := (fits_natural_iff _).mp secondTyped
          cases tailTyped
          exact True.intro

abbrev interpretation : EquationalInterpretation signature :=
  ⟨Value, finish, FitsSort, finish_sorted⟩

abbrev evaluate := interpretation.evaluate
abbrev Assigned := interpretation.SortedAssignment

theorem evaluate_var (assignment : String → Option Value) (name : String) :
    evaluate assignment (.var name) = assignment name :=
  EquationalInterpretation.evaluate.eq_1 interpretation assignment name

theorem evaluate_app (assignment : String → Option Value) (label : String) (arguments : List Term) :
    evaluate assignment (.app label arguments) = finish label (arguments.map (evaluate assignment)) :=
  EquationalInterpretation.evaluate.eq_2 interpretation assignment label arguments

end Mettapedia.Languages.Maude.ConditionalMax.BoolPrelude
