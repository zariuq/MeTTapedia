import Mettapedia.GSLT.Parsing.GrammarConstructorActions
import Mettapedia.GSLT.Parsing.ExactDecimalLexeme
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Typed construction of ordinary MeTTa atoms

This target algebra constructs the existing host atom datatype. Its auxiliary
sorts are ordered argument sequences, text, and exact integers; they are not
another public formula representation. A generated interpretation may use
`GrammarConstructorActions.Templates rules algebra` and open routes with exact
heterogeneous child contexts.

Application accepts an arbitrary atom as its head. Neither application nor
expression construction evaluates that atom, flattens it, or treats a symbol
as a host call. Sequence append retains order and multiplicity. Source values
here are already decoded values: lexical admission, object-language binding,
and a language's choice of interpretation are separate obligations.

The operational theorem instantiates the existing many-sorted evaluation
GSLT and its OSLF result type. No correspondence with C execution or complete
language interpretation is asserted in this module.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.MeTTaAtomConstruction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySortedEvaluation
open Mettapedia.OSLF.Framework.PathTypeSynthesis

/-- Sorts of construction inputs and intermediate results. -/
inductive Kind where
  | atom
  | atoms
  | text
  | integer
  | integerLexeme
  | rationalLexeme
  deriving DecidableEq, Repr

/-- All observable values use existing host and standard datatypes. -/
abbrev Value : Kind → Type
  | .atom => Atom
  | .atoms => List Atom
  | .text => String
  | .integer => Int
  | .integerLexeme => ExactDecimalLexeme.Integer
  | .rationalLexeme => ExactDecimalLexeme.Rational

/-- A typed structural signature, independent of any source grammar's labels.
There is no operation for unchecked indexing or implicit evaluation. -/
inductive Operation : List Kind → Kind → Type where
  | symbol : Operation [.text] .atom
  | string : Operation [.text] .atom
  | integer : Operation [.integer] .atom
  | integerValue : Operation [.integerLexeme] .integer
  | rationalComponents : Operation [.rationalLexeme] .atoms
  | empty : Operation [] .atoms
  | cons : Operation [.atom, .atoms] .atoms
  | append : Operation [.atoms, .atoms] .atoms
  | expression : Operation [.atoms] .atom
  | application : Operation [.atom, .atoms] .atom
  | textAppend : Operation [.text, .text] .text

/-- Total evaluation takes exactly the arguments declared by the operation. -/
def interpretOperation : {inputs : List Kind} → {output : Kind} →
    Operation inputs output → FamilyList Value inputs → Value output
  | _, _, .symbol, .cons text .nil => .symbol text
  | _, _, .string, .cons text .nil => .grounded (.string text)
  | _, _, .integer, .cons integer .nil => .grounded (.int integer)
  | _, _, .integerValue, .cons lexeme .nil => lexeme.value
  | _, _, .rationalComponents, .cons lexeme .nil =>
      [.grounded (.int lexeme.numerator), .grounded (.int lexeme.denominator)]
  | _, _, .empty, .nil => []
  | _, _, .cons, .cons head (.cons tail .nil) => head :: tail
  | _, _, .append, .cons left (.cons right .nil) => List.append left right
  | _, _, .expression, .cons atoms .nil => .expression atoms
  | _, _, .application, .cons head (.cons arguments .nil) =>
      .expression (head :: arguments)
  | _, _, .textAppend, .cons left (.cons right .nil) => String.append left right

/-- The construction algebra accepts decoded inputs and builds host values. -/
def algebra : ManySortedConstructionAlgebra where
  Kind := Kind
  Object := Value
  Source := Value
  Operation := Operation
  interpretSource := id
  interpretOperation := interpretOperation

/-- Open typed actions, directly usable by the grammar-indexed templates. -/
abbrev Action (context : List Kind) (result : Kind) :=
  OpenConstructionRoute algebra context result

/-- Elaborate the action before its values so the exact child sorts are known. -/
def Action.run {context : List Kind} {result : Kind}
    (action : Action context result) (values : FamilyList Value context) : Value result :=
  OpenConstructionRoute.evaluate algebra values action

/-- An application built from a head child and an ordered argument child. -/
def applicationAction : Action [.atom, .atoms] .atom :=
  .apply .application
    (.cons (.input .here) (.cons (.input (.there .here)) .nil))

/-- A sequence accumulator takes the earlier sequence before the later one. -/
def appendAction : Action [.atoms, .atoms] .atoms :=
  .apply .append
    (.cons (.input .here) (.cons (.input (.there .here)) .nil))

/-- Construct a symbol from exactly the text-valued child. -/
def symbolAction : Action [.text] .atom :=
  .apply .symbol (.cons (.input .here) .nil)

/-- Construct a host string, keeping it distinct from the same-spelled symbol. -/
def stringAction : Action [.text] .atom :=
  .apply .string (.cons (.input .here) .nil)

/-- Construct a native exact integer from a validated decimal lexeme. -/
def integerLexemeAction : Action [.integerLexeme] .atom :=
  .apply .integer (.cons
    (.apply .integerValue (.cons (.input .here) .nil)) .nil)

/-- Expose a validated rational's numerator and denominator in source order. -/
def rationalComponentsAction : Action [.rationalLexeme] .atoms :=
  .apply .rationalComponents (.cons (.input .here) .nil)

/-- Application preserves both the complete head and the ordered arguments. -/
theorem applicationAction_evaluates (head : Atom) (arguments : List Atom) :
    Action.run applicationAction (.cons head (.cons arguments .nil)) =
        Atom.expression (head :: arguments) := rfl

/-- Append preserves the entire earlier prefix and later suffix. -/
theorem appendAction_evaluates (left right : List Atom) :
    Action.run appendAction (.cons left (.cons right .nil)) = left ++ right := rfl

theorem appendAction_length (left right : List Atom) :
    (Action.run appendAction (.cons left (.cons right .nil))).length =
        left.length + right.length := by
  simp only [appendAction_evaluates, List.length_append]

/-- A constructor-only operation cannot silently swap its two children. -/
theorem appendAction_order (first second : Atom) (different : first ≠ second) :
    Action.run appendAction (.cons [first] (.cons [second] .nil)) ≠ [second, first] := by
  intro equality
  change [first, second] = [second, first] at equality
  exact different (List.cons.inj equality).1

/-- In particular, equal occurrences are retained twice rather than deduplicated. -/
theorem appendAction_multiplicity (value : Atom) :
    Action.run appendAction (.cons [value] (.cons [value] .nil)) = [value, value] := rfl

/-- The application constructor is injective in both its head and arguments. -/
theorem applicationAction_injective
    (head otherHead : Atom) (arguments otherArguments : List Atom) :
    Action.run applicationAction (.cons head (.cons arguments .nil)) =
      Action.run applicationAction (.cons otherHead (.cons otherArguments .nil)) ↔
      head = otherHead ∧ arguments = otherArguments := by
  simp only [applicationAction_evaluates, Atom.expression.injEq, List.cons.injEq]

/-- Expression-headed application is not silently flattened into its head. -/
theorem nested_head_not_flattened (head argument : Atom) :
    Action.run applicationAction
        (.cons (Atom.expression [head]) (.cons [argument] .nil)) ≠
      Atom.expression [head, argument] := by
  intro equality
  have impossible : Atom.expression [head] = head := by
    simpa only [applicationAction_evaluates, Atom.expression.injEq,
      List.cons.injEq, and_true] using equality
  have sizes := congrArg sizeOf impossible
  simp at sizes
  omega

/-- Symbols and strings never become equal merely by sharing text. -/
theorem symbol_string_distinct (symbolText stringText : String) :
    Action.run symbolAction (.cons symbolText .nil) ≠
      Action.run stringAction (.cons stringText .nil) := by
  intro equality
  cases equality

/-- Exact integers retain their value, without conversion through floating point. -/
theorem integer_injective (left right : Int) :
    interpretOperation .integer (.cons left .nil) =
      interpretOperation .integer (.cons right .nil) ↔ left = right := by
  simp only [interpretOperation, Atom.grounded.injEq, GroundedValue.int.injEq]

theorem integerLexemeAction_evaluates (lexeme : ExactDecimalLexeme.Integer) :
    Action.run integerLexemeAction (.cons lexeme .nil) =
      .grounded (.int lexeme.value) := rfl

theorem rationalComponentsAction_evaluates
    (lexeme : ExactDecimalLexeme.Rational) :
    Action.run rationalComponentsAction (.cons lexeme .nil) =
      [.grounded (.int lexeme.numerator), .grounded (.int lexeme.denominator)] := rfl

/-- Positional child access cannot manufacture an atom from a text-only context. -/
theorem no_atom_position_in_text :
    ¬ Nonempty (ConstructionVariable [Kind.text] Kind.atom) := by
  rintro ⟨position⟩
  cases position with
  | there impossible => cases impossible

/-- OSLF result membership describes the operational construction computation,
not just membership in the inert atom carrier. -/
theorem result_native_iff {kind : Kind}
    (route : ConstructionTree algebra kind) (value : Value kind) :
    (pathOSLF (evaluationGSLT algebra kind)).satisfies route
      (resultNativeType algebra value).pred ↔ algebra.evaluate route = value :=
  satisfies_result_iff algebra route value

namespace Examples

/-- Build `(f (g x))` from three open, atom-valued children. -/
def nestedApplication : Action [.atom, .atom, .atom] .atom :=
  .apply .application
    (.cons (.input .here)
      (.cons
        (.apply .cons
          (.cons
            (.apply .application
              (.cons (.input (.there .here))
                (.cons
                  (.apply .cons
                    (.cons (.input (.there (.there .here)))
                      (.cons (.apply .empty .nil) .nil))) .nil)))
            (.cons (.apply .empty .nil) .nil))) .nil))

/-- Closing a generated action uses the existing typed graft operation. -/
def nestedRoute : ConstructionTree algebra .atom :=
  OpenConstructionRoute.graft algebra nestedApplication
    (.cons (.source (.symbol "f"))
      (.cons (.source (.symbol "g")) (.cons (.source (.symbol "x")) .nil)))

theorem nestedRoute_value :
    algebra.evaluate nestedRoute =
      Atom.expression [.symbol "f", .expression [.symbol "g", .symbol "x"]] := rfl

theorem nestedRoute_native :
    (pathOSLF (evaluationGSLT algebra .atom)).satisfies nestedRoute
      (resultNativeType algebra (kind := .atom)
        (Atom.expression [.symbol "f", .expression [.symbol "g", .symbol "x"]])).pred :=
  (result_native_iff nestedRoute _).mpr nestedRoute_value

/-- A different application tree is not licensed by the same native evidence. -/
theorem nestedRoute_wrong_native :
    ¬ (pathOSLF (evaluationGSLT algebra .atom)).satisfies nestedRoute
      (resultNativeType algebra (kind := .atom)
        (Atom.expression [.expression [.symbol "f", .symbol "g"], .symbol "x"])).pred := by
  rw [result_native_iff, nestedRoute_value]
  intro equality
  cases equality

end Examples

#print axioms applicationAction_injective
#print axioms appendAction_order
#print axioms Examples.nestedRoute_native
#print axioms Examples.nestedRoute_wrong_native

end Mettapedia.GSLT.Parsing.MeTTaAtomConstruction
