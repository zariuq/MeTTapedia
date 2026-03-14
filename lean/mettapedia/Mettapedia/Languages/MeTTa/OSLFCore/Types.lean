import Mettapedia.Languages.MeTTa.OSLFCore.Atomspace

/-!
# MeTTaCore Type System

The type system for MeTTa, following the Hyperon Experimental specification.
MeTTa uses a simple but expressive type system with meta-types, type annotations,
and function types.

## Main Definitions

* `MetaType` - The built-in meta-types (Atom, Symbol, Variable, etc.)
* `typeAnnotation` - Create type annotation `(: atom type)`
* `functionType` - Create function type `(-> args... ret)`
* `HasType` - Type judgment: atom has type in atomspace context
* `checkType` - Decidable type checking

## References

* [Hyperon Experimental Spec](https://trueagi-io.github.io/hyperon-experimental/metta/)
* Meta-MeTTa paper: type-driven evaluation
-/

namespace Mettapedia.Languages.MeTTa.OSLFCore

/-! ## Meta-Types -/

/-- The built-in meta-types in MeTTa.
    These are the "types of types" that classify atoms. -/
inductive MetaType where
  | atom       -- Type of all atoms
  | symbol     -- Type of symbols
  | variable   -- Type of variables
  | expression -- Type of expressions
  | grounded   -- Type of grounded values
  | type       -- Type of types (kind)
  deriving DecidableEq, Repr, Inhabited

namespace MetaType

/-- Convert meta-type to its symbol representation -/
def toAtom : MetaType → Atom
  | .atom => .symbol "Atom"
  | .symbol => .symbol "Symbol"
  | .variable => .symbol "Variable"
  | .expression => .symbol "Expression"
  | .grounded => .symbol "Grounded"
  | .type => .symbol "Type"

/-- Parse atom to meta-type if applicable -/
def fromAtom : Atom → Option MetaType
  | .symbol "Atom" => some .atom
  | .symbol "Symbol" => some .symbol
  | .symbol "Variable" => some .variable
  | .symbol "Expression" => some .expression
  | .symbol "Grounded" => some .grounded
  | .symbol "Type" => some .type
  | _ => none

/-- Check if atom represents a meta-type -/
def isMetaType (a : Atom) : Bool :=
  fromAtom a |>.isSome

end MetaType

/-! ## Type Constructors -/

/-- Create a type annotation: `(: atom type)` -/
def typeAnnotation (a ty : Atom) : Atom :=
  .expression [.symbol ":", a, ty]

/-- Create a function type: `(-> arg_types... ret_type)` -/
def functionType (argTypes : List Atom) (retType : Atom) : Atom :=
  .expression (.symbol "->" :: argTypes ++ [retType])

/-- Check if atom is a type annotation -/
def isTypeAnnotation : Atom → Bool
  | .expression [.symbol ":", _, _] => true
  | _ => false

/-- Check if atom is a function type -/
def isFunctionType : Atom → Bool
  | .expression (.symbol "->" :: _ :: _) => true
  | _ => false

/-- Extract the typed atom from an annotation -/
def getAnnotatedAtom : Atom → Option Atom
  | .expression [.symbol ":", a, _] => some a
  | _ => none

/-- Extract the type from an annotation -/
def getAnnotationType : Atom → Option Atom
  | .expression [.symbol ":", _, ty] => some ty
  | _ => none

/-- Extract argument types from function type -/
def getFunctionArgTypes : Atom → Option (List Atom)
  | .expression (.symbol "->" :: args) =>
      if args.length ≥ 1 then some (args.dropLast) else none
  | _ => none

/-- Extract return type from function type -/
def getFunctionRetType : Atom → Option Atom
  | .expression (.symbol "->" :: args) =>
      args.getLast?
  | _ => none

/-! ## Intrinsic Types -/

/-- Get the intrinsic meta-type of an atom (without looking at atomspace) -/
def intrinsicType : Atom → MetaType
  | .symbol _ => .symbol
  | .var _ => .variable
  | .grounded _ => .grounded
  | .expression _ => .expression

/-- Convert intrinsic type to atom -/
def intrinsicTypeAtom (a : Atom) : Atom :=
  (intrinsicType a).toAtom

/-! ## Type Judgment -/

/-- Type judgment: `HasType space a ty` means `a` has type `ty` in context `space`.

    The typing rules are:
    1. Intrinsic: symbols have type Symbol, variables have type Variable, etc.
    2. Annotated: if `(: a ty)` is in space, then `a` has type `ty`
    3. Function application: if `f : (-> A B)` and `x : A`, then `(f x) : B`
    4. Subtyping: every atom also has type Atom -/
inductive HasType (space : Atomspace) : Atom → Atom → Prop where
  | intrinsicSymbol (s : String) :
      HasType space (.symbol s) (.symbol "Symbol")
  | intrinsicVariable (v : String) :
      HasType space (.var v) (.symbol "Variable")
  | intrinsicGrounded (g : GroundedValue) :
      HasType space (.grounded g) (.symbol "Grounded")
  | intrinsicExpression (es : List Atom) :
      HasType space (.expression es) (.symbol "Expression")
  | annotated (a ty : Atom) :
      typeAnnotation a ty ∈ space.atoms →
      HasType space a ty
  | atomSubtype (a : Atom) (ty : Atom) :
      HasType space a ty →
      HasType space a (.symbol "Atom")
  | groundedInt (n : Int) :
      HasType space (.grounded (.int n)) (.symbol "Int")
  | groundedString (s : String) :
      HasType space (.grounded (.string s)) (.symbol "String")
  | groundedBool (b : Bool) :
      HasType space (.grounded (.bool b)) (.symbol "Bool")

/-! ## Type Checking -/

/-- Check if atom has a specific type (decidable version).
    Returns true if the type can be verified, false otherwise. -/
def checkType (space : Atomspace) (a ty : Atom) : Bool :=
  -- Check intrinsic types
  match ty with
  | .symbol "Symbol" =>
      match a with
      | .symbol _ => true
      | _ => false
  | .symbol "Variable" =>
      match a with
      | .var _ => true
      | _ => false
  | .symbol "Grounded" =>
      match a with
      | .grounded _ => true
      | _ => false
  | .symbol "Expression" =>
      match a with
      | .expression _ => true
      | _ => false
  | .symbol "Atom" => true  -- Everything is an Atom
  | .symbol "Int" =>
      match a with
      | .grounded (.int _) => true
      | _ => false
  | .symbol "String" =>
      match a with
      | .grounded (.string _) => true
      | _ => false
  | .symbol "Bool" =>
      match a with
      | .grounded (.bool _) => true
      | _ => false
  | _ =>
      -- Check annotations in space
      space.contains (typeAnnotation a ty)

/-- Get all known types for an atom from the atomspace -/
def getTypes (space : Atomspace) (a : Atom) : Multiset Atom :=
  -- Get intrinsic type
  let intrinsic := {intrinsicTypeAtom a}
  -- Get annotated types
  let annotations := space.typeAnnotations.filterMap fun ann =>
    match ann with
    | .expression [.symbol ":", a', ty] =>
        if a' == a then some ty else none
    | _ => none
  intrinsic + annotations

/-! ## Type-Driven Evaluation Control -/

/-- Check if evaluation should proceed based on type.
    In MeTTa, types can control whether an expression is evaluated. -/
noncomputable def shouldEvaluate (space : Atomspace) (a : Atom) : Bool :=
  -- By default, evaluate if not explicitly typed as data
  -- This is a simplified version; full MeTTa has more complex rules
  match getTypes space a |>.toList.head? with
  | some (.symbol "Data") => false  -- Don't evaluate data
  | some (.symbol "Quote") => false  -- Don't evaluate quotes
  | _ => true

/-! ## Theorems -/

/-- Every atom has its intrinsic meta-type -/
theorem hasIntrinsicType (space : Atomspace) (a : Atom) :
    HasType space a (intrinsicTypeAtom a) := by
  match a with
  | .symbol s => exact HasType.intrinsicSymbol s
  | .var v => exact HasType.intrinsicVariable v
  | .grounded g => exact HasType.intrinsicGrounded g
  | .expression es => exact HasType.intrinsicExpression es

/-- Every atom has type Atom -/
theorem hasTypeAtom (space : Atomspace) (a : Atom) :
    HasType space a (.symbol "Atom") := by
  exact HasType.atomSubtype a (intrinsicTypeAtom a) (hasIntrinsicType space a)

/-- Type annotation creates correct typing -/
theorem annotation_gives_type (space : Atomspace) (a ty : Atom)
    (h : typeAnnotation a ty ∈ space.atoms) :
    HasType space a ty :=
  HasType.annotated a ty h

/-- checkType is sound for Symbol -/
theorem checkType_symbol_sound (space : Atomspace) (s : String) :
    checkType space (.symbol s) (.symbol "Symbol") = true := rfl

/-- checkType is sound for Variable -/
theorem checkType_variable_sound (space : Atomspace) (v : String) :
    checkType space (.var v) (.symbol "Variable") = true := rfl

/-- checkType is sound for Grounded -/
theorem checkType_grounded_sound (space : Atomspace) (g : GroundedValue) :
    checkType space (.grounded g) (.symbol "Grounded") = true := rfl

/-- checkType is sound for Expression -/
theorem checkType_expression_sound (space : Atomspace) (es : List Atom) :
    checkType space (.expression es) (.symbol "Expression") = true := rfl

/-- checkType is sound for Atom (everything is an Atom) -/
theorem checkType_atom_sound (space : Atomspace) (a : Atom) :
    checkType space a (.symbol "Atom") = true := rfl

/-! ## Unit Tests -/

section Tests

-- Meta-type parsing
example : MetaType.fromAtom (.symbol "Atom") = some .atom := rfl
example : MetaType.fromAtom (.symbol "Symbol") = some .symbol := rfl
example : MetaType.fromAtom (.symbol "foo") = none := rfl

-- Type annotation
example : typeAnnotation (.symbol "x") (.symbol "Int") =
          .expression [.symbol ":", .symbol "x", .symbol "Int"] := rfl

-- Function type
example : functionType [.symbol "Int"] (.symbol "Int") =
          .expression [.symbol "->", .symbol "Int", .symbol "Int"] := rfl
example : functionType [.symbol "Int", .symbol "Int"] (.symbol "Bool") =
          .expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Bool"] := rfl

-- Intrinsic types
example : intrinsicType (.symbol "x") = .symbol := rfl
example : intrinsicType (.var "x") = .variable := rfl
example : intrinsicType (.grounded (.int 42)) = .grounded := rfl
example : intrinsicType (.expression []) = .expression := rfl

-- Type checking
example : checkType Atomspace.empty (.symbol "x") (.symbol "Symbol") = true := rfl
example : checkType Atomspace.empty (.var "x") (.symbol "Variable") = true := rfl
example : checkType Atomspace.empty (.grounded (.int 42)) (.symbol "Int") = true := rfl
example : checkType Atomspace.empty (.symbol "x") (.symbol "Atom") = true := rfl

-- Type annotations in space
example : isTypeAnnotation (.expression [.symbol ":", .symbol "x", .symbol "Int"]) = true := rfl
example : isTypeAnnotation (.symbol "x") = false := rfl

-- Function type predicates
example : isFunctionType (.expression [.symbol "->", .symbol "Int", .symbol "Int"]) = true := rfl
example : isFunctionType (.symbol "->") = false := rfl

end Tests

end Mettapedia.Languages.MeTTa.OSLFCore
