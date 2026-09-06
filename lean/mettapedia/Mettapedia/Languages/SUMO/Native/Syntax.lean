/-!
# Intrinsically scoped syntax for SUMO's native logical core

SUO-KIF does not syntactically separate individuals, functions, relations,
and formulas into Church-style simple types.  In particular, a variable may
occur in operator position, formulas may occur as arguments, and the SUMO
upper ontology contains self-application.  This syntax retains that unityped
character while making the two binding disciplines explicit:

* ordinary variables range over the model carrier;
* row variables range over finite argument sequences.

Function application and relation application have distinct syntactic
constructors because their results are used differently, but both accept an
arbitrary term as operator.  A formula used as an argument is retained by
`Term.quote`; it is not lowered to an opaque first-order name.

`Term.kappa` records SUO-KIF's class-forming binder.  The core syntax does not
assign it a computation or comprehension rule; such a rule belongs only to a
declared extension with a sound model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native

universe uSymbol uLiteral

mutual
  /-- Unityped SUMO terms with `ordinary` ordinary-variable slots and `rows`
  row-variable slots. -/
  inductive Term (Symbol : Type uSymbol) (Literal : Type uLiteral) :
      Nat -> Nat -> Type (max uSymbol uLiteral) where
    | var {ordinary rows : Nat} : Fin ordinary ->
        Term Symbol Literal ordinary rows
    | constant {ordinary rows : Nat} : Symbol ->
        Term Symbol Literal ordinary rows
    | literal {ordinary rows : Nat} : Literal ->
        Term Symbol Literal ordinary rows
    | application {ordinary rows : Nat} :
        Term Symbol Literal ordinary rows ->
        Spine Symbol Literal ordinary rows ->
        Term Symbol Literal ordinary rows
    | quote {ordinary rows : Nat} :
        Formula Symbol Literal ordinary rows ->
        Term Symbol Literal ordinary rows
    | kappa {ordinary rows : Nat} :
        Formula Symbol Literal (ordinary + 1) rows ->
        Term Symbol Literal ordinary rows

  /-- An exact argument spine. A row occurrence contributes an arbitrary
  finite sequence at evaluation and substitution time. -/
  inductive Spine (Symbol : Type uSymbol) (Literal : Type uLiteral) :
      Nat -> Nat -> Type (max uSymbol uLiteral) where
    | nil {ordinary rows : Nat} : Spine Symbol Literal ordinary rows
    | term {ordinary rows : Nat} :
        Term Symbol Literal ordinary rows ->
        Spine Symbol Literal ordinary rows ->
        Spine Symbol Literal ordinary rows
    | row {ordinary rows : Nat} :
        Fin rows ->
        Spine Symbol Literal ordinary rows ->
        Spine Symbol Literal ordinary rows

  /-- Native SUMO formulas. Relation operators are unityped terms, so this
  includes constant relations, relation variables, and computed operators. -/
  inductive Formula (Symbol : Type uSymbol) (Literal : Type uLiteral) :
      Nat -> Nat -> Type (max uSymbol uLiteral) where
    | top {ordinary rows : Nat} : Formula Symbol Literal ordinary rows
    | bottom {ordinary rows : Nat} : Formula Symbol Literal ordinary rows
    | atom {ordinary rows : Nat} :
        Term Symbol Literal ordinary rows ->
        Spine Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    | asserted {ordinary rows : Nat} :
        Term Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    | equal {ordinary rows : Nat} :
        Term Symbol Literal ordinary rows ->
        Term Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    /-- The argument belongs to the operator's effective zero-based domain
    at the supplied position. -/
    | inOperatorDomain {ordinary rows : Nat} :
        Term Symbol Literal ordinary rows ->
        Nat ->
        Term Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    /-- The exact tail satisfies the operator's arity and effective domains,
    beginning at the supplied zero-based argument position. -/
    | tailInOperatorDomain {ordinary rows : Nat} :
        Term Symbol Literal ordinary rows ->
        Nat ->
        Spine Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    | not {ordinary rows : Nat} :
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    | and {ordinary rows : Nat} :
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    | or {ordinary rows : Nat} :
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    | implies {ordinary rows : Nat} :
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    | iff {ordinary rows : Nat} :
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows ->
        Formula Symbol Literal ordinary rows
    /-- Every object denoted by the exact argument spine satisfies the body. -/
    | allInSpine {ordinary rows : Nat} :
        Spine Symbol Literal ordinary rows ->
        Formula Symbol Literal (ordinary + 1) rows ->
        Formula Symbol Literal ordinary rows
    | allObject {ordinary rows : Nat} :
        Formula Symbol Literal (ordinary + 1) rows ->
        Formula Symbol Literal ordinary rows
    | someObject {ordinary rows : Nat} :
        Formula Symbol Literal (ordinary + 1) rows ->
        Formula Symbol Literal ordinary rows
    | allRow {ordinary rows : Nat} :
        Formula Symbol Literal ordinary (rows + 1) ->
        Formula Symbol Literal ordinary rows
    | someRow {ordinary rows : Nat} :
        Formula Symbol Literal ordinary (rows + 1) ->
        Formula Symbol Literal ordinary rows
end

deriving instance DecidableEq for Term, Spine, Formula

deriving instance Repr for Term, Spine, Formula

/-- Closed formulas have no free ordinary or row variables. -/
abbrev Sentence (Symbol : Type uSymbol) (Literal : Type uLiteral) :=
  Formula Symbol Literal 0 0

namespace Spine

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}
variable {ordinary rows : Nat}

/-- A one-argument spine. -/
def singleton (term : Term Symbol Literal ordinary rows) :
    Spine Symbol Literal ordinary rows :=
  .term term .nil

/-- Convert a finite list of ordinary arguments to a spine. -/
def ofTerms (terms : List (Term Symbol Literal ordinary rows)) :
    Spine Symbol Literal ordinary rows :=
  terms.foldr .term .nil

/-- Concatenate exact spines without expanding row variables. -/
def append : Spine Symbol Literal ordinary rows ->
    Spine Symbol Literal ordinary rows ->
    Spine Symbol Literal ordinary rows
  | .nil, suffix => suffix
  | .term value rest, suffix => .term value (append rest suffix)
  | .row rowVariable rest, suffix => .row rowVariable (append rest suffix)

@[simp] theorem nil_append
    (suffix : Spine Symbol Literal ordinary rows) :
    append .nil suffix = suffix := rfl

@[simp] theorem term_append
    (value : Term Symbol Literal ordinary rows)
    (rest suffix : Spine Symbol Literal ordinary rows) :
    append (.term value rest) suffix = .term value (append rest suffix) := rfl

@[simp] theorem row_append
    (rowVariable : Fin rows)
    (rest suffix : Spine Symbol Literal ordinary rows) :
    append (.row rowVariable rest) suffix =
      .row rowVariable (append rest suffix) := rfl

end Spine

/-! ## Source-shape canaries -/

namespace SyntaxCanary

/-- The SUMO upper-ontology formula `(instance instance BinaryPredicate)` is
well scoped without splitting either occurrence of `instance` into a type. -/
def selfApplication : Sentence String Unit :=
  .atom (.constant "instance")
    (.term (.constant "instance")
      (.term (.constant "BinaryPredicate") .nil))

/-- A quantified ordinary variable can occur in relation-operator position. -/
def variableRelation : Formula String Unit 1 0 :=
  .atom (.var 0) (.singleton (.constant "Human"))

/-- A formula passed to `believes` remains a native formula intension. -/
def formulaArgument : Sentence String Unit :=
  .atom (.constant "believes")
    (.term (.constant "Mary")
      (.term
        (.quote
          (.atom (.constant "likes")
            (.term (.constant "John")
              (.term (.constant "Sue") .nil))))
        .nil))

/-- A row occurrence is a single scoped node, not a bounded family of
fixed-arity approximations. -/
def exactRow : Formula String Unit 0 1 :=
  .atom (.constant "holds") (.row 0 .nil)

example : selfApplication =
    .atom (.constant "instance")
      (.term (.constant "instance")
        (.term (.constant "BinaryPredicate") .nil)) := rfl

example : variableRelation =
    .atom (.var 0) (.singleton (.constant "Human")) := rfl

example : exactRow = .atom (.constant "holds") (.row 0 .nil) := rfl

end SyntaxCanary

end Mettapedia.Languages.SUMO.Native
