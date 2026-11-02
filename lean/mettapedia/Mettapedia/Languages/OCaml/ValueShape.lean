import Mettapedia.Languages.OCaml.Syntax

/-! Data and function-presence equivalence for primitive observations.
All closure addresses and captures may differ. The relation is narrower
than a general behavioral equivalence and carries no execution authority. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

mutual
  inductive ValueShape : Value → Value → Prop where
    | literal (value : Literal) : ValueShape (.literal value) (.literal value)
    | tuple {left right} (fields : FieldsShape left right) : ValueShape (.tuple left) (.tuple right)
    | cons {head first tail rest} (front : ValueShape head first) (back : ValueShape tail rest) :
        ValueShape (.cons head tail) (.cons first rest)
    | variant {typeId constructor left right} (fields : FieldsShape left right) :
        ValueShape (.variant typeId constructor left) (.variant typeId constructor right)
    | closure (left right : FunctionRef) (first second : List Value) : ValueShape (.closure left first) (.closure right second)

  inductive FieldsShape : List Value → List Value → Prop where
    | nil : FieldsShape [] []
    | cons {left right first second} (head : ValueShape left right) (tail : FieldsShape first second) :
        FieldsShape (left :: first) (right :: second)
end

theorem FieldsShape.length {left right : List Value} (same : FieldsShape left right) : left.length = right.length :=
  match same with
  | .nil => rfl
  | .cons _ tail => by simp only [List.length_cons, tail.length]
termination_by structural same

mutual
  theorem ValueShape.symm {left right : Value} (same : ValueShape left right) : ValueShape right left :=
    match same with
    | .literal value => .literal value
    | .tuple fields => .tuple fields.symm
    | .cons front back => .cons front.symm back.symm
    | .variant fields => .variant fields.symm
    | .closure left right first second => .closure right left second first
    termination_by structural same

  theorem FieldsShape.symm {left right : List Value} (same : FieldsShape left right) : FieldsShape right left :=
    match same with
    | .nil => .nil
    | .cons head tail => .cons head.symm tail.symm
    termination_by structural same
end

#print axioms FieldsShape.length
#print axioms ValueShape.symm
#print axioms FieldsShape.symm

end Mettapedia.Languages.OCaml
