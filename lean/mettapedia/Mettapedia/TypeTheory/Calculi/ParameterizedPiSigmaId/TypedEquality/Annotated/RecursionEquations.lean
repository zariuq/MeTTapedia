import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DefinedConstants

/-!
# The equations of a definition by structural recursion

A function `f : Π (t : T). M` on a declared datatype `T` is defined by structural recursion
when it has one equation for each constructor `k`,

    f (k v₁ … vₐ) ⟶ rhs,

whose right side may call `f` at the recursive fields of the constructor, and nowhere else.
Later arguments of the function are part of the result family `M`: for a function of a list
and a further list, `M` is the type of functions from lists to lists, and a right side is an
abstraction over the further argument. This is the class the draft kernel admits by its check
of structural recursion, with the inspected argument first.

A right side is given with its recursive calls abstracted, as the unannotated
`Normalization.DeclaresRecursion` gives it: a body over the fields of the constructor and one
hypothesis for each recursive field (`methodCtx`), the hypothesis for a field having the
result type at that field (`resultAt`). The body has the result type at the constructor
applied to its fields (`ctorAt`). The right side of the equation is the body with the call of
`f` at each recursive field substituted for its hypothesis (`callSub`).

`recursionEquations` lists the equations, one per constructor, as `DefiningEquation`s over the
telescope of the constructor's fields; `withDefinition` makes them the computation rules of
`f`. Their set model is in `TowerInterpretation/SetRecursion.lean`.

Positive example: a constructor without recursive fields has no hypothesis, and its method
context is the telescope of its fields (`methodCtx_zero`). Negative example: a constant with
no constructor to match has no equation (`recursionEquations_nil`), so a function on a
datatype without constructors computes nowhere.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization

variable {Head : Type}

/-- The result type at the field at position `p`, in a context of `a` fields and `r`
hypotheses: the result family at that field's variable. -/
def resultAt (M : CTm Head 1) (a r p : Nat) : CTm Head (a + r) :=
  M.subst fun _ => if h : p < a then .var ⟨r + (a - 1 - p), by omega⟩ else .const .anonymous

/-- **The context of a method**: the fields of the constructor, then a hypothesis for each of
its first `r` recursive fields, of the result type at that field. -/
def methodCtx (T : DeclName) (M : CTm Head 1) (fields : List (Field Head)) :
    (r : Nat) → CCtx Head (fields.length + r)
  | 0 => liftCtx (ctorTele T fields)
  | r + 1 => .snoc (methodCtx T M fields r)
      (resultAt M fields.length r ((recPositions fields).getD r 0))

/-- Positive example: without hypotheses the method context is the telescope of the fields. -/
theorem methodCtx_zero (T : DeclName) (M : CTm Head 1) (fields : List (Field Head)) :
    methodCtx T M fields 0 = liftCtx (ctorTele T fields) := rfl

/-- The constructor applied to the variables of its fields, in the context of a method. -/
def ctorAt (k : DeclName) (a r : Nat) : CTm Head (a + r) :=
  liftTm (Presentation.rename (wkN r) (appSpine (.const k) (metaVars a)))

/-- The terms that replace the variables of a method's context in an equation, the oldest
first: the variables of the fields, and for each recursive field the defined constant applied
to its variable. -/
def callTerms (f : DeclName) (fields : List (Field Head)) : List (CTm Head fields.length) :=
  (metaVars fields.length).map liftTm ++
    (recPositions fields).map fun p =>
      .app (.const f) (liftTm ((metaVars fields.length).getD p defaultTm))

theorem length_callTerms (f : DeclName) (fields : List (Field Head)) :
    (callTerms f fields).length = fields.length + (recPositions fields).length := by
  rw [callTerms, List.length_append, List.length_map, List.length_map, length_metaVars]

/-- **The recursive calls in place of the hypotheses**: the substitution of a method's context
by the field variables and the calls of the defined constant at the recursive fields. -/
def callSub (f : DeclName) (fields : List (Field Head)) :
    CSub Head (fields.length + (recPositions fields).length) fields.length :=
  fun j => (callTerms f fields).getD
    (fields.length + (recPositions fields).length - 1 - j.val) (.const .anonymous)

/-- **The equation of a constructor**: on the left the defined constant at the constructor
applied to its field variables, on the right the body with the recursive calls in place of the
hypotheses; over the telescope of the fields. -/
def recursionEquation (f T k : DeclName) (fields : List (Field Head))
    (body : CTm Head (fields.length + (recPositions fields).length)) : DefiningEquation Head where
  arity := fields.length
  telescope := liftCtx (ctorTele T fields)
  left := .app (.const f) (liftTm (appSpine (.const k) (metaVars fields.length)))
  right := body.subst (callSub f fields)

/-- **The equations of a definition by structural recursion**, one for each constructor. -/
def recursionEquations (f T : DeclName) (ctors : List (DeclName × List (Field Head)))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      CTm Head (fields.length + (recPositions fields).length)) : List (DefiningEquation Head) :=
  ctors.map fun entry => recursionEquation f T entry.1 entry.2 (body entry.1 entry.2)

/-- An equation of the definition is the equation of one of the constructors. -/
theorem mem_recursionEquations {f T : DeclName} {ctors : List (DeclName × List (Field Head))}
    {body : (k : DeclName) → (fields : List (Field Head)) →
      CTm Head (fields.length + (recPositions fields).length)} {e : DefiningEquation Head}
    (member : e ∈ recursionEquations f T ctors body) :
    ∃ (i : Nat) (k : DeclName) (fields : List (Field Head)), ctors[i]? = some (k, fields) ∧
      e = recursionEquation f T k fields (body k fields) := by
  obtain ⟨entry, memberEntry, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, found⟩ := List.getElem?_of_mem memberEntry
  exact ⟨i, entry.1, entry.2, found, rfl⟩

/-- Negative example: over a datatype without constructors the definition has no equation. -/
theorem recursionEquations_nil (f T : DeclName)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      CTm Head (fields.length + (recPositions fields).length)) :
    recursionEquations f T [] body = [] := rfl

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
