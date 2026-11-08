import Mettapedia.Languages.Lean.CodeEquations.Erased

/-!
# Lean values in the erased spelling

A computed Lean value printed as the PeTTa term erasure gives it: naturals as
numbers, Booleans as `true`/`false`, constructors by their encoded names over
their fields. Lean's own evaluation of `PeTTaValue.render t` is the reference
a code-equation run is compared with.
-/

namespace Mettapedia.Languages.Lean.CodeEquations

class PeTTaValue (α : Type u) where
  render : α → String

export PeTTaValue (render)

/-- Render an erased constructor application for a value observer. -/
def ctorApp (c : Lean.Name) (fields : List String) : String :=
  if fields.isEmpty then ctorSymbol c
  else "(" ++ " ".intercalate (ctorSymbol c :: fields) ++ ")"

instance : PeTTaValue Nat := ⟨toString⟩
instance : PeTTaValue Bool := ⟨fun b => if b then "true" else "false"⟩
instance : PeTTaValue String := ⟨quoteString⟩
instance : PeTTaValue Unit := ⟨fun _ => ctorSymbol ``PUnit.unit⟩

instance [PeTTaValue α] : PeTTaValue (List α) where
  render l := l.foldr (fun a acc => ctorApp ``List.cons [render a, acc]) (ctorSymbol ``List.nil)

instance [PeTTaValue α] : PeTTaValue (Option α) where
  render
    | none => ctorSymbol ``Option.none
    | some a => ctorApp ``Option.some [render a]

instance [PeTTaValue α] [PeTTaValue β] : PeTTaValue (α × β) where
  render p := ctorApp ``Prod.mk [render p.1, render p.2]

instance : PeTTaValue Ordering where
  render
    | .lt => ctorSymbol ``Ordering.lt
    | .eq => ctorSymbol ``Ordering.eq
    | .gt => ctorSymbol ``Ordering.gt

#guard render [1, 2] == "(List.cons 1 (List.cons 2 List.nil))"
#guard render (some (3, true)) == "(Option.some (Prod.mk 3 true))"

end Mettapedia.Languages.Lean.CodeEquations
