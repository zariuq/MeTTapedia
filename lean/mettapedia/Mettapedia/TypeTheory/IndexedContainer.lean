import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Defs

/-!
# Indexed containers as normal forms for unary strictly-positive families

An indexed container separates a family into output-indexed shapes and the
positions at which parameter data occur.  Its extension is the dependent pair
of a shape and a labelling of every position.  This is the semantic normal form
used by the native-family capability layer; object-language declaration
elaboration remains a separate, source-faithful theorem.

Strict positivity does not imply finitarity.  Accordingly, `Finitary` is an
additional proof that every position fibre is finite.  Lists and vectors have
this proof.  The positive reader container with natural-number positions does
not.
-/

namespace Mettapedia.TypeTheory

universe uOutput uShape uPosition uElement uTarget uThird

/-- A one-parameter indexed container.  `Shape output` records the complete
structural skeleton at an output index; `Position shape` records every place
where a parameter value is stored. -/
structure IndexedContainer (Output : Type uOutput) where
  Shape : Output → Type uShape
  Position : {output : Output} → Shape output → Type uPosition

namespace IndexedContainer

variable {Output : Type uOutput}

/-- Interpret an indexed container at a parameter type. -/
abbrev Extension
    (container : IndexedContainer.{uOutput, uShape, uPosition} Output)
    (Element : Type uElement) (output : Output) :
    Type (max uShape uPosition uElement) :=
  Σ shape : container.Shape output, container.Position shape → Element

/-- Map the stored parameter values without changing the structural shape. -/
def map
    (container : IndexedContainer.{uOutput, uShape, uPosition} Output)
    (function : Element → Target) {output : Output} :
    container.Extension Element output →
      container.Extension Target output
  | ⟨shape, values⟩ => ⟨shape, fun position => function (values position)⟩

@[simp] theorem map_id
    (container : IndexedContainer.{uOutput, uShape, uPosition} Output)
    {output : Output} (value : container.Extension Element output) :
    container.map (fun element => element) value = value := by
  cases value
  rfl

@[simp] theorem map_comp
    (container : IndexedContainer.{uOutput, uShape, uPosition} Output)
    (first : Element → Target) (second : Target → Third)
    {output : Output} (value : container.Extension Element output) :
    container.map second (container.map first value) =
      container.map (fun element => second (first element)) value := by
  cases value
  rfl

/-- Finitarity is operational evidence, not part of strict positivity: every
shape has finitely many parameter positions. -/
structure Finitary
    (container : IndexedContainer.{uOutput, uShape, uPosition} Output) where
  positionFintype : ∀ {output : Output} (shape : container.Shape output),
    Fintype (container.Position shape)

namespace Examples

/-- Lists in indexed-container normal form: length is the shape and `Fin
length` names stored elements. -/
def list : IndexedContainer Unit where
  Shape := fun _ => Nat
  Position := fun length => Fin length

def listFinitary : Finitary list where
  positionFintype := fun {output} length => by
    cases output
    change Fintype (Fin length)
    infer_instance

/-- The container extension is exactly the usual shape/tuple encoding of
lists. -/
def listExtensionEquiv (Element : Type uElement) :
    List Element ≃ list.Extension Element () :=
  List.equivSigmaTuple

/-- Vectors use the length as output index.  Their sole shape stores exactly
`Fin length` parameter positions. -/
def vector : IndexedContainer Nat where
  Shape := fun _ => Unit
  Position := fun {_length} _ => Fin _length

def vectorFinitary : Finitary vector where
  positionFintype := fun {output} shape => by
    cases shape
    change Fintype (Fin output)
    infer_instance

/-- An infinitary but still positive container: one shape with a parameter at
every natural-number position. -/
def reader : IndexedContainer Unit where
  Shape := fun _ => Unit
  Position := fun _ => Nat

def readerExtensionEquiv (Element : Type uElement) :
    reader.Extension Element () ≃ (Nat → Element) where
  toFun value := value.2
  invFun values := ⟨(), values⟩
  left_inv := by rintro ⟨shape, values⟩; cases shape; rfl
  right_inv := fun _ => rfl

/-- Strict positivity permits infinitary positions, so it cannot manufacture
the separate finitarity capability. -/
theorem reader_not_finitary : ¬ Nonempty (Finitary reader) := by
  rintro ⟨finitary⟩
  letI : Fintype Nat :=
    @Finitary.positionFintype Unit reader finitary () ()
  exact not_finite Nat

end Examples

#print axioms map_id
#print axioms map_comp
#print axioms Examples.listExtensionEquiv
#print axioms Examples.reader_not_finitary

end IndexedContainer
end Mettapedia.TypeTheory
