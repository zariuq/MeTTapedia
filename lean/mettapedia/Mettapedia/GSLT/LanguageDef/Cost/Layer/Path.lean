import Mettapedia.GSLT.LanguageDef.Cost.Layer.Basic
import Mathlib.Combinatorics.Quiver.Path

/-!
# Composable paths of Cost layers

A cost layer has a source and a compact output, but two consecutive layers do
not in general flatten to one layer.  The honest iteration object is therefore
a path in the directed network of layers.

`OrderedCIGSLT` already carries the quiver of its semantic morphisms through
its category instance.  `Cost.Layer.Vertex` is a deliberate wrapper giving the
layer network its own arrow type without installing a competing quiver
instance on the semantic category.
-/

namespace Mettapedia.GSLT.LanguageDef

/-- A vertex in the directed network whose edges are cost layers. -/
structure Cost.Layer.Vertex where
  object : OrderedCIGSLT

namespace Cost.Layer.Vertex

/-- Regard an ordered continued authority as a layer-network vertex. -/
def of (object : OrderedCIGSLT) : Cost.Layer.Vertex := ⟨object⟩

end Cost.Layer.Vertex

/-- An edge from `source` to `target` is a layer over the source whose compact
output is the target. -/
structure Cost.Layer.Edge
    (source target : Cost.Layer.Vertex) where
  layer : Cost.LayerOn source.object
  compactOutput_eq : layer.layer.compactOutput = target.object

instance : Quiver Cost.Layer.Vertex where
  Hom := Cost.Layer.Edge

namespace Cost.Layer

/-- Every cost layer is a canonical edge from its source to its compact
output. -/
def toEdge (layer : Cost.Layer) :
    Cost.Layer.Edge (.of layer.source) (.of layer.compactOutput) where
  layer := layer.onSource
  compactOutput_eq := rfl

end Cost.Layer

/-- A composable cost path reuses mathlib's free path construction.  Its
composition retains every layer boundary. -/
abbrev Cost.Path (source target : Cost.Layer.Vertex) :=
  Quiver.Path source target

namespace Cost.Path

/-- The path consisting of one cost layer. -/
def ofLayer (layer : Cost.Layer) :
    Cost.Path (.of layer.source) (.of layer.compactOutput) :=
  Quiver.Hom.toPath layer.toEdge

/-- Paths of a specified length.  The index records genuine layer count; it
does not postulate a flattened iterated layer. -/
abbrev OfLength (source target : Cost.Layer.Vertex) (length : Nat) :=
  { path : Cost.Path source target // path.length = length }

@[simp] theorem length_ofLayer (layer : Cost.Layer) :
    (ofLayer layer).length = 1 :=
  by simp [ofLayer]

/-- The empty path contains no cost layer. -/
def nil (vertex : Cost.Layer.Vertex) :
    Cost.Path.OfLength vertex vertex 0 :=
  ⟨Quiver.Path.nil, rfl⟩

/-- Prefixing a path by a layer increments the retained layer count. -/
def cons {source middle target : Cost.Layer.Vertex}
    (path : Cost.Path source middle)
    (layer : Cost.Layer.Edge middle target) :
    Cost.Path source target :=
  Quiver.Path.cons path layer

@[simp] theorem length_cons {source middle target : Cost.Layer.Vertex}
    (path : Cost.Path source middle)
    (layer : Cost.Layer.Edge middle target) :
    (cons path layer).length = path.length + 1 :=
  Quiver.Path.length_cons source middle target path layer

end Cost.Path

end Mettapedia.GSLT.LanguageDef
