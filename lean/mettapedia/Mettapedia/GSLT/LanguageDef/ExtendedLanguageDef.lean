import Mettapedia.GSLT.LanguageDef.ExtensionComposition

/-!
# Language definitions with compositional extension layers

`ExtendedLanguageDef layer` is the common mathematical core beneath convenient
language-specific authoring records.  It stores one exact five-field
`LanguageDef` together with one payload in a `CompositionalLayer` over that
same definition.

The layer is not an untyped attachment.  It supplies:

* an authored GSLT whose terms describe extension declarations;
* an elaborator invariant under the GSLT's equations and rewrites;
* empty-document and concatenation laws; and
* an exact quotation of every payload back into authored terms.

Independent layers compose by `CompositionalLayer.product`.  Consequently this
record does not grow a new optional field for every extension kind: a proof
calculus, logic declarations, oracle declarations, and future semantic layers
can be combined at the type level while retaining their own authoring GSLTs.

This structure concerns authoring and exact elaboration.  A semantic GSLT or a
compiled abstract machine is additional law-bearing data: different payload
kinds have different denotations, and runtime choices must not be smuggled into
the language definition.

For direct authoring, `extendedLanguageDef!` keeps the five core fields in one
ordinary record and names each independently composed layer:

```
extendedLanguageDef!
  { name := "example", types := [...], terms := [...],
    equations := [...], rewrites := [...] }
  with layer (logicLayer) { logicDeclarations }
  and  layer (oracleLayer) { oracleDeclarations }
```

The notation expands only to `ExtendedLanguageDef.addLayer`; it introduces no
second representation and supports any finite number of compositional layers.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uFiber uFiberRight

/-- One five-field language definition together with a payload authored by a
compositional GSLT layer over that exact definition. -/
structure ExtendedLanguageDef
    (layer : CompositionalLayer.{0, uFiber} LanguageDef)
    extends LanguageDef where
  /-- The elaborated extension payload over the inherited five-field base. -/
  extension : layer.Fiber toLanguageDef

namespace ExtendedLanguageDef

variable {layer : CompositionalLayer.{0, uFiber} LanguageDef}

/-- The authored GSLT in which this definition's extension is written. -/
def authoredGSLT (definition : ExtendedLanguageDef layer) : GSLT :=
  (layer.system definition.toLanguageDef).authoring.theory

/-- The canonical authored term denoting the stored extension payload. -/
def authoredSource (definition : ExtendedLanguageDef layer) :
    definition.authoredGSLT.Term :=
  layer.quote definition.toLanguageDef definition.extension

/-- The stored payload is grounded in the layer's authored GSLT: elaborating
its canonical source recovers exactly that payload. -/
@[simp] theorem elaborate_authoredSource
    (definition : ExtendedLanguageDef layer) :
    layer.elaborate definition.toLanguageDef definition.authoredSource =
      some definition.extension :=
  layer.elaborate_quote definition.toLanguageDef definition.extension

/-- The same object viewed in the dependent total space of its coGSLT layer. -/
def attached (definition : ExtendedLanguageDef layer) :
    layer.toCoGSLTLayer.toExtensionLayer.Total :=
  layer.toCoGSLTLayer.attach definition.toLanguageDef definition.extension

/-- Erasure of the attached extension recovers the inherited five-field
language definition definitionally. -/
@[simp] theorem erase_attached (definition : ExtendedLanguageDef layer) :
    layer.toCoGSLTLayer.erase definition.attached =
      definition.toLanguageDef :=
  rfl

/-- Attach a second independently authored layer to the same base.  The result
is indexed by the canonical product authoring GSLT, not by an ad hoc pair. -/
def addLayer
    (definition : ExtendedLanguageDef layer)
    (right : CompositionalLayer.{0, uFiberRight} LanguageDef)
    (rightExtension : right.Fiber definition.toLanguageDef) :
    ExtendedLanguageDef (layer.product right) where
  toLanguageDef := definition.toLanguageDef
  extension := (definition.extension, rightExtension)

@[simp] theorem addLayer_language
    (definition : ExtendedLanguageDef layer)
    (right : CompositionalLayer.{0, uFiberRight} LanguageDef)
    (rightExtension : right.Fiber definition.toLanguageDef) :
    (definition.addLayer right rightExtension).toLanguageDef =
      definition.toLanguageDef :=
  rfl

@[simp] theorem addLayer_left
    (definition : ExtendedLanguageDef layer)
    (right : CompositionalLayer.{0, uFiberRight} LanguageDef)
    (rightExtension : right.Fiber definition.toLanguageDef) :
    (definition.addLayer right rightExtension).extension.1 =
      definition.extension :=
  rfl

@[simp] theorem addLayer_right
    (definition : ExtendedLanguageDef layer)
    (right : CompositionalLayer.{0, uFiberRight} LanguageDef)
    (rightExtension : right.Fiber definition.toLanguageDef) :
    (definition.addLayer right rightExtension).extension.2 = rightExtension :=
  rfl

/-- Build a definition with two independently authored layers at once. -/
def ofProduct
    (base : LanguageDef)
    (left : CompositionalLayer.{0, uFiber} LanguageDef)
    (right : CompositionalLayer.{0, uFiberRight} LanguageDef)
    (leftExtension : left.Fiber base)
    (rightExtension : right.Fiber base) :
    ExtendedLanguageDef (left.product right) where
  toLanguageDef := base
  extension := (leftExtension, rightExtension)

@[simp] theorem ofProduct_language
    (base : LanguageDef)
    (left : CompositionalLayer.{0, uFiber} LanguageDef)
    (right : CompositionalLayer.{0, uFiberRight} LanguageDef)
    (leftExtension : left.Fiber base)
    (rightExtension : right.Fiber base) :
    (ofProduct base left right leftExtension rightExtension).toLanguageDef =
      base :=
  rfl

@[simp] theorem ofProduct_extension
    (base : LanguageDef)
    (left : CompositionalLayer.{0, uFiber} LanguageDef)
    (right : CompositionalLayer.{0, uFiberRight} LanguageDef)
    (leftExtension : left.Fiber base)
    (rightExtension : right.Fiber base) :
    (ofProduct base left right leftExtension rightExtension).extension =
      (leftExtension, rightExtension) :=
  rfl

end ExtendedLanguageDef

/-! ## One-block authoring notation -/

/-- Author one exact five-field base and one or more named compositional layer
payloads as a single `ExtendedLanguageDef`.  The resulting layer index is the
left-associated product in written order. -/
syntax (name := extendedLanguageDefTerm)
  "extendedLanguageDef!" term:arg
    "with" "layer" "(" term ")" "{" term "}"
    ("and" "layer" "(" term ")" "{" term "}")* : term

macro_rules
  | `(extendedLanguageDef! $base
        with layer ($firstLayer) { $firstExtension }
        $[and layer ($layers) { $extensions }]*) => do
      let mut result ←
        `(({ toLanguageDef := $base
             extension := $firstExtension } :
            ExtendedLanguageDef $firstLayer))
      for nextLayer in layers, extension in extensions do
        result ← `($result |>.addLayer $nextLayer $extension)
      pure result

/-! ## Authoring canaries -/

namespace ExtendedLanguageDefSyntaxCanary

private def base : LanguageDef :=
  LanguageDef.empty "three-layer-authoring-canary"

private def marker : ProofCalculus :=
  { judgments := [{ head := "Marked", arity := 0 }] }

/-- Positive: the notation accepts any finite nonempty layer sequence and
retains the written, left-associated order. -/
private def threeLayers :
    ExtendedLanguageDef
      ((calculusLayer.product calculusLayer).product calculusLayer) :=
  extendedLanguageDef! base
    with layer (calculusLayer) { ProofCalculus.empty }
    and layer (calculusLayer) { ProofCalculus.empty }
    and layer (calculusLayer) { marker }

@[simp] theorem threeLayers_language :
    threeLayers.toLanguageDef = base :=
  rfl

@[simp] theorem threeLayers_extension :
    threeLayers.extension =
      ((ProofCalculus.empty, ProofCalculus.empty), marker) :=
  rfl

private def threeEmptyLayers :
    ExtendedLanguageDef
      ((calculusLayer.product calculusLayer).product calculusLayer) :=
  extendedLanguageDef! base
    with layer (calculusLayer) { ProofCalculus.empty }
    and layer (calculusLayer) { ProofCalculus.empty }
    and layer (calculusLayer) { ProofCalculus.empty }

/-- Negative: changing a layer payload changes the combined definition even
when the five-field base and every other layer stay fixed. -/
theorem final_layer_is_not_erased :
    threeLayers.extension ≠ threeEmptyLayers.extension := by
  intro equal
  have judgmentsEqual := congrArg (fun payload => payload.2.judgments) equal
  simp [threeLayers, threeEmptyLayers, marker, ProofCalculus.empty] at judgmentsEqual

end ExtendedLanguageDefSyntaxCanary

end Mettapedia.GSLT.LanguageDef
