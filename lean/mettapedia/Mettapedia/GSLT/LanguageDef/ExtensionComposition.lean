import Mettapedia.GSLT.LanguageDef.InferenceExtension
import Mettapedia.GSLT.Core.FreeDocumentNormalization

set_option linter.dupNamespace false

/-!
# Composing authored extension languages

Two extension languages over one core — a proof calculus and, say, a native
operation interface — should be authorable side by side and assembled into one
extension language.  `ExtensionLayer.product` already glues the *payloads*.
Nothing glues the *authoring languages*, and this module explains why and
supplies the structure that closes the gap.

## Where the gap is

A `CoGSLTLayer` carries an elaborator `Term → Option (Fiber base)` and nothing
else.  Suppose two of them, with fibres `F` and `G`, and suppose we want their
composite to have fibre `F × G`.  A document that mentions only left-hand
declarations must still elaborate to a *pair*, so the composite has to invent a
`G`.  Nothing in `CoGSLTLayer` supplies one, and the choice is not free:
`padding_is_authored` exhibits two right-hand layers over one carrier whose
composites disagree on a document containing no right-hand declaration at all.

The missing structure is not an independently selected unit or payload
algebra.  It is authored concatenation together with the law that elaboration
carries concatenation to payload merge.  The meaning of the authored empty
term is then the payload unit, and both neutral laws and associativity follow.
`GSLT.CompositionalElaboration.toPartialMonoid` proves this derivation.

## What then composes

A `CompositionalLayer` is an indexed family of exact elaborations from
compositional GSLTs satisfying that homomorphism law.  Every compositional
layer induces a `CoGSLTLayer`, and compositional layers are closed under
`product`:

* the two complete authored theories embed into a free mixed-document GSLT;
* payload merge is the product of the two derived partial monoids;
* quotation places the two canonical component terms in one mixed document;
* exact round trip and append preservation are theorems.

`product_elaborates_left_only` and `product_elaborates_right_only` are the
compatibility laws: the composite restricted to one side's documents is that
side's elaborator, padded by the meaning of the other side's authored empty
term.  That is what makes the assembly conservative on each component rather
than merely type-correct.

## Where it genuinely stops

Composition of *authored* extensions is total.  Composition of *admitted* ones
is interpreted separately in `ExtensionCompositionAdmission`; its negative
example exhibits two individually admitted proof calculi whose merge is
rejected.

`Compatible` names the overlap condition this forces, and
`append_isSome_of_compatible` discharges the part of it that the partial monoid
already sees.  The gluing law itself — compatible admitted calculi merge to an
admitted calculus — is `ExtensionGluing.gluing_of_compatible`.

So the extension architecture is a fibration over the core, with a fibrewise
partial monoid on authored declarations and a compatibility relation on
admitted ones.  Authored composition is unconditional; admitted composition
holds exactly on compatible overlaps.
-/

namespace Mettapedia.GSLT.LanguageDef.ExtensionComposition

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uBase uFiber uFiberRight uFiberThird
universe uArtifactLeft uArtifactRight uObservationLeft uObservationRight

/-! ## The proof-calculus partial monoid

`ProofCalculus` already carries this structure; the associativity available
beside it is the conditional form, so the unconditional law is proved here. -/

/-- Authored proof calculi assemble as a partial monoid, failing exactly on a
conflict of rooted conversion authority. -/
def proofCalculusMonoid : PartialMonoid ProofCalculus where
  unit := .empty
  op := ProofCalculus.append?
  unit_op := ProofCalculus.empty_append
  op_unit := ProofCalculus.append_empty
  op_assoc := by
    rintro ⟨firstJudgments, firstRules, firstConversion⟩
      ⟨secondJudgments, secondRules, secondConversion⟩
      ⟨thirdJudgments, thirdRules, thirdConversion⟩
    cases firstConversion <;> cases secondConversion <;> cases thirdConversion <;>
      simp [ProofCalculus.append?, List.append_assoc]

/-! ## Folding a document

Elaboration of a declaration list is the fold of its generators through the
derived partial monoid.  The generic fold lives in `GSLT.Core.Composition`;
this specialization only removes the per-generator `Option`. -/

/-- Fold a generator list into a payload, failing on the first conflict. -/
def foldWith {Fiber : Type u} {Generator : Type v}
    (monoid : PartialMonoid Fiber) (interpret : Generator → Fiber) :
    List Generator → Option Fiber :=
  monoid.foldOption (fun generator => some (interpret generator))

@[simp] theorem foldWith_nil {Fiber : Type u} {Generator : Type v}
    (monoid : PartialMonoid Fiber) (interpret : Generator → Fiber) :
    foldWith monoid interpret [] = some monoid.unit :=
  rfl

@[simp] theorem foldWith_cons {Fiber : Type u} {Generator : Type v}
    (monoid : PartialMonoid Fiber) (interpret : Generator → Fiber)
    (generator : Generator) (rest : List Generator) :
    foldWith monoid interpret (generator :: rest) =
      (foldWith monoid interpret rest).bind fun tail =>
        monoid.op (interpret generator) tail :=
  rfl

/-- **The fold is a homomorphism of partial monoids.**  Concatenating documents
merges their payloads, and a conflict anywhere is a conflict overall.  This is
the law that makes side-by-side authoring meaningful. -/
theorem foldWith_append {Fiber : Type u} {Generator : Type v}
    (monoid : PartialMonoid Fiber) (interpret : Generator → Fiber)
    (first second : List Generator) :
    foldWith monoid interpret (first ++ second) =
      (foldWith monoid interpret first).bind fun leftValue =>
        (foldWith monoid interpret second).bind fun rightValue =>
          monoid.op leftValue rightValue :=
  PartialMonoid.foldOption_append monoid
    (fun generator => some (interpret generator)) first second

/-! ## Compositional layers

An indexed compositional layer is only a family of law-bearing
`CompositionalElaboration`s.  In particular, it does not carry a payload
partial monoid as independent data. -/

/-- A family of compositional authored GSLTs indexed by an unchanged base. -/
structure CompositionalLayer (Base : Type uBase) where
  /-- The payload attached over each base. -/
  Fiber : Base → Type uFiber
  /-- The authored language and its law-preserving exact elaboration. -/
  system : ∀ base, GSLT.CompositionalElaboration (Fiber base)

namespace CompositionalLayer

variable {Base : Type uBase}

/-- Every exact declaration codec supplies an indexed compositional layer.
The index is unchanged and does not influence raw decoding; contextual
admission may subsequently restrict the resulting payload fibre. -/
def ofCodec (Base : Type uBase) {Syntax : Type} {Payload : Type uFiber}
    (codec : ExactDeclarationCodec Syntax Payload) :
    CompositionalLayer.{uBase, uFiber} Base where
  Fiber := fun _ => List Payload
  system := fun _ => codec.compositionalElaboration

/-- The payload partial monoid forced by authored concatenation. -/
def monoid (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base) :
    PartialMonoid (layer.Fiber base) :=
  (layer.system base).toPartialMonoid

/-- Elaborate an authored term over one base. -/
def elaborate (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base) :
    (layer.system base).authoring.theory.Term → Option (layer.Fiber base) :=
  (layer.system base).elaboration.elaborate

/-- Canonical authored representative of a payload. -/
def quote (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base) :
    layer.Fiber base → (layer.system base).authoring.theory.Term :=
  (layer.system base).elaboration.quote

@[simp] theorem elaborate_quote
    (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base)
    (value : layer.Fiber base) :
    layer.elaborate base (layer.quote base value) = some value :=
  (layer.system base).elaboration.elaborate_quote value

/-! ### The composite -/

/-- **Two authored extension languages assemble into one.**  The source is the
generic product of the two complete compositional elaborations, applied
pointwise over the unchanged base.  The LanguageDef layer adds no assembly
law of its own. -/
def product
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base) :
    CompositionalLayer.{uBase, max uFiber uFiberRight} Base where
  Fiber := fun base => left.Fiber base × right.Fiber base
  system := fun base => (left.system base).product (right.system base)

@[simp] theorem product_fiber
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    (base : Base) :
    (left.product right).Fiber base = (left.Fiber base × right.Fiber base) :=
  rfl

/-- The composite restricted to a left-hand term is the left elaborator,
padded only by the right authored empty payload. -/
theorem product_elaborates_left_only
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    (base : Base) (source : (left.system base).authoring.theory.Term) :
    (left.product right).elaborate base [Sum.inl source] =
      (left.elaborate base source).map
        fun value => (value, (right.system base).emptyPayload) := by
  exact (left.system base).product_elaborates_left_only
    (right.system base) source

/-- And symmetrically on the right. -/
theorem product_elaborates_right_only
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    (base : Base) (source : (right.system base).authoring.theory.Term) :
    (left.product right).elaborate base [Sum.inr source] =
      (right.elaborate base source).map
        fun value => ((left.system base).emptyPayload, value) := by
  exact (left.system base).product_elaborates_right_only
    (right.system base) source

/-! ### The coGSLT extension induced by a compositional layer -/

/-- Forget only the compositional law, retaining the exact authored GSLT
elaboration. -/
def toCoGSLTLayer (layer : CompositionalLayer.{uBase, uFiber} Base) :
    CoGSLTLayer.{uBase, uFiber} Base where
  Fiber := layer.Fiber
  sourceGSLT := fun base => (layer.system base).authoring.theory
  elaborate := layer.elaborate
  quote := layer.quote
  elaborate_quote := layer.elaborate_quote
  elaborate_equation := fun base => (layer.system base).elaboration.equation
  elaborate_rewrite := fun base => (layer.system base).elaboration.rewrite

/-- Forgetting the compositional law from a codec-induced layer recovers the
ordinary coGSLT layer induced by that same codec, definitionally.  There is one
elaborator and one quotation map, not parallel authorities. -/
@[simp] theorem ofCodec_toCoGSLTLayer (Base : Type uBase)
    {Syntax : Type} {Payload : Type uFiber}
    (codec : ExactDeclarationCodec Syntax Payload) :
    (ofCodec Base codec).toCoGSLTLayer = codec.layer Base :=
  rfl

@[simp] theorem toCoGSLTLayer_fiber
    (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base) :
    layer.toCoGSLTLayer.Fiber base = layer.Fiber base :=
  rfl

/-- The composite coGSLT layer has exactly the product fibre. -/
theorem toCoGSLTLayer_product_fiber
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    (base : Base) :
    (left.product right).toCoGSLTLayer.Fiber base =
      (left.Fiber base × right.Fiber base) :=
  rfl

/-! ### Products of certified realizations -/

/-- Independent certified realizations assemble over the generic product
layer.  The artifact and the named observation are paired componentwise, so
adequacy of the composite is derived solely from adequacy of its components. -/
def productRealization
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {LeftObservation : Base → Type uObservationLeft}
    {RightObservation : Base → Type uObservationRight}
    (leftRealization : CoGSLTLayer.Realization left.toCoGSLTLayer
      LeftArtifact LeftObservation)
    (rightRealization : CoGSLTLayer.Realization right.toCoGSLTLayer
      RightArtifact RightObservation) :
    CoGSLTLayer.Realization (left.product right).toCoGSLTLayer
      (fun base => LeftArtifact base × RightArtifact base)
      (fun base => LeftObservation base × RightObservation base) :=
  leftRealization.product rightRealization

@[simp] theorem productRealization_compile
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {LeftObservation : Base → Type uObservationLeft}
    {RightObservation : Base → Type uObservationRight}
    (leftRealization : CoGSLTLayer.Realization left.toCoGSLTLayer
      LeftArtifact LeftObservation)
    (rightRealization : CoGSLTLayer.Realization right.toCoGSLTLayer
      RightArtifact RightObservation)
    (base : Base) (declarations : left.Fiber base × right.Fiber base) :
    (left.productRealization right leftRealization rightRealization).compile
        base declarations =
      (leftRealization.compile base declarations.1,
        rightRealization.compile base declarations.2) :=
  rfl

end CompositionalLayer

/-! ## Flat free-document layers

`CompositionalLayer` is the general interface: its authored term language may
have any internal representation of empty and concatenation.  Many important
layers satisfy a stronger property.  Their source is literally one free
document over a GSLT of declaration generators.  Retaining that generator
boundary lets products combine generators first and take the free-document
closure exactly once, instead of building documents of documents.

`FreeDocumentLayer` is this refinement.  Its map to `CompositionalLayer`
forgets only the chosen generators.  Unit, product, associator, unitors, and
braiding below are inherited from the corresponding GSLT constructions, while
the elaboration laws prove that the structural maps carry exactly the expected
payload maps.
-/

/-- An indexed family of exact elaborations from one flat free document over
an authored generator GSLT. -/
structure FreeDocumentLayer (Base : Type uBase) where
  /-- The payload attached over each base. -/
  Fiber : Base → Type uFiber
  /-- Generator GSLT, its single document closure, and exact elaboration. -/
  system : ∀ base, GSLT.FreeDocumentElaboration.{0, uFiber} (Fiber base)

namespace FreeDocumentLayer

variable {Base : Type uBase}

/-- A base-independent free-document elaboration regarded as an indexed
layer. -/
def constant (Base : Type uBase)
    {Payload : Type uFiber}
    (system : GSLT.FreeDocumentElaboration.{0, uFiber} Payload) :
    FreeDocumentLayer.{uBase, uFiber} Base where
  Fiber := fun _ => Payload
  system := fun _ => system

/-- Forget the chosen generator GSLT while retaining the exact compositional
elaboration. -/
def toCompositionalLayer
    (layer : FreeDocumentLayer.{uBase, uFiber} Base) :
    CompositionalLayer.{uBase, uFiber} Base where
  Fiber := layer.Fiber
  system := fun base => (layer.system base).toCompositionalElaboration

@[simp] theorem toCompositionalLayer_fiber
    (layer : FreeDocumentLayer.{uBase, uFiber} Base) (base : Base) :
    layer.toCompositionalLayer.Fiber base = layer.Fiber base :=
  rfl

/-- The one authored source GSLT at a fixed base. -/
def sourceGSLT
    (layer : FreeDocumentLayer.{uBase, uFiber} Base)
    (base : Base) : GSLT :=
  GSLT.freeDocument (layer.system base).generators

/-- Elaborate one flat authored document. -/
def elaborate
    (layer : FreeDocumentLayer.{uBase, uFiber} Base) (base : Base) :
    (layer.sourceGSLT base).Term → Option (layer.Fiber base) :=
  (layer.system base).elaboration.elaborate

/-- Canonical flat authored document for a payload. -/
def quote
    (layer : FreeDocumentLayer.{uBase, uFiber} Base) (base : Base) :
    layer.Fiber base → (layer.sourceGSLT base).Term :=
  (layer.system base).elaboration.quote

@[simp] theorem elaborate_quote
    (layer : FreeDocumentLayer.{uBase, uFiber} Base) (base : Base)
    (value : layer.Fiber base) :
    layer.elaborate base (layer.quote base value) = some value :=
  (layer.system base).elaboration.elaborate_quote value

/-- Forget the flat-document refinement at the ordinary coGSLT boundary. -/
def toCoGSLTLayer
    (layer : FreeDocumentLayer.{uBase, uFiber} Base) :
    CoGSLTLayer.{uBase, uFiber, 0} Base :=
  layer.toCompositionalLayer.toCoGSLTLayer

@[simp] theorem toCoGSLTLayer_sourceGSLT
    (layer : FreeDocumentLayer.{uBase, uFiber} Base) (base : Base) :
    layer.toCoGSLTLayer.sourceGSLT base = layer.sourceGSLT base :=
  rfl

@[simp] theorem toCoGSLTLayer_elaborate
    (layer : FreeDocumentLayer.{uBase, uFiber} Base) (base : Base) :
    layer.toCoGSLTLayer.elaborate base = layer.elaborate base :=
  rfl

/-! ### Symmetric flat composition -/

/-- The neutral layer has no generators and exactly one payload. -/
def unit (Base : Type uBase) : FreeDocumentLayer.{uBase, 0} Base :=
  constant Base GSLT.FreeDocumentElaboration.unit.{0}

/-- Flat layer product combines generator GSLTs first, then takes one
free-document closure. -/
def product
    (left : FreeDocumentLayer.{uBase, uFiber} Base)
    (right : FreeDocumentLayer.{uBase, uFiberRight} Base) :
    FreeDocumentLayer.{uBase, max uFiber uFiberRight} Base where
  Fiber := fun base => left.Fiber base × right.Fiber base
  system := fun base => (left.system base).product (right.system base)

@[simp] theorem product_fiber
    (left : FreeDocumentLayer.{uBase, uFiber} Base)
    (right : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (base : Base) :
    (left.product right).Fiber base =
      (left.Fiber base × right.Fiber base) :=
  rfl

@[simp] theorem product_generators
    (left : FreeDocumentLayer.{uBase, uFiber} Base)
    (right : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (base : Base) :
    ((left.product right).system base).generators =
      GSLT.disjointSum (left.system base).generators
        (right.system base).generators :=
  rfl

/-- The general nested product is a correct but non-canonical implementation
of the flat product.  Normalizing its component-document blocks yields exactly
the flat elaboration, so callers can use one flat source language without
losing any payload meaning. -/
theorem nested_product_elaboration_eq_flat
    (left : FreeDocumentLayer.{uBase, uFiber} Base)
    (right : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (base : Base)
    (source : List
      (List (left.system base).generators.Term ⊕
        List (right.system base).generators.Term)) :
    (left.toCompositionalLayer.product right.toCompositionalLayer).elaborate
        base source =
      (left.product right).elaborate base
        (GSLT.FreeDocumentProduct.flatten source) :=
  GSLT.FreeDocumentProduct.elaborate_genericProduct_eq_flatProduct
    (left.system base) (right.system base) source

/-- The flat product restricted to a left document is the left elaboration,
padded only by the right empty payload. -/
theorem product_elaborates_left_only
    (left : FreeDocumentLayer.{uBase, uFiber} Base)
    (right : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (base : Base) (source : List (left.system base).generators.Term) :
    (left.product right).elaborate base
        (source.map (Sum.inl : (left.system base).generators.Term →
          (left.system base).generators.Term ⊕
            (right.system base).generators.Term)) =
      (left.elaborate base source).map
        fun value => (value, (right.system base).emptyPayload) :=
  (left.system base).product_elaborates_left_only
    (right.system base) source

/-- The symmetric right restriction law. -/
theorem product_elaborates_right_only
    (left : FreeDocumentLayer.{uBase, uFiber} Base)
    (right : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (base : Base) (source : List (right.system base).generators.Term) :
    (left.product right).elaborate base
        (source.map (Sum.inr : (right.system base).generators.Term →
          (left.system base).generators.Term ⊕
            (right.system base).generators.Term)) =
      (right.elaborate base source).map
        fun value => ((left.system base).emptyPayload, value) :=
  (left.system base).product_elaborates_right_only
    (right.system base) source

/-- Rebracketing three flat layers is a structural isomorphism of their one
authored source GSLT. -/
def productAssociator
    (first : FreeDocumentLayer.{uBase, uFiber} Base)
    (second : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (third : FreeDocumentLayer.{uBase, uFiberThird} Base)
    (base : Base) :
    GSLT.StructuralIsomorphism
      (((first.product second).product third).sourceGSLT base)
      ((first.product (second.product third)).sourceGSLT base) :=
  GSLT.FreeDocumentElaboration.flatProductAssociator
    (first.system base) (second.system base) (third.system base)

/-- The structural associator carries elaboration to product reassociation. -/
theorem product_elaboration_associative
    (first : FreeDocumentLayer.{uBase, uFiber} Base)
    (second : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (third : FreeDocumentLayer.{uBase, uFiberThird} Base)
    (base : Base)
    (source : List
      (((first.system base).generators.Term ⊕
          (second.system base).generators.Term) ⊕
        (third.system base).generators.Term)) :
    ((((first.product second).product third).elaborate base source).map
        (Equiv.prodAssoc (first.Fiber base) (second.Fiber base)
          (third.Fiber base))) =
      (first.product (second.product third)).elaborate base
        ((productAssociator first second third base).termEquiv source) :=
  GSLT.FreeDocumentElaboration.product_elaboration_associative
    (first.system base) (second.system base) (third.system base) source

/-- Removing the neutral left layer is a structural isomorphism of the one
authored source GSLT. -/
def productLeftUnitor
    (layer : FreeDocumentLayer.{uBase, uFiber} Base)
    (base : Base) :
    GSLT.StructuralIsomorphism
      ((((unit Base).product layer).sourceGSLT base))
      (layer.sourceGSLT base) :=
  GSLT.FreeDocumentElaboration.flatProductLeftUnitor.{uFiber, 0}
    (layer.system base)

/-- The left unitor removes exactly the neutral `PUnit` payload. -/
theorem product_elaboration_left_unit
    (layer : FreeDocumentLayer.{uBase, uFiber} Base)
    (base : Base)
    (source : List
      (GSLT.disjointSumUnit.Term ⊕ (layer.system base).generators.Term)) :
    ((((unit Base).product layer).elaborate base source).map
        (Equiv.punitProd (layer.Fiber base))) =
      layer.elaborate base ((productLeftUnitor layer base).termEquiv source) :=
  by
    have unitorAction :=
      GSLT.FreeDocumentElaboration.flatProductLeftUnitor_apply.{uFiber, 0}
        (layer.system base) source
    calc
      ((((unit Base).product layer).elaborate base source).map
          (Equiv.punitProd (layer.Fiber base))) =
          (layer.system base).elaboration.elaborate
            (GSLT.MixedDocument.right source) :=
        GSLT.FreeDocumentElaboration.product_elaboration_left_unit.{uFiber, 0}
          (layer.system base) source
      _ = (layer.system base).elaboration.elaborate
          ((GSLT.FreeDocumentElaboration.flatProductLeftUnitor.{uFiber, 0}
            (layer.system base)).termEquiv source) :=
        congrArg (layer.system base).elaboration.elaborate
          unitorAction.symm
      _ = layer.elaborate base
          ((productLeftUnitor layer base).termEquiv source) := rfl

/-- Removing the neutral right layer is a structural isomorphism of the one
authored source GSLT. -/
def productRightUnitor
    (layer : FreeDocumentLayer.{uBase, uFiber} Base)
    (base : Base) :
    GSLT.StructuralIsomorphism
      (((layer.product (unit Base)).sourceGSLT base))
      (layer.sourceGSLT base) :=
  GSLT.FreeDocumentElaboration.flatProductRightUnitor.{uFiber, 0}
    (layer.system base)

/-- The right unitor removes exactly the neutral `PUnit` payload. -/
theorem product_elaboration_right_unit
    (layer : FreeDocumentLayer.{uBase, uFiber} Base)
    (base : Base)
    (source : List
      ((layer.system base).generators.Term ⊕ GSLT.disjointSumUnit.Term)) :
    (((layer.product (unit Base)).elaborate base source).map
        (Equiv.prodPUnit (layer.Fiber base))) =
      layer.elaborate base ((productRightUnitor layer base).termEquiv source) :=
  by
    have unitorAction :=
      GSLT.FreeDocumentElaboration.flatProductRightUnitor_apply.{uFiber, 0}
        (layer.system base) source
    calc
      (((layer.product (unit Base)).elaborate base source).map
          (Equiv.prodPUnit (layer.Fiber base))) =
          (layer.system base).elaboration.elaborate
            (GSLT.MixedDocument.left source) :=
        GSLT.FreeDocumentElaboration.product_elaboration_right_unit.{uFiber, 0}
          (layer.system base) source
      _ = (layer.system base).elaboration.elaborate
          ((GSLT.FreeDocumentElaboration.flatProductRightUnitor.{uFiber, 0}
            (layer.system base)).termEquiv source) :=
        congrArg (layer.system base).elaboration.elaborate
          unitorAction.symm
      _ = layer.elaborate base
          ((productRightUnitor layer base).termEquiv source) := rfl

/-- Exchanging two flat layers is a structural isomorphism of their one
authored source GSLT. -/
def productBraiding
    (left : FreeDocumentLayer.{uBase, uFiber} Base)
    (right : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (base : Base) :
    GSLT.StructuralIsomorphism
      ((left.product right).sourceGSLT base)
      ((right.product left).sourceGSLT base) :=
  GSLT.FreeDocumentElaboration.flatProductBraiding
    (left.system base) (right.system base)

/-- Braiding the source exchanges exactly the two payload coordinates. -/
theorem product_elaboration_commutative
    (left : FreeDocumentLayer.{uBase, uFiber} Base)
    (right : FreeDocumentLayer.{uBase, uFiberRight} Base)
    (base : Base)
    (source : List
      ((left.system base).generators.Term ⊕
        (right.system base).generators.Term)) :
    (((left.product right).elaborate base source).map
        (Equiv.prodComm (left.Fiber base) (right.Fiber base))) =
      (right.product left).elaborate base
        ((productBraiding left right base).termEquiv source) :=
  GSLT.FreeDocumentElaboration.product_elaboration_commutative
    (left.system base) (right.system base) source

/-! ### Executable separation controls -/

namespace Canary

private def naturals : FreeDocumentLayer Unit :=
  constant Unit (GSLT.FreeDocumentElaboration.orderedList Nat)

private def booleans : FreeDocumentLayer Unit :=
  constant Unit (GSLT.FreeDocumentElaboration.orderedList Bool)

/-- Positive: two independently authored layers elaborate from one interleaved
flat document. -/
example :
    (naturals.product booleans).elaborate ()
      [Sum.inl (2 : Nat), Sum.inr true, Sum.inl (5 : Nat), Sum.inr false] =
        some ([2, 5], [true, false]) :=
  rfl

/-- Negative: flat composition does not erase the right payload. -/
theorem right_payload_is_observable :
    (naturals.product booleans).elaborate ()
        [Sum.inl (2 : Nat), Sum.inr true] ≠
      (naturals.product booleans).elaborate ()
        [Sum.inl (2 : Nat), Sum.inr false] := by
  intro equality
  change some (([2] : List Nat), ([true] : List Bool)) =
    some (([2] : List Nat), ([false] : List Bool)) at equality
  have payloadEquality :
      (([2] : List Nat), ([true] : List Bool)) =
        (([2] : List Nat), ([false] : List Bool)) :=
    Option.some.inj equality
  have headEquality : some true = some false :=
    congrArg (fun payload => payload.2.head?) payloadEquality
  exact Bool.noConfusion (Option.some.inj headEquality)

end Canary

end FreeDocumentLayer

/-! ## The inference extension is compositional -/

/-- The generic partial-monoid fold is exactly the established calculus
elaborator. -/
theorem foldWith_proofCalculus_eq_elaborate :
    ∀ source : CalculusSyntax,
      foldWith proofCalculusMonoid elaborateDeclaration source =
        elaborate source
  | [] => rfl
  | declaration :: declarations => by
      change
        (foldWith proofCalculusMonoid elaborateDeclaration declarations).bind
            (fun tail =>
              (elaborateDeclaration declaration).append? tail) =
          (elaborate declarations).bind fun tail =>
            (elaborateDeclaration declaration).append? tail
      rw [foldWith_proofCalculus_eq_elaborate declarations]

/-- The one canonical compositional elaboration of authored proof-calculus
documents.  Both the general extension layer and the admitted calculus layer
below reuse this object; there is no second construction whose laws could
drift. -/
def calculusAuthoringGSLT : GSLT.FreeDocumentElaboration ProofCalculus where
  generators := calculusDeclarationGSLT
  elaboration :=
    { elaborate := elaborate
      equation := elaborate_equation
      rewrite := elaborate_rewrite
      quote := quote
      elaborate_quote := elaborate_quote }
  emptyPayload := .empty
  merge := ProofCalculus.append?
  elaborate_empty := elaborate_empty
  elaborate_append := elaborate_append

/-- The calculus declarations as a flat indexed authoring layer.  This is the
generator-preserving refinement used for products that must not nest authored
documents. -/
def calculusAuthoringLayer : FreeDocumentLayer LanguageDef :=
  FreeDocumentLayer.constant LanguageDef calculusAuthoringGSLT

/-- The proof-calculus extension with its complete compositional structure.
Its atom theory is the authored calculus-declaration GSLT, not a newly
generated rewrite-free wrapper. -/
def calculusLayer : CompositionalLayer LanguageDef :=
  calculusAuthoringLayer.toCompositionalLayer

/-- The generic compositional construction recovers the established authored
calculus GSLT definitionally. -/
@[simp] theorem calculusLayer_sourceGSLT (language : LanguageDef) :
    calculusLayer.toCoGSLTLayer.sourceGSLT language = calculusSyntaxGSLT :=
  rfl

/-- The generic compositional construction uses the established calculus
elaborator, not a parallel decoder. -/
@[simp] theorem calculusLayer_elaborate (language : LanguageDef)
    (source : CalculusSyntax) :
    calculusLayer.toCoGSLTLayer.elaborate language source = elaborate source :=
  rfl

/-- Canonical quotation is also shared definitionally. -/
@[simp] theorem calculusLayer_quote (language : LanguageDef)
    (calculus : ProofCalculus) :
    calculusLayer.toCoGSLTLayer.quote language calculus = quote calculus :=
  rfl

/-! ## The empty meaning is semantic data

Why a bare `CoGSLTLayer` cannot be composed: the value the composite assigns to
a document that mentions no right-hand declaration still depends on the right
layer.  Two right-hand layers over one carrier make that dependence visible. -/

private def trivialMonoid : PartialMonoid Unit where
  unit := ()
  op := fun _ _ => some ()
  unit_op := fun _ => rfl
  op_unit := fun _ => rfl
  op_assoc := fun _ _ _ => rfl

private def trivialLayer : CompositionalLayer Unit where
  Fiber := fun _ => Unit
  system := fun _ =>
    { authoring := GSLT.freeDocumentCompositional (GSLT.discrete Unit)
      elaboration :=
        { elaborate := fun _ => some ()
          equation := by intro _ _ _; rfl
          rewrite := by intro _ _ _; rfl
          quote := fun _ => []
          elaborate_quote := fun _ => rfl }
      emptyPayload := ()
      merge := trivialMonoid.op
      elaborate_empty := rfl
      elaborate_append := by intro _ _; rfl }

private def orMonoid : PartialMonoid Bool where
  unit := false
  op := fun first second => some (first || second)
  unit_op := by intro value; simp
  op_unit := by intro value; simp
  op_assoc := by intro first second third; simp [Bool.or_assoc]

private def andMonoid : PartialMonoid Bool where
  unit := true
  op := fun first second => some (first && second)
  unit_op := by intro value; simp
  op_unit := by intro value; simp
  op_assoc := by intro first second third; simp [Bool.and_assoc]

private def orFlagLayer : CompositionalLayer Unit where
  Fiber := fun _ => Bool
  system := fun _ =>
    { authoring := GSLT.freeDocumentCompositional (GSLT.discrete Unit)
      elaboration :=
        { elaborate := foldWith orMonoid fun _ => true
          equation := by
            intro source target equivalent
            have equal := GSLT.DocumentEquiv.eq_of
              (fun {left right} component => by
                change left = right at component
                exact component) equivalent
            subst target
            rfl
          rewrite := by
            intro source target step
            rcases step with
              ⟨_, _, _, raw, _⟩
            exact (GSLT.RawDocumentStep.false_of_no_step
              (fun {left right} impossible => by
                change False at impossible
                exact impossible) raw).elim
          quote := fun flag => if flag then [()] else []
          elaborate_quote := by intro flag; cases flag <;> rfl }
      emptyPayload := false
      merge := orMonoid.op
      elaborate_empty := rfl
      elaborate_append := foldWith_append orMonoid (fun _ => true) }

private def andFlagLayer : CompositionalLayer Unit where
  Fiber := fun _ => Bool
  system := fun _ =>
    { authoring := GSLT.freeDocumentCompositional (GSLT.discrete Unit)
      elaboration :=
        { elaborate := foldWith andMonoid fun _ => false
          equation := by
            intro source target equivalent
            have equal := GSLT.DocumentEquiv.eq_of
              (fun {left right} component => by
                change left = right at component
                exact component) equivalent
            subst target
            rfl
          rewrite := by
            intro source target step
            rcases step with
              ⟨_, _, _, raw, _⟩
            exact (GSLT.RawDocumentStep.false_of_no_step
              (fun {left right} impossible => by
                change False at impossible
                exact impossible) raw).elim
          quote := fun flag => if flag then [] else [()]
          elaborate_quote := by intro flag; cases flag <;> rfl }
      emptyPayload := true
      merge := andMonoid.op
      elaborate_empty := rfl
      elaborate_append := foldWith_append andMonoid (fun _ => false) }

private theorem orComposite_left_only :
    (trivialLayer.product orFlagLayer).elaborate () [Sum.inl [()]] =
      some ((), false) :=
  rfl

private theorem andComposite_left_only :
    (trivialLayer.product andFlagLayer).elaborate () [Sum.inl [()]] =
      some ((), true) :=
  rfl

/-- **The meaning of an empty authored term matters.**  One and the same
left-hand document elaborates to different payloads under two composites whose
right-hand elaborators assign different meanings to their empty term.  A bare
`CoGSLTLayer` names neither composition nor its empty term, so it supplies no
canonical padding value. -/
theorem padding_is_authored :
    ((trivialLayer.product orFlagLayer).elaborate () [Sum.inl [()]]).map Prod.snd ≠
      ((trivialLayer.product andFlagLayer).elaborate () [Sum.inl [()]]).map
        Prod.snd := by
  intro equality
  rw [orComposite_left_only, andComposite_left_only] at equality
  exact Bool.noConfusion (Option.some.inj equality)

private def canaryJudgment : JudgmentDecl := ⟨"Canary", 1⟩

private def canaryCalculus : ProofCalculus := { judgments := [canaryJudgment] }

/-! ## The overlap condition

What compatible means for two authored proof calculi, and the part of it the
partial monoid already enforces. -/

/-- Two authored calculi overlap cleanly: no shared judgment head, no shared
rule identifier, and at most one rooted conversion authority. -/
structure Compatible (first second : ProofCalculus) : Prop where
  /-- Judgment heads are disjoint. -/
  judgmentHeads : ∀ head ∈ first.judgments.map JudgmentDecl.head,
    head ∉ second.judgments.map JudgmentDecl.head
  /-- Rule identifiers are disjoint. -/
  ruleIds : ∀ id ∈ first.rules.map RuleSchema.id,
    id ∉ second.rules.map RuleSchema.id
  /-- At most one side roots a conversion interface. -/
  conversion : first.conversion = none ∨ second.conversion = none

/-- Compatible calculi always merge as authored data. -/
theorem append_isSome_of_compatible {first second : ProofCalculus}
    (compatible : Compatible first second) :
    (proofCalculusMonoid.op first second).isSome := by
  cases compatible.conversion with
  | inl firstNone =>
      cases hsecond : second.conversion <;>
        simp [proofCalculusMonoid, ProofCalculus.append?, firstNone, hsecond]
  | inr secondNone =>
      cases hfirst : first.conversion <;>
        simp [proofCalculusMonoid, ProofCalculus.append?, hfirst, secondNone]

/-- The counterexample above is incompatible, as it must be: it declares one
judgment head twice. -/
theorem canary_not_compatible : ¬ Compatible canaryCalculus canaryCalculus := by
  intro compatible
  have member : canaryJudgment.head ∈
      canaryCalculus.judgments.map JudgmentDecl.head := by
    simp [canaryCalculus]
  exact compatible.judgmentHeads canaryJudgment.head member member

/-! ## Where this sits

Composition of authored extension languages is settled here: `product` is
total, its round trip is proved, and both restriction laws hold.  The
compatibility relation and the negative result are here too, so the boundary
between the two regimes is visible in one place.

The gluing law over that boundary is `ExtensionGluing.gluing_of_compatible`.

Two things this does **not** claim.  Nothing here compiles an extension into
core rewrites, so no interpreter/compiler agreement is asserted — that is the
staging theorem and it is untouched.  And a fibration with a gluing law on
pairwise overlaps is not yet descent: descent needs covers, and no notion of
cover is defined for language cores.
-/

end Mettapedia.GSLT.LanguageDef.ExtensionComposition
