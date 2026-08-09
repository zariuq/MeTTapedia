import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Language-definition extensions as indexed GSLT layers

A language definition and a tool's realization of that language are different
objects.  This module supplies the neutral boundary between them.

An `ExtensionLayer Base` is an indexed family of declarations over a base.  Its
Grothendieck total space stores a base together with one declaration in the
fibre above it; `erase` forgets only the declaration.  Products glue independent
layers over the same base without merging their schemas.

`CoGSLTLayer` adds an authored GSLT for the extension language itself.  Its
elaborator is required to respect both equations and rewrites, while quotation
is a section of elaboration.  A compiler or runtime `Realization` is separate
and must carry an observation-indexed adequacy certificate; it is not a field
of either the base language or the extension language.

The conservativity notion here is deliberately observation-indexed.  Attaching
data automatically preserves observations that factor through `erase`; it does
not assert that every possible semantics ignores the new layer.  Components
such as proof presentations satisfy the former condition, whereas a logic or
native-operation layer may intentionally add observable behaviour and must
prove its own stronger law.
-/

namespace Mettapedia.GSLT.LanguageDef.Extension

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization

universe uBase uFiber uFiber' uArtifact uObservation uTerm

/-- A typed family of extension declarations indexed by a base object. -/
structure ExtensionLayer (Base : Type uBase) where
  Fiber : Base → Type uFiber

namespace ExtensionLayer

/-- The total space of a layer: a base paired with data in its fibre. -/
abbrev Total {Base : Type uBase} (layer : ExtensionLayer.{uBase, uFiber} Base) :=
  Σ base, layer.Fiber base

/-- Forget an attached declaration and recover its exact base. -/
def erase {Base : Type uBase} {layer : ExtensionLayer.{uBase, uFiber} Base} :
    layer.Total → Base :=
  Sigma.fst

/-- Attach one declaration to the base over which it is indexed. -/
def attach {Base : Type uBase} (layer : ExtensionLayer.{uBase, uFiber} Base)
    (base : Base) (declaration : layer.Fiber base) : layer.Total :=
  ⟨base, declaration⟩

@[simp] theorem erase_attach {Base : Type uBase}
    (layer : ExtensionLayer.{uBase, uFiber} Base) (base : Base)
    (declaration : layer.Fiber base) :
    layer.erase (layer.attach base declaration) = base :=
  rfl

/-- The empty layer, with exactly one declaration over every base. -/
def unit (Base : Type uBase) : ExtensionLayer.{uBase, 0} Base where
  Fiber := fun _ => Unit

/-- Fibrewise product: independent components are glued at the same base. -/
def product {Base : Type uBase}
    (left : ExtensionLayer.{uBase, uFiber} Base)
    (right : ExtensionLayer.{uBase, uFiber'} Base) :
    ExtensionLayer.{uBase, max uFiber uFiber'} Base where
  Fiber := fun base => left.Fiber base × right.Fiber base

/-- Glue two declarations that are already known to lie over the same base. -/
def glueAt {Base : Type uBase}
    (left : ExtensionLayer.{uBase, uFiber} Base)
    (right : ExtensionLayer.{uBase, uFiber'} Base) (base : Base)
    (leftDeclaration : left.Fiber base)
    (rightDeclaration : right.Fiber base) :
    (left.product right).Fiber base :=
  (leftDeclaration, rightDeclaration)

@[simp] theorem glueAt_left {Base : Type uBase}
    (left : ExtensionLayer.{uBase, uFiber} Base)
    (right : ExtensionLayer.{uBase, uFiber'} Base) (base : Base)
    (leftDeclaration : left.Fiber base)
    (rightDeclaration : right.Fiber base) :
    (left.glueAt right base leftDeclaration rightDeclaration).1 =
      leftDeclaration :=
  rfl

@[simp] theorem glueAt_right {Base : Type uBase}
    (left : ExtensionLayer.{uBase, uFiber} Base)
    (right : ExtensionLayer.{uBase, uFiber'} Base) (base : Base)
    (leftDeclaration : left.Fiber base)
    (rightDeclaration : right.Fiber base) :
    (left.glueAt right base leftDeclaration rightDeclaration).2 =
      rightDeclaration :=
  rfl

/-- Reassociate three independently glued layers without changing data. -/
def productAssocEquiv {Base : Type uBase}
    (first : ExtensionLayer.{uBase, uFiber} Base)
    (second : ExtensionLayer.{uBase, uFiber'} Base)
    (third : ExtensionLayer.{uBase, uArtifact} Base) (base : Base) :
    ((first.product second).product third).Fiber base ≃
      (first.product (second.product third)).Fiber base where
  toFun := fun declaration =>
    (declaration.1.1, declaration.1.2, declaration.2)
  invFun := fun declaration =>
    ((declaration.1, declaration.2.1), declaration.2.2)
  left_inv := fun declaration => by cases declaration; rfl
  right_inv := fun declaration => by cases declaration; rfl

/-- Reindex a layer along a map of bases. -/
def reindex {Base' : Type*} {Base : Type uBase}
    (map : Base' → Base) (layer : ExtensionLayer.{uBase, uFiber} Base) :
    ExtensionLayer Base' where
  Fiber := fun base => layer.Fiber (map base)

/-- A map between layers that never changes the underlying base. -/
structure Hom {Base : Type uBase}
    (source : ExtensionLayer.{uBase, uFiber} Base)
    (target : ExtensionLayer.{uBase, uFiber'} Base) where
  map : ∀ base, source.Fiber base → target.Fiber base

namespace Hom

def id {Base : Type uBase}
    (layer : ExtensionLayer.{uBase, uFiber} Base) : Hom layer layer where
  map := fun _ declaration => declaration

def comp {Base : Type uBase}
    {first : ExtensionLayer.{uBase, uFiber} Base}
    {second : ExtensionLayer.{uBase, uFiber'} Base}
    {third : ExtensionLayer.{uBase, uArtifact} Base}
    (after : Hom second third) (before : Hom first second) : Hom first third where
  map := fun base declaration => after.map base (before.map base declaration)

@[simp] theorem id_map {Base : Type uBase}
    (layer : ExtensionLayer.{uBase, uFiber} Base) (base : Base)
    (declaration : layer.Fiber base) :
    (id layer).map base declaration = declaration :=
  rfl

@[simp] theorem comp_map {Base : Type uBase}
    {first : ExtensionLayer.{uBase, uFiber} Base}
    {second : ExtensionLayer.{uBase, uFiber'} Base}
    {third : ExtensionLayer.{uBase, uArtifact} Base}
    (after : Hom second third) (before : Hom first second) (base : Base)
    (declaration : first.Fiber base) :
    (comp after before).map base declaration =
      after.map base (before.map base declaration) :=
  rfl

end Hom

/-! ## Observation-indexed conservativity -/

/-- An extended observation is conservative when it sees only the erased base. -/
def Conserves {Base : Type uBase} {Observation : Type uObservation}
    (layer : ExtensionLayer.{uBase, uFiber} Base)
    (observeBase : Base → Observation)
    (observeExtended : layer.Total → Observation) : Prop :=
  ∀ attached, observeExtended attached = observeBase (layer.erase attached)

/-- Every base observation has a canonical conservative lift. -/
def liftObservation {Base : Type uBase}
    (layer : ExtensionLayer.{uBase, uFiber} Base)
    {Observation : Type uObservation} (observe : Base → Observation) :
    layer.Total → Observation :=
  observe ∘ layer.erase

@[simp] theorem liftObservation_attach {Base : Type uBase}
    (layer : ExtensionLayer.{uBase, uFiber} Base)
    {Observation : Type uObservation} (observe : Base → Observation)
    (base : Base) (declaration : layer.Fiber base) :
    layer.liftObservation observe (layer.attach base declaration) =
      observe base :=
  rfl

/-- The canonical lift preserves the base observation exactly. -/
theorem liftObservation_conservative {Base : Type uBase}
    (layer : ExtensionLayer.{uBase, uFiber} Base)
    {Observation : Type uObservation} (observe : Base → Observation) :
    ∀ attached,
      layer.liftObservation observe attached = observe (layer.erase attached) :=
  fun _ => rfl

end ExtensionLayer

/-! ## A GSLT-authored extension language -/

/-- An extension layer whose own syntax and sugar are specified by a GSLT.

`elaborate` is invariant under both authored equations and one-step rewrites.
Thus a syntax-sugar rewrite cannot change which extension declaration the
source denotes.  `quote` chooses a canonical source representative. -/
structure CoGSLTLayer (Base : Type uBase) extends
    ExtensionLayer.{uBase, uFiber} Base where
  sourceGSLT : Base → GSLT.{uTerm}
  elaborate : ∀ base, (sourceGSLT base).Term → Option (Fiber base)
  quote : ∀ base, Fiber base → (sourceGSLT base).Term
  elaborate_quote : ∀ base declaration,
    elaborate base (quote base declaration) = some declaration
  elaborate_equation : ∀ base
      {source target : (sourceGSLT base).Term},
    (sourceGSLT base).Equiv source target →
      elaborate base source = elaborate base target
  elaborate_rewrite : ∀ base
      {source target : (sourceGSLT base).Term},
    (sourceGSLT base).Step source target →
      elaborate base source = elaborate base target

namespace CoGSLTLayer

/-- The non-indexed exact elaboration obtained by fixing one base.  This is
the bridge from dependent language-definition layers to the general GSLT
elaboration interface. -/
def elaborationAt {Base : Type uBase}
    (layer : CoGSLTLayer.{uBase, uFiber, uTerm} Base) (base : Base) :
    GSLT.ExactElaboration (layer.sourceGSLT base) (layer.Fiber base) where
  elaborate := layer.elaborate base
  equation := layer.elaborate_equation base
  rewrite := layer.elaborate_rewrite base
  quote := layer.quote base
  elaborate_quote := layer.elaborate_quote base

/-- Quotation in every coGSLT layer is injective at a fixed base. -/
theorem quote_injective {Base : Type uBase}
    (layer : CoGSLTLayer.{uBase, uFiber, uTerm} Base) (base : Base) :
    Function.Injective (layer.quote base) :=
  (layer.elaborationAt base).quote_injective

/-- A certified staged realization specialized to the elaborated fibres of a
coGSLT layer.  Its implementation and laws are the generic
`Mettapedia.GSLT.Realization`; this abbreviation adds no second authority. -/
abbrev Realization {Base : Type uBase}
    (layer : CoGSLTLayer Base)
    (Artifact : Base → Type uArtifact)
    (Observation : Base → Type uObservation) :=
  Mettapedia.GSLT.Realization layer.Fiber Artifact Observation

/-- Elaborate authored syntax and compile only after elaboration succeeds. -/
def Realization.compileTerm? {Base : Type uBase}
    {layer : CoGSLTLayer Base}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization layer Artifact Observation) (base : Base)
    (source : (layer.sourceGSLT base).Term) : Option (Artifact base) := do
  let declaration ← layer.elaborate base source
  pure (realization.compile base declaration)

/-- **End-to-end staging adequacy.**  Elaborating and compiling an authored
GSLT term, then observing the artifact, gives exactly the semantic observation
of the elaborated payload.  Failed elaboration remains `none` on both sides. -/
theorem Realization.compileTerm?_adequate {Base : Type uBase}
    {layer : CoGSLTLayer Base}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization layer Artifact Observation) (base : Base)
    (source : (layer.sourceGSLT base).Term) :
    (realization.compileTerm? base source).map
        (realization.observeArtifact base) =
      (layer.elaborate base source).map
        (realization.observeSource base) := by
  unfold Realization.compileTerm?
  cases elaborated : layer.elaborate base source with
  | none => rfl
  | some declaration =>
      exact congrArg some (realization.adequate base declaration)

/-- A rejected authored term cannot acquire a backend artifact through the
certified staging interface. -/
theorem Realization.compileTerm?_eq_none_of_elaborate_eq_none
    {Base : Type uBase}
    {layer : CoGSLTLayer Base}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization layer Artifact Observation) (base : Base)
    (source : (layer.sourceGSLT base).Term)
    (rejected : layer.elaborate base source = none) :
    realization.compileTerm? base source = none := by
  simp [Realization.compileTerm?, rejected]

/-- Quoted canonical declarations compile to the realization of the original
declaration. -/
@[simp] theorem Realization.compileTerm_quote {Base : Type uBase}
    {layer : CoGSLTLayer Base}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization layer Artifact Observation) (base : Base)
    (declaration : layer.Fiber base) :
    realization.compileTerm? base (layer.quote base declaration) =
      some (realization.compile base declaration) := by
  simp [Realization.compileTerm?, layer.elaborate_quote]

/-- Canonically quoted declarations have exactly their payload observation. -/
@[simp] theorem Realization.observeSource_quote {Base : Type uBase}
    {layer : CoGSLTLayer Base}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization layer Artifact Observation) (base : Base)
    (declaration : layer.Fiber base) :
    (layer.elaborate base (layer.quote base declaration)).map
        (realization.observeSource base) =
      some (realization.observeSource base declaration) := by
  simp [layer.elaborate_quote]

/-- The certificate is the common semantic interface for every realization. -/
@[simp] theorem Realization.observe_compile {Base : Type uBase}
    {layer : CoGSLTLayer Base}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization layer Artifact Observation) (base : Base)
    (declaration : layer.Fiber base) :
    realization.observeArtifact base (realization.compile base declaration) =
      realization.observeSource base declaration :=
  realization.adequate base declaration

/-- Compilation cannot distinguish equated syntax presentations. -/
theorem Realization.compileTerm?_eq_of_equation {Base : Type uBase}
    {layer : CoGSLTLayer Base}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization layer Artifact Observation) (base : Base)
    {source target : (layer.sourceGSLT base).Term}
    (equivalent : (layer.sourceGSLT base).Equiv source target) :
    realization.compileTerm? base source =
      realization.compileTerm? base target := by
  simp only [Realization.compileTerm?]
  rw [layer.elaborate_equation base equivalent]

/-- Compilation cannot distinguish a syntax term from one of its authored
sugar-rewrite successors. -/
theorem Realization.compileTerm?_eq_of_rewrite {Base : Type uBase}
    {layer : CoGSLTLayer Base}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization layer Artifact Observation) (base : Base)
    {source target : (layer.sourceGSLT base).Term}
    (step : (layer.sourceGSLT base).Step source target) :
    realization.compileTerm? base source =
      realization.compileTerm? base target := by
  simp only [Realization.compileTerm?]
  rw [layer.elaborate_rewrite base step]

end CoGSLTLayer

/-! ## Reusable declaration-document coGSLTs -/

/-- A small authored document language for extension declarations.  Bundles
may nest; elaboration flattens them in authored order. -/
inductive DeclarationDocument (Declaration : Type uTerm) where
  | declaration (value : Declaration)
  | bundle (documents : List (DeclarationDocument Declaration))
deriving Repr

namespace DeclarationDocument

mutual

def values : DeclarationDocument Declaration → List Declaration
  | .declaration value => [value]
  | .bundle documents => valuesList documents
termination_by document => sizeOf document

def valuesList : List (DeclarationDocument Declaration) → List Declaration
  | [] => []
  | document :: documents => values document ++ valuesList documents
termination_by documents => sizeOf documents

end


@[simp] theorem values_bundle_map (declarations : List Declaration) :
    values (.bundle (declarations.map DeclarationDocument.declaration)) =
      declarations := by
  simp only [values]
  induction declarations with
  | nil => simp [valuesList]
  | cons declaration declarations inductionHypothesis =>
      simp [valuesList, values, inductionHypothesis]

end DeclarationDocument

/-- An exact structural codec from authored declaration syntax to the payload
consumed by a validated extension. -/
structure ExactDeclarationCodec (Syntax : Type uTerm)
    (Payload : Type uFiber) where
  encode : Payload → Syntax
  decode : Syntax → Payload
  decode_encode : ∀ payload, decode (encode payload) = payload
  encode_decode : ∀ source, encode (decode source) = source

/-- The reusable class of GSLTs that author finite declaration sequences.
Different declaration grammars specialize the source terms; the payload is
always the ordered list obtained by exact elaboration. -/
abbrev DeclarationAuthoringGSLT (Payload : Type uFiber) :=
  GSLT.CompositionalElaboration (List Payload)

namespace ExactDeclarationCodec

/-- Elaborate a declaration document by decoding and flattening it. -/
def elaborate (codec : ExactDeclarationCodec Syntax Payload)
    (source : DeclarationDocument Syntax) : List Payload :=
  source.values.map codec.decode

/-- Quote a payload list as one canonical flat declaration bundle. -/
def quote (codec : ExactDeclarationCodec Syntax Payload)
    (payloads : List Payload) : DeclarationDocument Syntax :=
  .bundle (payloads.map fun payload => .declaration (codec.encode payload))

@[simp] theorem elaborate_quote
    (codec : ExactDeclarationCodec Syntax Payload) (payloads : List Payload) :
    codec.elaborate (codec.quote payloads) = payloads := by
  unfold elaborate quote
  have mapDeclaration :
      payloads.map (fun payload =>
          DeclarationDocument.declaration (codec.encode payload)) =
        (payloads.map codec.encode).map
          DeclarationDocument.declaration := by
    simp [List.map_map, Function.comp_def]
  rw [mapDeclaration]
  rw [DeclarationDocument.values_bundle_map]
  clear mapDeclaration
  induction payloads with
  | nil => rfl
  | cons payload payloads inductionHypothesis =>
      simp only [List.map_cons]
      rw [codec.decode_encode payload, inductionHypothesis]

/-- Two declaration documents are equivalent exactly when they flatten to
the same declaration sequence.  Bundle nesting and empty bundles are thereby
authored equations rather than elaborator-only conventions. -/
def DeclarationDocumentEquiv (source target : DeclarationDocument Syntax) : Prop :=
  source.values = target.values

/-- The declaration document as a GSLT.  Its equations identify precisely the
bundle trees with the same ordered declarations; it has no primitive semantic
rewrite.  Component-specific sugar can layer rewrites before this canonical
document language. -/
def documentGSLT (Syntax : Type) : GSLT where
  Term := DeclarationDocument Syntax
  equations :=
    { r := DeclarationDocumentEquiv
      iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ impossible
    exact False.elim impossible
  rewrites_resp_right := by
    intro _ _ _ impossible _
    exact False.elim impossible

/-- Codec elaboration is well defined on the declaration-document
equations. -/
theorem elaborate_equation (codec : ExactDeclarationCodec Syntax Payload)
    {source target : DeclarationDocument Syntax}
    (equivalent : (documentGSLT Syntax).Equiv source target) :
    codec.elaborate source = codec.elaborate target := by
  change source.values = target.values at equivalent
  simp [ExactDeclarationCodec.elaborate, equivalent]

/-- Declaration documents carry empty and concatenation internally to their
GSLT.  Concatenation builds one bundle node; the monoid laws hold through the
flattening equations. -/
def documentCompositional (Syntax : Type) : GSLT.Compositional where
  theory := documentGSLT Syntax
  empty := .bundle []
  append := fun first second => .bundle [first, second]
  empty_append := by
    intro document
    change DeclarationDocumentEquiv (.bundle [.bundle [], document]) document
    simp [DeclarationDocumentEquiv, DeclarationDocument.values,
      DeclarationDocument.valuesList]
  append_empty := by
    intro document
    change DeclarationDocumentEquiv (.bundle [document, .bundle []]) document
    simp [DeclarationDocumentEquiv, DeclarationDocument.values,
      DeclarationDocument.valuesList]
  append_assoc := by
    intro first second third
    change DeclarationDocumentEquiv
      (.bundle [.bundle [first, second], third])
      (.bundle [first, .bundle [second, third]])
    simp [DeclarationDocumentEquiv, DeclarationDocument.values,
      DeclarationDocument.valuesList, List.append_assoc]
  append_equiv := by
    intro first first' second second' firstEquivalent secondEquivalent
    change first.values = first'.values at firstEquivalent
    change second.values = second'.values at secondEquivalent
    change DeclarationDocumentEquiv (.bundle [first, second])
      (.bundle [first', second'])
    simp [DeclarationDocumentEquiv, DeclarationDocument.values,
      DeclarationDocument.valuesList, firstEquivalent, secondEquivalent]
  append_step_left := by
    intro _ _ impossible _
    exact False.elim impossible
  append_step_right := by
    intro _ _ _ impossible
    exact False.elim impossible

/-- Every exact declaration codec is automatically a compositional
elaboration.  Payload composition is ordered list concatenation, and its
algebraic laws are consequently derived from the authored bundle equations. -/
def compositionalElaboration {Syntax : Type} {Payload : Type uFiber}
    (codec : ExactDeclarationCodec Syntax Payload) :
    DeclarationAuthoringGSLT Payload where
  authoring := documentCompositional Syntax
  elaboration :=
    { elaborate := fun source => some (codec.elaborate source)
      equation := by
        intro source target equivalent
        rw [codec.elaborate_equation equivalent]
      rewrite := by
        intro _ _ impossible
        exact False.elim impossible
      quote := codec.quote
      elaborate_quote := by
        intro payloads
        simp [ExactDeclarationCodec.elaborate_quote] }
  emptyPayload := []
  merge := fun first second => some (first ++ second)
  elaborate_empty := by
    simp [documentCompositional, ExactDeclarationCodec.elaborate,
      DeclarationDocument.values, DeclarationDocument.valuesList]
  elaborate_append := by
    intro first second
    simp [documentCompositional, ExactDeclarationCodec.elaborate,
      DeclarationDocument.values, DeclarationDocument.valuesList,
      List.map_append]

/-- Every exact declaration codec induces a coGSLT-authored extension layer. -/
def layer (Base : Type uBase)
    {Syntax : Type} {Payload : Type uFiber}
    (codec : ExactDeclarationCodec Syntax Payload) : CoGSLTLayer Base where
  Fiber := fun _ => List Payload
  sourceGSLT := fun _ => (codec.compositionalElaboration).authoring.theory
  elaborate := fun _ => (codec.compositionalElaboration).elaboration.elaborate
  quote := fun _ => (codec.compositionalElaboration).elaboration.quote
  elaborate_quote := fun _ =>
    (codec.compositionalElaboration).elaboration.elaborate_quote
  elaborate_equation := fun _ =>
    (codec.compositionalElaboration).elaboration.equation
  elaborate_rewrite := fun _ =>
    (codec.compositionalElaboration).elaboration.rewrite

/-- A baseline certified realization of declaration sequences as arrays.
This is a genuine representation change: the semantic observation is the
ordered declaration list recovered from the backend array. -/
def arrayRealization (Base : Type uBase)
    {Syntax : Type} {Payload : Type uFiber}
    (codec : ExactDeclarationCodec Syntax Payload) :
    CoGSLTLayer.Realization (codec.layer Base)
      (fun _ => Array Payload) (fun _ => List Payload) where
  compile := fun _ declarations => declarations.toArray
  observeSource := fun _ declarations => declarations
  observeArtifact := fun _ artifact => artifact.toList
  adequate := by
    intro _ declarations
    simp

/-- Dropping the final declaration is not adequate for the exact list
observation.  The realization obligation therefore rules out a concrete
lossy backend. -/
theorem dropLast_array_not_exact {Payload : Type uFiber} (payload : Payload) :
    (#[payload].pop : Array Payload).toList ≠ [payload] := by
  simp

end ExactDeclarationCodec

/-! ## Negative canary: extension data is not generally derivable from base -/

private def booleanLayer : ExtensionLayer Unit where
  Fiber := fun _ => Bool

private def booleanAttachedFalse : booleanLayer.Total := ⟨(), false⟩
private def booleanAttachedTrue : booleanLayer.Total := ⟨(), true⟩

/-- Two extension declarations can share one base and still differ.  Therefore
the fibre is genuine information, not a redundant function of the base. -/
def booleanLayerNonTrivialFiber :
    NonTrivialFiber booleanLayer.erase (fun attached => attached.2) where
  left := booleanAttachedFalse
  right := booleanAttachedTrue
  sameShadow := rfl
  differentValue := by decide

theorem extension_payload_not_determined_by_base :
    ¬ Factors booleanLayer.erase (fun attached => attached.2) :=
  booleanLayerNonTrivialFiber.not_factors

end Mettapedia.GSLT.LanguageDef.Extension
