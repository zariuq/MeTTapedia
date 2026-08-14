import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Megalodon publication hash roots

Megalodon uses a tagged Merkle-style hash algebra to name terms, proofs, and
documents.  This module specifies that algebra independently of any concrete
SHA-256 implementation.  In particular, none of the results below assumes
that hashes are injective: exact logical endpoint identity remains a separate
structural codec property.

The recursive equations and numeric domains mirror Megalodon's `Mathdata`
hash-root layer.  Hashing a serialized type and resolving an authored hash name
are explicit inputs because both cross the logical-kernel/publication boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.PublicationHashRoot

open Mettapedia.Languages.Megalodon.MathdataKernel

/-- Primitive operations needed by Megalodon's publication hash-root tree.
`typeRoot?` includes the exact bit serialization of a type; `namedRoot?`
decodes a publication name carrying an already-computed hash value. -/
structure HashOps (Hash : Type) where
  hashInt32 : UInt32 → Hash
  hashPair : Hash → Hash → Hash
  hashTag : Hash → UInt32 → Hash
  typeRoot? : Tp → Option Hash
  namedRoot? : Name → Option Hash

variable {Hash : Type}

/-- Megalodon's published term/proof indices are restricted to sixteen bits by
the source serialization. -/
def index32? (index : Nat) : Option UInt32 :=
  if index < 65536 then some (UInt32.ofNat index) else none

@[simp] theorem index32?_of_lt (index : Nat) (bound : index < 65536) :
    index32? index = some (UInt32.ofNat index) := by
  simp [index32?, bound]

@[simp] theorem index32?_of_not_lt (index : Nat) (bound : ¬ index < 65536) :
    index32? index = none := by
  simp [index32?, bound]

mutual

/-- Publication root of a Megalodon term.  Named terms are content-addressed
leaves supplied by `namedRoot?`; all other nodes use the exact Mathdata tags
96 through 104. -/
def termRoot? (operations : HashOps Hash) : Tm → Option Hash
  | .named name => operations.namedRoot? name
  | .prim index => do
      let encoded : UInt32 ← index32? index
      pure (operations.hashTag (operations.hashInt32 encoded) 96)
  | .db index => do
      let encoded : UInt32 ← index32? index
      pure (operations.hashTag (operations.hashInt32 encoded) 97)
  | .app function argument => do
      let functionRoot ← termRoot? operations function
      let argumentRoot ← termRoot? operations argument
      pure (operations.hashTag
        (operations.hashPair functionRoot argumentRoot) 98)
  | .lam type body => do
      let typeRoot ← operations.typeRoot? type
      let bodyRoot ← termRoot? operations body
      pure (operations.hashTag (operations.hashPair typeRoot bodyRoot) 99)
  | .imp domain codomain => do
      let domainRoot ← termRoot? operations domain
      let codomainRoot ← termRoot? operations codomain
      pure (operations.hashTag
        (operations.hashPair domainRoot codomainRoot) 100)
  | .all type body => do
      let typeRoot ← operations.typeRoot? type
      let bodyRoot ← termRoot? operations body
      pure (operations.hashTag (operations.hashPair typeRoot bodyRoot) 101)
  | .typeApp function type => do
      let functionRoot ← termRoot? operations function
      let typeRoot ← operations.typeRoot? type
      pure (operations.hashTag
        (operations.hashPair functionRoot typeRoot) 102)
  | .typeLam body => do
      let bodyRoot ← termRoot? operations body
      pure (operations.hashTag bodyRoot 103)
  | .typeAll body => do
      let bodyRoot ← termRoot? operations body
      pure (operations.hashTag bodyRoot 104)

/-- Publication root of a Megalodon proof article, using the exact Mathdata
tags 128 through 135. -/
def proofRoot? (operations : HashOps Hash) : Pf → Option Hash
  | .gpa name => operations.namedRoot? name
  | .known name => do
      let root ← operations.namedRoot? name
      pure (operations.hashTag root 128)
  | .hyp index => do
      let encoded : UInt32 ← index32? index
      pure (operations.hashTag (operations.hashInt32 encoded) 129)
  | .termApp proof term => do
      let proofRoot ← proofRoot? operations proof
      let termRoot ← termRoot? operations term
      pure (operations.hashTag
        (operations.hashPair proofRoot termRoot) 130)
  | .proofApp function argument => do
      let functionRoot ← proofRoot? operations function
      let argumentRoot ← proofRoot? operations argument
      pure (operations.hashTag
        (operations.hashPair functionRoot argumentRoot) 131)
  | .proofLam proposition body => do
      let propositionRoot ← termRoot? operations proposition
      let bodyRoot ← proofRoot? operations body
      pure (operations.hashTag
        (operations.hashPair propositionRoot bodyRoot) 132)
  | .termLam type body => do
      let typeRoot ← operations.typeRoot? type
      let bodyRoot ← proofRoot? operations body
      pure (operations.hashTag
        (operations.hashPair typeRoot bodyRoot) 133)
  | .typeApp proof type => do
      let proofRoot ← proofRoot? operations proof
      let typeRoot ← operations.typeRoot? type
      pure (operations.hashTag
        (operations.hashPair proofRoot typeRoot) 134)
  | .typeLam body => do
      let bodyRoot ← proofRoot? operations body
      pure (operations.hashTag bodyRoot 135)

end

/-- One publication-level Megalodon document item. -/
inductive DocumentItem where
  | signature (name : Name)
  | parameter (name : Name) (type : Tp)
  | definition (type : Tp) (term : Tm)
  | known (proposition : Tm)
  | conjecture (proposition : Tm)
  | proofOf (proposition : Tm) (proof : Pf)
deriving DecidableEq, Repr

abbrev Document := List DocumentItem

/-- A partial document retains exactly enough hash material to reconstruct a
document root.  Its pre-hashed cases match Megalodon's publication protocol;
they are not logical proof certificates. -/
inductive PartialDocument (Hash : Type) where
  | nil
  | hash (root : Hash)
  | signature (name : Name) (tail : PartialDocument Hash)
  | parameter (name : Name) (type : Tp) (tail : PartialDocument Hash)
  | parameterHash (payloadRoot : Hash) (tail : PartialDocument Hash)
  | definition (type : Tp) (term : Tm) (tail : PartialDocument Hash)
  | definitionHash (payloadRoot : Hash) (tail : PartialDocument Hash)
  | known (proposition : Tm) (tail : PartialDocument Hash)
  | conjecture (proposition : Tm) (tail : PartialDocument Hash)
  | proofOf (proposition : Tm) (proof : Pf) (tail : PartialDocument Hash)
  | proofOfHash (payloadRoot : Hash) (tail : PartialDocument Hash)
deriving Repr

/-- Root of one document item, using the exact Mathdata tags 172 through 177. -/
def documentItemRoot? (operations : HashOps Hash) :
    DocumentItem → Option Hash
  | .signature name => do
      let root ← operations.namedRoot? name
      pure (operations.hashTag root 172)
  | .parameter name type => do
      let nameRoot ← operations.namedRoot? name
      let typeRoot ← operations.typeRoot? type
      pure (operations.hashTag (operations.hashPair nameRoot typeRoot) 173)
  | .definition type term => do
      let typeRoot ← operations.typeRoot? type
      let termRoot ← termRoot? operations term
      pure (operations.hashTag (operations.hashPair typeRoot termRoot) 174)
  | .known proposition => do
      let root ← termRoot? operations proposition
      pure (operations.hashTag root 175)
  | .conjecture proposition => do
      let root ← termRoot? operations proposition
      pure (operations.hashTag root 176)
  | .proofOf proposition proof => do
      let propositionRoot ← termRoot? operations proposition
      let proofRoot ← proofRoot? operations proof
      pure (operations.hashTag
        (operations.hashPair propositionRoot proofRoot) 177)

/-- Root of a complete Megalodon document. -/
def documentRoot? (operations : HashOps Hash) : Document → Option Hash
  | [] => some (operations.hashInt32 180)
  | item :: tail => do
      let itemRoot ← documentItemRoot? operations item
      let tailRoot ← documentRoot? operations tail
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)

/-- Root of a partial Megalodon document. -/
def partialDocumentRoot? (operations : HashOps Hash) :
    PartialDocument Hash → Option Hash
  | .nil => some (operations.hashInt32 180)
  | .hash root => some root
  | .signature name tail => do
      let nameRoot ← operations.namedRoot? name
      let tailRoot ← partialDocumentRoot? operations tail
      pure (operations.hashTag
        (operations.hashPair (operations.hashTag nameRoot 172) tailRoot) 181)
  | .parameter name type tail => do
      let nameRoot ← operations.namedRoot? name
      let typeRoot ← operations.typeRoot? type
      let tailRoot ← partialDocumentRoot? operations tail
      let itemRoot := operations.hashTag
        (operations.hashPair nameRoot typeRoot) 173
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)
  | .parameterHash payloadRoot tail => do
      let tailRoot ← partialDocumentRoot? operations tail
      let itemRoot := operations.hashTag payloadRoot 173
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)
  | .definition type term tail => do
      let typeRoot ← operations.typeRoot? type
      let termRoot ← termRoot? operations term
      let tailRoot ← partialDocumentRoot? operations tail
      let itemRoot := operations.hashTag
        (operations.hashPair typeRoot termRoot) 174
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)
  | .definitionHash payloadRoot tail => do
      let tailRoot ← partialDocumentRoot? operations tail
      let itemRoot := operations.hashTag payloadRoot 174
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)
  | .known proposition tail => do
      let propositionRoot ← termRoot? operations proposition
      let tailRoot ← partialDocumentRoot? operations tail
      let itemRoot := operations.hashTag propositionRoot 175
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)
  | .conjecture proposition tail => do
      let propositionRoot ← termRoot? operations proposition
      let tailRoot ← partialDocumentRoot? operations tail
      let itemRoot := operations.hashTag propositionRoot 176
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)
  | .proofOf proposition proof tail => do
      let propositionRoot ← termRoot? operations proposition
      let proofRoot ← proofRoot? operations proof
      let tailRoot ← partialDocumentRoot? operations tail
      let itemRoot := operations.hashTag
        (operations.hashPair propositionRoot proofRoot) 177
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)
  | .proofOfHash payloadRoot tail => do
      let tailRoot ← partialDocumentRoot? operations tail
      let itemRoot := operations.hashTag payloadRoot 177
      pure (operations.hashTag
        (operations.hashPair itemRoot tailRoot) 181)

/-- Embed a complete document into the partial-document carrier without
pre-hashing any item. -/
def PartialDocument.ofDocument : Document → PartialDocument Hash
  | [] => .nil
  | .signature name :: tail => .signature name (ofDocument tail)
  | .parameter name type :: tail => .parameter name type (ofDocument tail)
  | .definition type term :: tail => .definition type term (ofDocument tail)
  | .known proposition :: tail => .known proposition (ofDocument tail)
  | .conjecture proposition :: tail => .conjecture proposition (ofDocument tail)
  | .proofOf proposition proof :: tail =>
      .proofOf proposition proof (ofDocument tail)

/-- Complete and partial document hashing agree exactly on the canonical
embedding. -/
theorem partialDocumentRoot?_ofDocument (operations : HashOps Hash)
    (document : Document) :
    partialDocumentRoot? operations (PartialDocument.ofDocument document) =
      documentRoot? operations document := by
  induction document with
  | nil => rfl
  | cons item tail inductionHypothesis =>
      cases item <;>
        simp [PartialDocument.ofDocument, partialDocumentRoot?, documentRoot?,
          documentItemRoot?, inductionHypothesis, Option.bind_assoc]

/-! ## Positive and negative boundary canaries -/

private def symbolicOps : HashOps (List Nat) where
  hashInt32 (value : UInt32) := [1, value.toNat]
  hashPair left right := [7, left.length] ++ left ++ right
  hashTag root (tag : UInt32) := [8, tag.toNat] ++ root
  typeRoot? _ := some [64]
  namedRoot? name := some [0, name.length]

private def canaryDocument : Document :=
  [.known (.imp (.prim 0) (.prim 1)),
    .proofOf (.imp (.prim 0) (.prim 1))
      (.proofApp (.known "modus-ponens") (.known "premise"))]

/-- The full-to-partial agreement is executable on a nontrivial document. -/
example :
    partialDocumentRoot? symbolicOps
        (PartialDocument.ofDocument canaryDocument) =
      documentRoot? symbolicOps canaryDocument := by
  exact partialDocumentRoot?_ofDocument symbolicOps canaryDocument

private def collapsingOps : HashOps Unit where
  hashInt32 _ := ()
  hashPair _ _ := ()
  hashTag _ _ := ()
  typeRoot? _ := some ()
  namedRoot? _ := some ()

/-- A publication root is not exact logical identity without a separate
injectivity assumption: this valid hash algebra collapses distinct documents. -/
theorem publication_root_does_not_imply_document_identity :
    let left : Document := [.known (.prim 0)]
    let right : Document := [.conjecture (.prim 0)]
    left ≠ right ∧
      documentRoot? collapsingOps left = documentRoot? collapsingOps right := by
  dsimp
  constructor
  · decide
  · rfl

/-- Out-of-range syntax is rejected before publication rather than wrapped
through the machine integer carrier. -/
theorem oversized_index_is_rejected : index32? 65536 = none := by
  rfl

end Mettapedia.Languages.Megalodon.PublicationHashRoot
