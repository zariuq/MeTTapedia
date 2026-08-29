import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationComputation

/-!
# Source-faithful authored signatures for cumulative Prime

`Declaration.Signature` is the extensional semantic environment consumed by
typing and conversion.  It is intentionally not a source program: lookup
forgets shadowed declarations, while proposition-valued root computation
forgets equation identity and its substitution witness.

This module supplies the missing authored layer.  A declaration document keeps
source order, bundle structure up to the explicit document equations, complete
open equation schemas, and stable equation-occurrence identity.  Its semantic
interpretation reuses the existing `Signature` and
`ProofRelevantRootComputation`; no parallel typing calculus is introduced.

The non-injectivity theorem is part of the interface.  An implementation may
cache or execute the extensional interpretation, but it may not claim to have
reconstructed the authored program from that interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredDeclarationSignature

open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration

/-! ## Authored declarations -/

/-- One named open equation schema.  The context and displayed type are
authored data even though raw root computation consumes only the endpoints.
Later formation attaches typing receipts to this exact schema rather than
trying to recover a telescope from an untyped rewrite. -/
structure EquationSchema where
  label : DeclName
  arity : Nat
  context : Ctx Tower.Head arity
  left : Tower.Tm arity
  right : Tower.Tm arity
  type : Tower.Tm arity
  deriving Repr

/-- The ordered source declaration language.  Constants and equations remain
distinguishable; in particular, equations are not smuggled into constant
lookup and constants are not mistaken for operational rules. -/
inductive SourceDeclaration where
  | constant (name : DeclName) (entry : Entry Tower.Head)
  | equation (schema : EquationSchema)
  deriving Repr

abbrev SourceDocument := DeclarationDocument SourceDeclaration

/-- Prime declaration syntax is already structural, so its exact declaration
codec is the identity isomorphism.  The nontrivial elaboration performed below
is ordered document flattening followed by semantic interpretation. -/
def sourceCodec :
    ExactDeclarationCodec SourceDeclaration SourceDeclaration where
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

/-- The existing compositional declaration-document GSLT, specialized to
Prime declarations. -/
def authoringGSLT : DeclarationAuthoringGSLT SourceDeclaration :=
  sourceCodec.compositionalElaboration

/-- Exact authored elaboration preserves declaration order and multiplicity. -/
def elaborate (source : SourceDocument) : List SourceDeclaration :=
  sourceCodec.elaborate source

/-- Select constant declarations without disturbing their relative order. -/
def constantDeclarations :
    List SourceDeclaration -> List (DeclName × Entry Tower.Head)
  | [] => []
  | .constant name entry :: declarations =>
      (name, entry) :: constantDeclarations declarations
  | .equation _ :: declarations => constantDeclarations declarations

/-- Select equation schemas without disturbing their relative order.  The
resulting list index is the stable occurrence identity used below. -/
def equationSchemas : List SourceDeclaration -> List EquationSchema
  | [] => []
  | .constant _ _ :: declarations => equationSchemas declarations
  | .equation schema :: declarations => schema :: equationSchemas declarations

/-! ## Proof-relevant substitution instances -/

/-- One exact substitution instance of an authored equation occurrence.
`index`, rather than list membership, preserves the identity of duplicate
schemas. -/
structure EquationOccurrence (schemas : List EquationSchema)
    {ambient : Nat} (source target : Tower.Tm ambient) where
  index : Fin schemas.length
  substitution : Sub Tower.Head (schemas.get index).arity ambient
  sourceEquation :
    Presentation.subst substitution (schemas.get index).left = source
  targetEquation :
    Presentation.subst substitution (schemas.get index).right = target

namespace EquationOccurrence

/-- Transport an occurrence across an equality of authored schema inventories.
The map changes only the type-level inventory; the retained schema position,
substitution, and endpoint equations are unchanged. -/
def schemaEquiv {first second : List EquationSchema}
    (schemas : first = second) {ambient : Nat}
    {source target : Tower.Tm ambient} :
    EquationOccurrence first source target ≃
      EquationOccurrence second source target := by
  cases schemas
  exact Equiv.refl _

@[simp] theorem schemaEquiv_refl
    {schemas : List EquationSchema} {ambient : Nat}
    {source target : Tower.Tm ambient}
    (occurrence : EquationOccurrence schemas source target) :
    schemaEquiv (Eq.refl schemas) occurrence = occurrence :=
  rfl

/-- Two authored occurrences are equal exactly when they retain the same
schema position and the same (dependently typed) substitution.  Endpoint
equations are propositions and therefore add no spurious receipt identity. -/
@[ext] theorem ext {schemas : List EquationSchema} {ambient : Nat}
    {source target : Tower.Tm ambient}
    (first second : EquationOccurrence schemas source target)
    (index : first.index = second.index)
    (substitution : HEq first.substitution second.substitution) :
    first = second := by
  cases first with
  | mk firstIndex firstSubstitution firstSource firstTarget =>
      cases second with
      | mk secondIndex secondSubstitution secondSource secondTarget =>
          cases index
          cases substitution
          rfl

/-- Renaming changes the ambient telescope but preserves the authored
occurrence and its substitution history. -/
def rename {schemas : List EquationSchema} {n m : Nat}
    {source target : Tower.Tm n}
    (occurrence : EquationOccurrence schemas source target)
    (renameMap : Ren n m) :
    EquationOccurrence schemas
      (Presentation.rename renameMap source)
      (Presentation.rename renameMap target) where
  index := occurrence.index
  substitution := fun index =>
    Presentation.rename renameMap (occurrence.substitution index)
  sourceEquation := by
    rw [← Presentation.rename_subst, occurrence.sourceEquation]
  targetEquation := by
    rw [← Presentation.rename_subst, occurrence.targetEquation]

/-- Substitution composes with the retained authored substitution and leaves
the source occurrence identity unchanged. -/
def substitute {schemas : List EquationSchema} {n m : Nat}
    {source target : Tower.Tm n}
    (occurrence : EquationOccurrence schemas source target)
    (substitution : Sub Tower.Head n m) :
    EquationOccurrence schemas
      (Presentation.subst substitution source)
      (Presentation.subst substitution target) where
  index := occurrence.index
  substitution := fun index =>
    Presentation.subst substitution (occurrence.substitution index)
  sourceEquation := by
    rw [← Presentation.subst_comp, occurrence.sourceEquation]
  targetEquation := by
    rw [← Presentation.subst_comp, occurrence.targetEquation]

/-- Inventory transport commutes with ambient renaming. -/
theorem schemaEquiv_rename
    {first second : List EquationSchema} (schemas : first = second)
    {n m : Nat} {source target : Tower.Tm n}
    (occurrence : EquationOccurrence first source target)
    (renameMap : Ren n m) :
    schemaEquiv schemas (occurrence.rename renameMap) =
      (schemaEquiv schemas occurrence).rename renameMap := by
  cases schemas
  rfl

/-- Inventory transport commutes with simultaneous substitution. -/
theorem schemaEquiv_substitute
    {first second : List EquationSchema} (schemas : first = second)
    {n m : Nat} {source target : Tower.Tm n}
    (occurrence : EquationOccurrence first source target)
    (substitution : Sub Tower.Head n m) :
    schemaEquiv schemas (occurrence.substitute substitution) =
      (schemaEquiv schemas occurrence).substitute substitution := by
  cases schemas
  rfl

/-- Every authored schema has a canonical occurrence under the identity
substitution. -/
def canonical (schemas : List EquationSchema) (index : Fin schemas.length) :
    EquationOccurrence schemas (schemas.get index).left
      (schemas.get index).right where
  index := index
  substitution := ids
  sourceEquation := Presentation.subst_ids _
  targetEquation := Presentation.subst_ids _

end EquationOccurrence

/-- The proof-relevant root computation generated by an ordered equation
inventory.  Logical conversion will consume its support; native execution and
receipts may retain the full `EquationOccurrence`. -/
def equationComputation (schemas : List EquationSchema) :
    ProofRelevantRootComputation Tower.Head where
  Evidence := EquationOccurrence schemas
  rename := by
    intro n m renameMap source target occurrence
    exact occurrence.rename renameMap
  substitute := by
    intro n m substitution source target occurrence
    exact occurrence.substitute substitution

/-! ## Semantic interpretation -/

/-- Interpret an ordered declaration sequence into the established extensional
Prime signature.  First-wins constant lookup and support-erased computation
are deliberate semantic readouts, not source representations. -/
def semanticSignature (declarations : List SourceDeclaration) :
    Signature Tower.Head where
  entries := (Signature.ofList (constantDeclarations declarations)).entries
  computation :=
    (equationComputation (equationSchemas declarations)).support

/-- Interpret one authored declaration document after exact ordered
elaboration. -/
def interpret (source : SourceDocument) : Signature Tower.Head :=
  semanticSignature (elaborate source)

@[simp] theorem elaborate_quote (declarations : List SourceDeclaration) :
    elaborate (sourceCodec.quote declarations) = declarations := by
  exact sourceCodec.elaborate_quote declarations

@[simp] theorem interpret_quote (declarations : List SourceDeclaration) :
    interpret (sourceCodec.quote declarations) =
      semanticSignature declarations := by
  simp [interpret]

/-! ## Positive and negative controls -/

private def exampleTerm : Tower.Tm 0 := .head .legacyGround
private def exampleType : Tower.Tm 0 := .head (.sort Tower.zero)

private def firstEquation : EquationSchema where
  label := `Prime.SourceExample.first
  arity := 0
  context := .nil
  left := exampleTerm
  right := exampleTerm
  type := exampleType

private def secondEquation : EquationSchema where
  label := `Prime.SourceExample.second
  arity := 0
  context := .nil
  left := exampleTerm
  right := exampleTerm
  type := exampleType

private def duplicateEndpointSchemas : List EquationSchema :=
  [firstEquation, secondEquation]

private def firstDuplicateOccurrence :
    EquationOccurrence duplicateEndpointSchemas exampleTerm exampleTerm where
  index := ⟨0, by decide⟩
  substitution := ids
  sourceEquation := by rfl
  targetEquation := by rfl

private def secondDuplicateOccurrence :
    EquationOccurrence duplicateEndpointSchemas exampleTerm exampleTerm where
  index := ⟨1, by decide⟩
  substitution := ids
  sourceEquation := by rfl
  targetEquation := by rfl

/-- Duplicate operational endpoints retain two distinct authored receipts.
This is the proof-relevant multiplicity that proposition-valued support
intentionally forgets. -/
theorem duplicate_endpoints_retain_occurrence_identity :
    ∃ first second :
        (equationComputation duplicateEndpointSchemas).Evidence
          exampleTerm exampleTerm,
      first ≠ second := by
  refine ⟨firstDuplicateOccurrence, secondDuplicateOccurrence, ?_⟩
  intro equal
  have indexValues := congrArg
    (fun occurrence => occurrence.index.val) equal
  simp [firstDuplicateOccurrence, secondDuplicateOccurrence] at indexValues

/-- Proposition-valued support cannot be an adequate receipt representation:
the two distinct authored occurrences above become the same inhabitance fact.
This is the permanent negative control for any endpoint-only computation API. -/
theorem occurrence_to_support_not_injective :
    ¬ Function.Injective
      (fun occurrence :
          EquationOccurrence duplicateEndpointSchemas exampleTerm exampleTerm =>
        (⟨occurrence⟩ : Nonempty
          (EquationOccurrence duplicateEndpointSchemas exampleTerm exampleTerm))) := by
  intro injective
  have supportsEqual :
      (⟨firstDuplicateOccurrence⟩ : Nonempty
        (EquationOccurrence duplicateEndpointSchemas exampleTerm exampleTerm)) =
      ⟨secondDuplicateOccurrence⟩ := Subsingleton.elim _ _
  have occurrencesEqual :
      firstDuplicateOccurrence = secondDuplicateOccurrence :=
    injective supportsEqual
  have indexValues := congrArg
    (fun occurrence => occurrence.index.val) occurrencesEqual
  simp [firstDuplicateOccurrence, secondDuplicateOccurrence] at indexValues

/-- An empty authored equation inventory cannot manufacture a root step. -/
theorem empty_equations_have_no_evidence
    (n : Nat) (source target : Tower.Tm n) :
    ¬ Nonempty ((equationComputation []).Evidence source target) := by
  rintro ⟨occurrence⟩
  exact Fin.elim0 occurrence.index

private def shadowedName : DeclName := `Prime.SourceExample.A

private def firstEntry : Entry Tower.Head where
  type := .head (.sort Tower.zero)

private def laterEntry : Entry Tower.Head where
  type := .head (.sort (.succ Tower.zero))

private def shadowedDeclarations : List SourceDeclaration :=
  [.constant shadowedName firstEntry,
   .constant shadowedName laterEntry]

private def singleDeclaration : List SourceDeclaration :=
  [.constant shadowedName firstEntry]

theorem shadowed_source_differs_from_single :
    shadowedDeclarations ≠ singleDeclaration := by
  intro equal
  have lengths := congrArg List.length equal
  simp [shadowedDeclarations, singleDeclaration] at lengths

/-- First-wins nominal interpretation cannot recover a later shadowed source
declaration.  This is an intended information-losing map, not an adequacy
failure of the authored layer. -/
theorem shadowed_and_single_semantic_signatures_equal :
    semanticSignature shadowedDeclarations =
      semanticSignature singleDeclaration := by
  have entriesEqual :
      (Signature.ofList
          (constantDeclarations shadowedDeclarations)).entries =
        (Signature.ofList
          (constantDeclarations singleDeclaration)).entries := by
    funext candidate
    by_cases same : candidate = shadowedName
    · subst candidate
      simp [shadowedDeclarations, singleDeclaration, constantDeclarations,
        Signature.ofList, Signature.insert, Signature.empty]
    · simp [shadowedDeclarations, singleDeclaration, constantDeclarations,
        Signature.ofList, Signature.insert, Signature.empty, same]
  unfold semanticSignature
  rw [entriesEqual]
  have equationsEqual :
      equationSchemas shadowedDeclarations =
        equationSchemas singleDeclaration := by
    rfl
  rw [equationsEqual]

/-- Consequently the semantic signature interpretation is not injective.
Authored declaration order and provenance must remain available whenever a
later consumer needs them. -/
theorem semanticSignature_not_injective :
    ¬ Function.Injective semanticSignature := by
  intro injective
  exact shadowed_source_differs_from_single
    (injective shadowed_and_single_semantic_signatures_equal)

private def nestedDocument : SourceDocument :=
  .bundle
    [.declaration (.equation firstEquation),
     .bundle [.declaration (.equation secondEquation)]]

/-- Bundle nesting is syntactic; exact elaboration retains the flat authored
order and both equation occurrences. -/
theorem nested_document_elaborates_in_order :
    elaborate nestedDocument =
      [.equation firstEquation, .equation secondEquation] := by
  simp [elaborate, sourceCodec, nestedDocument,
    ExactDeclarationCodec.elaborate, DeclarationDocument.values,
    DeclarationDocument.valuesList]

#print axioms duplicate_endpoints_retain_occurrence_identity
#print axioms occurrence_to_support_not_injective
#print axioms empty_equations_have_no_evidence
#print axioms semanticSignature_not_injective
#print axioms nested_document_elaborates_in_order

end AuthoredDeclarationSignature
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
