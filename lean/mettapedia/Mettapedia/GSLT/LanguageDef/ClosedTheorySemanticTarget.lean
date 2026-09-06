import Mettapedia.GSLT.LanguageDef.NIKTheoryTranslationExt

/-!
# Closed Pi-institution theories as native NIK fibres

A closed theory in a Pi-institution already has the semantic information
needed for a one-fibre NIK theory family: its sentences are claims and its
closed theorem set is both scope and meaning.  A proof calculus for the
institution then supplies a native evidence discipline whose theorem-image law
is inherited exactly.

The bridge does not synthesize a Boolean checker.  Decidability and replay are
additional data, so an `AuthorityContract` is available only after a native
checker and an exact certificate boundary have independently been supplied.
This keeps a semantic theory, its proof objects, and one implementation of a
checker distinct.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ClosedTheorySemanticTarget

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe uSignature uHom uSentence

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uHom} Signature]
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}

/-! ## From a closed theory to one native semantic fibre -/

/-- The singleton signature carrier of one closed theory.  The selected
native signature remains visible in the type parameter, while irrelevant
ambient signatures are not added to the NIK object. -/
inductive SelectedSignature (signature : Signature) : Type uSignature where
  | selected : SelectedSignature signature

instance (signature : Signature) :
    Subsingleton (SelectedSignature signature) where
  allEq first second := by
    cases first
    cases second
    rfl

/-- A closed Pi-institution theory viewed as one heterogeneous NIK theory
fibre.  No checker or certificate format is selected. -/
def theoryFamily (logical : PiInstitution.TheoryObject institution) :
    TheoryFamily.{uSignature, 0, uSentence} Unit where
  Signature := SelectedSignature logical.signature
  signatureOf := fun _ => .selected
  Claim := fun _ => institution.sentence.obj logical.signature
  Scope := fun _ formula => formula ∈ logical.theory.1
  Meaning := fun _ formula => formula ∈ logical.theory.1
  scope_sound := fun _ _ theoremhood => theoremhood

/-- A proof calculus supplies exactly the native proof objects of the one-fibre
theory. -/
def evidenceDiscipline
    (calculus : PiInstitution.ProofCalculus institution)
    (logical : PiInstitution.TheoryObject institution) :
    EvidenceDiscipline (theoryFamily logical) where
  ProofObject := fun _ => calculus.proof.obj logical
  Proves := fun _ proof formula =>
    calculus.projection.app logical proof = formula
  scope_iff_proof := by
    intro _ formula
    exact (calculus.theorem_image logical formula).symm

/-- Proofs over one claim retain the identity of their native proof object. -/
def ProofFibre {logical : PiInstitution.TheoryObject institution}
    (discipline : EvidenceDiscipline (theoryFamily logical))
    (formula : institution.sentence.obj logical.signature) :=
  { proof : discipline.ProofObject () // discipline.Proves () proof formula }

theorem proofFibre_nonempty_iff_scope
    {logical : PiInstitution.TheoryObject institution}
    (discipline : EvidenceDiscipline (theoryFamily logical))
    (formula : institution.sentence.obj logical.signature) :
    Nonempty (ProofFibre discipline formula) ↔
      formula ∈ logical.theory.1 := by
  constructor
  · rintro ⟨⟨proof, proves⟩⟩
    have inScope : (theoryFamily logical).Scope () formula :=
      (discipline.scope_iff_proof () formula).mpr ⟨proof, proves⟩
    exact inScope
  · intro theoremhood
    have inScope : (theoryFamily logical).Scope () formula := theoremhood
    obtain ⟨proof, proves⟩ :=
      (discipline.scope_iff_proof () formula).mp inScope
    exact ⟨⟨proof, proves⟩⟩

/-! ## Closed-theory routes induce semantic NIK routes -/

/-- A little-theory morphism induces a heterogeneous semantic route between
the corresponding one-fibre NIK theories. -/
def theoryTranslation
    {source target : PiInstitution.TheoryObject institution}
    (translation : PiInstitution.TheoryHom source target) :
    TheoryTranslation (theoryFamily source) (theoryFamily target) where
  mapKind := id
  mapSignature := fun _ => .selected
  signature_commutes := by intro _; rfl
  mapClaim := fun _ formula =>
    institution.sentence.map translation.mapSignature formula
  scope_preserved := by
    intro _ formula theoremhood
    exact translation.preserves theoremhood
  meaning_preserved := by
    intro _ formula theoremhood
    exact translation.preserves theoremhood

/-- The one-fibre construction sends the identity little-theory route to the
identity NIK semantic route. -/
theorem theoryTranslation_identity
    (logical : PiInstitution.TheoryObject institution) :
    theoryTranslation (PiInstitution.TheoryHom.identity logical) =
      NIKHeterogeneousTheory.TheoryTranslation.identity
        (theoryFamily logical) := by
  apply CertifiedTheoryCategory.TheoryTranslation.ext_data
  · intro kind
    rfl
  · intro signature
    cases signature
    rfl
  · intro kind formula
    cases kind
    exact heq_of_eq
      (institution.sentence.map_id_apply logical.signature formula)

/-- The one-fibre construction preserves composition of little-theory
routes. -/
theorem theoryTranslation_comp
    {first middle last : PiInstitution.TheoryObject institution}
    (earlier : PiInstitution.TheoryHom first middle)
    (later : PiInstitution.TheoryHom middle last) :
    theoryTranslation (PiInstitution.TheoryHom.comp earlier later) =
      NIKHeterogeneousTheory.TheoryTranslation.comp
        (theoryTranslation earlier) (theoryTranslation later) := by
  apply CertifiedTheoryCategory.TheoryTranslation.ext_data
  · intro kind
    rfl
  · intro signature
    cases signature
    rfl
  · intro kind formula
    cases kind
    exact heq_of_eq
      (institution.sentence.map_comp_apply earlier.mapSignature
        later.mapSignature formula)

/-- Closed little theories and their native translations form a genuine
semantic subgraph of the heterogeneous NIK theory category.  No checker or
certificate representation is selected by this functor. -/
def closedTheoryFunctor :
    PiInstitution.TheoryObject institution ⥤
      CertifiedTheoryCategory.TheoryObject.{0, uSignature, uSentence} where
  obj logical := ⟨Unit, theoryFamily logical⟩
  map translation := theoryTranslation translation
  map_id logical := theoryTranslation_identity logical
  map_comp earlier later := theoryTranslation_comp earlier later

/-- Naturality of a proof calculus says that its native proof objects move
with the same sentence translation as the little-theory route. -/
theorem mapProof_proves
    (calculus : PiInstitution.ProofCalculus institution)
    {source target : PiInstitution.TheoryObject institution}
    (translation : PiInstitution.TheoryHom source target)
    {proof : calculus.proof.obj source}
    {formula : institution.sentence.obj source.signature}
    (proves : calculus.projection.app source proof = formula) :
    calculus.projection.app target (calculus.proof.map translation proof) =
      institution.sentence.map translation.mapSignature formula := by
  have naturality := congrArg
    (fun function => function proof)
    (calculus.projection.naturality translation)
  change calculus.projection.app target
      (calculus.proof.map translation proof) =
    institution.sentence.map translation.mapSignature
      (calculus.projection.app source proof) at naturality
  rw [proves] at naturality
  exact naturality

/-! ## Proof identity is not fixed by theoremhood -/

abbrev thinDiscipline
    (logical : PiInstitution.TheoryObject institution) :=
  evidenceDiscipline (PiInstitution.ProofCalculus.thin institution) logical

abbrev taggedDiscipline
    (logical : PiInstitution.TheoryObject institution) :=
  evidenceDiscipline (PiInstitution.ProofCalculus.tagged institution) logical

/-- The canonical thin calculus has at most one proof of a fixed theorem. -/
theorem thinProofFibre_subsingleton
    (logical : PiInstitution.TheoryObject institution)
    (formula : institution.sentence.obj logical.signature) :
    Subsingleton (ProofFibre (thinDiscipline logical) formula) where
  allEq := by
    intro first second
    apply Subtype.ext
    apply Subtype.ext
    exact first.property.trans second.property.symm

/-- The tagged calculus supplies a concrete proof of a theorem with each
Boolean occurrence tag. -/
def taggedFalseProof
    (logical : PiInstitution.TheoryObject institution)
    (formula : institution.sentence.obj logical.signature)
    (theoremhood : formula ∈ logical.theory.1) :
    ProofFibre (taggedDiscipline logical) formula :=
  ⟨(⟨formula, theoremhood⟩, false), rfl⟩

def taggedTrueProof
    (logical : PiInstitution.TheoryObject institution)
    (formula : institution.sentence.obj logical.signature)
    (theoremhood : formula ∈ logical.theory.1) :
    ProofFibre (taggedDiscipline logical) formula :=
  ⟨(⟨formula, theoremhood⟩, true), rfl⟩

/-- Negative control: the same extensional theoremhood predicate admits a
proof-relevant discipline with two distinct proofs in one fixed fibre. -/
theorem taggedProofs_distinct
    (logical : PiInstitution.TheoryObject institution)
    (formula : institution.sentence.obj logical.signature)
    (theoremhood : formula ∈ logical.theory.1) :
    taggedFalseProof logical formula theoremhood ≠
      taggedTrueProof logical formula theoremhood := by
  intro equalProofs
  have equalTags := congrArg (fun proof => proof.1.2) equalProofs
  cases equalTags

theorem taggedProofFibre_not_subsingleton
    (logical : PiInstitution.TheoryObject institution)
    (formula : institution.sentence.obj logical.signature)
    (theoremhood : formula ∈ logical.theory.1) :
    ¬Subsingleton (ProofFibre (taggedDiscipline logical) formula) := by
  intro subsingleton
  exact taggedProofs_distinct logical formula theoremhood
    (subsingleton.allEq _ _)

#print axioms evidenceDiscipline
#print axioms proofFibre_nonempty_iff_scope
#print axioms theoryTranslation
#print axioms theoryTranslation_identity
#print axioms theoryTranslation_comp
#print axioms closedTheoryFunctor
#print axioms mapProof_proves
#print axioms thinProofFibre_subsingleton
#print axioms taggedProofs_distinct
#print axioms taggedProofFibre_not_subsingleton

end Mettapedia.GSLT.LanguageDef.ClosedTheorySemanticTarget
