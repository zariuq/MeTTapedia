import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.CalculusExtension

/-!
# Proof-carrying GSLT definitions

A CertificateGSLT begins with a validated finite proof-theoretic definition.  Its
primitive rules generate derivations; chronological proof DAGs share
previously checked derivations without changing the presented judgment.  The
context-and-substitution structure needed for the stronger algebraic
classification is built separately from open derivations.

This module installs only the strict, rule-retaining subcategory.  An arrow in
this subcategory keeps every source rule with exactly the same identifier and
schema.  It therefore transports derivations and checked proof meaning without
inventing an opaque preservation callback.  General interpretations, in which
one primitive source rule is implemented by a target proof-DAG template, are a
strict extension of this nucleus and require an explicit calculus of premise
holes.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusExtension

/-- A validated proof-theoretic definition.  Source identity and source
adequacy remain separate structures: this object records exactly the language,
judgments, rules, and validation evidence consumed by the generic checker. -/
structure Object where
  definition : ValidatedCalculusLanguageDef

namespace Object

/-- The exact authored calculus-GSLT document underlying a certificate-GSLT object.
The checker-facing definition is therefore a validated elaboration target,
not an ungrounded record beside the GSLT theory. -/
def authoredSource (object : Object) : CalculusSyntax :=
  CalculusExtension.authoredSource object.definition.1

/-- The authored document elaborates to exactly the calculus checked by the
certificate-GSLT object. -/
@[simp] theorem authoredSource_elaborates (object : Object) :
    elaborate object.authoredSource =
      some object.definition.1.toCalculus := by
  simp [authoredSource]

/-- Elaborating the source together with its base recovers the exact
checker-facing definition. -/
@[simp] theorem authoredSource_recovers (object : Object) :
    elaborateDefinition? object.definition.1.toLanguageDef object.authoredSource =
      some object.definition.1 := by
  simp [authoredSource]

/-- Certificate-GSLT derivability is reachability in the GSLT derived from the
authored calculus document. -/
theorem derivability_via_authoredSource (object : Object) (goals : GoalState) :
    elaborate object.authoredSource = some object.definition.1.toCalculus ∧
      (Nonempty (DerivationList object.definition goals) ↔
        (proofSearchGSLT object.definition).MultiStep goals []) :=
  ⟨object.authoredSource_elaborates,
    derivationList_nonempty_iff_proofSearch object.definition goals⟩

end Object

/-- The rule-retaining view supports the first honest category of CertificateGSLTs.
The wrapper leaves the underlying `Object` available for the later, more
general category of derivation-valued interpretations. -/
structure RuleRetaining where
  toCertificateGSLT : Object

namespace RuleRetaining

/-- Construct the strict view directly from a validated definition. -/
def ofDefinition (definition : ValidatedCalculusLanguageDef) : RuleRetaining :=
  ⟨⟨definition⟩⟩

/-- The validated definition checked at this object. -/
abbrev definition (object : RuleRetaining) : ValidatedCalculusLanguageDef :=
  object.toCertificateGSLT.definition

/-- A strict certificate-GSLT arrow retains every source rule lookup exactly.
Consequently the existing generic derivation transport is derived from this
field, rather than postulated as a second semantic authority. -/
structure Morphism (source target : RuleRetaining) : Type where
  refines : RuleLookupRefines source.definition target.definition

namespace Morphism

/-- Strict arrows are proof-irrelevant once their endpoints are fixed. -/
instance {source target : RuleRetaining} :
    Subsingleton (Morphism source target) :=
  ⟨fun ⟨_⟩ ⟨_⟩ => by congr⟩

/-- Identity retains every rule lookup. -/
def id (object : RuleRetaining) : Morphism object object :=
  ⟨RuleLookupRefines.refl object.definition⟩

/-- Composition is transitivity of exact rule retention. -/
def comp {first second third : RuleRetaining}
    (later : Morphism second third) (earlier : Morphism first second) :
    Morphism first third :=
  ⟨earlier.refines.trans later.refines⟩

/-- Transport a Type-valued derivation along a strict certificate-GSLT arrow. -/
def mapDerivation {source target : RuleRetaining}
    (morphism : Morphism source target) {goal : Pattern}
    (derivation : Derivation source.definition goal) :
    Derivation target.definition goal :=
  derivation.transport morphism.refines

/-- Transport a checked raw proof while retaining its exact proof tree. -/
def mapCheckedProof {source target : RuleRetaining}
    (morphism : Morphism source target) {goal : Pattern}
    (proof : CheckedProof source.definition goal) :
    CheckedProof target.definition goal :=
  proof.transport morphism.refines

@[simp] theorem mapCheckedProof_payload
    {source target : RuleRetaining} (morphism : Morphism source target)
    {goal : Pattern} (proof : CheckedProof source.definition goal) :
    (morphism.mapCheckedProof proof).1 = proof.1 := rfl

end Morphism

/-- Validated proof definitions and exact rule-retaining arrows form a
category.  The laws reduce to proof irrelevance after transitivity has built
the composite refinement. -/
instance : Category RuleRetaining where
  Hom := Morphism
  id := Morphism.id
  comp earlier later := Morphism.comp later earlier
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Any two strict arrows with the same endpoints agree.  This explicit
category-level form is convenient when a construction exposes homs through
Mathlib's `CategoryStruct.Hom` rather than the reducible `Morphism` name. -/
theorem hom_ext {source target : RuleRetaining}
    (first second : source ⟶ target) : first = second := by
  change Morphism source target at first second
  exact Subsingleton.elim first second

/-- Every validated append-only definition extension is a strict
certificate-GSLT arrow. -/
def ofValidatedExtension {base : ValidatedCalculusLanguageDef}
    (extension : ValidatedCalculusLanguageExtension base) :
    ofDefinition base ⟶ ofDefinition extension.target :=
  ⟨extension.refines⟩

/-- A missing source rule makes a strict arrow impossible.  This negative
boundary prevents the category from degenerating into an indiscrete category
whose arrows merely assert their desired conclusion. -/
theorem hom_isEmpty_of_missing
    {source target : RuleRetaining} {ruleId : RuleId} {rule : RuleSchema}
    (sourceHas : source.definition.1.lookupRule? ruleId = some rule)
    (targetMissing : target.definition.1.lookupRule? ruleId = none) :
    IsEmpty (source ⟶ target) := by
  constructor
  intro morphism
  exact not_ruleLookupRefines_of_missing sourceHas targetMissing
    morphism.refines

/-! ## Chronological DAG evidence -/

/-- A chronological proof DAG accepted by the generic checker at one root.
Backward references and ordered premises are checked by `checkDAGBlocks`; no
acyclicity proposition is trusted separately. -/
structure CheckedDAG (object : RuleRetaining) (goal : Pattern) where
  rootId : Nat
  blocks : List (List DAGNode)
  accepted : checkDAGBlocks object.definition goal rootId blocks = true

namespace CheckedDAG

/-- An accepted DAG reconstructs an exact raw proof and a Type-valued
derivation with the same erasure. -/
theorem exactDerivation {object : RuleRetaining} {goal : Pattern}
    (dag : CheckedDAG object goal) :
    ∃ (proof : RawProof) (derivation : Derivation object.definition goal),
      expandDAGBlocks? object.definition goal dag.rootId dag.blocks =
          some proof ∧
        derivation.erase = proof :=
  checkDAGBlocks_exact_derivation dag.accepted

/-- Strict certificate-GSLT arrows preserve the meaning of every accepted DAG.
The same reconstructed raw proof is accepted by the target definition and
has a transported target derivation.  This is the basic naturality square for
the generic DAG checker. -/
theorem transportMeaning {source target : RuleRetaining} {goal : Pattern}
    (morphism : source ⟶ target) (dag : CheckedDAG source goal) :
    ∃ (proof : RawProof) (derivation : Derivation target.definition goal),
      expandDAGBlocks? source.definition goal dag.rootId dag.blocks =
          some proof ∧
        derivation.erase = proof ∧
        checkRaw target.definition goal proof = true := by
  rcases dag.exactDerivation with ⟨proof, sourceDerivation, expanded, erased⟩
  let targetDerivation : Derivation target.definition goal :=
    morphism.mapDerivation sourceDerivation
  refine ⟨proof, targetDerivation, expanded, ?_, ?_⟩
  · change (sourceDerivation.transport morphism.refines).erase = proof
    rw [Derivation.erase_transport, erased]
  · exact checkRaw_true_of_ruleLookupRefines morphism.refines
      (expandDAGBlocks?_sound expanded)

end CheckedDAG

end RuleRetaining

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
