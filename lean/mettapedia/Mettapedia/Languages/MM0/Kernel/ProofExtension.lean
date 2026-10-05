import Mettapedia.Languages.MM0.Kernel.TheoryAdmission
import Mettapedia.Languages.MM0.Kernel.SignatureExtension

/-!
# Preserving the same MM0 evidence through checked theory growth

Successful checking is monotone under preservation of existing signature
entries. The conversion witness, proof witness, context, hypothesis list and
computed conclusion are unchanged. Refusals are not monotone: a previously
unknown symbol may become available later.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

theorem ConvWitness.Checks.extendSignatures {beforeTerms afterTerms : TermSignature}
    {beforeDefinitions afterDefinitions : Definition.Signature}
    (terms : ∀ index declaration, beforeTerms index = some declaration →
      afterTerms index = some declaration)
    (definitions : ∀ index body, beforeDefinitions index = some body → afterDefinitions index = some body)
    {context : Context} {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : Checks beforeTerms beforeDefinitions context witness left right sort) :
    Checks afterTerms afterDefinitions context witness left right sort := by
  induction checked using Checks.rec
      (motive_2 := fun children left right binders _ =>
        ChecksArgs afterTerms afterDefinitions context children left right binders) with
  | refl typed => exact .refl (typed.extendSignature terms)
  | symm _ ih => exact .symm ih
  | trans _ _ ihFirst ihSecond => exact .trans ihFirst ihSecond
  | congruence known _ ih => exact .congruence (terms _ _ known) ih
  | unfold known unfolded typed =>
      exact .unfold (terms _ _ known) (unfolded.extendSignatures terms definitions)
        (typed.extendSignature terms)
  | nil => exact .nil
  | cons leftFits rightFits _ _ ihChild ihTail =>
      exact .cons (leftFits.extendSignature terms) (rightFits.extendSignature terms) ihChild ihTail

theorem ProofWitness.Checks.extendSignatures {beforeTerms afterTerms : TermSignature}
    {beforeDefinitions afterDefinitions : Definition.Signature}
    {beforeTheorems afterTheorems : TheoremSignature}
    (terms : ∀ index declaration, beforeTerms index = some declaration →
      afterTerms index = some declaration)
    (definitions : ∀ index body, beforeDefinitions index = some body → afterDefinitions index = some body)
    (theorems : ∀ index declaration, beforeTheorems index = some declaration →
      afterTheorems index = some declaration)
    {context : Context} {hypotheses : List Preterm} {witness : ProofWitness} {expression : Preterm}
    (checked : Checks beforeTerms beforeDefinitions beforeTheorems context hypotheses witness expression) :
    Checks afterTerms afterDefinitions afterTheorems context hypotheses witness expression := by
  induction checked using Checks.rec
      (motive_2 := fun children expressions _ =>
        ChecksList afterTerms afterDefinitions afterTheorems context hypotheses children expressions) with
  | hyp known => exact .hyp known
  | theoremApp known instanceProof _ ih =>
      exact .theoremApp (theorems _ _ known) (instanceProof.extendSignature terms) ih
  | conversion converted _ ih => exact .conversion (converted.extendSignatures terms definitions) ih
  | nil => exact .nil
  | cons _ _ ihChild ihTail => exact .cons ihChild ihTail

theorem Derives.extendSignatures {beforeTerms afterTerms : TermSignature}
    {beforeDefinitions afterDefinitions : Definition.Signature}
    {beforeTheorems afterTheorems : TheoremSignature}
    (terms : ∀ index declaration, beforeTerms index = some declaration →
      afterTerms index = some declaration)
    (definitions : ∀ index body, beforeDefinitions index = some body → afterDefinitions index = some body)
    (theorems : ∀ index declaration, beforeTheorems index = some declaration →
      afterTheorems index = some declaration)
    {context : Context} {hypotheses : List Preterm} {expression : Preterm}
    (derived : Derives beforeTerms beforeDefinitions beforeTheorems context hypotheses expression) :
    Derives afterTerms afterDefinitions afterTheorems context hypotheses expression := by
  obtain ⟨witness, checked⟩ := derived.certificate_exists
  exact (checked.extendSignatures terms definitions theorems).derives

namespace Theory

theorem Extends.preserves_proof {before after : Theory} (extension : Extends before after)
    {context : Context} {hypotheses : List Preterm} {witness : ProofWitness} {expression : Preterm}
    (accepted : ProofWitness.proof? before.termSignature before.definitionSignature
      before.theoremSignature context hypotheses witness = some expression) :
    ProofWitness.proof? after.termSignature after.definitionSignature after.theoremSignature
      context hypotheses witness = some expression :=
  ((ProofWitness.proof_sound accepted).extendSignatures
    extension.terms extension.definitions extension.theorems).eval

theorem Extends.preserves_check {before after : Theory} (extension : Extends before after)
    {context : Context} {hypotheses : List Preterm} {witness : ProofWitness} {expression : Preterm}
    (accepted : ProofWitness.check before.termSignature before.definitionSignature
      before.theoremSignature context hypotheses witness expression = true) :
    ProofWitness.check after.termSignature after.definitionSignature after.theoremSignature
      context hypotheses witness expression = true :=
  (ProofWitness.check_iff _ _ _ _ _ _ _).mpr
    (((ProofWitness.check_iff _ _ _ _ _ _ _).mp accepted).extendSignatures
      extension.terms extension.definitions extension.theorems)

theorem Runs.preserves_check {before after : Theory} {admissions : List Admission}
    (runs : Runs before admissions after)
    {context : Context} {hypotheses : List Preterm} {witness : ProofWitness} {expression : Preterm}
    (accepted : ProofWitness.check before.termSignature before.definitionSignature
      before.theoremSignature context hypotheses witness expression = true) :
    ProofWitness.check after.termSignature after.definitionSignature after.theoremSignature
      context hypotheses witness expression = true := runs.extends.preserves_check accepted

end Theory

end Mettapedia.Languages.MM0.Kernel
