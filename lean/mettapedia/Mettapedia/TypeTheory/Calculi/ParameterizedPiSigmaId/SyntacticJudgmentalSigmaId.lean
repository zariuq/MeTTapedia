import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticConversionEnrichment

/-!
# Judgmental dependent sums and identity types in the parameterized syntactic natural model

This module continues the conversion-enriched syntactic natural model with
native dependent sums and intensional identity types.  Formation,
introduction, elimination, and substitution act on intrinsic terms.  The
second Sigma beta law exposes the essential two-dimensional boundary:

* `snd (pair a b)` is initially typed in the fibre `B[fst (pair a b)]`;
* the beta target `b` inhabits `B[a]`;
* a retained conversion between those two formed types transports the source
  term before the retained term-level beta receipt is applied.

Thus computation changes a dependent judgment by explicit conversion
evidence rather than by pretending that the two raw type codes are Lean
equal.  The Tower example at the end makes that distinction nondegenerate.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SyntacticJudgmentalSigmaId

open CategoryTheory
open SyntacticContextual
open SyntacticJudgmentalPi
open SyntacticConversionEnrichment
open ProofRelevantStructuralComputation
open Mettapedia.TypeTheory.JudgmentalEquality

universe uEvidence

/-! ## Intrinsic dependent sums -/

/-- Native formation data for a dependent sum.  The result universe is
retained rather than recomputed from raw syntax. -/
structure DependentSum {rules : Rules Head}
    {context : FormedContext rules} (domain : TypeOver context)
    (codomain : TypeOver (extendContext context domain)) where
  level : Head
  isUniverse : rules.isUniverse level
  join : rules.join domain.level codomain.level level

namespace DependentSum

/-- The formed Sigma type supplied by native formation evidence. -/
def type {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain) : TypeOver context where
  code := .sigma domain.code codomain.code
  level := sum.level
  isUniverse := sum.isUniverse
  formed := .sigmaForm domain.formed domain.isUniverse codomain.formed
    codomain.isUniverse sum.join

/-- Pairing constructs an intrinsic Sigma term directly. -/
def pair {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (first : Term context domain)
    (second : Term context (instantiateType codomain first)) :
    Term context sum.type where
  code := .pair first.code second.code
  typed := by
    change HasType rules context.context (.pair first.code second.code)
      (.sigma domain.code codomain.code)
    exact HasType.pairIntro first.typed second.typed

/-- The first projection remains in the domain fibre. -/
def firstProjection {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (pair : Term context sum.type) : Term context domain where
  code := .fst pair.code
  typed := HasType.fstElim pair.typed

/-- The second projection is indexed by the first projection of the same
pair.  It is not prematurely transported to an extensionally equal fibre. -/
def secondProjection {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (pair : Term context sum.type) :
    Term context (instantiateType codomain (sum.firstProjection pair)) where
  code := .snd pair.code
  typed := by
    simpa only [instantiateType, reindex_argumentSection_code,
      firstProjection] using (HasType.sndElim pair.typed)

/-! ## Stability under context substitution -/

/-- Reindex native Sigma-formation data. -/
def reindex {rules : Rules Head} {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target) :
    DependentSum (domain.reindex morphism)
      (codomain.reindex (liftContextHom morphism domain)) where
  level := sum.level
  isUniverse := sum.isUniverse
  join := sum.join

/-- Sigma formation satisfies the same strict reindexing law as Pi
formation. -/
theorem type_reindex {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (morphism : source ⟶ target) :
    sum.type.reindex morphism = (sum.reindex morphism).type := by
  apply TypeOver.ext
  · change
      subst morphism.substitution (.sigma domain.code codomain.code) =
        .sigma (subst morphism.substitution domain.code)
          (subst (liftContextHom morphism domain).substitution codomain.code)
    simp only [Presentation.subst, liftContextHom_substitution]
    rfl
  · rfl

/-- Reindex a Sigma term and expose it in the reindexed Sigma fibre. -/
def reindexedPair {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (pair : Term target sum.type)
    (morphism : source ⟶ target) :
    Term source (sum.reindex morphism).type :=
  Term.cast (sum.type_reindex morphism) (pair.reindex morphism)

/-- Pair construction commutes with arbitrary typed context substitution. -/
theorem pair_reindex {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain)
    (first : Term target domain)
    (second : Term target (instantiateType codomain first))
    (morphism : source ⟶ target) :
    sum.reindexedPair (sum.pair first second) morphism =
      (sum.reindex morphism).pair (first.reindex morphism)
        (Term.cast (instantiateType_reindex codomain first morphism)
          (second.reindex morphism)) := by
  apply Term.ext
  simp only [reindexedPair, Term.cast_code, pair, Term.reindex,
    Presentation.subst]
  congr 1
  exact (Term.cast_code (instantiateType_reindex codomain first morphism)
    (second.reindex morphism)).symm

/-- First projection commutes with context substitution. -/
theorem firstProjection_reindex {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (pair : Term target sum.type)
    (morphism : source ⟶ target) :
    (sum.firstProjection pair).reindex morphism =
      (sum.reindex morphism).firstProjection
        (sum.reindexedPair pair morphism) := by
  apply Term.ext
  simp only [firstProjection, reindexedPair, Term.cast_code, Term.reindex,
    Presentation.subst]

/-- The dependent result type of second projection obeys Beck--Chevalley.
The first-projection reindexing theorem supplies the equality of its
arguments. -/
theorem secondProjectionType_reindex {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (pair : Term target sum.type)
    (morphism : source ⟶ target) :
    (instantiateType codomain (sum.firstProjection pair)).reindex morphism =
      instantiateType
        (codomain.reindex (liftContextHom morphism domain))
        ((sum.reindex morphism).firstProjection
          (sum.reindexedPair pair morphism)) := by
  rw [instantiateType_reindex]
  rw [sum.firstProjection_reindex pair morphism]

/-- Second projection commutes with context substitution after transporting
along its dependent result-type equality. -/
theorem secondProjection_reindex {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (sum : DependentSum domain codomain) (pair : Term target sum.type)
    (morphism : source ⟶ target) :
    Term.cast (sum.secondProjectionType_reindex pair morphism)
        ((sum.secondProjection pair).reindex morphism) =
      (sum.reindex morphism).secondProjection
        (sum.reindexedPair pair morphism) := by
  apply Term.ext
  simp only [Term.cast_code, secondProjection, reindexedPair,
    Term.reindex, Presentation.subst]
  exact Term.cast_code (sum.secondProjectionType_reindex pair morphism)
    ((sum.secondProjection pair).reindex morphism)

/-! ## Proof-relevant Sigma computation -/

/-- First-projection beta is a step inside the unchanged domain fibre. -/
def firstBetaReceipt {rules : Rules Head}
    {context : FormedContext rules}
    (retained : RetainedRoot.{uEvidence} rules)
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (first : Term context domain)
    (second : Term context (instantiateType codomain first)) :
    (termComputation retained context).Step
      (sum.firstProjection (sum.pair first second)) first :=
  .betaSigmaFst first.code second.code

/-- The opening substitutions for `fst (pair a b)` and `a` are pointwise
convertible.  The newest component carries the actual first-beta receipt;
all older components carry explicit reflexivity receipts. -/
private def firstBetaSubstitutionConversion
    {rules : Rules Head} {context : FormedContext rules}
    (retained : RetainedRoot.{uEvidence} rules)
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (first : Term context domain)
    (second : Term context (instantiateType codomain first)) :
    ∀ index,
      StructuralConversionReceipt retained.computation rules.headEq
        (subst0 (sum.firstProjection (sum.pair first second)).code index)
        (subst0 first.code index) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact .step (.betaSigmaFst first.code second.code)
  · intro prior
    exact ConversionEvidence.refl
      (computation := rawStructuralComputation retained.computation
        rules.headEq context.arity)
      (.var prior)

/-- The source and target fibres of second beta are related by the retained
pointwise substitution of first-beta evidence through the codomain. -/
def secondBetaTypeConversion {rules : Rules Head}
    {context : FormedContext rules}
    (retained : RetainedRoot.{uEvidence} rules)
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (first : Term context domain)
    (second : Term context (instantiateType codomain first)) :
    TypeConversion retained
      (instantiateType codomain
        (sum.firstProjection (sum.pair first second)))
      (instantiateType codomain first) where
  receipt := by
    change StructuralConversionReceipt retained.computation rules.headEq
      (inst0 (sum.firstProjection (sum.pair first second)).code
        codomain.code)
      (inst0 first.code codomain.code)
    exact StructuralConversionReceipt.substitutePointwise
      (sum.firstBetaSubstitutionConversion retained first second)
      codomain.code

/-- Transport second projection into the beta target's formed fibre while
retaining the complete type-conversion path. -/
def secondBetaTransport {rules : Rules Head}
    {context : FormedContext rules}
    (retained : RetainedRoot.{uEvidence} rules)
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (first : Term context domain)
    (second : Term context (instantiateType codomain first)) :
    TermTransport retained
      (instantiateType codomain
        (sum.firstProjection (sum.pair first second)))
      (instantiateType codomain first) where
  sourceTerm := sum.secondProjection (sum.pair first second)
  typeConversion := sum.secondBetaTypeConversion retained first second

/-- Second-projection beta after explicit type transport.  This receipt and
`secondBetaTypeConversion` are distinct proof-relevant dimensions. -/
def secondBetaReceipt {rules : Rules Head}
    {context : FormedContext rules}
    (retained : RetainedRoot.{uEvidence} rules)
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (first : Term context domain)
    (second : Term context (instantiateType codomain first)) :
    (termComputation retained context).Step
      (sum.secondBetaTransport retained first second).targetTerm second :=
  .betaSigmaSnd first.code second.code

/-- Retained second-beta conversion in the target fibre. -/
def secondBetaConversion {rules : Rules Head}
    {context : FormedContext rules}
    (retained : RetainedRoot.{uEvidence} rules)
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (sum : DependentSum domain codomain)
    (first : Term context domain)
    (second : Term context (instantiateType codomain first)) :
    ConversionEvidence (termComputation retained context)
      (sum.secondBetaTransport retained first second).targetTerm second :=
  .step (sum.secondBetaReceipt retained first second)

end DependentSum

/-! ## Intrinsic identity types -/

/-- The native identity type over an already formed carrier. -/
def identityType {rules : Rules Head} {context : FormedContext rules}
    (carrier : TypeOver context) (left right : Term context carrier) :
    TypeOver context where
  code := .id carrier.code left.code right.code
  level := carrier.level
  isUniverse := carrier.isUniverse
  formed := .idForm carrier.formed carrier.isUniverse left.typed right.typed

/-- Reflexivity constructs a term of the diagonal identity type directly. -/
def identityReflexivity {rules : Rules Head}
    {context : FormedContext rules} {carrier : TypeOver context}
    (term : Term context carrier) :
    Term context (identityType carrier term term) where
  code := .refl term.code
  typed := .reflIntro term.typed

/-- Identity formation commutes with context substitution. -/
theorem identityType_reindex {rules : Rules Head}
    {source target : FormedContext rules} (carrier : TypeOver target)
    (left right : Term target carrier) (morphism : source ⟶ target) :
    (identityType carrier left right).reindex morphism =
      identityType (carrier.reindex morphism) (left.reindex morphism)
        (right.reindex morphism) := by
  apply TypeOver.ext
  · rfl
  · rfl

/-- Reflexivity commutes with context substitution. -/
theorem identityReflexivity_reindex {rules : Rules Head}
    {source target : FormedContext rules} {carrier : TypeOver target}
    (term : Term target carrier) (morphism : source ⟶ target) :
    Term.cast (identityType_reindex carrier term term morphism)
        ((identityReflexivity term).reindex morphism) =
      identityReflexivity (term.reindex morphism) := by
  apply Term.ext
  rw [Term.cast_code]
  rfl

/-! ## Nondegenerate Tower controls -/


/-! ## Axiom audit -/

#print axioms DependentSum.type
#print axioms DependentSum.pair
#print axioms DependentSum.type_reindex
#print axioms DependentSum.pair_reindex
#print axioms DependentSum.secondProjection_reindex
#print axioms DependentSum.firstBetaReceipt
#print axioms DependentSum.secondBetaTypeConversion
#print axioms DependentSum.secondBetaTransport
#print axioms DependentSum.secondBetaConversion
#print axioms identityType
#print axioms identityReflexivity
#print axioms identityType_reindex
#print axioms identityReflexivity_reindex

end SyntacticJudgmentalSigmaId
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
