import Mettapedia.Languages.MeTTa.PureKernel.Universe.SyntacticJudgmentalPi

/-!
# Conversion-enriched fibres of the Prime syntactic natural model

The ordinary syntactic natural model indexes terms by exact formed types.
Dependent computation sometimes changes that raw type only up to judgmental
conversion: the second projection of `(a, b)` initially has type
`B[fst (a, b)]`, while its beta target `b` has type `B[a]`.

This module retains that change explicitly.  `TypeConversion` is a
proof-relevant structural conversion between two formed type codes in one
context.  `TermTransport` carries both the source term and the conversion
used to view its unchanged raw code in the target fibre.  Nothing is
quotiented into Lean equality, and no checker is replayed during transport.

The result is the small two-dimensional enrichment required by dependent
Sigma computation and, later, by GSLT-IL refinement cells and NIK receipts.

The present layer is deliberately the exact proof-relevant refinement of the
existing syntactic `Conv`: its endpoints are formed, while intermediate raw
syntax is retained by the conversion receipt.  A semantic claim that every
intermediate is itself formed requires the separately named computation-
preservation authority of the declaration package; it is not inferred here
from endpoint formation.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
namespace SyntacticConversionEnrichment

open CategoryTheory
open SyntacticContextual
open SyntacticJudgmentalPi
open ProofRelevantStructuralComputation
open Mettapedia.TypeTheory.JudgmentalEquality

universe uEvidence

/-! ## Formed-type conversion -/

/-- A proof-relevant judgmental conversion between two already formed
endpoints in one context.  Formation is carried by the endpoints and the
exact raw structural conversion path is retained independently. -/
structure TypeConversion
    (retained : RetainedRoot.{uEvidence} rules)
    {context : FormedContext rules}
    (source target : TypeOver context) where
  receipt : StructuralConversionReceipt retained.computation rules.headEq
    source.code target.code

namespace TypeConversion

/-- Exact conversion support after replacing the retained root's support
relation by the authored root relation of the presentation. -/
private theorem retainedConversion_support_iff_nonempty
    {Head : Type} {rules : Rules Head}
    (retained : RetainedRoot.{uEvidence} rules)
    {left right : Tm Head n} :
    @Conv Head n rules.headEq left right rules.computation ↔
      Nonempty
        (@StructuralConversionReceipt Head retained.computation rules.headEq
          n left right) := by
  constructor
  · intro support
    have retainedSupport :
        Conv rules.headEq left right retained.computation.support :=
      Relation.EqvGen.mono
        (fun _ _ step =>
          (StructuralStepReceipt.support_iff_nonempty
            retained.computation rules.headEq).mpr
            ((retained_support_iff_nonempty retained).mp step))
        support
    exact
      (StructuralConversionReceipt.support_iff_nonempty
        retained.computation rules.headEq).mp retainedSupport
  · rintro ⟨conversion⟩
    exact Relation.EqvGen.mono
      (fun _ _ step =>
        (retained_support_iff_nonempty retained).mpr
          ((StructuralStepReceipt.support_iff_nonempty
            retained.computation rules.headEq).mp step))
      conversion.toSupport

/-- Forget only the conversion path, retaining proposition-valued support. -/
def toSupport
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {source target : TypeOver context}
    (conversion : TypeConversion retained source target) :
    Conv rules.headEq source.code target.code rules.computation :=
  (retainedConversion_support_iff_nonempty retained).mpr
    ⟨conversion.receipt⟩

/-- Identity conversion retains an explicit reflexive receipt. -/
def refl
    (retained : RetainedRoot.{uEvidence} rules)
    {context : FormedContext rules} (type : TypeOver context) :
    TypeConversion retained type type where
  receipt := ConversionEvidence.refl
    (computation := rawStructuralComputation retained.computation
      rules.headEq context.arity)
    type.code

/-- Reverse a formed-type conversion without discarding its path. -/
def symm
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {source target : TypeOver context}
    (conversion : TypeConversion retained source target) :
    TypeConversion retained target source where
  receipt := .symm conversion.receipt

/-- Compose formed-type conversions while retaining the intermediate type
code and both paths. -/
def trans
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules}
    {source middle target : TypeOver context}
    (first : TypeConversion retained source middle)
    (second : TypeConversion retained middle target) :
    TypeConversion retained source target where
  receipt := .trans first.receipt second.receipt

/-- Exact support theorem: ordinary conversion between formed endpoints is
precisely inhabitation of the retained conversion fibre. -/
theorem support_iff_nonempty
    (retained : RetainedRoot.{uEvidence} rules)
    {context : FormedContext rules} {source target : TypeOver context} :
    Conv rules.headEq source.code target.code rules.computation ↔
      Nonempty (TypeConversion retained source target) := by
  constructor
  · intro support
    rcases
        (retainedConversion_support_iff_nonempty retained).mp support with
      ⟨receipt⟩
    exact ⟨⟨receipt⟩⟩
  · rintro ⟨conversion⟩
    exact conversion.toSupport

/-- Formed-type conversion is stable under every typed context
substitution. -/
def reindex
    {retained : RetainedRoot.{uEvidence} rules}
    {sourceContext targetContext : FormedContext rules}
    {source target : TypeOver targetContext}
    (conversion : TypeConversion retained source target)
    (morphism : sourceContext ⟶ targetContext) :
    TypeConversion retained (source.reindex morphism)
      (target.reindex morphism) where
  receipt := conversion.receipt.substitute morphism.substitution

/-- If ordinary conversion support is absent, no proof-relevant formed-type
conversion can be fabricated. -/
@[reducible] def isEmpty_of_not_support
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {source target : TypeOver context}
    (unsupported :
      ¬ Conv rules.headEq source.code target.code rules.computation) :
    IsEmpty (TypeConversion retained source target) :=
  ⟨fun conversion => unsupported conversion.toSupport⟩

end TypeConversion

/-! ## Terms transported along retained type conversion -/

/-- A term together with the exact judgmental conversion used to transport
its type.  The raw term code is not changed. -/
structure TermTransport
    (retained : RetainedRoot.{uEvidence} rules)
    {context : FormedContext rules}
    (source target : TypeOver context) where
  sourceTerm : Term context source
  typeConversion : TypeConversion retained source target

namespace TermTransport

/-- The target-fibre term, constructed by the native conversion rule.  The
proof-relevant conversion remains available in the enclosing transport. -/
def targetTerm
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {source target : TypeOver context}
    (transport : TermTransport retained source target) :
    Term context target where
  code := transport.sourceTerm.code
  typed := .conv transport.sourceTerm.typed
    transport.typeConversion.toSupport

@[simp] theorem targetTerm_code
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {source target : TypeOver context}
    (transport : TermTransport retained source target) :
    transport.targetTerm.code = transport.sourceTerm.code :=
  rfl

/-- Identity transport does not change the intrinsic term. -/
def refl
    (retained : RetainedRoot.{uEvidence} rules)
    {context : FormedContext rules} {type : TypeOver context}
    (term : Term context type) : TermTransport retained type type where
  sourceTerm := term
  typeConversion := TypeConversion.refl retained type

@[simp] theorem refl_targetTerm
    (retained : RetainedRoot.{uEvidence} rules)
    {context : FormedContext rules} {type : TypeOver context}
    (term : Term context type) :
    (TermTransport.refl retained term).targetTerm = term := by
  apply Term.ext
  rfl

/-- Continue a transport through a second retained type conversion. -/
def compose
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules}
    {source middle target : TypeOver context}
    (transport : TermTransport retained source middle)
    (conversion : TypeConversion retained middle target) :
    TermTransport retained source target where
  sourceTerm := transport.sourceTerm
  typeConversion := transport.typeConversion.trans conversion

/-- Reindex a term transport along a typed context substitution. -/
def reindex
    {retained : RetainedRoot.{uEvidence} rules}
    {sourceContext targetContext : FormedContext rules}
    {source target : TypeOver targetContext}
    (transport : TermTransport retained source target)
    (morphism : sourceContext ⟶ targetContext) :
    TermTransport retained (source.reindex morphism)
      (target.reindex morphism) where
  sourceTerm := transport.sourceTerm.reindex morphism
  typeConversion := transport.typeConversion.reindex morphism

/-- Constructing the target term commutes with context substitution. -/
theorem targetTerm_reindex
    {retained : RetainedRoot.{uEvidence} rules}
    {sourceContext targetContext : FormedContext rules}
    {source target : TypeOver targetContext}
    (transport : TermTransport retained source target)
    (morphism : sourceContext ⟶ targetContext) :
    transport.targetTerm.reindex morphism =
      (transport.reindex morphism).targetTerm := by
  apply Term.ext
  rfl

end TermTransport

/-! ## Axiom audit -/

#print axioms TypeConversion.support_iff_nonempty
#print axioms TypeConversion.reindex
#print axioms TypeConversion.isEmpty_of_not_support
#print axioms TermTransport.targetTerm
#print axioms TermTransport.refl_targetTerm
#print axioms TermTransport.targetTerm_reindex

end SyntacticConversionEnrichment
end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
