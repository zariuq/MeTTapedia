import Mettapedia.GSLT.Parsing.HornSpecializationBody

/-!
# Semantic specialization heads are exhaustively enumerable

This module joins the certificate-independent meaning of an admitted Horn
specialization to the finite, apart-renamed head enumerator.  It establishes
that head discovery depends only on the admitted program and unification
semantics, not on an operational specialization certificate.
-/

namespace Mettapedia.GSLT.Parsing.HornSemanticEnumeration

open HornCertificate HornSpecialization HornUnification HornHeadEnumeration
open HornSpecializationHead HornSpecializationBody

theorem semanticSpecializationHead_semanticallyUnifiable
    {program : Program} {parseRelation : String} {rule : Rule}
    {substitution : SymbolicSubstitution} {categories : CategoryTable}
    {production : StreamProduction}
    (semantic : SemanticSpecializes program parseRelation rule substitution
      categories production) :
    ∃ instantiatedHead,
      instantiateSymbolicAtom substitution rule.head = some instantiatedHead ∧
      SemanticallyUnifiable instantiatedHead rule := by
  cases semantic with
  | intro head body parsedHead member substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
      refine ⟨head, instantiatedHead, symbolicLPSubstitution substitution, ?_⟩
      rw [symbolicLPSubstitution_apply_queryAtom]
      exact
        (symbolicLPSubstitution_apply_encodeAtom substitution rule.head head
          instantiatedHead).symm

/-- Every semantically valid specialization head is found by the executable
finite head scan at a common bound for its admitted finite program. -/
theorem semanticSpecialization_head_is_enumerated
    {program : Program} {parseRelation : String} {rule : Rule}
    {substitution : SymbolicSubstitution} {categories : CategoryTable}
    {production : StreamProduction}
    (semantic : SemanticSpecializes program parseRelation rule substitution
      categories production) :
    ∃ instantiatedHead maximumFuel result,
      instantiateSymbolicAtom substitution rule.head = some instantiatedHead ∧
      result ∈ matchHeads program instantiatedHead maximumFuel ∧
      HeadMatches instantiatedHead maximumFuel rule result := by
  obtain ⟨instantiatedHead, headInstantiated, unifiable⟩ :=
    semanticSpecializationHead_semanticallyUnifiable semantic
  have ruleMember : rule ∈ program := by
    cases semantic with
    | intro head body parsedHead member substitutionValid categoriesValid
        instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
        category start finish => exact member
  obtain ⟨maximumFuel, bounded⟩ :=
    finiteProgram_has_unification_bound program instantiatedHead
  obtain ⟨result, resultMember, matched⟩ :=
    matchHeads_semantically_exhaustive program instantiatedHead maximumFuel
      bounded rule ruleMember unifiable
  exact ⟨instantiatedHead, maximumFuel, result, headInstantiated,
    resultMember, matched⟩

/-- Production enumeration has no caller-selected search bound: total
unification finds every semantically valid admitted specialization head. -/
theorem semanticSpecialization_head_is_enumeratedTotal
    {program : Program} {parseRelation : String} {rule : Rule}
    {substitution : SymbolicSubstitution} {categories : CategoryTable}
    {production : StreamProduction}
    (semantic : SemanticSpecializes program parseRelation rule substitution
      categories production) :
    ∃ instantiatedHead result,
      instantiateSymbolicAtom substitution rule.head = some instantiatedHead ∧
      result ∈ matchHeadsTotal program instantiatedHead ∧
      TotalHeadMatches instantiatedHead rule result := by
  obtain ⟨instantiatedHead, headInstantiated, unifiable⟩ :=
    semanticSpecializationHead_semanticallyUnifiable semantic
  have ruleMember : rule ∈ program := by
    cases semantic with
    | intro head body parsedHead member substitutionValid categoriesValid
        instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
        category start finish => exact member
  obtain ⟨result, resultMember, matched⟩ :=
    matchHeadsTotal_semantically_exhaustive program instantiatedHead rule
      ruleMember unifiable
  exact ⟨instantiatedHead, result, headInstantiated, resultMember, matched⟩

theorem classRule_semantic_head_is_enumerated :
    ∃ instantiatedHead maximumFuel result,
      instantiateSymbolicAtom classCertificate.substitution
          classCertificate.rule.head = some instantiatedHead ∧
      result ∈ matchHeads exampleProgram instantiatedHead maximumFuel ∧
      HeadMatches instantiatedHead maximumFuel classCertificate.rule result :=
  semanticSpecialization_head_is_enumerated
    classRule_has_certificate_independent_semantics

theorem classRule_semantic_head_is_enumeratedTotal :
    ∃ instantiatedHead result,
      instantiateSymbolicAtom classCertificate.substitution
          classCertificate.rule.head = some instantiatedHead ∧
      result ∈ matchHeadsTotal exampleProgram instantiatedHead ∧
      TotalHeadMatches instantiatedHead classCertificate.rule result :=
  semanticSpecialization_head_is_enumeratedTotal
    classRule_has_certificate_independent_semantics

end Mettapedia.GSLT.Parsing.HornSemanticEnumeration
