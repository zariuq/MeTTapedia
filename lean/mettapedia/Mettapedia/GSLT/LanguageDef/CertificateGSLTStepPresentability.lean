import Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-!
# The boundary of direct step-relation presentation

Which rewrite relations can be handed to the generic inference checker as
proof systems over their own terms?  The checker's schema language answers
with a decidable admission predicate (`Presentation.isValidV2`), and this
module extracts its sharpest necessary condition: every rule pattern must
be free of collection-rest matching.

Consequently a rewrite rule that decomposes a bag — matching
`{x, ...rest}` — has no direct transliteration into the current schema
language: any presentation containing such a schema is rejected, whatever
else it declares.  Bag-level steps therefore require either an explicit
decomposition/exchange proof theory (for example over binary constructors)
or a separately verified checker extension whose certificate records the
bag decomposition.  This theorem does not put bag semantics beyond
CertificateGSLT in principle; it pins the boundary of this checker format.

The positive side of the boundary is exercised in
`CertificateGSLTStepPresentabilityCanary`: a small hand-authored trace theory with
congruence, reflexive-transitive trace judgments, checkable traces whose
evidence carries strictly more than their endpoints, and a trace DAG that
shares a common axiom sub-derivation.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

theorem isValidV1_of_isValidV2 {presentation : Presentation}
    (valid : presentation.isValidV2 = true) :
    presentation.isValidV1 = true := by
  unfold Presentation.isValidV2 at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.1.1.1

theorem rule_isValidV1_of_isValidV2 {presentation : Presentation}
    (valid : presentation.isValidV2 = true)
    {rule : RuleSchema} (mem : rule ∈ presentation.rules) :
    RuleSchema.isValidV1 rule = true := by
  have baseValid := isValidV1_of_isValidV2 valid
  unfold Presentation.isValidV1 at baseValid
  simp only [Bool.and_eq_true] at baseValid
  exact List.all_eq_true.mp baseValid.1.2 rule mem

/-- Admission forces every rule pattern to be collection-rest free. -/
theorem rule_patterns_restFree_of_isValidV2 {presentation : Presentation}
    (valid : presentation.isValidV2 = true)
    {rule : RuleSchema} (mem : rule ∈ presentation.rules) :
    (RuleSchema.patterns rule).all patternHasNoCollectionRest = true := by
  have ruleValid := rule_isValidV1_of_isValidV2 valid mem
  unfold RuleSchema.isValidV1 at ruleValid
  simp only [Bool.and_eq_true] at ruleValid
  exact ruleValid.1.2

/-- The impossibility direction of the boundary: one collection-rest rule
pattern rejects the entire presentation, independently of every other
declaration.  Bag-matching rewrite rules therefore have no direct
schema transliteration. -/
theorem isValidV2_eq_false_of_collectionRest_rule
    {presentation : Presentation} {rule : RuleSchema}
    (mem : rule ∈ presentation.rules)
    (restful :
      (RuleSchema.patterns rule).all patternHasNoCollectionRest = false) :
    presentation.isValidV2 = false := by
  cases valid : presentation.isValidV2 with
  | false => rfl
  | true =>
      rw [rule_patterns_restFree_of_isValidV2 valid mem] at restful
      exact Bool.noConfusion restful

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
