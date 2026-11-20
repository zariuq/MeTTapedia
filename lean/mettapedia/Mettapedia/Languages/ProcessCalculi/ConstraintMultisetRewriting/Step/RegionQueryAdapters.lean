import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionObservations

/-!
# Conservative exact-query admission adapters

Exact query lists enter the region-query admission through their actual
`Query.toRegion` images. Empty query lists retain plain occurrence admission.
These laws make no claim that an at-model footprint establishes a query's
observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RegionQueryAdapters

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

theorem valid_exact_iff (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (queries : List (PredicateQueryAdmission.Query T S O)) (before : Configuration T O) (selection : Selection O) :
    PredicateQueryAdmission.RegionValid A label rule (queries.map PredicateQueryAdmission.Query.toRegion) before selection ↔
      PredicateQueryAdmission.Valid A label rule queries before selection :=
  PredicateQueryAdmission.valid_iff_regionValid.symm

theorem valid_empty_iff (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (before : Configuration T O) (selection : Selection O) :
    PredicateQueryAdmission.RegionValid A label rule [] before selection ↔ selection.Valid A label rule before :=
  PredicateQueryAdmission.regionValid_nil_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RegionQueryAdapters
