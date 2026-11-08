import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsSeparationFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitude

/-!
# Frames and interference verdicts

R33's paths of a region (`AmplitudeRuns.regionPaths`) are the values the region carries at
amplitudes (`regionPaths_eq_regionValues`). With `AmplitudeRuns.verdict_iff_query`:

* **At an admitted frame, every verdict on the region is the verdict on what the query saw**
  (`verdict_frame`).
* **A query admits exactly the frames that change no interference verdict on its region**
  (`frame_admitted_iff_verdicts`): the general `frame_admitted_iff_values` at amplitudes.
* **A cancellation holds beside an admitted frame exactly when it holds without it**
  (`destructive_frame`).

A frame that brings a nonzero path into the region refutes a cancellation
(`AmplitudeRuns.destructive_refuted_by_arrival`), and such a frame is refused by the query
(`census_frame_iff`): the query's side condition and the stability of its verdicts are one
condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (PredicateQuery)
open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude)
open AmplitudeRuns (pathsOf regionPaths Destructive verdict_iff_query)

universe uT uS uO

namespace SeparationRuns

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (wave : T → Amplitude)

omit [DecidableEq O] in
/-- R33's paths of a region are the values the region carries, at amplitudes. -/
theorem regionPaths_eq_regionValues (region : T → Bool) (C : Configuration T O) :
    regionPaths label wave region C = regionValues label wave region C :=
  rfl

/-- **At an admitted frame, every verdict on the region is the verdict on what the query saw**:
`verdict_iff_query` at the framed cut. -/
theorem verdict_frame (verdict : Multiset Amplitude → Prop) {f : Firing T S O}
    {C E : Configuration T O} {query : PredicateQuery O T}
    (member : PredicateQueryAdmission.Query.fixed query ∈ f.queries)
    (framed : f.Valid A label (tensor C E)) :
    verdict (regionPaths label wave query.region (tensor C E)) ↔
      verdict (pathsOf label wave query.seen) :=
  verdict_iff_query A label wave verdict framed member

/-- **A query admits exactly the frames that change no interference verdict on its region.** -/
theorem frame_admitted_iff_verdicts {f : Firing T S O} {C E : Configuration T O}
    {query : PredicateQuery O T} (only : f.queries = [PredicateQueryAdmission.Query.fixed query])
    (guards : ∀ check ∈ f.rule.checks, ∃ left right, check = .equal left right)
    (valid : f.Valid A label C) (apart : Disjoint C.present E.present)
    (after : Separable A (f.result label C) E) :
    f.Valid A label (tensor C E) ↔
      ∀ verdict : Multiset Amplitude → Prop,
        verdict (regionPaths label wave query.region (tensor C E)) ↔
          verdict (regionPaths label wave query.region C) :=
  frame_admitted_iff_values A label wave only guards valid apart after

/-- **A cancellation holds beside an admitted frame exactly when it holds without it.** -/
theorem destructive_frame {f : Firing T S O} {C E : Configuration T O} {query : PredicateQuery O T}
    (member : PredicateQueryAdmission.Query.fixed query ∈ f.queries) (valid : f.Valid A label C)
    (framed : f.Valid A label (tensor C E)) :
    Destructive (regionPaths label wave query.region (tensor C E)) ↔
      Destructive (regionPaths label wave query.region C) :=
  (verdict_frame A label wave Destructive member framed).trans
    (verdict_iff_query A label wave Destructive valid member).symm

end SeparationRuns

open SeparationRuns

#print axioms regionPaths_eq_regionValues
#print axioms verdict_frame
#print axioms frame_admitted_iff_verdicts
#print axioms destructive_frame

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
