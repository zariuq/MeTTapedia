import Mettapedia.Languages.Metamath.InferenceProjection

/-!
# Structural invariants exposed by Metamath inference projection

The executable projector records uniqueness with a Boolean length comparison
after `List.eraseDups`.  Runtime substitution correspondence instead consumes
the proposition-level `List.Nodup` invariant.  This module proves that bridge
and exposes it for caller frames, stored assertion views, successful prefix
projections, and successfully generated presentations.

No assertion-application or runtime-step correspondence is claimed here.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge

/-- Deduplication cannot increase the length of a string list. -/
private theorem eraseDups_length_le : (values : List String) →
    values.eraseDups.length ≤ values.length
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.succ_le_succ_iff]
      exact
        (eraseDups_length_le
          (values.filter fun candidate => !candidate == value)).trans
        (List.length_filter_le (fun candidate => !candidate == value) values)
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le
    (List.length_filter_le (fun candidate => !candidate == value) values)

/-- The projector's executable no-loss test entails ordinary list
uniqueness.  The proof is independent of the particular hypothesis view. -/
theorem nodup_of_eraseDups_length_eq :
    (values : List String) →
      values.eraseDups.length = values.length → values.Nodup
  | [] => by simp
  | value :: values => by
      intro hlength
      rw [List.eraseDups_cons] at hlength
      simp only [List.length_cons, Nat.succ.injEq] at hlength
      let filtered := values.filter fun candidate => !candidate == value
      change filtered.eraseDups.length = values.length at hlength
      have heraseLe : filtered.eraseDups.length ≤ filtered.length :=
        eraseDups_length_le filtered
      have hfilterLe : filtered.length ≤ values.length :=
        List.length_filter_le (fun candidate => !candidate == value) values
      have hvaluesLe : values.length ≤ filtered.length := by
        rw [← hlength]
        exact heraseLe
      have hfilterLength : filtered.length = values.length :=
        Nat.le_antisymm hfilterLe hvaluesLe
      have hall : ∀ candidate ∈ values,
          !candidate == value = true :=
        List.length_filter_eq_length_iff.mp hfilterLength
      have hfilterEq : filtered = values :=
        List.filter_eq_self.mpr hall
      have hrecursive :
          filtered.eraseDups.length = filtered.length :=
        hlength.trans hfilterLength.symm
      have htail : filtered.Nodup :=
        nodup_of_eraseDups_length_eq filtered hrecursive
      rw [hfilterEq] at htail
      simp only [List.nodup_cons]
      refine ⟨?_, htail⟩
      intro hmember
      have hfalse := hall value hmember
      simp at hfalse
termination_by values => values.length
decreasing_by
  simpa [filtered] using Nat.lt_succ_of_le
    (List.length_filter_le (fun candidate => !candidate == value) values)

/-- The Boolean floating-variable gate exposes the proposition-level key
uniqueness used by finite-substitution semantics. -/
theorem floatingVariableNames_nodup_of_hasUniqueFloatingVariables
    (hypotheses : List HypothesisView)
    (hunique : hasUniqueFloatingVariables hypotheses = true) :
    (floatingVariableNames hypotheses).Nodup := by
  apply nodup_of_eraseDups_length_eq
  unfold hasUniqueFloatingVariables at hunique
  simpa using hunique

/-- A frame accepted by the projection discipline has distinct floating
variable names. -/
theorem floatingVariableNames_nodup_of_frameProjectionValid
    (frame : RuntimeFrame) (hypotheses : List HypothesisView)
    (hvalid : frameProjectionValid frame hypotheses = true) :
    (floatingVariableNames hypotheses).Nodup := by
  apply floatingVariableNames_nodup_of_hasUniqueFloatingVariables
  simp only [frameProjectionValid, Bool.and_eq_true] at hvalid
  exact hvalid.1.1.1.1.2

/-- Every revalidated assertion view exposes distinct substitution keys. -/
theorem assertion_floatingVariableNames_nodup_of_assertionViewValid
    (declaredConstants declaredVariables : List String)
    (assertion : AssertionView)
    (hvalid :
      assertionViewValid declaredConstants declaredVariables assertion = true) :
    (floatingVariableNames assertion.hypotheses).Nodup := by
  apply floatingVariableNames_nodup_of_frameProjectionValid assertion.frame
  simp only [assertionViewValid, Bool.and_eq_true] at hvalid
  exact hvalid.1.1.1

/-- Membership in a valid inspectable projection entails the assertion's
distinct floating-key invariant. -/
theorem assertion_floatingVariableNames_nodup_of_prefixProjectionValid
    (projection : PrefixProjection) (assertion : AssertionView)
    (hvalid : prefixProjectionValid projection = true)
    (hmember : assertion ∈ projection.assertions) :
    (floatingVariableNames assertion.hypotheses).Nodup := by
  apply assertion_floatingVariableNames_nodup_of_assertionViewValid
    projection.declaredConstants projection.declaredVariables assertion
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
  exact List.all_eq_true.mp hvalid.1.2 assertion hmember

/-- A successful live-prefix projection exposes its repeated validation gate
as an ordinary proposition. -/
theorem prefixProjectionValid_of_projectPrefix?_eq_some
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectPrefix? db = some projection) :
    prefixProjectionValid projection = true := by
  unfold projectPrefix? at hproject
  simp only [bind, Option.bind_eq_some_iff] at hproject
  obtain ⟨_guardError, _herror, _guardWellFormed, _hwellFormed,
    _guardDV, _hdv, _guardEmbedded, _hembedded, _guardDeclarations,
    _hdeclarations, activeHypotheses, _hactive, _guardFrame, _hframe,
    assertions, _hassertions, _guardProjection, hprojectionValid,
    hprojection⟩ := hproject
  cases hprojection
  unfold guard at hprojectionValid
  split at hprojectionValid
  · assumption
  · simp at hprojectionValid

/-- Hence every assertion retained by a successful live-prefix projection has
distinct generated substitution keys. -/
theorem projectedAssertion_floatingVariableNames_nodup
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    (floatingVariableNames assertion.hypotheses).Nodup :=
  assertion_floatingVariableNames_nodup_of_prefixProjectionValid
    projection assertion
      (prefixProjectionValid_of_projectPrefix?_eq_some db projection hproject)
      hmember

/-- A successfully generated raw presentation likewise exposes the validation
gate independently of later V2 admission. -/
theorem prefixProjectionValid_of_presentationOfProjection?_eq_some
    (projection : PrefixProjection) (presentation : Presentation)
    (hprojection :
      presentationOfProjection? projection = some presentation) :
    prefixProjectionValid projection = true := by
  unfold presentationOfProjection? at hprojection
  simp only [Option.bind_eq_bind] at hprojection
  rw [Option.bind_eq_some_iff] at hprojection
  rcases hprojection with ⟨_witness, hguard, _⟩
  unfold guard at hguard
  split at hguard
  · assumption
  · simp at hguard

/-- Consequently a projected assertion used to generate a successful
presentation has distinct floating keys. -/
theorem generatedAssertion_floatingVariableNames_nodup
    (projection : PrefixProjection) (presentation : Presentation)
    (assertion : AssertionView)
    (hprojection :
      presentationOfProjection? projection = some presentation)
    (hmember : assertion ∈ projection.assertions) :
    (floatingVariableNames assertion.hypotheses).Nodup :=
  assertion_floatingVariableNames_nodup_of_prefixProjectionValid
    projection assertion
      (prefixProjectionValid_of_presentationOfProjection?_eq_some
        projection presentation hprojection)
      hmember

section Examples

private def distinctFloatingHypotheses : List HypothesisView :=
  [ .floating "wx" "wff" "x"
  , .essential "ess" ⟨"|-", [.var "x"]⟩
  , .floating "wy" "wff" "y" ]

private def duplicateFloatingHypotheses : List HypothesisView :=
  [ .floating "wx" "wff" "x"
  , .floating "wx-again" "setvar" "x" ]

/-- Positive boundary: essential hypotheses contribute no key, and distinct
floating hypotheses remain ordered and unique. -/
example : hasUniqueFloatingVariables distinctFloatingHypotheses = true := by
  decide

example : (floatingVariableNames distinctFloatingHypotheses).Nodup := by
  exact floatingVariableNames_nodup_of_hasUniqueFloatingVariables
    distinctFloatingHypotheses (by decide)

/-- Negative boundary: two floating hypotheses for the same variable fail the
executable gate and proposition-level uniqueness. -/
example : hasUniqueFloatingVariables duplicateFloatingHypotheses = false := by
  decide

example : ¬(floatingVariableNames duplicateFloatingHypotheses).Nodup := by
  decide

end Examples

end Mettapedia.Languages.Metamath.InferenceProjection
