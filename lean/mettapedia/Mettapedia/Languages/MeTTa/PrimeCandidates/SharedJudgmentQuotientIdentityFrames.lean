import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientComprehension
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientIdentity

/-!
# Native based-context comparisons on the shared interpretation

Projection, right endpoint and retained identity witness determine a map
into the actual two-binder context. No choice of motive, elimination rule
or raw annotation equality is needed for that uniqueness statement.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientIdentityFrames

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment FormationSensitiveContextual
open SharedJudgmentQuotientInterpretation SharedJudgmentQuotientComprehension
open SharedJudgmentTypeInterpretation
open Mettapedia.TypeTheory
open ContextualBasedIdentityOperations (basedContext baseProjection rightEndpoint witnessType)

variable {assembly : Assembly}

/-- Both binders matter: the outer projection and varying endpoint first
determine the endpoint context map, then the path variable determines the
full based-context map. -/
theorem based_arrow_unique
    (identity : ContextualTypeOperations.IdentityFormationOperations (QuotientCwf.cwf assembly.rules))
    {source target : QuotientCwf.QContext assembly.rules}
    {type : QuotientCwf.Ty target} (left : QuotientCwf.Tm target type)
    {first second : source ⟶ basedContext identity left}
    (projection : first ≫ baseProjection identity left = second ≫ baseProjection identity left)
    (endpoint : (QuotientCwf.tmSub (rightEndpoint identity left) first).val =
      (QuotientCwf.tmSub (rightEndpoint identity left) second).val)
    (witness : (QuotientCwf.tmSub (QuotientCwf.vz (witnessType identity left)) first).val =
      (QuotientCwf.tmSub (QuotientCwf.vz (witnessType identity left)) second).val) :
    first = second := by
  apply QuotientCwf.pair_unique (witnessType identity left)
  · apply QuotientCwf.pair_unique type
    · exact (Category.assoc first _ _).trans
        (projection.trans (Category.assoc second _ _).symm)
    · change QuotientCwf.totalSub (QuotientCwf.vz type).val
          (first ≫ QuotientCwf.wk (witnessType identity left)) =
        QuotientCwf.totalSub (QuotientCwf.vz type).val
          (second ≫ QuotientCwf.wk (witnessType identity left))
      exact (QuotientCwf.totalSub_comp (QuotientCwf.vz type).val first
        (QuotientCwf.wk (witnessType identity left))).trans
        (endpoint.trans (QuotientCwf.totalSub_comp (QuotientCwf.vz type).val second
          (QuotientCwf.wk (witnessType identity left))).symm)
  · exact witness

private theorem inverse_unique {C : Type} [Category C] {source target : C}
    {first second : source ⟶ target} {firstInverse secondInverse : target ⟶ source}
    (same : first = second) (left : firstInverse ≫ first = 𝟙 target)
    (right : second ≫ secondInverse = 𝟙 source) : firstInverse = secondInverse := by
  calc
    firstInverse = firstInverse ≫ (second ≫ secondInverse) := by
      rw [right, Category.comp_id]
    _ = (firstInverse ≫ first) ≫ secondInverse := by rw [same, Category.assoc]
    _ = secondInverse := by rw [left, Category.id_comp]

private theorem pullback_injective {Head : Type} {rules : Rules Head}
    {source target : QuotientCwf.QContext rules}
    {forward : source ⟶ target} {backward : target ⟶ source}
    (inverse : backward ≫ forward = 𝟙 target)
    {first second : QuotientCwf.Ty target}
    (same : QuotientCwf.tySub first forward = QuotientCwf.tySub second forward) :
    first = second := by
  have pulled := congrArg (fun family => QuotientCwf.tySub family backward) same
  simpa only [← QuotientCwf.tySub_comp, inverse, QuotientCwf.tySub_id] using pulled

/-- The independently supplied interpretation graphs determine every field
of a qualified frame. In particular, its motive and method cannot be
changed while retaining the same native source and comparison laws. -/
theorem frame_unique
    {operations : FrameOperations (QuotientCwf.cwf assembly.rules)} {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    {first second : JFrame (data assembly) operations source type left motive method}
    (firstMeaning : JFrameMeaning (data assembly) operations first)
    (secondMeaning : JFrameMeaning (data assembly) operations second) :
    first = second := by
  rcases first with ⟨firstFormed, firstType, firstLeft, firstMotive, firstBase, firstComparison, firstReflexivity⟩
  rcases second with ⟨secondFormed, secondType, secondLeft, secondMotive, secondBase, secondComparison, secondReflexivity⟩
  have typeEqual := type_meaning_unique firstMeaning.typeMeaning secondMeaning.typeMeaning
  dsimp only at typeEqual
  cases typeEqual
  have leftEqual : firstLeft = secondLeft :=
    Subtype.ext (term_meaning_value_unique firstMeaning.leftMeaning secondMeaning.leftMeaning)
  cases leftEqual
  have forwardEqual : firstComparison.forward = secondComparison.forward := by
    apply based_arrow_unique operations.identity firstLeft
    · exact substitution_meaning_unique firstMeaning.projection secondMeaning.projection
    · exact term_meaning_value_unique firstMeaning.rightMeaning secondMeaning.rightMeaning
    · exact term_meaning_value_unique firstMeaning.witnessMeaning secondMeaning.witnessMeaning
  have backwardEqual : firstComparison.backward = secondComparison.backward :=
    inverse_unique forwardEqual firstMeaning.inverse.1 secondMeaning.inverse.2
  have comparisonEqual : firstComparison = secondComparison := by
    cases firstComparison
    cases secondComparison
    cases forwardEqual
    cases backwardEqual
    rfl
  cases comparisonEqual
  have motiveEqual : firstMotive = secondMotive :=
    pullback_injective firstMeaning.inverse.1
      (type_meaning_unique firstMeaning.motiveMeaning secondMeaning.motiveMeaning)
  cases motiveEqual
  have baseEqual : firstBase = secondBase :=
    Subtype.ext (term_meaning_value_unique firstMeaning.methodMeaning secondMeaning.methodMeaning)
  cases baseEqual
  have reflexivityEqual : firstReflexivity = secondReflexivity :=
    substitution_meaning_unique firstMeaning.reflexivityMeaning secondMeaning.reflexivityMeaning
  cases reflexivityEqual
  rfl

#print axioms based_arrow_unique
#print axioms frame_unique

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientIdentityFrames
