import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef
import Mettapedia.OSLF.Framework.SelectedNativeTypeDemand
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Selected native-type demand for FOF Skolemization

The Skolemization presentation contains twenty-six authored root rewrites:
fifteen term/environment operations followed by eleven formula operations.
This module assigns each root its actual result carrier and selects both
endpoints of its one-dimensional modal profile.  The demand is the complete
finite input to the shared selected-native-type generator; it does not define
a second typing calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNativeTypeDemand

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationLanguageDef

/-- The validated authored Skolemization transformation. -/
def source : ValidatedLanguageDef :=
  TptpFofSkolemizationLanguageDef.validated

/-- Result carrier of one authored root, in exact rewrite order. -/
def rootType (index : Fin source.language.rewrites.length) : TypeExpr :=
  match index.val with
  | 0 => .base "TptpFofSkolemTerm:TermShiftResult"
  | 1 => .base "TptpFofSkolemTerm:TermShiftResult"
  | 2 => .base "TptpFofSkolemTerm:TermShiftResult"
  | 3 => .base "TptpFofSkolemTerm:TermsShiftResult"
  | 4 => .base "TptpFofSkolemTerm:TermsShiftResult"
  | 5 => .base "TptpFofSkolemTerm:EnvShiftResult"
  | 6 => .base "TptpFofSkolemTerm:EnvShiftResult"
  | 7 => .base "TptpFofSkolemTerm:VariablesResult"
  | 8 => .base "TptpFofSkolemTerm:VariablesResult"
  | 9 => .base "TptpFofSkolemTerm:LookupResult"
  | 10 => .base "TptpFofSkolemTerm:LookupResult"
  | 11 => .base "TptpFofSkolemTerm:TranslateTermResult"
  | 12 => .base "TptpFofSkolemTerm:TranslateTermResult"
  | 13 => .base "TptpFofSkolemTerm:TranslateTermsResult"
  | 14 => .base "TptpFofSkolemTerm:TranslateTermsResult"
  | 15 => .base "TptpFofSkolemize:MatrixResult"
  | 16 => .base "TptpFofSkolemize:MatrixResult"
  | 17 => .base "TptpFofSkolemize:MatrixResult"
  | 18 => .base "TptpFofSkolemize:MatrixResult"
  | 19 => .base "TptpFofSkolemize:MatrixResult"
  | 20 => .base "TptpFofSkolemize:MatrixResult"
  | 21 => .base "TptpFofSkolemize:MatrixResult"
  | 22 => .base "TptpFofSkolemize:MatrixResult"
  | _ => .base "TptpFofSkolemize:FormResult"

set_option maxHeartbeats 800000 in
private theorem rootLeftTyped
    (index : Fin source.language.rewrites.length) :
    HasType source.language
      (FreeTypeContext.ofList
        (source.language.rewrites.get index).typeContext) []
      (source.language.rewrites.get index).left (rootType index) := by
  apply checkHasType_sound
  fin_cases index <;> decide +kernel

set_option maxHeartbeats 800000 in
private theorem rootRightTyped
    (index : Fin source.language.rewrites.length) :
    HasType source.language
      (FreeTypeContext.ofList
        (source.language.rewrites.get index).typeContext) []
      (source.language.rewrites.get index).right (rootType index) := by
  apply checkHasType_sound
  fin_cases index <;> decide +kernel

private theorem rootSourceIsObject
    (index : Fin source.language.rewrites.length) :
    isObjectPattern (source.language.rewrites.get index).left = true := by
  fin_cases index <;> decide +kernel

/-- Exact sorting evidence for one authored Skolemization root. -/
def rootTyping (index : Fin source.language.rewrites.length) :
    DisplayedRewriteTyping source where
  site := DisplayedRewriteSite.root source.language index
  rewriteType := rootType index
  focusBoundPrefix := []
  focusType := rootType index
  rewriteLeftTyped := rootLeftTyped index
  rewriteRightTyped := rootRightTyped index
  sourceIsObject := rootSourceIsObject index
  focusTyped := rootLeftTyped index

/-- Every generated carrier root is declared by the authored source. -/
theorem rootTyping_grounded
    (index : Fin source.language.rewrites.length) :
    SelectedNativeTypeFoundation.CarrierGrounded (rootTyping index) := by
  intro object objectMembership name nameMembership
  have roots :
      SelectedNativeTypeFoundation.requiredCarrierRoots
          (rootTyping index) = [rootType index, rootType index] := by
    simp [SelectedNativeTypeFoundation.requiredCarrierRoots, rootTyping,
      DisplayedContextProfile.carrierTypes,
      DisplayedContextProfile.bindings,
      DisplayedContextProfile.variableNames,
      DisplayedContextProfile.externalFreeFvarNames,
      DisplayedRewriteSite.root]
  rw [roots] at objectMembership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at objectMembership
  rcases objectMembership with rfl | rfl
  all_goals
    fin_cases index <;>
      simp [rootType, TypeExpr.baseNames] at nameMembership <;>
      subst name <;> decide

/-- One explicitly profiled authored root. -/
def profiledRoot (index : Fin source.language.rewrites.length)
    (code : CarrierUniverseSignature.Code) :
    ProfiledRewriteOccurrence source :=
  ProfiledRewriteOccurrence.constant
    (rootTyping index) (rootTyping_grounded index) code

/-- Complete authored-order selection: star then box at every root. -/
def selectedOccurrences : List (ProfiledRewriteOccurrence source) :=
  (List.finRange source.language.rewrites.length).flatMap fun index =>
    [profiledRoot index .star, profiledRoot index .box]

/-- Complete sparse native-type demand for Skolemization. -/
def demand : SelectedNativeTypeDemand source :=
  ⟨selectedOccurrences⟩

/-- Negative control omitting every box endpoint. -/
def allStarDemand : SelectedNativeTypeDemand source :=
  ⟨(List.finRange source.language.rewrites.length).map fun index =>
    profiledRoot index .star⟩

theorem source_rewrite_count : source.language.rewrites.length = 26 := by
  rfl

theorem selectedOccurrences_count : selectedOccurrences.length = 52 := by
  decide

theorem allStarOccurrences_count : allStarDemand.occurrences.length = 26 := by
  decide

/-- A half-profile cannot masquerade as the complete selected demand. -/
theorem demand_ne_allStarDemand : demand ≠ allStarDemand := by
  intro equality
  have lengths := congrArg
    (fun selected => selected.occurrences.length) equality
  change 52 = 26 at lengths
  omega

#print axioms rootTyping_grounded
#print axioms selectedOccurrences_count
#print axioms demand_ne_allStarDemand

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNativeTypeDemand
