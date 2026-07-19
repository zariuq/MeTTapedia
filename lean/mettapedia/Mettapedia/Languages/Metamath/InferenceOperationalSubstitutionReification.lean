import Mettapedia.Languages.Metamath.InferenceOperationalExprReification
import Mettapedia.Languages.Metamath.InferenceProjectionInvariants
import Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge
import Mettapedia.Languages.Metamath.InferenceAssertionResultFrame

/-!
# Canonical finite substitutions from operational Metamath substitutions

An operational `Metamath.Spec.Subst` is total, while the generated inference
calculus records one finite binding for each authored floating hypothesis.
This file constructs that authored-order list by canonically reifying every
operational image relative to the caller's active variable names.

Using the original total substitution as the fallback is essential: the
resulting finite substitution totalizes extensionally to the original
function, including variables absent from the callee frame.  Reverse formula
substitution additionally states the precise caller/callee classification
boundary: source constants must not be reclassified as caller variables;
source variables are replaced and need no such caller-side condition.
-/

namespace Mettapedia.Languages.Metamath.InferenceOperationalSubstitutionReification

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge
open Mettapedia.Languages.Metamath.InferenceAssertionResultFrame
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceOperationalExprReification

/-! ## Authored-order finite image -/

/-- Traverse projected hypotheses in authored order, retaining exactly the
floating hypotheses and canonically reifying their total substitution images.
Essential hypotheses contribute no binding. -/
def reifyOperationalSubstitution (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst) :
    List HypothesisView → FiniteSubstitution
  | [] => []
  | .floating _label _typecode variableName :: hypotheses =>
      { variableName
        replacement := reifyOperationalExpr callerActiveNames
          (specSubstitution ⟨variableName⟩) } ::
        reifyOperationalSubstitution callerActiveNames specSubstitution
          hypotheses
  | .essential _label _formula :: hypotheses =>
      reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses

/-- The finite key list is exactly the floating-hypothesis list, including its
authored order. -/
theorem reifyOperationalSubstitution_keys
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView) :
    (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses).map FormulaBinding.variableName =
      floatingVariableNames hypotheses := by
  induction hypotheses with
  | nil => rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis <;>
        simp [reifyOperationalSubstitution, floatingVariableNames,
          HypothesisView.floatingVariable?, ih]

/-- Lookup in the canonical finite image is exactly floating-name membership,
and the replacement is forced to be the canonical reification of that total
image.  Duplicate floating hypotheses, if supplied outside projection, do not
change the replacement. -/
theorem lookup_reifyOperationalSubstitution_iff
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (variableName : String) (replacement : ConstantHeadedFormula) :
    LookupSemantics
        (reifyOperationalSubstitution callerActiveNames specSubstitution
          hypotheses)
        variableName replacement ↔
      variableName ∈ floatingVariableNames hypotheses ∧
        replacement = reifyOperationalExpr callerActiveNames
          (specSubstitution ⟨variableName⟩) := by
  induction hypotheses with
  | nil => simp [reifyOperationalSubstitution, LookupSemantics,
      floatingVariableNames]
  | cons hypothesis hypotheses ih =>
      cases hypothesis with
      | floating label typecode headVariable =>
          change
            ({ variableName, replacement } : FormulaBinding) ∈
                ({ variableName := headVariable
                   replacement := reifyOperationalExpr callerActiveNames
                     (specSubstitution ⟨headVariable⟩) } :
                  FormulaBinding) ::
                  reifyOperationalSubstitution callerActiveNames
                    specSubstitution hypotheses ↔
              variableName ∈
                  headVariable :: floatingVariableNames hypotheses ∧
                replacement = reifyOperationalExpr callerActiveNames
                  (specSubstitution ⟨variableName⟩)
          constructor
          · intro hlookup
            rcases List.mem_cons.mp hlookup with hhead | htail
            · have hname : variableName = headVariable :=
                congrArg FormulaBinding.variableName hhead
              have hreplacement : replacement =
                  reifyOperationalExpr callerActiveNames
                    (specSubstitution ⟨headVariable⟩) :=
                congrArg FormulaBinding.replacement hhead
              subst variableName
              exact ⟨by simp, hreplacement⟩
            · have htail' := ih.mp htail
              exact ⟨by simp [htail'.1], htail'.2⟩
          · rintro ⟨hname, hreplacement⟩
            rcases List.mem_cons.mp hname with hhead | htail
            · subst variableName
              subst replacement
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _
                (ih.mpr ⟨htail, hreplacement⟩)
      | essential label formula =>
          exact ih

/-- Every authored floating hypothesis contributes its exact canonical
binding. -/
theorem lookup_reifyOperationalSubstitution_of_floating
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    {hypotheses : List HypothesisView}
    {label typecode variableName : String}
    (hmember : .floating label typecode variableName ∈ hypotheses) :
    LookupSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      variableName
      (reifyOperationalExpr callerActiveNames
        (specSubstitution ⟨variableName⟩)) := by
  apply (lookup_reifyOperationalSubstitution_iff callerActiveNames
    specSubstitution hypotheses variableName _).mpr
  constructor
  · simp only [floatingVariableNames, List.mem_filterMap]
    exact ⟨.floating label typecode variableName, hmember, rfl⟩
  · rfl

/-- Distinct projected floating names give distinct finite-substitution keys. -/
theorem reifyOperationalSubstitution_keysUnique
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (hnames : (floatingVariableNames hypotheses).Nodup) :
    SubstitutionKeysUnique
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses) := by
  unfold SubstitutionKeysUnique
  rw [reifyOperationalSubstitution_keys]
  exact hnames

/-- Every replacement in the canonical finite image obeys the caller's active
name classification. -/
theorem reifyOperationalSubstitution_replacement_respectsFrame
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    {variableName : String} {replacement : ConstantHeadedFormula}
    (hlookup : LookupSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      variableName replacement) :
    formulaSymbolsRespectFrame callerActiveNames replacement = true := by
  have hreplacement :=
    (lookup_reifyOperationalSubstitution_iff callerActiveNames
      specSubstitution hypotheses variableName replacement).mp hlookup
  rw [hreplacement.2]
  exact reifyOperationalExpr_respectsFrame callerActiveNames
    (specSubstitution ⟨variableName⟩)

/-- Canonical lookup images have exactly the same ordered, duplicate-preserving
variable classification as the original operational substitution images. -/
theorem lookup_varsInExpr_eq_bodyVariables_reifyOperationalSubstitution
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    {variableName : String} {replacement : ConstantHeadedFormula}
    (hlookup : LookupSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      variableName replacement) :
    Metamath.Spec.varsInExpr
        (callerActiveNames.map Metamath.Spec.Variable.mk)
        (specSubstitution ⟨variableName⟩) =
      (BodyVariables replacement.body).map
        Metamath.Spec.Variable.mk := by
  have hreplacement :=
    (lookup_reifyOperationalSubstitution_iff callerActiveNames
      specSubstitution hypotheses variableName replacement).mp hlookup
  rw [hreplacement.2]
  exact varsInExpr_eq_bodyVariables_reifyOperationalExpr
    callerActiveNames (specSubstitution ⟨variableName⟩)

/-! ## Exact totalization -/

/-- Totalization with the original operational substitution as fallback agrees
pointwise with that substitution on every variable, including absent keys. -/
theorem operationalSubstitution_reifyOperationalSubstitution_apply
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (queriedVariable : Metamath.Spec.Variable) :
    operationalSubstitution specSubstitution
        (reifyOperationalSubstitution callerActiveNames specSubstitution
          hypotheses)
        queriedVariable =
      specSubstitution queriedVariable := by
  induction hypotheses with
  | nil => rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis with
      | essential label formula =>
          exact ih
      | floating label typecode variableName =>
          simp only [reifyOperationalSubstitution, operationalSubstitution]
          by_cases hname : variableName = queriedVariable.v
          · rw [if_pos hname,
              operationalExpr_reifyOperationalExpr]
            have hvariable :
                (Metamath.Spec.Variable.mk variableName) = queriedVariable :=
              Metamath.Spec.Variable.ext _ _ hname
            rw [hvariable]
          · rw [if_neg hname]
            exact ih

/-- Function-level form of exact totalization.  No key-uniqueness premise is
needed because duplicate authored names receive the same total image. -/
theorem operationalSubstitution_reifyOperationalSubstitution
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView) :
    operationalSubstitution specSubstitution
        (reifyOperationalSubstitution callerActiveNames specSubstitution
          hypotheses) =
      specSubstitution := by
  funext queriedVariable
  exact operationalSubstitution_reifyOperationalSubstitution_apply
    callerActiveNames specSubstitution hypotheses queriedVariable

/-! ## Reverse formula substitution -/

/-- The minimal caller-side condition for reifying an operational substitution
result back into tagged formula substitution: source constants survive
substitution, so none may be a caller-active name.  Source variables are
replaced and intentionally impose no caller-side classification requirement. -/
def FormulaConstantsAvoid (callerActiveNames : List String)
    (source : ConstantHeadedFormula) : Prop :=
  ∀ constantName, .const constantName ∈ source.body →
    constantName ∉ callerActiveNames

/-- Canonically reifying the operational `applySubst` result constructs exact
finite formula-substitution semantics. -/
theorem spec_applySubst_to_formulaSubstitutionSemantics
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (hnames : (floatingVariableNames hypotheses).Nodup)
    (source : ConstantHeadedFormula)
    (hsourceRespect :
      formulaSymbolsRespectFrame (floatingVariableNames hypotheses) source =
        true)
    (hconstants : FormulaConstantsAvoid callerActiveNames source) :
    FormulaSubstitutionSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      source
      (reifyOperationalExpr callerActiveNames
        (Metamath.Spec.applySubst
          ((floatingVariableNames hypotheses).map
            Metamath.Spec.Variable.mk)
          specSubstitution (operationalExpr source))) := by
  let finiteSubstitution :=
    reifyOperationalSubstitution callerActiveNames specSubstitution hypotheses
  have hlookup : ∀ {variableName : String},
      .var variableName ∈ source.body →
        ∃ replacement : ConstantHeadedFormula,
          LookupSemantics finiteSubstitution variableName replacement := by
    intro variableName hmember
    have hsymbol := List.all_eq_true.mp hsourceRespect
      (.var variableName) hmember
    have hname : variableName ∈ floatingVariableNames hypotheses := by
      simpa [symbolRespectsFrame] using
        (List.contains_iff_mem.mp hsymbol)
    refine ⟨reifyOperationalExpr callerActiveNames
      (specSubstitution ⟨variableName⟩), ?_⟩
    exact (lookup_reifyOperationalSubstitution_iff callerActiveNames
      specSubstitution hypotheses variableName _).mpr ⟨hname, rfl⟩
  obtain ⟨resultBody, hbody⟩ :=
    bodySubstitution_exists_of_lookupSemantics hlookup
  let intermediate : ConstantHeadedFormula :=
    { typecode := source.typecode, body := resultBody }
  have hsemantics :
      FormulaSubstitutionSemantics finiteSubstitution source intermediate :=
    ⟨rfl, hbody⟩
  have hunique : SubstitutionKeysUnique finiteSubstitution :=
    reifyOperationalSubstitution_keysUnique callerActiveNames
      specSubstitution hypotheses hnames
  have hreplacements : ∀ variableName replacement,
      LookupSemantics finiteSubstitution variableName replacement →
        formulaSymbolsRespectFrame callerActiveNames replacement = true := by
    intro variableName replacement hbinding
    exact reifyOperationalSubstitution_replacement_respectsFrame
      callerActiveNames specSubstitution hypotheses hbinding
  have hintermediateRespect :
      formulaSymbolsRespectFrame callerActiveNames intermediate = true :=
    formulaSubstitutionSemantics_result_respects callerActiveNames
      hsemantics hconstants hreplacements
  have herasure :=
    formulaSubstitutionSemantics_to_spec_applySubst
      specSubstitution hunique (floatingVariableNames hypotheses)
      hsourceRespect hsemantics
  rw [operationalSubstitution_reifyOperationalSubstitution] at herasure
  have hcanonical :
      intermediate =
        reifyOperationalExpr callerActiveNames
          (Metamath.Spec.applySubst
            ((floatingVariableNames hypotheses).map
              Metamath.Spec.Variable.mk)
            specSubstitution (operationalExpr source)) :=
    eq_reifyOperationalExpr_of_respectsFrame callerActiveNames intermediate _
      hintermediateRespect herasure.symm
  rw [← hcanonical]
  exact hsemantics

/-- Arbitrary-result form of the reverse constructor. -/
theorem formulaSubstitutionSemantics_of_spec_applySubst
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (hnames : (floatingVariableNames hypotheses).Nodup)
    (source : ConstantHeadedFormula)
    (result : Metamath.Spec.Expr)
    (hsourceRespect :
      formulaSymbolsRespectFrame (floatingVariableNames hypotheses) source =
        true)
    (hconstants : FormulaConstantsAvoid callerActiveNames source)
    (happly :
      Metamath.Spec.applySubst
          ((floatingVariableNames hypotheses).map
            Metamath.Spec.Variable.mk)
          specSubstitution (operationalExpr source) = result) :
    FormulaSubstitutionSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      source (reifyOperationalExpr callerActiveNames result) := by
  rw [← happly]
  exact spec_applySubst_to_formulaSubstitutionSemantics callerActiveNames
    specSubstitution hypotheses hnames source hsourceRespect hconstants

/-! ## Reverse disjoint-variable semantics -/

/-- The exact callee-side coverage needed to materialize the two finite
bindings queried by each DV pair.  Unlike `frameDVValid`, this predicate does
not require an orientation or no-self condition that reverse DV semantics does
not use on the callee side. -/
def DVVariablesCovered (hypotheses : List HypothesisView)
    (calleeFrame : RuntimeFrame) : Prop :=
  ∀ pair ∈ calleeFrame.dj.toList,
    pair.1 ∈ floatingVariableNames hypotheses ∧
      pair.2 ∈ floatingVariableNames hypotheses

/-- The ordinary projection frame gate supplies the weaker coverage
predicate. -/
theorem dvVariablesCovered_of_frameDVValid
    (hypotheses : List HypothesisView) (calleeFrame : RuntimeFrame)
    (hvalid :
      frameDVValid calleeFrame (floatingVariableNames hypotheses) = true) :
    DVVariablesCovered hypotheses calleeFrame := by
  intro pair hpair
  simp only [frameDVValid] at hvalid
  have hpairValid := List.all_eq_true.mp hvalid pair hpair
  simp only [Bool.and_eq_true] at hpairValid
  exact ⟨List.contains_iff_mem.mp hpairValid.1.2,
    List.contains_iff_mem.mp hpairValid.2⟩

/-- Declarative `dvRel` directly supplies the generated symmetric pair
membership.  Its inequality component is additional information needed only
in the opposite, generated-to-declarative direction. -/
theorem spec_dvRel_to_dvRelation (pairs : List (String × String))
    (leftName rightName : String)
    (hrelation : Metamath.Spec.dvRel (ToSpecDVPairs pairs)
      ⟨leftName⟩ ⟨rightName⟩) :
    DVRelation pairs leftName rightName := by
  rcases hrelation.2 with hforward | hreverse
  · exact Or.inl ((mem_toSpecDVPairs_iff pairs leftName rightName).mp
      hforward)
  · exact Or.inr ((mem_toSpecDVPairs_iff pairs rightName leftName).mp
      hreverse)

/-- Declarative operational `dvOK` constructs the generated finite DV
semantics for the canonical substitution image.  Explicit callee-variable
coverage supplies both finite lookups.  No caller no-self premise is needed in
this reverse direction because declarative `dvRel` already contains stored
forward-or-reverse pair membership. -/
theorem spec_dvOK_to_dvOKSemantics
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (callerFrame calleeFrame : RuntimeFrame)
    (hcalleeCoverage : DVVariablesCovered hypotheses calleeFrame)
    (hSpec :
      Metamath.Spec.dvOK
        (callerActiveNames.map Metamath.Spec.Variable.mk)
        (ToSpecDVPairs calleeFrame.dj.toList)
        (ToSpecDVPairs callerFrame.dj.toList)
        specSubstitution) :
    DVOKSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      callerFrame calleeFrame := by
  intro pair hpair
  rcases pair with ⟨leftVariable, rightVariable⟩
  have hpairCovered :=
    hcalleeCoverage (leftVariable, rightVariable) hpair
  have hleftName :
      leftVariable ∈ floatingVariableNames hypotheses :=
    hpairCovered.1
  have hrightName :
      rightVariable ∈ floatingVariableNames hypotheses :=
    hpairCovered.2
  let leftReplacement := reifyOperationalExpr callerActiveNames
    (specSubstitution ⟨leftVariable⟩)
  let rightReplacement := reifyOperationalExpr callerActiveNames
    (specSubstitution ⟨rightVariable⟩)
  have hleftLookup : LookupSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      leftVariable leftReplacement :=
    (lookup_reifyOperationalSubstitution_iff callerActiveNames
      specSubstitution hypotheses leftVariable leftReplacement).mpr
      ⟨hleftName, rfl⟩
  have hrightLookup : LookupSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      rightVariable rightReplacement :=
    (lookup_reifyOperationalSubstitution_iff callerActiveNames
      specSubstitution hypotheses rightVariable rightReplacement).mpr
      ⟨hrightName, rfl⟩
  refine ⟨leftReplacement, rightReplacement,
    hleftLookup, hrightLookup, ?_⟩
  have hspecPair := hSpec ⟨leftVariable⟩ ⟨rightVariable⟩
    ((mem_toSpecDVPairs_iff calleeFrame.dj.toList
      leftVariable rightVariable).mpr hpair)
  intro leftName hleft rightName hright
  have hleftClassification :=
    lookup_varsInExpr_eq_bodyVariables_reifyOperationalSubstitution
      callerActiveNames specSubstitution hypotheses hleftLookup
  have hrightClassification :=
    lookup_varsInExpr_eq_bodyVariables_reifyOperationalSubstitution
      callerActiveNames specSubstitution hypotheses hrightLookup
  have hleftSpec :
      (Metamath.Spec.Variable.mk leftName) ∈
        Metamath.Spec.varsInExpr
          (callerActiveNames.map Metamath.Spec.Variable.mk)
          (specSubstitution ⟨leftVariable⟩) := by
    rw [hleftClassification]
    exact List.mem_map.mpr ⟨leftName, hleft, rfl⟩
  have hrightSpec :
      (Metamath.Spec.Variable.mk rightName) ∈
        Metamath.Spec.varsInExpr
          (callerActiveNames.map Metamath.Spec.Variable.mk)
          (specSubstitution ⟨rightVariable⟩) := by
    rw [hrightClassification]
    exact List.mem_map.mpr ⟨rightName, hright, rfl⟩
  exact spec_dvRel_to_dvRelation callerFrame.dj.toList leftName rightName
    (hspecPair ⟨leftName⟩ hleftSpec ⟨rightName⟩ hrightSpec)

/-! ## Executable boundaries -/

section Examples

private def exampleSpecSubstitution : Metamath.Spec.Subst :=
    fun queriedVariable =>
  if queriedVariable.v = "x" then
    ⟨⟨"wff"⟩, ["a", "c", "a"]⟩
  else if queriedVariable.v = "y" then
    ⟨⟨"wff"⟩, ["b"]⟩
  else
    ⟨⟨"wff"⟩, [queriedVariable.v]⟩

private def exampleHypotheses : List HypothesisView :=
  [ .floating "wx" "wff" "x"
  , .essential "ess" ⟨"|-", [.var "x"]⟩
  , .floating "wy" "wff" "y" ]

/-- Positive boundary: essential hypotheses are omitted, while floating
bindings retain authored order and canonical caller-relative tags. -/
example :
    reifyOperationalSubstitution ["a", "b"] exampleSpecSubstitution
        exampleHypotheses =
      [ ⟨"x", ⟨"wff", [.var "a", .const "c", .var "a"]⟩⟩
      , ⟨"y", ⟨"wff", [.var "b"]⟩⟩ ] := by
  decide

/-- Positive fallback boundary: a variable absent from the finite authored
list is evaluated by the original total substitution. -/
example :
    operationalSubstitution exampleSpecSubstitution
        (reifyOperationalSubstitution ["a", "b"]
          exampleSpecSubstitution exampleHypotheses)
        ⟨"z"⟩ =
      ⟨⟨"wff"⟩, ["z"]⟩ := by
  decide

private def formulaHypotheses : List HypothesisView :=
  [.floating "wx" "wff" "x"]

private def formulaSource : ConstantHeadedFormula :=
  ⟨"|-", [.const "(", .var "x", .const ")"]⟩

/-- The reverse formula constructor replaces the callee variable while
retaining constants that remain constants for the caller. -/
example :
    FormulaSubstitutionSemantics
      (reifyOperationalSubstitution ["a"] exampleSpecSubstitution
        formulaHypotheses)
      formulaSource
      (reifyOperationalExpr ["a"]
        (Metamath.Spec.applySubst [⟨"x"⟩] exampleSpecSubstitution
          (operationalExpr formulaSource))) := by
  apply spec_applySubst_to_formulaSubstitutionSemantics
  · decide
  · decide
  · intro constantName hmember
    simp [formulaSource] at hmember
    rcases hmember with rfl | rfl
    · decide
    · decide

private def classificationMismatchSource : ConstantHeadedFormula :=
  ⟨"|-", [.const "a"]⟩

/-- Negative boundary: the formula is valid for an empty callee variable set,
but its surviving constant would be reclassified as a caller variable. -/
example :
    formulaSymbolsRespectFrame [] classificationMismatchSource = true ∧
      ¬FormulaConstantsAvoid ["a"] classificationMismatchSource := by
  constructor
  · decide
  · intro havoid
    exact havoid "a" (by simp [classificationMismatchSource]) (by simp)

/-- Consequently canonical operational reification is not finite tagged
substitution semantics when the constant-avoidance condition is dropped. -/
example :
    ¬FormulaSubstitutionSemantics
      (reifyOperationalSubstitution ["a"] exampleSpecSubstitution [])
      classificationMismatchSource
      (reifyOperationalExpr ["a"]
        (Metamath.Spec.applySubst [] exampleSpecSubstitution
          (operationalExpr classificationMismatchSource))) := by
  intro hsemantics
  rcases hsemantics with ⟨_typecode, hbody⟩
  cases hbody

private def exampleCallerFrame : RuntimeFrame :=
  ⟨#[ ("a", "b") ], #[]⟩

private def exampleCalleeFrame : RuntimeFrame :=
  ⟨#[ ("x", "y") ], #["wx", "wy"]⟩

private theorem exampleSpecDVOK :
    Metamath.Spec.dvOK [⟨"a"⟩, ⟨"b"⟩]
      (ToSpecDVPairs exampleCalleeFrame.dj.toList)
      (ToSpecDVPairs exampleCallerFrame.dj.toList)
      exampleSpecSubstitution := by
  unfold Metamath.Spec.dvOK
  intro leftVariable rightVariable hpair
  rcases leftVariable with ⟨leftVariable⟩
  rcases rightVariable with ⟨rightVariable⟩
  have hpairNames :
      (leftVariable, rightVariable) ∈
        exampleCalleeFrame.dj.toList :=
    (mem_toSpecDVPairs_iff exampleCalleeFrame.dj.toList
      leftVariable rightVariable).mp hpair
  change (leftVariable, rightVariable) ∈ [("x", "y")] at hpairNames
  simp only [List.mem_singleton] at hpairNames
  have hleft : leftVariable = "x" :=
    congrArg Prod.fst hpairNames
  have hright : rightVariable = "y" :=
    congrArg Prod.snd hpairNames
  subst leftVariable
  subst rightVariable
  dsimp only
  intro leftResult hleft rightResult hright
  have hleftResult : leftResult = ⟨"a"⟩ := by
    simpa [Metamath.Spec.varsInExpr, exampleSpecSubstitution] using hleft
  have hrightResult : rightResult = ⟨"b"⟩ := by
    simpa [Metamath.Spec.varsInExpr, exampleSpecSubstitution] using hright
  subst leftResult
  subst rightResult
  have hdistinct :
      DVPairNamesDistinct exampleCallerFrame.dj.toList := by
    apply dvPairNamesDistinct_of_strictOrderAll
    decide
  apply (dvRelation_iff_spec_dvRel exampleCallerFrame.dj.toList
    hdistinct "a" "b").mp
  apply Or.inl
  change ("a", "b") ∈ [("a", "b")]
  simp

/-- The reverse DV constructor is executable on a canonical two-variable
instance. -/
example :
    DVOKSemantics
      (reifyOperationalSubstitution ["a", "b"] exampleSpecSubstitution
        [.floating "wx" "wff" "x", .floating "wy" "wff" "y"])
      exampleCallerFrame exampleCalleeFrame := by
  apply spec_dvOK_to_dvOKSemantics
  · apply dvVariablesCovered_of_frameDVValid
    decide
  · exact exampleSpecDVOK

end Examples

end Mettapedia.Languages.Metamath.InferenceOperationalSubstitutionReification
