import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoOpening
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution

/-!
# Rho `LanguageDef` semantic adequacy

The strict-core rho calculus is authored once as `rhoCalc`.  This file checks
the reflective COMM declaration and relates its compiled right-hand side to
the existing paper-facing semantic substitution.

The selected declaration also compiles the repeated-channel equality used by
the generic matcher.  Its canonical representatives are proved to agree with
the independently developed pure-rho canonicalizer.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch

/-- The authored COMM rule has exactly one selected reflective declaration. -/
theorem rhoComm_declaration_selected :
    declarationForRule? rhoCalc rhoCommRewrite = some rhoReflectivePresentation := by
  decide +kernel

/-- The generic rule-aware matcher is definitionally specialized by the
authored rho declaration, not by an engine callback. -/
theorem matchPatternForRule_rhoComm (term : Pattern) :
    matchPatternForRule rhoCalc rhoCommRewrite term =
      matchPatternWith rhoCanonicalEquivalent rhoCommRewrite.left term := by
  simp only [matchPatternForRule, rhoComm_declaration_selected]
  rfl

/-- The compiled matcher for authored rho COMM has the independent
equivalence-parameterized relational specification on every candidate. -/
theorem matchPatternForRule_rhoComm_iff
    {term : Pattern} {bindings : Bindings} :
    bindings ∈ matchPatternForRule rhoCalc rhoCommRewrite term ↔
      MatchRelWith rhoCanonicalEquivalent rhoCommRewrite.left term bindings := by
  rw [matchPatternForRule_iff_matchRelWith_of_declaration
    rhoComm_declaration_selected]
  rfl

/-- Consequently, the executable premise-aware rule application uses the
proved pure-rho repeated-channel comparator for every candidate term. -/
theorem applyRuleWithPremisesUsing_rhoComm
    (relationEnvironment : RelationEnv) (term : Pattern) :
    applyRuleWithPremisesUsing relationEnvironment rhoCalc rhoCommRewrite term =
      (matchPatternWith rhoCanonicalEquivalent rhoCommRewrite.left term).flatMap
        (fun bindings =>
          (applyPremisesWithEnv relationEnvironment rhoCalc rhoCommRewrite.premises bindings).map
            (fun finalBindings =>
              applyBindingsForRule rhoCalc rhoCommRewrite finalBindings)) := by
  unfold applyRuleWithPremisesUsing
  rw [matchPatternForRule_rhoComm]

/-- The strict-core authored language passes its structural validation gate. -/
theorem rhoCalc_validate : rhoCalc.validate = [] := by
  exact rhoCalc_validate_eq_nil

/-- The extracted authored COMM rule is a rewrite of the strict-core language. -/
theorem rhoCommRewrite_mem : rhoCommRewrite ∈ rhoCalc.rewrites := by
  simp [rhoCalc]

/-- A missing rule reference is rejected rather than silently compiled. -/
theorem malformed_reflective_rule_rejected :
    ({ rhoCalc with
        reflectivePresentations :=
          [{ rhoReflectivePresentation with rewriteRule := "MissingComm" }] }).validate ≠ [] := by
  exact rhoCalc_missing_reflective_rule_validate_ne_nil

/-! ## Authored COMM right-hand side -/

/-- Matcher bindings for a concrete COMM occurrence. -/
def rhoCommBindings (channel body payload : Pattern) (rest : List Pattern) : Bindings :=
  [("n", channel), ("p", body), ("q", payload),
    ("rest", .collection .hashBag rest none)]

/-- Compiling the authored COMM right-hand side selects reflective
substitution and preserves the unmatched parallel components. -/
theorem applyBindingsForRule_rhoComm
    (channel body payload : Pattern) (rest : List Pattern) :
    applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel body payload rest) =
      .collection .hashBag
        (substituteReflective rhoReflectivePresentation 0
            (.apply "NQuote"
              [normalizeReflective rhoReflectivePresentation payload]) body ::
          rest)
        none := by
  rw [applyBindingsForRule, rhoComm_declaration_selected]
  simp [rhoCommRewrite, rhoCommBindings, applyBindingsReflective,
    applyBindingsReflectiveList, normalizeReflectiveReplacement,
    rhoReflectivePresentation]

/-! ## Derived-syntax agreement -/

private theorem rhoDrop_normalization_congr
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name)
    (nameIH : normalizeReflective rhoReflectivePresentation name =
      semanticNormalizeName name) :
    normalizeReflective rhoReflectivePresentation (.apply "PDrop" [name]) =
      semanticNormalizeProc (.apply "PDrop" [name]) := by
  cases typed <;>
    simp_all [normalizeReflective, normalizeReflectiveList,
      finishNormalizeReflectiveApply,
      semanticNormalizeName, semanticNormalizeProc,
      rhoReflectivePresentation]

private theorem rhoQuote_normalization_congr
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process)
    (processIH : normalizeReflective rhoReflectivePresentation process =
      semanticNormalizeProc process) :
    normalizeReflective rhoReflectivePresentation (.apply "NQuote" [process]) =
      semanticNormalizeName (.apply "NQuote" [process]) := by
  cases typed <;>
    simp_all [normalizeReflective, normalizeReflectiveList,
      finishNormalizeReflectiveApply,
      semanticNormalizeName, semanticNormalizeProc,
      rhoReflectivePresentation]

/-- Static name normalization compiled from the authored presentation agrees
exactly with the existing paper-facing name normalizer on derived names. -/
theorem normalizeReflective_rhoName_agrees
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name) :
    normalizeReflective rhoReflectivePresentation name =
      semanticNormalizeName name := by
  apply NameWellSorted.rec
    (presentation := rhoReflectivePresentation) (free := free) (t := typed)
    (motive_1 := fun _ name _ =>
      normalizeReflective rhoReflectivePresentation name =
        semanticNormalizeName name)
    (motive_2 := fun _ process _ =>
      normalizeReflective rhoReflectivePresentation process =
        semanticNormalizeProc process)
    (motive_3 := fun _ processes _ =>
      normalizeReflectiveList rhoReflectivePresentation processes =
        semanticNormalizeProcList processes)
  case quote =>
    intro bound process processTyped processIH
    exact rhoQuote_normalization_congr processTyped processIH
  case drop =>
    intro bound name nameTyped nameIH
    exact rhoDrop_normalization_congr nameTyped nameIH
  all_goals
    intros
    simp_all [normalizeReflective, normalizeReflectiveList,
      finishNormalizeReflectiveApply,
      semanticNormalizeName, semanticNormalizeProc,
      semanticNormalizeProcList, rhoReflectivePresentation]

/-- Static process normalization compiled from the authored presentation
agrees exactly with the existing normalizer on derived processes. -/
theorem normalizeReflective_rhoProc_agrees
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process) :
    normalizeReflective rhoReflectivePresentation process =
      semanticNormalizeProc process := by
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation) (free := free) (t := typed)
    (motive_1 := fun _ name _ =>
      normalizeReflective rhoReflectivePresentation name =
        semanticNormalizeName name)
    (motive_2 := fun _ process _ =>
      normalizeReflective rhoReflectivePresentation process =
        semanticNormalizeProc process)
    (motive_3 := fun _ processes _ =>
      normalizeReflectiveList rhoReflectivePresentation processes =
        semanticNormalizeProcList processes)
  case quote =>
    intro bound process processTyped processIH
    exact rhoQuote_normalization_congr processTyped processIH
  case drop =>
    intro bound name nameTyped nameIH
    exact rhoDrop_normalization_congr nameTyped nameIH
  all_goals
    intros
    simp_all [normalizeReflective, normalizeReflectiveList,
      finishNormalizeReflectiveApply,
      semanticNormalizeName, semanticNormalizeProc,
      semanticNormalizeProcList, rhoReflectivePresentation]

/-- List form of derived process-normalization agreement. -/
theorem normalizeReflective_rhoProcList_agrees
    {free : FreeSortContext} {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted rhoReflectivePresentation free bound processes) :
    normalizeReflectiveList rhoReflectivePresentation processes =
      semanticNormalizeProcList processes := by
  apply ProcListWellSorted.rec
    (presentation := rhoReflectivePresentation) (free := free) (t := typed)
    (motive_1 := fun _ name _ =>
      normalizeReflective rhoReflectivePresentation name =
        semanticNormalizeName name)
    (motive_2 := fun _ process _ =>
      normalizeReflective rhoReflectivePresentation process =
        semanticNormalizeProc process)
    (motive_3 := fun _ processes _ =>
      normalizeReflectiveList rhoReflectivePresentation processes =
        semanticNormalizeProcList processes)
  case quote =>
    intro bound process processTyped processIH
    exact rhoQuote_normalization_congr processTyped processIH
  case drop =>
    intro bound name nameTyped nameIH
    exact rhoDrop_normalization_congr nameTyped nameIH
  all_goals
    intros
    simp_all [normalizeReflective, normalizeReflectiveList,
      finishNormalizeReflectiveApply,
      semanticNormalizeName, semanticNormalizeProc,
      semanticNormalizeProcList, rhoReflectivePresentation]

/-! ## Derived substitution agreement -/

private theorem substituteNameMark_rhoName_agrees
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name)
    (depth : Nat) (replacementName : Pattern) :
    substituteNameMark rhoReflectivePresentation depth replacementName name =
      semanticSubstNameMark depth replacementName name := by
  unfold substituteNameMark semanticSubstNameMark
  rw [normalizeReflective_rhoName_agrees typed]
  generalize semanticNormalizeName name = normalized
  cases normalized <;> rfl

private theorem substituteReflective_rhoName_eq_mark
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name)
    (depth : Nat) (replacementName : Pattern) :
    substituteReflective rhoReflectivePresentation depth replacementName name =
      (substituteNameMark rhoReflectivePresentation depth replacementName name).1 := by
  cases typed with
  | bvar lookup =>
      simp only [substituteReflective, substituteNameMark, normalizeReflective]
      split <;> rfl
  | fvar lookup =>
      rfl
  | quote processTyped =>
      cases processTyped <;>
        simp [substituteReflective, substituteNameMark, normalizeReflective,
          normalizeReflectiveList, finishNormalizeReflectiveApply,
          rhoReflectivePresentation]

private theorem substituteReflective_rhoName_agrees
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name)
    (depth : Nat) (replacementName : Pattern) :
    substituteReflective rhoReflectivePresentation depth replacementName name =
      semanticSubstName depth replacementName name := by
  rw [substituteReflective_rhoName_eq_mark typed]
  unfold semanticSubstName
  rw [substituteNameMark_rhoName_agrees typed]

/-- Reflective substitution compiled from the authored declaration agrees
exactly with paper-facing semantic substitution on processes admitted by the
derived presentation syntax.  The restriction to the derived process judgment
is essential: the ambient `Pattern` type also contains ill-sorted terms on
which a quotation can occur directly in process position. -/
theorem substituteReflective_rhoProc_agrees
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process)
    (depth : Nat) (replacementName : Pattern) :
    substituteReflective rhoReflectivePresentation depth replacementName process =
      semanticSubstProc depth replacementName process := by
  suffices agreement : ∀ depth replacementName,
      substituteReflective rhoReflectivePresentation depth replacementName process =
        semanticSubstProc depth replacementName process by
    exact agreement depth replacementName
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation) (free := free) (t := typed)
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ process _ =>
      ∀ depth replacementName,
        substituteReflective rhoReflectivePresentation depth replacementName process =
          semanticSubstProc depth replacementName process)
    (motive_3 := fun _ processes _ =>
      ∀ depth replacementName,
        substituteReflectiveList rhoReflectivePresentation depth replacementName processes =
          semanticSubstProcList depth replacementName processes)
  case drop =>
    intro bound name nameTyped _ depth replacementName
    have markAgreement :=
      substituteNameMark_rhoName_agrees nameTyped depth replacementName
    simp only [rhoReflectivePresentation] at markAgreement ⊢
    unfold substituteReflective semanticSubstProc
    rw [markAgreement]
    cases markResult : semanticSubstNameMark depth replacementName name with
    | mk substitutedName matched =>
        cases matched <;> cases substitutedName <;> simp [markResult]
        case true.apply constructor arguments =>
          cases arguments with
          | nil => simp
          | cons argument rest =>
              cases rest with
              | nil =>
                  by_cases isQuote : constructor = "NQuote" <;>
                    simp [isQuote]
              | cons second tail => simp
  case output =>
    intro bound channel payload channelTyped _ _ payloadIH depth replacementName
    have channelAgreement :=
      substituteReflective_rhoName_agrees channelTyped depth replacementName
    have payloadAgreement := payloadIH depth replacementName
    simp only [rhoReflectivePresentation] at channelAgreement payloadAgreement ⊢
    simp only [substituteReflective, substituteReflectiveList, semanticSubstProc]
    rw [channelAgreement, payloadAgreement]
  case input =>
    intro bound channel body channelTyped _ _ bodyIH depth replacementName
    have channelAgreement :=
      substituteReflective_rhoName_agrees channelTyped depth replacementName
    have bodyAgreement := bodyIH (depth + 1) replacementName
    simp only [rhoReflectivePresentation] at channelAgreement bodyAgreement ⊢
    simp only [substituteReflective, substituteReflectiveList, semanticSubstProc]
    rw [channelAgreement, bodyAgreement]
  all_goals
    intros
    simp_all [substituteReflective, substituteReflectiveList,
      semanticSubstProc, semanticSubstProcList, rhoReflectivePresentation]

/-- On derived rho syntax, the complete right-hand side compiled from the
authored COMM declaration is exactly the established semantic COMM result. -/
theorem applyBindingsForRule_rhoComm_agrees_derived
    {free : FreeSortContext} {bound : List String} {body payload : Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free
      (rhoReflectivePresentation.nameSort :: bound) body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free bound payload)
    (channel : Pattern) (rest : List Pattern) :
    applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel body payload rest) =
      .collection .hashBag (semanticCommSubst body payload :: rest) none := by
  rw [applyBindingsForRule_rhoComm]
  rw [normalizeReflective_rhoProc_agrees payloadTyped]
  rw [substituteReflective_rhoProc_agrees bodyTyped]
  rfl

/-! ## Executable agreement witnesses -/

/-- A received quoted payload exposes a matched dropped name exactly as the
paper-facing semantic COMM substitution does. -/
theorem rhoComm_bound_drop_agrees (channel : Pattern) (rest : List Pattern) :
    applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel (.apply "PDrop" [.bvar 0])
          (.apply "PZero" []) rest) =
      .collection .hashBag
        (semanticCommSubst (.apply "PDrop" [.bvar 0]) (.apply "PZero" []) :: rest)
        none := by
  rfl

/-- The concrete bound-drop witness generalizes to every payload admitted by
the syntax derived from the authored rho presentation. -/
theorem rhoComm_bound_drop_agrees_derived
    {free : FreeSortContext} {bound : List String} {payload : Pattern}
    (payloadTyped :
      ProcWellSorted rhoReflectivePresentation free bound payload)
    (channel : Pattern) (rest : List Pattern) :
    applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel (.apply "PDrop" [.bvar 0]) payload rest) =
      .collection .hashBag
        (semanticCommSubst (.apply "PDrop" [.bvar 0]) payload :: rest)
        none := by
  rw [applyBindingsForRule_rhoComm]
  rw [semanticCommSubst_collapses_bound_drop]
  rw [← normalizeReflective_rhoProc_agrees payloadTyped]
  cases payloadTyped <;>
    simp [normalizeReflective, normalizeReflectiveList,
      finishNormalizeReflectiveApply, substituteReflective,
      substituteNameMark,
      rhoReflectivePresentation]

/-- Literal quoted code remains opaque to the received-name substitution. -/
theorem rhoComm_quoted_code_agrees (channel : Pattern) (rest : List Pattern) :
    let quotedBody :=
      .apply "NQuote" [.apply "POutput" [.bvar 0, .apply "PZero" []]]
    applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel quotedBody (.apply "PZero" []) rest) =
      .collection .hashBag
        (semanticCommSubst quotedBody (.apply "PZero" []) :: rest) none := by
  rfl

/-- Negative boundary: a free dropped quotation is inert in the cost/pure
profile; compiling COMM does not introduce a free-Drop reduction. -/
theorem rhoComm_free_drop_stays_inert (channel : Pattern) (rest : List Pattern) :
    let freeDrop := .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]
    applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommBindings channel freeDrop (.apply "PZero" []) rest) =
      .collection .hashBag
        (semanticCommSubst freeDrop (.apply "PZero" []) :: rest) none := by
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
