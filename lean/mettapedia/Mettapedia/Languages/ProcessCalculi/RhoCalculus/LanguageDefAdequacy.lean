import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
import Mettapedia.OSLF.MeTTaIL.ReflectiveEngine
import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoOpening
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
import Mettapedia.OSLF.MeTTaIL.QuoteDropReflective

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
open Mettapedia.OSLF.MeTTaIL.ReflectiveEngine
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent (quotesLiteral)
open Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission (withQuoteScope_quoteConstructor
  withQuoteScope_dropConstructor withQuoteScope_parallelUnitConstructor withQuoteScope_parallelCollection
  withQuoteScope_inputConstructor withQuoteScope_outputConstructor withQuoteScope_nameSort
  withQuoteScope_processSort)

/-- The authored COMM rule has exactly one selected matching presentation. -/
theorem rhoComm_matchingPresentation_selected :
    matchingPresentationForRule? rhoReflectionProfile rhoCommRewrite =
      some rhoReflectivePresentation.toReflectivePresentationDecl := by
  decide +kernel

/-- The authored COMM rule has exactly one selected substitution
presentation. -/
theorem rhoComm_substitutionPresentation_selected :
    substitutionPresentationForRule? rhoReflectionProfile rhoCommRewrite =
      some rhoReflectivePresentation.toReflectivePresentationDecl := by
  decide +kernel

/-- The generic rule-aware matcher is definitionally specialized by the
authored rho declaration, not by an engine callback. -/
theorem matchPatternForRule_rhoComm (term : Pattern) :
    matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite term =
      matchPatternWith rhoCanonicalEquivalent rhoCommRewrite.left term := by
  simp only [matchPatternForRuleUsing, rhoComm_matchingPresentation_selected]
  rfl

/-- The compiled matcher for authored rho COMM has the independent
equivalence-parameterized relational specification on every candidate. -/
theorem matchPatternForRule_rhoComm_iff
    {term : Pattern} {bindings : Bindings} :
    bindings ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite term ↔
      MatchRelWith rhoCanonicalEquivalent rhoCommRewrite.left term bindings := by
  rw [matchPatternForRuleUsing_iff_matchRelWith_of_presentation
    rhoComm_matchingPresentation_selected]
  rfl

/-- Consequently, the executable premise-aware rule application uses the
proved pure-rho repeated-channel comparator for every candidate term. -/
theorem applyRuleWithPremisesUsing_rhoComm
    (relationEnvironment : RelationEnv) (term : Pattern) :
    applyRuleWithPremisesUsingReflection rhoReflectionProfile
        relationEnvironment rhoCalc rhoCommRewrite term =
      (matchPatternWith rhoCanonicalEquivalent rhoCommRewrite.left term).flatMap
        (fun bindings =>
          (applyPremisesWithEnv relationEnvironment rhoCalc rhoCommRewrite.premises bindings).map
            (fun finalBindings =>
              applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite finalBindings)) := by
  unfold applyRuleWithPremisesUsingReflection
  rw [matchPatternForRule_rhoComm]

/-- The strict-core authored language passes its structural validation gate. -/
theorem rhoCalc_validate : rhoCalc.validate = [] := by
  exact rhoCalc_validate_eq_nil

/-- The extracted authored COMM rule is a rewrite of the strict-core language. -/
theorem rhoCommRewrite_mem : rhoCommRewrite ∈ rhoCalc.rewrites := by
  simp [rhoCalc]

/-- A missing rule reference is rejected rather than silently compiled. -/
theorem malformed_reflective_rule_rejected :
    Mettapedia.OSLF.MeTTaIL.Reflection.validate rhoCalc
      { rhoReflectionProfile with
        rules := [{ rhoReflectiveRule with rewriteRule := "MissingComm" }] } ≠ [] := by
  exact rho_missing_rewrite_rejected

/-! ## Authored COMM right-hand side -/

/-- Matcher bindings for a concrete COMM occurrence. -/
def rhoCommBindings (channel body payload : Pattern) (rest : List Pattern) : Bindings :=
  [("n", channel), ("p", body), ("q", payload),
    ("rest", .collection .hashBag rest none)]

/-- Compiling the authored COMM right-hand side selects reflective
substitution and preserves the unmatched parallel components. -/
theorem applyBindingsForRule_rhoComm
    (channel body payload : Pattern) (rest : List Pattern) :
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (rhoCommBindings channel body payload rest) =
      .collection .hashBag
        (substituteReflective rhoReflectivePresentation 0
            (.apply "NQuote"
              [normalizeReflective rhoReflectivePresentation payload]) body ::
          rest)
        none := by
  rw [applyBindingsForRuleUsing, rhoComm_substitutionPresentation_selected]
  simp [rhoCommRewrite, rhoCommBindings, applyBindingsReflective,
    applyBindingsReflectiveList, normalizeReflectiveReplacement,
    rhoReflectivePresentation]

section ScopeGeneral

/-! The agreement theorems below hold for rho's constructors under every quote
scope: the operations are rho's own, and only the admission premise of a
quotation depends on the scope. -/

variable {scope : QuoteScope}

/-! ## Derived-syntax agreement -/

private theorem rhoDrop_normalization_congr
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name)
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
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process)
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
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name) :
    normalizeReflective rhoReflectivePresentation name =
      semanticNormalizeName name := by
  apply NameWellSorted.rec
    (presentation := rhoReflectivePresentation.withQuoteScope scope) (free := free) (t := typed)
    (motive_1 := fun _ name _ =>
      normalizeReflective rhoReflectivePresentation name =
        semanticNormalizeName name)
    (motive_2 := fun _ process _ =>
      normalizeReflective rhoReflectivePresentation process =
        semanticNormalizeProc process)
    (motive_3 := fun _ processes _ =>
      normalizeReflectiveList rhoReflectivePresentation processes =
        semanticNormalizeProcList processes)
  all_goals try simp only [withQuoteScope_quoteConstructor, withQuoteScope_dropConstructor,
    withQuoteScope_parallelUnitConstructor, withQuoteScope_parallelCollection,
    withQuoteScope_inputConstructor, withQuoteScope_outputConstructor, withQuoteScope_nameSort,
    withQuoteScope_processSort] at *
  case quote =>
    intro bound process processTyped _ processIH
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
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) :
    normalizeReflective rhoReflectivePresentation process =
      semanticNormalizeProc process := by
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation.withQuoteScope scope) (free := free) (t := typed)
    (motive_1 := fun _ name _ =>
      normalizeReflective rhoReflectivePresentation name =
        semanticNormalizeName name)
    (motive_2 := fun _ process _ =>
      normalizeReflective rhoReflectivePresentation process =
        semanticNormalizeProc process)
    (motive_3 := fun _ processes _ =>
      normalizeReflectiveList rhoReflectivePresentation processes =
        semanticNormalizeProcList processes)
  all_goals try simp only [withQuoteScope_quoteConstructor, withQuoteScope_dropConstructor,
    withQuoteScope_parallelUnitConstructor, withQuoteScope_parallelCollection,
    withQuoteScope_inputConstructor, withQuoteScope_outputConstructor, withQuoteScope_nameSort,
    withQuoteScope_processSort] at *
  case quote =>
    intro bound process processTyped _ processIH
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
    (typed : ProcListWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound processes) :
    normalizeReflectiveList rhoReflectivePresentation processes =
      semanticNormalizeProcList processes := by
  apply ProcListWellSorted.rec
    (presentation := rhoReflectivePresentation.withQuoteScope scope) (free := free) (t := typed)
    (motive_1 := fun _ name _ =>
      normalizeReflective rhoReflectivePresentation name =
        semanticNormalizeName name)
    (motive_2 := fun _ process _ =>
      normalizeReflective rhoReflectivePresentation process =
        semanticNormalizeProc process)
    (motive_3 := fun _ processes _ =>
      normalizeReflectiveList rhoReflectivePresentation processes =
        semanticNormalizeProcList processes)
  all_goals try simp only [withQuoteScope_quoteConstructor, withQuoteScope_dropConstructor,
    withQuoteScope_parallelUnitConstructor, withQuoteScope_parallelCollection,
    withQuoteScope_inputConstructor, withQuoteScope_outputConstructor, withQuoteScope_nameSort,
    withQuoteScope_processSort] at *
  case quote =>
    intro bound process processTyped _ processIH
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

/-! ## Derived substitution agreement on the literal-quotation fiber

Reflective substitution resolves every quotation of a drop, also one hidden
behind the parallel unit such as `@(*x | 0)`, before substituting. The
paper-facing semantic substitution keeps such a name as written. The two
therefore agree exactly on the fiber where every quotation exposes a drop only
literally (`ReflectiveCoherent.quotesLiteral`); outside it they differ in
spelling (see `hiddenQuoteDrop_comm_differs`). -/

open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent in
private theorem rho_distinct :
    rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor ≠
      rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor := by
  decide

private theorem rhoName_isName
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name) :
    Mettapedia.OSLF.MeTTaIL.QuoteDrop.isName rhoReflectivePresentation name = true := by
  cases typed <;> simp [Mettapedia.OSLF.MeTTaIL.QuoteDrop.isName, rhoReflectivePresentation]

open Mettapedia.OSLF.MeTTaIL.QuoteDrop in
/-- Every drop of a derived rho process receives a name. -/
theorem rhoProc_dropsNamed
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) :
    dropsNamed rhoReflectivePresentation process = true := by
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation.withQuoteScope scope) (free := free) (t := typed)
    (motive_1 := fun _ name _ => dropsNamed rhoReflectivePresentation name = true)
    (motive_2 := fun _ process _ => dropsNamed rhoReflectivePresentation process = true)
    (motive_3 := fun _ processes _ =>
      ∀ process ∈ processes, dropsNamed rhoReflectivePresentation process = true)
  all_goals try simp only [withQuoteScope_quoteConstructor, withQuoteScope_dropConstructor,
    withQuoteScope_parallelUnitConstructor, withQuoteScope_parallelCollection,
    withQuoteScope_inputConstructor, withQuoteScope_outputConstructor, withQuoteScope_nameSort,
    withQuoteScope_processSort] at *
  case quote =>
    intro bound process _ admitted processIH
    apply dropsNamed_of_apply
    · intro argument member; rw [List.mem_singleton] at member; subst member; exact processIH
    · intro same; simp [rhoReflectivePresentation] at same
  case unit => intros; exact dropsNamed_of_apply (by simp) (by simp)
  case drop =>
    intro bound name nameTyped nameIH
    apply dropsNamed_of_apply
    · intro argument member; rw [List.mem_singleton] at member; subst member; exact nameIH
    · intro _ argument single
      simp only [List.cons.injEq, and_true] at single
      subst single
      exact rhoName_isName nameTyped
  case output =>
    intro bound channel payload _ _ channelIH payloadIH
    apply dropsNamed_of_apply
    · intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact channelIH
      · exact payloadIH
    · intro same; simp [rhoReflectivePresentation] at same
  case input =>
    intro bound channel body _ _ channelIH bodyIH
    apply dropsNamed_of_apply
    · intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact channelIH
      · rw [dropsNamed]; exact bodyIH
    · intro same; simp [rhoReflectivePresentation] at same
  case parallel =>
    intro bound processes _ processesIH
    rw [dropsNamed]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall]
    exact processesIH
  case nil => intro _ process membership; simp at membership
  case cons =>
    intro bound process processes _ _ processIH processesIH member membership
    rcases List.mem_cons.mp membership with rfl | membership
    · exact processIH
    · exact processesIH member membership
  all_goals intros; rw [dropsNamed]

theorem rhoName_dropsNamed
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name) :
    Mettapedia.OSLF.MeTTaIL.QuoteDrop.dropsNamed rhoReflectivePresentation name = true := by
  cases typed with
  | bvar _ => rw [Mettapedia.OSLF.MeTTaIL.QuoteDrop.dropsNamed]
  | fvar _ => rw [Mettapedia.OSLF.MeTTaIL.QuoteDrop.dropsNamed]
  | quote processTyped =>
      apply Mettapedia.OSLF.MeTTaIL.QuoteDrop.dropsNamed_of_apply
      · intro argument member
        rw [List.mem_singleton] at member; subst member
        exact rhoProc_dropsNamed processTyped
      · intro same; simp [rhoReflectivePresentation] at same

/-- The index action of binder-preserving substitution. -/
private abbrev preserving (replacementName : Pattern) : Nat → Nat → Pattern :=
  fun level index => if index = level then replacementName else .bvar index

open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent Mettapedia.OSLF.MeTTaIL.QuoteDrop in
/-- On the fiber, a derived name substitutes exactly as the paper-facing name
substitution, and is recognized as the bound name exactly when the
paper-facing comparison recognizes it. -/
private theorem rhoName_fiber_agrees
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name)
    (fiber : quotesLiteral rhoReflectivePresentation name = true)
    (depth : Nat) (replacementName : Pattern) :
    matchesBinder rhoReflectivePresentation depth (normalizeReflective rhoReflectivePresentation name) =
        decide (Canonical.canonicalize name = .bvar depth) ∧
      substituteResolved rhoReflectivePresentation (preserving replacementName) depth
          (normalizeReflective rhoReflectivePresentation name) =
        semanticSubstName depth replacementName name := by
  have named := rhoName_dropsNamed typed
  have resolvedEq := resolveQuotes_eq_normal rho_distinct named fiber
  have resolved : QuotesResolved rhoReflectivePresentation
      (normalizeReflective rhoReflectivePresentation name) := by
    rw [← resolvedEq]; exact resolveQuotes_resolved name
  have canonical : canonicalize rhoReflectivePresentation
      (normalizeReflective rhoReflectivePresentation name) = Canonical.canonicalize name := by
    rw [canonicalize_normalizeReflective rho_distinct, derivedCanonicalize_eq]
  have decision : matchesBinder rhoReflectivePresentation depth
      (normalizeReflective rhoReflectivePresentation name) =
      decide (Canonical.canonicalize name = .bvar depth) := by
    simp only [matchesBinder,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.BinderHead.ofPattern_index_iff, canonical]
  refine ⟨decision, ?_⟩
  have shaped : isName rhoReflectivePresentation (normalizeReflective rhoReflectivePresentation name) = true :=
    (normal_shape rho_distinct name named).1 (rhoName_isName typed)
  show _ = (semanticSubstNameMark depth replacementName name).1
  unfold semanticSubstNameMark
  rw [← normalizeReflective_rhoName_agrees typed, ← canonical]
  generalize normalizeReflective rhoReflectivePresentation name = normal at shaped resolved
  cases normal with
  | bvar index =>
      by_cases hit : index = depth
      · subst hit; simp [substituteResolved, preserving, canonicalize]
      · simp [substituteResolved, preserving, canonicalize, hit]
  | fvar label => simp [substituteResolved, canonicalize]
  | apply label arguments =>
      match arguments, shaped, resolved with
      | [payload], shaped, resolved =>
          have quoted : label = rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor := by
            simpa [isName] using shaped
          subst quoted
          rw [canonicalize_unary_of_resolved resolved]
          simp [substituteResolved]
      | [], shaped, _ => simp [isName] at shaped
      | _ :: _ :: _, shaped, _ => simp [isName] at shaped
  | lambda _ _ => simp [isName] at shaped
  | multiLambda _ _ _ => simp [isName] at shaped
  | subst _ _ => simp [isName] at shaped
  | collection _ _ _ => simp [isName] at shaped

private theorem rho_receive (replacementName : Pattern) :
    receive rhoReflectivePresentation.toReflectivePresentationDecl
        rhoReflectivePresentation.dropConstructor replacementName =
      (match replacementName, true with
        | .apply "NQuote" [p], true => p
        | _, _ => .apply "PDrop" [replacementName]) := by
  cases replacementName with
  | apply quote arguments =>
    match arguments with
    | [process] =>
      by_cases quoted : quote = "NQuote"
      · subst quoted; rfl
      · have notQuote : ¬ quote = rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor :=
          quoted
        have lhs : receive rhoReflectivePresentation.toReflectivePresentationDecl
            rhoReflectivePresentation.dropConstructor (.apply quote [process]) =
            .apply "PDrop" [.apply quote [process]] := by
          simp only [receive, notQuote, if_false]; rfl
        rw [lhs]
        split
        · rename_i same _
          injection same with labelEq
          exact absurd labelEq quoted
        · rfl
    | [] => simp [receive]; rfl
    | _ :: _ :: _ => simp [receive]; rfl
  | _ => rfl

open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent in
private theorem rhoProc_fiber_agrees
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) :
    ∀ depth replacementName, quotesLiteral rhoReflectivePresentation process = true →
      substituteResolved rhoReflectivePresentation (preserving replacementName) depth
          (normalizeReflective rhoReflectivePresentation process) =
        semanticSubstProc depth replacementName process := by
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation.withQuoteScope scope) (free := free) (t := typed)
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ process _ =>
      ∀ depth replacementName, quotesLiteral rhoReflectivePresentation process = true →
        substituteResolved rhoReflectivePresentation (preserving replacementName) depth
            (normalizeReflective rhoReflectivePresentation process) =
          semanticSubstProc depth replacementName process)
    (motive_3 := fun _ processes _ =>
      ∀ depth replacementName, quotesLiteralList rhoReflectivePresentation processes = true →
        (normalizeReflectiveList rhoReflectivePresentation processes).map
            (substituteResolved rhoReflectivePresentation (preserving replacementName) depth) =
          semanticSubstProcList depth replacementName processes)
  all_goals try simp only [withQuoteScope_dropConstructor, withQuoteScope_parallelUnitConstructor,
    withQuoteScope_parallelCollection, withQuoteScope_inputConstructor,
    withQuoteScope_outputConstructor, withQuoteScope_nameSort, withQuoteScope_processSort] at *
  case drop =>
    intro bound name nameTyped _ depth replacementName fiber
    have nameFiber := quotesLiteral_args fiber name (by simp)
    obtain ⟨decision, agrees⟩ := rhoName_fiber_agrees nameTyped nameFiber depth replacementName
    rw [normalizeReflective_unary_of_ne_quote rho_distinct, substituteResolved_drop rho_distinct,
      decision]
    show _ = semanticSubstProc depth replacementName (.apply "PDrop" [name])
    by_cases hit : Canonical.canonicalize name = .bvar depth
    · simp only [hit, decide_true, if_true, preserving]
      rw [rho_receive]
      simp only [semanticSubstProc, semanticSubstNameMark, hit, if_true]
      rfl
    · simp only [hit, decide_false, Bool.false_eq_true, if_false]
      rw [agrees]
      simp [semanticSubstProc, semanticSubstNameMark, semanticSubstName, hit,
        rhoReflectivePresentation]
  case output =>
    intro bound channel payload channelTyped _ _ payloadIH depth replacementName fiber
    have channelFiber := quotesLiteral_args fiber channel (by simp)
    have payloadFiber := quotesLiteral_args fiber payload (by simp)
    have channelAgrees := (rhoName_fiber_agrees channelTyped channelFiber depth replacementName).2
    have payloadAgrees := payloadIH depth replacementName payloadFiber
    rw [normalizeReflective_apply_long, List.map_cons, List.map_cons, List.map_nil,
      substituteResolved_apply_long, List.map_cons, List.map_cons, List.map_nil,
      channelAgrees, payloadAgrees]
    show _ = semanticSubstProc depth replacementName (.apply "POutput" [channel, payload])
    simp only [semanticSubstProc, rhoReflectivePresentation]
  case input =>
    intro bound channel body channelTyped _ _ bodyIH depth replacementName fiber
    have channelFiber := quotesLiteral_args fiber channel (by simp)
    have bodyFiber : quotesLiteral rhoReflectivePresentation body = true := by
      simpa [quotesLiteral] using quotesLiteral_args fiber (.lambda none body) (by simp)
    have channelAgrees := (rhoName_fiber_agrees channelTyped channelFiber depth replacementName).2
    have bodyAgrees := bodyIH (depth + 1) replacementName bodyFiber
    rw [normalizeReflective_apply_long, List.map_cons, List.map_cons, List.map_nil,
      substituteResolved_apply_long, List.map_cons, List.map_cons, List.map_nil, channelAgrees]
    simp only [normalizeReflective, substituteResolved, bodyAgrees]
    show _ = semanticSubstProc depth replacementName (.apply "PInput" [channel, .lambda none body])
    simp only [semanticSubstProc, rhoReflectivePresentation]
  case parallel =>
    intro bound processes _ processesIH depth replacementName fiber
    have listAgrees := processesIH depth replacementName fiber
    simp only [normalizeReflective, substituteResolved, substituteResolvedList_eq_map]
    rw [listAgrees]
    simp only [semanticSubstProc]
  case unit =>
    intro bound depth replacementName _
    show substituteResolved _ _ depth (normalizeReflective _ (.apply "PZero" [])) =
      semanticSubstProc depth replacementName (.apply "PZero" [])
    simp [normalizeReflective, normalizeReflectiveList, finish_nil, substituteResolved,
      semanticSubstProc]
  case nil =>
    intro bound depth replacementName _
    simp [normalizeReflectiveList, semanticSubstProcList]
  case cons =>
    intro bound process processes _ _ processIH processesIH depth replacementName fiber
    simp only [quotesLiteralList, Bool.and_eq_true] at fiber
    simp only [normalizeReflectiveList, List.map_cons, semanticSubstProcList]
    rw [processIH depth replacementName fiber.1, processesIH depth replacementName fiber.2]
  all_goals intros; first
    | trivial
    | simp [normalizeReflective, substituteResolved, preserving, semanticSubstProc]

/-- Reflective substitution compiled from the authored declaration agrees
exactly with paper-facing semantic substitution on processes admitted by the
derived presentation syntax whose quotations expose a drop only literally.
Exact agreement is stated on that fiber because reflective substitution
resolves a quotation of a drop hidden behind the parallel unit, while the
paper-facing operation keeps it as written; `hiddenQuoteDrop_comm_differs`
is the negative example. -/
theorem substituteReflective_rhoProc_agrees
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process)
    (fiber : quotesLiteral rhoReflectivePresentation process = true)
    (depth : Nat) (replacementName : Pattern) :
    substituteReflective rhoReflectivePresentation depth replacementName process =
      semanticSubstProc depth replacementName process := by
  unfold substituteReflective
  rw [Mettapedia.OSLF.MeTTaIL.QuoteDrop.resolveQuotes_eq_normal rho_distinct
    (rhoProc_dropsNamed typed) fiber]
  exact rhoProc_fiber_agrees typed depth replacementName fiber

/-- On derived rho syntax whose body lies in the literal-quotation fiber, the
complete right-hand side compiled from the authored COMM declaration is
exactly the established semantic COMM result. The fiber hypothesis is needed
for exact agreement: see `hiddenQuoteDrop_comm_differs`. -/
theorem applyBindingsForRule_rhoComm_agrees_derived
    {free : FreeSortContext} {bound : List String} {body payload : Pattern}
    (bodyTyped : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free
      (rhoReflectivePresentation.nameSort :: bound) body)
    (fiber : quotesLiteral rhoReflectivePresentation body = true)
    (payloadTyped : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound payload)
    (channel : Pattern) (rest : List Pattern) :
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (rhoCommBindings channel body payload rest) =
      .collection .hashBag (semanticCommSubst body payload :: rest) none := by
  rw [applyBindingsForRule_rhoComm]
  rw [normalizeReflective_rhoProc_agrees payloadTyped]
  rw [substituteReflective_rhoProc_agrees bodyTyped fiber]
  rfl

open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent Mettapedia.OSLF.MeTTaIL.QuoteDrop in
private theorem rhoName_canonical_agrees
    {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name)
    (depth : Nat) (replacementName : Pattern) :
    canonicalize rhoReflectivePresentation (semanticSubstName depth replacementName name) =
      canonicalize rhoReflectivePresentation (substituteResolved rhoReflectivePresentation
        (preserving replacementName) depth (canonicalize rhoReflectivePresentation name)) := by
  have named := rhoName_dropsNamed typed
  have canonicalName := isName_canonicalize named (rhoName_isName typed)
  have canonical : canonicalize rhoReflectivePresentation name = Canonical.canonicalize name :=
    derivedCanonicalize_eq name
  unfold semanticSubstName semanticSubstNameMark
  rw [← canonical]
  by_cases hit : canonicalize rhoReflectivePresentation name = .bvar depth
  · rw [hit]; simp [substituteResolved, preserving]
  · simp only [hit, if_false]
    rw [← normalizeReflective_rhoName_agrees typed, canonicalize_normalizeReflective rho_distinct]
    have fixed : substituteResolved rhoReflectivePresentation (preserving replacementName) depth
        (canonicalize rhoReflectivePresentation name) = canonicalize rhoReflectivePresentation name := by
      generalize canonicalize rhoReflectivePresentation name = normal at canonicalName hit
      cases normal with
      | bvar index =>
          have different : index ≠ depth := fun same => hit (by rw [same])
          simp [substituteResolved, preserving, different]
      | fvar label => rfl
      | apply label arguments =>
          match arguments, canonicalName with
          | [payload], canonicalName =>
              have quoted : label = rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor := by
                simpa [isName] using canonicalName
              subst quoted
              simp [substituteResolved]
          | [], canonicalName => simp [isName] at canonicalName
          | _ :: _ :: _, canonicalName => simp [isName] at canonicalName
      | lambda _ _ => simp [isName] at canonicalName
      | multiLambda _ _ _ => simp [isName] at canonicalName
      | subst _ _ => simp [isName] at canonicalName
      | collection _ _ _ => simp [isName] at canonicalName
    rw [fixed, canonicalize_idempotent]

private theorem canonicalize_drop (name : Pattern) :
    canonicalize rhoReflectivePresentation (.apply "PDrop" [name]) =
      .apply "PDrop" [canonicalize rhoReflectivePresentation name] := by
  simp only [canonicalize, canonicalizeList]
  exact Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.finish_not_quote (by decide) _

open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent in
/-- The paper-facing substitution and reflective substitution agree up to the
declared name equations on every derived process: both canonical forms are
computed from the canonical form of the body. -/
theorem canonicalize_semanticSubstProc
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) :
    ∀ depth replacementName,
      canonicalize rhoReflectivePresentation (semanticSubstProc depth replacementName process) =
        canonicalize rhoReflectivePresentation (substituteResolved rhoReflectivePresentation
          (preserving replacementName) depth (canonicalize rhoReflectivePresentation process)) := by
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation.withQuoteScope scope) (free := free) (t := typed)
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ process _ => ∀ depth replacementName,
      canonicalize rhoReflectivePresentation (semanticSubstProc depth replacementName process) =
        canonicalize rhoReflectivePresentation (substituteResolved rhoReflectivePresentation
          (preserving replacementName) depth (canonicalize rhoReflectivePresentation process)))
    (motive_3 := fun _ processes _ => ∀ depth replacementName,
      (semanticSubstProcList depth replacementName processes).map
          (canonicalize rhoReflectivePresentation) =
        processes.map (fun process => canonicalize rhoReflectivePresentation
          (substituteResolved rhoReflectivePresentation (preserving replacementName) depth
            (canonicalize rhoReflectivePresentation process))))
  all_goals try simp only [withQuoteScope_dropConstructor, withQuoteScope_parallelUnitConstructor,
    withQuoteScope_parallelCollection, withQuoteScope_inputConstructor,
    withQuoteScope_outputConstructor, withQuoteScope_nameSort, withQuoteScope_processSort] at *
  case drop =>
    intro bound name nameTyped _ depth replacementName
    show canonicalize _ (semanticSubstProc depth replacementName (.apply "PDrop" [name])) =
      canonicalize _ (substituteResolved _ (preserving replacementName) depth
        (canonicalize _ (.apply rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor [name])))
    have dropCanonical : ∀ inner : Pattern, canonicalize rhoReflectivePresentation
        (.apply rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor [inner]) =
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor
          [canonicalize rhoReflectivePresentation inner] := by
      intro inner
      simp only [canonicalize, canonicalizeList]
      exact finish_not_quote rho_distinct _
    have decision : matchesBinder rhoReflectivePresentation depth (canonicalize rhoReflectivePresentation name) =
        decide (Canonical.canonicalize name = .bvar depth) := by
      have canonical := derivedCanonicalize_eq name
      rw [matchesBinder_canonicalize]
      simp only [matchesBinder, Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.BinderHead.ofPattern_index_iff,
        canonical]
    have nameAgrees := rhoName_canonical_agrees nameTyped depth replacementName
    rw [dropCanonical, substituteResolved_drop rho_distinct, decision]
    by_cases hit : Canonical.canonicalize name = .bvar depth
    · simp only [hit, decide_true, if_true, preserving]
      rw [rho_receive]
      simp only [semanticSubstProc, semanticSubstNameMark, hit, if_true]
      rfl
    · simp only [hit, decide_false, Bool.false_eq_true, if_false]
      unfold semanticSubstName semanticSubstNameMark at nameAgrees
      simp only [hit, if_false] at nameAgrees
      rw [dropCanonical, ← nameAgrees]
      simp only [semanticSubstProc, semanticSubstNameMark, hit, if_false]
      split
      · simp_all
      · exact dropCanonical _
  case output =>
    intro bound channel payload channelTyped _ _ payloadIH depth replacementName
    have channelAgrees := rhoName_canonical_agrees channelTyped depth replacementName
    show canonicalize _ (semanticSubstProc depth replacementName (.apply "POutput" [channel, payload])) =
      canonicalize _ (substituteResolved _ _ depth (canonicalize _ (.apply "POutput" [channel, payload])))
    simp only [semanticSubstProc, canonicalize, canonicalizeList, finish_long,
      substituteResolved, substituteResolvedList]
    rw [channelAgrees, payloadIH depth replacementName]
  case input =>
    intro bound channel body channelTyped _ _ bodyIH depth replacementName
    have channelAgrees := rhoName_canonical_agrees channelTyped depth replacementName
    show canonicalize _ (semanticSubstProc depth replacementName
        (.apply "PInput" [channel, .lambda none body])) =
      canonicalize _ (substituteResolved _ _ depth
        (canonicalize _ (.apply "PInput" [channel, .lambda none body])))
    simp only [semanticSubstProc, canonicalize, canonicalizeList, finish_long,
      substituteResolved, substituteResolvedList]
    rw [channelAgrees, bodyIH (depth + 1) replacementName]
  case parallel =>
    intro bound processes _ processesIH depth replacementName
    show canonicalize _ (semanticSubstProc depth replacementName (.collection .hashBag processes none)) =
      canonicalize _ (substituteResolved _ _ depth
        (canonicalize _ (.collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          processes none)))
    rw [canonicalize_substituteResolved_canonical_parallel]
    simp only [semanticSubstProc]
    rw [show (Pattern.collection CollType.hashBag (semanticSubstProcList depth replacementName processes) none) =
        .collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          (semanticSubstProcList depth replacementName processes) none from rfl,
      canonicalize_parallel_eq, processesIH depth replacementName]
  case unit =>
    intro bound depth replacementName
    show canonicalize _ (semanticSubstProc depth replacementName (.apply "PZero" [])) = _
    simp [semanticSubstProc, canonicalize, canonicalizeList, finish_nil, substituteResolved,
      rhoReflectivePresentation]
  case nil =>
    intro bound depth replacementName
    simp [semanticSubstProcList]
  case cons =>
    intro bound process processes _ _ processIH processesIH depth replacementName
    simp only [semanticSubstProcList, List.map_cons]
    rw [processIH depth replacementName, processesIH depth replacementName]
  all_goals intros; first
    | trivial
    | simp [semanticSubstProc, substituteResolved, preserving, canonicalize]

/-- Reflective substitution and the paper-facing substitution are equal up
to the declared name equations on every derived process. -/
theorem substituteReflective_rhoProc_equivalent
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process)
    (depth : Nat) (replacementName : Pattern) :
    rhoCanonicalEquivalent (substituteReflective rhoReflectivePresentation depth replacementName process)
      (semanticSubstProc depth replacementName process) = true := by
  have reflective := Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.canonicalize_substituteResolved_resolveQuotes
    (declaration := rhoReflectivePresentation) (preserving replacementName) depth process
  unfold rhoCanonicalEquivalent
  rw [canonicalEquivalent_eq_true_iff]
  show canonicalize _ (substituteResolved _ (preserving replacementName) depth
    (resolveQuotes _ process)) = _
  rw [reflective, canonicalize_semanticSubstProc typed depth replacementName]

/-! ## Resolution stays inside derived rho syntax -/

private theorem rho_member_typed
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) :
    ∀ member ∈ parallelLeaves rhoReflectivePresentation process,
      ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound member := by
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation.withQuoteScope scope) (free := free) (t := typed)
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun bound process _ => ∀ member ∈ parallelLeaves rhoReflectivePresentation process,
      ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound member)
    (motive_3 := fun bound processes _ => ∀ process ∈ processes,
      ∀ member ∈ parallelLeaves rhoReflectivePresentation process,
        ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound member)
  all_goals try simp only [withQuoteScope_dropConstructor, withQuoteScope_parallelUnitConstructor,
    withQuoteScope_parallelCollection, withQuoteScope_inputConstructor,
    withQuoteScope_outputConstructor, withQuoteScope_nameSort, withQuoteScope_processSort] at *
  case unit =>
    intro bound member membership
    simp [parallelLeaves] at membership
  case drop =>
    intro bound name nameTyped _ member membership
    simp only [parallelLeaves, List.mem_singleton] at membership
    subst membership; exact .drop nameTyped
  case output =>
    intro bound channel payload channelTyped payloadTyped _ _ member membership
    simp only [parallelLeaves, List.mem_singleton] at membership
    subst membership; exact .output channelTyped payloadTyped
  case input =>
    intro bound channel body channelTyped bodyTyped _ _ member membership
    simp only [parallelLeaves, List.mem_singleton] at membership
    subst membership; exact .input channelTyped bodyTyped
  case parallel =>
    intro bound processes _ processesIH member membership
    simp only [parallelLeaves, if_true, parallelLeavesList_eq_flatMap, List.mem_flatMap] at membership
    obtain ⟨element, elementMember, membership⟩ := membership
    exact processesIH element elementMember member membership
  case nil => intro bound process membership; simp at membership
  case cons =>
    intro bound process processes _ _ processIH processesIH element membership
    rcases List.mem_cons.mp membership with rfl | membership
    · exact processIH
    · exact processesIH element membership
  all_goals first
    | (intros; trivial)
    | (intro bound index lookup member membership
       simp only [parallelLeaves, List.mem_singleton] at membership
       subst membership; first | exact .bvar lookup | exact .fvar lookup)

/-- Resolving quotations of drops keeps derived rho syntax. -/
theorem rhoProc_resolveQuotes_typed
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) :
    ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound (resolveQuotes rhoReflectivePresentation process) := by
  apply ProcWellSorted.rec
    (presentation := rhoReflectivePresentation.withQuoteScope scope) (free := free) (t := typed)
    (motive_1 := fun bound name _ =>
      NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound (resolveQuotes rhoReflectivePresentation name))
    (motive_2 := fun bound process _ =>
      ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound (resolveQuotes rhoReflectivePresentation process))
    (motive_3 := fun bound processes _ =>
      ProcListWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound
        (resolveQuotesList rhoReflectivePresentation processes))
  all_goals try simp only [withQuoteScope_quoteConstructor, withQuoteScope_dropConstructor,
    withQuoteScope_parallelUnitConstructor, withQuoteScope_parallelCollection,
    withQuoteScope_inputConstructor, withQuoteScope_outputConstructor, withQuoteScope_nameSort,
    withQuoteScope_processSort] at *
  case quote =>
    intro bound process _ admitted processIH
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply, if_true]
    split
    · rename_i name exposed
      have member := rho_member_typed processIH
        (.apply rhoReflectivePresentation.dropConstructor [name])
        (by rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.exposedDrop?_eq_some_iff.mp exposed];
            exact List.mem_singleton_self _)
      generalize patternEq : Pattern.apply rhoReflectivePresentation.dropConstructor [name] = pattern
        at member
      cases member <;> simp [rhoReflectivePresentation] at patternEq
      rename_i nameTyped
      subst patternEq
      exact nameTyped
    · refine .quote processIH ?_
      cases scope with
      | closed =>
          change quoteAdmits rhoReflectivePresentation.toReflectivePresentationDecl process = true at admitted
          change quoteAdmits rhoReflectivePresentation.toReflectivePresentationDecl
            (resolveQuotes rhoReflectivePresentation process) = true
          rw [Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission.quoteAdmits_of_canonicalize_eq
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.canonicalize_resolveQuotes process)]
          exact admitted
      | reaching view => exact quoteAdmits_of_reaching rfl _
  case drop =>
    intro bound name _ nameIH
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply,
      show ¬ (rhoReflectivePresentation.dropConstructor =
        rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor) by decide, if_false]
    exact .drop nameIH
  case output =>
    intro bound channel payload _ _ channelIH payloadIH
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply]
    exact .output channelIH payloadIH
  case input =>
    intro bound channel body _ _ channelIH bodyIH
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply]
    exact .input channelIH bodyIH
  case parallel =>
    intro bound processes _ processesIH
    simp only [resolveQuotes]
    exact .parallel processesIH
  case unit =>
    intro bound
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply]
    exact .unit
  case nil => intro bound; exact .nil
  case cons =>
    intro bound process processes _ _ processIH processesIH
    simp only [resolveQuotesList]
    exact .cons processIH processesIH
  all_goals intro bound index lookup; first | exact .bvar lookup | exact .fvar lookup

/-- **Reflective substitution is the paper-facing substitution after
resolution**: on every derived process, reflective substitution equals the
paper-facing substitution applied to the resolved process, which lies in the
literal-quotation fiber. -/
theorem substituteReflective_rhoProc_eq_resolved
    {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process)
    (depth : Nat) (replacementName : Pattern) :
    substituteReflective rhoReflectivePresentation depth replacementName process =
      semanticSubstProc depth replacementName (resolveQuotes rhoReflectivePresentation process) := by
  have resolved := Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.resolveQuotes_resolved
    (declaration := rhoReflectivePresentation) process
  rw [← substituteReflective_rhoProc_agrees (rhoProc_resolveQuotes_typed typed)
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.quotesLiteral_of_resolved resolved)]
  unfold substituteReflective
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.resolveQuotes_of_resolved resolved]

/-- The compiled COMM right-hand side is the paper-facing COMM result of the
resolved body, on all derived rho syntax. -/
theorem applyBindingsForRule_rhoComm_eq_resolved
    {free : FreeSortContext} {bound : List String} {body payload : Pattern}
    (bodyTyped : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free
      (rhoReflectivePresentation.nameSort :: bound) body)
    (payloadTyped : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound payload)
    (channel : Pattern) (rest : List Pattern) :
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (rhoCommBindings channel body payload rest) =
      .collection .hashBag
        (semanticCommSubst (resolveQuotes rhoReflectivePresentation body) payload :: rest) none := by
  rw [applyBindingsForRule_rhoComm, normalizeReflective_rhoProc_agrees payloadTyped,
    substituteReflective_rhoProc_eq_resolved bodyTyped]
  rfl

/-- On the literal-quotation fiber, resolving the body does not change its
paper-facing COMM result. -/
theorem semanticCommSubst_resolveQuotes_of_fiber
    {free : FreeSortContext} {bound : List String} {body payload : Pattern}
    (bodyTyped : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free
      (rhoReflectivePresentation.nameSort :: bound) body)
    (fiber : quotesLiteral rhoReflectivePresentation body = true)
    (payloadTyped : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound payload) :
    semanticCommSubst (resolveQuotes rhoReflectivePresentation body) payload =
      semanticCommSubst body payload := by
  have resolved := applyBindingsForRule_rhoComm_eq_resolved bodyTyped payloadTyped (.fvar "c") []
  rw [applyBindingsForRule_rhoComm_agrees_derived bodyTyped fiber payloadTyped] at resolved
  injection resolved with _ elements
  injection elements with heads
  exact heads.symm

/-- Resolution is a structural congruence of the tree's rho relation, which
includes the quote-drop equation and congruence at every position. -/
theorem resolveQuotes_structuralCongruence (process : Pattern) :
    StructuralCongruence process (resolveQuotes rhoReflectivePresentation process) := by
  apply Canonical.structuralCongruence_of_canonicalize_eq
  rw [← derivedCanonicalize_eq, ← derivedCanonicalize_eq,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.canonicalize_resolveQuotes]

end ScopeGeneral

/-- `@(*x | 0)!(0)`: a well-sorted body whose channel is a quotation exposing a
drop only through the parallel unit. -/
def hiddenQuoteDropBody : Pattern :=
  .apply "POutput"
    [.apply "NQuote" [.collection .hashBag [.apply "PDrop" [.fvar "x"], .apply "PZero" []] none],
      .apply "PZero" []]

theorem hiddenQuoteDropBody_typed :
    ProcWellSorted rhoReflectivePresentation
      (fun name => if name = "x" then some rhoReflectivePresentation.nameSort else none)
      [rhoReflectivePresentation.nameSort] hiddenQuoteDropBody := by
  exact .output (.quote (.parallel (.cons (.drop (.fvar rfl)) (.cons .unit .nil))) (by decide)) .unit

/-- Negative example of exact agreement outside the fiber: the compiled COMM
right-hand side resolves the channel `@(*x | 0)` to `x`, while the
paper-facing substitution keeps it as written. -/
theorem hiddenQuoteDrop_comm_differs (channel : Pattern) (rest : List Pattern) :
    quotesLiteral rhoReflectivePresentation hiddenQuoteDropBody = false ∧
      applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
          (rhoCommBindings channel hiddenQuoteDropBody (.apply "PZero" []) rest) =
        .collection .hashBag (.apply "POutput" [.fvar "x", .apply "PZero" []] :: rest) none ∧
      semanticCommSubst hiddenQuoteDropBody (.apply "PZero" []) = hiddenQuoteDropBody := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  rw [applyBindingsForRule_rhoComm]
  congr 2

/-! ## Executable agreement witnesses -/

/-- A received quoted payload exposes a matched dropped name exactly as the
paper-facing semantic COMM substitution does. -/
theorem rhoComm_bound_drop_agrees (channel : Pattern) (rest : List Pattern) :
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
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
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (rhoCommBindings channel (.apply "PDrop" [.bvar 0]) payload rest) =
      .collection .hashBag
        (semanticCommSubst (.apply "PDrop" [.bvar 0]) payload :: rest)
        none := by
  exact applyBindingsForRule_rhoComm_agrees_derived (.drop (.bvar rfl)) (by decide)
    payloadTyped channel rest

/-- Quoted code that mentions the received name is not admitted: rho's
binders do not reach into quotations. -/
theorem rhoComm_quoted_binder_not_admitted :
    ¬ QuotesClosed rhoReflectivePresentation.toReflectivePresentationDecl
      (.apply "NQuote" [.apply "POutput" [.bvar 0, .apply "PZero" []]]) := by
  decide

/-- Admitted quoted code, whose only binder is its own, is untouched by the
received-name substitution. -/
theorem rhoComm_quoted_code_agrees (channel : Pattern) (rest : List Pattern) :
    let quotedBody :=
      .apply "NQuote" [.apply "PInput" [.apply "NQuote" [.apply "PZero" []],
        .lambda none (.apply "PDrop" [.bvar 0])]]
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (rhoCommBindings channel quotedBody (.apply "PZero" []) rest) =
      .collection .hashBag
        (semanticCommSubst quotedBody (.apply "PZero" []) :: rest) none := by
  rfl

/-- Negative boundary: a free dropped quotation is inert in the cost/pure
profile; compiling COMM does not introduce a free-Drop reduction. -/
theorem rhoComm_free_drop_stays_inert (channel : Pattern) (rest : List Pattern) :
    let freeDrop := .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite
        (rhoCommBindings channel freeDrop (.apply "PZero" []) rest) =
      .collection .hashBag
        (semanticCommSubst freeDrop (.apply "PZero" []) :: rest) none := by
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
