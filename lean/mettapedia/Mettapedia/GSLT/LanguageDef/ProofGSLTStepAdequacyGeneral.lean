import Mettapedia.GSLT.LanguageDef.ProofGSLTStepPresentation
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# General trace adequacy: the adequate fragment of direct trace languages

`ProofGSLTStepAdequacy` proves two-sided `Step`/`Steps` adequacy for one
fixture language.  This module proves it for **every** admitted language of
an explicitly gated fragment, and pins the fragment honestly: each gate
condition is there because a compiled counterexample shows adequacy fails
without it (`ProofGSLTStepAdequacyGeneralCanary`).

The adequate fragment, per rewrite rule:

* every premise is an authored congruence premise (`DirectTraceLanguage`);
* rule patterns are **hole skeletons**: constructor/binder shapes whose
  metavariables occur only at ambient depth, with no explicit-substitution
  and no collection nodes.  Explicit substitution is evaluated by
  `applyBindings` but preserved by schema instantiation, and collection
  matching is multiset-commutative while instantiation is positional, so
  either node breaks the executable alignment;
* the premise chain is **sequentially moded**: each congruence source is
  bound by the rule's left side and earlier congruence targets, and the
  right side is bound by the end of the chain.  Without modedness the
  generated schema proves ground instances the language cannot reach;
* the language declares no reflective presentations, so declarative
  matching is the syntactic matcher.

Within the fragment, for the generated presentation of the language:
checked `Step`/`Steps` derivations from checker-well-formed sources
correspond exactly to declarative `langReduces` steps and their
reflexive-transitive closure.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Skeleton patterns

The alignment between declarative matching (`matchPattern`/`applyBindings`)
and checker instantiation (`instantiateSchemaAt?`) holds on patterns built
from constructors, binders, bound variables, and ambient-depth
metavariables only. -/

mutual

/-- Constructor/binder shape with no metavariables anywhere.  Closed
skeletons match and instantiate purely structurally. -/
def patternClosedSkeleton : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => false
  | .apply _ arguments => patternsClosedSkeleton arguments
  | .lambda _ body => patternClosedSkeleton body
  | .multiLambda _ _ body => patternClosedSkeleton body
  | .subst _ _ => false
  | .collection _ _ _ => false
termination_by pattern => sizeOf pattern

def patternsClosedSkeleton : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      patternClosedSkeleton pattern && patternsClosedSkeleton patterns
termination_by patterns => sizeOf patterns

end

mutual

/-- Ambient-hole skeleton: metavariables occur only outside every binder,
and neither explicit-substitution nor collection nodes occur.  These are
the rule patterns of the adequate direct-trace fragment. -/
def patternHoleSkeleton : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ arguments => patternsHoleSkeleton arguments
  | .lambda _ body => patternClosedSkeleton body
  | .multiLambda _ _ body => patternClosedSkeleton body
  | .subst _ _ => false
  | .collection _ _ _ => false
termination_by pattern => sizeOf pattern

def patternsHoleSkeleton : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      patternHoleSkeleton pattern && patternsHoleSkeleton patterns
termination_by patterns => sizeOf patterns

end

mutual

/-- A closed skeleton is in particular a hole skeleton. -/
theorem patternHoleSkeleton_of_closed {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true) :
    patternHoleSkeleton pattern = true := by
  cases pattern with
  | bvar index => simp [patternHoleSkeleton]
  | fvar name => simp [patternClosedSkeleton] at closed
  | apply constructor arguments =>
      have argumentsClosed : patternsClosedSkeleton arguments = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [patternHoleSkeleton] using
        patternsHoleSkeleton_of_closed argumentsClosed
  | lambda binder body =>
      simpa [patternHoleSkeleton] using
        (by simpa [patternClosedSkeleton] using closed :
          patternClosedSkeleton body = true)
  | multiLambda arity binders body =>
      simpa [patternHoleSkeleton] using
        (by simpa [patternClosedSkeleton] using closed :
          patternClosedSkeleton body = true)
  | subst body replacement => simp [patternClosedSkeleton] at closed
  | collection collectionType elements rest =>
      simp [patternClosedSkeleton] at closed
termination_by sizeOf pattern

theorem patternsHoleSkeleton_of_closed {patterns : List Pattern}
    (closed : patternsClosedSkeleton patterns = true) :
    patternsHoleSkeleton patterns = true := by
  cases patterns with
  | nil => simp [patternsHoleSkeleton]
  | cons head tail =>
      simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
      simp only [patternsHoleSkeleton, Bool.and_eq_true]
      exact ⟨patternHoleSkeleton_of_closed closed.1,
        patternsHoleSkeleton_of_closed closed.2⟩
termination_by sizeOf patterns

end

/-- The ambient metavariable names of a pattern. -/
def patternOccurrenceNames (pattern : Pattern) : List String :=
  (patternMetavariableOccurrencesAt 0 pattern).map Prod.fst

mutual

/-- Closed skeletons have no metavariable occurrences at any depth. -/
theorem patternMetavariableOccurrencesAt_closed {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true) (depth : Nat) :
    patternMetavariableOccurrencesAt depth pattern = [] := by
  cases pattern with
  | bvar index => simp [patternMetavariableOccurrencesAt]
  | fvar name => simp [patternClosedSkeleton] at closed
  | apply constructor arguments =>
      have argumentsClosed : patternsClosedSkeleton arguments = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [patternMetavariableOccurrencesAt] using
        patternsMetavariableOccurrencesAt_closed argumentsClosed depth
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [patternMetavariableOccurrencesAt] using
        patternMetavariableOccurrencesAt_closed bodyClosed (depth + 1)
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [patternMetavariableOccurrencesAt] using
        patternMetavariableOccurrencesAt_closed bodyClosed (depth + arity)
  | subst body replacement => simp [patternClosedSkeleton] at closed
  | collection collectionType elements rest =>
      simp [patternClosedSkeleton] at closed
termination_by sizeOf pattern

theorem patternsMetavariableOccurrencesAt_closed {patterns : List Pattern}
    (closed : patternsClosedSkeleton patterns = true) (depth : Nat) :
    patternsMetavariableOccurrencesAt depth patterns = [] := by
  cases patterns with
  | nil => simp [patternsMetavariableOccurrencesAt]
  | cons head tail =>
      simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
      simp only [patternsMetavariableOccurrencesAt,
        patternMetavariableOccurrencesAt_closed closed.1 depth,
        patternsMetavariableOccurrencesAt_closed closed.2 depth,
        List.nil_append]
termination_by sizeOf patterns

end

/-! ## The adequate-fragment admission gate -/

/-- Sequential modedness of a congruence premise chain: starting from the
names bound by matching the rule's left side, each congruence source must be
fully bound before its premise runs, and each congruence target binds its
names for the rest of the chain.  Returns the final bound-name set, or
`none` when a premise is not a congruence premise, is not a hole skeleton,
or reads an unbound name. -/
def tracePremisesModed (bound : List String) : List Premise → Option (List String)
  | [] => some bound
  | .congruence source target :: rest =>
      if patternHoleSkeleton source && patternHoleSkeleton target &&
          (patternOccurrenceNames source).all bound.contains then
        tracePremisesModed (bound ++ patternOccurrenceNames target) rest
      else
        none
  | _ :: _ => none

/-- One rewrite rule lies in the adequate direct-trace fragment: skeleton
left/right patterns and a sequentially moded congruence premise chain that
binds the right side. -/
def rewriteDirectTraceAdequate (rule : RewriteRule) : Bool :=
  patternHoleSkeleton rule.left && patternHoleSkeleton rule.right &&
    match tracePremisesModed (patternOccurrenceNames rule.left) rule.premises with
    | some bound => (patternOccurrenceNames rule.right).all bound.contains
    | none => false

/-- The adequate direct-trace fragment of a language: every rewrite rule is
adequate and rewrite names are unique.  Matching and substitution in the
five-field core are syntactic by construction; reflective interpretations are
separate extensions and therefore require no exclusion clause here.  A
duplicated rewrite name would already be rejected by generated-presentation
admission (duplicate rule identifiers); the gate makes it locally checkable. -/
def languageDirectTraceAdequate (language : LanguageDef) : Bool :=
  language.rewrites.all rewriteDirectTraceAdequate &&
    decide (language.rewrites.map RewriteRule.name).Nodup

theorem languageDirectTraceAdequate_rules {language : LanguageDef}
    (adequate : languageDirectTraceAdequate language = true) :
    ∀ rule ∈ language.rewrites, rewriteDirectTraceAdequate rule = true := by
  simp only [languageDirectTraceAdequate, Bool.and_eq_true] at adequate
  exact List.all_eq_true.mp adequate.1

theorem languageDirectTraceAdequate_nodupNames {language : LanguageDef}
    (adequate : languageDirectTraceAdequate language = true) :
    (language.rewrites.map RewriteRule.name).Nodup := by
  simp only [languageDirectTraceAdequate, Bool.and_eq_true,
    decide_eq_true_eq] at adequate
  exact adequate.2

/-- A moded premise chain consists of congruence premises only. -/
theorem tracePremisesModed_congruence_shape :
    ∀ {premises : List Premise} {bound final : List String},
      tracePremisesModed bound premises = some final →
      ∀ premise ∈ premises, ∃ source target,
        premise = Premise.congruence source target := by
  intro premises
  induction premises with
  | nil =>
      intro bound final _ premise member
      cases member
  | cons head tail inductionHypothesis =>
      intro bound final chain premise member
      cases head with
      | congruence source target =>
          simp only [tracePremisesModed] at chain
          split at chain
          · rcases List.mem_cons.mp member with rfl | tailMember
            · exact ⟨source, target, rfl⟩
            · exact inductionHypothesis chain premise tailMember
          · cases chain
      | freshness condition => simp [tracePremisesModed] at chain
      | relationQuery relation arguments => simp [tracePremisesModed] at chain
      | forAll collection parameter body => simp [tracePremisesModed] at chain

/-- Adequate premise chains are congruence-only, so the adequate fragment
refines the direct-trace premise gate. -/
theorem directTracePresentable_of_adequate {language : LanguageDef}
    (adequate : languageDirectTraceAdequate language = true) :
    LanguageDef.directTracePresentable language = true := by
  apply List.all_eq_true.mpr
  intro rule member
  have ruleAdequate := languageDirectTraceAdequate_rules adequate rule member
  simp only [rewriteDirectTraceAdequate, Bool.and_eq_true] at ruleAdequate
  obtain ⟨final, chain⟩ : ∃ final,
      tracePremisesModed (patternOccurrenceNames rule.left) rule.premises =
        some final := by
    rcases modedResult : tracePremisesModed (patternOccurrenceNames rule.left)
        rule.premises with _ | final
    · simp only [modedResult] at ruleAdequate
      cases ruleAdequate.2
    · exact ⟨final, rfl⟩
  simp only [RewriteRule.directTracePresentable]
  apply List.all_eq_true.mpr
  intro premise premiseMember
  obtain ⟨source, target, rfl⟩ :=
    tracePremisesModed_congruence_shape chain premise premiseMember
  rfl

/-! ## Binding agreement toolkit

Matching produces binding lists whose entries agree with an ambient
assignment; merging such lists succeeds and preserves the agreement.
Agreement is stated by membership so internally duplicated entries are
covered. -/

/-- Every entry of `bindings` carries the value that `ambient` assigns to
its name. -/
def bindingsAgreeWith (ambient bindings : Bindings) : Prop :=
  ∀ pair ∈ bindings, Bindings.lookup ambient pair.1 = some pair.2

theorem bindingsAgreeWith_nil (ambient : Bindings) :
    bindingsAgreeWith ambient [] := by
  intro pair member
  cases member

/-- Successful lookups in an agreeing list are ambient lookups. -/
theorem bindingsAgreeWith_lookup {ambient bindings : Bindings}
    (agree : bindingsAgreeWith ambient bindings) {name : String}
    {value : Pattern}
    (lookup : Bindings.lookup bindings name = some value) :
    Bindings.lookup ambient name = some value := by
  unfold Bindings.lookup at lookup
  cases found : bindings.find? (fun pair => pair.1 == name) with
  | none => rw [found] at lookup; cases lookup
  | some pair =>
      rw [found] at lookup
      have valueEq : pair.2 = value := by simpa using lookup
      have nameEq : pair.1 = name := by
        simpa using List.find?_some found
      have ambientEq := agree pair (List.mem_of_find?_eq_some found)
      rw [nameEq, valueEq] at ambientEq
      exact ambientEq

/-- One merge step of `mergeBindings`, factored out for the fold lemmas. -/
private def mergeStep (accumulated : Bindings) (entry : String × Pattern) :
    Option Bindings :=
  match accumulated.find? (·.1 == entry.1) with
  | none => some ((entry.1, entry.2) :: accumulated)
  | some (_, existing) =>
      if existing == entry.2 then some accumulated else none

private theorem mergeBindings_eq_foldl (accumulated extra : Bindings) :
    mergeBindings accumulated extra =
      extra.foldlM (init := accumulated) mergeStep := by
  unfold mergeBindings mergeStep
  rfl

private theorem option_some_bind {α β : Type _} (value : α)
    (rest : α → Option β) : (some value >>= rest) = rest value := rfl

private theorem option_none_bind {α β : Type _} (rest : α → Option β) :
    ((none : Option α) >>= rest) = none := rfl

/-- Inversion of one successful merge step: either the entry name is new and
is prepended, or it is already bound to exactly the entry value. -/
private theorem mergeStep_some_inversion {accumulated merged : Bindings}
    {entry : String × Pattern}
    (step : mergeStep accumulated entry = some merged) :
    (accumulated.find? (·.1 == entry.1) = none ∧
        merged = entry :: accumulated) ∨
      (Bindings.lookup accumulated entry.1 = some entry.2 ∧
        merged = accumulated) := by
  unfold mergeStep at step
  cases found : accumulated.find? (·.1 == entry.1) with
  | none =>
      rw [found] at step
      have step' : some ((entry.1, entry.2) :: accumulated) = some merged :=
        step
      exact Or.inl ⟨rfl, (Option.some.inj step').symm⟩
  | some foundPair =>
      rcases foundPair with ⟨foundName, existing⟩
      rw [found] at step
      have step' :
          (if (existing == entry.2) = true then some accumulated else none) =
            some merged := step
      by_cases sameValue : (existing == entry.2) = true
      · rw [if_pos sameValue] at step'
        have valueEq : existing = entry.2 := by simpa using sameValue
        refine Or.inr ⟨?_, (Option.some.inj step').symm⟩
        unfold Bindings.lookup
        rw [found, ← valueEq]
        rfl
      · rw [if_neg sameValue] at step'
        cases step'

/-- Folding merge steps preserves every successful lookup of the
accumulator. -/
private theorem foldl_mergeStep_lookup_left :
    ∀ (extra accumulated merged : Bindings),
      extra.foldlM (init := accumulated) mergeStep = some merged →
      ∀ {name : String} {value : Pattern},
        Bindings.lookup accumulated name = some value →
        Bindings.lookup merged name = some value := by
  intro extra
  induction extra with
  | nil =>
      intro accumulated merged fold name value lookup
      have fold' : some accumulated = some merged := fold
      rw [← Option.some.inj fold']
      exact lookup
  | cons entry rest inductionHypothesis =>
      intro accumulated merged fold name value lookup
      rw [List.foldlM_cons] at fold
      cases step : mergeStep accumulated entry with
      | none => rw [step, option_none_bind] at fold; cases fold
      | some middle =>
          rw [step, option_some_bind] at fold
          refine inductionHypothesis middle merged fold ?_
          rcases mergeStep_some_inversion step with
            ⟨findNone, rfl⟩ | ⟨-, rfl⟩
          · unfold Bindings.lookup at lookup ⊢
            by_cases headMatch : (entry.1 == name) = true
            · exfalso
              have nameEq : entry.1 = name := by simpa using headMatch
              rw [← nameEq] at lookup
              rw [findNone] at lookup
              cases lookup
            · rw [List.find?_cons_of_neg (by simpa using headMatch)]
              exact lookup
          · exact lookup

/-- Every entry of the right operand of a successful merge fold is looked up
at exactly its own value in the result. -/
private theorem foldl_mergeStep_lookup_right :
    ∀ (extra accumulated merged : Bindings),
      extra.foldlM (init := accumulated) mergeStep = some merged →
      ∀ pair ∈ extra, Bindings.lookup merged pair.1 = some pair.2 := by
  intro extra
  induction extra with
  | nil =>
      intro accumulated merged _ pair member
      cases member
  | cons entry rest inductionHypothesis =>
      intro accumulated merged fold pair member
      rw [List.foldlM_cons] at fold
      cases step : mergeStep accumulated entry with
      | none => rw [step, option_none_bind] at fold; cases fold
      | some middle =>
          rw [step, option_some_bind] at fold
          rcases List.mem_cons.mp member with rfl | restMember
          · have middleLookup :
                Bindings.lookup middle pair.1 = some pair.2 := by
              rcases mergeStep_some_inversion step with
                ⟨-, rfl⟩ | ⟨accLookup, rfl⟩
              · unfold Bindings.lookup
                rw [List.find?_cons_of_pos (by simp)]
                rfl
              · exact accLookup
            exact foldl_mergeStep_lookup_left rest middle merged fold
              middleLookup
          · exact inductionHypothesis middle merged fold pair restMember

/-- Every entry of a successful merge fold comes from one of the
operands. -/
private theorem foldl_mergeStep_mem_source :
    ∀ (extra accumulated merged : Bindings),
      extra.foldlM (init := accumulated) mergeStep = some merged →
      ∀ pair ∈ merged, pair ∈ accumulated ∨ pair ∈ extra := by
  intro extra
  induction extra with
  | nil =>
      intro accumulated merged fold pair member
      have fold' : some accumulated = some merged := fold
      rw [← Option.some.inj fold'] at member
      exact Or.inl member
  | cons entry rest inductionHypothesis =>
      intro accumulated merged fold pair member
      rw [List.foldlM_cons] at fold
      cases step : mergeStep accumulated entry with
      | none => rw [step, option_none_bind] at fold; cases fold
      | some middle =>
          rw [step, option_some_bind] at fold
          rcases inductionHypothesis middle merged fold pair member with
            middleMember | restMember
          · rcases mergeStep_some_inversion step with
              ⟨-, rfl⟩ | ⟨-, rfl⟩
            · rcases List.mem_cons.mp middleMember with rfl | accMember
              · exact Or.inr (List.mem_cons_self ..)
              · exact Or.inl accMember
            · exact Or.inl middleMember
          · exact Or.inr (List.mem_cons_of_mem _ restMember)

/-- Merging lists that agree with one ambient assignment succeeds and
preserves the agreement. -/
private theorem foldl_mergeStep_some_of_agree {ambient : Bindings} :
    ∀ (extra accumulated : Bindings),
      bindingsAgreeWith ambient accumulated →
      bindingsAgreeWith ambient extra →
      ∃ merged, extra.foldlM (init := accumulated) mergeStep = some merged ∧
        bindingsAgreeWith ambient merged := by
  intro extra
  induction extra with
  | nil =>
      intro accumulated accAgrees _
      exact ⟨accumulated, by simp, accAgrees⟩
  | cons entry rest inductionHypothesis =>
      intro accumulated accAgrees extraAgrees
      have entryAgrees := extraAgrees entry (List.mem_cons_self ..)
      have restAgrees : bindingsAgreeWith ambient rest := fun pair member =>
        extraAgrees pair (List.mem_cons_of_mem _ member)
      have stepResult : ∃ middle,
          mergeStep accumulated entry = some middle ∧
            bindingsAgreeWith ambient middle := by
        unfold mergeStep
        cases found : accumulated.find? (·.1 == entry.1) with
        | none =>
            refine ⟨(entry.1, entry.2) :: accumulated, rfl, ?_⟩
            intro pair member
            rcases List.mem_cons.mp member with rfl | accMember
            · exact entryAgrees
            · exact accAgrees pair accMember
        | some foundPair =>
            rcases foundPair with ⟨foundName, existing⟩
            have foundMember := List.mem_of_find?_eq_some found
            have foundNameEq : foundName = entry.1 := by
              simpa using List.find?_some found
            have existingAmbient := accAgrees (foundName, existing) foundMember
            rw [foundNameEq] at existingAmbient
            have valueEq : existing = entry.2 :=
              Option.some.inj (existingAmbient.symm.trans entryAgrees)
            refine ⟨accumulated, ?_, accAgrees⟩
            show (if (existing == entry.2) = true then some accumulated
              else none) = some accumulated
            rw [if_pos (by simpa using valueEq)]
      obtain ⟨middle, step, middleAgrees⟩ := stepResult
      obtain ⟨merged, fold, mergedAgrees⟩ :=
        inductionHypothesis middle middleAgrees restAgrees
      refine ⟨merged, ?_, mergedAgrees⟩
      rw [List.foldlM_cons, step, option_some_bind]
      exact fold

/-- Merging preserves every successful lookup of the left operand. -/
theorem mergeBindings_lookup_left {accumulated extra merged : Bindings}
    (merge : mergeBindings accumulated extra = some merged)
    {name : String} {value : Pattern}
    (lookup : Bindings.lookup accumulated name = some value) :
    Bindings.lookup merged name = some value := by
  rw [mergeBindings_eq_foldl] at merge
  exact foldl_mergeStep_lookup_left extra accumulated merged merge lookup

/-- Every entry of the right operand of a successful merge is looked up at
exactly its own value in the result. -/
theorem mergeBindings_lookup_right {accumulated extra merged : Bindings}
    (merge : mergeBindings accumulated extra = some merged) :
    ∀ pair ∈ extra, Bindings.lookup merged pair.1 = some pair.2 := by
  rw [mergeBindings_eq_foldl] at merge
  exact foldl_mergeStep_lookup_right extra accumulated merged merge

/-- Every entry of a successful merge comes from one of the operands. -/
theorem mergeBindings_mem_source {accumulated extra merged : Bindings}
    (merge : mergeBindings accumulated extra = some merged) :
    ∀ pair ∈ merged, pair ∈ accumulated ∨ pair ∈ extra := by
  rw [mergeBindings_eq_foldl] at merge
  exact foldl_mergeStep_mem_source extra accumulated merged merge

/-- Merging two lists that agree with one ambient assignment succeeds, and
the result again agrees. -/
theorem mergeBindings_some_of_agree {ambient accumulated extra : Bindings}
    (accAgrees : bindingsAgreeWith ambient accumulated)
    (extraAgrees : bindingsAgreeWith ambient extra) :
    ∃ merged, mergeBindings accumulated extra = some merged ∧
      bindingsAgreeWith ambient merged := by
  rw [mergeBindings_eq_foldl]
  exact foldl_mergeStep_some_of_agree extra accumulated accAgrees extraAgrees

private theorem mergeBindings_nil_right (bindings : Bindings) :
    mergeBindings bindings [] = some bindings := rfl

/-- A successful lookup names a member pair. -/
theorem bindings_mem_of_lookup {bindings : Bindings} {name : String}
    {value : Pattern}
    (lookup : Bindings.lookup bindings name = some value) :
    (name, value) ∈ bindings := by
  unfold Bindings.lookup at lookup
  cases found : bindings.find? (fun pair => pair.1 == name) with
  | none => rw [found] at lookup; cases lookup
  | some pair =>
      rw [found] at lookup
      have valueEq : pair.2 = value := by simpa using lookup
      have nameEq : pair.1 = name := by simpa using List.find?_some found
      have member := List.mem_of_find?_eq_some found
      rw [← nameEq, ← valueEq]
      simpa using member

/-! ## Occurrence-name bookkeeping -/

/-- The ambient metavariable names across a pattern list. -/
def patternsOccurrenceNames (patterns : List Pattern) : List String :=
  (patternsMetavariableOccurrencesAt 0 patterns).map Prod.fst

@[simp] theorem patternOccurrenceNames_fvar (name : String) :
    patternOccurrenceNames (.fvar name) = [name] := by
  simp [patternOccurrenceNames, patternMetavariableOccurrencesAt]

@[simp] theorem patternOccurrenceNames_bvar (index : Nat) :
    patternOccurrenceNames (.bvar index) = [] := by
  simp [patternOccurrenceNames, patternMetavariableOccurrencesAt]

@[simp] theorem patternOccurrenceNames_apply (constructor : String)
    (arguments : List Pattern) :
    patternOccurrenceNames (.apply constructor arguments) =
      patternsOccurrenceNames arguments := by
  simp [patternOccurrenceNames, patternsOccurrenceNames,
    patternMetavariableOccurrencesAt]

@[simp] theorem patternsOccurrenceNames_nil :
    patternsOccurrenceNames [] = [] := by
  simp [patternsOccurrenceNames, patternsMetavariableOccurrencesAt]

@[simp] theorem patternsOccurrenceNames_cons (pattern : Pattern)
    (patterns : List Pattern) :
    patternsOccurrenceNames (pattern :: patterns) =
      patternOccurrenceNames pattern ++ patternsOccurrenceNames patterns := by
  simp [patternsOccurrenceNames, patternOccurrenceNames,
    patternsMetavariableOccurrencesAt]

theorem patternOccurrenceNames_closed {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true) :
    patternOccurrenceNames pattern = [] := by
  simp [patternOccurrenceNames,
    patternMetavariableOccurrencesAt_closed closed 0]

/-! ## `applyBindings` on skeleton patterns -/

theorem applyBindings_fvar (bindings : Bindings) (name : String) :
    applyBindings bindings (.fvar name) =
      (Bindings.lookup bindings name).getD (.fvar name) := by
  simp only [applyBindings, Bindings.lookup]
  cases bindings.find? (fun pair => pair.1 == name) with
  | none => rfl
  | some pair => rfl

mutual

/-- Closed skeletons are fixed by every binding application. -/
theorem applyBindings_closedSkeleton {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true) (bindings : Bindings) :
    applyBindings bindings pattern = pattern := by
  cases pattern with
  | bvar index => simp [applyBindings]
  | fvar name => simp [patternClosedSkeleton] at closed
  | apply constructor arguments =>
      have argumentsClosed : patternsClosedSkeleton arguments = true := by
        simpa [patternClosedSkeleton] using closed
      simp only [applyBindings]
      rw [applyBindingsList_closedSkeleton argumentsClosed bindings]
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simp only [applyBindings]
      rw [applyBindings_closedSkeleton bodyClosed bindings]
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simp only [applyBindings]
      rw [applyBindings_closedSkeleton bodyClosed bindings]
  | subst body replacement => simp [patternClosedSkeleton] at closed
  | collection collectionType elements rest =>
      simp [patternClosedSkeleton] at closed
termination_by sizeOf pattern

theorem applyBindingsList_closedSkeleton {patterns : List Pattern}
    (closed : patternsClosedSkeleton patterns = true) (bindings : Bindings) :
    patterns.map (applyBindings bindings) = patterns := by
  cases patterns with
  | nil => rfl
  | cons head tail =>
      simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
      simp only [List.map_cons,
        applyBindings_closedSkeleton closed.1 bindings,
        applyBindingsList_closedSkeleton closed.2 bindings]
termination_by sizeOf patterns

end

mutual

/-- Binding application on hole skeletons depends only on the lookups of
the pattern's own occurrence names. -/
theorem applyBindings_agree {pattern : Pattern}
    (hole : patternHoleSkeleton pattern = true) {left right : Bindings}
    (agree : ∀ name ∈ patternOccurrenceNames pattern,
      Bindings.lookup left name = Bindings.lookup right name) :
    applyBindings left pattern = applyBindings right pattern := by
  cases pattern with
  | bvar index => simp [applyBindings]
  | fvar name =>
      rw [applyBindings_fvar, applyBindings_fvar,
        agree name (by simp)]
  | apply constructor arguments =>
      have argumentsHole : patternsHoleSkeleton arguments = true := by
        simpa [patternHoleSkeleton] using hole
      simp only [applyBindings]
      rw [applyBindingsList_agree argumentsHole (by simpa using agree)]
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      simp only [applyBindings]
      rw [applyBindings_closedSkeleton bodyClosed left,
        applyBindings_closedSkeleton bodyClosed right]
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      simp only [applyBindings]
      rw [applyBindings_closedSkeleton bodyClosed left,
        applyBindings_closedSkeleton bodyClosed right]
  | subst body replacement => simp [patternHoleSkeleton] at hole
  | collection collectionType elements rest =>
      simp [patternHoleSkeleton] at hole
termination_by sizeOf pattern

theorem applyBindingsList_agree {patterns : List Pattern}
    (holes : patternsHoleSkeleton patterns = true) {left right : Bindings}
    (agree : ∀ name ∈ patternsOccurrenceNames patterns,
      Bindings.lookup left name = Bindings.lookup right name) :
    patterns.map (applyBindings left) = patterns.map (applyBindings right) := by
  cases patterns with
  | nil => rfl
  | cons head tail =>
      simp only [patternsHoleSkeleton, Bool.and_eq_true] at holes
      simp only [patternsOccurrenceNames_cons, List.mem_append] at agree
      simp only [List.map_cons,
        applyBindings_agree holes.1
          (fun name member => agree name (Or.inl member)),
        applyBindingsList_agree holes.2
          (fun name member => agree name (Or.inr member))]
termination_by sizeOf patterns

end

mutual

/-- Well-scoped closed skeletons are ground at their scope depth. -/
theorem isGroundAt_of_closedSkeleton {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true) (depth : Nat)
    (wellScoped : Pattern.isWellScopedAt depth pattern = true) :
    Pattern.isGroundAt depth pattern = true := by
  cases pattern with
  | bvar index =>
      simpa [Pattern.isGroundAt] using
        (by simpa [Pattern.isWellScopedAt] using wellScoped : index < depth)
  | fvar name => simp [patternClosedSkeleton] at closed
  | apply constructor arguments =>
      have argumentsClosed : patternsClosedSkeleton arguments = true := by
        simpa [patternClosedSkeleton] using closed
      have argumentsScoped :
          Pattern.isWellScopedListAt depth arguments = true := by
        simpa [Pattern.isWellScopedAt] using wellScoped
      simpa [Pattern.isGroundAt] using
        isGroundListAt_of_closedSkeleton argumentsClosed depth argumentsScoped
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      have bodyScoped : Pattern.isWellScopedAt (depth + 1) body = true := by
        simpa [Pattern.isWellScopedAt] using wellScoped
      simpa [Pattern.isGroundAt] using
        isGroundAt_of_closedSkeleton bodyClosed (depth + 1) bodyScoped
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      have bodyScoped :
          Pattern.isWellScopedAt (depth + arity) body = true := by
        simpa [Pattern.isWellScopedAt] using wellScoped
      simpa [Pattern.isGroundAt] using
        isGroundAt_of_closedSkeleton bodyClosed (depth + arity) bodyScoped
  | subst body replacement => simp [patternClosedSkeleton] at closed
  | collection collectionType elements rest =>
      simp [patternClosedSkeleton] at closed
termination_by sizeOf pattern

theorem isGroundListAt_of_closedSkeleton {patterns : List Pattern}
    (closed : patternsClosedSkeleton patterns = true) (depth : Nat)
    (wellScoped : Pattern.isWellScopedListAt depth patterns = true) :
    Pattern.isGroundListAt depth patterns = true := by
  cases patterns with
  | nil => simp [Pattern.isGroundListAt]
  | cons head tail =>
      simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at wellScoped
      simp only [Pattern.isGroundListAt, Bool.and_eq_true]
      exact ⟨isGroundAt_of_closedSkeleton closed.1 depth wellScoped.1,
        isGroundListAt_of_closedSkeleton closed.2 depth wellScoped.2⟩
termination_by sizeOf patterns

end

/-- Values assigned by a binding list are checker-well-formed. -/
def bindingsValuesWellFormed (bindings : Bindings) : Prop :=
  ∀ pair ∈ bindings, Pattern.isGroundAt 0 pair.2 = true ∧
    Pattern.hasCanonicalBinderMetadata pair.2 = true

mutual

/-- Applying well-formed bindings that cover a well-scoped, canonical hole
skeleton produces a checker-well-formed term. -/
theorem applyBindings_wellFormed {pattern : Pattern}
    (hole : patternHoleSkeleton pattern = true)
    (wellScoped : Pattern.isWellScopedAt 0 pattern = true)
    (canonical : Pattern.hasCanonicalBinderMetadata pattern = true)
    {bindings : Bindings}
    (values : bindingsValuesWellFormed bindings)
    (cover : ∀ name ∈ patternOccurrenceNames pattern,
      (Bindings.lookup bindings name).isSome) :
    Pattern.isGroundAt 0 (applyBindings bindings pattern) = true ∧
      Pattern.hasCanonicalBinderMetadata
        (applyBindings bindings pattern) = true := by
  cases pattern with
  | bvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at wellScoped
      omega
  | fvar name =>
      obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
        (cover name (by simp))
      rw [applyBindings_fvar, valueEq]
      exact values (name, value) (bindings_mem_of_lookup valueEq)
  | apply constructor arguments =>
      have argumentsHole : patternsHoleSkeleton arguments = true := by
        simpa [patternHoleSkeleton] using hole
      have argumentsScoped :
          Pattern.isWellScopedListAt 0 arguments = true := by
        simpa [Pattern.isWellScopedAt] using wellScoped
      have argumentsCanonical :
          Pattern.hasCanonicalBinderMetadataList arguments = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonical
      have listFacts := applyBindingsList_wellFormed argumentsHole
        argumentsScoped argumentsCanonical values (by simpa using cover)
      constructor
      · simpa [applyBindings, Pattern.isGroundAt] using listFacts.1
      · simpa [applyBindings, Pattern.hasCanonicalBinderMetadata] using
          listFacts.2
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      have bodyScoped : Pattern.isWellScopedAt 1 body = true := by
        simpa [Pattern.isWellScopedAt] using wellScoped
      have binderNone : binder.isNone = true ∧
          Pattern.hasCanonicalBinderMetadata body = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonical
      have fixed := applyBindings_closedSkeleton bodyClosed bindings
      constructor
      · simp only [applyBindings, fixed, Pattern.isGroundAt]
        exact isGroundAt_of_closedSkeleton bodyClosed 1 bodyScoped
      · simp only [applyBindings, fixed, Pattern.hasCanonicalBinderMetadata,
          Bool.and_eq_true]
        exact ⟨binderNone.1, binderNone.2⟩
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      have bodyScoped : Pattern.isWellScopedAt (0 + arity) body = true := by
        simpa [Pattern.isWellScopedAt] using wellScoped
      have binderFacts : binders.isEmpty = true ∧
          Pattern.hasCanonicalBinderMetadata body = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonical
      have fixed := applyBindings_closedSkeleton bodyClosed bindings
      constructor
      · simp only [applyBindings, fixed, Pattern.isGroundAt]
        simpa using isGroundAt_of_closedSkeleton bodyClosed (0 + arity)
          bodyScoped
      · simp only [applyBindings, fixed, Pattern.hasCanonicalBinderMetadata,
          Bool.and_eq_true]
        exact ⟨binderFacts.1, binderFacts.2⟩
  | subst body replacement => simp [patternHoleSkeleton] at hole
  | collection collectionType elements rest =>
      simp [patternHoleSkeleton] at hole
termination_by sizeOf pattern

theorem applyBindingsList_wellFormed {patterns : List Pattern}
    (holes : patternsHoleSkeleton patterns = true)
    (wellScoped : Pattern.isWellScopedListAt 0 patterns = true)
    (canonical : Pattern.hasCanonicalBinderMetadataList patterns = true)
    {bindings : Bindings}
    (values : bindingsValuesWellFormed bindings)
    (cover : ∀ name ∈ patternsOccurrenceNames patterns,
      (Bindings.lookup bindings name).isSome) :
    Pattern.isGroundListAt 0 (patterns.map (applyBindings bindings)) = true ∧
      Pattern.hasCanonicalBinderMetadataList
        (patterns.map (applyBindings bindings)) = true := by
  cases patterns with
  | nil => simp [Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadataList]
  | cons head tail =>
      simp only [patternsHoleSkeleton, Bool.and_eq_true] at holes
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at wellScoped
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        at canonical
      simp only [patternsOccurrenceNames_cons, List.mem_append] at cover
      have headFacts := applyBindings_wellFormed holes.1 wellScoped.1 canonical.1
        values (fun name member => cover name (Or.inl member))
      have tailFacts := applyBindingsList_wellFormed holes.2 wellScoped.2
        canonical.2 values (fun name member => cover name (Or.inr member))
      simp only [List.map_cons, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
      exact ⟨⟨headFacts.1, tailFacts.1⟩, ⟨headFacts.2, tailFacts.2⟩⟩
termination_by sizeOf patterns

end

/-! ## Alignment of checker instantiation with binding application -/

/-- The positional argument assignment of a rule instance, as a binding
list. -/
def zipBindings : List (String × Nat) → List Pattern → Bindings
  | (name, _) :: formals, argument :: arguments =>
      (name, argument) :: zipBindings formals arguments
  | _, _ => []

theorem lookupArgumentAt?_eq_zip_lookup :
    ∀ {formals : List (String × Nat)} {arguments : List Pattern},
      (∀ formal ∈ formals, formal.2 = 0) →
      ∀ name : String,
        lookupArgumentAt? formals arguments name 0 =
          Bindings.lookup (zipBindings formals arguments) name := by
  intro formals
  induction formals with
  | nil =>
      intro arguments _ name
      cases arguments <;>
        simp [lookupArgumentAt?, zipBindings, Bindings.lookup]
  | cons formal rest inductionHypothesis =>
      intro arguments allZero name
      rcases formal with ⟨formalName, formalDepth⟩
      have formalDepthZero : formalDepth = 0 :=
        allZero (formalName, formalDepth) (List.mem_cons_self ..)
      subst formalDepthZero
      cases arguments with
      | nil => simp [lookupArgumentAt?, zipBindings, Bindings.lookup]
      | cons argument args =>
          simp only [lookupArgumentAt?, zipBindings]
          by_cases nameMatch : formalName = name
          · subst nameMatch
            rw [if_pos rfl]
            unfold Bindings.lookup
            rw [List.find?_cons_of_pos (by simp)]
            rfl
          · rw [if_neg (by simp [nameMatch])]
            unfold Bindings.lookup
            rw [List.find?_cons_of_neg (by simpa using nameMatch)]
            exact inductionHypothesis
              (fun formal member => allZero formal
                (List.mem_cons_of_mem _ member)) name

mutual

/-- Closed skeletons instantiate to themselves at every depth. -/
theorem instantiateSchemaAt?_closedSkeleton {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true)
    (formals : List (String × Nat)) (arguments : List Pattern) (depth : Nat) :
    instantiateSchemaAt? formals arguments depth pattern = some pattern := by
  cases pattern with
  | bvar index => simp [instantiateSchemaAt?]
  | fvar name => simp [patternClosedSkeleton] at closed
  | apply constructor schemas =>
      have schemasClosed : patternsClosedSkeleton schemas = true := by
        simpa [patternClosedSkeleton] using closed
      simp [instantiateSchemaAt?,
        instantiateSchemasAt?_closedSkeleton schemasClosed formals arguments
          depth]
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simp [instantiateSchemaAt?,
        instantiateSchemaAt?_closedSkeleton bodyClosed formals arguments
          (depth + 1)]
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simp [instantiateSchemaAt?,
        instantiateSchemaAt?_closedSkeleton bodyClosed formals arguments
          (depth + arity)]
  | subst body replacement => simp [patternClosedSkeleton] at closed
  | collection collectionType elements rest =>
      simp [patternClosedSkeleton] at closed
termination_by sizeOf pattern

theorem instantiateSchemasAt?_closedSkeleton {patterns : List Pattern}
    (closed : patternsClosedSkeleton patterns = true)
    (formals : List (String × Nat)) (arguments : List Pattern) (depth : Nat) :
    instantiateSchemasAt? formals arguments depth patterns = some patterns := by
  cases patterns with
  | nil => simp [instantiateSchemasAt?]
  | cons head tail =>
      simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
      simp [instantiateSchemasAt?,
        instantiateSchemaAt?_closedSkeleton closed.1 formals arguments depth,
        instantiateSchemasAt?_closedSkeleton closed.2 formals arguments depth]
termination_by sizeOf patterns

end

mutual

/-- On hole skeletons whose occurrence names are all assigned, checker
instantiation is exactly binding application with the positional
assignment. -/
theorem instantiateSchemaAt?_eq_applyBindings {pattern : Pattern}
    (hole : patternHoleSkeleton pattern = true)
    {formals : List (String × Nat)} {arguments : List Pattern}
    (allZero : ∀ formal ∈ formals, formal.2 = 0)
    (cover : ∀ name ∈ patternOccurrenceNames pattern,
      (Bindings.lookup (zipBindings formals arguments) name).isSome) :
    instantiateSchemaAt? formals arguments 0 pattern =
      some (applyBindings (zipBindings formals arguments) pattern) := by
  cases pattern with
  | bvar index => simp [instantiateSchemaAt?, applyBindings]
  | fvar name =>
      obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
        (cover name (by simp))
      rw [applyBindings_fvar, valueEq]
      simpa [instantiateSchemaAt?] using
        (lookupArgumentAt?_eq_zip_lookup allZero name).trans valueEq
  | apply constructor schemas =>
      have schemasHole : patternsHoleSkeleton schemas = true := by
        simpa [patternHoleSkeleton] using hole
      simp [instantiateSchemaAt?, applyBindings,
        instantiateSchemasAt?_eq_applyBindings schemasHole allZero
          (by simpa using cover)]
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      simp [instantiateSchemaAt?, applyBindings,
        instantiateSchemaAt?_closedSkeleton bodyClosed formals arguments 1,
        applyBindings_closedSkeleton bodyClosed]
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      simp [instantiateSchemaAt?, applyBindings,
        instantiateSchemaAt?_closedSkeleton bodyClosed formals arguments arity,
        applyBindings_closedSkeleton bodyClosed]
  | subst body replacement => simp [patternHoleSkeleton] at hole
  | collection collectionType elements rest =>
      simp [patternHoleSkeleton] at hole
termination_by sizeOf pattern

theorem instantiateSchemasAt?_eq_applyBindings {patterns : List Pattern}
    (holes : patternsHoleSkeleton patterns = true)
    {formals : List (String × Nat)} {arguments : List Pattern}
    (allZero : ∀ formal ∈ formals, formal.2 = 0)
    (cover : ∀ name ∈ patternsOccurrenceNames patterns,
      (Bindings.lookup (zipBindings formals arguments) name).isSome) :
    instantiateSchemasAt? formals arguments 0 patterns =
      some (patterns.map
        (applyBindings (zipBindings formals arguments))) := by
  cases patterns with
  | nil => simp [instantiateSchemasAt?]
  | cons head tail =>
      simp only [patternsHoleSkeleton, Bool.and_eq_true] at holes
      simp only [patternsOccurrenceNames_cons, List.mem_append] at cover
      simp [instantiateSchemasAt?,
        instantiateSchemaAt?_eq_applyBindings holes.1 allZero
          (fun name member => cover name (Or.inl member)),
        instantiateSchemasAt?_eq_applyBindings holes.2 allZero
          (fun name member => cover name (Or.inr member))]
termination_by sizeOf patterns

end

/-! ## Matching on skeleton patterns -/

mutual

/-- Closed skeletons match themselves with no bindings. -/
theorem matchPattern_closedSkeleton_self {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true) :
    [] ∈ matchPattern pattern pattern := by
  cases pattern with
  | bvar index => simp [matchPattern]
  | fvar name => simp [patternClosedSkeleton] at closed
  | apply constructor arguments =>
      have argumentsClosed : patternsClosedSkeleton arguments = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [matchPattern] using
        matchArgs_closedSkeleton_self argumentsClosed
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [matchPattern] using matchPattern_closedSkeleton_self bodyClosed
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      simpa [matchPattern] using matchPattern_closedSkeleton_self bodyClosed
  | subst body replacement => simp [patternClosedSkeleton] at closed
  | collection collectionType elements rest =>
      simp [patternClosedSkeleton] at closed
termination_by sizeOf pattern

theorem matchArgs_closedSkeleton_self {patterns : List Pattern}
    (closed : patternsClosedSkeleton patterns = true) :
    [] ∈ matchArgs patterns patterns := by
  cases patterns with
  | nil => simp [matchArgs]
  | cons head tail =>
      simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
      have headSelf := matchPattern_closedSkeleton_self closed.1
      have tailSelf := matchArgs_closedSkeleton_self closed.2
      simp only [matchArgs, List.mem_flatMap, List.mem_filterMap]
      exact ⟨[], headSelf, [], tailSelf, rfl⟩
termination_by sizeOf patterns

end

mutual

/-- A closed canonical skeleton matches only itself, with no bindings. -/
theorem matchPattern_closedSkeleton_eq {pattern term : Pattern}
    (closed : patternClosedSkeleton pattern = true)
    (canonicalPattern : Pattern.hasCanonicalBinderMetadata pattern = true)
    (canonicalTerm : Pattern.hasCanonicalBinderMetadata term = true) :
    ∀ bindings ∈ matchPattern pattern term,
      term = pattern ∧ bindings = [] := by
  intro bindings member
  cases pattern with
  | bvar index =>
      cases term with
      | bvar termIndex =>
          simp only [matchPattern] at member
          split at member
          case isTrue guard =>
              have indexEq : termIndex = index := by
                have := of_decide_eq_true (by simpa using guard)
                omega
              simp only [List.mem_singleton] at member
              exact ⟨by rw [indexEq], member⟩
          case isFalse => simp at member
      | fvar name => simp [matchPattern] at member
      | apply constructor arguments => simp [matchPattern] at member
      | lambda binder body => simp [matchPattern] at member
      | multiLambda arity binders body => simp [matchPattern] at member
      | subst body replacement => simp [matchPattern] at member
      | collection collectionType elements rest =>
          simp [matchPattern] at member
  | fvar name => simp [patternClosedSkeleton] at closed
  | apply constructor arguments =>
      have argumentsClosed : patternsClosedSkeleton arguments = true := by
        simpa [patternClosedSkeleton] using closed
      have argumentsCanonical :
          Pattern.hasCanonicalBinderMetadataList arguments = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalPattern
      cases term with
      | apply termConstructor termArguments =>
          simp only [matchPattern] at member
          split at member
          case isTrue guard =>
              have guardFacts :
                  constructor = termConstructor ∧
                    arguments.length = termArguments.length := by
                simpa using guard
              have termArgumentsCanonical :
                  Pattern.hasCanonicalBinderMetadataList termArguments =
                    true := by
                simpa [Pattern.hasCanonicalBinderMetadata] using canonicalTerm
              have listFacts := matchArgs_closedSkeleton_eq argumentsClosed
                argumentsCanonical termArgumentsCanonical bindings member
              exact ⟨by rw [guardFacts.1, listFacts.1], listFacts.2⟩
          case isFalse => simp at member
      | bvar termIndex => simp [matchPattern] at member
      | fvar termName => simp [matchPattern] at member
      | lambda binder body => simp [matchPattern] at member
      | multiLambda arity binders body => simp [matchPattern] at member
      | subst body replacement => simp [matchPattern] at member
      | collection collectionType elements rest =>
          simp [matchPattern] at member
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      have binderFacts : binder.isNone = true ∧
          Pattern.hasCanonicalBinderMetadata body = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalPattern
      cases term with
      | lambda termBinder termBody =>
          have termBinderFacts : termBinder.isNone = true ∧
              Pattern.hasCanonicalBinderMetadata termBody = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using canonicalTerm
          have bodyFacts := matchPattern_closedSkeleton_eq bodyClosed
            binderFacts.2 termBinderFacts.2 bindings
            (by simpa [matchPattern] using member)
          refine ⟨?_, bodyFacts.2⟩
          rw [bodyFacts.1, Option.isNone_iff_eq_none.mp binderFacts.1,
            Option.isNone_iff_eq_none.mp termBinderFacts.1]
      | bvar termIndex => simp [matchPattern] at member
      | fvar termName => simp [matchPattern] at member
      | apply termConstructor termArguments => simp [matchPattern] at member
      | multiLambda arity binders body => simp [matchPattern] at member
      | subst body replacement => simp [matchPattern] at member
      | collection collectionType elements rest =>
          simp [matchPattern] at member
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternClosedSkeleton] using closed
      have binderFacts : binders.isEmpty = true ∧
          Pattern.hasCanonicalBinderMetadata body = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalPattern
      cases term with
      | multiLambda termArity termBinders termBody =>
          have termBinderFacts : termBinders.isEmpty = true ∧
              Pattern.hasCanonicalBinderMetadata termBody = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using canonicalTerm
          simp only [matchPattern] at member
          split at member
          case isTrue guard =>
              have arityEq : arity = termArity := by simpa using guard
              have bodyFacts := matchPattern_closedSkeleton_eq bodyClosed
                binderFacts.2 termBinderFacts.2 bindings member
              refine ⟨?_, bodyFacts.2⟩
              rw [bodyFacts.1, arityEq,
                List.isEmpty_iff.mp binderFacts.1,
                List.isEmpty_iff.mp termBinderFacts.1]
          case isFalse => simp at member
      | bvar termIndex => simp [matchPattern] at member
      | fvar termName => simp [matchPattern] at member
      | apply termConstructor termArguments => simp [matchPattern] at member
      | lambda termBinder termBody => simp [matchPattern] at member
      | subst body replacement => simp [matchPattern] at member
      | collection collectionType elements rest =>
          simp [matchPattern] at member
  | subst body replacement => simp [patternClosedSkeleton] at closed
  | collection collectionType elements rest =>
      simp [patternClosedSkeleton] at closed
termination_by sizeOf pattern

theorem matchArgs_closedSkeleton_eq {patterns terms : List Pattern}
    (closed : patternsClosedSkeleton patterns = true)
    (canonicalPatterns :
      Pattern.hasCanonicalBinderMetadataList patterns = true)
    (canonicalTerms : Pattern.hasCanonicalBinderMetadataList terms = true) :
    ∀ bindings ∈ matchArgs patterns terms,
      terms = patterns ∧ bindings = [] := by
  intro bindings member
  cases patterns with
  | nil =>
      cases terms with
      | nil => simpa [matchArgs] using member
      | cons termHead termTail => simp [matchArgs] at member
  | cons head tail =>
      cases terms with
      | nil => simp [matchArgs] at member
      | cons termHead termTail =>
          simp only [patternsClosedSkeleton, Bool.and_eq_true] at closed
          simp only [Pattern.hasCanonicalBinderMetadataList,
            Bool.and_eq_true] at canonicalPatterns canonicalTerms
          simp only [matchArgs, List.mem_flatMap, List.mem_filterMap]
            at member
          obtain ⟨headBindings, headMember, tailBindings, tailMember,
            mergeEq⟩ := member
          have headFacts := matchPattern_closedSkeleton_eq closed.1
            canonicalPatterns.1 canonicalTerms.1 headBindings headMember
          have tailFacts := matchArgs_closedSkeleton_eq closed.2
            canonicalPatterns.2 canonicalTerms.2 tailBindings tailMember
          rw [headFacts.2, tailFacts.2] at mergeEq
          have mergeEq' : some ([] : Bindings) = some bindings := mergeEq
          exact ⟨by rw [headFacts.1, tailFacts.1],
            (Option.some.inj mergeEq').symm⟩
termination_by sizeOf patterns

end

mutual

/-- Match soundness on hole skeletons: every produced binding list
reconstructs the term, binds exactly the pattern's occurrence names, and
carries checker-well-formed values. -/
theorem matchPattern_holeSkeleton_sound {pattern term : Pattern}
    (hole : patternHoleSkeleton pattern = true)
    (canonicalPattern : Pattern.hasCanonicalBinderMetadata pattern = true)
    (termGround : Pattern.isGroundAt 0 term = true)
    (termCanonical : Pattern.hasCanonicalBinderMetadata term = true) :
    ∀ bindings ∈ matchPattern pattern term,
      applyBindings bindings pattern = term ∧
      (∀ pair ∈ bindings, pair.1 ∈ patternOccurrenceNames pattern) ∧
      (∀ name ∈ patternOccurrenceNames pattern,
        (Bindings.lookup bindings name).isSome) ∧
      bindingsValuesWellFormed bindings := by
  intro bindings member
  cases pattern with
  | bvar index =>
      cases term with
      | bvar termIndex => simp [Pattern.isGroundAt] at termGround
      | fvar name => simp [matchPattern] at member
      | apply constructor arguments => simp [matchPattern] at member
      | lambda binder body => simp [matchPattern] at member
      | multiLambda arity binders body => simp [matchPattern] at member
      | subst body replacement => simp [matchPattern] at member
      | collection collectionType elements rest =>
          simp [matchPattern] at member
  | fvar name =>
      simp only [matchPattern, List.mem_singleton] at member
      subst member
      refine ⟨by simp [applyBindings_fvar, Bindings.lookup], ?_, ?_, ?_⟩
      · intro pair pairMember
        simp only [List.mem_singleton] at pairMember
        subst pairMember
        simp
      · intro occurrenceName occurrenceMember
        simp only [patternOccurrenceNames_fvar, List.mem_singleton]
          at occurrenceMember
        subst occurrenceMember
        simp [Bindings.lookup]
      · intro pair pairMember
        simp only [List.mem_singleton] at pairMember
        subst pairMember
        exact ⟨termGround, termCanonical⟩
  | apply constructor arguments =>
      have argumentsHole : patternsHoleSkeleton arguments = true := by
        simpa [patternHoleSkeleton] using hole
      have argumentsCanonical :
          Pattern.hasCanonicalBinderMetadataList arguments = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalPattern
      cases term with
      | apply termConstructor termArguments =>
          have termArgumentsGround :
              Pattern.isGroundListAt 0 termArguments = true := by
            simpa [Pattern.isGroundAt] using termGround
          have termArgumentsCanonical :
              Pattern.hasCanonicalBinderMetadataList termArguments =
                true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using termCanonical
          simp only [matchPattern] at member
          split at member
          case isTrue guard =>
              have guardFacts :
                  constructor = termConstructor ∧
                    arguments.length = termArguments.length := by
                simpa using guard
              have listFacts := matchArgs_holeSkeleton_sound argumentsHole
                argumentsCanonical termArgumentsGround
                termArgumentsCanonical bindings member
              refine ⟨?_, by simpa using listFacts.2.1,
                by simpa using listFacts.2.2.1, listFacts.2.2.2⟩
              simp [applyBindings, listFacts.1, guardFacts.1]
          case isFalse => simp at member
      | bvar termIndex => simp [matchPattern] at member
      | fvar termName => simp [matchPattern] at member
      | lambda binder body => simp [matchPattern] at member
      | multiLambda arity binders body => simp [matchPattern] at member
      | subst body replacement => simp [matchPattern] at member
      | collection collectionType elements rest =>
          simp [matchPattern] at member
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      have binderFacts : binder.isNone = true ∧
          Pattern.hasCanonicalBinderMetadata body = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalPattern
      cases term with
      | lambda termBinder termBody =>
          have termBinderFacts : termBinder.isNone = true ∧
              Pattern.hasCanonicalBinderMetadata termBody = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using termCanonical
          obtain ⟨bodyEq, bindingsNil⟩ := matchPattern_closedSkeleton_eq
            bodyClosed binderFacts.2 termBinderFacts.2 bindings
            (by simpa [matchPattern] using member)
          subst bindingsNil
          refine ⟨?_, by simp, ?_, ?_⟩
          · rw [applyBindings_closedSkeleton
              (by simpa [patternClosedSkeleton] using bodyClosed :
                patternClosedSkeleton (Pattern.lambda binder body) = true)]
            rw [bodyEq, Option.isNone_iff_eq_none.mp binderFacts.1,
              Option.isNone_iff_eq_none.mp termBinderFacts.1]
          · intro occurrenceName occurrenceMember
            rw [patternOccurrenceNames_closed
              (by simpa [patternClosedSkeleton] using bodyClosed)]
              at occurrenceMember
            cases occurrenceMember
          · intro pair pairMember
            cases pairMember
      | bvar termIndex => simp [matchPattern] at member
      | fvar termName => simp [matchPattern] at member
      | apply termConstructor termArguments => simp [matchPattern] at member
      | multiLambda arity binders body => simp [matchPattern] at member
      | subst body replacement => simp [matchPattern] at member
      | collection collectionType elements rest =>
          simp [matchPattern] at member
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      have binderFacts : binders.isEmpty = true ∧
          Pattern.hasCanonicalBinderMetadata body = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalPattern
      cases term with
      | multiLambda termArity termBinders termBody =>
          have termBinderFacts : termBinders.isEmpty = true ∧
              Pattern.hasCanonicalBinderMetadata termBody = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using termCanonical
          simp only [matchPattern] at member
          split at member
          case isTrue guard =>
              have arityEq : arity = termArity := by simpa using guard
              obtain ⟨bodyEq, bindingsNil⟩ := matchPattern_closedSkeleton_eq
                bodyClosed binderFacts.2 termBinderFacts.2 bindings member
              subst bindingsNil
              refine ⟨?_, by simp, ?_, ?_⟩
              · rw [applyBindings_closedSkeleton
                  (by simpa [patternClosedSkeleton] using bodyClosed :
                    patternClosedSkeleton
                      (Pattern.multiLambda arity binders body) = true)]
                rw [bodyEq, arityEq,
                  List.isEmpty_iff.mp binderFacts.1,
                  List.isEmpty_iff.mp termBinderFacts.1]
              · intro occurrenceName occurrenceMember
                rw [patternOccurrenceNames_closed
                  (by simpa [patternClosedSkeleton] using bodyClosed)]
                  at occurrenceMember
                cases occurrenceMember
              · intro pair pairMember
                cases pairMember
          case isFalse => simp at member
      | bvar termIndex => simp [matchPattern] at member
      | fvar termName => simp [matchPattern] at member
      | apply termConstructor termArguments => simp [matchPattern] at member
      | lambda termBinder termBody => simp [matchPattern] at member
      | subst body replacement => simp [matchPattern] at member
      | collection collectionType elements rest =>
          simp [matchPattern] at member
  | subst body replacement => simp [patternHoleSkeleton] at hole
  | collection collectionType elements rest =>
      simp [patternHoleSkeleton] at hole
termination_by sizeOf pattern

theorem matchArgs_holeSkeleton_sound {patterns terms : List Pattern}
    (holes : patternsHoleSkeleton patterns = true)
    (canonicalPatterns :
      Pattern.hasCanonicalBinderMetadataList patterns = true)
    (termsGround : Pattern.isGroundListAt 0 terms = true)
    (termsCanonical : Pattern.hasCanonicalBinderMetadataList terms = true) :
    ∀ bindings ∈ matchArgs patterns terms,
      patterns.map (applyBindings bindings) = terms ∧
      (∀ pair ∈ bindings, pair.1 ∈ patternsOccurrenceNames patterns) ∧
      (∀ name ∈ patternsOccurrenceNames patterns,
        (Bindings.lookup bindings name).isSome) ∧
      bindingsValuesWellFormed bindings := by
  intro bindings member
  cases patterns with
  | nil =>
      cases terms with
      | nil =>
          have bindingsNil : bindings = [] := by
            simpa [matchArgs] using member
          subst bindingsNil
          refine ⟨rfl, ?_, ?_, ?_⟩
          · intro pair pairMember; cases pairMember
          · intro name nameMember; simp at nameMember
          · intro pair pairMember; cases pairMember
      | cons termHead termTail => simp [matchArgs] at member
  | cons head tail =>
      cases terms with
      | nil => simp [matchArgs] at member
      | cons termHead termTail =>
          simp only [patternsHoleSkeleton, Bool.and_eq_true] at holes
          simp only [Pattern.hasCanonicalBinderMetadataList,
            Bool.and_eq_true] at canonicalPatterns termsCanonical
          simp only [Pattern.isGroundListAt, Bool.and_eq_true] at termsGround
          simp only [matchArgs, List.mem_flatMap, List.mem_filterMap]
            at member
          obtain ⟨headBindings, headMember, tailBindings, tailMember,
            mergeEq⟩ := member
          have headFacts := matchPattern_holeSkeleton_sound holes.1
            canonicalPatterns.1 termsGround.1 termsCanonical.1
            headBindings headMember
          have tailFacts := matchArgs_holeSkeleton_sound holes.2
            canonicalPatterns.2 termsGround.2 termsCanonical.2
            tailBindings tailMember
          have headAgree : ∀ name ∈ patternOccurrenceNames head,
              Bindings.lookup bindings name =
                Bindings.lookup headBindings name := by
            intro name nameMember
            obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
              (headFacts.2.2.1 name nameMember)
            rw [valueEq, mergeBindings_lookup_left mergeEq valueEq]
          have tailAgree : ∀ name ∈ patternsOccurrenceNames tail,
              Bindings.lookup bindings name =
                Bindings.lookup tailBindings name := by
            intro name nameMember
            obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
              (tailFacts.2.2.1 name nameMember)
            rw [valueEq, mergeBindings_lookup_right mergeEq (name, value)
              (bindings_mem_of_lookup valueEq)]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [List.map_cons]
            rw [applyBindings_agree holes.1 headAgree, headFacts.1,
              applyBindingsList_agree holes.2 tailAgree, tailFacts.1]
          · intro pair pairMember
            simp only [patternsOccurrenceNames_cons, List.mem_append]
            rcases mergeBindings_mem_source mergeEq pair pairMember with
              headPair | tailPair
            · exact Or.inl (headFacts.2.1 pair headPair)
            · exact Or.inr (tailFacts.2.1 pair tailPair)
          · intro name nameMember
            simp only [patternsOccurrenceNames_cons, List.mem_append]
              at nameMember
            rcases nameMember with headName | tailName
            · rw [headAgree name headName]
              exact headFacts.2.2.1 name headName
            · rw [tailAgree name tailName]
              exact tailFacts.2.2.1 name tailName
          · intro pair pairMember
            rcases mergeBindings_mem_source mergeEq pair pairMember with
              headPair | tailPair
            · exact headFacts.2.2.2 pair headPair
            · exact tailFacts.2.2.2 pair tailPair
termination_by sizeOf patterns

end

mutual

/-- Matching a hole skeleton against its own instance succeeds, with
bindings that agree with the instantiating assignment and cover the
pattern's occurrence names. -/
theorem matchPattern_own_instance {pattern : Pattern}
    (hole : patternHoleSkeleton pattern = true) {ambient : Bindings}
    (cover : ∀ name ∈ patternOccurrenceNames pattern,
      (Bindings.lookup ambient name).isSome) :
    ∃ bindings ∈ matchPattern pattern (applyBindings ambient pattern),
      bindingsAgreeWith ambient bindings ∧
      ∀ name ∈ patternOccurrenceNames pattern,
        (Bindings.lookup bindings name).isSome := by
  cases pattern with
  | bvar index =>
      refine ⟨[], by simp [applyBindings, matchPattern],
        bindingsAgreeWith_nil ambient, ?_⟩
      intro name nameMember
      simp at nameMember
  | fvar name =>
      obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
        (cover name (by simp))
      refine ⟨[(name, value)],
        by simp [applyBindings_fvar, valueEq, matchPattern], ?_, ?_⟩
      · intro pair pairMember
        simp only [List.mem_singleton] at pairMember
        subst pairMember
        exact valueEq
      · intro occurrenceName occurrenceMember
        simp only [patternOccurrenceNames_fvar, List.mem_singleton]
          at occurrenceMember
        subst occurrenceMember
        simp [Bindings.lookup]
  | apply constructor arguments =>
      have argumentsHole : patternsHoleSkeleton arguments = true := by
        simpa [patternHoleSkeleton] using hole
      obtain ⟨bindings, bindingsMember, agrees, bindingsCover⟩ :=
        matchArgs_own_instance argumentsHole (by simpa using cover)
      refine ⟨bindings, ?_, agrees, by simpa using bindingsCover⟩
      simpa [applyBindings, matchPattern] using bindingsMember
  | lambda binder body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      refine ⟨[], ?_, bindingsAgreeWith_nil ambient, ?_⟩
      · simp only [applyBindings, applyBindings_closedSkeleton bodyClosed]
        simpa [matchPattern] using matchPattern_closedSkeleton_self bodyClosed
      · intro name nameMember
        rw [patternOccurrenceNames_closed
          (by simpa [patternClosedSkeleton] using bodyClosed :
            patternClosedSkeleton (Pattern.lambda binder body) = true)]
          at nameMember
        cases nameMember
  | multiLambda arity binders body =>
      have bodyClosed : patternClosedSkeleton body = true := by
        simpa [patternHoleSkeleton] using hole
      refine ⟨[], ?_, bindingsAgreeWith_nil ambient, ?_⟩
      · simp only [applyBindings, applyBindings_closedSkeleton bodyClosed]
        simpa [matchPattern] using matchPattern_closedSkeleton_self bodyClosed
      · intro name nameMember
        rw [patternOccurrenceNames_closed
          (by simpa [patternClosedSkeleton] using bodyClosed :
            patternClosedSkeleton
              (Pattern.multiLambda arity binders body) = true)]
          at nameMember
        cases nameMember
  | subst body replacement => simp [patternHoleSkeleton] at hole
  | collection collectionType elements rest =>
      simp [patternHoleSkeleton] at hole
termination_by sizeOf pattern

theorem matchArgs_own_instance {patterns : List Pattern}
    (holes : patternsHoleSkeleton patterns = true) {ambient : Bindings}
    (cover : ∀ name ∈ patternsOccurrenceNames patterns,
      (Bindings.lookup ambient name).isSome) :
    ∃ bindings ∈ matchArgs patterns (patterns.map (applyBindings ambient)),
      bindingsAgreeWith ambient bindings ∧
      ∀ name ∈ patternsOccurrenceNames patterns,
        (Bindings.lookup bindings name).isSome := by
  cases patterns with
  | nil =>
      refine ⟨[], by simp [matchArgs], bindingsAgreeWith_nil ambient, ?_⟩
      intro name nameMember
      simp at nameMember
  | cons head tail =>
      simp only [patternsHoleSkeleton, Bool.and_eq_true] at holes
      simp only [patternsOccurrenceNames_cons, List.mem_append] at cover
      obtain ⟨headBindings, headMember, headAgrees, headCover⟩ :=
        matchPattern_own_instance holes.1
          (fun name member => cover name (Or.inl member))
      obtain ⟨tailBindings, tailMember, tailAgrees, tailCover⟩ :=
        matchArgs_own_instance holes.2
          (fun name member => cover name (Or.inr member))
      obtain ⟨merged, mergeEq, mergedAgrees⟩ :=
        mergeBindings_some_of_agree headAgrees tailAgrees
      refine ⟨merged, ?_, mergedAgrees, ?_⟩
      · simp only [List.map_cons, matchArgs, List.mem_flatMap,
          List.mem_filterMap]
        exact ⟨headBindings, headMember, tailBindings, tailMember, mergeEq⟩
      · intro name nameMember
        simp only [patternsOccurrenceNames_cons, List.mem_append]
          at nameMember
        rcases nameMember with headName | tailName
        · obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
            (headCover name headName)
          rw [mergeBindings_lookup_left mergeEq valueEq]
          rfl
        · obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
            (tailCover name tailName)
          rw [mergeBindings_lookup_right mergeEq (name, value)
            (bindings_mem_of_lookup valueEq)]
          rfl
termination_by sizeOf patterns

end

/-! ## Fuel monotonicity of the contextual step relation

`PremisesAt` threads one fuel index through a whole premise list, while
independent child steps arrive with their own fuel witnesses; raising every
witness to a common bound is what lets them share a rule application. -/

section FuelMonotonicity

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

private theorem stepAt_mono_bundle (base : BasePremiseEvaluator)
    (lang : LanguageDef) :
    ∀ fuel : Nat,
      (∀ {source target : Pattern},
        StepAt base lang fuel source target →
          StepAt base lang (fuel + 1) source target) ∧
      (∀ {bindings result : Bindings} {premise : Premise},
        PremiseAt base lang fuel bindings premise result →
          PremiseAt base lang (fuel + 1) bindings premise result) ∧
      (∀ {initial final : Bindings} {premises : List Premise},
        PremisesAt base lang fuel initial premises final →
          PremisesAt base lang (fuel + 1) initial premises final) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel inductionHypothesis =>
      have stepPart : ∀ {source target : Pattern},
          StepAt base lang fuel source target →
            StepAt base lang (fuel + 1) source target := by
        intro source target evidence
        cases evidence with
        | rule ruleMember matchMember premisesEvidence applyEq =>
            rename_i innerFuel rule initialBindings finalBindings
            exact .rule ruleMember matchMember
              ((inductionHypothesis innerFuel (by omega)).2.2
                premisesEvidence) applyEq
      have premisePart : ∀ {bindings result : Bindings} {premise : Premise},
          PremiseAt base lang fuel bindings premise result →
            PremiseAt base lang (fuel + 1) bindings premise result := by
        intro bindings result premise evidence
        cases evidence with
        | freshness baseEvidence => exact .freshness baseEvidence
        | relationQuery baseEvidence => exact .relationQuery baseEvidence
        | forAll baseEvidence => exact .forAll baseEvidence
        | congruence stepEvidence matchEvidence mergeEvidence =>
            exact .congruence (stepPart stepEvidence) matchEvidence
              mergeEvidence
      refine ⟨stepPart, premisePart, ?_⟩
      intro initial final premises evidence
      induction premises generalizing initial with
      | nil =>
          cases evidence with
          | nil => exact .nil _
      | cons premise rest listHypothesis =>
          cases evidence with
          | cons premiseEvidence restEvidence =>
              exact .cons (premisePart premiseEvidence)
                (listHypothesis restEvidence)

/-- One authored step at a bounded contextual depth remains valid at every
larger depth. -/
theorem stepAt_mono {base : BasePremiseEvaluator} {lang : LanguageDef}
    {fuel fuel' : Nat} (le : fuel ≤ fuel') {source target : Pattern}
    (evidence : StepAt base lang fuel source target) :
    StepAt base lang fuel' source target := by
  induction le with
  | refl => exact evidence
  | step _ ih => exact (stepAt_mono_bundle base lang _).1 ih

/-- Premise-chain evidence at a bounded contextual depth remains valid at
every larger depth. -/
theorem premisesAt_mono {base : BasePremiseEvaluator} {lang : LanguageDef}
    {fuel fuel' : Nat} (le : fuel ≤ fuel') {initial final : Bindings}
    {premises : List Premise}
    (evidence : PremisesAt base lang fuel initial premises final) :
    PremisesAt base lang fuel' initial premises final := by
  induction le with
  | refl => exact evidence
  | step _ ih => exact (stepAt_mono_bundle base lang _).2.2 ih

end FuelMonotonicity

/-! ## The generated presentation: shapes, lookups, and coverage -/

section GeneralAdequacy

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- The checker's argument discipline: top-level closed executable data with
canonical binder metadata. -/
def wellFormedTerm (term : Pattern) : Prop :=
  Pattern.isGroundAt 0 term = true ∧
    Pattern.hasCanonicalBinderMetadata term = true

/-- The generated one-step judgment. -/
def stepJudgment (stepSource stepTarget : Pattern) : Pattern :=
  .apply "Step" [stepSource, stepTarget]

/-- The generated trace judgment. -/
def stepsJudgment (stepSource stepTarget : Pattern) : Pattern :=
  .apply "Steps" [stepSource, stepTarget]

/-! ### Moded-chain inversion and monotonicity -/

theorem tracePremisesModed_cons_inversion {bound final : List String}
    {sourcePattern targetPattern : Pattern} {rest : List Premise}
    (chain : tracePremisesModed bound
      (.congruence sourcePattern targetPattern :: rest) = some final) :
    patternHoleSkeleton sourcePattern = true ∧
      patternHoleSkeleton targetPattern = true ∧
      (patternOccurrenceNames sourcePattern).all bound.contains = true ∧
      tracePremisesModed (bound ++ patternOccurrenceNames targetPattern)
        rest = some final := by
  simp only [tracePremisesModed] at chain
  split at chain
  case isTrue guard =>
      simp only [Bool.and_eq_true] at guard
      exact ⟨guard.1.1, guard.1.2, guard.2, chain⟩
  case isFalse => cases chain

theorem tracePremisesModed_extends :
    ∀ {premises : List Premise} {bound final : List String},
      tracePremisesModed bound premises = some final →
      ∀ name ∈ bound, name ∈ final := by
  intro premises
  induction premises with
  | nil =>
      intro bound final chain name member
      have chainEq : some bound = some final := chain
      rw [← Option.some.inj chainEq]
      exact member
  | cons head tail inductionHypothesis =>
      intro bound final chain name member
      cases head with
      | congruence sourcePattern targetPattern =>
          obtain ⟨-, -, -, rest⟩ := tracePremisesModed_cons_inversion chain
          exact inductionHypothesis rest name (List.mem_append_left _ member)
      | freshness condition => simp [tracePremisesModed] at chain
      | relationQuery relation arguments => simp [tracePremisesModed] at chain
      | forAll collection parameter body => simp [tracePremisesModed] at chain

/-! ### Adequate-rule accessors -/

theorem rewriteDirectTraceAdequate_left {rule : RewriteRule}
    (adequate : rewriteDirectTraceAdequate rule = true) :
    patternHoleSkeleton rule.left = true := by
  simp only [rewriteDirectTraceAdequate, Bool.and_eq_true] at adequate
  exact adequate.1.1

theorem rewriteDirectTraceAdequate_right {rule : RewriteRule}
    (adequate : rewriteDirectTraceAdequate rule = true) :
    patternHoleSkeleton rule.right = true := by
  simp only [rewriteDirectTraceAdequate, Bool.and_eq_true] at adequate
  exact adequate.1.2

theorem rewriteDirectTraceAdequate_chain {rule : RewriteRule}
    (adequate : rewriteDirectTraceAdequate rule = true) :
    ∃ bound, tracePremisesModed (patternOccurrenceNames rule.left)
        rule.premises = some bound ∧
      (patternOccurrenceNames rule.right).all bound.contains = true := by
  simp only [rewriteDirectTraceAdequate, Bool.and_eq_true] at adequate
  rcases chainResult : tracePremisesModed (patternOccurrenceNames rule.left)
      rule.premises with _ | bound
  · rw [chainResult] at adequate
    cases adequate.2
  · rw [chainResult] at adequate
    exact ⟨bound, rfl, adequate.2⟩

/-! ### Generated-schema shapes -/

@[simp] theorem rewriteStepRule_id (rule : RewriteRule) :
    (rewriteStepRule rule).id = ⟨"step-rewrite-" ++ rule.name⟩ := rfl

@[simp] theorem rewriteStepRule_metavariables (rule : RewriteRule) :
    (rewriteStepRule rule).metavariables =
      rule.typeContext.map (fun binding => (binding.1, 0)) := rfl

@[simp] theorem rewriteStepRule_premises (rule : RewriteRule) :
    (rewriteStepRule rule).premises =
      rewritePremiseJudgments rule.premises := rfl

@[simp] theorem rewriteStepRule_conclusion (rule : RewriteRule) :
    (rewriteStepRule rule).conclusion =
      stepJudgment rule.left rule.right := rfl

@[simp] theorem rewriteStepRule_sideConditions (rule : RewriteRule) :
    (rewriteStepRule rule).sideConditions = [] := rfl

theorem rewriteStepRule_formals_zero (rule : RewriteRule) :
    ∀ formal ∈ (rewriteStepRule rule).metavariables, formal.2 = 0 := by
  intro formal member
  simp only [rewriteStepRule_metavariables] at member
  obtain ⟨binding, -, bindingEq⟩ := List.mem_map.mp member
  rw [← bindingEq]

@[simp] theorem rewriteStepRule_formal_names (rule : RewriteRule) :
    (rewriteStepRule rule).metavariables.map Prod.fst =
      rule.typeContext.map Prod.fst := by
  simp [rewriteStepRule_metavariables, List.map_map, Function.comp_def]

@[simp] theorem rewritePremiseJudgments_congruence_cons
    (sourcePattern targetPattern : Pattern) (rest : List Premise) :
    rewritePremiseJudgments (.congruence sourcePattern targetPattern :: rest) =
      stepJudgment sourcePattern targetPattern ::
        rewritePremiseJudgments rest := rfl

/-! ### Occurrence coverage from schema validity -/

private theorem mem_patternsOccurrences_of_mem {patterns : List Pattern}
    {pattern : Pattern} (member : pattern ∈ patterns)
    {occurrence : String × Nat}
    (occMember : occurrence ∈ patternMetavariableOccurrencesAt 0 pattern) :
    occurrence ∈ patternsMetavariableOccurrencesAt 0 patterns := by
  induction patterns with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · simp only [patternsMetavariableOccurrencesAt, List.mem_append]
        exact Or.inl occMember
      · simp only [patternsMetavariableOccurrencesAt, List.mem_append]
        exact Or.inr (inductionHypothesis tailMember)

/-- Every occurrence name of a schema pattern of a V1-valid rule is a
declared formal name. -/
theorem isValidV1_occurrence_names_subset {rule : RuleSchema}
    (ruleValid : RuleSchema.isValidV1 rule = true) {pattern : Pattern}
    (patternMember : pattern ∈ RuleSchema.patterns rule)
    {name : String} (nameMember : name ∈ patternOccurrenceNames pattern) :
    name ∈ rule.metavariables.map Prod.fst := by
  obtain ⟨occurrence, occMember, nameEq⟩ := List.mem_map.mp nameMember
  have inRule : occurrence ∈ RuleSchema.occurrences rule :=
    mem_patternsOccurrences_of_mem patternMember occMember
  unfold RuleSchema.isValidV1 at ruleValid
  simp only [Bool.and_eq_true] at ruleValid
  have contained := List.all_eq_true.mp ruleValid.1.1.1.1.2 occurrence inRule
  have memberMeta : occurrence ∈ rule.metavariables := by
    simpa using contained
  exact List.mem_map.mpr ⟨occurrence, memberMeta, nameEq⟩

/-- Every declared formal name of a V1-valid rule occurs in some schema
pattern. -/
theorem isValidV1_formal_names_occur {rule : RuleSchema}
    (ruleValid : RuleSchema.isValidV1 rule = true) {name : String}
    (nameMember : name ∈ rule.metavariables.map Prod.fst) :
    ∃ pattern ∈ RuleSchema.patterns rule,
      name ∈ patternOccurrenceNames pattern := by
  obtain ⟨formal, formalMember, nameEq⟩ := List.mem_map.mp nameMember
  unfold RuleSchema.isValidV1 at ruleValid
  simp only [Bool.and_eq_true] at ruleValid
  have contained := List.all_eq_true.mp ruleValid.1.1.1.2 formal formalMember
  have occMember : formal ∈ RuleSchema.occurrences rule := by
    simpa using contained
  unfold RuleSchema.occurrences at occMember
  clear contained
  generalize RuleSchema.patterns rule = patterns at occMember ⊢
  induction patterns with
  | nil => simp [patternsMetavariableOccurrencesAt] at occMember
  | cons head tail inductionHypothesis =>
      simp only [patternsMetavariableOccurrencesAt, List.mem_append]
        at occMember
      rcases occMember with headOcc | tailOcc
      · exact ⟨head, List.mem_cons_self .., List.mem_map.mpr
          ⟨formal, headOcc, nameEq⟩⟩
      · obtain ⟨pattern, patternMember, patternName⟩ :=
          inductionHypothesis tailOcc
        exact ⟨pattern, List.mem_cons_of_mem _ patternMember, patternName⟩

/-! ### Positional coverage of zipped arguments -/

theorem argumentsValidAt_length :
    ∀ {formals : List (String × Nat)} {arguments : List Pattern},
      argumentsValidAt formals arguments = true →
      formals.length = arguments.length := by
  intro formals
  induction formals with
  | nil =>
      intro arguments valid
      cases arguments with
      | nil => rfl
      | cons argument args => simp [argumentsValidAt] at valid
  | cons formal rest inductionHypothesis =>
      intro arguments valid
      cases arguments with
      | nil => simp [argumentsValidAt] at valid
      | cons argument args =>
          rcases formal with ⟨formalName, formalDepth⟩
          simp only [argumentsValidAt, Bool.and_eq_true] at valid
          simpa using inductionHypothesis valid.2

theorem zipBindings_covers :
    ∀ {formals : List (String × Nat)} {arguments : List Pattern},
      formals.length = arguments.length →
      ∀ name ∈ formals.map Prod.fst,
        (Bindings.lookup (zipBindings formals arguments) name).isSome := by
  intro formals
  induction formals with
  | nil =>
      intro arguments _ name nameMember
      simp at nameMember
  | cons formal rest inductionHypothesis =>
      intro arguments lengthEq name nameMember
      cases arguments with
      | nil => simp at lengthEq
      | cons argument args =>
          rcases formal with ⟨formalName, formalDepth⟩
          simp only [zipBindings]
          by_cases headName : formalName = name
          · subst headName
            unfold Bindings.lookup
            rw [List.find?_cons_of_pos (by simp)]
            rfl
          · have restMember : name ∈ rest.map Prod.fst := by
              simp only [List.map_cons, List.mem_cons] at nameMember
              rcases nameMember with headEq | restMember
              · exact absurd headEq.symm headName
              · exact restMember
            unfold Bindings.lookup
            rw [List.find?_cons_of_neg (by simpa using headName)]
            exact inductionHypothesis (by simpa using lengthEq) name restMember

theorem argumentsValidAt_zip_values :
    ∀ {formals : List (String × Nat)} {arguments : List Pattern},
      (∀ formal ∈ formals, formal.2 = 0) →
      argumentsValidAt formals arguments = true →
      bindingsValuesWellFormed (zipBindings formals arguments) := by
  intro formals
  induction formals with
  | nil =>
      intro arguments _ _ pair pairMember
      cases arguments with
      | nil => cases pairMember
      | cons argument args => cases pairMember
  | cons formal rest inductionHypothesis =>
      intro arguments allZero valid pair pairMember
      cases arguments with
      | nil => simp [argumentsValidAt] at valid
      | cons argument args =>
          rcases formal with ⟨formalName, formalDepth⟩
          have formalDepthZero : formalDepth = 0 :=
            allZero (formalName, formalDepth) (List.mem_cons_self ..)
          subst formalDepthZero
          simp only [argumentsValidAt, argumentValidAt, Bool.and_eq_true]
            at valid
          simp only [zipBindings] at pairMember
          rcases List.mem_cons.mp pairMember with rfl | restPair
          · exact ⟨valid.1.1, valid.1.2⟩
          · exact inductionHypothesis
              (fun formal member => allZero formal
                (List.mem_cons_of_mem _ member))
              valid.2 pair restPair

/-! ### Rule lookup in the generated table -/

private theorem stepRewriteName_inj {left right : String}
    (eq : ("step-rewrite-" ++ left : String) = "step-rewrite-" ++ right) :
    left = right := by
  have listEq : ("step-rewrite-" ++ left).toList =
      ("step-rewrite-" ++ right).toList := by rw [eq]
  simp only [String.toList_append] at listEq
  exact String.ext (List.append_cancel_left listEq)

private theorem find?_mapped_rewrite {rewrites : List RewriteRule}
    (nodupNames : (rewrites.map RewriteRule.name).Nodup)
    {rewrite : RewriteRule} (member : rewrite ∈ rewrites) :
    (rewrites.map rewriteStepRule).find?
        (fun candidate =>
          decide (candidate.id = (rewriteStepRule rewrite).id)) =
      some (rewriteStepRule rewrite) := by
  induction rewrites with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at nodupNames
      rcases List.mem_cons.mp member with rfl | tailMember
      · rw [List.map_cons, List.find?_cons_of_pos (by simp)]
      · rw [List.map_cons, List.find?_cons_of_neg ?head]
        · exact inductionHypothesis nodupNames.2 tailMember
        case head =>
          simp only [decide_eq_true_eq, rewriteStepRule_id, RuleId.mk.injEq]
          intro idEq
          have nameEq : head.name = rewrite.name := stepRewriteName_inj idEq
          exact nodupNames.1
            (nameEq ▸ List.mem_map_of_mem tailMember)

/-- Looking up an adequate rewrite's generated identifier yields exactly its
generated schema. -/
theorem generated_lookup_rewrite (source : DirectTraceLanguage)
    (nodupNames : (source.language.rewrites.map RewriteRule.name).Nodup)
    {rewrite : RewriteRule} (member : rewrite ∈ source.language.rewrites) :
    (stepPresentation source).lookupRule? (rewriteStepRule rewrite).id =
      some (rewriteStepRule rewrite) := by
  show (source.language.rewrites.map rewriteStepRule ++
      [stepReflRule, stepTransRule]).find? _ = _
  rw [List.find?_append, find?_mapped_rewrite nodupNames member]
  rfl

private theorem length_step_rewrite_id (name : String) :
    (("step-rewrite-" ++ name : String)).length = 13 + name.length := by
  have prefixLength : ("step-rewrite-" : String).length = 13 := rfl
  simp [String.length_append, prefixLength]

private theorem mapped_find?_fixed_none (source : DirectTraceLanguage)
    {fixedId : RuleId} (shortLength : fixedId.value.length < 13) :
    (source.language.rewrites.map rewriteStepRule).find?
        (fun candidate => decide (candidate.id = fixedId)) = none := by
  apply List.find?_eq_none.mpr
  intro candidate candidateMember
  obtain ⟨rewrite, -, candidateEq⟩ := List.mem_map.mp candidateMember
  subst candidateEq
  simp only [decide_eq_true_eq, rewriteStepRule_id]
  intro idEq
  have valueEq : ("step-rewrite-" ++ rewrite.name : String) =
      fixedId.value := congrArg RuleId.value idEq
  have lengthEq := congrArg String.length valueEq
  rw [length_step_rewrite_id] at lengthEq
  omega

/-- Looking up the reflexivity identifier yields the reflexivity schema. -/
theorem generated_lookup_refl (source : DirectTraceLanguage) :
    (stepPresentation source).lookupRule? ⟨"steps-refl"⟩ =
      some stepReflRule := by
  show (source.language.rewrites.map rewriteStepRule ++
      [stepReflRule, stepTransRule]).find? _ = _
  rw [List.find?_append,
    mapped_find?_fixed_none source (fixedId := ⟨"steps-refl"⟩)
      (by decide), Option.none_or]
  rw [List.find?_cons_of_pos (by simp [stepReflRule])]

/-- Looking up the transitivity identifier yields the transitivity schema. -/
theorem generated_lookup_trans (source : DirectTraceLanguage) :
    (stepPresentation source).lookupRule? ⟨"steps-trans"⟩ =
      some stepTransRule := by
  show (source.language.rewrites.map rewriteStepRule ++
      [stepReflRule, stepTransRule]).find? _ = _
  rw [List.find?_append,
    mapped_find?_fixed_none source (fixedId := ⟨"steps-trans"⟩)
      (by decide), Option.none_or]
  rw [List.find?_cons_of_neg (by decide),
    List.find?_cons_of_pos (by simp [stepTransRule])]

/-- Every admitted rule of the generated table is a generated rewrite schema
or one of the two trace schemas. -/
theorem generated_lookup_inversion (source : DirectTraceLanguage)
    {ruleId : RuleId} {rule : RuleSchema}
    (lookup : (stepPresentation source).lookupRule? ruleId = some rule) :
    (∃ rewrite ∈ source.language.rewrites, rule = rewriteStepRule rewrite) ∨
      rule = stepReflRule ∨ rule = stepTransRule := by
  have member : rule ∈ (stepPresentation source).rules :=
    List.mem_of_find?_eq_some lookup
  have memberSplit : rule ∈ source.language.rewrites.map rewriteStepRule ∨
      rule ∈ [stepReflRule, stepTransRule] := List.mem_append.mp member
  rcases memberSplit with mapped | fixed
  · obtain ⟨rewrite, rewriteMember, ruleEq⟩ := List.mem_map.mp mapped
    exact Or.inl ⟨rewrite, rewriteMember, ruleEq.symm⟩
  · rcases List.mem_cons.mp fixed with reflEq | transMember
    · exact Or.inr (Or.inl reflEq)
    · rcases List.mem_cons.mp transMember with transEq | empty
      · exact Or.inr (Or.inr transEq)
      · cases empty

/-! ### Judgment decompositions and premise-judgment facts -/

@[simp] theorem patternHoleSkeleton_stepJudgment
    (stepSource stepTarget : Pattern) :
    patternHoleSkeleton (stepJudgment stepSource stepTarget) =
      (patternHoleSkeleton stepSource && patternHoleSkeleton stepTarget) := by
  simp [stepJudgment, patternHoleSkeleton, patternsHoleSkeleton]

@[simp] theorem patternOccurrenceNames_stepJudgment
    (stepSource stepTarget : Pattern) :
    patternOccurrenceNames (stepJudgment stepSource stepTarget) =
      patternOccurrenceNames stepSource ++
        patternOccurrenceNames stepTarget := by
  simp [stepJudgment]

@[simp] theorem applyBindings_stepJudgment (bindings : Bindings)
    (stepSource stepTarget : Pattern) :
    applyBindings bindings (stepJudgment stepSource stepTarget) =
      stepJudgment (applyBindings bindings stepSource)
        (applyBindings bindings stepTarget) := by
  simp [stepJudgment, applyBindings]

@[simp] theorem applyBindings_stepsJudgment (bindings : Bindings)
    (stepSource stepTarget : Pattern) :
    applyBindings bindings (stepsJudgment stepSource stepTarget) =
      stepsJudgment (applyBindings bindings stepSource)
        (applyBindings bindings stepTarget) := by
  simp [stepsJudgment, applyBindings]

theorem stepJudgment_inj {leftSource leftTarget rightSource rightTarget :
    Pattern}
    (eq : stepJudgment leftSource leftTarget =
      stepJudgment rightSource rightTarget) :
    leftSource = rightSource ∧ leftTarget = rightTarget := by
  simpa [stepJudgment] using eq

theorem stepsJudgment_inj {leftSource leftTarget rightSource rightTarget :
    Pattern}
    (eq : stepsJudgment leftSource leftTarget =
      stepsJudgment rightSource rightTarget) :
    leftSource = rightSource ∧ leftTarget = rightTarget := by
  simpa [stepsJudgment] using eq

theorem stepJudgment_ne_stepsJudgment (a b c d : Pattern) :
    stepJudgment a b ≠ stepsJudgment c d := by
  simp [stepJudgment, stepsJudgment]

/-- Every generated premise judgment of a moded chain is a hole skeleton. -/
theorem rewritePremiseJudgments_hole :
    ∀ {premises : List Premise} {boundNames finalNames : List String},
      tracePremisesModed boundNames premises = some finalNames →
      patternsHoleSkeleton (rewritePremiseJudgments premises) = true := by
  intro premises
  induction premises with
  | nil =>
      intro boundNames finalNames _
      simp [rewritePremiseJudgments, patternsHoleSkeleton]
  | cons head tail inductionHypothesis =>
      intro boundNames finalNames chain
      cases head with
      | congruence sourcePattern targetPattern =>
          obtain ⟨sourceHole, targetHole, -, rest⟩ :=
            tracePremisesModed_cons_inversion chain
          simp [rewritePremiseJudgments_congruence_cons, patternsHoleSkeleton,
            sourceHole, targetHole, inductionHypothesis rest]
      | freshness condition => simp [tracePremisesModed] at chain
      | relationQuery relation arguments => simp [tracePremisesModed] at chain
      | forAll collection parameter body => simp [tracePremisesModed] at chain

/-- Every generated premise judgment arises from a congruence premise. -/
theorem mem_rewritePremiseJudgments {premises : List Premise}
    {pattern : Pattern}
    (member : pattern ∈ rewritePremiseJudgments premises) :
    ∃ sourcePattern targetPattern,
      Premise.congruence sourcePattern targetPattern ∈ premises ∧
        pattern = stepJudgment sourcePattern targetPattern := by
  induction premises with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      cases head with
      | congruence sourcePattern targetPattern =>
          rcases List.mem_cons.mp
              (by simpa [rewritePremiseJudgments_congruence_cons]
                using member) with headEq | tailMember
          · exact ⟨sourcePattern, targetPattern, List.mem_cons_self .., headEq⟩
          · obtain ⟨s, t, premiseMember, patternEq⟩ :=
              inductionHypothesis tailMember
            exact ⟨s, t, List.mem_cons_of_mem _ premiseMember, patternEq⟩
      | freshness condition =>
          obtain ⟨s, t, premiseMember, patternEq⟩ :=
            inductionHypothesis (by simpa [rewritePremiseJudgments]
              using member)
          exact ⟨s, t, List.mem_cons_of_mem _ premiseMember, patternEq⟩
      | relationQuery relation arguments =>
          obtain ⟨s, t, premiseMember, patternEq⟩ :=
            inductionHypothesis (by simpa [rewritePremiseJudgments]
              using member)
          exact ⟨s, t, List.mem_cons_of_mem _ premiseMember, patternEq⟩
      | forAll collection parameter body =>
          obtain ⟨s, t, premiseMember, patternEq⟩ :=
            inductionHypothesis (by simpa [rewritePremiseJudgments]
              using member)
          exact ⟨s, t, List.mem_cons_of_mem _ premiseMember, patternEq⟩

/-- Occurrence names across a pattern list are the occurrence names of its
members. -/
theorem mem_patternsOccurrenceNames {patterns : List Pattern}
    {name : String} :
    name ∈ patternsOccurrenceNames patterns ↔
      ∃ pattern ∈ patterns, name ∈ patternOccurrenceNames pattern := by
  induction patterns with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp [patternsOccurrenceNames_cons, inductionHypothesis,
        List.mem_cons]

/-! ### Per-pattern facts from schema validity -/

theorem isValidV1_pattern_wellScoped {rule : RuleSchema}
    (ruleValid : RuleSchema.isValidV1 rule = true) {pattern : Pattern}
    (patternMember : pattern ∈ RuleSchema.patterns rule) :
    Pattern.isWellScoped pattern = true := by
  unfold RuleSchema.isValidV1 at ruleValid
  simp only [Bool.and_eq_true] at ruleValid
  exact List.all_eq_true.mp ruleValid.1.1.2 pattern patternMember

theorem isValidV1_pattern_canonical {rule : RuleSchema}
    (ruleValid : RuleSchema.isValidV1 rule = true) {pattern : Pattern}
    (patternMember : pattern ∈ RuleSchema.patterns rule) :
    Pattern.hasCanonicalBinderMetadata pattern = true := by
  unfold RuleSchema.isValidV1 at ruleValid
  simp only [Bool.and_eq_true] at ruleValid
  exact List.all_eq_true.mp ruleValid.2 pattern patternMember

theorem generated_conclusion_mem_patterns (rule : RewriteRule) :
    stepJudgment rule.left rule.right ∈
      RuleSchema.patterns (rewriteStepRule rule) := by
  unfold RuleSchema.patterns
  exact List.mem_append_right _ (List.mem_cons_self ..)

theorem generated_premise_mem_patterns {rule : RewriteRule} {pattern : Pattern}
    (member : pattern ∈ rewritePremiseJudgments rule.premises) :
    pattern ∈ RuleSchema.patterns (rewriteStepRule rule) := by
  unfold RuleSchema.patterns
  exact List.mem_append_left _ member

/-! ### Argument-shape inversions for the fixed trace schemas -/

theorem argumentsValidAt_one_inversion {name : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt [(name, 0)] arguments = true) :
    ∃ argument, arguments = [argument] ∧ wellFormedTerm argument := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons argument rest =>
      cases rest with
      | nil =>
          simp only [argumentsValidAt, argumentValidAt, Bool.and_eq_true]
            at valid
          exact ⟨argument, rfl, valid.1.1, valid.1.2⟩
      | cons second rest => simp [argumentsValidAt] at valid

theorem argumentsValidAt_three_inversion
    {firstName secondName thirdName : String} {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0)] arguments = true) :
    ∃ first second third, arguments = [first, second, third] ∧
      wellFormedTerm first ∧ wellFormedTerm second ∧ wellFormedTerm third := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil =>
                  simp only [argumentsValidAt, argumentValidAt,
                    Bool.and_eq_true] at valid
                  exact ⟨first, second, third, rfl,
                    ⟨valid.1.1, valid.1.2⟩, ⟨valid.2.1.1, valid.2.1.2⟩,
                    valid.2.2.1.1, valid.2.2.1.2⟩
              | cons fourth rest => simp [argumentsValidAt] at valid

/-! ### The validated generated presentation -/

/-- The generated presentation together with its admission evidence. -/
def generatedValidated (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true) :
    ValidatedPresentation :=
  ⟨stepPresentation source, valid⟩

@[simp] theorem generatedValidated_fst (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true) :
    (generatedValidated source valid).1 = stepPresentation source := rfl

/-- V1 validity of a generated rewrite schema, extracted from generated
presentation admission. -/
theorem generated_rule_isValidV1 (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true)
    {rewrite : RewriteRule}
    (rewriteMember : rewrite ∈ source.language.rewrites) :
    RuleSchema.isValidV1 (rewriteStepRule rewrite) = true :=
  rule_isValidV1_of_isValidV2 valid
    (List.mem_append_left _ (List.mem_map_of_mem rewriteMember))

theorem rewritePremiseJudgments_mem_of_congruence :
    ∀ {premises : List Premise} {sourcePattern targetPattern : Pattern},
      Premise.congruence sourcePattern targetPattern ∈ premises →
      stepJudgment sourcePattern targetPattern ∈
        rewritePremiseJudgments premises := by
  intro premises
  induction premises with
  | nil => intro _ _ member; cases member
  | cons head tail inductionHypothesis =>
      intro sourcePattern targetPattern member
      rcases List.mem_cons.mp member with headEq | tailMember
      · rw [← headEq, rewritePremiseJudgments_congruence_cons]
        exact List.mem_cons_self ..
      · cases head with
        | congruence s t =>
            rw [rewritePremiseJudgments_congruence_cons]
            exact List.mem_cons_of_mem _ (inductionHypothesis tailMember)
        | freshness condition =>
            simpa [rewritePremiseJudgments] using
              inductionHypothesis tailMember
        | relationQuery relation arguments =>
            simpa [rewritePremiseJudgments] using
              inductionHypothesis tailMember
        | forAll collection parameter body =>
            simpa [rewritePremiseJudgments] using
              inductionHypothesis tailMember

/-- The zipped positional assignment covers every occurrence name of every
schema pattern of the generated rule. -/
theorem generated_zip_cover (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true)
    {rewrite : RewriteRule}
    (rewriteMember : rewrite ∈ source.language.rewrites)
    {arguments : List Pattern}
    (argumentsValid : argumentsValidAt
      (rewriteStepRule rewrite).metavariables arguments = true)
    {pattern : Pattern}
    (patternMember : pattern ∈ RuleSchema.patterns (rewriteStepRule rewrite)) :
    ∀ name ∈ patternOccurrenceNames pattern,
      (Bindings.lookup
        (zipBindings (rewriteStepRule rewrite).metavariables arguments)
        name).isSome := by
  intro name nameMember
  exact zipBindings_covers (argumentsValidAt_length argumentsValid) name
    (isValidV1_occurrence_names_subset
      (generated_rule_isValidV1 source valid rewriteMember)
      patternMember nameMember)

/-- Instantiating a generated rewrite schema at valid arguments is exactly
binding application with the positional assignment, on premises and
conclusion alike. -/
theorem generated_rewrite_instantiation (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true)
    (nodupNames : (source.language.rewrites.map RewriteRule.name).Nodup)
    {rewrite : RewriteRule}
    (rewriteMember : rewrite ∈ source.language.rewrites)
    (ruleAdequate : rewriteDirectTraceAdequate rewrite = true)
    {arguments : List Pattern}
    (argumentsValid : argumentsValidAt
      (rewriteStepRule rewrite).metavariables arguments = true) :
    instantiateRule? (generatedValidated source valid)
        ⟨(rewriteStepRule rewrite).id, arguments⟩ =
      some ((rewritePremiseJudgments rewrite.premises).map
          (applyBindings
            (zipBindings (rewriteStepRule rewrite).metavariables arguments)),
        stepJudgment
          (applyBindings
            (zipBindings (rewriteStepRule rewrite).metavariables arguments)
            rewrite.left)
          (applyBindings
            (zipBindings (rewriteStepRule rewrite).metavariables arguments)
            rewrite.right)) := by
  obtain ⟨chainBound, chain, -⟩ := rewriteDirectTraceAdequate_chain ruleAdequate
  have premisesAligned := instantiateSchemasAt?_eq_applyBindings
    (rewritePremiseJudgments_hole chain)
    (rewriteStepRule_formals_zero rewrite)
    (fun name nameMember => by
      obtain ⟨pattern, patternMember, patternName⟩ :=
        mem_patternsOccurrenceNames.mp nameMember
      exact generated_zip_cover source valid rewriteMember argumentsValid
        (generated_premise_mem_patterns patternMember) name patternName)
  have conclusionHole :
      patternHoleSkeleton (stepJudgment rewrite.left rewrite.right) = true := by
    simp [rewriteDirectTraceAdequate_left ruleAdequate,
      rewriteDirectTraceAdequate_right ruleAdequate]
  have conclusionAligned := instantiateSchemaAt?_eq_applyBindings
    conclusionHole (rewriteStepRule_formals_zero rewrite)
    (generated_zip_cover source valid rewriteMember argumentsValid
      (generated_conclusion_mem_patterns rewrite))
  have sideConditionsTrue := RuleSchema.sideConditionsHold_of_empty
    (rewriteStepRule rewrite) arguments (rewriteStepRule_sideConditions rewrite)
  simp only [instantiateRule?, generatedValidated_fst]
  rw [generated_lookup_rewrite source nodupNames rewriteMember]
  simp only [argumentsValid, if_true, sideConditionsTrue,
    instantiateSchemas?, instantiateSchema?, rewriteStepRule_premises,
    rewriteStepRule_conclusion, premisesAligned, conclusionAligned,
    option_some_bind, applyBindings_stepJudgment]

/-! ### Derivation heights -/

mutual

/-- Height of a checked derivation. -/
def derivationHeight {presentation : ValidatedPresentation} :
    {goal : Pattern} → Derivation presentation goal → Nat
  | _, .byRule _ _ children => derivationListHeight children + 1

/-- Combined height of ordered child derivations. -/
def derivationListHeight {presentation : ValidatedPresentation} :
    {goals : List Pattern} → DerivationList presentation goals → Nat
  | _, .nil => 0
  | _, .cons head tail => derivationHeight head + derivationListHeight tail

end

/-! ### Soundness: checked trace derivations are declarative reductions -/

/-- The two claims proved of every checked goal of the generated
presentation. -/
private def generalSoundClaim (source : DirectTraceLanguage)
    (goal : Pattern) : Prop :=
  (∀ stepSource stepTarget, goal = stepJudgment stepSource stepTarget →
    langReduces source.language stepSource stepTarget) ∧
  (∀ stepSource stepTarget, goal = stepsJudgment stepSource stepTarget →
    Relation.ReflTransGen (langReduces source.language) stepSource stepTarget)

/-- Declarative premise evidence built from checked child certificates,
walking the moded congruence chain. -/
private theorem sound_premise_chain (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true)
    {σ : Bindings} {heightBound : Nat}
    (childSound : ∀ {goal : Pattern}
      (child : Derivation (generatedValidated source valid) goal),
      derivationHeight child < heightBound →
      ∀ stepSource stepTarget, goal = stepJudgment stepSource stepTarget →
        langReduces source.language stepSource stepTarget) :
    ∀ (premises : List Premise)
      (children : DerivationList (generatedValidated source valid)
        ((rewritePremiseJudgments premises).map (applyBindings σ)))
      {boundNames finalNames : List String}
      (_ : tracePremisesModed boundNames premises = some finalNames)
      {current : Bindings}
      (_ : bindingsAgreeWith σ current)
      (_ : ∀ name ∈ boundNames, (Bindings.lookup current name).isSome)
      (_ : ∀ sourcePattern targetPattern,
        Premise.congruence sourcePattern targetPattern ∈ premises →
        ∀ name ∈ patternOccurrenceNames targetPattern,
          (Bindings.lookup σ name).isSome)
      (_ : derivationListHeight children < heightBound),
      ∃ finalBindings fuel,
        PremisesAt (engineBasePremises RelationEnv.empty) source.language
          fuel current premises finalBindings ∧
        bindingsAgreeWith σ finalBindings ∧
        (∀ name ∈ finalNames, (Bindings.lookup finalBindings name).isSome)
  | [], _, boundNames, finalNames, chain, current, currentAgrees,
      currentCover, _, _ => by
      have chainEq : some boundNames = some finalNames := chain
      obtain rfl := Option.some.inj chainEq
      exact ⟨current, 0, .nil current, currentAgrees, currentCover⟩
  | .congruence sourcePattern targetPattern :: rest, children, boundNames,
      finalNames, chain, current, currentAgrees, currentCover, σTargetCover,
      heights => by
      obtain ⟨sourceHole, targetHole, sourceBound, restChain⟩ :=
        tracePremisesModed_cons_inversion chain
      cases children with
      | cons headChild tailChildren =>
      have heightSplit : derivationHeight headChild < heightBound ∧
          derivationListHeight tailChildren < heightBound := by
        simp only [derivationListHeight] at heights
        omega
      have headReduces := childSound headChild heightSplit.1
        (applyBindings σ sourcePattern) (applyBindings σ targetPattern)
        (by simp [stepJudgment, applyBindings])
      obtain ⟨headFuel, headEvidence⟩ := headReduces
      have currentApplied : applyBindings current sourcePattern =
          applyBindings σ sourcePattern := by
        apply applyBindings_agree sourceHole
        intro name nameMember
        have nameBound : name ∈ boundNames := by
          simpa using List.all_eq_true.mp sourceBound name nameMember
        obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
          (currentCover name nameBound)
        rw [valueEq, bindingsAgreeWith_lookup currentAgrees valueEq]
      obtain ⟨premiseBindings, premiseMember, premiseAgrees, premiseCover⟩ :=
        matchPattern_own_instance targetHole
          (σTargetCover sourcePattern targetPattern (List.mem_cons_self ..))
      obtain ⟨next, mergeEq, nextAgrees⟩ :=
        mergeBindings_some_of_agree currentAgrees premiseAgrees
      have nextCover : ∀ name ∈ boundNames ++
          patternOccurrenceNames targetPattern,
          (Bindings.lookup next name).isSome := by
        intro name nameMember
        rcases List.mem_append.mp nameMember with boundName | targetName
        · obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
            (currentCover name boundName)
          rw [mergeBindings_lookup_left mergeEq valueEq]
          rfl
        · obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
            (premiseCover name targetName)
          rw [mergeBindings_lookup_right mergeEq (name, value)
            (bindings_mem_of_lookup valueEq)]
          rfl
      obtain ⟨finalBindings, restFuel, restEvidence, finalAgrees,
          finalCover⟩ :=
        sound_premise_chain source valid childSound rest tailChildren
          restChain nextAgrees nextCover
          (fun s t member => σTargetCover s t (List.mem_cons_of_mem _ member))
          heightSplit.2
      refine ⟨finalBindings, max headFuel restFuel, ?_, finalAgrees,
        finalCover⟩
      exact .cons
        (.congruence
          (stepAt_mono (Nat.le_max_left _ _) (currentApplied ▸ headEvidence))
          premiseMember mergeEq)
        (premisesAt_mono (Nat.le_max_right _ _) restEvidence)
  | .freshness condition :: rest, _, boundNames, finalNames, chain, _, _, _,
      _, _ => by
      simp [tracePremisesModed] at chain
  | .relationQuery relation arguments :: rest, _, boundNames, finalNames,
      chain, _, _, _, _, _ => by
      simp [tracePremisesModed] at chain
  | .forAll collection parameter body :: rest, _, boundNames, finalNames,
      chain, _, _, _, _, _ => by
      simp [tracePremisesModed] at chain

/-- Soundness, bounded form: every checked derivation of a `Step` judgment
is a declarative step, and of a `Steps` judgment a declarative reduction
sequence. -/
private theorem general_sound_bounded (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true) :
    ∀ (bound : Nat) {goal : Pattern}
      (derivation : Derivation (generatedValidated source valid) goal),
      derivationHeight derivation ≤ bound → generalSoundClaim source goal := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | _ bound inductionHypothesis =>
      intro goal derivation heightBound
      cases derivation with
      | byRule ruleInstance application children =>
      have executable :=
        instantiateRule?_eq_some_iff_application.mpr application
      simp only [instantiateRule?, generatedValidated_fst] at executable
      cases lookup :
          (stepPresentation source).lookupRule? ruleInstance.ruleId with
      | none => simp [lookup] at executable
      | some rule =>
          simp only [lookup] at executable
          have childSound : ∀ {childGoal : Pattern}
              (child : Derivation (generatedValidated source valid)
                childGoal),
              derivationHeight child < bound →
              generalSoundClaim source childGoal := by
            intro childGoal child heightLt
            exact inductionHypothesis (derivationHeight child)
              (by omega) child (Nat.le_refl _)
          rcases generated_lookup_inversion source lookup with
            ⟨rewrite, rewriteMember, rfl⟩ | rfl | rfl
          · -- A generated rewrite schema.
            have ruleAdequate := languageDirectTraceAdequate_rules adequate
              rewrite rewriteMember
            by_cases argumentsValid : argumentsValidAt
                (rewriteStepRule rewrite).metavariables
                ruleInstance.arguments = true
            · obtain ⟨chainBound, chain, rightAll⟩ :=
                rewriteDirectTraceAdequate_chain ruleAdequate
              have premisesAligned := instantiateSchemasAt?_eq_applyBindings
                (rewritePremiseJudgments_hole chain)
                (rewriteStepRule_formals_zero rewrite)
                (arguments := ruleInstance.arguments)
                (fun name nameMember => by
                  obtain ⟨pattern, patternMember, patternName⟩ :=
                    mem_patternsOccurrenceNames.mp nameMember
                  exact generated_zip_cover source valid rewriteMember
                    argumentsValid
                    (generated_premise_mem_patterns patternMember)
                    name patternName)
              have conclusionHole : patternHoleSkeleton
                  (stepJudgment rewrite.left rewrite.right) = true := by
                simp [rewriteDirectTraceAdequate_left ruleAdequate,
                  rewriteDirectTraceAdequate_right ruleAdequate]
              have conclusionAligned := instantiateSchemaAt?_eq_applyBindings
                conclusionHole (rewriteStepRule_formals_zero rewrite)
                (arguments := ruleInstance.arguments)
                (generated_zip_cover source valid rewriteMember
                  argumentsValid (generated_conclusion_mem_patterns rewrite))
              have sideConditionsTrue := RuleSchema.sideConditionsHold_of_empty
                (rewriteStepRule rewrite) ruleInstance.arguments
                (rewriteStepRule_sideConditions rewrite)
              rw [if_pos argumentsValid, if_pos sideConditionsTrue]
                at executable
              simp only [instantiateSchemas?, instantiateSchema?,
                rewriteStepRule_premises, rewriteStepRule_conclusion,
                premisesAligned, conclusionAligned, option_some_bind,
                applyBindings_stepJudgment,
                Option.some.injEq, Prod.mk.injEq] at executable
              obtain ⟨premisesEq, goalEq⟩ := executable
              subst premisesEq
              subst goalEq
              constructor
              · intro stepSource stepTarget goalEq'
                obtain ⟨sourceEq, targetEq⟩ := stepJudgment_inj goalEq'
                rw [← sourceEq, ← targetEq]
                have leftHole := rewriteDirectTraceAdequate_left ruleAdequate
                have leftCover : ∀ name ∈
                    patternOccurrenceNames rewrite.left,
                    (Bindings.lookup (zipBindings (rewriteStepRule rewrite).metavariables
                      ruleInstance.arguments) name).isSome := by
                  intro name nameMember
                  refine generated_zip_cover source valid rewriteMember
                    argumentsValid
                    (generated_conclusion_mem_patterns rewrite) name ?_
                  simp only [patternOccurrenceNames_stepJudgment,
                    List.mem_append]
                  exact Or.inl nameMember
                obtain ⟨initialBindings, initialMember, initialAgrees,
                    initialCover⟩ :=
                  matchPattern_own_instance leftHole leftCover
                have σTargetCover : ∀ premiseSource premiseTarget,
                    Premise.congruence premiseSource premiseTarget ∈
                      rewrite.premises →
                    ∀ name ∈ patternOccurrenceNames premiseTarget,
                      (Bindings.lookup (zipBindings (rewriteStepRule rewrite).metavariables
                      ruleInstance.arguments) name).isSome := by
                  intro premiseSource premiseTarget premiseMember name
                    nameMember
                  refine generated_zip_cover source valid rewriteMember
                    argumentsValid
                    (generated_premise_mem_patterns
                      (rewritePremiseJudgments_mem_of_congruence
                        premiseMember)) name ?_
                  simp only [patternOccurrenceNames_stepJudgment,
                    List.mem_append]
                  exact Or.inr nameMember
                have heightsOK : derivationListHeight children < bound := by
                  simp only [derivationHeight] at heightBound
                  omega
                obtain ⟨finalBindings, chainFuel, premisesEvidence,
                    finalAgrees, finalCover⟩ :=
                  sound_premise_chain source valid
                    (fun child heightLt s t gEq =>
                      (childSound child heightLt).1 s t gEq)
                    rewrite.premises children chain initialAgrees
                    initialCover σTargetCover heightsOK
                have applyFinal : applyBindingsForRule source.language
                    rewrite finalBindings =
                      applyBindings (zipBindings (rewriteStepRule rewrite).metavariables
                      ruleInstance.arguments) rewrite.right := by
                  rw [applyBindingsForRule_eq_syntactic]
                  apply applyBindings_agree
                    (rewriteDirectTraceAdequate_right ruleAdequate)
                  intro name nameMember
                  have nameFinal : name ∈ chainBound := by
                    simpa using List.all_eq_true.mp rightAll name nameMember
                  obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
                    (finalCover name nameFinal)
                  rw [valueEq, bindingsAgreeWith_lookup finalAgrees valueEq]
                have initialMember' : initialBindings ∈
                    matchPatternForRule source.language rewrite
                      (applyBindings (zipBindings (rewriteStepRule rewrite).metavariables
                      ruleInstance.arguments) rewrite.left) := by
                  rw [matchPatternForRule_eq_syntactic]
                  exact initialMember
                exact ⟨chainFuel + 1, .rule rewriteMember initialMember'
                  premisesEvidence applyFinal⟩
              · intro stepSource stepTarget goalEq'
                exact absurd goalEq'
                  (stepJudgment_ne_stepsJudgment _ _ _ _)
            · rw [if_neg argumentsValid] at executable
              simp at executable
          · -- The reflexivity schema.
            by_cases argumentsValid : argumentsValidAt
                stepReflRule.metavariables ruleInstance.arguments = true
            · obtain ⟨point, argumentsEq, wfPoint⟩ :=
                argumentsValidAt_one_inversion
                  (by simpa [stepReflRule] using argumentsValid)
              rw [if_pos argumentsValid] at executable
              rw [argumentsEq] at executable
              simp [stepReflRule, RuleSchema.sideConditionsHold,
                instantiateSchemas?, instantiateSchema?,
                instantiateSchemasAt?, instantiateSchemaAt?,
                lookupArgumentAt?, option_some_bind]
                at executable
              obtain ⟨premisesEq, goalEq⟩ := executable
              subst premisesEq
              subst goalEq
              constructor
              · intro stepSource stepTarget goalEq'
                exact absurd goalEq'.symm
                  (stepJudgment_ne_stepsJudgment _ _ _ _)
              · intro stepSource stepTarget goalEq'
                obtain ⟨sourceEq, targetEq⟩ := stepsJudgment_inj
                  (goalEq' :
                    stepsJudgment point point =
                      stepsJudgment stepSource stepTarget)
                rw [← sourceEq, ← targetEq]
            · rw [if_neg argumentsValid] at executable
              simp at executable
          · -- The transitivity schema.
            by_cases argumentsValid : argumentsValidAt
                stepTransRule.metavariables ruleInstance.arguments = true
            · obtain ⟨stepSource₀, middle₀, stepTarget₀, argumentsEq, wfS,
                  wfM, wfT⟩ :=
                argumentsValidAt_three_inversion
                  (by simpa [stepTransRule] using argumentsValid)
              rw [if_pos argumentsValid] at executable
              rw [argumentsEq] at executable
              simp [stepTransRule, RuleSchema.sideConditionsHold,
                instantiateSchemas?, instantiateSchema?,
                instantiateSchemasAt?, instantiateSchemaAt?,
                lookupArgumentAt?, option_some_bind] at executable
              obtain ⟨premisesEq, goalEq⟩ := executable
              subst premisesEq
              subst goalEq
              cases children with
              | cons stepChild starChildren =>
              cases starChildren with
              | cons starChild emptyChildren =>
              have childHeights : derivationHeight stepChild < bound ∧
                  derivationHeight starChild < bound := by
                simp only [derivationHeight, derivationListHeight]
                  at heightBound
                omega
              have stepFact := (childSound stepChild childHeights.1).1
                stepSource₀ middle₀ rfl
              have starFact := (childSound starChild childHeights.2).2
                middle₀ stepTarget₀ rfl
              constructor
              · intro stepSource stepTarget goalEq'
                exact absurd goalEq'.symm
                  (stepJudgment_ne_stepsJudgment _ _ _ _)
              · intro stepSource stepTarget goalEq'
                obtain ⟨sourceEq, targetEq⟩ := stepsJudgment_inj
                  (goalEq' :
                    stepsJudgment stepSource₀ stepTarget₀ =
                      stepsJudgment stepSource stepTarget)
                rw [← sourceEq, ← targetEq]
                exact Relation.ReflTransGen.head stepFact starFact
            · rw [if_neg argumentsValid] at executable
              simp at executable

/-- Soundness of a single checked derivation. -/
private theorem general_sound_derivation (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true) {goal : Pattern}
    (derivation : Derivation (generatedValidated source valid) goal) :
    generalSoundClaim source goal :=
  general_sound_bounded source adequate valid
    (derivationHeight derivation) derivation (Nat.le_refl _)

/-! ### Completeness support -/

@[simp] theorem hasCanonicalBinderMetadata_stepJudgment
    (stepSource stepTarget : Pattern) :
    Pattern.hasCanonicalBinderMetadata (stepJudgment stepSource stepTarget) =
      (Pattern.hasCanonicalBinderMetadata stepSource &&
        Pattern.hasCanonicalBinderMetadata stepTarget) := by
  simp [stepJudgment, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

@[simp] theorem isWellScoped_stepJudgment (stepSource stepTarget : Pattern) :
    Pattern.isWellScoped (stepJudgment stepSource stepTarget) =
      (Pattern.isWellScoped stepSource && Pattern.isWellScoped stepTarget) := by
  simp [stepJudgment, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]

/-- Occurrence names of every congruence premise of a moded chain are bound
by the end of the chain. -/
theorem tracePremisesModed_premise_occ :
    ∀ {premises : List Premise} {boundNames finalNames : List String},
      tracePremisesModed boundNames premises = some finalNames →
      ∀ {sourcePattern targetPattern : Pattern},
        Premise.congruence sourcePattern targetPattern ∈ premises →
        (∀ name ∈ patternOccurrenceNames sourcePattern, name ∈ finalNames) ∧
        (∀ name ∈ patternOccurrenceNames targetPattern, name ∈ finalNames) := by
  intro premises
  induction premises with
  | nil =>
      intro boundNames finalNames _ sourcePattern targetPattern member
      cases member
  | cons head tail inductionHypothesis =>
      intro boundNames finalNames chain sourcePattern targetPattern member
      cases head with
      | congruence headSource headTarget =>
          obtain ⟨-, -, sourceBound, restChain⟩ :=
            tracePremisesModed_cons_inversion chain
          rcases List.mem_cons.mp member with headEq | tailMember
          · injection headEq with sourceEq targetEq
            subst sourceEq
            subst targetEq
            constructor
            · intro name nameMember
              have nameBound : name ∈ boundNames := by
                simpa using List.all_eq_true.mp sourceBound name nameMember
              exact tracePremisesModed_extends restChain name
                (List.mem_append_left _ nameBound)
            · intro name nameMember
              exact tracePremisesModed_extends restChain name
                (List.mem_append_right _ nameMember)
          · exact inductionHypothesis restChain tailMember
      | freshness condition => simp [tracePremisesModed] at chain
      | relationQuery relation arguments => simp [tracePremisesModed] at chain
      | forAll collection parameter body => simp [tracePremisesModed] at chain

/-- Occurrence names of every schema pattern of an adequate generated rule
are bound by the end of its moded chain. -/
theorem generated_pattern_occ_subset {rewrite : RewriteRule}
    {chainBound : List String}
    (chain : tracePremisesModed (patternOccurrenceNames rewrite.left)
      rewrite.premises = some chainBound)
    (rightAll : (patternOccurrenceNames rewrite.right).all
      chainBound.contains = true)
    {pattern : Pattern}
    (patternMember : pattern ∈ RuleSchema.patterns (rewriteStepRule rewrite)) :
    ∀ name ∈ patternOccurrenceNames pattern, name ∈ chainBound := by
  intro name nameMember
  rcases List.mem_append.mp patternMember with premiseMember | conclusionMember
  · obtain ⟨premiseSource, premiseTarget, congruenceMember, patternEq⟩ :=
      mem_rewritePremiseJudgments premiseMember
    subst patternEq
    have occFacts := tracePremisesModed_premise_occ chain congruenceMember
    simp only [patternOccurrenceNames_stepJudgment, List.mem_append]
      at nameMember
    rcases nameMember with sourceName | targetName
    · exact occFacts.1 name sourceName
    · exact occFacts.2 name targetName
  · have conclusionEq : pattern = stepJudgment rewrite.left rewrite.right := by
      simpa using conclusionMember
    subst conclusionEq
    simp only [patternOccurrenceNames_stepJudgment, List.mem_append]
      at nameMember
    rcases nameMember with leftName | rightName
    · exact tracePremisesModed_extends chain name leftName
    · simpa using List.all_eq_true.mp rightAll name rightName

/-- The canonical argument vector read off a binding list. -/
def bindingsArguments (formals : List (String × Nat)) (bindings : Bindings) :
    List Pattern :=
  formals.map fun formal =>
    (Bindings.lookup bindings formal.1).getD (.fvar formal.1)

theorem argumentsValidAt_bindingsArguments
    {formals : List (String × Nat)} {bindings : Bindings}
    (allZero : ∀ formal ∈ formals, formal.2 = 0)
    (values : bindingsValuesWellFormed bindings)
    (cover : ∀ name ∈ formals.map Prod.fst,
      (Bindings.lookup bindings name).isSome) :
    argumentsValidAt formals (bindingsArguments formals bindings) = true := by
  induction formals with
  | nil => rfl
  | cons formal rest inductionHypothesis =>
      rcases formal with ⟨formalName, formalDepth⟩
      have formalDepthZero : formalDepth = 0 :=
        allZero (formalName, formalDepth) (List.mem_cons_self ..)
      subst formalDepthZero
      obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
        (cover formalName (by simp))
      have valueFacts := values (formalName, value)
        (bindings_mem_of_lookup valueEq)
      simp only [bindingsArguments, List.map_cons, argumentsValidAt,
        argumentValidAt, valueEq, Option.getD_some, Bool.and_eq_true]
      refine ⟨⟨valueFacts.1, valueFacts.2⟩, ?_⟩
      exact inductionHypothesis
        (fun formal member => allZero formal (List.mem_cons_of_mem _ member))
        (fun name member => cover name (List.mem_cons_of_mem _ member))

private theorem bindings_lookup_cons_self (name : String) (value : Pattern)
    (rest : Bindings) :
    Bindings.lookup ((name, value) :: rest) name = some value := by
  unfold Bindings.lookup
  rw [List.find?_cons_of_pos (by simp)]
  rfl

private theorem bindings_lookup_cons_ne {headName name : String}
    (ne : headName ≠ name) (value : Pattern) (rest : Bindings) :
    Bindings.lookup ((headName, value) :: rest) name =
      Bindings.lookup rest name := by
  unfold Bindings.lookup
  rw [List.find?_cons_of_neg (by simpa using ne)]

/-- The positional assignment of the canonical argument vector looks up
exactly like the source binding list on formal names. -/
theorem zipBindings_bindingsArguments_lookup :
    ∀ (formals : List (String × Nat)) (bindings : Bindings),
      (∀ name ∈ formals.map Prod.fst,
        (Bindings.lookup bindings name).isSome) →
      ∀ name ∈ formals.map Prod.fst,
        Bindings.lookup
            (zipBindings formals (bindingsArguments formals bindings)) name =
          Bindings.lookup bindings name
  | [], bindings, _, name, nameMember => by simp at nameMember
  | (formalName, formalDepth) :: rest, bindings, cover, name, nameMember => by
      have zipEq : zipBindings ((formalName, formalDepth) :: rest)
          (bindingsArguments ((formalName, formalDepth) :: rest) bindings) =
            (formalName,
              (Bindings.lookup bindings formalName).getD
                (.fvar formalName)) ::
              zipBindings rest (bindingsArguments rest bindings) := rfl
      rw [zipEq]
      by_cases headName : formalName = name
      · subst headName
        rw [bindings_lookup_cons_self]
        obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
          (cover formalName (by simp))
        rw [valueEq, Option.getD_some]
      · rw [bindings_lookup_cons_ne headName]
        have restMember : name ∈ rest.map Prod.fst := by
          simp only [List.map_cons, List.mem_cons] at nameMember
          rcases nameMember with headEq | restMember
          · exact absurd headEq.symm headName
          · exact restMember
        exact zipBindings_bindingsArguments_lookup rest bindings
          (fun innerName member =>
            cover innerName (List.mem_cons_of_mem _ member))
          name restMember

/-! ### General instantiation of the fixed trace schemas -/

theorem generated_refl_instantiates (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true) {point : Pattern}
    (wfPoint : wellFormedTerm point) :
    instantiateRule? (generatedValidated source valid)
        ⟨⟨"steps-refl"⟩, [point]⟩ =
      some ([], stepsJudgment point point) := by
  obtain ⟨pointGround, pointCanonical⟩ := wfPoint
  simp only [instantiateRule?, generatedValidated_fst]
  rw [generated_lookup_refl source]
  simp [stepReflRule, argumentsValidAt, argumentValidAt, pointGround,
    pointCanonical, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, stepsJudgment]

/-- Checked child certificates and final-binding facts, built by walking a
moded congruence chain alongside its declarative premise evidence. -/
private theorem complete_premise_chain (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true)
    {innerFuel : Nat}
    (stepComplete : ∀ {stepSource stepTarget : Pattern},
      StepAt (engineBasePremises RelationEnv.empty) source.language
        innerFuel stepSource stepTarget →
      wellFormedTerm stepSource →
      Nonempty (Derivation (generatedValidated source valid)
        (stepJudgment stepSource stepTarget)) ∧ wellFormedTerm stepTarget) :
    ∀ (premises : List Premise) {boundNames finalNames : List String}
      (_ : tracePremisesModed boundNames premises = some finalNames)
      {current finalBindings : Bindings}
      (_ : PremisesAt (engineBasePremises RelationEnv.empty)
        source.language innerFuel current premises finalBindings)
      (_ : ∀ sourcePattern targetPattern,
        Premise.congruence sourcePattern targetPattern ∈ premises →
        Pattern.isWellScoped sourcePattern = true ∧
        Pattern.hasCanonicalBinderMetadata sourcePattern = true ∧
        Pattern.hasCanonicalBinderMetadata targetPattern = true)
      (_ : bindingsValuesWellFormed current)
      (_ : ∀ name ∈ boundNames, (Bindings.lookup current name).isSome),
      bindingsValuesWellFormed finalBindings ∧
      (∀ name ∈ finalNames, (Bindings.lookup finalBindings name).isSome) ∧
      (∀ {name : String} {value : Pattern},
        Bindings.lookup current name = some value →
        Bindings.lookup finalBindings name = some value) ∧
      Nonempty (DerivationList (generatedValidated source valid)
        ((rewritePremiseJudgments premises).map
          (applyBindings finalBindings)))
  | [], boundNames, finalNames, chain, current, finalBindings, evidence,
      _, currentValues, currentCover => by
      cases evidence with
      | nil =>
          have chainEq : some boundNames = some finalNames := chain
          obtain rfl := Option.some.inj chainEq
          exact ⟨currentValues, currentCover, fun lookupEq => lookupEq,
            ⟨.nil⟩⟩
  | .congruence sourcePattern targetPattern :: rest, boundNames, finalNames,
      chain, current, finalBindings, evidence, premisePatternFacts,
      currentValues, currentCover => by
      obtain ⟨sourceHole, targetHole, sourceBound, restChain⟩ :=
        tracePremisesModed_cons_inversion chain
      obtain ⟨sourceScoped, sourceCanonical, targetCanonical⟩ :=
        premisePatternFacts sourcePattern targetPattern
          (List.mem_cons_self ..)
      cases evidence with
      | cons premiseEvidence restEvidence =>
      cases premiseEvidence with
      | congruence stepEvidence matchTarget merged =>
      rename_i middle premiseBindings candidate
      have sourceOccCover : ∀ name ∈ patternOccurrenceNames sourcePattern,
          (Bindings.lookup current name).isSome := by
        intro name nameMember
        have nameBound : name ∈ boundNames := by
          simpa using List.all_eq_true.mp sourceBound name nameMember
        exact currentCover name nameBound
      have steppedWf := applyBindings_wellFormed sourceHole sourceScoped
        sourceCanonical currentValues sourceOccCover
      obtain ⟨⟨childDerivation⟩, wfCandidate⟩ :=
        stepComplete stepEvidence steppedWf
      have matchFacts := matchPattern_holeSkeleton_sound targetHole
        targetCanonical wfCandidate.1 wfCandidate.2 premiseBindings
        matchTarget
      have middleValues : bindingsValuesWellFormed middle := by
        intro pair pairMember
        rcases mergeBindings_mem_source merged pair pairMember with
          currentPair | premisePair
        · exact currentValues pair currentPair
        · exact matchFacts.2.2.2 pair premisePair
      have middleCover : ∀ name ∈ boundNames ++
          patternOccurrenceNames targetPattern,
          (Bindings.lookup middle name).isSome := by
        intro name nameMember
        rcases List.mem_append.mp nameMember with boundName | targetName
        · obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
            (currentCover name boundName)
          rw [mergeBindings_lookup_left merged valueEq]
          rfl
        · obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
            (matchFacts.2.2.1 name targetName)
          rw [mergeBindings_lookup_right merged (name, value)
            (bindings_mem_of_lookup valueEq)]
          rfl
      obtain ⟨finalValues, finalCover, finalExtMiddle, ⟨restList⟩⟩ :=
        complete_premise_chain source valid stepComplete rest restChain
          restEvidence
          (fun s t member => premisePatternFacts s t
            (List.mem_cons_of_mem _ member))
          middleValues middleCover
      have finalExt : ∀ {name : String} {value : Pattern},
          Bindings.lookup current name = some value →
          Bindings.lookup finalBindings name = some value :=
        fun lookupEq =>
          finalExtMiddle (mergeBindings_lookup_left merged lookupEq)
      have sourceEq : applyBindings finalBindings sourcePattern =
          applyBindings current sourcePattern := by
        apply applyBindings_agree sourceHole
        intro name nameMember
        obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
          (sourceOccCover name nameMember)
        rw [valueEq, finalExt valueEq]
      have targetEq : applyBindings finalBindings targetPattern =
          candidate := by
        have toPremise : applyBindings finalBindings targetPattern =
            applyBindings premiseBindings targetPattern := by
          apply applyBindings_agree targetHole
          intro name nameMember
          obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
            (matchFacts.2.2.1 name nameMember)
          rw [valueEq, finalExtMiddle
            (mergeBindings_lookup_right merged (name, value)
              (bindings_mem_of_lookup valueEq))]
        rw [toPremise, matchFacts.1]
      have judgmentEq : stepJudgment (applyBindings current sourcePattern)
          candidate =
            applyBindings finalBindings
              (stepJudgment sourcePattern targetPattern) := by
        rw [applyBindings_stepJudgment, sourceEq, targetEq]
      exact ⟨finalValues, finalCover, finalExt,
        ⟨.cons (judgmentEq ▸ childDerivation) restList⟩⟩
  | .freshness condition :: rest, boundNames, finalNames, chain, current,
      finalBindings, evidence, premisePatternFacts, currentValues,
      currentCover => by
      simp [tracePremisesModed] at chain
  | .relationQuery relation arguments :: rest, boundNames, finalNames,
      chain, current, finalBindings, evidence, premisePatternFacts,
      currentValues, currentCover => by
      simp [tracePremisesModed] at chain
  | .forAll collection parameter body :: rest, boundNames, finalNames,
      chain, current, finalBindings, evidence, premisePatternFacts,
      currentValues, currentCover => by
      simp [tracePremisesModed] at chain

/-- Completeness, bounded form: every declarative step from a
checker-well-formed source has a checked `Step` certificate, and steps
preserve checker well-formedness. -/
private theorem general_complete_stepAt (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true) :
    ∀ (fuel : Nat) {stepSource stepTarget : Pattern},
      StepAt (engineBasePremises RelationEnv.empty) source.language fuel
        stepSource stepTarget →
      wellFormedTerm stepSource →
      Nonempty (Derivation (generatedValidated source valid)
        (stepJudgment stepSource stepTarget)) ∧
        wellFormedTerm stepTarget := by
  have nodupNames := languageDirectTraceAdequate_nodupNames adequate
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel inductionHypothesis =>
      intro stepSource stepTarget evidence wfSource
      cases evidence with
      | rule ruleMember matchMember premisesEvidence applyEq =>
          rename_i innerFuel rewrite initialBindings finalBindings
          have ruleAdequate := languageDirectTraceAdequate_rules adequate
            rewrite ruleMember
          have ruleValid := generated_rule_isValidV1 source valid ruleMember
          have leftHole := rewriteDirectTraceAdequate_left ruleAdequate
          have rightHole := rewriteDirectTraceAdequate_right ruleAdequate
          obtain ⟨chainBound, chain, rightAll⟩ :=
            rewriteDirectTraceAdequate_chain ruleAdequate
          have conclusionCanonical := isValidV1_pattern_canonical ruleValid
            (generated_conclusion_mem_patterns rewrite)
          have conclusionScoped := isValidV1_pattern_wellScoped ruleValid
            (generated_conclusion_mem_patterns rewrite)
          simp only [hasCanonicalBinderMetadata_stepJudgment,
            Bool.and_eq_true] at conclusionCanonical
          simp only [isWellScoped_stepJudgment, Bool.and_eq_true]
            at conclusionScoped
          rw [matchPatternForRule_eq_syntactic] at matchMember
          have matchFacts := matchPattern_holeSkeleton_sound leftHole
            conclusionCanonical.1 wfSource.1 wfSource.2 initialBindings
            matchMember
          have premisePatternFacts : ∀ s t,
              Premise.congruence s t ∈ rewrite.premises →
              Pattern.isWellScoped s = true ∧
              Pattern.hasCanonicalBinderMetadata s = true ∧
              Pattern.hasCanonicalBinderMetadata t = true := by
            intro s t member
            have judgmentMember := generated_premise_mem_patterns
              (rewritePremiseJudgments_mem_of_congruence member)
            have canonical := isValidV1_pattern_canonical ruleValid
              judgmentMember
            have wellScopedFact := isValidV1_pattern_wellScoped ruleValid
              judgmentMember
            simp only [hasCanonicalBinderMetadata_stepJudgment,
              Bool.and_eq_true] at canonical
            simp only [isWellScoped_stepJudgment, Bool.and_eq_true]
              at wellScopedFact
            exact ⟨wellScopedFact.1, canonical.1, canonical.2⟩
          obtain ⟨finalValues, finalCover, finalExt, ⟨childList⟩⟩ :=
            complete_premise_chain source valid
              (fun stepEvidence wf =>
                inductionHypothesis innerFuel (by omega) stepEvidence wf)
              rewrite.premises chain premisesEvidence premisePatternFacts
              matchFacts.2.2.2 matchFacts.2.2.1
          have formalNamesCover : ∀ name ∈
              (rewriteStepRule rewrite).metavariables.map Prod.fst,
              name ∈ chainBound := by
            intro name nameMember
            obtain ⟨pattern, patternMember, patternName⟩ :=
              isValidV1_formal_names_occur ruleValid nameMember
            exact generated_pattern_occ_subset chain rightAll patternMember
              name patternName
          have finalFormalCover : ∀ name ∈
              (rewriteStepRule rewrite).metavariables.map Prod.fst,
              (Bindings.lookup finalBindings name).isSome :=
            fun name nameMember =>
              finalCover name (formalNamesCover name nameMember)
          have argumentsValid := argumentsValidAt_bindingsArguments
            (rewriteStepRule_formals_zero rewrite) finalValues
            finalFormalCover
          have zipLookup := zipBindings_bindingsArguments_lookup
            (rewriteStepRule rewrite).metavariables finalBindings
            finalFormalCover
          have patternAgree : ∀ {pattern : Pattern},
              pattern ∈ RuleSchema.patterns (rewriteStepRule rewrite) →
              ∀ name ∈ patternOccurrenceNames pattern,
              Bindings.lookup
                  (zipBindings (rewriteStepRule rewrite).metavariables
                    (bindingsArguments
                      (rewriteStepRule rewrite).metavariables
                      finalBindings)) name =
                Bindings.lookup finalBindings name := by
            intro pattern patternMember name nameMember
            exact zipLookup name (isValidV1_occurrence_names_subset
              ruleValid patternMember nameMember)
          have instEq := generated_rewrite_instantiation source valid
            nodupNames ruleMember ruleAdequate argumentsValid
          have premisesComponent :
              (rewritePremiseJudgments rewrite.premises).map
                (applyBindings
                  (zipBindings (rewriteStepRule rewrite).metavariables
                    (bindingsArguments
                      (rewriteStepRule rewrite).metavariables
                      finalBindings))) =
              (rewritePremiseJudgments rewrite.premises).map
                (applyBindings finalBindings) := by
            apply applyBindingsList_agree (rewritePremiseJudgments_hole chain)
            intro name nameMember
            obtain ⟨pattern, patternMember, patternName⟩ :=
              mem_patternsOccurrenceNames.mp nameMember
            exact patternAgree (generated_premise_mem_patterns patternMember)
              name patternName
          have targetEq : applyBindings finalBindings rewrite.right =
              stepTarget := by
            rw [applyBindingsForRule_eq_syntactic] at applyEq
            exact applyEq
          have leftComponent : applyBindings
              (zipBindings (rewriteStepRule rewrite).metavariables
                (bindingsArguments (rewriteStepRule rewrite).metavariables
                  finalBindings)) rewrite.left = stepSource := by
            have zipToFinal := applyBindings_agree leftHole
              (fun name nameMember => patternAgree
                (generated_conclusion_mem_patterns rewrite) name
                (by
                  simp only [patternOccurrenceNames_stepJudgment,
                    List.mem_append]
                  exact Or.inl nameMember))
            have finalToInitial : applyBindings finalBindings rewrite.left =
                applyBindings initialBindings rewrite.left := by
              apply applyBindings_agree leftHole
              intro name nameMember
              obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
                (matchFacts.2.2.1 name nameMember)
              rw [valueEq, finalExt valueEq]
            rw [zipToFinal, finalToInitial, matchFacts.1]
          have rightComponent : applyBindings
              (zipBindings (rewriteStepRule rewrite).metavariables
                (bindingsArguments (rewriteStepRule rewrite).metavariables
                  finalBindings)) rewrite.right = stepTarget := by
            have zipToFinal := applyBindings_agree rightHole
              (fun name nameMember => patternAgree
                (generated_conclusion_mem_patterns rewrite) name
                (by
                  simp only [patternOccurrenceNames_stepJudgment,
                    List.mem_append]
                  exact Or.inr nameMember))
            rw [zipToFinal, targetEq]
          rw [premisesComponent, leftComponent, rightComponent] at instEq
          have wfTarget : wellFormedTerm stepTarget := by
            rw [← targetEq]
            exact applyBindings_wellFormed rightHole conclusionScoped.2
              conclusionCanonical.2 finalValues
              (fun name nameMember => finalCover name
                (by simpa using List.all_eq_true.mp rightAll name nameMember))
          exact ⟨⟨.byRule
            ⟨(rewriteStepRule rewrite).id,
              bindingsArguments (rewriteStepRule rewrite).metavariables
                finalBindings⟩
            (instantiateRule?_eq_some_iff_application.mp instEq)
            childList⟩, wfTarget⟩

theorem generated_trans_instantiates (source : DirectTraceLanguage)
    (valid : (stepPresentation source).isValidV2 = true)
    {stepSource middle stepTarget : Pattern}
    (wfSource : wellFormedTerm stepSource) (wfMiddle : wellFormedTerm middle)
    (wfTarget : wellFormedTerm stepTarget) :
    instantiateRule? (generatedValidated source valid)
        ⟨⟨"steps-trans"⟩, [stepSource, middle, stepTarget]⟩ =
      some ([stepJudgment stepSource middle, stepsJudgment middle stepTarget],
        stepsJudgment stepSource stepTarget) := by
  obtain ⟨sourceGround, sourceCanonical⟩ := wfSource
  obtain ⟨middleGround, middleCanonical⟩ := wfMiddle
  obtain ⟨targetGround, targetCanonical⟩ := wfTarget
  simp only [instantiateRule?, generatedValidated_fst]
  rw [generated_lookup_trans source]
  simp [stepTransRule, argumentsValidAt, argumentValidAt, sourceGround,
    sourceCanonical, middleGround, middleCanonical, targetGround,
    targetCanonical, RuleSchema.sideConditionsHold, instantiateSchemas?,
    instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
    lookupArgumentAt?, stepJudgment, stepsJudgment]

/-! ### The general adequacy interface -/

/-- General two-sided one-step trace adequacy: over every adequate admitted
direct-trace language, a checked `Step` certificate from a checker-well-formed
source exists exactly when the language takes the declarative step. -/
theorem directTrace_step_adequacy (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true)
    {stepSource stepTarget : Pattern}
    (wfSource : wellFormedTerm stepSource) :
    Nonempty (Derivation (generatedValidated source valid)
        (stepJudgment stepSource stepTarget)) ↔
      langReduces source.language stepSource stepTarget := by
  constructor
  · rintro ⟨derivation⟩
    exact (general_sound_derivation source adequate valid derivation).1
      stepSource stepTarget rfl
  · rintro ⟨fuel, evidence⟩
    exact (general_complete_stepAt source adequate valid fuel evidence
      wfSource).1

/-- Declarative steps preserve the checker's argument discipline. -/
theorem directTrace_step_preserves_wellFormed (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true)
    {stepSource stepTarget : Pattern}
    (step : langReduces source.language stepSource stepTarget)
    (wfSource : wellFormedTerm stepSource) : wellFormedTerm stepTarget := by
  obtain ⟨fuel, evidence⟩ := step
  exact (general_complete_stepAt source adequate valid fuel evidence
    wfSource).2

private theorem general_star_complete (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true)
    {stepSource stepTarget : Pattern}
    (star : Relation.ReflTransGen (langReduces source.language)
      stepSource stepTarget)
    (wfSource : wellFormedTerm stepSource) :
    Nonempty (Derivation (generatedValidated source valid)
      (stepsJudgment stepSource stepTarget)) ∧
      wellFormedTerm stepTarget := by
  revert wfSource
  induction star using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro wfTarget
      exact ⟨⟨.byRule ⟨⟨"steps-refl"⟩, [stepTarget]⟩
        (instantiateRule?_eq_some_iff_application.mp
          (generated_refl_instantiates source valid wfTarget)) .nil⟩,
        wfTarget⟩
  | head headStep restStar restHypothesis =>
      rename_i headSource headMiddle
      intro wfHead
      have wfMiddle := directTrace_step_preserves_wellFormed source adequate
        valid headStep wfHead
      obtain ⟨⟨restDerivation⟩, wfTarget⟩ := restHypothesis wfMiddle
      obtain ⟨fuel, evidence⟩ := headStep
      obtain ⟨⟨stepDerivation⟩, -⟩ := general_complete_stepAt source
        adequate valid fuel evidence wfHead
      exact ⟨⟨.byRule
        ⟨⟨"steps-trans"⟩, [headSource, headMiddle, stepTarget]⟩
        (instantiateRule?_eq_some_iff_application.mp
          (generated_trans_instantiates source valid wfHead wfMiddle
            wfTarget))
        (.cons stepDerivation (.cons restDerivation .nil))⟩, wfTarget⟩

/-- General two-sided trace adequacy: a checked `Steps` certificate from a
checker-well-formed source exists exactly when the language takes a
reflexive-transitive reduction sequence. -/
theorem directTrace_steps_adequacy (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true)
    {stepSource stepTarget : Pattern}
    (wfSource : wellFormedTerm stepSource) :
    Nonempty (Derivation (generatedValidated source valid)
        (stepsJudgment stepSource stepTarget)) ↔
      Relation.ReflTransGen (langReduces source.language)
        stepSource stepTarget := by
  constructor
  · rintro ⟨derivation⟩
    exact (general_sound_derivation source adequate valid derivation).2
      stepSource stepTarget rfl
  · intro star
    exact (general_star_complete source adequate valid star wfSource).1

/-- One-step reduction is exactly existence of an accepted finite
certificate over the generated presentation. -/
theorem directTrace_step_iff_certificate (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true)
    {stepSource stepTarget : Pattern}
    (wfSource : wellFormedTerm stepSource) :
    langReduces source.language stepSource stepTarget ↔
      ∃ proof : RawProof,
        checkRaw (generatedValidated source valid)
          (stepJudgment stepSource stepTarget) proof = true := by
  rw [← directTrace_step_adequacy source adequate valid wfSource]
  constructor
  · rintro ⟨derivation⟩
    exact ⟨derivation.erase, checkRaw_erase derivation⟩
  · rintro ⟨proof, accepted⟩
    exact checkRaw_soundness accepted

/-- Reachability is exactly existence of an accepted finite trace
certificate over the generated presentation. -/
theorem directTrace_reachability_iff_certificate (source : DirectTraceLanguage)
    (adequate : languageDirectTraceAdequate source.language = true)
    (valid : (stepPresentation source).isValidV2 = true)
    {stepSource stepTarget : Pattern}
    (wfSource : wellFormedTerm stepSource) :
    Relation.ReflTransGen (langReduces source.language)
        stepSource stepTarget ↔
      ∃ proof : RawProof,
        checkRaw (generatedValidated source valid)
          (stepsJudgment stepSource stepTarget) proof = true := by
  rw [← directTrace_steps_adequacy source adequate valid wfSource]
  constructor
  · rintro ⟨derivation⟩
    exact ⟨derivation.erase, checkRaw_erase derivation⟩
  · rintro ⟨proof, accepted⟩
    exact checkRaw_soundness accepted

end GeneralAdequacy

end Mettapedia.GSLT.LanguageDef.ProofGSLT
