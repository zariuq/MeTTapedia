import Mettapedia.Logic.HostingStyles.AmbientSpace.Steps

/-!
# A constructor that the space and the subject do not mention is in no answer

`tokens counted pattern` counts the applications in a pattern whose label is
counted.  This module shows that a count that is zero stays zero through the
operations that a step of the ambient presentation is made of:

* lifting and the binder-eliminating instantiation of patterns
  (`tokens_liftBVars_eq_zero`, `tokens_instantiateBVarAt_eq_zero`), hence
  beta;
* matching a first-order pattern: the values that a match binds are parts of
  its subject (`tokens_of_matched`), and an instance of a first-order pattern
  under such bindings (`tokens_applyBindings_eq_zero`);
* reading a stored atom as a side of a rule (`tokens_asRule_eq_zero`), the
  atoms that a space stores (`tokens_of_mem_storedAtoms`), and so the answers
  of a space for a subject (`tokens_of_mem_matchResults`);
* contraction, for a count that does not count quotation and dropping
  (`tokens_contract`).

Hence **a step of a member of the family, from a pattern without a counted
constructor at a space without one, reaches a pattern without one**
(`ambient_stepAt_tokens`).  With the count of the run constructor this says
that the family never builds a run.

Typing is carried along the two inclusions of constructors that the
comparison of the two candidates needs: a term of a language is a term of a
language with more constructors (`wellSorted_of_terms_subset`), and a term
without a counted constructor is a term of the language without the counted
constructors (`wellSorted_of_tokens_eq_zero`); a term of a language none of
whose constructors is counted has none (`tokens_eq_zero_of_hasType`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution
  (liftBVars liftBVarsList liftBVarsList_eq_map instantiateBVarAt instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList tokensList_eq_zero)

variable {counted : String → Bool}

/-! ## Counts that are zero -/

/-- The members of a list without token have none. -/
theorem tokens_eq_zero_of_mem :
    ∀ {patterns : List Pattern}, tokensList counted patterns = 0 →
      ∀ pattern ∈ patterns, tokens counted pattern = 0
  | [], _, _, member => by cases member
  | head :: tail, zero, pattern, member => by
      rw [tokensList] at zero
      rcases List.mem_cons.mp member with rfl | inTail
      · omega
      · exact tokens_eq_zero_of_mem (by omega) pattern inTail

/-- An application has no token exactly when its label is not counted and its
arguments have none. -/
theorem tokens_apply_eq_zero_iff {label : String} {arguments : List Pattern} :
    tokens counted (.apply label arguments) = 0 ↔
      counted label = false ∧ ∀ argument ∈ arguments, tokens counted argument = 0 := by
  rw [tokens]
  constructor
  · intro zero
    by_cases isCounted : counted label = true
    · simp [isCounted] at zero
    · refine ⟨by simpa using isCounted, tokens_eq_zero_of_mem (by simp [isCounted] at zero; exact zero)⟩
  · rintro ⟨uncounted, each⟩
    simp [uncounted, tokensList_eq_zero each]

/-! ## Lifting and instantiation -/

/-- Lifting adds no token. -/
theorem tokens_liftBVars_eq_zero (pattern : Pattern) :
    ∀ cutoff shift : Nat, tokens counted pattern = 0 →
      tokens counted (liftBVars cutoff shift pattern) = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro cutoff shift _
      rw [liftBVars]
      split <;> rfl
  | hfvar name => intro cutoff shift _; rfl
  | happly label arguments ih =>
      intro cutoff shift zero
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp zero
      rw [liftBVars, liftBVarsList_eq_map]
      exact tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun lifted member => by
        obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
        exact ih argument inArguments cutoff shift (each argument inArguments)⟩
  | hlambda binder body ih =>
      intro cutoff shift zero
      rw [liftBVars, tokens]
      exact ih _ _ (by rwa [tokens] at zero)
  | hmultiLambda arity binders body ih =>
      intro cutoff shift zero
      rw [liftBVars, tokens]
      exact ih _ _ (by rwa [tokens] at zero)
  | hsubst body replacement ihBody ihReplacement =>
      intro cutoff shift zero
      rw [tokens] at zero
      rw [liftBVars, tokens, ihBody _ _ (by omega), ihReplacement _ _ (by omega)]
  | hcollection kind elements rest ih =>
      intro cutoff shift zero
      rw [tokens] at zero
      rw [liftBVars, liftBVarsList_eq_map, tokens]
      exact tokensList_eq_zero fun lifted member => by
        obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
        exact ih element inElements cutoff shift (tokens_eq_zero_of_mem zero element inElements)

/-- **Instantiating a bound variable of a pattern without token by a pattern
without token gives a pattern without token.** -/
theorem tokens_instantiateBVarAt_eq_zero {replacement : Pattern}
    (clean : tokens counted replacement = 0) (pattern : Pattern) :
    ∀ depth : Nat, tokens counted pattern = 0 →
      tokens counted (instantiateBVarAt depth replacement pattern) = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth _
      rw [instantiateBVarAt]
      split
      · rfl
      · split
        · exact tokens_liftBVars_eq_zero replacement 0 depth clean
        · rfl
  | hfvar name => intro depth _; rw [instantiateBVarAt]; rfl
  | happly label arguments ih =>
      intro depth zero
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp zero
      rw [instantiateBVarAt]
      exact tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun instantiated member => by
        obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
        exact ih argument inArguments depth (each argument inArguments)⟩
  | hlambda binder body ih =>
      intro depth zero
      rw [instantiateBVarAt, tokens]
      exact ih _ (by rwa [tokens] at zero)
  | hmultiLambda arity binders body ih =>
      intro depth zero
      rw [instantiateBVarAt, tokens]
      exact ih _ (by rwa [tokens] at zero)
  | hsubst body nested ihBody ihNested =>
      intro depth zero
      rw [tokens] at zero
      rw [instantiateBVarAt, tokens, ihBody _ (by omega), ihNested _ (by omega)]
  | hcollection kind elements rest ih =>
      intro depth zero
      rw [tokens] at zero
      rw [instantiateBVarAt, tokens]
      exact tokensList_eq_zero fun instantiated member => by
        obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
        exact ih element inElements depth (tokens_eq_zero_of_mem zero element inElements)

/-! ## Matching and instances -/

/-- What a merge of two lists of bindings binds, one of the two binds. -/
theorem mem_of_mergeBindings {second : Bindings} :
    ∀ {first merged : Bindings}, mergeBindings first second = some merged →
      ∀ entry ∈ merged, entry ∈ first ∨ entry ∈ second := by
  induction second with
  | nil =>
      intro first merged same entry member
      have equal : first = merged := by simpa [mergeBindings] using same
      exact .inl (equal ▸ member)
  | cons head rest ih =>
      intro first merged same entry member
      obtain ⟨name, value⟩ := head
      cases found : first.find? (fun candidate => candidate.1 == name) with
      | none =>
          simp only [mergeBindings, List.foldlM_cons, found, Option.bind_eq_bind,
            Option.bind_some] at same
          rcases ih (first := (name, value) :: first) same entry member with inFirst | inRest
          · rcases List.mem_cons.mp inFirst with rfl | inOld
            · exact .inr (List.mem_cons_self ..)
            · exact .inl inOld
          · exact .inr (List.mem_cons_of_mem _ inRest)
      | some existing =>
          simp only [mergeBindings, List.foldlM_cons, found, Option.bind_eq_bind] at same
          by_cases agree : (existing.2 == value) = true
          · simp only [agree, if_true, Option.bind_some] at same
            rcases ih (first := first) same entry member with inFirst | inRest
            · exact .inl inFirst
            · exact .inr (List.mem_cons_of_mem _ inRest)
          · simp [agree] at same

/-- The values bound by a match of a list of first-order patterns against a
list without token have no token. -/
theorem tokens_of_matchedArgs :
    ∀ {patterns : List Pattern},
      (∀ pattern ∈ patterns, ∀ {subject : Pattern} {bindings : Bindings},
        bindings ∈ matchPattern pattern subject → tokens counted subject = 0 →
          ∀ entry ∈ bindings, tokens counted entry.2 = 0) →
      ∀ {subjects : List Pattern} {bindings : Bindings},
        MatchArgsRel patterns subjects bindings → tokensList counted subjects = 0 →
          ∀ entry ∈ bindings, tokens counted entry.2 = 0
  | [], _, _, _, related, _, entry, member => by
      cases related
      cases member
  | head :: tail, each, _, _, related, zero, entry, member => by
      cases related with
      | cons headRel tailRel merged =>
          rw [tokensList] at zero
          rcases mem_of_mergeBindings merged entry member with inHead | inTail
          · exact each head (List.mem_cons_self ..) (matchRel_complete headRel) (by omega) entry
              inHead
          · exact tokens_of_matchedArgs
              (fun pattern inTail' => each pattern (List.mem_cons_of_mem _ inTail')) tailRel
              (by omega) entry inTail

/-- **The values that a match of a first-order pattern binds are parts of its
subject**: against a subject without token they have no token. -/
theorem tokens_of_matched (pattern : Pattern) :
    isMatchCorrectAux pattern = true → ∀ {subject : Pattern} {bindings : Bindings},
      bindings ∈ matchPattern pattern subject → tokens counted subject = 0 →
        ∀ entry ∈ bindings, tokens counted entry.2 = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _ subject bindings matched _ entry member
      cases matchPattern_sound matched with
      | bvar => cases member
  | hfvar name =>
      intro _ subject bindings matched zero entry member
      rw [mem_matchPattern_fvar.mp matched] at member
      rw [List.mem_singleton.mp member]
      exact zero
  | happly label arguments ih =>
      intro exact subject bindings matched zero entry member
      have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
      cases matchPattern_sound matched with
      | apply argsRel _ =>
          rw [tokens] at zero
          exact tokens_of_matchedArgs
            (fun argument inArguments => ih argument inArguments (each argument inArguments))
            argsRel (by omega) entry member
  | hlambda binder body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ => intro exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ => intro exact; simp [isMatchCorrectAux] at exact

/-- **An instance of a first-order pattern without token, under bindings
whose values have no token, has no token.** -/
theorem tokens_applyBindings_eq_zero {bindings : Bindings}
    (values : ∀ entry ∈ bindings, tokens counted entry.2 = 0) (pattern : Pattern) :
    isMatchCorrectAux pattern = true → tokens counted pattern = 0 →
      tokens counted (applyBindings bindings pattern) = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _; simp [applyBindings, tokens]
  | hfvar name =>
      intro _ _
      rw [applyBindings]
      split
      · next value found => exact values _ (List.mem_of_find?_eq_some found)
      · rfl
  | happly label arguments ih =>
      intro exact zero
      have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
      obtain ⟨uncounted, clean⟩ := tokens_apply_eq_zero_iff.mp zero
      have unfolded : applyBindings bindings (.apply label arguments) =
          .apply label (arguments.map (applyBindings bindings)) := by simp [applyBindings]
      rw [unfolded]
      exact tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun instance_ member => by
        obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
        exact ih argument inArguments (each argument inArguments) (clean argument inArguments)⟩
  | hlambda binder body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ => intro exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ => intro exact; simp [isMatchCorrectAux] at exact

/-! ## Spaces and their answers -/

/-- Reading a stored atom as a side of a rule adds no token. -/
theorem tokens_asRule_eq_zero (pattern : Pattern) :
    tokens counted pattern = 0 → tokens counted (asRule pattern) = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rw [asRule]; rfl
  | hfvar name => intro _; rw [asRule]; rfl
  | happly label arguments ih =>
      intro zero
      obtain ⟨uncounted, clean⟩ := tokens_apply_eq_zero_iff.mp zero
      by_cases isVariable : label = "prime-variable"
      · rw [asRule, if_pos isVariable]
        rfl
      · rw [asRule_apply_of_ne isVariable]
        exact tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun read member => by
          obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
          exact ih argument inArguments (clean argument inArguments)⟩
  | hlambda binder body _ => intro zero; rw [asRule]; exact zero
  | hmultiLambda arity binders body _ => intro zero; rw [asRule]; exact zero
  | hsubst body replacement _ _ => intro zero; rw [asRule]; exact zero
  | hcollection kind elements rest _ => intro zero; rw [asRule]; exact zero

/-- **The atoms that a space without token stores have no token.** -/
theorem tokens_of_mem_storedAtoms (space : Pattern) :
    tokens counted space = 0 → ∀ atom ∈ storedAtoms space, tokens counted atom = 0 := by
  induction space using Pattern.inductionOn with
  | hbvar index => intro _ atom member; simp [storedAtoms] at member
  | hfvar name => intro _ atom member; simp [storedAtoms] at member
  | happly label arguments ih =>
      intro zero atom member
      obtain ⟨-, clean⟩ := tokens_apply_eq_zero_iff.mp zero
      by_cases isAdd : label = "prime-space-add"
      · rw [storedAtoms, if_pos isAdd] at member
        rcases arguments with _ | ⟨stored, _ | ⟨rest, _ | ⟨extra, more⟩⟩⟩
        · simp [storedAtomsList] at member
        · simp [storedAtomsList] at member
        · rw [storedAtomsList] at member
          rcases List.mem_cons.mp member with rfl | inRest
          · exact clean _ (List.mem_cons_self ..)
          · exact ih rest (by simp) (clean rest (by simp)) atom inRest
        · simp [storedAtomsList] at member
      · rw [storedAtoms, if_neg isAdd] at member
        cases member
  | hlambda binder body _ => intro _ atom member; simp [storedAtoms] at member
  | hmultiLambda arity binders body _ => intro _ atom member; simp [storedAtoms] at member
  | hsubst body replacement _ _ => intro _ atom member; simp [storedAtoms] at member
  | hcollection kind elements rest _ => intro _ atom member; simp [storedAtoms] at member

/-- What a stored atom is when it is read as an equation. -/
theorem eq_equation_of_viewEquation {atom left right : Pattern}
    (viewed : MeTTaZero.viewEquation? atom = some (left, right)) :
    atom = .apply "=" [left, right] := by
  unfold MeTTaZero.viewEquation? at viewed
  split at viewed
  · next first second =>
      obtain ⟨rfl, rfl⟩ : first = left ∧ second = right := by simpa using viewed
      rfl
  · cases viewed

/-- The answers of a stored atom without token, for a subject without token,
have no token. -/
theorem tokens_of_mem_atomResults {subject atom : Pattern} (cleanAtom : tokens counted atom = 0)
    (cleanSubject : tokens counted subject = 0) :
    ∀ answer ∈ atomResults subject atom, tokens counted answer = 0 := by
  intro answer member
  unfold atomResults at member
  split at member
  · next left right viewed =>
      obtain rfl := eq_equation_of_viewEquation viewed
      obtain ⟨-, sides⟩ := tokens_apply_eq_zero_iff.mp cleanAtom
      split at member
      · next exact =>
          simp only [Bool.and_eq_true] at exact
          obtain ⟨bindings, matched, rfl⟩ := List.mem_map.mp member
          exact tokens_applyBindings_eq_zero
            (tokens_of_matched (asRule left) exact.1 matched cleanSubject) (asRule right) exact.2
            (tokens_asRule_eq_zero right (sides right (by simp)))
      · cases member
  · cases member

/-- **The answers of a space without token, for a subject without token,
have no token.** -/
theorem tokens_of_mem_matchResults {space subject : Pattern}
    (cleanSpace : tokens counted space = 0) (cleanSubject : tokens counted subject = 0) :
    ∀ answer ∈ matchResults space subject, tokens counted answer = 0 := by
  intro answer member
  obtain ⟨atom, stored, found⟩ := List.mem_flatMap.mp member
  exact tokens_of_mem_atomResults (tokens_of_mem_storedAtoms space cleanSpace atom stored)
    cleanSubject answer found

/-- **Contraction keeps every count that does not count quotation and
dropping.** -/
theorem tokens_contract (quote : counted "prime-quote" = false)
    (drop : counted "prime-drop" = false) (pattern : Pattern) :
    tokens counted (contract pattern) = tokens counted pattern :=
  (ambient_quoteDropOnly.tokens_equiv quote drop
    (equationEquiv_contract silentEvaluator ambient_quoteDropOnly.authored pattern)).symm

/-! ## A step of a member builds no constructor that it was not given -/

/-- **A step of a member of the family, from a pattern without a counted
constructor at a space without one, reaches a pattern without one**, for
every count that does not count quotation and dropping. -/
theorem ambient_stepAt_tokens (quote : counted "prime-quote" = false)
    (drop : counted "prime-drop" = false) {space : Pattern}
    (cleanSpace : tokens counted (contract space) = 0) :
    ∀ (fuel : Nat) {source target : Pattern},
      StepAt (ambientEvaluator space) ambient fuel source target →
        tokens counted source = 0 → tokens counted target = 0 := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
      intro source target step clean
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨-, inner⟩ := tokens_apply_eq_zero_iff.mp (parts _ (List.mem_cons_self ..))
        have cleanBody : tokens counted body = 0 := by
          have abstraction := inner (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        exact tokens_instantiateBVarAt_eq_zero (parts argument (by simp)) body 0 cleanBody
      · obtain ⟨function, argument, next, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        obtain ⟨uncounted, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        refine tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun part inParts => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inParts
        rcases inParts with rfl | rfl
        · exact ih inner (parts function (by simp))
        · exact parts _ (by simp)
      · obtain ⟨function, argument, next, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        obtain ⟨uncounted, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        refine tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun part inParts => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inParts
        rcases inParts with rfl | rfl
        · exact parts _ (by simp)
        · exact ih inner (parts argument (by simp))
      · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        obtain ⟨uncounted, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens counted body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        refine tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun part inParts => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inParts
        rcases inParts with rfl | rfl
        · exact ih inner (parts domain (by simp))
        · rw [tokens]
          exact cleanBody
      · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        obtain ⟨uncounted, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens counted body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        refine tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun part inParts => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inParts
        rcases inParts with rfl | rfl
        · exact parts _ (by simp)
        · rw [tokens]
          exact ih inner cleanBody
      · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        obtain ⟨uncounted, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens counted body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        refine tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun part inParts => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inParts
        rcases inParts with rfl | rfl
        · exact ih inner (parts domain (by simp))
        · rw [tokens]
          exact cleanBody
      · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        obtain ⟨uncounted, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens counted body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        refine tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun part inParts => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inParts
        rcases inParts with rfl | rfl
        · exact parts _ (by simp)
        · rw [tokens]
          exact ih inner cleanBody
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        obtain ⟨-, names⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨-, atoms⟩ := tokens_apply_eq_zero_iff.mp (names (quoted atom) (by simp [quoted]))
        exact atoms atom (by simp)
      · obtain ⟨answer, found, applied⟩ := root_inv matched premises
        rw [applied]
        exact tokens_of_mem_matchResults cleanSpace
          (by rw [tokens_contract quote drop]; exact clean) answer found

/-! ## Typing along an inclusion of constructors -/

/-- **A term of a language is a term of every language that declares its constructors.** -/
theorem hasType_of_terms_subset {small large : LanguageDef}
    (subset : ∀ rule ∈ small.terms, rule ∈ large.terms) {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType small free bound pattern type) : HasType large free bound pattern type :=
  HasType.of_terms_subset (fun rule member => subset rule member) typed

theorem argumentsHaveTypes_of_terms_subset {small large : LanguageDef}
    (subset : ∀ rule ∈ small.terms, rule ∈ large.terms) {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes small free bound arguments parameters) :
    ArgumentsHaveTypes large free bound arguments parameters :=
  ArgumentsHaveTypes.of_terms_subset (fun rule member => subset rule member) typed

theorem elementsHaveType_of_terms_subset {small large : LanguageDef}
    (subset : ∀ rule ∈ small.terms, rule ∈ large.terms) {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
    (typed : ElementsHaveType small free bound elements elementType) :
    ElementsHaveType large free bound elements elementType :=
  ElementsHaveType.of_terms_subset (fun rule member => subset rule member) typed

/-- A term of a language is a term of every language that declares its
constructors. -/
theorem wellSorted_of_terms_subset {small large : LanguageDef}
    (subset : ∀ rule ∈ small.terms, rule ∈ large.terms) {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (sorted : OpenPatternWellSorted small free bound type pattern) :
    OpenPatternWellSorted large free bound type pattern :=
  ⟨hasType_of_terms_subset subset sorted.1, sorted.2.1, sorted.2.2.1, sorted.2.2.2⟩

mutual
  /-- **A term without a counted constructor is a term of every language that
  declares the constructors that are not counted**, when no constructor is a
  bare collection. -/
  theorem hasType_of_tokens_eq_zero {large small : LanguageDef}
      (kept : ∀ rule ∈ large.terms, counted rule.label = false → rule ∈ small.terms)
      (plain : ∀ rule ∈ large.terms, usesBareCollection? rule = false)
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType large free bound pattern type) (clean : tokens counted pattern = 0) :
      HasType small free bound pattern type := by
    cases typed with
    | bvar found => exact .bvar found
    | fvar found => exact .fvar found
    | @constructor _ rule arguments member notBare argumentsTyped =>
        obtain ⟨uncounted, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        exact .constructor (kept rule member uncounted) notBare
          (argumentsHaveTypes_of_tokens_eq_zero kept plain argumentsTyped
            (tokensList_eq_zero parts))
    | lambda bodyTyped =>
        exact .lambda (hasType_of_tokens_eq_zero kept plain bodyTyped (by rwa [tokens] at clean))
    | multiLambda bodyTyped =>
        exact .multiLambda
          (hasType_of_tokens_eq_zero kept plain bodyTyped (by rwa [tokens] at clean))
    | subst bodyTyped replacementTyped =>
        rw [tokens] at clean
        exact .subst (hasType_of_tokens_eq_zero kept plain bodyTyped (by omega))
          (hasType_of_tokens_eq_zero kept plain replacementTyped (by omega))
    | collection elementsTyped =>
        exact .collection
          (elementsHaveType_of_tokens_eq_zero kept plain elementsTyped
            (by rwa [tokens] at clean))
    | collectionConstructor member shape elementsTyped =>
        have bare := (usesBareCollection?_eq_true_iff _).mpr ⟨_, _, _, shape⟩
        rw [plain _ member] at bare
        cases bare

  theorem argumentsHaveTypes_of_tokens_eq_zero {large small : LanguageDef}
      (kept : ∀ rule ∈ large.terms, counted rule.label = false → rule ∈ small.terms)
      (plain : ∀ rule ∈ large.terms, usesBareCollection? rule = false)
      {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes large free bound arguments parameters)
      (clean : tokensList counted arguments = 0) :
      ArgumentsHaveTypes small free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation expectedType argumentTyped argumentsTyped =>
        rw [tokensList] at clean
        exact .cons representation expectedType
          (hasType_of_tokens_eq_zero kept plain argumentTyped (by omega))
          (argumentsHaveTypes_of_tokens_eq_zero kept plain argumentsTyped (by omega))

  theorem elementsHaveType_of_tokens_eq_zero {large small : LanguageDef}
      (kept : ∀ rule ∈ large.terms, counted rule.label = false → rule ∈ small.terms)
      (plain : ∀ rule ∈ large.terms, usesBareCollection? rule = false)
      {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType large free bound elements elementType)
      (clean : tokensList counted elements = 0) :
      ElementsHaveType small free bound elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        rw [tokensList] at clean
        exact .cons (hasType_of_tokens_eq_zero kept plain elementTyped (by omega))
          (elementsHaveType_of_tokens_eq_zero kept plain elementsTyped (by omega))
end

/-- A term without a counted constructor is a term of every language that
declares the constructors that are not counted. -/
theorem wellSorted_of_tokens_eq_zero {large small : LanguageDef}
    (kept : ∀ rule ∈ large.terms, counted rule.label = false → rule ∈ small.terms)
    (plain : ∀ rule ∈ large.terms, usesBareCollection? rule = false)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (sorted : OpenPatternWellSorted large free bound type pattern)
    (clean : tokens counted pattern = 0) : OpenPatternWellSorted small free bound type pattern :=
  ⟨hasType_of_tokens_eq_zero kept plain sorted.1 clean, sorted.2.1, sorted.2.2.1, sorted.2.2.2⟩

mutual
  /-- **A term of a language none of whose constructors is counted has no
  counted constructor.** -/
  theorem tokens_eq_zero_of_hasType {lang : LanguageDef}
      (absent : ∀ rule ∈ lang.terms, counted rule.label = false) {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType lang free bound pattern type) (object : isObjectPattern pattern = true) :
      tokens counted pattern = 0 := by
    cases typed with
    | bvar _ => rfl
    | fvar _ => rfl
    | @constructor _ rule arguments member _ argumentsTyped =>
        exact tokens_apply_eq_zero_iff.mpr ⟨absent rule member,
          tokens_eq_zero_of_mem (tokensList_eq_zero_of_arguments absent argumentsTyped
            (by simpa [isObjectPattern] using object))⟩
    | lambda bodyTyped =>
        rw [tokens]
        exact tokens_eq_zero_of_hasType absent bodyTyped (by simpa [isObjectPattern] using object)
    | multiLambda bodyTyped =>
        rw [tokens]
        exact tokens_eq_zero_of_hasType absent bodyTyped (by simpa [isObjectPattern] using object)
    | subst _ _ => simp [isObjectPattern] at object
    | collection elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        rw [tokens]
        exact tokensList_eq_zero_of_elements absent elementsTyped object.2
    | collectionConstructor _ _ elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        rw [tokens]
        exact tokensList_eq_zero_of_elements absent elementsTyped object.2

  theorem tokensList_eq_zero_of_arguments {lang : LanguageDef}
      (absent : ∀ rule ∈ lang.terms, counted rule.label = false) {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes lang free bound arguments parameters)
      (object : isObjectPatternList arguments = true) : tokensList counted arguments = 0 := by
    cases typed with
    | nil => rfl
    | cons _ _ argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        rw [tokensList, tokens_eq_zero_of_hasType absent argumentTyped object.1,
          tokensList_eq_zero_of_arguments absent argumentsTyped object.2]

  theorem tokensList_eq_zero_of_elements {lang : LanguageDef}
      (absent : ∀ rule ∈ lang.terms, counted rule.label = false) {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType lang free bound elements elementType)
      (object : isObjectPatternList elements = true) : tokensList counted elements = 0 := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        rw [tokensList, tokens_eq_zero_of_hasType absent elementTyped object.1,
          tokensList_eq_zero_of_elements absent elementsTyped object.2]
end

#print axioms tokens_liftBVars_eq_zero
#print axioms tokens_instantiateBVarAt_eq_zero
#print axioms mem_of_mergeBindings
#print axioms tokens_of_matched
#print axioms tokens_applyBindings_eq_zero
#print axioms tokens_asRule_eq_zero
#print axioms tokens_of_mem_storedAtoms
#print axioms tokens_of_mem_matchResults
#print axioms tokens_contract
#print axioms ambient_stepAt_tokens
#print axioms wellSorted_of_terms_subset
#print axioms wellSorted_of_tokens_eq_zero
#print axioms tokens_eq_zero_of_hasType

end Mettapedia.Logic.HostingStyles.AmbientSpace
