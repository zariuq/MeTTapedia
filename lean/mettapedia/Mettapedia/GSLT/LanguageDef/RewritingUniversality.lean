import Mettapedia.GSLT.LanguageDef.PartialRecursivePresentation
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement
import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.EngineCoded.Bindings
import Mettapedia.OSLF.MeTTaIL.EngineCoded.RuleApplication
import Mettapedia.OSLF.MeTTaIL.EngineCoded.ReferenceSteps

/-!
# Every recursively enumerable relation is a step relation

The step relations of languages are exactly the recursively enumerable relations. A relation on
numbers is recursively enumerable exactly when some language, with no relation environment, steps each
numeral exactly to the numerals it is related to (`re_iff_steps`). One direction is the enumerability of
the reference relation (`EngineCoded.referenceStep_enumerable`); this file proves the other
(`every_re_relation_steps`).

The language of a code `c` (`universal c`) has three kinds of rules:
- **generators**: a term `numerals` steps to every numeral and a term `codes` to every code;
- **the inference rules of partial recursive functions** (`PartialRecursive.rules`), each as a rewrite
  rule: its conclusion steps to `true` when its metavariables are generated values of their sorts and
  every premise steps to `true` (`judgmentRule`);
- **the relation of the code**: a numeral `m` steps to a numeral `n` when `pair m n`, computed by a
  premise, is an input on which `c` halts (`relationRule`).

Every step is a generated value, a true judgment stepping to `true`, or a related pair of numerals
(`sound`); every true judgment steps to `true`, since stepping to `true` is closed under the rule
instances at values (`judgments_closed` with `PartialRecursive.holds_closed`); and related numerals step
(`relation_complete`). The rules are binder-free, so the contextual and reference relations agree
(`profile`).

Instances of first-order schemas behave as substitutions: instantiating a schema depends only on
what its metavariables are bound to (`schema_congr`), a match of a schema keeps its value under any
extension of its bindings (`schema_extends`), and a schema matches each of its instances with bindings
that agree with the instance (`schema_match_complete`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RewritingUniversality

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

/-! ## Bindings -/

/-- One binding list extends another: every name the first binds, the second binds to the same value. -/
def Extends (smaller larger : Bindings) : Prop :=
  ∀ (name : String) (value : Pattern), smaller.find? (·.1 == name) = some (name, value) →
    larger.find? (·.1 == name) = some (name, value)

theorem Extends.refl (bindings : Bindings) : Extends bindings bindings := fun _ _ found => found

theorem Extends.trans {first second third : Bindings} (lower : Extends first second) (upper : Extends second third) :
    Extends first third := fun name value found => upper name value (lower name value found)

theorem Extends.of_merge_left {first second result : Bindings} (merged : mergeBindings first second = some result) :
    Extends first result := fun _ _ found => Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_left merged found

theorem Extends.of_merge_right {first second result : Bindings} (merged : mergeBindings first second = some result) :
    Extends second result := fun _ _ found => Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_right merged found

theorem find?_key {bindings : Bindings} {name : String} {entry : String × Pattern}
    (found : bindings.find? (·.1 == name) = some entry) : entry = (name, entry.2) := by
  have keyed := List.find?_some found
  simp only [beq_iff_eq] at keyed
  rw [← keyed]

theorem applyBindings_fvar_of_find? {bindings : Bindings} {name : String} {value : Pattern}
    (found : bindings.find? (·.1 == name) = some (name, value)) : applyBindings bindings (.fvar name) = value := by
  simp [applyBindings, found]

theorem find?_zip_map (f : String → Pattern) : ∀ (names : List String) {name : String}, name ∈ names →
    (names.zip (names.map f)).find? (·.1 == name) = some (name, f name)
  | [], _, member => absurd member List.not_mem_nil
  | first :: rest, name, member => by
      by_cases same : first = name
      · subst same
        simp
      · have later : name ∈ rest := (List.mem_cons.mp member).resolve_left fun equal => same equal.symm
        simp [same, find?_zip_map f rest later]

/-- The values a binding list gives to names; a name it does not bind stands for itself. -/
def valuesOf (bindings : Bindings) (names : List String) : List Pattern :=
  names.map fun name => applyBindings bindings (.fvar name)

/-- Bindings agree with a substitution: every entry gives a name the value the substitution gives it. -/
def AgreesWith (bindings substitution : Bindings) : Prop :=
  ∀ entry ∈ bindings, applyBindings substitution (.fvar entry.1) = entry.2

theorem AgreesWith.find? {bindings substitution : Bindings} (agrees : AgreesWith bindings substitution)
    {name : String} {value : Pattern} (found : bindings.find? (·.1 == name) = some (name, value)) :
    applyBindings substitution (.fvar name) = value :=
  agrees _ (List.mem_of_find?_eq_some found)

/-- **Merging bindings that agree with one substitution succeeds and agrees with it.** -/
theorem merge_agrees {substitution : Bindings} :
    ∀ (second first : Bindings), AgreesWith first substitution → AgreesWith second substitution →
      ∃ result, mergeBindings first second = some result ∧ AgreesWith result substitution
  | [], first, agreesFirst, _ => ⟨first, by simp [mergeBindings], agreesFirst⟩
  | (name, value) :: rest, first, agreesFirst, agreesSecond => by
      have agreesRest : AgreesWith rest substitution := fun entry member =>
        agreesSecond entry (List.mem_cons_of_mem _ member)
      have headValue : applyBindings substitution (.fvar name) = value := agreesSecond _ List.mem_cons_self
      rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeBindings_eq, List.foldl_cons, Option.bind_some]
      cases found : first.find? (·.1 == name) with
      | none =>
          have headStep : Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeEntry first (name, value) =
              some ((name, value) :: first) := by
            unfold Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeEntry
            rw [found]
          rw [headStep, ← Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeBindings_eq]
          refine merge_agrees rest ((name, value) :: first) (fun entry member => ?_) agreesRest
          rcases List.mem_cons.mp member with same | inFirst
          · rw [same]; exact headValue
          · exact agreesFirst entry inFirst
      | some entry =>
          have keyed := find?_key found
          have existing : applyBindings substitution (.fvar name) = entry.2 := by
            have agreed := agreesFirst entry (List.mem_of_find?_eq_some found)
            rw [keyed] at agreed
            exact agreed
          have equal : (entry.2 == value) = true := by rw [← existing, headValue]; exact beq_self_eq_true _
          have headStep : Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeEntry first (name, value) = some first := by
            unfold Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeEntry
            rw [found]
            exact if_pos equal
          rw [headStep, ← Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeBindings_eq]
          exact merge_agrees rest first agreesFirst agreesRest

/-! ## Schemas -/

mutual
  /-- **Instantiating a schema depends only on its metavariables' values.** -/
  theorem schema_congr {names : List String} {pattern : Pattern} (schema : Schema names pattern)
      {first second : Bindings}
      (same : ∀ name ∈ names, applyBindings first (.fvar name) = applyBindings second (.fvar name)) :
      applyBindings first pattern = applyBindings second pattern := by
    cases schema with
    | metavariable member => exact same _ member
    | constructor arguments =>
        simp only [applyBindings]
        rw [schemas_congr arguments same]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem schemas_congr {names : List String} {patterns : List Pattern} (schemas : Schemas names patterns)
      {first second : Bindings}
      (same : ∀ name ∈ names, applyBindings first (.fvar name) = applyBindings second (.fvar name)) :
      patterns.map (applyBindings first) = patterns.map (applyBindings second) := by
    cases schemas with
    | nil => rfl
    | cons head tail => simp only [List.map_cons, schema_congr head same, schemas_congr tail same]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- A schema instantiated by its metavariables' values under some bindings is instantiated by them. -/
theorem schema_valuesOf {names : List String} {pattern : Pattern} (schema : Schema names pattern)
    (bindings : Bindings) :
    applyBindings (names.zip (valuesOf bindings names)) pattern = applyBindings bindings pattern :=
  schema_congr schema fun name member => by
    unfold valuesOf
    rw [applyBindings_fvar_of_find? (find?_zip_map _ names member)]

theorem schemas_valuesOf {names : List String} {patterns : List Pattern} (schemas : Schemas names patterns)
    (bindings : Bindings) :
    patterns.map (applyBindings (names.zip (valuesOf bindings names))) = patterns.map (applyBindings bindings) :=
  schemas_congr schemas fun name member => by
    unfold valuesOf
    rw [applyBindings_fvar_of_find? (find?_zip_map _ names member)]

theorem mem_matchArgs_cons {pattern : Pattern} {patterns : List Pattern} {term : Pattern} {terms : List Pattern}
    {bindings : Bindings} (found : bindings ∈ matchArgs (pattern :: patterns) (term :: terms)) :
    ∃ head ∈ matchPattern pattern term, ∃ tail ∈ matchArgs patterns terms, mergeBindings head tail = some bindings := by
  rw [matchArgs] at found
  simp only [List.mem_flatMap, List.mem_filterMap] at found
  obtain ⟨head, inHead, tail, inTail, merged⟩ := found
  exact ⟨head, inHead, tail, inTail, merged⟩

mutual
  /-- **A match of a schema keeps its value under any extension of its bindings.** -/
  theorem schema_extends {names : List String} {pattern : Pattern} (schema : Schema names pattern)
      {term : Pattern} {matched larger : Bindings} (found : matched ∈ matchPattern pattern term)
      (extended : Extends matched larger) :
      applyBindings larger pattern = applyBindings matched pattern := by
    cases schema with
    | metavariable member =>
        rename_i name
        have single : matched = [(name, term)] := by simpa [matchPattern] using found
        subst single
        rw [applyBindings_fvar_of_find? (extended name term (by simp)),
          applyBindings_fvar_of_find? (by simp : [(name, term)].find? (·.1 == name) = some (name, term))]
    | constructor arguments =>
        rename_i label patterns
        cases term with
        | apply label' terms =>
            simp only [matchPattern] at found
            split at found
            · simp only [applyBindings]
              rw [schemas_extends arguments found extended]
            · simp at found
        | _ => simp [matchPattern] at found
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem schemas_extends {names : List String} {patterns : List Pattern} (schemas : Schemas names patterns)
      {terms : List Pattern} {matched larger : Bindings} (found : matched ∈ matchArgs patterns terms)
      (extended : Extends matched larger) :
      patterns.map (applyBindings larger) = patterns.map (applyBindings matched) := by
    cases schemas with
    | nil => rfl
    | cons head tail =>
        rename_i pattern rest
        cases terms with
        | nil => simp [matchArgs] at found
        | cons term terms =>
            obtain ⟨headBindings, inHead, tailBindings, inTail, merged⟩ := mem_matchArgs_cons found
            have headExt := Extends.of_merge_left merged
            have tailExt := Extends.of_merge_right merged
            simp only [List.map_cons]
            rw [schema_extends head inHead (headExt.trans extended), schema_extends head inHead headExt,
              schemas_extends tail inTail (tailExt.trans extended), schemas_extends tail inTail tailExt]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- **A schema matches each of its instances** with bindings that agree with the instance. -/
  theorem schema_match_complete {names : List String} {pattern : Pattern} (schema : Schema names pattern)
      (substitution : Bindings) :
      ∃ matched ∈ matchPattern pattern (applyBindings substitution pattern), AgreesWith matched substitution := by
    cases schema with
    | metavariable member =>
        rename_i name
        refine ⟨[(name, applyBindings substitution (.fvar name))], by simp [matchPattern], ?_⟩
        intro entry inside
        rw [List.mem_singleton.mp inside]
    | constructor arguments =>
        rename_i label patterns
        obtain ⟨matched, inArgs, agrees⟩ := schemas_match_complete arguments substitution
        refine ⟨matched, ?_, agrees⟩
        simp only [applyBindings, matchPattern, beq_self_eq_true, List.length_map, Bool.and_self, if_true]
        exact inArgs
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem schemas_match_complete {names : List String} {patterns : List Pattern} (schemas : Schemas names patterns)
      (substitution : Bindings) :
      ∃ matched ∈ matchArgs patterns (patterns.map (applyBindings substitution)), AgreesWith matched substitution := by
    cases schemas with
    | nil => exact ⟨[], by simp [matchArgs], fun _ inside => absurd inside List.not_mem_nil⟩
    | cons head tail =>
        obtain ⟨headBindings, inHead, agreesHead⟩ := schema_match_complete head substitution
        obtain ⟨tailBindings, inTail, agreesTail⟩ := schemas_match_complete tail substitution
        obtain ⟨result, merged, agrees⟩ := merge_agrees tailBindings headBindings agreesHead agreesTail
        refine ⟨result, ?_, agrees⟩
        rw [List.map_cons, matchArgs]
        simp only [List.mem_flatMap, List.mem_filterMap]
        exact ⟨headBindings, inHead, tailBindings, inTail, merged⟩
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- A schema's match instantiates it to the matched term. -/
  theorem schema_match_sound {names : List String} {pattern : Pattern} (schema : Schema names pattern)
      {term : Pattern} {matched : Bindings} (found : matched ∈ matchPattern pattern term) :
      applyBindings matched pattern = term := by
    cases schema with
    | metavariable member =>
        rename_i name
        have single : matched = [(name, term)] := by simpa [matchPattern] using found
        subst single
        exact applyBindings_fvar_of_find? (by simp)
    | constructor arguments =>
        rename_i label patterns
        cases term with
        | apply label' terms =>
            simp only [matchPattern] at found
            split at found
            · rename_i same
              simp only [Bool.and_eq_true, beq_iff_eq] at same
              simp only [applyBindings, same.1, schemas_match_sound arguments found]
            · simp at found
        | _ => simp [matchPattern] at found
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem schemas_match_sound {names : List String} {patterns : List Pattern} (schemas : Schemas names patterns)
      {terms : List Pattern} {matched : Bindings} (found : matched ∈ matchArgs patterns terms) :
      patterns.map (applyBindings matched) = terms := by
    cases schemas with
    | nil =>
        cases terms with
        | nil => rfl
        | cons _ _ => simp [matchArgs] at found
    | cons head tail =>
        cases terms with
        | nil => simp [matchArgs] at found
        | cons term terms =>
            obtain ⟨headBindings, inHead, tailBindings, inTail, merged⟩ := mem_matchArgs_cons found
            simp only [List.map_cons]
            rw [schema_extends head inHead (Extends.of_merge_left merged), schema_match_sound head inHead,
              schemas_extends tail inTail (Extends.of_merge_right merged), schemas_match_sound tail inTail]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## The language -/

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.PartialRecursive
open Nat.Partrec (Code)

/-- The judgment that holds. -/
def trueP : Pattern := .apply "true" []

/-- A term that steps to every numeral. -/
def numeralsP : Pattern := .apply "numerals" []

/-- A term that steps to every code. -/
def codesP : Pattern := .apply "codes" []

/-- The term that steps to every closed value of a sort. -/
def valuesP (sort : TypeExpr) : Pattern := if sort = codeSort then codesP else numeralsP

/-- A rule whose premises give its metavariables values. -/
def valueRule (name : String) (left : Pattern) (values : List (String × Pattern)) (right : Pattern) :
    RewriteRule :=
  { name := name, typeContext := [], premises := values.map fun entry => .congruence entry.2 (mv entry.1),
    left := left, right := right }

/-- The numerals and the codes. -/
def generatorRules : List RewriteRule :=
  [valueRule "numeralsZero" numeralsP [] zeroP,
   valueRule "numeralsSucc" numeralsP [("x", numeralsP)] (succP (mv "x")),
   valueRule "codesZero" codesP [] czeroP,
   valueRule "codesSucc" codesP [] csuccP,
   valueRule "codesLeft" codesP [] cleftP,
   valueRule "codesRight" codesP [] crightP,
   valueRule "codesPair" codesP [("f", codesP), ("g", codesP)] (cpairP (mv "f") (mv "g")),
   valueRule "codesComp" codesP [("f", codesP), ("g", codesP)] (ccompP (mv "f") (mv "g")),
   valueRule "codesPrec" codesP [("f", codesP), ("g", codesP)] (cprecP (mv "f") (mv "g")),
   valueRule "codesSearch" codesP [("f", codesP)] (crfindP (mv "f"))]

/-- The premises that give every metavariable of an inference rule a closed value of its sort. -/
def valuePremises (rule : SortedFirstOrderRules.Rule) : List Premise :=
  (rule.row.vars.zip rule.variableTypes).map fun entry => .congruence (valuesP entry.2) (mv entry.1)

/-- **An inference rule as a rewrite rule**: its conclusion steps to `true` when its metavariables are
closed values of their sorts and every premise steps to `true`. -/
def judgmentRule (rule : SortedFirstOrderRules.Rule) : RewriteRule :=
  { name := rule.row.id, typeContext := [],
    premises := valuePremises rule ++ rule.row.premises.map fun premise => .congruence premise trueP,
    left := rule.row.conclusion, right := trueP }

/-- **The relation of a code**: a numeral steps to a numeral when the code halts on their pair. -/
def relationRule (c : Code) : RewriteRule :=
  { name := "relation", typeContext := [],
    premises := [.congruence numeralsP (mv "x"), .congruence numeralsP (mv "y"), .congruence numeralsP (mv "p"),
      .congruence (pairP (mv "x") (mv "y") (mv "p")) trueP, .congruence (haltsP (codePattern c) (mv "p")) trueP],
    left := mv "x", right := mv "y" }

/-- The language of a code: the numerals, the codes, the inference rules of partial recursive functions,
and the relation of the code. -/
def universal (c : Code) : LanguageDef :=
  { language with equations := [], rewrites := generatorRules ++ rules.map judgmentRule ++ [relationRule c] }

/-- The steps of the language, with no relation environment. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

theorem rules_schemas : ∀ rule ∈ rules,
    Schema rule.row.vars rule.row.conclusion ∧ Schemas rule.row.vars rule.row.premises ∧ rule.row.vars.Nodup := by
  have checked : rules.all (fun rule => checkSchema rule.row.vars rule.row.conclusion &&
      checkSchemas rule.row.vars rule.row.premises && decide rule.row.vars.Nodup) = true := by decide +kernel
  intro rule member
  have all := List.all_eq_true.mp checked rule member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at all
  exact ⟨(checkSchema_iff _ _).mp all.1.1, (checkSchemas_iff _ _).mp all.1.2, all.2⟩

/-! ## Facts about the terms -/

@[simp] theorem applyBindings_closed (bindings : Bindings) (name : String) :
    applyBindings bindings (.apply name []) = .apply name [] := by
  simp [applyBindings]

theorem num_head : ∀ n : ℕ, ∃ label arguments, num n = .apply label arguments ∧ (label = "zero" ∨ label = "succ")
  | 0 => ⟨"zero", [], rfl, .inl rfl⟩
  | n + 1 => ⟨"succ", [num n], rfl, .inr rfl⟩

theorem codePattern_head : ∀ code : Code, ∃ label arguments, codePattern code = .apply label arguments ∧
    label ∈ ["czero", "csucc", "cleft", "cright", "cpair", "ccomp", "cprec", "crfind"]
  | .zero => ⟨_, _, rfl, by simp⟩
  | .succ => ⟨_, _, rfl, by simp⟩
  | .left => ⟨_, _, rfl, by simp⟩
  | .right => ⟨_, _, rfl, by simp⟩
  | .pair _ _ => ⟨_, _, rfl, by simp⟩
  | .comp _ _ => ⟨_, _, rfl, by simp⟩
  | .prec _ _ => ⟨_, _, rfl, by simp⟩
  | .rfind' _ => ⟨_, _, rfl, by simp⟩

theorem num_ne_apply {n : ℕ} {label : String} {arguments : List Pattern}
    (other : label ≠ "zero" ∧ label ≠ "succ") : num n ≠ .apply label arguments := by
  obtain ⟨head, rest, same, named⟩ := num_head n
  rw [same]
  intro equal
  injection equal with labels
  rcases named with rfl | rfl
  · exact other.1 labels.symm
  · exact other.2 labels.symm

theorem codePattern_ne_trueP (code : Code) : codePattern code ≠ trueP := by
  obtain ⟨head, rest, same, named⟩ := codePattern_head code
  rw [same, trueP]
  intro equal
  injection equal with labels
  subst labels
  simp at named

theorem num_injective : Function.Injective num := by
  intro first
  induction first with
  | zero => intro second same; cases second with
    | zero => rfl
    | succ _ => simp [num, zeroP, succP] at same
  | succ first ih => intro second same; cases second with
    | zero => simp [num, zeroP, succP] at same
    | succ second => simp only [num, succP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
                     rw [ih same]

theorem valid_num (n : ℕ) : ¬ Valid (num n) := by
  cases n <;> simp [num, zeroP, succP, Valid]

theorem applyBindingsForRule_plain (rule : RewriteRule) (bindings : Bindings) (free : binderFree rule.right = true)
    (c : Code) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule (universal c) rule bindings =
      applyBindings bindings rule.right := by
  rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.applyBindingsForRule_eq]
  exact applyBindingsScoped_zero_of_binderFree rule.left bindings rule.right free

theorem single_merge {bindings result : Bindings} {name : String} {value : Pattern}
    (merged : mergeBindings bindings [(name, value)] = some result) :
    Extends bindings result ∧ result.find? (·.1 == name) = some (name, value) :=
  ⟨Extends.of_merge_left merged, Extends.of_merge_right merged name value (by simp)⟩

theorem extends_fvar {smaller larger : Bindings} (extended : Extends smaller larger) {name : String}
    {value : Pattern} (bound : smaller.find? (·.1 == name) = some (name, value)) :
    applyBindings larger (.fvar name) = value :=
  applyBindings_fvar_of_find? (extended name value bound)

theorem applyBindings_apply' (bindings : Bindings) (label : String) (arguments : List Pattern) :
    applyBindings bindings (.apply label arguments) = .apply label (arguments.map (applyBindings bindings)) := by
  simp [applyBindings]

theorem applyBindings_codePattern (bindings : Bindings) : ∀ code : Code,
    applyBindings bindings (codePattern code) = codePattern code
  | .zero | .succ | .left | .right => applyBindings_closed _ _
  | .pair f g | .comp f g | .prec f g => by
      simp only [codePattern, cpairP, ccompP, cprecP, applyBindings_apply', List.map_cons, List.map_nil,
        applyBindings_codePattern bindings f, applyBindings_codePattern bindings g]
  | .rfind' f => by
      simp only [codePattern, crfindP, applyBindings_apply', List.map_cons, List.map_nil,
        applyBindings_codePattern bindings f]

theorem matchPattern_closed {name : String} {candidate : Pattern} {bindings : Bindings}
    (found : bindings ∈ matchPattern (.apply name []) candidate) : candidate = .apply name [] ∧ bindings = [] := by
  cases candidate with
  | apply label arguments =>
      simp only [matchPattern] at found
      split at found
      · rename_i same
        simp only [Bool.and_eq_true, beq_iff_eq] at same
        obtain ⟨rfl, lengths⟩ := same
        cases arguments with
        | nil =>
            simp only [matchArgs, List.mem_singleton] at found
            exact ⟨rfl, found⟩
        | cons _ _ => simp at lengths
      · simp at found
  | _ => simp [matchPattern] at found

theorem matchPattern_mv {name : String} {candidate : Pattern} {bindings : Bindings}
    (found : bindings ∈ matchPattern (mv name) candidate) : bindings = [(name, candidate)] := by
  simpa [mv, matchPattern] using found

/-! ## What a step can be -/

/-- **What a step of the language can be**: a numeral or a code generated, a true judgment stepping to
`true`, or two numerals related by the code. -/
def Spec (c : Code) (source target : Pattern) : Prop :=
  (source = numeralsP ∧ ∃ n, target = num n) ∨ (source = codesP ∧ ∃ code, target = codePattern code) ∨
    (target = trueP ∧ Valid source) ∨ ∃ m n, source = num m ∧ target = num n ∧ (c.eval (Nat.pair m n)).Dom

theorem spec_numerals {c : Code} {target : Pattern} (spec : Spec c numeralsP target) : ∃ n, target = num n := by
  rcases spec with ⟨_, found⟩ | ⟨same, _⟩ | ⟨_, valid⟩ | ⟨m, n, same, _, _⟩
  · exact found
  · simp [numeralsP, codesP] at same
  · simp [numeralsP, Valid] at valid
  · exact absurd same.symm (num_ne_apply ⟨by decide, by decide⟩)

theorem spec_codes {c : Code} {target : Pattern} (spec : Spec c codesP target) : ∃ code, target = codePattern code := by
  rcases spec with ⟨same, _⟩ | ⟨_, found⟩ | ⟨_, valid⟩ | ⟨m, n, same, _, _⟩
  · simp [numeralsP, codesP] at same
  · exact found
  · simp [codesP, Valid] at valid
  · exact absurd same.symm (num_ne_apply ⟨by decide, by decide⟩)

theorem spec_true {c : Code} {source : Pattern} (spec : Spec c source trueP) : Valid source := by
  rcases spec with ⟨_, n, same⟩ | ⟨_, code, same⟩ | ⟨_, valid⟩ | ⟨m, n, _, same, _⟩
  · exact absurd same.symm (num_ne_apply ⟨by decide, by decide⟩)
  · exact absurd same.symm (codePattern_ne_trueP code)
  · exact valid
  · exact absurd same.symm (num_ne_apply ⟨by decide, by decide⟩)

variable (c : Code)

theorem premisesAt_append {fuel : ℕ} : ∀ {first second : List Premise} {initial final : Bindings},
    PremisesAt base (universal c) fuel initial (first ++ second) final →
      ∃ middle, PremisesAt base (universal c) fuel initial first middle ∧
        PremisesAt base (universal c) fuel middle second final
  | [], _, initial, _, evidence => ⟨initial, .nil initial, evidence⟩
  | _ :: _, _, _, _, evidence => by
      cases evidence with
      | cons head tail =>
          obtain ⟨middle, before, after⟩ := premisesAt_append tail
          exact ⟨middle, .cons head before, after⟩

/-- Congruence premises only extend the bindings. -/
theorem extends_of_congruences {fuel : ℕ} : ∀ {premises : List Premise} {initial final : Bindings},
    (∀ premise ∈ premises, ∃ source target, premise = .congruence source target) →
    PremisesAt base (universal c) fuel initial premises final → Extends initial final
  | [], _, _, _, evidence => by cases evidence; exact Extends.refl _
  | premise :: premises, initial, final, congruences, evidence => by
      cases evidence with
      | cons head tail =>
          obtain ⟨source, target, rfl⟩ := congruences premise List.mem_cons_self
          cases head with
          | congruence _ _ merged =>
              exact (Extends.of_merge_left merged).trans
                (extends_of_congruences (fun other inside => congruences other (List.mem_cons_of_mem _ inside)) tail)

/-- Premises that step to `true` keep the bindings, and each of their instances steps to `true`. -/
theorem truePremises {fuel : ℕ} : ∀ {patterns : List Pattern} {initial final : Bindings},
    PremisesAt base (universal c) fuel initial (patterns.map fun pattern => .congruence pattern trueP) final →
      final = initial ∧ ∀ pattern ∈ patterns, StepAt base (universal c) fuel (applyBindings initial pattern) trueP
  | [], _, _, evidence => by
      cases evidence
      exact ⟨rfl, fun _ inside => absurd inside List.not_mem_nil⟩
  | pattern :: patterns, initial, final, evidence => by
      cases evidence with
      | cons head tail =>
          cases head with
          | congruence step matched merged =>
              obtain ⟨rfl, rfl⟩ := matchPattern_closed matched
              simp only [mergeBindings, List.foldlM_nil, pure, Option.some.injEq] at merged
              subst merged
              obtain ⟨kept, steps⟩ := truePremises tail
              refine ⟨kept, fun other inside => ?_⟩
              rcases List.mem_cons.mp inside with rfl | later
              · exact step
              · exact steps other later

section Soundness

variable {c}
variable {fuel : ℕ} (ih : ∀ {source target : Pattern}, StepAt base (universal c) fuel source target → Spec c source target)
include ih

theorem numeralPremise {bindings result : Bindings} {name : String}
    (evidence : PremiseAt base (universal c) fuel bindings (.congruence numeralsP (mv name)) result) :
    ∃ n, Extends bindings result ∧ result.find? (·.1 == name) = some (name, num n) := by
  cases evidence with
  | congruence step matched merged =>
      have spec := ih step
      rw [show applyBindings bindings numeralsP = numeralsP from applyBindings_closed _ _] at spec
      obtain ⟨n, rfl⟩ := spec_numerals spec
      rw [matchPattern_mv matched] at merged
      exact ⟨n, single_merge merged⟩

theorem codePremise {bindings result : Bindings} {name : String}
    (evidence : PremiseAt base (universal c) fuel bindings (.congruence codesP (mv name)) result) :
    ∃ code, Extends bindings result ∧ result.find? (·.1 == name) = some (name, codePattern code) := by
  cases evidence with
  | congruence step matched merged =>
      have spec := ih step
      rw [show applyBindings bindings codesP = codesP from applyBindings_closed _ _] at spec
      obtain ⟨code, rfl⟩ := spec_codes spec
      rw [matchPattern_mv matched] at merged
      exact ⟨code, single_merge merged⟩

theorem truePremise {bindings result : Bindings} {pattern : Pattern}
    (evidence : PremiseAt base (universal c) fuel bindings (.congruence pattern trueP) result) :
    result = bindings ∧ Valid (applyBindings bindings pattern) := by
  cases evidence with
  | congruence step matched merged =>
      obtain ⟨rfl, rfl⟩ := matchPattern_closed matched
      simp only [mergeBindings, List.foldlM_nil, pure, Option.some.injEq] at merged
      exact ⟨merged.symm, spec_true (ih step)⟩

/-- Two code premises bind their names to codes. -/
theorem twoCodes {first second : String} {final : Bindings}
    (premises : PremisesAt base (universal c) fuel []
      [.congruence codesP (mv first), .congruence codesP (mv second)] final) :
    ∃ f g : Code, applyBindings final (mv first) = codePattern f ∧ applyBindings final (mv second) = codePattern g := by
  cases premises with
  | cons head tail =>
      obtain ⟨f, _, foundF⟩ := codePremise ih head
      cases tail with
      | cons head' tail' =>
          obtain ⟨g, extended, foundG⟩ := codePremise ih head'
          cases tail'
          exact ⟨f, g, extends_fvar extended foundF, applyBindings_fvar_of_find? foundG⟩

/-- **A numeral steps by the relation only to a numeral it is related to.** -/
theorem relation_sound {source : Pattern} {final : Bindings}
    (premises : PremisesAt base (universal c) fuel [("x", source)] (relationRule c).premises final) :
    ∃ m n, source = num m ∧ applyBindings final (mv "y") = num n ∧ (c.eval (Nat.pair m n)).Dom := by
  cases premises with
  | cons p1 t1 =>
  obtain ⟨m, e1, f1⟩ := numeralPremise ih p1
  cases t1 with
  | cons p2 t2 =>
  obtain ⟨n, e2, f2⟩ := numeralPremise ih p2
  cases t2 with
  | cons p3 t3 =>
  obtain ⟨q, e3, f3⟩ := numeralPremise ih p3
  cases t3 with
  | cons p4 t4 =>
  obtain ⟨same4, valid4⟩ := truePremise ih p4
  cases t4 with
  | cons p5 t5 =>
  obtain ⟨same5, valid5⟩ := truePremise ih p5
  cases t5
  subst same5
  subst same4
  have sourceFound : [("x", source)].find? (·.1 == "x") = some ("x", source) := by simp
  have sourceIs : source = num m := by
    have both := e1 "x" source sourceFound
    rw [f1] at both
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at both
    exact both.symm
  have xFound := e3 "x" (num m) (e2 "x" (num m) f1)
  have yFound := e3 "y" (num n) f2
  rw [show applyBindings _ (pairP (mv "x") (mv "y") (mv "p")) = pairP (num m) (num n) (num q) by
    simp only [pairP, mv, applyBindings_apply', List.map_cons, List.map_nil, applyBindings_fvar_of_find? xFound,
      applyBindings_fvar_of_find? yFound, applyBindings_fvar_of_find? f3]] at valid4
  rw [show applyBindings _ (haltsP (codePattern c) (mv "p")) = haltsP (codePattern c) (num q) by
    simp only [haltsP, mv, applyBindings_apply', List.map_cons, List.map_nil, applyBindings_codePattern,
      applyBindings_fvar_of_find? f3]] at valid5
  simp only [valid_pair, natValue_num] at valid4
  simp only [valid_halts, codeValue_codePattern, natValue_num] at valid5
  refine ⟨m, n, sourceIs, applyBindings_fvar_of_find? yFound, ?_⟩
  rw [valid4]
  exact valid5

end Soundness

open Mettapedia.GSLT.LanguageDef.FirstOrderRules (FORule)

/-- **Every step of the language is one of the four kinds of `Spec`.** -/
theorem sound : ∀ (fuel : ℕ) {source target : Pattern},
    StepAt base (universal c) fuel source target → Spec c source target := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
      intro source target step
      cases step with
      | rule member matched premises applied =>
          rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq] at matched
          simp only [universal, List.mem_append, List.mem_map, List.mem_singleton] at member
          rcases member with (generator | ⟨inference, inRules, rfl⟩) | rfl
          · simp only [generatorRules, List.mem_cons, List.not_mem_nil, or_false] at generator
            rcases generator with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              obtain ⟨rfl, rfl⟩ := matchPattern_closed matched <;>
              rw [applyBindingsForRule_plain _ _ rfl] at applied <;>
              simp only [valueRule, List.map_cons, List.map_nil] at premises applied
            · cases premises
              exact Or.inl ⟨rfl, 0, by rw [← applied]; exact applyBindings_closed _ _⟩
            · cases premises with
              | cons head tail =>
                  obtain ⟨n, _, found⟩ := numeralPremise ih head
                  cases tail
                  refine Or.inl ⟨rfl, n + 1, ?_⟩
                  rw [← applied]
                  simp only [succP, mv, applyBindings_apply', List.map_cons, List.map_nil,
                    applyBindings_fvar_of_find? found]
                  rfl
            · cases premises
              exact Or.inr (Or.inl ⟨rfl, .zero, by rw [← applied]; exact applyBindings_closed _ _⟩)
            · cases premises
              exact Or.inr (Or.inl ⟨rfl, .succ, by rw [← applied]; exact applyBindings_closed _ _⟩)
            · cases premises
              exact Or.inr (Or.inl ⟨rfl, .left, by rw [← applied]; exact applyBindings_closed _ _⟩)
            · cases premises
              exact Or.inr (Or.inl ⟨rfl, .right, by rw [← applied]; exact applyBindings_closed _ _⟩)
            · obtain ⟨f, g, foundF, foundG⟩ := twoCodes ih premises
              refine Or.inr (Or.inl ⟨rfl, .pair f g, ?_⟩)
              rw [← applied]
              simp only [cpairP, applyBindings_apply', List.map_cons, List.map_nil, foundF, foundG]
              rfl
            · obtain ⟨f, g, foundF, foundG⟩ := twoCodes ih premises
              refine Or.inr (Or.inl ⟨rfl, .comp f g, ?_⟩)
              rw [← applied]
              simp only [ccompP, applyBindings_apply', List.map_cons, List.map_nil, foundF, foundG]
              rfl
            · obtain ⟨f, g, foundF, foundG⟩ := twoCodes ih premises
              refine Or.inr (Or.inl ⟨rfl, .prec f g, ?_⟩)
              rw [← applied]
              simp only [cprecP, applyBindings_apply', List.map_cons, List.map_nil, foundF, foundG]
              rfl
            · cases premises with
              | cons head tail =>
                  obtain ⟨f, _, found⟩ := codePremise ih head
                  cases tail
                  refine Or.inr (Or.inl ⟨rfl, .rfind' f, ?_⟩)
                  rw [← applied]
                  simp only [crfindP, mv, applyBindings_apply', List.map_cons, List.map_nil,
                    applyBindings_fvar_of_find? found]
                  rfl
          · obtain ⟨conclusionSchema, premiseSchemas, -⟩ := rules_schemas inference inRules
            simp only [judgmentRule] at matched premises applied
            rw [applyBindingsForRule_plain _ _ rfl] at applied
            obtain ⟨middle, valued, trued⟩ := premisesAt_append c premises
            have extended := extends_of_congruences c (fun premise inside => by
              obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
              exact ⟨_, _, rfl⟩) valued
            obtain ⟨-, steps⟩ := truePremises c trued
            refine Or.inr (Or.inr (Or.inl ⟨by rw [← applied]; exact applyBindings_closed _ _, ?_⟩))
            have premisesValid : ∀ premise ∈ inference.row.instPremises (valuesOf middle inference.row.vars),
                Valid premise := by
              intro premise inside
              rw [FORule.instPremises, FORule.bindings, schemas_valuesOf premiseSchemas] at inside
              obtain ⟨pattern, inPremises, rfl⟩ := List.mem_map.mp inside
              exact spec_true (ih (steps pattern inPremises))
            have valid := rule_sound inRules (valuesOf middle inference.row.vars) (by simp [valuesOf])
              premisesValid
            rw [FORule.instConclusion, FORule.bindings, schema_valuesOf conclusionSchema,
              schema_extends conclusionSchema matched extended, schema_match_sound conclusionSchema matched] at valid
            exact valid
          · simp only [relationRule] at matched premises applied
            rw [applyBindingsForRule_plain _ _ rfl] at applied
            rw [matchPattern_mv matched] at premises
            obtain ⟨m, n, rfl, target_is, halts⟩ := relation_sound ih premises
            exact Or.inr (Or.inr (Or.inr ⟨m, n, rfl, applied ▸ target_is, halts⟩))

/-! ## Completeness -/

theorem merge_fresh {bindings : Bindings} {name : String} {value : Pattern}
    (absent : bindings.find? (·.1 == name) = none) :
    mergeBindings bindings [(name, value)] = some ((name, value) :: bindings) := by
  rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeBindings_eq, List.foldl_cons, List.foldl_nil, Option.bind_some]
  unfold Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeEntry
  rw [absent]

theorem merge_same {bindings : Bindings} {name : String} {value : Pattern}
    (present : bindings.find? (·.1 == name) = some (name, value)) :
    mergeBindings bindings [(name, value)] = some bindings := by
  rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeBindings_eq, List.foldl_cons, List.foldl_nil, Option.bind_some]
  unfold Mettapedia.OSLF.MeTTaIL.EngineCoded.mergeEntry
  rw [present]
  simp

theorem find?_zip_of_mem : ∀ {names : List String} {values : List Pattern} {name : String} {value : Pattern},
    names.Nodup → (name, value) ∈ names.zip values → (names.zip values).find? (·.1 == name) = some (name, value)
  | [], _, _, _, _, member => by simp at member
  | _ :: _, [], _, _, _, member => by simp at member
  | first :: names, firstValue :: values, name, value, distinct, member => by
      rw [List.zip_cons_cons, List.mem_cons] at member
      rcases member with same | later
      · simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        simp
      · have absent : first ≠ name := by
          intro equal
          subst equal
          exact (List.nodup_cons.mp distinct).1 (List.of_mem_zip later).1
        simp [absent, find?_zip_of_mem (List.nodup_cons.mp distinct).2 later]

theorem applyBindings_valuesP (bindings : Bindings) (sort : TypeExpr) :
    applyBindings bindings (valuesP sort) = valuesP sort := by
  unfold valuesP
  split <;> exact applyBindings_closed _ _

/-- The rules of the language are its rules. -/
theorem generator_member {rule : RewriteRule} (member : rule ∈ generatorRules) : rule ∈ (universal c).rewrites := by
  simp [universal, member]

theorem judgment_member {rule : SortedFirstOrderRules.Rule} (member : rule ∈ rules) :
    judgmentRule rule ∈ (universal c).rewrites := by
  simp only [universal, List.mem_append, List.mem_map, List.mem_singleton]
  exact Or.inl (Or.inr ⟨rule, member, rfl⟩)

theorem relation_member : relationRule c ∈ (universal c).rewrites := by
  simp [universal]

theorem premisesAt_append_of {fuel : ℕ} : ∀ {first second : List Premise} {initial middle final : Bindings},
    PremisesAt base (universal c) fuel initial first middle → PremisesAt base (universal c) fuel middle second final →
      PremisesAt base (universal c) fuel initial (first ++ second) final
  | [], _, _, _, _, before, after => by cases before; exact after
  | _ :: _, _, _, _, _, before, after => by
      cases before with
      | cons head tail => exact .cons head (premisesAt_append_of tail after)

theorem numeralPremise_of {fuel : ℕ} {bindings result : Bindings} {name : String} {source value : Pattern}
    (step : StepAt base (universal c) fuel source value) (closed : applyBindings bindings source = source)
    (merged : mergeBindings bindings [(name, value)] = some result) :
    PremiseAt base (universal c) fuel bindings (.congruence source (mv name)) result :=
  .congruence (closed ▸ step) (by simp [mv, matchPattern]) merged

theorem truePremise_of {fuel : ℕ} {bindings : Bindings} {pattern : Pattern}
    (step : StepAt base (universal c) fuel (applyBindings bindings pattern) trueP) :
    PremiseAt base (universal c) fuel bindings (.congruence pattern trueP) bindings :=
  .congruence (premiseBindings := []) step (by simp [trueP, matchPattern, matchArgs]) (by simp [mergeBindings])

/-- **The numerals generate every numeral.** -/
theorem numerals_complete : ∀ n : ℕ, ∃ fuel, StepAt base (universal c) fuel numeralsP (num n)
  | 0 => ⟨1, .rule (generator_member c (by simp [generatorRules]))
      (rule := valueRule "numeralsZero" numeralsP [] zeroP) (initialBindings := [])
      (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; simp [valueRule, numeralsP, matchPattern,
        matchArgs])
      (.nil []) (by rw [applyBindingsForRule_plain _ _ rfl]; exact applyBindings_closed _ _)⟩
  | n + 1 => by
      obtain ⟨fuel, step⟩ := numerals_complete n
      refine ⟨fuel + 1, .rule (generator_member c (by simp [generatorRules]))
        (rule := valueRule "numeralsSucc" numeralsP [("x", numeralsP)] (succP (mv "x"))) (initialBindings := [])
        (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; simp [valueRule, numeralsP,
          matchPattern, matchArgs])
        (.cons (numeralPremise_of c step (applyBindings_closed _ _) (merge_fresh rfl)) (.nil _)) ?_⟩
      rw [applyBindingsForRule_plain _ _ rfl]
      simp only [valueRule, succP, mv, applyBindings_apply', List.map_cons, List.map_nil]
      rw [applyBindings_fvar_of_find? (by simp : [("x", num n)].find? (·.1 == "x") = some ("x", num n))]
      rfl

/-- A code generator without premises. -/
theorem constantCode {name label : String} (member : valueRule name codesP [] (.apply label []) ∈ generatorRules) :
    StepAt base (universal c) 1 codesP (.apply label []) :=
  .rule (generator_member c member) (initialBindings := [])
    (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; simp [valueRule, codesP, matchPattern, matchArgs])
    (.nil []) (by rw [applyBindingsForRule_plain _ _ rfl]; exact applyBindings_closed _ _)

/-- Two codes bound by the premises of a code generator. -/
theorem twoCodePremises {fuelF fuelG : ℕ} {f g : Code}
    (stepF : StepAt base (universal c) fuelF codesP (codePattern f))
    (stepG : StepAt base (universal c) fuelG codesP (codePattern g)) :
    PremisesAt base (universal c) (fuelF + fuelG) []
      ([("f", codesP), ("g", codesP)].map fun entry => .congruence entry.2 (mv entry.1))
      [("g", codePattern g), ("f", codePattern f)] := by
  simp only [List.map_cons, List.map_nil]
  exact .cons (numeralPremise_of c (stepF.mono_fuel (by omega)) (applyBindings_closed _ _) (merge_fresh rfl))
    (.cons (numeralPremise_of c (stepG.mono_fuel (by omega)) (applyBindings_closed _ _) (merge_fresh (by simp)))
      (.nil _))

theorem twoCodeValues (f g : Code) (label : String) :
    applyBindings [("g", codePattern g), ("f", codePattern f)] (.apply label [mv "f", mv "g"]) =
      .apply label [codePattern f, codePattern g] := by
  simp only [mv, applyBindings_apply', List.map_cons, List.map_nil]
  rw [applyBindings_fvar_of_find? (by simp : [("g", codePattern g), ("f", codePattern f)].find? (·.1 == "f") =
      some ("f", codePattern f)),
    applyBindings_fvar_of_find? (by simp : [("g", codePattern g), ("f", codePattern f)].find? (·.1 == "g") =
      some ("g", codePattern g))]

/-- **The codes generate every code.** -/
theorem codes_complete : ∀ code : Code, ∃ fuel, StepAt base (universal c) fuel codesP (codePattern code)
  | .zero => ⟨1, constantCode c (name := "codesZero") (by simp [generatorRules, czeroP])⟩
  | .succ => ⟨1, constantCode c (name := "codesSucc") (by simp [generatorRules, csuccP])⟩
  | .left => ⟨1, constantCode c (name := "codesLeft") (by simp [generatorRules, cleftP])⟩
  | .right => ⟨1, constantCode c (name := "codesRight") (by simp [generatorRules, crightP])⟩
  | .pair f g => by
      obtain ⟨fuelF, stepF⟩ := codes_complete f
      obtain ⟨fuelG, stepG⟩ := codes_complete g
      exact ⟨fuelF + fuelG + 1, .rule (generator_member c (by simp [generatorRules]))
        (rule := valueRule "codesPair" codesP [("f", codesP), ("g", codesP)] (cpairP (mv "f") (mv "g")))
        (initialBindings := [])
        (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; simp [valueRule, codesP, matchPattern,
          matchArgs])
        (twoCodePremises c stepF stepG)
        (by rw [applyBindingsForRule_plain _ _ rfl]; exact twoCodeValues f g "cpair")⟩
  | .comp f g => by
      obtain ⟨fuelF, stepF⟩ := codes_complete f
      obtain ⟨fuelG, stepG⟩ := codes_complete g
      exact ⟨fuelF + fuelG + 1, .rule (generator_member c (by simp [generatorRules]))
        (rule := valueRule "codesComp" codesP [("f", codesP), ("g", codesP)] (ccompP (mv "f") (mv "g")))
        (initialBindings := [])
        (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; simp [valueRule, codesP, matchPattern,
          matchArgs])
        (twoCodePremises c stepF stepG)
        (by rw [applyBindingsForRule_plain _ _ rfl]; exact twoCodeValues f g "ccomp")⟩
  | .prec f g => by
      obtain ⟨fuelF, stepF⟩ := codes_complete f
      obtain ⟨fuelG, stepG⟩ := codes_complete g
      exact ⟨fuelF + fuelG + 1, .rule (generator_member c (by simp [generatorRules]))
        (rule := valueRule "codesPrec" codesP [("f", codesP), ("g", codesP)] (cprecP (mv "f") (mv "g")))
        (initialBindings := [])
        (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; simp [valueRule, codesP, matchPattern,
          matchArgs])
        (twoCodePremises c stepF stepG)
        (by rw [applyBindingsForRule_plain _ _ rfl]; exact twoCodeValues f g "cprec")⟩
  | .rfind' f => by
      obtain ⟨fuel, step⟩ := codes_complete f
      refine ⟨fuel + 1, .rule (generator_member c (by simp [generatorRules]))
        (rule := valueRule "codesSearch" codesP [("f", codesP)] (crfindP (mv "f"))) (initialBindings := [])
        (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; simp [valueRule, codesP, matchPattern,
          matchArgs])
        (.cons (numeralPremise_of c step (applyBindings_closed _ _) (merge_fresh rfl)) (.nil _)) ?_⟩
      rw [applyBindingsForRule_plain _ _ rfl]
      simp only [valueRule, crfindP, mv, applyBindings_apply', List.map_cons, List.map_nil]
      rw [applyBindings_fvar_of_find? (by simp : [("f", codePattern f)].find? (·.1 == "f") = some ("f", codePattern f))]
      rfl

/-- Every value is generated by the term of its sort. -/
theorem value_generated : ∀ value : Value, ∃ fuel, StepAt base (universal c) fuel (valuesP value.sort) value.pattern
  | .nat n => by
      obtain ⟨fuel, step⟩ := numerals_complete c n
      exact ⟨fuel, by simpa [Value.sort, Value.pattern, valuesP, natSort, codeSort] using step⟩
  | .code code => by
      obtain ⟨fuel, step⟩ := codes_complete c code
      exact ⟨fuel, by simpa [Value.sort, Value.pattern, valuesP] using step⟩

/-- **Value premises bind every metavariable to its value.** -/
theorem valuePremises_complete (substitution : Bindings) : ∀ (entries : List (String × Value)) (bindings : Bindings),
    AgreesWith bindings substitution →
    (∀ entry ∈ entries, applyBindings substitution (.fvar entry.1) = entry.2.pattern) →
    ∃ fuel result, PremisesAt base (universal c) fuel bindings
        (entries.map fun entry => .congruence (valuesP entry.2.sort) (mv entry.1)) result ∧
      AgreesWith result substitution ∧
        ∀ entry ∈ entries, result.find? (·.1 == entry.1) = some (entry.1, entry.2.pattern)
  | [], bindings, agrees, _ => ⟨0, bindings, .nil _, agrees, fun _ inside => absurd inside List.not_mem_nil⟩
  | (name, value) :: rest, bindings, agrees, valued => by
      obtain ⟨fuel₀, generated⟩ := value_generated c value
      have own : applyBindings substitution (.fvar name) = value.pattern := valued _ List.mem_cons_self
      obtain ⟨first, merged, agreesFirst, boundFirst⟩ : ∃ first, mergeBindings bindings [(name, value.pattern)] = some first ∧
          AgreesWith first substitution ∧ first.find? (·.1 == name) = some (name, value.pattern) := by
        cases found : bindings.find? (·.1 == name) with
        | none =>
            refine ⟨_, merge_fresh found, fun entry inside => ?_, by simp⟩
            rcases List.mem_cons.mp inside with rfl | earlier
            · exact own
            · exact agrees entry earlier
        | some entry =>
            have keyed := find?_key found
            have existing : applyBindings substitution (.fvar name) = entry.2 := by
              have agreed := agrees entry (List.mem_of_find?_eq_some found)
              rw [keyed] at agreed
              exact agreed
            have same : entry = (name, value.pattern) := by rw [keyed, ← existing, own]
            rw [same] at found
            exact ⟨bindings, merge_same found, agrees, found⟩
      obtain ⟨fuel', result, evidence, agreesResult, boundRest⟩ :=
        valuePremises_complete substitution rest first agreesFirst (fun entry inside => valued entry (List.mem_cons_of_mem _ inside))
      have extended := extends_of_congruences c (fun premise inside => by
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
        exact ⟨_, _, rfl⟩) evidence
      refine ⟨fuel₀ + fuel', result, .cons (numeralPremise_of c (generated.mono_fuel (by omega))
        (applyBindings_valuesP _ _) merged) (evidence.mono_fuel (by omega)), agreesResult, fun entry inside => ?_⟩
      rcases List.mem_cons.mp inside with rfl | later
      · exact extended _ _ boundFirst
      · exact boundRest entry later

/-- Premises that step to `true` hold when each of their instances does. -/
theorem truePremises_complete (bindings : Bindings) : ∀ patterns : List Pattern,
    (∀ pattern ∈ patterns, ∃ fuel, StepAt base (universal c) fuel (applyBindings bindings pattern) trueP) →
      ∃ fuel, PremisesAt base (universal c) fuel bindings (patterns.map fun pattern => .congruence pattern trueP)
        bindings
  | [], _ => ⟨0, .nil _⟩
  | pattern :: patterns, steps => by
      obtain ⟨fuel₀, step⟩ := steps pattern List.mem_cons_self
      obtain ⟨fuel', rest⟩ := truePremises_complete bindings patterns
        (fun other inside => steps other (List.mem_cons_of_mem _ inside))
      exact ⟨fuel₀ + fuel', .cons (truePremise_of c (step.mono_fuel (by omega))) (rest.mono_fuel (by omega))⟩

theorem exists_mem_zip {α β : Type} : ∀ {names : List α} {values : List β} {name : α},
    names.length = values.length → name ∈ names → ∃ value, (name, value) ∈ names.zip values
  | [], _, _, _, inside => absurd inside List.not_mem_nil
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | first :: names, value :: values, name, lengths, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨value, by simp⟩
      · obtain ⟨found, member⟩ := exists_mem_zip (by simpa using lengths) later
        exact ⟨found, by simp [member]⟩

open Mettapedia.GSLT.LanguageDef.FirstOrderRules (FORule) in
/-- **The language steps every true judgment to `true`**: stepping to `true` is closed under the rule
instances at closed values. -/
theorem judgments_closed : ClosedUnderValues (fun judgment => ∃ fuel, StepAt base (universal c) fuel judgment trueP) := by
  intro rule member values sorts arity premisesHold
  obtain ⟨conclusionSchema, premiseSchemas, distinct⟩ := rules_schemas rule member
  obtain ⟨initial, matched, agrees⟩ :=
    schema_match_complete conclusionSchema (rule.row.vars.zip (values.map Value.pattern))
  have valued : ∀ entry ∈ rule.row.vars.zip values,
      applyBindings (rule.row.vars.zip (values.map Value.pattern)) (.fvar entry.1) = entry.2.pattern := by
    intro entry inside
    refine applyBindings_fvar_of_find? (find?_zip_of_mem distinct ?_)
    rw [List.zip_map_right]
    exact List.mem_map_of_mem (f := Prod.map id Value.pattern) inside
  obtain ⟨fuel₁, middle, evidence, _, bound⟩ :=
    valuePremises_complete c (rule.row.vars.zip (values.map Value.pattern)) (rule.row.vars.zip values) initial agrees
      valued
  have sameAt : ∀ name ∈ rule.row.vars, applyBindings middle (.fvar name) =
      applyBindings (rule.row.vars.zip (values.map Value.pattern)) (.fvar name) := by
    intro name inside
    obtain ⟨value, pairIn⟩ := exists_mem_zip arity.symm inside
    rw [applyBindings_fvar_of_find? (bound _ pairIn), valued _ pairIn]
  obtain ⟨fuel₂, trued⟩ := truePremises_complete c middle rule.row.premises (fun pattern inside => by
    obtain ⟨fuel, step⟩ := premisesHold (applyBindings (rule.row.vars.zip (values.map Value.pattern)) pattern) (by
      rw [FORule.instPremises, FORule.bindings]
      exact List.mem_map_of_mem inside)
    refine ⟨fuel, ?_⟩
    rwa [schema_congr (Schemas.member premiseSchemas inside) sameAt])
  have valuePremisesAre : valuePremises rule =
      (rule.row.vars.zip values).map fun entry => .congruence (valuesP entry.2.sort) (mv entry.1) := by
    rw [valuePremises, ← sorts, List.zip_map_right, List.map_map]
    rfl
  refine ⟨fuel₁ + fuel₂ + 1, .rule (judgment_member c member) (initialBindings := initial)
    (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; exact matched)
    (premisesAt_append_of c (first := valuePremises rule) (by rw [valuePremisesAre]; exact evidence.mono_fuel (by omega))
      (trued.mono_fuel (by omega))) ?_⟩
  rw [applyBindingsForRule_plain _ _ rfl]
  exact applyBindings_closed _ _

/-- **The relation rule relates numerals the code relates.** -/
theorem relation_complete {m n : ℕ} (halts : (c.eval (Nat.pair m n)).Dom) :
    ∃ fuel, StepAt base (universal c) fuel (num m) (num n) := by
  obtain ⟨fuel₁, step₁⟩ := numerals_complete c m
  obtain ⟨fuel₂, step₂⟩ := numerals_complete c n
  obtain ⟨fuel₃, step₃⟩ := numerals_complete c (Nat.pair m n)
  obtain ⟨fuel₄, step₄⟩ := holds_closed (judgments_closed c) (.pair m n (Nat.pair m n)) rfl
  obtain ⟨fuel₅, step₅⟩ := holds_closed (judgments_closed c) (.halts c (Nat.pair m n)) halts
  have pairAt : applyBindings [("p", num (Nat.pair m n)), ("y", num n), ("x", num m)] (pairP (mv "x") (mv "y") (mv "p")) =
      (Judgment.pair m n (Nat.pair m n)).pattern := by
    simp [pairP, mv, applyBindings_apply', Judgment.pattern, applyBindings]
  have haltsAt : applyBindings [("p", num (Nat.pair m n)), ("y", num n), ("x", num m)] (haltsP (codePattern c) (mv "p")) =
      (Judgment.halts c (Nat.pair m n)).pattern := by
    simp only [haltsP, mv, applyBindings_apply', List.map_cons, List.map_nil, applyBindings_codePattern, Judgment.pattern]
    rw [applyBindings_fvar_of_find? (by simp : [("p", num (Nat.pair m n)), ("y", num n), ("x", num m)].find?
      (·.1 == "p") = some ("p", num (Nat.pair m n)))]
  refine ⟨fuel₁ + fuel₂ + fuel₃ + fuel₄ + fuel₅ + 1, .rule (relation_member c) (initialBindings := [("x", num m)])
    (finalBindings := [("p", num (Nat.pair m n)), ("y", num n), ("x", num m)])
    (by rw [Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPatternForRule_eq]; simp [relationRule, mv, matchPattern]) ?_ ?_⟩
  · simp only [relationRule]
    refine .cons (numeralPremise_of c (step₁.mono_fuel (by omega)) (applyBindings_closed _ _) (merge_same (by simp)))
      (.cons (numeralPremise_of c (step₂.mono_fuel (by omega)) (applyBindings_closed _ _) (merge_fresh (by simp)))
      (.cons (numeralPremise_of c (step₃.mono_fuel (by omega)) (applyBindings_closed _ _) (merge_fresh (by simp)))
      (.cons (truePremise_of c (by rw [pairAt]; exact step₄.mono_fuel (by omega)))
      (.cons (truePremise_of c (by rw [haltsAt]; exact step₅.mono_fuel (by omega))) (.nil _)))))
  · rw [applyBindingsForRule_plain _ _ rfl]
    simp only [relationRule, mv]
    exact applyBindings_fvar_of_find? (by simp)

/-- **A numeral steps exactly to the numerals the code relates it to.** -/
theorem numeral_step_iff {m : ℕ} {target : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base (universal c) (num m) target ↔ ∃ n, target = num n ∧ (c.eval (Nat.pair m n)).Dom := by
  constructor
  · rintro ⟨fuel, step⟩
    rcases sound c fuel step with ⟨same, _⟩ | ⟨same, _⟩ | ⟨_, valid⟩ | ⟨m', n, same, rfl, halts⟩
    · exact absurd same (num_ne_apply ⟨by decide, by decide⟩)
    · exact absurd same (num_ne_apply ⟨by decide, by decide⟩)
    · exact absurd valid (valid_num m)
    · obtain rfl := num_injective same
      exact ⟨n, rfl, halts⟩
  · rintro ⟨n, rfl, halts⟩
    exact relation_complete c halts

/-! ## The reference relation -/

section Alignment

open Mettapedia.OSLF.MeTTaIL.ReferenceStep (notDeeper notDeeperList extraNotDeeper extraNotDeeperList sourceAligned
  premiseAligned ruleAligned ReferenceProfile)

mutual
  theorem notDeeper_of_binderFree (sites : Pattern) :
      ∀ pattern : Pattern, binderFree pattern = true → notDeeper sites 0 pattern = true
    | .fvar _, _ => by simp only [notDeeper]; split <;> simp
    | .bvar _, _ => by simp [notDeeper]
    | .apply _ arguments, free => by
        simp only [notDeeper]
        exact notDeeperList_of_binderFree sites arguments free
    | .lambda _ _, free => by simp [binderFree] at free
    | .multiLambda _ _ _, free => by simp [binderFree] at free
    | .subst _ _, free => by simp [binderFree] at free
    | .collection _ elements rest, free => by
        simp only [notDeeper, Bool.and_eq_true]
        refine ⟨notDeeperList_of_binderFree sites elements free, ?_⟩
        cases rest with
        | none => rfl
        | some _ => simp only; split <;> simp

  theorem notDeeperList_of_binderFree (sites : Pattern) :
      ∀ patterns : List Pattern, binderFreeList patterns = true → notDeeperList sites 0 patterns = true
    | [], _ => by simp [notDeeperList]
    | pattern :: patterns, free => by
        simp only [binderFreeList, Bool.and_eq_true] at free
        simp only [notDeeperList, notDeeper_of_binderFree sites pattern free.1,
          notDeeperList_of_binderFree sites patterns free.2, Bool.and_self]
end

mutual
  theorem extraNotDeeper_of_binderFree (lhs : Pattern) (extra : List Pattern) :
      ∀ pattern : Pattern, binderFree pattern = true → extraNotDeeper lhs extra 0 pattern = true
    | .fvar _, _ => by simp only [extraNotDeeper]; split <;> (try split) <;> simp
    | .bvar _, _ => by simp [extraNotDeeper]
    | .apply _ arguments, free => by
        simp only [extraNotDeeper]
        exact extraNotDeeperList_of_binderFree lhs extra arguments free
    | .lambda _ _, free => by simp [binderFree] at free
    | .multiLambda _ _ _, free => by simp [binderFree] at free
    | .subst _ _, free => by simp [binderFree] at free
    | .collection _ elements rest, free => by
        simp only [extraNotDeeper, Bool.and_eq_true]
        refine ⟨extraNotDeeperList_of_binderFree lhs extra elements free, ?_⟩
        cases rest with
        | none => rfl
        | some _ => simp only; split <;> (try split) <;> simp

  theorem extraNotDeeperList_of_binderFree (lhs : Pattern) (extra : List Pattern) :
      ∀ patterns : List Pattern, binderFreeList patterns = true → extraNotDeeperList lhs extra 0 patterns = true
    | [], _ => by simp [extraNotDeeperList]
    | pattern :: patterns, free => by
        simp only [binderFreeList, Bool.and_eq_true] at free
        simp only [extraNotDeeperList, extraNotDeeper_of_binderFree lhs extra pattern free.1,
          extraNotDeeperList_of_binderFree lhs extra patterns free.2, Bool.and_self]
end

theorem sourceAligned_of_binderFree (sites : Pattern) (source : Pattern) (free : binderFree source = true) :
    sourceAligned sites source = true := by
  cases source with
  | fvar _ => rfl
  | _ => exact notDeeper_of_binderFree sites _ free

/-- **A rule of binder-free congruence premises is aligned.** -/
theorem ruleAligned_of_binderFree (rule : RewriteRule)
    (premises : ∀ premise ∈ rule.premises, ∃ source target, premise = .congruence source target ∧
      binderFree source = true)
    (right : binderFree rule.right = true) : ruleAligned rule = true := by
  unfold ruleAligned
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun premise inside => ?_, extraNotDeeper_of_binderFree _ _ _ right⟩
  obtain ⟨source, target, rfl, free⟩ := premises premise inside
  exact sourceAligned_of_binderFree _ source free

theorem binderFree_codePattern : ∀ code : Code, binderFree (codePattern code) = true
  | .zero | .succ | .left | .right => rfl
  | .pair f g | .comp f g | .prec f g => by
      simp [codePattern, cpairP, ccompP, cprecP, binderFree, binderFreeList, binderFree_codePattern f,
        binderFree_codePattern g]
  | .rfind' f => by simp [codePattern, crfindP, binderFree, binderFreeList, binderFree_codePattern f]

theorem binderFree_valuesP (sort : TypeExpr) : binderFree (valuesP sort) = true := by
  unfold valuesP
  split <;> rfl

/-- **The language of a code is aligned**, so its contextual and reference relations agree. -/
theorem profile : ReferenceProfile (universal c) := by
  intro rule member
  simp only [universal, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with (generator | ⟨inference, inRules, rfl⟩) | rfl
  · simp only [generatorRules, List.mem_cons, List.not_mem_nil, or_false] at generator
    rcases generator with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · obtain ⟨_, premiseSchemas, _⟩ := rules_schemas inference inRules
    refine ruleAligned_of_binderFree _ (fun premise inside => ?_) rfl
    simp only [judgmentRule, valuePremises, List.mem_append, List.mem_map] at inside
    rcases inside with ⟨entry, _, rfl⟩ | ⟨pattern, inPremises, rfl⟩
    · exact ⟨_, _, rfl, binderFree_valuesP _⟩
    · exact ⟨_, _, rfl, Schema.binderFree (Schemas.member premiseSchemas inPremises)⟩
  · refine ruleAligned_of_binderFree _ (fun premise inside => ?_) rfl
    simp only [relationRule, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, _, rfl, rfl⟩
    · exact ⟨_, _, rfl, rfl⟩
    · exact ⟨_, _, rfl, rfl⟩
    · exact ⟨_, _, rfl, rfl⟩
    · refine ⟨_, _, rfl, ?_⟩
      simp [haltsP, mv, binderFree, binderFreeList, binderFree_codePattern]

end Alignment

/-- **In the reference relation, a numeral steps exactly to the numerals the code relates it to.** -/
theorem reference_numeral_step_iff {m : ℕ} {target : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.Step RelationEnv.empty (universal c) (num m) target ↔
      ∃ n, target = num n ∧ (c.eval (Nat.pair m n)).Dom := by
  rw [← Mettapedia.OSLF.MeTTaIL.ReferenceStep.contextualStep_iff_step RelationEnv.empty (universal c) (profile c)]
  exact numeral_step_iff c

variable {c}

/-- **Every recursively enumerable relation on numbers is the step relation of a language on numerals**:
a numeral steps exactly to the numerals it is related to. -/
theorem every_re_relation_steps {R : ℕ → ℕ → Prop} (enumerable : REPred fun p : ℕ × ℕ => R p.1 p.2) :
    ∃ language : LanguageDef, ∀ (m : ℕ) (target : Pattern),
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.Step RelationEnv.empty language (num m) target ↔
        ∃ n, target = num n ∧ R m n := by
  have unpaired : REPred fun k : ℕ => R k.unpair.1 k.unpair.2 :=
    Partrec.comp enumerable Computable.unpair
  obtain ⟨code, represented⟩ := every_re_represented unpaired
  refine ⟨universal code, fun m target => ?_⟩
  rw [reference_numeral_step_iff code]
  refine exists_congr fun n => and_congr_right fun _ => ?_
  rw [← derives_halts_iff, ← represented, Nat.unpair_pair]

theorem num_codeComputable : Mettapedia.Computability.CodeComputable num := by
  have succ : Mettapedia.Computability.CodeComputable₂ fun (_ : ℕ) (pattern : Pattern) => succP pattern :=
    Mettapedia.OSLF.MeTTaIL.PatternCode.CodeComputable'.apply (Mettapedia.Computability.CodeComputable.const "succ")
      (Mettapedia.Computability.CodeComputable.list_cons Mettapedia.Computability.CodeComputable.snd
        (Mettapedia.Computability.CodeComputable.const []))
  refine (Mettapedia.Computability.CodeComputable.iterate Mettapedia.Computability.CodeComputable.id
    (Mettapedia.Computability.CodeComputable.const zeroP) succ).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- **A relation on numbers is recursively enumerable exactly when it is the step relation of a language
on numerals.** -/
theorem re_iff_steps (R : ℕ → ℕ → Prop) :
    REPred (fun p : ℕ × ℕ => R p.1 p.2) ↔
      ∃ language : LanguageDef, ∀ m n,
        Mettapedia.OSLF.MeTTaIL.ReferenceStep.Step RelationEnv.empty language (num m) (num n) ↔ R m n := by
  constructor
  · intro enumerable
    obtain ⟨language, steps⟩ := every_re_relation_steps enumerable
    refine ⟨language, fun m n => ?_⟩
    rw [steps]
    constructor
    · rintro ⟨n', same, related⟩
      rw [num_injective same]
      exact related
    · exact fun related => ⟨n, rfl, related⟩
  · rintro ⟨language, steps⟩
    obtain ⟨listed, enumerable, agrees⟩ :=
      Mettapedia.OSLF.MeTTaIL.EngineCoded.referenceStep_enumerable RelationEnv.empty language
        ((Mettapedia.Computability.CodeComputable.const []).of_eq fun _ => rfl)
    obtain ⟨track, computable, tracks⟩ := num_codeComputable
    have numCodes : Computable fun n : ℕ => Mettapedia.Computability.code (num n) :=
      computable.of_eq fun n => tracks n
    refine (show REPred fun p : ℕ × ℕ => listed (Mettapedia.Computability.code (num p.1),
        Mettapedia.Computability.code (num p.2)) from
      Partrec.comp enumerable ((numCodes.comp Computable.fst).pair (numCodes.comp Computable.snd))).of_eq
      fun p => ?_
    rw [agrees, steps]

end Mettapedia.GSLT.LanguageDef.RewritingUniversality

#print axioms Mettapedia.GSLT.LanguageDef.RewritingUniversality.every_re_relation_steps
#print axioms Mettapedia.GSLT.LanguageDef.RewritingUniversality.re_iff_steps
