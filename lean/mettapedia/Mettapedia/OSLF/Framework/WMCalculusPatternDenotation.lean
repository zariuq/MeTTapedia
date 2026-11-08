import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.MatchBindingExtension
import Mettapedia.OSLF.MeTTaIL.BindingAgreement

/-!
# Denotations of first-order patterns, and soundness of authored rewriting

A `PatternAlgebra` reads each constructor label as a partial operation on a
value type, and a valuation reads free names.  `denote` folds a first-order
pattern (free names and constructor applications) to an optional value; every
other pattern form has no denotation.

A relation premise is read by a `RelationMeaning`: the value tuples a relation
name relates.  An environment *certifies* a meaning under a valuation when every
row it returns denotes a tuple in the meaning.  A rule is *valid* when, under
every valuation satisfying the meaning of its premises, its right side denotes
whatever its left side denotes.  Congruence premises are read as the same
preservation property one level down.

`step_preserves` is the soundness theorem for the least contextual relation
`Step (engineBasePremises env) lang`: if every rule of `lang` is valid and has
the first-order shape the evaluator needs (`ruleDenotable`), every step
under a certified environment, at any contextual depth, preserves the
denotation of its source.  Preservation is one-directional: a source without a
denotation constrains nothing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusPatternDenotation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.MatchBindingExtension
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- Constructor labels read as partial operations on `V`. -/
structure PatternAlgebra (V : Type) where
  op : String → List V → Option V

section Denotation

variable {V : Type} (A : PatternAlgebra V)

mutual
/-- Denotation of a first-order pattern under a valuation of free names. -/
def denote (ρ : String → Option V) : Pattern → Option V
  | .fvar name => ρ name
  | .apply label args => (denoteList ρ args).bind (A.op label)
  | .bvar _ => none
  | .lambda _ _ => none
  | .multiLambda _ _ _ => none
  | .subst _ _ => none
  | .collection _ _ _ => none

/-- Denotation of an argument list: defined when every argument is. -/
def denoteList (ρ : String → Option V) : List Pattern → Option (List V)
  | [] => some []
  | pattern :: patterns =>
      (denote ρ pattern).bind fun value => (denoteList ρ patterns).map (value :: ·)
end

/-- The valuation that reads a bound metavariable by the denotation of its
binding and an unbound one as before. -/
def extend (ρ : String → Option V) (bindings : Bindings) : String → Option V :=
  fun name =>
    match bindings.find? (·.1 == name) with
    | some (_, value) => denote A ρ value
    | none => ρ name

variable {A}

@[simp] theorem denote_fvar (ρ : String → Option V) (name : String) :
    denote A ρ (.fvar name) = ρ name := rfl

@[simp] theorem denote_apply (ρ : String → Option V) (label : String) (args : List Pattern) :
    denote A ρ (.apply label args) = (denoteList A ρ args).bind (A.op label) := rfl

@[simp] theorem denoteList_nil (ρ : String → Option V) : denoteList A ρ [] = some [] := rfl

@[simp] theorem denoteList_cons (ρ : String → Option V) (pattern : Pattern)
    (patterns : List Pattern) :
    denoteList A ρ (pattern :: patterns) =
      (denote A ρ pattern).bind fun value => (denoteList A ρ patterns).map (value :: ·) := rfl

/-! Applications of fixed arity, as chains of `Option.bind`. -/

theorem denote_apply_nil (ρ : String → Option V) (label : String) :
    denote A ρ (.apply label []) = A.op label [] := rfl

theorem denote_apply_one (ρ : String → Option V) (label : String) (first : Pattern) :
    denote A ρ (.apply label [first]) =
      (denote A ρ first).bind fun a => A.op label [a] := by
  simp only [denote_apply, denoteList_cons, denoteList_nil]
  cases denote A ρ first <;> rfl

theorem denote_apply_two (ρ : String → Option V) (label : String) (first second : Pattern) :
    denote A ρ (.apply label [first, second]) =
      (denote A ρ first).bind fun a => (denote A ρ second).bind fun b => A.op label [a, b] := by
  simp only [denote_apply, denoteList_cons, denoteList_nil]
  cases denote A ρ first <;> cases denote A ρ second <;> rfl

theorem denote_apply_three (ρ : String → Option V) (label : String)
    (first second third : Pattern) :
    denote A ρ (.apply label [first, second, third]) =
      (denote A ρ first).bind fun a => (denote A ρ second).bind fun b =>
        (denote A ρ third).bind fun c => A.op label [a, b, c] := by
  simp only [denote_apply, denoteList_cons, denoteList_nil]
  cases denote A ρ first <;> cases denote A ρ second <;> cases denote A ρ third <;> rfl

theorem denote_apply_four (ρ : String → Option V) (label : String)
    (first second third fourth : Pattern) :
    denote A ρ (.apply label [first, second, third, fourth]) =
      (denote A ρ first).bind fun a => (denote A ρ second).bind fun b =>
        (denote A ρ third).bind fun c => (denote A ρ fourth).bind fun d =>
          A.op label [a, b, c, d] := by
  simp only [denote_apply, denoteList_cons, denoteList_nil]
  cases denote A ρ first <;> cases denote A ρ second <;> cases denote A ρ third <;>
    cases denote A ρ fourth <;> rfl

/-- **Substitution**: instantiating a first-order schema and then denoting it is
denoting the schema under the extended valuation. -/
theorem denote_applyBindings (ρ : String → Option V) (bindings : Bindings) :
    ∀ pattern : Pattern, Pattern.isMatchCorrect pattern = true →
      denote A ρ (applyBindings bindings pattern) = denote A (extend A ρ bindings) pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; simp [applyBindings, denote]
  | hfvar name =>
      intro _
      cases found : bindings.find? (·.1 == name) with
      | none => simp [applyBindings, found, extend]
      | some entry =>
          obtain ⟨key, value⟩ := entry
          simp [applyBindings, found, extend]
  | happly label args ih =>
      intro correct
      simp only [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
      have list : ∀ patterns : List Pattern, (∀ q ∈ patterns, q ∈ args) →
          isMatchCorrectListAux patterns = true →
          denoteList A ρ (patterns.map (applyBindings bindings)) =
            denoteList A (extend A ρ bindings) patterns := by
        intro patterns
        induction patterns with
        | nil => intro _ _; rfl
        | cons head tail tailIh =>
            intro within correctList
            simp only [isMatchCorrectListAux, Bool.and_eq_true] at correctList
            simp only [List.map_cons, denoteList_cons]
            rw [ih head (within head List.mem_cons_self) correctList.1,
              tailIh (fun q member => within q (List.mem_cons_of_mem _ member)) correctList.2]
      simp only [applyBindings, denote_apply]
      rw [list args (fun _ member => member) correct]
  | hlambda => intro correct; simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hmultiLambda => intro correct; simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hsubst => intro correct; simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hcollection => intro correct; simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct

theorem denoteList_map_applyBindings (ρ : String → Option V) (bindings : Bindings) :
    ∀ patterns : List Pattern, (∀ p ∈ patterns, Pattern.isMatchCorrect p = true) →
      denoteList A ρ (patterns.map (applyBindings bindings)) =
        denoteList A (extend A ρ bindings) patterns
  | [], _ => rfl
  | head :: tail, correct => by
      simp only [List.map_cons, denoteList_cons]
      rw [denote_applyBindings ρ bindings head (correct head List.mem_cons_self),
        denoteList_map_applyBindings ρ bindings tail
          (fun p member => correct p (List.mem_cons_of_mem _ member))]

end Denotation

/-! ## Bindings: what matching binds, and what merging keeps -/

section Bindings

/-- One step of merging. -/
theorem mergeBindings_cons (first : Bindings) (key : String) (value : Pattern)
    (rest : Bindings) :
    mergeBindings first ((key, value) :: rest) =
      match first.find? (·.1 == key) with
      | none => mergeBindings ((key, value) :: first) rest
      | some (_, existing) => if existing == value then mergeBindings first rest else none := by
  simp only [mergeBindings, List.foldlM_cons]
  cases first.find? (·.1 == key) with
  | none => rfl
  | some entry =>
      obtain ⟨_, existing⟩ := entry
      by_cases agree : (existing == value) = true <;> simp [agree]

/-- A merged binding list selects, for each name, the entry of one of its two
inputs. -/
theorem mergeBindings_find_cases : ∀ {first second merged : Bindings},
    mergeBindings first second = some merged → ∀ name : String,
    merged.find? (·.1 == name) = first.find? (·.1 == name) ∨
      merged.find? (·.1 == name) = second.find? (·.1 == name)
  | first, [], merged, merge, name => by
      simp only [mergeBindings, List.foldlM_nil] at merge
      have : merged = first := (Option.some.inj merge).symm
      exact Or.inl (by rw [this])
  | first, (key, value) :: rest, merged, merge, name => by
      rw [mergeBindings_cons] at merge
      cases found : first.find? (·.1 == key) with
      | none =>
          simp only [found] at merge
          by_cases keyName : key = name
          · subst keyName
            right
            have inMerged := mergeBindings_subsumed_left merge
              (x := key) (v := value) (by simp)
            rw [inMerged]
            simp
          · have keyName' : (key == name) = false := by simpa using keyName
            rcases mergeBindings_find_cases merge name with same | same
            · left
              rw [same]
              simp [keyName']
            · right
              rw [same]
              simp [keyName']
      | some entry =>
          obtain ⟨entryKey, existing⟩ := entry
          by_cases agree : (existing == value) = true
          · simp only [found, agree, if_true] at merge
            by_cases keyName : key = name
            · subst keyName
              left
              have tested := List.find?_some found
              have entryKeyEq : entryKey = key := beq_iff_eq.mp tested
              subst entryKeyEq
              rw [mergeBindings_subsumed_left merge found, found]
            · have keyName' : (key == name) = false := by simpa using keyName
              rcases mergeBindings_find_cases merge name with same | same
              · exact Or.inl same
              · right
                rw [same]
                simp [keyName']
          · simp [found, agree] at merge

/-- Merging two lists that a third extends gives a list it extends. -/
theorem extends_of_merge {first second merged target : Bindings}
    (merge : mergeBindings first second = some merged)
    (firstExtends : BindingsExtends first target) (secondExtends : BindingsExtends second target) :
    BindingsExtends merged target := by
  intro name value found
  rcases mergeBindings_find_cases merge name with same | same
  · exact firstExtends name value (same ▸ found)
  · exact secondExtends name value (same ▸ found)

theorem extends_refl (bindings : Bindings) : BindingsExtends bindings bindings :=
  fun _ _ found => found

theorem extends_trans {first second third : Bindings}
    (firstSecond : BindingsExtends first second) (secondThird : BindingsExtends second third) :
    BindingsExtends first third :=
  fun name value found => secondThird name value (firstSecond name value found)

theorem extends_left_of_merge {first second merged : Bindings}
    (merge : mergeBindings first second = some merged) : BindingsExtends first merged :=
  fun _ _ found => mergeBindings_subsumed_left merge found

theorem extends_right_of_merge {first second merged : Bindings}
    (merge : mergeBindings first second = some merged) : BindingsExtends second merged :=
  fun _ _ found => mergeBindings_subsumed_right merge found

/-- Matching a first-order schema binds every metavariable of the schema. -/
theorem matchRel_binds (pattern : Pattern) :
    ∀ (term : Pattern) (bindings : Bindings), Pattern.isMatchCorrect pattern = true →
      MatchRel pattern term bindings →
      ∀ name ∈ pattern.freeFvarNames, ∃ value, bindings.find? (·.1 == name) = some (name, value) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _ _ _ name member; simp [Pattern.freeFvarNames] at member
  | hfvar varName =>
      intro term bindings _ matched name member
      simp only [Pattern.freeFvarNames, List.mem_singleton] at member
      subst member
      cases matched
      exact ⟨term, by simp⟩
  | happly label args ih =>
      intro term bindings correct matched name member
      simp only [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
      simp only [Pattern.freeFvarNames, List.mem_flatMap] at member
      obtain ⟨arg, argMember, nameMember⟩ := member
      cases matched with
      | apply argsMatched _ =>
          have argsBind : ∀ (patterns terms : List Pattern) (bound : Bindings),
              (∀ q ∈ patterns, q ∈ args) → isMatchCorrectListAux patterns = true →
              MatchArgsRel patterns terms bound →
              ∀ q ∈ patterns, name ∈ q.freeFvarNames →
                ∃ value, bound.find? (·.1 == name) = some (name, value) := by
            intro patterns
            induction patterns with
            | nil => intro _ _ _ _ _ q member; cases member
            | cons head tail tailIh =>
                intro terms bound within correctList argsRel q qMember nameIn
                simp only [isMatchCorrectListAux, Bool.and_eq_true] at correctList
                cases argsRel with
                | cons headMatched tailMatched merged =>
                    rcases List.mem_cons.mp qMember with rfl | later
                    · obtain ⟨value, found⟩ := ih q (within q List.mem_cons_self) _ _
                        correctList.1 headMatched name nameIn
                      exact ⟨value, mergeBindings_subsumed_left merged found⟩
                    · obtain ⟨value, found⟩ := tailIh _ _
                        (fun p member => within p (List.mem_cons_of_mem _ member))
                        correctList.2 tailMatched q later nameIn
                      exact ⟨value, mergeBindings_subsumed_right merged found⟩
          exact argsBind args _ bindings (fun _ member => member) correct argsMatched
            arg argMember nameMember
  | hlambda => intro _ _ correct; simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hmultiLambda => intro _ _ correct; simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hsubst => intro _ _ correct; simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hcollection => intro _ _ correct; simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct

/-- When every metavariable of a schema is bound, extending the bindings leaves
its instance unchanged. -/
theorem applyBindings_of_extends_of_bound {initial final : Bindings} (pattern : Pattern)
    (extension : BindingsExtends initial final)
    (bound : ∀ name ∈ pattern.freeFvarNames,
      ∃ value, initial.find? (·.1 == name) = some (name, value)) :
    applyBindings final pattern = applyBindings initial pattern := by
  apply applyBindings_congr
  intro name member
  obtain ⟨value, found⟩ := bound name member
  rw [found, extension name value found]

/-- A matched relation row is the instance of the premise arguments under every
binding list that extends both the bindings before the premise and the row's
own bindings. -/
theorem matchRelationArgs_correct : ∀ (args row : List Pattern) (seed extension : Bindings),
    (∀ arg ∈ args, Pattern.isMatchCorrect arg = true) →
    extension ∈ matchRelationArgs seed args row →
    ∀ final : Bindings, BindingsExtends seed final → BindingsExtends extension final →
      args.map (applyBindings final) = row
  | [], [], _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, member, _, _, _ => by simp [matchRelationArgs] at member
  | _ :: _, [], _, _, _, member, _, _, _ => by simp [matchRelationArgs] at member
  | arg :: args, value :: values, seed, extension, correct, member, final, seedExtends,
      extensionExtends => by
      simp only [matchRelationArgs, List.mem_flatMap] at member
      obtain ⟨head, headMember, rest⟩ := member
      cases seedMerge : mergeBindings seed head with
      | none => simp [seedMerge] at rest
      | some extended =>
          simp only [seedMerge, List.mem_filterMap] at rest
          obtain ⟨tail, tailMember, headTail⟩ := rest
          have headFinal : BindingsExtends head final :=
            extends_trans (extends_left_of_merge headTail) extensionExtends
          have tailFinal : BindingsExtends tail final :=
            extends_trans (extends_right_of_merge headTail) extensionExtends
          have extendedFinal : BindingsExtends extended final :=
            extends_of_merge seedMerge seedExtends headFinal
          have headValue : applyBindings final arg = value := by
            cases arg with
            | fvar name =>
                simp only [matchRelationArgument] at headMember
                cases looked : seed.lookup name with
                | some existing =>
                    simp only [looked] at headMember
                    by_cases same : existing = value
                    · subst same
                      have found := lookup_preserved seedExtends looked
                      simp only [Bindings.lookup] at found
                      obtain ⟨entry, foundEntry, entryValue⟩ := Option.map_eq_some_iff.mp found
                      obtain ⟨entryKey, entryVal⟩ := entry
                      simp only at entryValue
                      subst entryValue
                      simp [applyBindings, foundEntry]
                    · simp [same] at headMember
                | none =>
                    simp only [looked, List.mem_singleton] at headMember
                    subst headMember
                    have found := headFinal name value (by simp)
                    simp [applyBindings, found]
            | _ =>
                simp only [matchRelationArgument] at headMember
                exact matchRel_correct_of_extends (matchPattern_sound headMember)
                  (correct _ List.mem_cons_self) headFinal
          have tailValues := matchRelationArgs_correct args values extended tail
            (fun arg member => correct arg (List.mem_cons_of_mem _ member)) tailMember final
            extendedFinal tailFinal
          simp only [List.map_cons, headValue, tailValues]

end Bindings

/-! ## Valid rules, certified environments, and the evaluator's shape -/

section Soundness

variable {V : Type} (A : PatternAlgebra V)

mutual
/-- The metavariables of a first-order pattern, by structural recursion. -/
def patternNames : Pattern → List String
  | .fvar name => [name]
  | .apply _ args => patternNamesList args
  | .bvar _ => []
  | .lambda _ _ => []
  | .multiLambda _ _ _ => []
  | .subst _ _ => []
  | .collection _ _ _ => []

def patternNamesList : List Pattern → List String
  | [] => []
  | pattern :: patterns => patternNames pattern ++ patternNamesList patterns
end

theorem patternNames_eq_freeFvarNames (pattern : Pattern)
    (correct : Pattern.isMatchCorrect pattern = true) :
    patternNames pattern = pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [patternNames, Pattern.freeFvarNames]
  | hfvar name => simp [patternNames, Pattern.freeFvarNames]
  | happly label args ih =>
      simp only [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
      have list : ∀ patterns : List Pattern, (∀ q ∈ patterns, q ∈ args) →
          isMatchCorrectListAux patterns = true →
          patternNamesList patterns = patterns.flatMap Pattern.freeFvarNames := by
        intro patterns
        induction patterns with
        | nil => intro _ _; rfl
        | cons head tail tailIh =>
            intro within correctList
            simp only [isMatchCorrectListAux, Bool.and_eq_true] at correctList
            simp only [patternNamesList, List.flatMap_cons]
            rw [ih head (within head List.mem_cons_self) correctList.1,
              tailIh (fun q member => within q (List.mem_cons_of_mem _ member)) correctList.2]
      simp only [patternNames, Pattern.freeFvarNames]
      exact list args (fun _ member => member) correct
  | hlambda => simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hmultiLambda => simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hsubst => simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct
  | hcollection => simp [Pattern.isMatchCorrect, isMatchCorrectAux] at correct

/-- What a relation name relates, as value tuples. -/
abbrev RelationMeaning (V : Type) := String → List V → Prop

/-- The semantic reading of a premise under a valuation of the rule's
metavariables.  Premise forms the first-order evaluator does not support are
read as unsatisfiable; `ruleDenotable` excludes them. -/
def PremiseHolds (M : RelationMeaning V) (ν : String → Option V) : Premise → Prop
  | .relationQuery relation args => ∃ values, denoteList A ν args = some values ∧ M relation values
  | .congruence source target => ∀ value, denote A ν source = some value →
      denote A ν target = some value
  | .freshness _ => False
  | .scopedStep _ => False
  | .forAll _ _ _ => False

/-- A rule is valid when, under every valuation satisfying its premises, the
right side denotes whatever the left side denotes. -/
def RuleValid (M : RelationMeaning V) (rule : RewriteRule) : Prop :=
  ∀ ν : String → Option V, (∀ premise ∈ rule.premises, PremiseHolds A M ν premise) →
    ∀ value, denote A ν rule.left = some value → denote A ν rule.right = some value

/-- An environment certifies a meaning under a valuation when every row it
returns denotes a related tuple. -/
def Certifies (M : RelationMeaning V) (ρ : String → Option V) (env : RelationEnv) : Prop :=
  ∀ relation args row, row ∈ env.tuples relation args →
    ∃ values, denoteList A ρ row = some values ∧ M relation values

/-- The premise forms the first-order evaluator reads: relation queries other
than the built-in `eq`, with first-order arguments, and congruence premises
whose source uses only metavariables of the left side. -/
def premiseDenotable (leftNames : List String) : Premise → Bool
  | .relationQuery relation args =>
      relation != "eq" && args.all Pattern.isMatchCorrect
  | .congruence source target =>
      Pattern.isMatchCorrect source && Pattern.isMatchCorrect target &&
        (patternNames source).all leftNames.contains
  | .freshness _ => false
  | .scopedStep _ => false
  | .forAll _ _ _ => false

/-- First-order sides and denotable premises. -/
def ruleDenotable (rule : RewriteRule) : Bool :=
  Pattern.isMatchCorrect rule.left && Pattern.isMatchCorrect rule.right &&
    rule.premises.all (premiseDenotable (patternNames rule.left))

variable {A}

private theorem builtinRelationTuples_eq_nil (lang : LanguageDef) {relation : String}
    (notEq : (relation != "eq") = true) (args : List Pattern) :
    builtinRelationTuples lang relation args = [] := by
  unfold builtinRelationTuples
  split
  · simp at notEq
  · rfl

/-- One evaluated premise extends the bindings, and its reading holds under
every further extension. -/
private theorem premiseAt_sound {M : RelationMeaning V} {ρ : String → Option V}
    {env : RelationEnv} (certified : Certifies A M ρ env) {lang : LanguageDef} {fuel : Nat}
    (stepSound : ∀ source target, StepAt (engineBasePremises env) lang fuel source target →
      ∀ value, denote A ρ source = some value → denote A ρ target = some value)
    {leftNames : List String} {before after : Bindings} {premise : Premise}
    (evaluated : PremiseAt (engineBasePremises env) lang fuel before premise after)
    (shape : premiseDenotable leftNames premise = true)
    (bound : ∀ name ∈ leftNames, ∃ value, before.find? (·.1 == name) = some (name, value)) :
    BindingsExtends before after ∧
      ∀ final, BindingsExtends after final → PremiseHolds A M (extend A ρ final) premise := by
  cases evaluated with
  | freshness _ => simp [premiseDenotable] at shape
  | forAll _ => simp [premiseDenotable] at shape
  | scopedRoot _ _ _ _ => simp [premiseDenotable] at shape
  | relationQuery returned =>
      rename_i relation args
      simp only [premiseDenotable, Bool.and_eq_true, List.all_eq_true] at shape
      simp only [engineBasePremises, premiseStepWithEnv, relationQueryStep, List.mem_flatMap,
        List.mem_filterMap, List.mem_append] at returned
      obtain ⟨row, rowMember, extension, matched, merged⟩ := returned
      rw [builtinRelationTuples_eq_nil lang shape.1] at rowMember
      rcases rowMember with builtin | rowMember
      · cases builtin
      obtain ⟨values, rowValues, related⟩ := certified _ _ _ rowMember
      refine ⟨extends_left_of_merge merged, fun final afterFinal => ?_⟩
      have instances : args.map (applyBindings final) = row :=
        matchRelationArgs_correct args row before extension shape.2 matched final
          (extends_trans (extends_left_of_merge merged) afterFinal)
          (extends_trans (extends_right_of_merge merged) afterFinal)
      refine ⟨values, ?_, related⟩
      rw [← denoteList_map_applyBindings ρ final args shape.2, instances, rowValues]
  | congruence stepped targetMatched merged =>
      rename_i premiseBindings source target candidate
      simp only [premiseDenotable, Bool.and_eq_true, List.all_eq_true] at shape
      obtain ⟨⟨sourceCorrect, targetCorrect⟩, sourceNames⟩ := shape
      refine ⟨extends_left_of_merge merged, fun final afterFinal => ?_⟩
      intro value sourceValue
      have sourceBound : ∀ name ∈ source.freeFvarNames,
          ∃ value, before.find? (·.1 == name) = some (name, value) :=
        fun name member => bound name (by
          rw [← patternNames_eq_freeFvarNames source sourceCorrect] at member
          simpa using sourceNames name member)
      have sourceSame : applyBindings final source = applyBindings before source :=
        applyBindings_of_extends_of_bound source
          (extends_trans (extends_left_of_merge merged) afterFinal) sourceBound
      have targetSame : applyBindings final target = candidate :=
        matchRel_correct_of_extends (matchPattern_sound targetMatched) targetCorrect
          (extends_trans (extends_right_of_merge merged) afterFinal)
      rw [← denote_applyBindings ρ final source sourceCorrect, sourceSame] at sourceValue
      rw [← denote_applyBindings ρ final target targetCorrect, targetSame]
      exact stepSound _ _ stepped value sourceValue

/-- An evaluated premise list extends the bindings, and every premise's reading
holds under every further extension. -/
private theorem premisesAt_sound {M : RelationMeaning V} {ρ : String → Option V}
    {env : RelationEnv} (certified : Certifies A M ρ env) {lang : LanguageDef} {fuel : Nat}
    (stepSound : ∀ source target, StepAt (engineBasePremises env) lang fuel source target →
      ∀ value, denote A ρ source = some value → denote A ρ target = some value)
    {leftNames : List String} :
    ∀ (premises : List Premise) (before after : Bindings),
      PremisesAt (engineBasePremises env) lang fuel before premises after →
      premises.all (premiseDenotable leftNames) = true →
      (∀ name ∈ leftNames, ∃ value, before.find? (·.1 == name) = some (name, value)) →
      BindingsExtends before after ∧
        ∀ final, BindingsExtends after final →
          ∀ premise ∈ premises, PremiseHolds A M (extend A ρ final) premise
  | [], before, after, evaluated, _, _ => by
      cases evaluated
      exact ⟨extends_refl _, fun _ _ _ member => by cases member⟩
  | premise :: premises, before, after, evaluated, shape, bound => by
      cases evaluated with
      | cons first rest =>
          rename_i middle
          simp only [List.all_cons, Bool.and_eq_true] at shape
          obtain ⟨firstExtends, firstHolds⟩ :=
            premiseAt_sound certified stepSound first shape.1 bound
          have middleBound : ∀ name ∈ leftNames,
              ∃ value, middle.find? (·.1 == name) = some (name, value) := by
            intro name member
            obtain ⟨value, found⟩ := bound name member
            exact ⟨value, firstExtends name value found⟩
          obtain ⟨restExtends, restHolds⟩ :=
            premisesAt_sound certified stepSound premises middle after rest shape.2 middleBound
          refine ⟨extends_trans firstExtends restExtends, fun final afterFinal p member => ?_⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact firstHolds final (extends_trans restExtends afterFinal)
          · exact restHolds final afterFinal p later

/-- **Soundness of authored rewriting.**  Under an environment that certifies the
relation meaning, every step of the least contextual relation of a language
whose rules are denotable and valid preserves the denotation of its source. -/
theorem step_preserves {M : RelationMeaning V} {ρ : String → Option V} {env : RelationEnv}
    (certified : Certifies A M ρ env) {lang : LanguageDef}
    (shape : ∀ rule ∈ lang.rewrites, ruleDenotable rule = true)
    (valid : ∀ rule ∈ lang.rewrites, RuleValid A M rule) {source target : Pattern}
    (step : Step (engineBasePremises env) lang source target) :
    ∀ value, denote A ρ source = some value → denote A ρ target = some value := by
  obtain ⟨fuel, step⟩ := step
  induction fuel generalizing source target with
  | zero => cases step
  | succ fuel ih =>
      cases step with
      | rule member matched premises applied =>
          rename_i rule initial final
          have ruleShape := shape rule member
          simp only [ruleDenotable, Bool.and_eq_true] at ruleShape
          obtain ⟨⟨leftCorrect, rightCorrect⟩, premiseShape⟩ := ruleShape
          rw [matchPatternForRule_eq_syntactic] at matched
          have matchedRel := matchPattern_sound matched
          have leftBound : ∀ name ∈ patternNames rule.left,
              ∃ value, initial.find? (·.1 == name) = some (name, value) := by
            rw [patternNames_eq_freeFvarNames rule.left leftCorrect]
            exact matchRel_binds rule.left source initial leftCorrect matchedRel
          obtain ⟨initialFinal, holds⟩ := premisesAt_sound certified
            (fun source target stepped => ih stepped) rule.premises initial final premises
            premiseShape leftBound
          have leftInstance : applyBindings final rule.left = source :=
            matchRel_correct_of_extends matchedRel leftCorrect initialFinal
          have rightInstance : applyBindings final rule.right = target := by
            rw [← applied]
            symm
            apply applyBindingsForRuleUsing_empty_eq_applyBindings
            exact ruleDepthAligned_of_binderFree rule
              (binderFree_of_isMatchCorrectAux _ leftCorrect)
              (binderFree_of_isMatchCorrectAux _ rightCorrect)
          intro value sourceValue
          rw [← leftInstance, denote_applyBindings ρ final rule.left leftCorrect] at sourceValue
          rw [← rightInstance, denote_applyBindings ρ final rule.right rightCorrect]
          exact valid rule member (extend A ρ final) (holds final (extends_refl _)) value
            sourceValue

/-- A language whose rules are all valid and denotable, and its reachability:
every finite chain of steps preserves the denotation. -/
theorem steps_preserve {M : RelationMeaning V} {ρ : String → Option V} {env : RelationEnv}
    (certified : Certifies A M ρ env) {lang : LanguageDef}
    (shape : ∀ rule ∈ lang.rewrites, ruleDenotable rule = true)
    (valid : ∀ rule ∈ lang.rewrites, RuleValid A M rule) {source target : Pattern}
    (steps : Relation.ReflTransGen (Step (engineBasePremises env) lang) source target) :
    ∀ value, denote A ρ source = some value → denote A ρ target = some value := by
  induction steps with
  | refl => exact fun _ h => h
  | tail _ last ih =>
      exact fun value h => step_preserves certified shape valid last value (ih value h)

/-- A congruence rule `f(…, x, …) ↦ f(…, x', …)` with premise `x ↦ x'` is valid
in every algebra and for every relation meaning. -/
theorem congruence_valid (M : RelationMeaning V) (label : String)
    (before after : List Pattern) (name name' : String) (rule : RewriteRule)
    (premisesEq : rule.premises = [.congruence (.fvar name) (.fvar name')])
    (leftEq : rule.left = .apply label (before ++ .fvar name :: after))
    (rightEq : rule.right = .apply label (before ++ .fvar name' :: after)) :
    RuleValid A M rule := by
  intro ν holds value leftValue
  have premise := holds (.congruence (.fvar name) (.fvar name')) (by simp [premisesEq])
  simp only [PremiseHolds, denote_fvar] at premise
  rw [leftEq, denote_apply] at leftValue
  rw [rightEq, denote_apply]
  have split : ∀ (prefixArgs : List Pattern) (suffix : List Pattern) (values : List V),
      denoteList A ν (prefixArgs ++ .fvar name :: suffix) = some values →
      denoteList A ν (prefixArgs ++ .fvar name' :: suffix) = some values := by
    intro prefixArgs
    induction prefixArgs with
    | nil =>
        intro suffix values h
        simp only [List.nil_append, denoteList_cons, denote_fvar] at h ⊢
        cases nameValue : ν name with
        | none => simp [nameValue] at h
        | some v => rw [premise v nameValue]; simpa [nameValue] using h
    | cons head tail ih =>
        intro suffix values h
        simp only [List.cons_append, denoteList_cons] at h ⊢
        cases headValue : denote A ν head with
        | none => simp [headValue] at h
        | some v =>
            simp only [headValue, Option.bind_some] at h ⊢
            cases tailValues : denoteList A ν (tail ++ .fvar name :: suffix) with
            | none => simp [tailValues] at h
            | some vs => rw [ih suffix vs tailValues]; simpa [tailValues] using h
  cases values : denoteList A ν (before ++ .fvar name :: after) with
  | none => simp [values] at leftValue
  | some vs => rw [split before after vs values]; simpa [values] using leftValue

end Soundness

#print axioms denote_applyBindings
#print axioms mergeBindings_find_cases
#print axioms matchRel_binds
#print axioms matchRelationArgs_correct
#print axioms step_preserves
#print axioms steps_preserve
#print axioms congruence_valid

end Mettapedia.OSLF.Framework.WMCalculusPatternDenotation
