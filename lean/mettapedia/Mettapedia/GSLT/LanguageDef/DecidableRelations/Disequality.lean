import Mettapedia.GSLT.LanguageDef.DecidableRelations.Stores
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Std.Data.String.ToNat

/-!
# Disequality derived by the language's own rules

A signature, a list of constructors with their arities, generates two judgments whose rules any language can hold:
- `Equal(a, b) ~> Yes`, one rule, by the repeated pattern variable `Equal(x, x)`;
- `Unequal(a, b) ~> Yes`:
  - a clash rule for every pair of differently named constructors;
  - for every constructor and argument position, a rule whose premise is `Unequal` at that argument.

Take a language that holds these rules and no other rule applying to `Equal` or `Unequal` terms (`Private`). On
first-order ground terms of the signature, the language then derives `Equal(a, b)` exactly when `a = b`
(`derives_equal_iff`), and `Unequal(a, b)` exactly when `a ≠ b` (`derives_unequal_iff`). So the pair is complemented there
(`equality_complemented`): the failure of equality is witnessed by a derivation of disequality, by the language's own rules.

The derivations are steps of the reference semantics (`ReferenceStep.StepValid`), the meaning the native types of the
language are stated over.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-! ## Variables -/

/-- The variable of a family at an index: `x0`, `x1`, …. -/
def variableName (family : String) (index : Nat) : String := family ++ Nat.repr index

theorem variableName_injective {family : String} {first second : Nat}
    (same : variableName family first = variableName family second) : first = second := by
  unfold variableName at same
  have lists := congrArg String.toList same
  simp only [String.toList_append] at lists
  exact Nat.repr_inj.mp (String.toList_inj.mp (List.append_cancel_left lists))

theorem variableName_x_ne_y (first second : Nat) : variableName "x" first ≠ variableName "y" second := by
  intro same
  have lists := congrArg String.toList same
  simp [variableName, String.toList_append] at lists

/-- The variables `family start`, …, `family (start + count - 1)`. -/
def variablesFrom (family : String) : Nat → Nat → List Pattern
  | _, 0 => []
  | start, count + 1 => .fvar (variableName family start) :: variablesFrom family (start + 1) count

theorem variablesFrom_length (family : String) : ∀ start count, (variablesFrom family start count).length = count
  | _, 0 => rfl
  | start, count + 1 => by simp [variablesFrom, variablesFrom_length family (start + 1) count]

/-- The variable at a position of a variable list. -/
theorem variablesFrom_getElem (family : String) : ∀ (start count index : Nat) (inside : index < count),
    (variablesFrom family start count)[index]'(by rw [variablesFrom_length]; exact inside) =
      .fvar (variableName family (start + index))
  | _, 0, _, inside => absurd inside (Nat.not_lt_zero _)
  | start, count + 1, 0, _ => by simp [variablesFrom]
  | start, count + 1, index + 1, inside => by
      simp only [variablesFrom, List.getElem_cons_succ]
      rw [variablesFrom_getElem family (start + 1) count index (by omega)]
      congr 2
      omega

/-! ## The generated rules -/

/-- The judgment of equality. -/
def equalJudgment : String := "Equal"

/-- The judgment of disequality. -/
def unequalJudgment : String := "Unequal"

/-- A constructor applied to a family of variables. -/
def constructorPattern (family : String) (constructor : String × Nat) : Pattern :=
  .apply constructor.1 (variablesFrom family 0 constructor.2)

/-- `Equal(x, x) ~> Yes`. -/
def equalRule : RewriteRule :=
  ⟨"Equal", [], [], .apply equalJudgment [.fvar "x", .fvar "x"], yes, none⟩

/-- `Unequal(c(x…), d(y…)) ~> Yes` for differently named `c` and `d`. -/
def clashRule (first second : String × Nat) : RewriteRule :=
  ⟨s!"Clash:{first.1}:{second.1}", [], [],
    .apply unequalJudgment [constructorPattern "x" first, constructorPattern "y" second], yes, none⟩

/-- `Unequal(c(x…), c(y…)) ~> Yes` if `Unequal(xᵢ, yᵢ) ~> Yes`. -/
def argumentRule (constructor : String × Nat) (position : Nat) : RewriteRule :=
  ⟨s!"Argument:{constructor.1}:{position}", [],
    [.congruence (.apply unequalJudgment [.fvar (variableName "x" position), .fvar (variableName "y" position)]) yes],
    .apply unequalJudgment [constructorPattern "x" constructor, constructorPattern "y" constructor], yes, none⟩

/-- **The rules of equality and disequality** a signature generates. -/
def disequalityRules (signature : List (String × Nat)) : List RewriteRule :=
  equalRule ::
    ((signature.flatMap fun first =>
        signature.filterMap fun second => if first.1 = second.1 then none else some (clashRule first second)) ++
      signature.flatMap fun constructor => (List.range constructor.2).map (argumentRule constructor))

/-- The generated rules are equality, clashes of different names, and argument rules. -/
theorem mem_disequalityRules {signature : List (String × Nat)} {rule : RewriteRule}
    (member : rule ∈ disequalityRules signature) :
    rule = equalRule ∨
      (∃ first ∈ signature, ∃ second ∈ signature, first.1 ≠ second.1 ∧ rule = clashRule first second) ∨
      (∃ constructor ∈ signature, ∃ position < constructor.2, rule = argumentRule constructor position) := by
  simp only [disequalityRules, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_filterMap,
    List.mem_map, List.mem_range] at member
  rcases member with equal | ⟨first, firstMember, second, secondMember, made⟩ | ⟨constructor, member, position,
    inside, made⟩
  · exact .inl equal
  · by_cases same : first.1 = second.1
    · simp [same] at made
    · simp only [same, if_false, Option.some.injEq] at made
      exact .inr (.inl ⟨first, firstMember, second, secondMember, same, made.symm⟩)
  · exact .inr (.inr ⟨constructor, member, position, inside, made.symm⟩)

/-- **The language's other rules do not apply to equality and disequality judgments.** -/
def Private (language : LanguageDef) (signature : List (String × Nat)) : Prop :=
  ∀ rule ∈ language.rewrites, rule ∉ disequalityRules signature →
    ∀ arguments, matchPattern rule.left (.apply equalJudgment arguments) = [] ∧
      matchPattern rule.left (.apply unequalJudgment arguments) = []

/-- A first-order ground term built from the signature's constructors, at their arities. -/
inductive TermOf (signature : List (String × Nat)) : Pattern → Prop
  | apply {constructor : String} {arguments : List Pattern} :
      (constructor, arguments.length) ∈ signature → (∀ argument ∈ arguments, TermOf signature argument) →
      TermOf signature (.apply constructor arguments)

theorem TermOf.firstOrder {signature : List (String × Nat)} {term : Pattern}
    (over : TermOf signature term) : FirstOrder term := by
  induction over with
  | apply _ _ firstOrder => exact .apply firstOrder

/-! ## Matching the generated patterns -/

/-- Merging bindings of new, distinct names adds them all. -/
theorem mergeBindings_fresh : ∀ (accumulated added : Bindings), (added.map Prod.fst).Nodup →
    (∀ entry ∈ added, entry.1 ∉ accumulated.map Prod.fst) →
      mergeBindings accumulated added = some (added.reverse ++ accumulated)
  | accumulated, [], _, _ => by simp [mergeBindings]
  | accumulated, entry :: added, distinct, fresh => by
      have absent : accumulated.find? (·.1 == entry.1) = none := by
        rw [List.find?_eq_none]
        intro other member same
        simp only [beq_iff_eq] at same
        exact fresh entry (List.mem_cons_self ..) (same ▸ List.mem_map_of_mem member)
      have rest : mergeBindings (entry :: accumulated) added = some (added.reverse ++ entry :: accumulated) := by
        apply mergeBindings_fresh
        · exact (List.nodup_cons.mp distinct).2
        · intro other member
          simp only [List.map_cons, List.mem_cons, not_or]
          refine ⟨fun same => ?_, fresh other (List.mem_cons_of_mem _ member)⟩
          exact (List.nodup_cons.mp distinct).1 (same ▸ List.mem_map_of_mem member)
      have step : mergeBindings accumulated (entry :: added) = mergeBindings (entry :: accumulated) added := by
        simp only [mergeBindings, List.foldlM_cons, absent]
        rfl
      rw [step, rest]
      simp

/-- **Distinct variables match any values of their number.** -/
theorem matchArgsRel_variables (family : String) : ∀ (values : List Pattern) (start : Nat),
    ∃ bindings, MatchArgsRel (variablesFrom family start values.length) values bindings ∧
      (bindings.map Prod.fst).Nodup ∧ ∀ entry ∈ bindings, ∃ index, start ≤ index ∧ entry.1 = variableName family index
  | [], _ => ⟨[], .nil, by simp, by simp⟩
  | value :: values, start => by
      obtain ⟨tail, related, distinct, named⟩ := matchArgsRel_variables family values (start + 1)
      have fresh : ∀ entry ∈ tail, entry.1 ∉ [(variableName family start, value)].map Prod.fst := by
        intro entry member same
        obtain ⟨index, later, equal⟩ := named entry member
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at same
        have := variableName_injective (equal.symm.trans same)
        omega
      refine ⟨tail.reverse ++ [(variableName family start, value)], ?_, ?_, ?_⟩
      · exact .cons .fvar related (mergeBindings_fresh _ _ distinct fresh)
      · rw [List.map_append, List.nodup_append]
        refine ⟨by rw [List.map_reverse]; exact List.nodup_reverse.mpr distinct, by simp, ?_⟩
        intro name member other otherMember same
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at otherMember
        rw [List.map_reverse, List.mem_reverse, List.mem_map] at member
        obtain ⟨entry, entryMember, rfl⟩ := member
        exact fresh entry entryMember (by simp [same, otherMember])
      · intro entry member
        rcases List.mem_append.mp member with inTail | inHead
        · obtain ⟨index, later, equal⟩ := named entry (List.mem_reverse.mp inTail)
          exact ⟨index, by omega, equal⟩
        · simp only [List.mem_singleton] at inHead
          exact ⟨start, le_refl _, by simp [inHead]⟩

/-- A constructor applied to variables matches the constructor applied to values of its arity. -/
theorem matchRel_constructorPattern (family : String) (constructor : String × Nat) {values : List Pattern}
    (arity : values.length = constructor.2) :
    ∃ bindings, MatchRel (constructorPattern family constructor) (.apply constructor.1 values) bindings ∧
      (bindings.map Prod.fst).Nodup ∧ ∀ entry ∈ bindings, ∃ index, entry.1 = variableName family index := by
  obtain ⟨bindings, related, distinct, named⟩ := matchArgsRel_variables family values 0
  refine ⟨bindings, ?_, distinct, fun entry member => ?_⟩
  · unfold constructorPattern
    rw [← arity]
    exact .apply related (variablesFrom_length _ _ _)
  · obtain ⟨index, _, equal⟩ := named entry member
    exact ⟨index, equal⟩

/-- **The disequality patterns match every pair of their constructors' applications.** -/
theorem matchPattern_unequal_nonempty (first second : String × Nat) {firstValues secondValues : List Pattern}
    (firstArity : firstValues.length = first.2) (secondArity : secondValues.length = second.2) :
    ∃ bindings, bindings ∈ matchPattern (.apply unequalJudgment [constructorPattern "x" first, constructorPattern "y" second])
      (.apply unequalJudgment [.apply first.1 firstValues, .apply second.1 secondValues]) := by
  obtain ⟨xs, xRelated, xDistinct, xNamed⟩ := matchRel_constructorPattern "x" first firstArity
  obtain ⟨ys, yRelated, yDistinct, yNamed⟩ := matchRel_constructorPattern "y" second secondArity
  have fresh : ∀ entry ∈ ys, entry.1 ∉ xs.map Prod.fst := by
    intro entry member present
    obtain ⟨index, yName⟩ := yNamed entry member
    obtain ⟨other, otherMember, sameName⟩ := List.mem_map.mp present
    obtain ⟨xIndex, xName⟩ := xNamed other otherMember
    exact variableName_x_ne_y xIndex index (xName.symm.trans (sameName.trans yName))
  refine ⟨ys.reverse ++ xs, matchRel_complete (.apply ?_ rfl)⟩
  exact .cons xRelated (.cons yRelated .nil (mergeBindings_nil_right ys)) (mergeBindings_fresh _ _ yDistinct fresh)

/-- A judgment of one repeated variable matches a pair of equal terms. -/
theorem matchPattern_repeated_self (judgment : String) (term : Pattern) :
    [("x", term)] ∈ matchPattern (.apply judgment [.fvar "x", .fvar "x"]) (.apply judgment [term, term]) := by
  apply matchRel_complete
  refine .apply (.cons .fvar (.cons .fvar .nil (mergeBindings_nil_right _)) ?_) rfl
  simp [mergeBindings, List.find?, BEq.beq]

/-- The equality pattern matches a pair of equal terms. -/
theorem matchPattern_equal_self (term : Pattern) :
    [("x", term)] ∈ matchPattern equalRule.left (.apply equalJudgment [term, term]) :=
  matchPattern_repeated_self equalJudgment term

/-! ## Steps of the generated rules -/

/-- The verdict is first-order. -/
theorem yes_firstOrder : FirstOrder yes := .apply (by simp)

/-- Only the verdict matches the verdict. -/
theorem eq_yes_of_mem_matchPattern {candidate : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern yes candidate) : candidate = yes := by
  rw [matchPattern_firstOrder yes_firstOrder candidate] at matched
  by_cases same : yes = candidate
  · exact same.symm
  · simp [same] at matched

/-- Bindings leave the verdict unchanged. -/
theorem applyBindingsScoped_yes (lhs : Pattern) (bindings : Bindings) (depth : Nat) :
    applyBindingsScoped lhs bindings depth yes = yes := by
  simp [yes]

/-- Lifting leaves a first-order term unchanged. -/
theorem liftBVars_firstOrder (cutoff shift : Nat) {term : Pattern} (first : FirstOrder term) :
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift term = term := by
  induction first with
  | @apply constructor arguments _ unchanged =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
      congr 1
      conv => rhs; rw [← List.map_id arguments]
      exact List.map_congr_left unchanged

/-- Scoped application gives back the first-order value plain application gives a variable. -/
theorem applyBindingsScoped_fvar {lhs : Pattern} {bindings : Bindings} {depth : Nat} {name : String}
    {value : Pattern} (first : FirstOrder value) (applied : applyBindings bindings (.fvar name) = value) :
    applyBindingsScoped lhs bindings depth (.fvar name) = value := by
  simp only [applyBindings] at applied
  simp only [applyBindingsScoped]
  split at applied
  · split
    · rw [applied]; exact liftBVars_firstOrder _ _ first
    · exact applied
  · rename_i missing
    cases first
    cases applied

/-- The variables of a constructor pattern are match-correct. -/
theorem isMatchCorrectList_variablesFrom (family : String) : ∀ start count,
    isMatchCorrectListAux (variablesFrom family start count) = true
  | _, 0 => rfl
  | start, count + 1 => by
      simp [variablesFrom, isMatchCorrectListAux, isMatchCorrectAux, isMatchCorrectList_variablesFrom family]

/-- The disequality patterns are match-correct. -/
theorem isMatchCorrect_unequal (first second : String × Nat) :
    Pattern.isMatchCorrect (.apply unequalJudgment [constructorPattern "x" first, constructorPattern "y" second]) =
      true := by
  simp [Pattern.isMatchCorrect, isMatchCorrectAux, isMatchCorrectListAux, constructorPattern,
    isMatchCorrectList_variablesFrom]

/-- A rule fires as one step from a matched term, given its premises' witnesses. -/
theorem stepValid_of_rule {relEnv : RelationEnv} {language : LanguageDef} {rule : RewriteRule} {term : Pattern}
    {initial final : Bindings} {witnesses : List Witness} (member : rule ∈ language.rewrites)
    (matched : initial ∈ matchPattern rule.left term)
    (premises : PremisesValid relEnv language (captureSites rule) initial rule.premises witnesses final)
    (right : rule.right = yes) : ∃ witness, StepValid relEnv language term witness yes := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  have step := StepValid.rule (relEnv := relEnv) (language := language) found
    (by rw [matchPatternForRule_eq_syntactic]; exact matched) premises
  rw [right, applyBindingsScoped_yes] at step
  exact ⟨_, step⟩

/-- **The data of a step to the verdict**: a rule of the language matched the term, and its premises held. -/
theorem stepValid_yes_cases {relEnv : RelationEnv} {language : LanguageDef} {term : Pattern} {witness : Witness}
    (step : StepValid relEnv language term witness yes) :
    ∃ rule ∈ language.rewrites, ∃ initial final witnesses, initial ∈ matchPattern rule.left term ∧
      PremisesValid relEnv language (captureSites rule) initial rule.premises witnesses final := by
  generalize target : yes = verdict at step
  cases step with
  | rule found matched premises =>
      exact ⟨_, List.mem_of_getElem? found, _, _, _, by rwa [matchPatternForRule_eq_syntactic] at matched,
        premises⟩

/-! ## Equality and disequality, derived -/

section Judgments

variable {relEnv : RelationEnv} {language : LanguageDef} {signature : List (String × Nat)}

/-- The rules other than equality do not apply to an equality judgment. -/
theorem matchPattern_equal_eq_nil {rule : RewriteRule} (member : rule ∈ disequalityRules signature)
    (other : rule ≠ equalRule) (arguments : List Pattern) :
    matchPattern rule.left (.apply equalJudgment arguments) = [] := by
  rcases mem_disequalityRules member with same | ⟨first, _, second, _, _, rfl⟩ | ⟨constructor, _, position, _, rfl⟩
  · exact absurd same other
  · simp [clashRule, matchPattern, equalJudgment, unequalJudgment]
  · simp [argumentRule, matchPattern, equalJudgment, unequalJudgment]

/-- **Equality holds exactly between equal terms.** -/
theorem derives_equal_iff (rules : ∀ rule ∈ disequalityRules signature, rule ∈ language.rewrites)
    (privacy : Private language signature) {first second : Pattern} :
    Derives relEnv language equalJudgment [first, second] ↔ first = second := by
  constructor
  · rintro ⟨witness, step⟩
    obtain ⟨rule, member, initial, final, witnesses, matched, _⟩ := stepValid_yes_cases step
    by_cases generated : rule ∈ disequalityRules signature
    · by_cases isEqual : rule = equalRule
      · subst isEqual
        have correct := matchPattern_correct matched (by simp [equalRule, Pattern.isMatchCorrect, isMatchCorrectAux,
          isMatchCorrectListAux])
        simp only [equalRule, applyBindings, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq] at correct
        exact correct.2.1.symm.trans correct.2.2.1
      · rw [matchPattern_equal_eq_nil generated isEqual] at matched
        simp at matched
    · rw [(privacy rule member generated [first, second]).1] at matched
      simp at matched
  · rintro rfl
    exact stepValid_of_rule (rules equalRule (List.mem_cons_self ..)) (matchPattern_equal_self first) (.nil _) rfl

/-- The arity a signature gives a name is unique when its names are. -/
theorem arity_unique {name : String} {first second : Nat} (names : (signature.map Prod.fst).Nodup)
    (firstMember : (name, first) ∈ signature) (secondMember : (name, second) ∈ signature) : first = second := by
  induction signature with
  | nil => simp at firstMember
  | cons head tail inner =>
      rw [List.map_cons, List.nodup_cons] at names
      rcases List.mem_cons.mp firstMember with headFirst | tailFirst <;>
        rcases List.mem_cons.mp secondMember with headSecond | tailSecond
      · rw [← headFirst] at headSecond
        exact (Prod.mk.inj headSecond).2.symm
      · subst headFirst
        exact absurd (List.mem_map_of_mem (f := Prod.fst) tailSecond) names.1
      · subst headSecond
        exact absurd (List.mem_map_of_mem (f := Prod.fst) tailFirst) names.1
      · exact inner names.2 tailFirst tailSecond

/-- Bindings apply to a constructor pattern argument by argument. -/
theorem applyBindings_constructorPattern (bindings : Bindings) (family : String) (constructor : String × Nat) :
    applyBindings bindings (constructorPattern family constructor) =
      .apply constructor.1 ((variablesFrom family 0 constructor.2).map (applyBindings bindings)) := by
  simp [constructorPattern, applyBindings]

/-- The two sides of equal judgment instances are equal. -/
theorem sides_of_judgment {judgment : String} {left right first second : Pattern}
    (same : Pattern.apply judgment [left, right] = .apply judgment [first, second]) : left = first ∧ right = second := by
  simpa using same

/-- The value bindings give a variable at a position of a constructor pattern. -/
theorem getElem_map_variablesFrom (bindings : Bindings) (family : String) {count position : Nat}
    (inside : position < count) :
    ((variablesFrom family 0 count).map (applyBindings bindings))[position]'(by
        rw [List.length_map, variablesFrom_length]; exact inside) =
      applyBindings bindings (.fvar (variableName family position)) := by
  rw [List.getElem_map, variablesFrom_getElem family 0 count position inside, Nat.zero_add]

/-- The value at a variable of a constructor pattern is one of the instance's arguments. -/
theorem mem_map_variablesFrom (bindings : Bindings) (family : String) {count position : Nat}
    (inside : position < count) :
    applyBindings bindings (.fvar (variableName family position)) ∈
      (variablesFrom family 0 count).map (applyBindings bindings) := by
  rw [← getElem_map_variablesFrom bindings family inside]
  exact List.getElem_mem _

/-- **Disequality holds only between different terms.** -/
theorem ne_of_derives_unequal (privacy : Private language signature) {first : Pattern} (firstOrder : FirstOrder first) :
    ∀ {second : Pattern}, FirstOrder second → Derives relEnv language unequalJudgment [first, second] →
      first ≠ second := by
  induction firstOrder with
  | @apply constructor arguments members inner =>
  intro second secondFirst judged
  obtain ⟨witness, step⟩ := judged
  obtain ⟨rule, member, initial, final, witnesses, matched, premises⟩ := stepValid_yes_cases step
  by_cases generated : rule ∈ disequalityRules signature
  · rcases mem_disequalityRules generated with rfl | ⟨left, _, right, _, different, rfl⟩ |
      ⟨shape, _, position, inside, rfl⟩
    · simp [equalRule, matchPattern, equalJudgment, unequalJudgment] at matched
    · have correct : applyBindings initial
          (.apply unequalJudgment [constructorPattern "x" left, constructorPattern "y" right]) =
          .apply unequalJudgment [.apply constructor arguments, second] :=
        matchPattern_correct matched (isMatchCorrect_unequal left right)
      simp only [applyBindings, List.map_cons, List.map_nil, applyBindings_constructorPattern] at correct
      obtain ⟨firstEq, secondEq⟩ := sides_of_judgment correct
      intro same
      rw [← same] at secondEq
      exact different ((Pattern.apply.inj firstEq).1.trans (Pattern.apply.inj secondEq).1.symm)
    · have correct : applyBindings initial
          (.apply unequalJudgment [constructorPattern "x" shape, constructorPattern "y" shape]) =
          .apply unequalJudgment [.apply constructor arguments, second] :=
        matchPattern_correct matched (isMatchCorrect_unequal shape shape)
      simp only [applyBindings, List.map_cons, List.map_nil, applyBindings_constructorPattern] at correct
      obtain ⟨firstEq, secondEq⟩ := sides_of_judgment correct
      have argumentsEq := (Pattern.apply.inj firstEq).2
      set leftValue := applyBindings initial (.fvar (variableName "x" position)) with leftValueDef
      set rightValue := applyBindings initial (.fvar (variableName "y" position)) with rightValueDef
      have leftMember : leftValue ∈ arguments := argumentsEq ▸ mem_map_variablesFrom initial "x" inside
      have rightFirst : FirstOrder rightValue := by
        rw [← secondEq] at secondFirst
        cases secondFirst with
        | apply secondMembers => exact secondMembers _ (mem_map_variablesFrom initial "y" inside)
      cases premises with
      | cons premise rest =>
          cases premise with
          | base isBaseTrue _ => simp [isBase] at isBaseTrue
          | step endpoints stepped matchedYes _ =>
              simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
              obtain ⟨rfl, rfl⟩ := endpoints
              have candidateYes := eq_yes_of_mem_matchPattern matchedYes
              subst candidateYes
              rw [applyBindingsScoped_apply] at stepped
              simp only [List.map_cons, List.map_nil] at stepped
              rw [applyBindingsScoped_fvar (members _ leftMember) leftValueDef.symm,
                applyBindingsScoped_fvar rightFirst rightValueDef.symm] at stepped
              have apart := inner leftValue leftMember rightFirst ⟨_, stepped⟩
              intro same
              rw [← same] at secondEq
              have rightArguments := (Pattern.apply.inj secondEq).2
              apply apart
              rw [leftValueDef, rightValueDef, ← getElem_map_variablesFrom initial "x" inside,
                ← getElem_map_variablesFrom initial "y" inside]
              exact List.getElem_of_eq (argumentsEq.trans rightArguments.symm) _
  · rw [(privacy rule member generated [.apply constructor arguments, second]).2] at matched
    simp at matched


/-- **Disequality holds between every two different terms of the signature.** -/
theorem derives_unequal_of_ne (rules : ∀ rule ∈ disequalityRules signature, rule ∈ language.rewrites)
    (names : (signature.map Prod.fst).Nodup) {first : Pattern} (over : TermOf signature first) :
    ∀ {second : Pattern}, TermOf signature second → first ≠ second →
      Derives relEnv language unequalJudgment [first, second] := by
  induction over with
  | @apply constructor arguments signed members inner =>
  intro second secondOver different
  cases secondOver with
  | @apply other values otherSigned valueMembers =>
  by_cases sameName : constructor = other
  · subst sameName
    have arity := arity_unique names signed otherSigned
    have differ : ∃ position, ∃ inside : position < arguments.length,
        arguments[position] ≠ values[position]'(arity ▸ inside) := by
      by_contra none
      push Not at none
      exact different (congrArg _ (List.ext_getElem arity fun position first _ => none position first))
    obtain ⟨position, inside, apart⟩ := differ
    obtain ⟨premiseWitness, premiseStep⟩ :=
      inner _ (List.getElem_mem inside) (valueMembers _ (List.getElem_mem _)) apart
    have ruleMember : argumentRule (constructor, arguments.length) position ∈ disequalityRules signature := by
      simp only [disequalityRules, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
      exact .inr (.inr ⟨_, signed, position, inside, rfl⟩)
    obtain ⟨initial, matchedInitial⟩ :=
      matchPattern_unequal_nonempty (constructor, arguments.length) (constructor, arguments.length) rfl arity.symm
    have correct : applyBindings initial (.apply unequalJudgment
        [constructorPattern "x" (constructor, arguments.length), constructorPattern "y" (constructor, arguments.length)]) =
        .apply unequalJudgment [.apply constructor arguments, .apply constructor values] :=
      matchPattern_correct matchedInitial (isMatchCorrect_unequal _ _)
    simp only [applyBindings, List.map_cons, List.map_nil, applyBindings_constructorPattern] at correct
    obtain ⟨firstEq, secondEq⟩ := sides_of_judgment correct
    have leftAt : applyBindings initial (.fvar (variableName "x" position)) = arguments[position] := by
      rw [← getElem_map_variablesFrom initial "x" inside]
      exact List.getElem_of_eq (Pattern.apply.inj firstEq).2 _
    have rightAt : applyBindings initial (.fvar (variableName "y" position)) = values[position]'(arity ▸ inside) := by
      rw [← getElem_map_variablesFrom initial "y" inside]
      exact List.getElem_of_eq (Pattern.apply.inj secondEq).2 _
    have premises : PremisesValid relEnv language (captureSites (argumentRule (constructor, arguments.length) position))
        initial (argumentRule (constructor, arguments.length) position).premises
        [.premiseStep premiseWitness yes [] initial] initial := by
      refine .cons (.step rfl ?_ ?_ (mergeBindings_nil_right initial)) (.nil initial)
      · rw [applyBindingsScoped_apply]
        simp only [List.map_cons, List.map_nil]
        rw [applyBindingsScoped_fvar (members _ (List.getElem_mem inside)).firstOrder leftAt,
          applyBindingsScoped_fvar (valueMembers _ (List.getElem_mem _)).firstOrder rightAt]
        exact premiseStep
      · rw [matchPattern_firstOrder yes_firstOrder yes]
        simp
    exact stepValid_of_rule (rules _ ruleMember) matchedInitial premises rfl
  · have ruleMember : clashRule (constructor, arguments.length) (other, values.length) ∈
        disequalityRules signature := by
      simp only [disequalityRules, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_filterMap]
      exact .inr (.inl ⟨_, signed, _, otherSigned, by simp [sameName]⟩)
    obtain ⟨initial, matchedInitial⟩ :=
      matchPattern_unequal_nonempty (constructor, arguments.length) (other, values.length) rfl rfl
    exact stepValid_of_rule (rules _ ruleMember) matchedInitial (.nil initial) rfl

/-- **Disequality holds exactly between different terms** of the signature. -/
theorem derives_unequal_iff (rules : ∀ rule ∈ disequalityRules signature, rule ∈ language.rewrites)
    (privacy : Private language signature) (names : (signature.map Prod.fst).Nodup) {first second : Pattern}
    (firstOver : TermOf signature first) (secondOver : TermOf signature second) :
    Derives relEnv language unequalJudgment [first, second] ↔ first ≠ second :=
  ⟨ne_of_derives_unequal privacy firstOver.firstOrder secondOver.firstOrder,
    derives_unequal_of_ne rules names firstOver secondOver⟩

/-- **Equality and disequality are complemented on the signature's terms**, by the language's own rules: the failure of
equality is witnessed by a derivation of disequality. -/
theorem equality_complemented (rules : ∀ rule ∈ disequalityRules signature, rule ∈ language.rewrites)
    (privacy : Private language signature) (names : (signature.map Prod.fst).Nodup) :
    Complemented (fun pair : Pattern × Pattern => Derives relEnv language equalJudgment [pair.1, pair.2])
      (fun pair => Derives relEnv language unequalJudgment [pair.1, pair.2])
      (fun pair => TermOf signature pair.1 ∧ TermOf signature pair.2) where
  disjoint pair inside equal unequal :=
    ne_of_derives_unequal privacy inside.1.firstOrder inside.2.firstOrder unequal
      ((derives_equal_iff rules privacy).mp equal)
  exhaustive pair inside := by
    by_cases same : pair.1 = pair.2
    · exact .inl ((derives_equal_iff rules privacy).mpr same)
    · exact .inr (derives_unequal_of_ne rules names inside.1 inside.2 same)

end Judgments

end Mettapedia.GSLT.LanguageDef.DecidableRelations
