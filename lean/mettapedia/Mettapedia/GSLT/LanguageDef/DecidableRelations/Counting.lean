import Mettapedia.GSLT.LanguageDef.DecidableRelations.Frame

/-!
# Counting in a closed collection

Three rules count an element `p` in a closed bag or set, with unary numerals:
- `Count(p, {}, Zero) ~> Yes`;
- `Count(p, {p, ...rest}, Succ(n)) ~> Yes` if `Count(p, {...rest}, n) ~> Yes`;
- `Count(p, {x, ...rest}, n) ~> Yes` if `Unequal(x, p) ~> Yes` and `Count(p, {...rest}, n) ~> Yes`.

Each step takes one element out of the collection and asks the same question of the rest. The empty collection ends
the count, so the collection is read as complete, and the language's own disequality decides the elements that are
not `p`.

Take the signature's equality and disequality rules, and no other rule applying to these judgments
(`CountingPrivate`). Then, on a term of the signature and a closed bag or set of such terms:
- the language derives `Count(p, c, k)` exactly when `p` occurs `k` times in `c` (`derives_count_iff`);
- the count zero is non-membership (`derives_count_zero_iff`);
- a count is complemented by the other counts (`count_complemented`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-! ## Numerals and rules -/

/-- The judgment that an element occurs a number of times in a collection. -/
def countJudgment : String := "Count"

/-- The numeral zero. -/
def zeroNumeral : Pattern := .apply "Zero" []

/-- The successor of a numeral. -/
def succNumeral (smaller : Pattern) : Pattern := .apply "Succ" [smaller]

/-- The unary numeral of a natural number. -/
def numeral : ℕ → Pattern
  | 0 => zeroNumeral
  | count + 1 => succNumeral (numeral count)

theorem numeral_firstOrder : ∀ count : ℕ, FirstOrder (numeral count)
  | 0 => .apply (by simp)
  | count + 1 => .apply (by simpa using numeral_firstOrder count)

theorem numeral_eq_zero_iff {count : ℕ} : numeral count = zeroNumeral ↔ count = 0 := by
  cases count <;> simp [numeral, zeroNumeral, succNumeral]

theorem numeral_eq_succ_iff {count : ℕ} {smaller : Pattern} :
    numeral count = succNumeral smaller ↔ ∃ previous, count = previous + 1 ∧ smaller = numeral previous := by
  cases count with
  | zero => simp [numeral, zeroNumeral, succNumeral]
  | succ previous =>
    simp only [numeral, succNumeral, Pattern.apply.injEq, List.cons.injEq, and_true, true_and, Nat.add_right_cancel_iff]
    exact ⟨fun same => ⟨previous, rfl, same.symm⟩, fun ⟨_, same, numeralSame⟩ => same ▸ numeralSame.symm⟩

/-- `Count(p, {}, Zero) ~> Yes`. -/
def countEmptyRule (kind : CollType) : RewriteRule :=
  ⟨"CountEmpty", [], [], .apply countJudgment [.fvar "p", .collection kind [] none, zeroNumeral], yes, none⟩

/-- The premise asking the count of the rest. -/
def countRestPremise (kind : CollType) : Premise :=
  .congruence (.apply countJudgment [.fvar "p", .collection kind [] (some "rest"), .fvar "n"]) yes

/-- `Count(p, {p, ...rest}, Succ(n)) ~> Yes` if `Count(p, {...rest}, n) ~> Yes`. -/
def countHitRule (kind : CollType) : RewriteRule :=
  ⟨"CountHit", [], [countRestPremise kind],
    .apply countJudgment [.fvar "p", .collection kind [.fvar "p"] (some "rest"), succNumeral (.fvar "n")], yes, none⟩

/-- The premise that the element taken differs from the element counted. -/
def countDifferentPremise : Premise := .congruence (.apply unequalJudgment [.fvar "x", .fvar "p"]) yes

/-- `Count(p, {x, ...rest}, n) ~> Yes` if `Unequal(x, p) ~> Yes` and `Count(p, {...rest}, n) ~> Yes`. -/
def countMissRule (kind : CollType) : RewriteRule :=
  ⟨"CountMiss", [], [countDifferentPremise, countRestPremise kind],
    .apply countJudgment [.fvar "p", .collection kind [.fvar "x"] (some "rest"), .fvar "n"], yes, none⟩

/-- **The rules of counting**, with the equality and disequality of the elements' signature. -/
def countingRules (signature : List (String × Nat)) (kind : CollType) : List RewriteRule :=
  disequalityRules signature ++ [countEmptyRule kind, countHitRule kind, countMissRule kind]

/-- **The language's other rules do not apply to the three judgments.** -/
def CountingPrivate (language : LanguageDef) (signature : List (String × Nat)) (kind : CollType) : Prop :=
  ∀ rule ∈ language.rewrites, rule ∉ countingRules signature kind →
    ∀ judgment ∈ [equalJudgment, unequalJudgment, countJudgment], ∀ arguments,
      matchPattern rule.left (.apply judgment arguments) = []

/-- Privacy of the three judgments gives privacy of equality and disequality. -/
theorem CountingPrivate.toPrivate {language : LanguageDef} {signature : List (String × Nat)} {kind : CollType}
    (privacy : CountingPrivate language signature kind) : Private language signature := by
  intro rule member notGenerated arguments
  by_cases inRules : rule ∈ countingRules signature kind
  · simp only [countingRules, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inRules
    rcases inRules with generated | rfl | rfl | rfl
    · exact absurd generated notGenerated
    · simp [countEmptyRule, matchPattern, countJudgment, equalJudgment, unequalJudgment]
    · simp [countHitRule, matchPattern, countJudgment, equalJudgment, unequalJudgment]
    · simp [countMissRule, matchPattern, countJudgment, equalJudgment, unequalJudgment]
  · exact ⟨privacy rule member inRules _ (by simp) arguments, privacy rule member inRules _ (by simp) arguments⟩

/-! ## Matching the counting patterns -/

/-- A match of a judgment pattern with three arguments. -/
theorem matchRel_three {label : String} {first second third term : Pattern} {bindings : Bindings}
    (related : MatchRel (.apply label [first, second, third]) term bindings) :
    ∃ a b c firstBindings secondBindings thirdBindings lastBindings, term = .apply label [a, b, c] ∧
      MatchRel first a firstBindings ∧ MatchRel second b secondBindings ∧ MatchRel third c thirdBindings ∧
      mergeBindings secondBindings thirdBindings = some lastBindings ∧
      mergeBindings firstBindings lastBindings = some bindings := by
  cases related with
  | apply arguments _ =>
    cases arguments with
    | cons firstRelated rest firstMerged =>
      cases rest with
      | cons secondRelated rest secondMerged =>
        cases rest with
        | cons thirdRelated rest thirdMerged =>
          cases rest
          rw [mergeBindings_nil_right, Option.some.injEq] at thirdMerged
          subst thirdMerged
          exact ⟨_, _, _, _, _, _, _, rfl, firstRelated, secondRelated, thirdRelated, secondMerged, firstMerged⟩

theorem matchRel_fvar_eq {name : String} {term : Pattern} {bindings : Bindings}
    (related : MatchRel (.fvar name) term bindings) : bindings = [(name, term)] := by
  cases related
  rfl

theorem matchRel_succ {name : String} {term : Pattern} {bindings : Bindings}
    (related : MatchRel (succNumeral (.fvar name)) term bindings) :
    ∃ smaller, term = succNumeral smaller ∧ bindings = [(name, smaller)] := by
  simp only [succNumeral] at related
  cases related with
  | apply arguments _ =>
    cases arguments with
    | cons nameRelated rest merged =>
      cases nameRelated
      cases rest
      rw [mergeBindings_nil_right, Option.some.injEq] at merged
      exact ⟨_, rfl, merged.symm⟩

theorem matchRel_zero {term : Pattern} {bindings : Bindings} (related : MatchRel zeroNumeral term bindings) :
    term = zeroNumeral ∧ bindings = [] := by
  simp only [zeroNumeral] at related
  cases related with
  | apply arguments _ =>
    cases arguments
    exact ⟨rfl, rfl⟩

theorem matchRel_empty {kind : CollType} {elements : List Pattern} {bindings : Bindings}
    (related : MatchRel (.collection kind [] none) (.collection kind elements none) bindings) :
    elements = [] ∧ bindings = [] := by
  cases related with
  | collection _ bag =>
    cases bag
    exact ⟨rfl, rfl⟩
  | vector arguments =>
    cases arguments
    exact ⟨rfl, rfl⟩

/-- **Taking one element out of a collection**: the pattern binds an element at some position and the rest. -/
theorem matchRel_takeOne {kind : CollType} (notVector : kind ≠ .vec) {name rest : String} (different : name ≠ rest)
    {elements : List Pattern} {bindings : Bindings}
    (related : MatchRel (.collection kind [.fvar name] (some rest)) (.collection kind elements none) bindings) :
    ∃ index, ∃ inside : index < elements.length,
      bindings = [(rest, .collection kind (elements.eraseIdx index) none), (name, elements[index])] := by
  cases related with
  | collection _ bag =>
    cases bag with
    | cons index inside elementRelated restRelated merged =>
      cases elementRelated
      cases restRelated
      rw [mergeBindings_fresh _ _ (by simp) (by simp [Ne.symm different])] at merged
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq] at merged
      exact ⟨index, inside, merged.symm⟩
  | vectorRest _ _ => exact absurd rfl notVector

variable {kind : CollType}

theorem countEmpty_matched {element counted : Pattern} {elements : List Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (countEmptyRule kind).left
      (.apply countJudgment [element, .collection kind elements none, counted])) :
    elements = [] ∧ counted = zeroNumeral := by
  obtain ⟨a, b, c, _, _, _, _, same, _, secondRelated, thirdRelated, _, _⟩ :=
    matchRel_three (matchPattern_sound matched)
  simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact ⟨(matchRel_empty secondRelated).1, (matchRel_zero thirdRelated).1⟩

theorem countHit_matched (notVector : kind ≠ .vec) {element counted : Pattern} {elements : List Pattern}
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern (countHitRule kind).left
      (.apply countJudgment [element, .collection kind elements none, counted])) :
    ∃ index, ∃ inside : index < elements.length, elements[index] = element ∧ ∃ smaller,
      counted = succNumeral smaller ∧
        bindings = [("rest", .collection kind (elements.eraseIdx index) none), ("n", smaller), ("p", element)] := by
  obtain ⟨a, b, c, _, _, _, _, same, firstRelated, secondRelated, thirdRelated, inner, outer⟩ :=
    matchRel_three (matchPattern_sound matched)
  simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  rw [matchRel_fvar_eq firstRelated] at outer
  obtain ⟨index, inside, rfl⟩ := matchRel_takeOne notVector (by decide) secondRelated
  obtain ⟨smaller, rfl, rfl⟩ := matchRel_succ thirdRelated
  rw [mergeBindings_fresh _ _ (by simp) (by simp)] at inner
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq] at inner
  subst inner
  rw [mergeBindings_cons_of_missing _ (by simp), mergeBindings_cons_of_missing _ (by simp),
    mergeBindings_cons_of_found (name := "p") (existing := element) _ (by simp)] at outer
  split at outer
  · rename_i agrees
    rw [mergeBindings_nil_right, Option.some.injEq] at outer
    exact ⟨index, inside, (beq_iff_eq.mp agrees).symm, smaller, rfl, outer.symm⟩
  · cases outer

theorem countMiss_matched (notVector : kind ≠ .vec) {element counted : Pattern} {elements : List Pattern}
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern (countMissRule kind).left
      (.apply countJudgment [element, .collection kind elements none, counted])) :
    ∃ index, ∃ inside : index < elements.length,
      bindings = [("x", elements[index]), ("rest", .collection kind (elements.eraseIdx index) none), ("n", counted),
        ("p", element)] := by
  obtain ⟨a, b, c, _, _, _, _, same, firstRelated, secondRelated, thirdRelated, inner, outer⟩ :=
    matchRel_three (matchPattern_sound matched)
  simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  rw [matchRel_fvar_eq firstRelated] at outer
  rw [matchRel_fvar_eq thirdRelated] at inner
  obtain ⟨index, inside, rfl⟩ := matchRel_takeOne notVector (by decide) secondRelated
  rw [mergeBindings_fresh _ _ (by simp) (by simp)] at inner
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq] at inner
  subst inner
  rw [mergeBindings_fresh _ _ (by simp) (by simp)] at outer
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq] at outer
  exact ⟨index, inside, outer.symm⟩

theorem countEmpty_matches (notVector : kind ≠ .vec) (element : Pattern) :
    [("p", element)] ∈ matchPattern (countEmptyRule kind).left
      (.apply countJudgment [element, .collection kind [] none, zeroNumeral]) :=
  matchRel_complete (.apply (.cons .fvar (.cons (.collection notVector .nilNoRest)
    (.cons (.apply .nil rfl) .nil rfl) rfl) rfl) rfl)

theorem countHit_matches (notVector : kind ≠ .vec) (element smaller : Pattern) (values : List Pattern) :
    [("rest", .collection kind values none), ("n", smaller), ("p", element)] ∈
      matchPattern (countHitRule kind).left
        (.apply countJudgment [element, .collection kind (element :: values) none, succNumeral smaller]) := by
  have bagMerged : mergeBindings [("p", element)] [("rest", .collection kind values none)] =
      some [("rest", .collection kind values none), ("p", element)] := by
    rw [mergeBindings_fresh _ _ (by simp) (by simp)]
    rfl
  have tailMerged : mergeBindings [("rest", .collection kind values none), ("p", element)] [("n", smaller)] =
      some [("n", smaller), ("rest", .collection kind values none), ("p", element)] := by
    rw [mergeBindings_fresh _ _ (by simp) (by simp)]
    rfl
  have headMerged : mergeBindings [("p", element)]
      [("n", smaller), ("rest", .collection kind values none), ("p", element)] =
      some [("rest", .collection kind values none), ("n", smaller), ("p", element)] := by
    rw [mergeBindings_cons_of_missing _ (by simp), mergeBindings_cons_of_missing _ (by simp),
      mergeBindings_cons_of_found (name := "p") (existing := element) _ (by simp)]
    simp only [beq_self_eq_true, ↓reduceIte, mergeBindings_nil_right]
  exact matchRel_complete (.apply (.cons .fvar (.cons (.collection notVector (.cons 0 (by simp) .fvar .nilRest bagMerged))
    (.cons (.apply (.cons .fvar .nil rfl) rfl) .nil rfl) tailMerged) headMerged) rfl)

theorem countMiss_matches (notVector : kind ≠ .vec) (element value counted : Pattern) (values : List Pattern) :
    [("x", value), ("rest", .collection kind values none), ("n", counted), ("p", element)] ∈
      matchPattern (countMissRule kind).left
        (.apply countJudgment [element, .collection kind (value :: values) none, counted]) := by
  have bagMerged : mergeBindings [("x", value)] [("rest", .collection kind values none)] =
      some [("rest", .collection kind values none), ("x", value)] := by
    rw [mergeBindings_fresh _ _ (by simp) (by simp)]
    rfl
  have tailMerged : mergeBindings [("rest", .collection kind values none), ("x", value)] [("n", counted)] =
      some [("n", counted), ("rest", .collection kind values none), ("x", value)] := by
    rw [mergeBindings_fresh _ _ (by simp) (by simp)]
    rfl
  have headMerged : mergeBindings [("p", element)]
      [("n", counted), ("rest", .collection kind values none), ("x", value)] =
      some [("x", value), ("rest", .collection kind values none), ("n", counted), ("p", element)] := by
    rw [mergeBindings_fresh _ _ (by simp) (by simp)]
    rfl
  exact matchRel_complete (.apply (.cons .fvar (.cons (.collection notVector (.cons 0 (by simp) .fvar .nilRest bagMerged))
    (.cons .fvar .nil rfl) tailMerged) headMerged) rfl)

/-! ## Premises asking judgments -/

section Premises

variable {relEnv : RelationEnv} {language : LanguageDef}

/-- **A premise asking a judgment of instantiated arguments** holds exactly where the language derives it, and binds
nothing. -/
theorem derives_of_judgmentPremise {sites source : Pattern} {bindings result : Bindings} {witness : Witness}
    {judgment : String} {arguments : List Pattern}
    (instantiated : applyBindingsScoped sites bindings (stepDepth sites (.congruence source yes)) source =
      .apply judgment arguments)
    (valid : PremiseValid relEnv language sites bindings (.congruence source yes) witness result) :
    result = bindings ∧ Derives relEnv language judgment arguments := by
  cases valid with
  | base isBaseTrue _ => simp [isBase] at isBaseTrue
  | step endpoints stepped matchedYes merged =>
    simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
    obtain ⟨rfl, rfl⟩ := endpoints
    have isYes := eq_yes_of_mem_matchPattern matchedYes
    subst isYes
    rw [matchPattern_firstOrder yes_firstOrder] at matchedYes
    simp only [↓reduceIte, List.mem_singleton] at matchedYes
    subst matchedYes
    rw [mergeBindings_nil_right, Option.some.injEq] at merged
    rw [instantiated] at stepped
    exact ⟨merged.symm, _, stepped⟩

theorem judgmentPremise_of_derives {sites source : Pattern} {bindings : Bindings} {judgment : String}
    {arguments : List Pattern}
    (instantiated : applyBindingsScoped sites bindings (stepDepth sites (.congruence source yes)) source =
      .apply judgment arguments)
    (derived : Derives relEnv language judgment arguments) :
    ∃ witness, PremiseValid relEnv language sites bindings (.congruence source yes) witness bindings := by
  obtain ⟨step, stepped⟩ := derived
  rw [← instantiated] at stepped
  refine ⟨_, .step rfl stepped ?_ (mergeBindings_nil_right _)⟩
  rw [matchPattern_firstOrder yes_firstOrder]
  simp

end Premises

/-- The count premise at bindings that read the element, the rest and the numeral. -/
theorem instantiate_countRest {sites : Pattern} {depth : ℕ} {bindings : Bindings} {element smaller : Pattern}
    {remaining : List Pattern} (elementFirst : FirstOrder element) (smallerFirst : FirstOrder smaller)
    (remainingFirst : ∀ x ∈ remaining, FirstOrder x) (atElement : applyBindings bindings (.fvar "p") = element)
    (atSmaller : applyBindings bindings (.fvar "n") = smaller)
    (atRest : bindings.find? (·.1 == "rest") = some ("rest", .collection kind remaining none)) :
    applyBindingsScoped sites bindings depth
        (.apply countJudgment [.fvar "p", .collection kind [] (some "rest"), .fvar "n"]) =
      .apply countJudgment [element, .collection kind remaining none, smaller] := by
  rw [applyBindingsScoped_apply]
  simp only [List.map_cons, List.map_nil]
  rw [applyBindingsScoped_fvar elementFirst atElement, applyBindingsScoped_collection,
    restSplice_of_found atRest remainingFirst, applyBindingsScoped_fvar smallerFirst atSmaller]
  simp

/-- The disequality premise at bindings that read the element taken and the element counted. -/
theorem instantiate_different {sites : Pattern} {depth : ℕ} {bindings : Bindings} {taken element : Pattern}
    (takenFirst : FirstOrder taken) (elementFirst : FirstOrder element)
    (atTaken : applyBindings bindings (.fvar "x") = taken) (atElement : applyBindings bindings (.fvar "p") = element) :
    applyBindingsScoped sites bindings depth (.apply unequalJudgment [.fvar "x", .fvar "p"]) =
      .apply unequalJudgment [taken, element] := by
  rw [applyBindingsScoped_apply]
  simp only [List.map_cons, List.map_nil]
  rw [applyBindingsScoped_fvar takenFirst atTaken, applyBindingsScoped_fvar elementFirst atElement]

/-! ## Counts, derived -/

section Judgments

variable {relEnv : RelationEnv} {language : LanguageDef} {signature : List (String × Nat)}

/-- The only rules applying to a count judgment are the three counting rules. -/
theorem eq_countRule {rule : RewriteRule} (privacy : CountingPrivate language signature kind)
    (member : rule ∈ language.rewrites) {arguments : List Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern rule.left (.apply countJudgment arguments)) :
    rule = countEmptyRule kind ∨ rule = countHitRule kind ∨ rule = countMissRule kind := by
  by_cases generated : rule ∈ countingRules signature kind
  · simp only [countingRules, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at generated
    rcases generated with equality | same | same | same
    · rw [matchPattern_disequality_other equality (by decide) (by decide)] at matched
      simp at matched
    · exact .inl same
    · exact .inr (.inl same)
    · exact .inr (.inr same)
  · rw [privacy rule member generated countJudgment (by simp) arguments] at matched
    simp at matched

/-- **A derived count is the number of occurrences.** -/
theorem count_eq_of_derives (privacy : CountingPrivate language signature kind) (notVector : kind ≠ .vec)
    {element : Pattern} (elementOver : TermOf signature element) (size : ℕ) :
    ∀ elements : List Pattern, elements.length = size → (∀ value ∈ elements, TermOf signature value) →
      ∀ count : ℕ, Derives relEnv language countJudgment [element, .collection kind elements none, numeral count] →
        elements.count element = count := by
  induction size using Nat.strong_induction_on with
  | _ size inner =>
  intro elements sized elementsOver count derived
  obtain ⟨witness, step⟩ := derived
  obtain ⟨rule, member, initial, final, witnesses, matched, premises⟩ := stepValid_yes_cases step
  have elementsFirst : ∀ value ∈ elements, FirstOrder value := fun value member => (elementsOver value member).firstOrder
  rcases eq_countRule privacy member matched with rfl | rfl | rfl
  · obtain ⟨rfl, zero⟩ := countEmpty_matched matched
    rw [numeral_eq_zero_iff.mp zero]
    rfl
  · obtain ⟨index, inside, found, smaller, numeralSame, rfl⟩ := countHit_matched notVector matched
    obtain ⟨previous, rfl, rfl⟩ := numeral_eq_succ_iff.mp numeralSame
    cases premises with
    | cons premise rest =>
      cases rest
      obtain ⟨_, restDerived⟩ := derives_of_judgmentPremise
        (instantiate_countRest (remaining := elements.eraseIdx index) elementOver.firstOrder (numeral_firstOrder previous)
          (fun value member => elementsFirst value (List.mem_of_mem_eraseIdx member))
          (by simp [applyBindings, List.find?]) (by simp [applyBindings, List.find?]) (by simp [List.find?])) premise
      have smallerCount := inner (size - 1) (by omega) (elements.eraseIdx index)
        (by rw [List.length_eraseIdx_of_lt inside]; omega)
        (fun value member => elementsOver value (List.mem_of_mem_eraseIdx member)) previous restDerived
      rw [← (List.getElem_cons_eraseIdx_perm inside).count_eq, found, List.count_cons_self, smallerCount]
  · obtain ⟨index, inside, rfl⟩ := countMiss_matched notVector matched
    cases premises with
    | cons different rest =>
      cases rest with
      | cons counted last =>
        cases last
        obtain ⟨same, unequal⟩ := derives_of_judgmentPremise
          (instantiate_different (elementsFirst _ (List.getElem_mem inside)) elementOver.firstOrder
            (by simp [applyBindings, List.find?]) (by simp [applyBindings, List.find?])) different
        subst same
        obtain ⟨_, restDerived⟩ := derives_of_judgmentPremise
          (instantiate_countRest (remaining := elements.eraseIdx index) elementOver.firstOrder (numeral_firstOrder count)
            (fun value member => elementsFirst value (List.mem_of_mem_eraseIdx member))
            (by simp [applyBindings, List.find?]) (by simp [applyBindings, List.find?]) (by simp [List.find?])) counted
        have differs := ne_of_derives_unequal privacy.toPrivate (elementsFirst _ (List.getElem_mem inside))
          elementOver.firstOrder unequal
        have smallerCount := inner (size - 1) (by omega) (elements.eraseIdx index)
          (by rw [List.length_eraseIdx_of_lt inside]; omega)
          (fun value member => elementsOver value (List.mem_of_mem_eraseIdx member)) count restDerived
        rw [← (List.getElem_cons_eraseIdx_perm inside).count_eq, List.count_cons_of_ne differs, smallerCount]

/-- **The language derives the number of occurrences.** -/
theorem derives_count (rules : ∀ rule ∈ countingRules signature kind, rule ∈ language.rewrites)
    (names : (signature.map Prod.fst).Nodup) (notVector : kind ≠ .vec) {element : Pattern}
    (elementOver : TermOf signature element) :
    ∀ elements : List Pattern, (∀ value ∈ elements, TermOf signature value) →
      Derives relEnv language countJudgment [element, .collection kind elements none, numeral (elements.count element)]
  | [], _ => stepValid_of_rule (rules _ (by simp [countingRules])) (countEmpty_matches notVector element) (.nil _) rfl
  | value :: values, valuesOver => by
    have tailOver : ∀ other ∈ values, TermOf signature other :=
      fun other member => valuesOver other (List.mem_cons_of_mem _ member)
    have valuesFirst : ∀ other ∈ values, FirstOrder other := fun other member => (tailOver other member).firstOrder
    have restDerived := derives_count rules names notVector elementOver values tailOver
    by_cases same : value = element
    · subst same
      rw [List.count_cons_self]
      obtain ⟨witness, restPremise⟩ := judgmentPremise_of_derives (sites := captureSites (countHitRule kind))
        (bindings := [("rest", .collection kind values none), ("n", numeral (values.count value)), ("p", value)])
        (source := .apply countJudgment [.fvar "p", .collection kind [] (some "rest"), .fvar "n"])
        (instantiate_countRest elementOver.firstOrder (numeral_firstOrder _) valuesFirst
          (by simp [applyBindings, List.find?]) (by simp [applyBindings, List.find?]) (by simp [List.find?]))
        restDerived
      exact stepValid_of_rule (rules _ (by simp [countingRules]))
        (countHit_matches notVector value (numeral (values.count value)) values) (.cons restPremise (.nil _)) rfl
    · rw [List.count_cons_of_ne same]
      have unequal := derives_unequal_of_ne (relEnv := relEnv)
        (fun rule generated => rules rule (List.mem_append_left _ generated)) names (valuesOver value List.mem_cons_self)
        elementOver same
      obtain ⟨differentWitness, differentPremise⟩ := judgmentPremise_of_derives (sites := captureSites (countMissRule kind))
        (bindings := [("x", value), ("rest", .collection kind values none), ("n", numeral (values.count element)),
          ("p", element)])
        (source := .apply unequalJudgment [.fvar "x", .fvar "p"])
        (instantiate_different (valuesOver value List.mem_cons_self).firstOrder elementOver.firstOrder
          (by simp [applyBindings, List.find?]) (by simp [applyBindings, List.find?]))
        unequal
      obtain ⟨restWitness, restPremise⟩ := judgmentPremise_of_derives (sites := captureSites (countMissRule kind))
        (bindings := [("x", value), ("rest", .collection kind values none), ("n", numeral (values.count element)),
          ("p", element)])
        (source := .apply countJudgment [.fvar "p", .collection kind [] (some "rest"), .fvar "n"])
        (instantiate_countRest elementOver.firstOrder (numeral_firstOrder _) valuesFirst
          (by simp [applyBindings, List.find?]) (by simp [applyBindings, List.find?]) (by simp [List.find?]))
        restDerived
      exact stepValid_of_rule (rules _ (by simp [countingRules]))
        (countMiss_matches notVector element value (numeral (values.count element)) values)
        (.cons differentPremise (.cons restPremise (.nil _))) rfl

/-- **The language derives a count exactly when it is the number of occurrences.** -/
theorem derives_count_iff (rules : ∀ rule ∈ countingRules signature kind, rule ∈ language.rewrites)
    (privacy : CountingPrivate language signature kind) (names : (signature.map Prod.fst).Nodup)
    (notVector : kind ≠ .vec) {element : Pattern} {elements : List Pattern} (elementOver : TermOf signature element)
    (elementsOver : ∀ value ∈ elements, TermOf signature value) (count : ℕ) :
    Derives relEnv language countJudgment [element, .collection kind elements none, numeral count] ↔
      elements.count element = count := by
  constructor
  · exact count_eq_of_derives privacy notVector elementOver _ elements rfl elementsOver count
  · rintro rfl
    exact derives_count rules names notVector elementOver elements elementsOver

/-- **The count zero is non-membership.** -/
theorem derives_count_zero_iff (rules : ∀ rule ∈ countingRules signature kind, rule ∈ language.rewrites)
    (privacy : CountingPrivate language signature kind) (names : (signature.map Prod.fst).Nodup)
    (notVector : kind ≠ .vec) {element : Pattern} {elements : List Pattern} (elementOver : TermOf signature element)
    (elementsOver : ∀ value ∈ elements, TermOf signature value) :
    Derives relEnv language countJudgment [element, .collection kind elements none, numeral 0] ↔ element ∉ elements := by
  rw [derives_count_iff rules privacy names notVector elementOver elementsOver, List.count_eq_zero]

/-- **A count is complemented by the other counts** on a term of the signature and a closed bag or set of such terms:
the language derives exactly one count. -/
theorem count_complemented (rules : ∀ rule ∈ countingRules signature kind, rule ∈ language.rewrites)
    (privacy : CountingPrivate language signature kind) (names : (signature.map Prod.fst).Nodup)
    (notVector : kind ≠ .vec) :
    Complemented
      (fun asked : Pattern × List Pattern × ℕ =>
        Derives relEnv language countJudgment [asked.1, .collection kind asked.2.1 none, numeral asked.2.2])
      (fun asked => ∃ other ≠ asked.2.2,
        Derives relEnv language countJudgment [asked.1, .collection kind asked.2.1 none, numeral other])
      (fun asked => TermOf signature asked.1 ∧ ∀ value ∈ asked.2.1, TermOf signature value) where
  disjoint asked inside held failed := by
    obtain ⟨other, different, derivedOther⟩ := failed
    have first := (derives_count_iff rules privacy names notVector inside.1 inside.2 _).mp held
    have second := (derives_count_iff rules privacy names notVector inside.1 inside.2 _).mp derivedOther
    exact different (second.symm.trans first)
  exhaustive asked inside := by
    by_cases same : asked.2.1.count asked.1 = asked.2.2
    · exact .inl ((derives_count_iff rules privacy names notVector inside.1 inside.2 _).mpr same)
    · exact .inr ⟨_, same, (derives_count_iff rules privacy names notVector inside.1 inside.2 _).mpr rfl⟩

end Judgments

/-! ## Controls -/

namespace CountingControls

/-- Two constants. -/
def signature : List (String × Nat) := [("A", 0), ("B", 0)]

def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []

/-- The counting rules over the two constants, for bags. -/
def language : LanguageDef := ⟨"Counting", [], [], [], countingRules signature .hashBag⟩

theorem rules : ∀ rule ∈ countingRules signature .hashBag, rule ∈ language.rewrites := fun _ member => member

theorem private_ : CountingPrivate language signature .hashBag := fun _ member notGenerated =>
  absurd member notGenerated

theorem names : (signature.map Prod.fst).Nodup := by decide

theorem a_over : TermOf signature a := .apply (by simp [signature]) (by simp)
theorem b_over : TermOf signature b := .apply (by simp [signature]) (by simp)

theorem bag_over : ∀ value ∈ [a, b, a], TermOf signature value := by
  simp [a_over, b_over]

/-- Positive: `A` occurs twice in `{A, B, A}`. -/
theorem a_twice : Derives RelationEnv.empty language countJudgment [a, .collection .hashBag [a, b, a] none, numeral 2] :=
  (derives_count_iff rules private_ names (by decide) a_over bag_over 2).mpr (by simp [a, b])

/-- Negative: `A` does not occur once in `{A, B, A}`. -/
theorem not_a_once :
    ¬ Derives RelationEnv.empty language countJudgment [a, .collection .hashBag [a, b, a] none, numeral 1] := by
  rw [derives_count_iff rules private_ names (by decide) a_over bag_over 1]
  simp [a, b]

/-- Positive: `B` occurs once. -/
theorem b_once : Derives RelationEnv.empty language countJudgment [b, .collection .hashBag [a, b, a] none, numeral 1] :=
  (derives_count_iff rules private_ names (by decide) b_over bag_over 1).mpr (by simp [a, b])

/-- The count zero is non-membership: `B` is not in `{A, A}`. -/
theorem b_absent : Derives RelationEnv.empty language countJudgment [b, .collection .hashBag [a, a] none, numeral 0] :=
  (derives_count_zero_iff rules private_ names (by decide) b_over (by simp [a_over])).mpr (by simp [a, b])

end CountingControls

end Mettapedia.GSLT.LanguageDef.DecidableRelations
