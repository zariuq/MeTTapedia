import Mettapedia.OSLF.Framework.FiniteModelContextual
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference

/-!
# Certificates that respect a language's equations

A certificate's model gives each term a value. Its verdicts transfer to the language when equivalent
object terms get one value (`RespectsEquations`). That follows from finite checks on the model
(`Certificate.equationsValid`):
- **bag and set laws**: the joins of unordered collections are left-commutative (already part of a
  valid certificate), and set joins are idempotent (`setIdempotent`);
- **declared collection algebras**: for a flattening algebra the join is associative with the empty
  collection as left identity and each element its own singleton; a declared unit constructor denotes
  the empty collection and is a left identity of the join (`algebraLaws`);
- **authored equations** without binders: both sides have one value under every table
  (`equationCheck`). Premises are not consulted. A premise only adds bindings
  (`premisesValid_extends`), so a model whose sides agree under every table respects each conditional
  instance; a model whose sides agree only where the premises hold is refused. Equations with binders
  are refused.

Evaluation is a congruence for every one-hole context (`eval_fill_congr`). Each generator of the
equations keeps the value at every environment (`derived_eval_eq`, `authored_eval_eq`). So a model that
passes the checks respects the equations (`respectsEquations_of_equationsValid`). This covers the
ρ-calculus: a bag with a flattening algebra and unit, and the authored `@(*N) = N`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.FiniteModels
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (matchPattern_sound BindingsExtends mergeBindings_subsumed_left)
open Mettapedia.OSLF.MeTTaIL.Engine (premiseStepWithEnv premiseStepWithEnv_freshness_mem
  premiseStepWithEnv_relationQuery_mem)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance)

variable {A : Type}

/-! ## Evaluation is a congruence -/

theorem eval_fill_congr (model : FiniteModel A) (valuation : Valuation A) {first second : Pattern}
    (same : ∀ outer : List A, eval model valuation outer first = eval model valuation outer second) :
    ∀ (context : OneHoleContext) (outer : List A),
      eval model valuation outer (context.fill first) = eval model valuation outer (context.fill second) := by
  intro context
  induction context with
  | hole => exact same
  | apply constructor before inner after previous =>
    intro outer
    simp only [OneHoleContext.fill, eval, evalList_eq_map, List.map_append, List.map_cons, previous outer]
  | lambda name inner previous =>
    intro outer
    simp only [OneHoleContext.fill, eval]
    congr 1
    funext value
    exact previous (value :: outer)
  | multiLambda arity names inner previous =>
    intro outer
    simp only [OneHoleContext.fill, eval]
    congr 1
    funext values
    exact previous (List.ofFn values ++ outer)
  | substBody inner replacement previous =>
    intro outer
    simp only [OneHoleContext.fill, eval]
    exact previous _
  | substReplacement body inner previous =>
    intro outer
    simp only [OneHoleContext.fill, eval, previous outer]
  | collection kind before inner after rest previous =>
    intro outer
    simp only [OneHoleContext.fill, eval, evalList_eq_map, List.map_append, List.map_cons, previous outer]

theorem object_of_list_middle {before after : List Pattern} {part : Pattern}
    (object : isObjectPatternList (before ++ part :: after) = true) : isObjectPattern part = true := by
  induction before with
  | nil =>
    simp only [List.nil_append, isObjectPatternList, Bool.and_eq_true] at object
    exact object.1
  | cons head tail previous =>
    simp only [List.cons_append, isObjectPatternList, Bool.and_eq_true] at object
    exact previous object.2

/-- A subterm of an object term at a hole is an object term. -/
theorem object_of_fill : ∀ (context : OneHoleContext) {part : Pattern},
    isObjectPattern (context.fill part) = true → isObjectPattern part = true
  | .hole, _, object => object
  | .apply constructor before inner after, part, object => by
    simp only [OneHoleContext.fill, isObjectPattern] at object
    exact object_of_fill inner (object_of_list_middle object)
  | .lambda _ inner, part, object => by
    simp only [OneHoleContext.fill, isObjectPattern] at object
    exact object_of_fill inner object
  | .multiLambda _ _ inner, part, object => by
    simp only [OneHoleContext.fill, isObjectPattern] at object
    exact object_of_fill inner object
  | .substBody _ _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .substReplacement _ _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .collection kind before inner after rest, part, object => by
    simp only [OneHoleContext.fill, isObjectPattern, Bool.and_eq_true] at object
    exact object_of_fill inner (object_of_list_middle object.2)

/-! ## Laws of folds -/

theorem foldr_perm {join : A → A → A} (commutes : ∀ first second rest, join first (join second rest) =
    join second (join first rest)) {left right : List A} (perm : left.Perm right) (start : A) :
    left.foldr join start = right.foldr join start := by
  induction perm with
  | nil => rfl
  | cons head _ previous => simp only [List.foldr_cons, previous]
  | swap first second rest => simp only [List.foldr_cons, commutes]
  | trans _ _ first second => exact first.trans second

theorem join_foldr {join : A → A → A} {unit : A} (associative : ∀ first second rest,
    join (join first second) rest = join first (join second rest)) (identity : ∀ rest, join unit rest = rest) :
    ∀ (values : List A) (rest : A), join (values.foldr join unit) rest = values.foldr join rest
  | [], rest => identity rest
  | value :: values, rest => by
    simp only [List.foldr_cons, associative, join_foldr associative identity values rest]

/-! ## The checks -/

mutual
/-- A pattern without abstractions or explicit substitutions. -/
def binderFree : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply _ arguments => binderFreeList arguments
  | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ => false
  | .collection _ elements _ => binderFreeList elements

def binderFreeList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => binderFree pattern && binderFreeList patterns
end

mutual
theorem occurrences_binderFree : ∀ (pattern : Pattern) (depth : ℕ), binderFree pattern = true →
    ∀ entry ∈ occurrences depth pattern, entry.2 = depth
  | .bvar _, _, _, _, inside => by simp [occurrences] at inside
  | .fvar _, _, _, _, inside => by
    simp only [occurrences, List.mem_singleton] at inside
    rw [inside]
  | .apply _ arguments, depth, free, entry, inside => by
    simp only [binderFree] at free
    simp only [occurrences] at inside
    exact occurrencesList_binderFree arguments depth free entry inside
  | .lambda _ _, _, free, _, _ | .multiLambda _ _ _, _, free, _, _ | .subst _ _, _, free, _, _ => by
    simp [binderFree] at free
  | .collection _ elements rest, depth, free, entry, inside => by
    simp only [binderFree] at free
    simp only [occurrences, List.mem_append] at inside
    rcases inside with inElements | inRest
    · exact occurrencesList_binderFree elements depth free entry inElements
    · cases rest <;> simp_all

theorem occurrencesList_binderFree : ∀ (patterns : List Pattern) (depth : ℕ), binderFreeList patterns = true →
    ∀ entry ∈ occurrencesList depth patterns, entry.2 = depth
  | [], _, _, _, inside => by simp [occurrencesList] at inside
  | pattern :: patterns, depth, free, entry, inside => by
    simp only [binderFreeList, Bool.and_eq_true] at free
    simp only [occurrencesList, List.mem_append] at inside
    rcases inside with here | later
    · exact occurrences_binderFree pattern depth free.1 entry here
    · exact occurrencesList_binderFree patterns depth free.2 entry later
end

/-! ## Premises only add bindings -/

/-- **A premise only adds bindings.** -/
theorem premiseValid_extends {relEnv : RelationEnv} {language : LanguageDef} {sites : Pattern} {initial : Bindings}
    {premise : Premise} {witness : Witness} {result : Bindings}
    (valid : PremiseValid relEnv language sites initial premise witness result) : BindingsExtends initial result := by
  cases valid with
  | base _ member =>
    cases premise with
    | freshness condition =>
      rw [premiseStepWithEnv_freshness_mem member]
      exact fun _ _ found => found
    | relationQuery name arguments =>
      obtain ⟨extra, merged⟩ := premiseStepWithEnv_relationQuery_mem member
      exact fun _ _ found => mergeBindings_subsumed_left merged found
    | congruence _ _ => simp [premiseStepWithEnv] at member
    | scopedStep _ => simp [premiseStepWithEnv] at member
    | forAll _ _ _ => simp [premiseStepWithEnv] at member
  | step _ _ _ merged => exact fun _ _ found => mergeBindings_subsumed_left merged found
  | forAll _ _ => exact fun _ _ found => found

/-- **Premises only add bindings.** -/
theorem premisesValid_extends {relEnv : RelationEnv} {language : LanguageDef} {sites : Pattern} :
    ∀ {initial : Bindings} {premises : List Premise} {witnesses : List Witness} {final : Bindings},
      PremisesValid relEnv language sites initial premises witnesses final → BindingsExtends initial final
  | _, [], _, _, valid => by
    cases valid
    exact fun _ _ found => found
  | _, _ :: _, _, _, valid => by
    cases valid with
    | cons first rest =>
      exact fun name value found => premisesValid_extends rest name value (premiseValid_extends first name value found)

/-- The metavariables of an equation, each at depth zero. -/
def equationSpec (equation : Equation) : List (String × ℕ) :=
  ((occurrences 0 equation.left ++ occurrences 0 equation.right).map (·.1)).dedup.map (·, 0)

/-- **A first-order equation**: no binders, closed sides, its collection tails bound on both sides, and
aligned. -/
def equationShape (equation : Equation) : Bool :=
  binderFree equation.left && binderFree equation.right &&
    equation.left.isWellScopedAt 0 && equation.right.isWellScopedAt 0 &&
    (restVars equation.right).all (· ∈ restVars equation.left) &&
    (restVars equation.left).all (· ∈ restVars equation.right) && equationAligned equation

namespace Certificate

variable [DecidableEq A] (certificate : Certificate A)

/-- Set joins are idempotent. -/
def setIdempotent : Bool :=
  certificate.elements.all fun first => certificate.elements.all fun rest =>
    certificate.model.collectionJoin .hashSet first (certificate.model.collectionJoin .hashSet first rest) ==
      certificate.model.collectionJoin .hashSet first rest

/-- The laws a declared collection algebra imposes on the model, for its kind. -/
def algebraLaws (kind : CollType) (algebra : CollectionAlgebra) : Bool :=
  (!algebra.flatten ||
    (certificate.elements.all fun element =>
      certificate.model.collectionJoin kind element (certificate.model.collectionUnit kind) == element) &&
    (certificate.elements.all fun rest =>
      certificate.model.collectionJoin kind (certificate.model.collectionUnit kind) rest == rest) &&
    (certificate.elements.all fun first => certificate.elements.all fun second => certificate.elements.all fun rest =>
      certificate.model.collectionJoin kind (certificate.model.collectionJoin kind first second) rest ==
        certificate.model.collectionJoin kind first (certificate.model.collectionJoin kind second rest))) &&
  match algebra.unit with
  | none => true
  | some unit =>
    certificate.model.collectionUnit kind == certificate.model.operation unit [] &&
      certificate.elements.all fun rest =>
        certificate.model.collectionJoin kind (certificate.model.operation unit []) rest == rest

/-- **An authored equation holds in the model**: it is first-order, and its two sides have one value under
every table, whatever its premises. -/
def equationCheck (equation : Equation) : Bool :=
  equationShape equation &&
    (tables certificate.elements (equationSpec equation)).all fun table =>
      eval certificate.model (tableValuation certificate.model certificate.elements table) [] equation.left ==
        eval certificate.model (tableValuation certificate.model certificate.elements table) [] equation.right

/-- **The model respects the language's collection laws**: set joins are idempotent when the language has sets, and
every declared algebra's laws hold. -/
def collectionLawsValid (language : LanguageDef) : Bool :=
  (!language.usesCollection .hashSet || setIdempotent certificate) &&
  (language.terms.all fun rule =>
    match rule.algebra?, rule.params with
    | some algebra, [.simple _ (.collection kind _)] => algebraLaws certificate kind algebra
    | _, _ => true)

/-- **The model respects the language's equations**: its collection laws, and every authored equation holds. -/
def equationsValid (language : LanguageDef) : Bool :=
  collectionLawsValid certificate language && language.equations.all (equationCheck certificate)

end Certificate

/-- **The model respects the language's equations**, in a reading: equivalent object terms have one value. -/
def RespectsEquations [DecidableEq A] (certificate : Certificate A) (relEnv : RelationEnv) (language : LanguageDef)
    (reading : LanguageReading := .syntax) : Prop :=
  ∀ first second, ObjectEquivalent relEnv language reading first second →
    value certificate.model first = value certificate.model second

/-- **A model respecting the syntax theory respects every reading**, each being contained in it. -/
theorem RespectsEquations.reading [DecidableEq A] {certificate : Certificate A} {relEnv : RelationEnv}
    {language : LanguageDef} (respects : RespectsEquations certificate relEnv language) (reading : LanguageReading) :
    RespectsEquations certificate relEnv language reading :=
  fun first second equivalent => respects first second equivalent.toSyntax

/-! ## Each generator keeps the value -/

namespace Certificate

variable [DecidableEq A] {certificate : Certificate A} {language : LanguageDef}

theorem collectionLawsValid_parts (checked : collectionLawsValid certificate language = true) :
    (language.usesCollection .hashSet = true → setIdempotent certificate = true) ∧
    (∀ rule ∈ language.terms, ∀ algebra kind name element, rule.algebra? = some algebra →
      rule.params = [.simple name (.collection kind element)] → algebraLaws certificate kind algebra = true) := by
  simp only [collectionLawsValid, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at checked
  obtain ⟨sets, algebras⟩ := checked
  refine ⟨fun uses => sets.resolve_left (by rw [uses]; decide), fun rule member algebra kind name element declared
    params => ?_⟩
  have := algebras rule member
  rw [declared, params] at this
  exact this

theorem equationsValid_collectionLaws (checked : equationsValid certificate language = true) :
    collectionLawsValid certificate language = true := by
  simp only [equationsValid, Bool.and_eq_true] at checked
  exact checked.1

theorem equationsValid_parts (checked : equationsValid certificate language = true) :
    (language.usesCollection .hashSet = true → setIdempotent certificate = true) ∧
    (∀ rule ∈ language.terms, ∀ algebra kind name element, rule.algebra? = some algebra →
      rule.params = [.simple name (.collection kind element)] → algebraLaws certificate kind algebra = true) ∧
    (∀ equation ∈ language.equations, equationCheck certificate equation = true) := by
  obtain ⟨sets, algebras⟩ := collectionLawsValid_parts (equationsValid_collectionLaws checked)
  simp only [equationsValid, Bool.and_eq_true, List.all_eq_true] at checked
  exact ⟨sets, algebras, checked.2⟩

theorem setIdempotent_spec (checked : setIdempotent certificate = true) (first rest : A) :
    certificate.model.collectionJoin .hashSet first (certificate.model.collectionJoin .hashSet first rest) =
      certificate.model.collectionJoin .hashSet first rest := by
  simp only [setIdempotent, List.all_eq_true, beq_iff_eq] at checked
  exact checked first (certificate.complete first) rest (certificate.complete rest)

theorem algebraLaws_flatten {kind : CollType} {algebra : CollectionAlgebra}
    (checked : algebraLaws certificate kind algebra = true) (flattens : algebra.flatten = true) :
    (∀ element, certificate.model.collectionJoin kind element (certificate.model.collectionUnit kind) = element) ∧
    (∀ rest, certificate.model.collectionJoin kind (certificate.model.collectionUnit kind) rest = rest) ∧
    (∀ first second rest, certificate.model.collectionJoin kind (certificate.model.collectionJoin kind first second) rest =
      certificate.model.collectionJoin kind first (certificate.model.collectionJoin kind second rest)) := by
  simp only [algebraLaws, flattens, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
  obtain ⟨⟨⟨single, identity⟩, associative⟩, -⟩ := checked
  exact ⟨fun element => single element (certificate.complete element),
    fun rest => identity rest (certificate.complete rest),
    fun first second rest => associative first (certificate.complete first) second (certificate.complete second) rest
      (certificate.complete rest)⟩

theorem algebraLaws_unit {kind : CollType} {algebra : CollectionAlgebra} {unit : String}
    (checked : algebraLaws certificate kind algebra = true) (declared : algebra.unit = some unit) :
    certificate.model.collectionUnit kind = certificate.model.operation unit [] ∧
      ∀ rest, certificate.model.collectionJoin kind (certificate.model.operation unit []) rest = rest := by
  simp only [algebraLaws, declared, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
  obtain ⟨-, empty, identity⟩ := checked
  exact ⟨empty, fun rest => identity rest (certificate.complete rest)⟩

/-- **The derived collection laws keep the value** at every environment. -/
theorem derived_eval_eq (contextual : certificate.contextualValid language = true)
    (laws : collectionLawsValid certificate language = true) {source target : Pattern}
    (derived : DerivedInstance language source target) (outer : List A) :
    eval certificate.model (stateValuation certificate.model) outer source =
      eval certificate.model (stateValuation certificate.model) outer target := by
  have commutes := Mettapedia.OSLF.Framework.FiniteModels.Certificate.preorder_commutes
    (Mettapedia.OSLF.Framework.FiniteModels.Certificate.contextual_preorder contextual)
  obtain ⟨sets, algebras⟩ := collectionLawsValid_parts laws
  cases derived with
  | bagPerm declaration _ perm =>
    rw [eval_collection, eval_collection]
    exact foldr_perm (fun first second rest => commutes .hashBag (by decide) first second rest) (perm.map _) _
  | setPerm declaration _ perm =>
    rw [eval_collection, eval_collection]
    exact foldr_perm (fun first second rest => commutes .hashSet (by decide) first second rest) (perm.map _) _
  | setDedup declaration kindTyped =>
    rw [eval_collection, eval_collection]
    simp only [List.map_cons, List.foldr_cons]
    exact setIdempotent_spec (sets (Mettapedia.GSLT.LanguageDef.EquationSemantics.usesCollection_eq_true_of_collectionTypedAt
      declaration kindTyped)) _ _
  | flatten algebraRule flattens _ =>
    obtain ⟨name, params⟩ := algebraRule.selfSorted
    obtain ⟨-, identity, associative⟩ :=
      algebraLaws_flatten (algebras _ algebraRule.authored _ _ _ _ algebraRule.declared params) flattens
    rw [eval_collection, eval_collection]
    simp only [List.map_append, List.map_cons, List.foldr_append, List.foldr_cons, eval_collection,
      join_foldr associative identity]
  | singleton algebraRule flattens _ =>
    obtain ⟨name, params⟩ := algebraRule.selfSorted
    obtain ⟨single, -, -⟩ :=
      algebraLaws_flatten (algebras _ algebraRule.authored _ _ _ _ algebraRule.declared params) flattens
    rw [eval_collection]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, single]
  | unitElim algebraRule declared _ =>
    obtain ⟨name, params⟩ := algebraRule.selfSorted
    obtain ⟨-, identity⟩ := algebraLaws_unit (algebras _ algebraRule.authored _ _ _ _ algebraRule.declared params) declared
    rw [eval_collection, eval_collection]
    simp only [List.map_append, List.map_cons, List.foldr_append, List.foldr_cons, eval, evalList, identity]
  | emptyUnit algebraRule declared _ =>
    obtain ⟨name, params⟩ := algebraRule.selfSorted
    obtain ⟨empty, -⟩ := algebraLaws_unit (algebras _ algebraRule.authored _ _ _ _ algebraRule.declared params) declared
    rw [eval_collection]
    simp only [List.map_nil, List.foldr_nil, eval, evalList, empty]

/-- One side of a first-order equation matched at a term evaluates as the other side instantiated by
bindings that extend the match, at every environment, when the two sides agree under every table. -/
theorem side_eval_eq (commutes : LeftCommutes certificate.model) {first second : Pattern} {spec : List (String × ℕ)}
    (keys : (spec.map Prod.fst).Nodup)
    (covers : ∀ entry ∈ occurrences 0 first ++ occurrences 0 second, (entry.1, 0) ∈ spec)
    (firstFree : binderFree first = true) (secondFree : binderFree second = true)
    (firstScoped : first.isWellScopedAt 0 = true) (secondScoped : second.isWellScopedAt 0 = true)
    (restsCovered : ∀ entry ∈ restVars second, entry ∈ restVars first)
    (agree : ∀ table ∈ tables certificate.elements spec,
      eval certificate.model (tableValuation certificate.model certificate.elements table) [] first =
        eval certificate.model (tableValuation certificate.model certificate.elements table) [] second)
    {source : Pattern} {initial final : Bindings} (matched : initial ∈ matchPattern first source)
    (extension : BindingsExtends initial final) (object : isObjectPattern source = true) (outer : List A) :
    eval certificate.model (stateValuation certificate.model) outer source =
      eval certificate.model (stateValuation certificate.model) outer (applyBindings final second) := by
  have firstBound : RestsBound final first := restsBound_of_matchRel (matchPattern_sound matched) final extension
  have secondBound : RestsBound final second := fun entry inside => firstBound entry (restsCovered entry inside)
  let shifted := shiftValuation (bindingValuation certificate.model final) outer
  obtain ⟨table, member, realizes⟩ := exists_table certificate.model certificate.elements certificate.complete shifted
    spec keys
  have readsTable : ∀ (pattern : Pattern), binderFree pattern = true → (∀ entry ∈ occurrences 0 pattern, (entry.1, 0) ∈ spec) →
      eval certificate.model shifted [] pattern =
        eval certificate.model (tableValuation certificate.model certificate.elements table) [] pattern := by
    intro pattern free inSpec
    refine eval_congr certificate.model pattern [] fun entry inside inner length => ?_
    have atZero := occurrences_binderFree pattern 0 free entry inside
    rw [atZero] at length
    have empty : inner = [] := List.length_eq_zero_iff.mp length
    subst empty
    have := realizes (entry.1, 0) (inSpec entry inside) [] (by simp)
    simp only [List.take_zero] at this
    exact this.symm
  have shift : ∀ (pattern : Pattern), pattern.isWellScopedAt 0 = true →
      eval certificate.model (bindingValuation certificate.model final) outer pattern =
        eval certificate.model shifted [] pattern := by
    intro pattern inScope
    have := eval_shift certificate.model (bindingValuation certificate.model final) outer pattern [] inScope
    simpa using this
  rw [← eval_of_matchRel certificate.model commutes (matchPattern_sound matched) object final extension outer,
    eval_applyBindings certificate.model final first firstBound outer,
    eval_applyBindings certificate.model final second secondBound outer, shift first firstScoped,
    shift second secondScoped,
    readsTable first firstFree fun entry inside => covers entry (List.mem_append_left _ inside),
    readsTable second secondFree fun entry inside => covers entry (List.mem_append_right _ inside)]
  exact agree table member

theorem equationShape_parts {equation : Equation} (shape : equationShape equation = true) :
    binderFree equation.left = true ∧ binderFree equation.right = true ∧
      equation.left.isWellScopedAt 0 = true ∧ equation.right.isWellScopedAt 0 = true ∧
      (∀ entry ∈ restVars equation.right, entry ∈ restVars equation.left) ∧
      (∀ entry ∈ restVars equation.left, entry ∈ restVars equation.right) ∧ equationAligned equation = true := by
  simp only [equationShape, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at shape
  obtain ⟨⟨⟨⟨⟨⟨leftFree, rightFree⟩, leftScoped⟩, rightScoped⟩, rightRests⟩, leftRests⟩, aligned⟩ := shape
  exact ⟨leftFree, rightFree, leftScoped, rightScoped, rightRests, leftRests, aligned⟩

theorem equationSpec_keys (equation : Equation) : ((equationSpec equation).map Prod.fst).Nodup := by
  simp only [equationSpec, List.map_map]
  have : (Prod.fst ∘ fun name : String => (name, 0)) = id := rfl
  rw [this, List.map_id]
  exact List.nodup_dedup _

theorem equationSpec_covers (equation : Equation) {entry : String × ℕ}
    (inside : entry ∈ occurrences 0 equation.left ++ occurrences 0 equation.right) :
    (entry.1, 0) ∈ equationSpec equation := by
  simp only [equationSpec, List.mem_map, List.mem_dedup]
  exact ⟨entry.1, ⟨entry, inside, rfl⟩, rfl⟩

/-- **Authored first-order equations keep the value** at every environment, premises or not. -/
theorem authored_eval_eq {relEnv : RelationEnv} (contextual : certificate.contextualValid language = true)
    (equations : equationsValid certificate language = true) {source target : Pattern}
    (authored : AuthoredEquation relEnv language source target) (object : isObjectPattern source = true)
    (outer : List A) :
    eval certificate.model (stateValuation certificate.model) outer source =
      eval certificate.model (stateValuation certificate.model) outer target := by
  have commutes := Mettapedia.OSLF.Framework.FiniteModels.Certificate.preorder_commutes
    (Mettapedia.OSLF.Framework.FiniteModels.Certificate.contextual_preorder contextual)
  obtain ⟨-, -, authoredChecked⟩ := equationsValid_parts equations
  cases authored with
  | @forward equation _ initial final witnesses member _ matched premises =>
    have checked := authoredChecked equation member
    simp only [equationCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
    obtain ⟨shape, agree⟩ := checked
    obtain ⟨leftFree, rightFree, leftScoped, rightScoped, rightRests, -, aligned⟩ := equationShape_parts shape
    obtain ⟨-, -, -, forwardRight, -⟩ := equationAligned_parts aligned
    rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ 0 equation.right forwardRight]
    exact side_eval_eq commutes (equationSpec_keys equation) (fun entry inside => equationSpec_covers equation inside)
      leftFree rightFree leftScoped rightScoped rightRests agree matched (premisesValid_extends premises) object outer
  | @reverse equation _ initial final witnesses member _ matched premises =>
    have checked := authoredChecked equation member
    simp only [equationCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
    obtain ⟨shape, agree⟩ := checked
    obtain ⟨leftFree, rightFree, leftScoped, rightScoped, -, leftRests, aligned⟩ := equationShape_parts shape
    obtain ⟨-, -, -, -, reverseLeft⟩ := equationAligned_parts aligned
    rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ 0 equation.left reverseLeft]
    refine side_eval_eq commutes (equationSpec_keys equation) (fun entry inside => equationSpec_covers equation ?_)
      rightFree leftFree rightScoped leftScoped leftRests (fun table member => (agree table member).symm) matched
      (premisesValid_extends premises) object outer
    rcases List.mem_append.mp inside with here | there
    · exact List.mem_append_right _ here
    · exact List.mem_append_left _ there
  | @declared equation _ _ _ _ member notRaw _ =>
    have checked := authoredChecked equation member
    simp only [equationCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
    obtain ⟨-, -, -, -, -, -, aligned⟩ := equationShape_parts checked.1
    exact absurd (equationAligned_parts aligned).1 (by simp [notRaw])
  | @premised equation _ _ _ _ _ member notRaw _ _ =>
    have checked := authoredChecked equation member
    simp only [equationCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
    obtain ⟨-, -, -, -, -, -, aligned⟩ := equationShape_parts checked.1
    exact absurd (equationAligned_parts aligned).1 (by simp [notRaw])

end Certificate

/-- **A model that passes the equation checks respects the equations.** -/
theorem respectsEquations_of_equationsValid [DecidableEq A] {certificate : Certificate A} {relEnv : RelationEnv}
    {language : LanguageDef} (contextual : certificate.contextualValid language = true)
    (equations : Certificate.equationsValid certificate language = true) : RespectsEquations certificate relEnv language := by
  intro first second equivalent
  induction equivalent with
  | rel _ _ step =>
    obtain ⟨firstObject, -, step⟩ := step
    cases step with
    | @inContext context redex contractum generator =>
      have same : ∀ outer, eval certificate.model (stateValuation certificate.model) outer redex =
          eval certificate.model (stateValuation certificate.model) outer contractum := by
        rcases generator with authored | derived
        · exact Certificate.authored_eval_eq contextual equations authored (object_of_fill context firstObject)
        · exact Certificate.derived_eval_eq contextual (Certificate.equationsValid_collectionLaws equations) derived
      exact eval_fill_congr certificate.model (stateValuation certificate.model) same context []
  | refl => rfl
  | symm _ _ _ previous => exact previous.symm
  | trans _ _ _ _ _ first second => exact first.trans second

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
