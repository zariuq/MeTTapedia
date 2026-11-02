import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.GSLT.LanguageDef.ConstructorSupport
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
import Mettapedia.OSLF.MeTTaIL.LinearMatch
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Definitional equations

A definition is an authored equation of a language definition, of one shape:
its left side is a constructor applied to distinct metavariables, its right
side is a first-order schema over them, and it has no premises. A list of
such equations is acyclic when each body mentions neither its own head nor
the head of a later definition.

Nothing new is defined for the equality these equations generate. It is the
equation theory every language definition already has. This module supplies
what is special about the definitional case:

* unfolding one definition, and all of them, as functions on patterns;
* the instances of a definitional equation are exactly its two sides under
  one substitution;
* unfolding the last definition maps the equation theory of the whole list
  into the equation theory of the earlier ones.

The carrier is the raw pattern type. Sorts and typing enter later, where
statements and derivations are compared.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DefinitionalEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.LinearMatch
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

/-- One definition: the defined constructor, its formals and its body. -/
structure Row where
  head : String
  formals : List String
  body : Pattern
  deriving Repr, DecidableEq

namespace Row

/-- The defined constructor applied to its formals. -/
def left (row : Row) : Pattern := .apply row.head (row.formals.map Pattern.fvar)

/-- Distinct formals, and a first-order body over them. -/
structure WellFormed (row : Row) : Prop where
  distinct : row.formals.Nodup
  schema : Schema row.formals row.body

end Row

/-- The authored equation states this definition. -/
structure Defines (equation : Equation) (row : Row) : Prop where
  noPremises : equation.premises = []
  left : equation.left = row.left
  right : equation.right = row.body

private theorem formals_binderFree (names : List String) :
    binderFreeList (names.map Pattern.fvar) = true := by
  induction names with
  | nil => rfl
  | cons name rest previous =>
      simp only [List.map_cons, binderFreeList, binderFree, previous, Bool.and_self]

/-- A well-formed first-order definition is read by the raw matcher even
when binding metadata is present: neither schema side introduces a binder. -/
theorem readsRaw_of_defines {equation : Equation} {row : Row}
    (defines : Defines equation row) (formed : row.WellFormed) : readsRaw equation = true := by
  simp only [readsRaw, defines.left, defines.right, Row.left, binderFree,
    formals_binderFree, formed.schema.binderFree, Bool.and_self, Bool.or_true]

/-! ## Binding application on first-order schemas -/

theorem applyBindings_fvar_of_find {bindings : Bindings} {name : String}
    {entry : String × Pattern}
    (found : bindings.find? (fun entry => entry.1 == name) = some entry) :
    applyBindings bindings (.fvar name) = entry.2 := by
  obtain ⟨key, value⟩ := entry
  simp [applyBindings, found]

theorem applyBindings_fvar_of_not_find {bindings : Bindings} {name : String}
    (absent : bindings.find? (fun entry => entry.1 == name) = none) :
    applyBindings bindings (.fvar name) = .fvar name := by
  simp [applyBindings, absent]

theorem applyBindings_apply (bindings : Bindings) (constructor : String)
    (arguments : List Pattern) :
    applyBindings bindings (.apply constructor arguments) =
      .apply constructor (arguments.map (applyBindings bindings)) := by
  simp [applyBindings]

/-- On a schema, binding application depends only on the values of its
metavariables. -/
theorem applyBindings_schema_congr {names : List String} {first second : Bindings}
    (agree : ∀ name ∈ names,
      applyBindings first (.fvar name) = applyBindings second (.fvar name)) :
    ∀ pattern : Pattern, Schema names pattern →
      applyBindings first pattern = applyBindings second pattern
  | .fvar name, schema => by
      cases schema with
      | metavariable member => exact agree name member
  | .apply constructor arguments, schema => by
      cases schema with
      | constructor schemas =>
        rw [applyBindings_apply, applyBindings_apply]
        congr 1
        apply List.map_congr_left
        intro argument member
        exact applyBindings_schema_congr agree argument (schemas.member member)
  | .bvar _, schema => by cases schema
  | .lambda _ _, schema => by cases schema
  | .multiLambda _ _ _, schema => by cases schema
  | .subst _ _, schema => by cases schema
  | .collection _ _ _, schema => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- Apply a function to every bound value. -/
def mapValues (function : Pattern → Pattern) (bindings : Bindings) : Bindings :=
  bindings.map (fun entry => (entry.1, function entry.2))

theorem applyBindings_mapValues_fvar (function : Pattern → Pattern)
    (fixes : ∀ name, function (.fvar name) = .fvar name) (bindings : Bindings)
    (name : String) :
    applyBindings (mapValues function bindings) (.fvar name) =
      function (applyBindings bindings (.fvar name)) := by
  have mapped : (mapValues function bindings).find? (fun entry => entry.1 == name) =
      (bindings.find? (fun entry => entry.1 == name)).map
        (fun entry => (entry.1, function entry.2)) := by
    simp [mapValues, List.find?_map, Function.comp_def]
  cases found : bindings.find? (fun entry => entry.1 == name) with
  | none =>
    rw [found] at mapped
    rw [applyBindings_fvar_of_not_find mapped, applyBindings_fvar_of_not_find found, fixes]
  | some entry =>
    rw [found] at mapped
    rw [applyBindings_fvar_of_find mapped, applyBindings_fvar_of_find found]

/-! ## Schemas are match-correct -/

theorem isMatchCorrect_of_schema {names : List String} :
    ∀ pattern : Pattern, Schema names pattern → isMatchCorrectAux pattern = true
  | .fvar _, _ => rfl
  | .apply constructor arguments, schema => by
      cases schema with
      | constructor schemas =>
        have each : ∀ argument ∈ arguments, isMatchCorrectAux argument = true :=
          fun argument member => isMatchCorrect_of_schema argument (schemas.member member)
        have all : ∀ patterns : List Pattern,
            (∀ argument ∈ patterns, isMatchCorrectAux argument = true) →
              isMatchCorrectListAux patterns = true := by
          intro patterns
          induction patterns with
          | nil => intro _; rfl
          | cons head tail inductionHypothesis =>
            intro every
            simp only [isMatchCorrectListAux, Bool.and_eq_true]
            exact ⟨every head (by simp),
              inductionHypothesis (fun argument member => every argument (by simp [member]))⟩
        simpa [isMatchCorrectAux] using all arguments each
  | .bvar _, schema => by cases schema
  | .lambda _ _, schema => by cases schema
  | .multiLambda _ _ _, schema => by cases schema
  | .subst _ _, schema => by cases schema
  | .collection _ _ _, schema => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem isMatchCorrect_left (row : Row) : isMatchCorrectAux row.left = true := by
  have all : ∀ names : List String,
      isMatchCorrectListAux (names.map Pattern.fvar) = true := by
    intro names
    induction names with
    | nil => rfl
    | cons head tail inductionHypothesis =>
      simp only [List.map_cons, isMatchCorrectListAux, isMatchCorrectAux, Bool.true_and]
      exact inductionHypothesis
  simpa [Row.left, isMatchCorrectAux] using all row.formals

/-! ## The two sides of a definition under one substitution -/

theorem applyBindings_left (bindings : Bindings) (row : Row) :
    applyBindings bindings row.left =
      .apply row.head (row.formals.map (fun name => applyBindings bindings (.fvar name))) := by
  rw [Row.left, applyBindings_apply, List.map_map]
  rfl

theorem mem_zip_map {names : List String} (function : String → Pattern) {name : String}
    (member : name ∈ names) : (name, function name) ∈ names.zip (names.map function) := by
  induction names with
  | nil => cases member
  | cons head tail inductionHypothesis =>
    rcases List.mem_cons.mp member with rfl | inTail
    · simp
    · simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
      exact Or.inr (inductionHypothesis inTail)

/-- Every substitution instance of a definition is an instance of its
authored equation, so the two sides are equal in the equation theory. -/
theorem instance_equivalent {base : BasePremiseEvaluator} {language : LanguageDef}
    {equation : Equation} {row : Row} (authored : equation ∈ language.equations)
    (defines : Defines equation row) (formed : row.WellFormed) (bindings : Bindings) :
    EquationEquiv base language (applyBindings bindings row.left)
      (applyBindings bindings row.body) := by
  let values := row.formals.map (fun name => applyBindings bindings (.fvar name))
  obtain ⟨matched, member, distinct, -, pairs⟩ :=
    matchArgs_fvars row.formals values formed.distinct (by simp [values])
  have matchedLeft : matched ∈ matchPattern equation.left (.apply row.head values) := by
    rw [defines.left, Row.left, matchPattern]
    simpa [values] using member
  have target : applyBindings matched equation.right = applyBindings bindings row.body := by
    rw [defines.right]
    apply applyBindings_schema_congr (names := row.formals) _ row.body formed.schema
    intro name nameMember
    have pair : (name, applyBindings bindings (.fvar name)) ∈ matched :=
      pairs _ (mem_zip_map (fun name => applyBindings bindings (.fvar name)) nameMember)
    exact applyBindings_fvar_of_find (find?_of_mem_of_nodup matched distinct pair)
  have witness : EquationInstance base language (.apply row.head values)
      (applyBindings bindings row.body) :=
    ⟨0, EquationInstanceAt.forward authored (readsRaw_of_defines defines formed) matchedLeft
      (by rw [defines.noPremises]; exact PremisesAt.nil matched) target⟩
  rw [applyBindings_left]
  exact equationInstance_equivalent witness

/-- An instance of a definitional equation is its two sides under one
substitution, in one of the two orientations. -/
theorem instance_shape {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern}
    (definitional : ∀ equation ∈ language.equations,
      ∃ row : Row, Defines equation row ∧ row.WellFormed)
    (witness : EquationInstance base language source target) :
    ∃ (equation : Equation) (row : Row) (bindings : Bindings),
      equation ∈ language.equations ∧ Defines equation row ∧ row.WellFormed ∧
        ((source = applyBindings bindings row.left ∧
            target = applyBindings bindings row.body) ∨
          (source = applyBindings bindings row.body ∧
            target = applyBindings bindings row.left)) := by
  obtain ⟨fuel, instanceAt⟩ := witness
  cases instanceAt with
  | @forward equation _ _ initial final authored _ matched premises applied =>
    obtain ⟨row, defines, formed⟩ := definitional equation authored
    rw [defines.noPremises] at premises
    cases premises
    refine ⟨equation, row, initial, authored, defines, formed, Or.inl ⟨?_, ?_⟩⟩
    · have correct := matchPattern_correct matched
        (by rw [defines.left]; exact isMatchCorrect_left row)
      rw [← defines.left]
      exact correct.symm
    · rw [← defines.right]
      exact applied.symm
  | @reverse equation _ _ initial final authored _ matched premises applied =>
    obtain ⟨row, defines, formed⟩ := definitional equation authored
    rw [defines.noPremises] at premises
    cases premises
    refine ⟨equation, row, initial, authored, defines, formed, Or.inr ⟨?_, ?_⟩⟩
    · have correct := matchPattern_correct matched
        (by rw [defines.right]; exact isMatchCorrect_of_schema row.body formed.schema)
      rw [← defines.right]
      exact correct.symm
    · rw [← defines.left]
      exact applied.symm
  | declared authored notRaw _ =>
    obtain ⟨row, defines, formed⟩ := definitional _ authored
    rw [readsRaw_of_defines defines formed] at notRaw
    cases notRaw

/-! ## Unfolding one definition -/

mutual
/-- Replace every saturated application of the defined constructor by the
body, everywhere in the pattern. -/
def unfoldOne (row : Row) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply name arguments =>
      if name = row.head ∧ arguments.length = row.formals.length then
        applyBindings (row.formals.zip (unfoldOneList row arguments)) row.body
      else .apply name (unfoldOneList row arguments)
  | .lambda name body => .lambda name (unfoldOne row body)
  | .multiLambda arity names body => .multiLambda arity names (unfoldOne row body)
  | .subst body replacement => .subst (unfoldOne row body) (unfoldOne row replacement)
  | .collection kind elements rest => .collection kind (unfoldOneList row elements) rest

def unfoldOneList (row : Row) : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => unfoldOne row pattern :: unfoldOneList row patterns
end

theorem unfoldOneList_eq_map (row : Row) :
    ∀ patterns : List Pattern, unfoldOneList row patterns = patterns.map (unfoldOne row)
  | [] => rfl
  | pattern :: patterns => by
      rw [unfoldOneList, List.map_cons, unfoldOneList_eq_map row patterns]

@[simp]
theorem unfoldOne_bvar (row : Row) (index : Nat) : unfoldOne row (.bvar index) = .bvar index := by
  rw [unfoldOne]

@[simp]
theorem unfoldOne_fvar (row : Row) (name : String) : unfoldOne row (.fvar name) = .fvar name := by
  rw [unfoldOne]

theorem unfoldOne_apply (row : Row) (name : String) (arguments : List Pattern) :
    unfoldOne row (.apply name arguments) =
      if name = row.head ∧ arguments.length = row.formals.length then
        applyBindings (row.formals.zip (arguments.map (unfoldOne row))) row.body
      else .apply name (arguments.map (unfoldOne row)) := by
  rw [unfoldOne, unfoldOneList_eq_map]

@[simp]
theorem unfoldOne_lambda (row : Row) (name : Option String) (body : Pattern) :
    unfoldOne row (.lambda name body) = .lambda name (unfoldOne row body) := by
  rw [unfoldOne]

@[simp]
theorem unfoldOne_multiLambda (row : Row) (arity : Nat) (names : List String) (body : Pattern) :
    unfoldOne row (.multiLambda arity names body) =
      .multiLambda arity names (unfoldOne row body) := by
  rw [unfoldOne]

@[simp]
theorem unfoldOne_subst (row : Row) (body replacement : Pattern) :
    unfoldOne row (.subst body replacement) =
      .subst (unfoldOne row body) (unfoldOne row replacement) := by
  rw [unfoldOne]

@[simp]
theorem unfoldOne_collection (row : Row) (kind : CollType) (elements : List Pattern)
    (rest : Option String) :
    unfoldOne row (.collection kind elements rest) =
      .collection kind (elements.map (unfoldOne row)) rest := by
  rw [unfoldOne, unfoldOneList_eq_map]

/-! ## Occurrences of a constructor -/

/-- No application of the constructor occurs in the pattern: every
constructor of the pattern is another one. -/
abbrev Avoids (head : String) (pattern : Pattern) : Prop :=
  ConstructorsWithin (· ≠ head) pattern

/-- Executable form of `Avoids`. -/
def checkAvoids (head : String) (pattern : Pattern) : Bool :=
  checkConstructorsWithin (· != head) pattern

theorem checkAvoids_iff (head : String) (pattern : Pattern) :
    checkAvoids head pattern = true ↔ Avoids head pattern :=
  (checkConstructorsWithin_eq_true_iff _ pattern).trans
    ⟨ConstructorsWithin.mono (fun _ differs => by simpa using differs),
      ConstructorsWithin.mono (fun _ differs => by simpa using differs)⟩

/-- Unfolding a constructor the schema does not mention commutes with
substitution into the schema. -/
theorem unfoldOne_applyBindings (row : Row) {names : List String} (bindings : Bindings) :
    ∀ pattern : Pattern, Schema names pattern → Avoids row.head pattern →
      unfoldOne row (applyBindings bindings pattern) =
        applyBindings (mapValues (unfoldOne row) bindings) pattern
  | .fvar name, _, _ =>
      (applyBindings_mapValues_fvar (unfoldOne row) (unfoldOne_fvar row) bindings name).symm
  | .apply constructor arguments, schema, absent => by
      cases schema with
      | constructor schemas =>
        obtain ⟨differs, inside⟩ := (constructorsWithin_apply _ _ _).mp absent
        rw [applyBindings_apply, applyBindings_apply, unfoldOne_apply,
          if_neg (fun both => differs both.1), List.map_map]
        congr 1
        apply List.map_congr_left
        intro argument member
        exact unfoldOne_applyBindings row bindings argument (schemas.member member)
          (inside.of_mem member)
  | .bvar _, schema, _ => by cases schema
  | .lambda _ _, schema, _ => by cases schema
  | .multiLambda _ _ _, schema, _ => by cases schema
  | .subst _ _, schema, _ => by cases schema
  | .collection _ _ _, schema, _ => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-! ## One unfolding pass on instances -/

theorem left_schema (row : Row) : Schema row.formals row.left := by
  have all : ∀ names : List String, (∀ name ∈ names, name ∈ row.formals) →
      Schemas row.formals (names.map Pattern.fvar) := by
    intro names
    induction names with
    | nil => intro _; exact .nil
    | cons head tail inductionHypothesis =>
      intro every
      exact .cons (.metavariable (every head (by simp)))
        (inductionHypothesis (fun name member => every name (by simp [member])))
  exact .constructor (all row.formals (fun _ member => member))

theorem avoids_left {head : String} {row : Row} (differs : row.head ≠ head) :
    Avoids head row.left := by
  refine (constructorsWithin_apply _ _ _).mpr ⟨differs, ?_⟩
  rw [constructorListWithin_iff_forall]
  intro pattern member
  obtain ⟨name, -, rfl⟩ := List.mem_map.mp member
  exact constructorsWithin_fvar _ name

theorem applyBindings_zip_map {names : List String} (distinct : names.Nodup)
    (function : String → Pattern) {name : String} (member : name ∈ names) :
    applyBindings (names.zip (names.map function)) (.fvar name) = function name := by
  have keys : ((names.zip (names.map function)).map Prod.fst).Nodup := by
    rw [List.map_fst_zip (by simp)]
    exact distinct
  exact applyBindings_fvar_of_find
    (find?_of_mem_of_nodup _ keys (mem_zip_map function member))

/-- Unfolding a definition sends each instance of another definition, whose
body does not mention it, to an instance of that other definition. -/
theorem unfoldOne_instance_other (row : Row) {other : Row} (formed : other.WellFormed)
    (differs : other.head ≠ row.head) (absent : Avoids row.head other.body)
    (bindings : Bindings) :
    unfoldOne row (applyBindings bindings other.left) =
        applyBindings (mapValues (unfoldOne row) bindings) other.left ∧
      unfoldOne row (applyBindings bindings other.body) =
        applyBindings (mapValues (unfoldOne row) bindings) other.body :=
  ⟨unfoldOne_applyBindings row bindings other.left (left_schema other) (avoids_left differs),
    unfoldOne_applyBindings row bindings other.body formed.schema absent⟩

/-- Unfolding a definition identifies the two sides of each of its own
instances. -/
theorem unfoldOne_instance_self {row : Row} (formed : row.WellFormed)
    (absent : Avoids row.head row.body) (bindings : Bindings) :
    unfoldOne row (applyBindings bindings row.left) =
      unfoldOne row (applyBindings bindings row.body) := by
  rw [applyBindings_left, unfoldOne_apply, if_pos ⟨rfl, by simp⟩, List.map_map,
    unfoldOne_applyBindings row bindings row.body formed.schema absent]
  apply applyBindings_schema_congr (names := row.formals) _ row.body formed.schema
  intro name member
  rw [applyBindings_zip_map formed.distinct _ member,
    applyBindings_mapValues_fvar (unfoldOne row) (unfoldOne_fvar row)]
  rfl

/-! ## One unfolding pass on the equation theory -/

section Pass

variable {base : BasePremiseEvaluator}

theorem equationEquiv_lookup {language : LanguageDef} (name : String) :
    ∀ (names : List String) {first second : List Pattern},
      List.Forall₂ (EquationEquiv base language) first second →
        EquationEquiv base language (applyBindings (names.zip first) (.fvar name))
          (applyBindings (names.zip second) (.fvar name))
  | [], _, _, _ => by
      simp only [List.zip_nil_left]
      exact Relation.EqvGen.refl _
  | _ :: _, _, _, .nil => by
      simp only [List.zip_nil_right]
      exact Relation.EqvGen.refl _
  | head :: tail, left :: leftTail, right :: rightTail, .cons related rest => by
      by_cases same : head = name
      · have foundLeft : ((head, left) :: tail.zip leftTail).find?
            (fun entry => entry.1 == name) = some (head, left) := by simp [same]
        have foundRight : ((head, right) :: tail.zip rightTail).find?
            (fun entry => entry.1 == name) = some (head, right) := by simp [same]
        rw [List.zip_cons_cons, List.zip_cons_cons, applyBindings_fvar_of_find foundLeft,
          applyBindings_fvar_of_find foundRight]
        exact related
      · have step : ∀ (value : Pattern) (others : List Pattern),
            applyBindings ((head, value) :: tail.zip others) (.fvar name) =
              applyBindings (tail.zip others) (.fvar name) := by
          intro value others
          cases found : (tail.zip others).find? (fun entry => entry.1 == name) with
          | none =>
            have whole : ((head, value) :: tail.zip others).find?
                (fun entry => entry.1 == name) = none := by simp [same, found]
            rw [applyBindings_fvar_of_not_find whole, applyBindings_fvar_of_not_find found]
          | some entry =>
            have whole : ((head, value) :: tail.zip others).find?
                (fun entry => entry.1 == name) = some entry := by simp [same, found]
            rw [applyBindings_fvar_of_find whole, applyBindings_fvar_of_find found]
        rw [List.zip_cons_cons, List.zip_cons_cons, step, step]
        exact equationEquiv_lookup name tail rest

/-- Pointwise equal arguments give equal instances of a schema. -/
theorem equationEquiv_instantiate {language : LanguageDef} (names : List String)
    {first second : List Pattern}
    (pointwise : List.Forall₂ (EquationEquiv base language) first second) :
    ∀ pattern : Pattern, Schema names pattern →
      EquationEquiv base language (applyBindings (names.zip first) pattern)
        (applyBindings (names.zip second) pattern)
  | .fvar name, _ => equationEquiv_lookup name names pointwise
  | .apply constructor arguments, schema => by
      cases schema with
      | constructor schemas =>
        rw [applyBindings_apply, applyBindings_apply]
        apply equationEquiv_apply_of_forall₂
        apply List.forall₂_map_left_iff.mpr
        apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro argument member
        exact equationEquiv_instantiate names pointwise argument (schemas.member member)
  | .bvar _, schema => by cases schema
  | .lambda _ _, schema => by cases schema
  | .multiLambda _ _ _, schema => by cases schema
  | .subst _ _, schema => by cases schema
  | .collection _ _ _, schema => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem forall₂_middle {relation : Pattern → Pattern → Prop}
    (reflexive : ∀ pattern, relation pattern pattern) {left right : Pattern}
    (related : relation left right) (after : List Pattern) :
    ∀ before : List Pattern,
      List.Forall₂ relation (before ++ left :: after) (before ++ right :: after)
  | [] => .cons related (List.forall₂_same.mpr (fun pattern _ => reflexive pattern))
  | head :: tail => .cons (reflexive head) (forall₂_middle reflexive related after tail)

/-- A relation between the unfoldings of two patterns survives every context. -/
theorem equationEquiv_unfoldOne_fill {language : LanguageDef} {row : Row}
    (formed : row.WellFormed) {redex contractum : Pattern}
    (related : EquationEquiv base language (unfoldOne row redex) (unfoldOne row contractum)) :
    ∀ context : OneHoleContext,
      EquationEquiv base language (unfoldOne row (context.fill redex))
        (unfoldOne row (context.fill contractum))
  | .hole => related
  | .apply constructor before inner after => by
      have inside := equationEquiv_unfoldOne_fill formed related inner
      simp only [OneHoleContext.fill, unfoldOne_apply, List.length_append, List.length_cons,
        List.map_append, List.map_cons]
      split
      · exact equationEquiv_instantiate row.formals
          (forall₂_middle (fun pattern => Relation.EqvGen.refl pattern) inside _ _) row.body
          formed.schema
      · exact equationEquiv_fill
          (.apply constructor (before.map (unfoldOne row)) .hole (after.map (unfoldOne row)))
          inside
  | .lambda name inner => by
      simpa [OneHoleContext.fill] using
        equationEquiv_fill (.lambda name .hole) (equationEquiv_unfoldOne_fill formed related inner)
  | .multiLambda arity names inner => by
      simpa [OneHoleContext.fill] using
        equationEquiv_fill (.multiLambda arity names .hole)
          (equationEquiv_unfoldOne_fill formed related inner)
  | .substBody inner replacement => by
      simpa [OneHoleContext.fill] using
        equationEquiv_fill (.substBody .hole (unfoldOne row replacement))
          (equationEquiv_unfoldOne_fill formed related inner)
  | .substReplacement body inner => by
      simpa [OneHoleContext.fill] using
        equationEquiv_fill (.substReplacement (unfoldOne row body) .hole)
          (equationEquiv_unfoldOne_fill formed related inner)
  | .collection kind before inner after rest => by
      simpa [OneHoleContext.fill] using
        equationEquiv_fill
          (.collection kind (before.map (unfoldOne row)) .hole (after.map (unfoldOne row)) rest)
          (equationEquiv_unfoldOne_fill formed related inner)

/-- An instance of a definitional equation, read on the equation's own sides. -/
theorem instance_sides {language : LanguageDef} {source target : Pattern}
    (definitional : ∀ equation ∈ language.equations,
      ∃ row : Row, Defines equation row ∧ row.WellFormed)
    (witness : EquationInstance base language source target) :
    ∃ (equation : Equation) (bindings : Bindings), equation ∈ language.equations ∧
      ((source = applyBindings bindings equation.left ∧
          target = applyBindings bindings equation.right) ∨
        (source = applyBindings bindings equation.right ∧
          target = applyBindings bindings equation.left)) := by
  obtain ⟨equation, row, bindings, authored, defines, -, sides⟩ :=
    instance_shape definitional witness
  refine ⟨equation, bindings, authored, ?_⟩
  rw [defines.left, defines.right]
  exact sides

/-- **One pass.** Unfolding a definition maps the equation theory of a
language into the equation theory of the language without that definition.
Each other definition must be well formed, have a different head and a body
that does not mention the unfolded one. -/
theorem equationEquiv_unfoldOne_pass {larger smaller : LanguageDef} {row : Row}
    (noDerived : ∀ source target : Pattern, ¬ DerivedInstance larger source target)
    (formed : row.WellFormed) (ownHead : Avoids row.head row.body)
    (classified : ∀ equation ∈ larger.equations,
      Defines equation row ∨
        ∃ other : Row, Defines equation other ∧ other.WellFormed ∧ other.head ≠ row.head ∧
          Avoids row.head other.body ∧ equation ∈ smaller.equations)
    {left right : Pattern} (equivalent : EquationEquiv base larger left right) :
    EquationEquiv base smaller (unfoldOne row left) (unfoldOne row right) := by
  have definitional : ∀ equation ∈ larger.equations,
      ∃ row : Row, Defines equation row ∧ row.WellFormed := by
    intro equation authored
    rcases classified equation authored with defines | ⟨other, defines, otherFormed, -⟩
    · exact ⟨row, defines, formed⟩
    · exact ⟨other, defines, otherFormed⟩
  induction equivalent with
  | rel source target step =>
    cases step with
    | inContext context generator =>
      apply equationEquiv_unfoldOne_fill formed _ context
      rcases generator with witness | derived
      · obtain ⟨equation, bindings, authored, sides⟩ := instance_sides definitional witness
        rcases classified equation authored with
          defines | ⟨other, defines, otherFormed, differs, absent, kept⟩
        · have same := unfoldOne_instance_self formed ownHead bindings
          rw [defines.left, defines.right] at sides
          rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [same]
            exact Relation.EqvGen.refl _
          · rw [same]
            exact Relation.EqvGen.refl _
        · obtain ⟨leftImage, bodyImage⟩ :=
            unfoldOne_instance_other row otherFormed differs absent bindings
          have image := instance_equivalent (base := base) kept defines otherFormed
            (mapValues (unfoldOne row) bindings)
          rw [defines.left, defines.right] at sides
          rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [leftImage, bodyImage]
            exact image
          · rw [leftImage, bodyImage]
            exact Relation.EqvGen.symm _ _ image
      · exact absurd derived (noDerived _ _)
  | refl pattern => exact Relation.EqvGen.refl _
  | symm _ _ _ inductionHypothesis => exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans _ _ _ _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- Every pattern is equal, in the equation theory, to its unfolding by an
authored definition. -/
theorem equationEquiv_unfoldOne {language : LanguageDef} {equation : Equation} {row : Row}
    (authored : equation ∈ language.equations) (defines : Defines equation row)
    (formed : row.WellFormed) :
    ∀ pattern : Pattern, EquationEquiv base language pattern (unfoldOne row pattern)
  | .bvar index => by
      rw [unfoldOne_bvar]
      exact Relation.EqvGen.refl _
  | .fvar name => by
      rw [unfoldOne_fvar]
      exact Relation.EqvGen.refl _
  | .apply name arguments => by
      have pointwise : List.Forall₂ (EquationEquiv base language) arguments
          (arguments.map (unfoldOne row)) := by
        apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro argument member
        exact equationEquiv_unfoldOne authored defines formed argument
      have congruence := equationEquiv_apply_of_forall₂ name pointwise
      rw [unfoldOne_apply]
      split
      · rename_i saturated
        obtain ⟨rfl, lengths⟩ := saturated
        have unfolded := instance_equivalent (base := base) authored defines formed
          (row.formals.zip (arguments.map (unfoldOne row)))
        have leftSide : applyBindings (row.formals.zip (arguments.map (unfoldOne row)))
            row.left = .apply row.head (arguments.map (unfoldOne row)) := by
          rw [Row.left, applyBindings_apply]
          congr 1
          exact applyBindings_fvars _
            (by rw [List.map_fst_zip (by simp [lengths])]; exact formed.distinct)
            row.formals _ (by simp [lengths]) (fun pair member => member)
        rw [leftSide] at unfolded
        exact Relation.EqvGen.trans _ _ _ congruence unfolded
      · exact congruence
  | .lambda name body => by
      rw [unfoldOne_lambda]
      simpa [OneHoleContext.fill] using
        equationEquiv_fill (.lambda name .hole)
          (equationEquiv_unfoldOne authored defines formed body)
  | .multiLambda arity names body => by
      rw [unfoldOne_multiLambda]
      simpa [OneHoleContext.fill] using
        equationEquiv_fill (.multiLambda arity names .hole)
          (equationEquiv_unfoldOne authored defines formed body)
  | .subst body replacement => by
      rw [unfoldOne_subst]
      have first : EquationEquiv base language (.subst body replacement)
          (.subst (unfoldOne row body) replacement) := by
        simpa [OneHoleContext.fill] using
          equationEquiv_fill (.substBody .hole replacement)
            (equationEquiv_unfoldOne authored defines formed body)
      have second : EquationEquiv base language (.subst (unfoldOne row body) replacement)
          (.subst (unfoldOne row body) (unfoldOne row replacement)) := by
        simpa [OneHoleContext.fill] using
          equationEquiv_fill (.substReplacement (unfoldOne row body) .hole)
            (equationEquiv_unfoldOne authored defines formed replacement)
      exact Relation.EqvGen.trans _ _ _ first second
  | .collection kind elements rest => by
      rw [unfoldOne_collection]
      apply equationEquiv_collection_of_forall₂
      apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_same.mpr
      intro element member
      exact equationEquiv_unfoldOne authored defines formed element
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

end Pass

end Mettapedia.GSLT.LanguageDef.DefinitionalEquations
