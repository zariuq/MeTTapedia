import Mettapedia.GSLT.Compilation.Uniform.QueryPremises
import Mettapedia.GSLT.Compilation.Uniform.Instantiation
import Mettapedia.OSLF.MeTTaIL.ReferenceStep
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderTyping

/-!
# Rules whose premises ask the step, at the reference meaning

A premise may ask the step itself (`ReferenceStep.PremiseValid.step`): its source, instantiated scope-correctly at the
premise's depth, steps to a term that its target matches. A quantified premise (`PremiseValid.forAll`) holds its body
for each element of a bound collection, with its parameter bound to the element; what the body binds stays inside.
A reference step is an instance of one rule's triple: the left side matches, the premises have witnesses, and the
right side is instantiated scope-correctly at depth zero (`step_iff`). Steps of data are data (`step_data`).

What premises state is read along them (`Hold`): each premise reads its inputs at the names bound before it
(`restrict`), as the source evaluates it, so a name nothing has bound yet stands for itself. A query asks its relation
for the rows of its arguments read that way and its arguments are the row it gets; a step premise's source, a
freshness condition and a quantified premise's collection are read that way too; a quantified premise's body sees only
the names bound before it and its parameter (`PremiseHolds`). No condition on the relations is needed.

The conditions on premises concern shapes only (`Flows`): a query's arguments and a step premise's target are ordered,
a vector rest in a query, a freshness term or a step premise is a vector rest of the left side, and a bag or set rest
of a source is one of the left side; a quantified premise's parameter shadows a rest of the same name in its body. The
right side and every step premise's source carry no binder names, and a rest of the right side is a rest of the left
side of the same kind (`TripleShape`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.StepPremises

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open Mettapedia.OSLF.MeTTaIL.Substitution (checkFreshness)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (StepValid PremiseValid PremisesValid ForAllValid Witness Step stepDepth
  stepEndpoints captureSitesOf isBase bindParameter)
open OrderedMatching
open QueryPremises (DataRows queryRows mem_query arguments_sound arguments_binds arguments_data arguments_complete)
open MatchesAndInstances (vectorRests bagRests BagSettled)

/-- The names a quantified premise's body sees: its parameter, and the names bound before it, which the parameter
shadows. -/
def scopeOf (bound : List String) (parameter : String) : List String := parameter :: bound.filter (· ≠ parameter)

theorem mem_scopeOf {bound : List String} {parameter name : String} :
    name ∈ scopeOf bound parameter ↔ name = parameter ∨ name ∈ bound := by
  simp only [scopeOf, List.mem_cons, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (same | ⟨inside, -⟩)
    · exact .inl same
    · exact .inr inside
  · rintro (same | inside)
    · exact .inl same
    · by_cases same : name = parameter
      · exact .inl same
      · exact .inr ⟨inside, same⟩

/-- **Bindings restricted to some names**: what is bound when only those names have been bound. -/
def restrict (bindings : Bindings) (visible : List String) : Bindings :=
  bindings.filter fun entry => entry.1 ∈ visible

theorem find?_restrict (bindings : Bindings) (visible : List String) (name : String) :
    (restrict bindings visible).find? (·.1 == name) =
      if name ∈ visible then bindings.find? (·.1 == name) else none := by
  induction bindings with
  | nil => simp [restrict]
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      simp only [restrict] at ih ⊢
      by_cases keyVisible : key ∈ visible
      · by_cases same : key = name
        · subst same
          simp [keyVisible]
        · have differ : (key == name) = false := by simpa using same
          simp only [List.filter_cons, keyVisible, decide_true, ↓reduceIte, List.find?_cons, differ, ih]
      · by_cases same : key = name
        · subst same
          simp [keyVisible, ih]
        · have differ : (key == name) = false := by simpa using same
          simp only [List.filter_cons, keyVisible, decide_false, Bool.false_eq_true, ↓reduceIte, List.find?_cons,
            differ, ih]

theorem lookupOrFvar_restrict (bindings : Bindings) (visible : List String) (name : String) :
    lookupOrFvar (restrict bindings visible) name =
      if name ∈ visible then lookupOrFvar bindings name else .fvar name := by
  by_cases inside : name ∈ visible
  · simp only [lookupOrFvar, applyBindings, find?_restrict, if_pos inside]
  · simp only [lookupOrFvar, applyBindings, find?_restrict, if_neg inside]

theorem dataOn_restrict {bindings : Bindings} (values : DataOn bindings) (visible : List String) :
    DataOn (restrict bindings visible) := by
  intro name value found
  rw [find?_restrict] at found
  split at found
  · exact values name value found
  · cases found

theorem settled_restrict {bindings : Bindings} {rests : List String} (settled : Settled bindings rests)
    {visible : List String} (within : ∀ rest ∈ rests, rest ∈ visible) : Settled (restrict bindings visible) rests := by
  intro rest inside
  rw [find?_restrict, if_pos (within rest inside)]
  exact settled rest inside

theorem bagSettled_restrict {bindings : Bindings} {pairs : List (String × CollType)} (settled : BagSettled bindings pairs)
    {visible : List String} (within : ∀ pair ∈ pairs, pair.1 ∈ visible) :
    BagSettled (restrict bindings visible) pairs := by
  intro pair inside
  rw [find?_restrict, if_pos (within pair inside)]
  exact settled pair inside

/-- A name bindings do not bind reads as itself. -/
theorem lookupOrFvar_absent {bindings : Bindings} {name : String} (absent : ∀ v, (name, v) ∉ bindings) :
    lookupOrFvar bindings name = .fvar name := by
  have none : bindings.find? (·.1 == name) = none := by
    rw [List.find?_eq_none]
    intro entry inside same
    have named : entry.1 = name := by simpa using same
    exact absent entry.2 (named ▸ inside)
  simp [lookupOrFvar, applyBindings, none]

/-- **Bindings of exactly the names bound so far** read, at every name, as any bindings that agree with them there,
restricted to those names: a name not bound yet stands for itself. -/
theorem lookupOrFvar_point {seed later : Bindings} {bound : List String}
    (keys : ∀ x v, (x, v) ∈ seed → x ∈ bound)
    (agree : ∀ name ∈ bound, lookupOrFvar seed name = lookupOrFvar later name) (name : String) :
    lookupOrFvar seed name = lookupOrFvar (restrict later bound) name := by
  rw [lookupOrFvar_restrict]
  split
  · exact agree name ‹_›
  · rename_i outside
    have absent : seed.find? (·.1 == name) = none := by
      rw [List.find?_eq_none]
      intro entry inside same
      have named : entry.1 = name := by simpa using same
      exact outside (named ▸ keys entry.1 entry.2 inside)
    simp [lookupOrFvar, applyBindings, absent]

/-- **The shapes premises are read in**, from the names bound before the first: a query's arguments and a step
premise's target are ordered, every vector rest is one of `settled`, and every bag or set rest of a source is one of
`bags`. A quantified premise's body is read from the names bound before it and its parameter, which shadows a rest of
the same name there, as the source's `bindParameter` does; the last index holds what is bound at the end. A name an
input mentions need not be bound: it is read as itself. -/
inductive Flows : List String → List (String × CollType) → List String → List Premise → List String → Prop
  | nil {settled : List String} {bags : List (String × CollType)} {bound : List String} :
      Flows settled bags bound [] bound
  | query {settled : List String} {bags : List (String × CollType)} {bound last : List String} {relation : String}
      {arguments : List Pattern} {premises : List Premise} :
      orderedList arguments = true →
      (∀ rest ∈ restNamesList arguments, rest ∈ settled) →
      Flows settled bags (bound ++ namesList arguments) premises last →
      Flows settled bags bound (.relationQuery relation arguments :: premises) last
  | step {settled : List String} {bags : List (String × CollType)} {bound last : List String} {premise : Premise}
      {source target : Pattern} {premises : List Premise} :
      stepEndpoints premise = some (source, target) →
      source.hasCanonicalBinderMetadata = true → ordered target = true →
      (∀ rest ∈ vectorRests source ++ restNames target, rest ∈ settled) →
      (∀ pair ∈ bagRests source, pair ∈ bags) →
      Flows settled bags (bound ++ names target) premises last →
      Flows settled bags bound (premise :: premises) last
  | fresh {settled : List String} {bags : List (String × CollType)} {bound last : List String}
      {condition : FreshnessCondition} {premises : List Premise} :
      ordered condition.term = true →
      (∀ rest ∈ restNames condition.term, rest ∈ settled) →
      Flows settled bags bound premises last →
      Flows settled bags bound (.freshness condition :: premises) last
  | forAll {settled : List String} {bags : List (String × CollType)} {bound last inner : List String}
      {collection parameter : String} {body : Premise} {premises : List Premise} :
      Flows (settled.filter (· ≠ parameter)) (bags.filter (·.1 ≠ parameter)) (scopeOf bound parameter) [body] inner →
      Flows settled bags bound premises last →
      Flows settled bags bound (.forAll collection parameter body :: premises) last

/-- **A freshness condition holds under bindings**: its name is a name, and it does not occur free in the
instantiated term. -/
def FreshHolds (bindings : Bindings) (condition : FreshnessCondition) : Prop :=
  ∃ name, lookupOrFvar bindings condition.varName = .fvar name ∧
    checkFreshness { varName := name, term := applyBindings bindings condition.term } = true

/-- The names bound after a premise, given those bound before it: a query binds its arguments' names, a step premise
its target's; the others bind nothing outside. -/
def nextBound (bound : List String) : Premise → List String
  | .relationQuery _ arguments => bound ++ namesList arguments
  | .congruence _ target => bound ++ names target
  | .scopedStep step => bound ++ names step.target
  | .freshness _ => bound
  | .forAll _ _ _ => bound

/-- The names bound after some premises, given those bound before the first. -/
def boundAfter : List String → List Premise → List String
  | bound, [] => bound
  | bound, premise :: premises => boundAfter (nextBound bound premise) premises

variable (relEnv : RelationEnv) (language : LanguageDef) in
/-- **What a premise states**, for a relation `S` of steps and binding sites `sites`, under the bindings of an
instance, with the names `visible` bound before it. Its inputs are read at the visible names, a name not bound yet
standing for itself: a query's arguments are a row its relation offers for the arguments read so; its step source,
instantiated scope-correctly at its depth, is related by `S` to its target; its freshness condition holds; and for each
element of its collection the body holds under bindings of the kind `good` that agree, on the parameter and the visible
names, with the bindings and the parameter bound to the element. -/
def PremiseHolds (S : Pattern → Pattern → Prop) (sites : Pattern) (good : Bindings → Prop) :
    List String → Bindings → Premise → Prop
  | visible, bindings, .relationQuery relation arguments =>
      arguments.map (applyBindings bindings) ∈
        queryRows relEnv language relation (arguments.map (applyBindings (restrict bindings visible)))
  | visible, bindings, .freshness condition => FreshHolds (restrict bindings visible) condition
  | visible, bindings, .congruence source target =>
      S (applyBindingsScoped sites (restrict bindings visible) (stepDepth sites (.congruence source target)) source)
        (applyBindings bindings target)
  | visible, bindings, .scopedStep step =>
      S (applyBindingsScoped sites (restrict bindings visible) (stepDepth sites (.scopedStep step)) step.source)
        (applyBindings bindings step.target)
  | visible, bindings, .forAll collection parameter body =>
      ∃ kind elements, lookupOrFvar (restrict bindings visible) collection = .collection kind elements none ∧
        ∀ element ∈ elements, ∃ result : Bindings, good result ∧
          (∀ name ∈ parameter :: visible,
            lookupOrFvar result name = lookupOrFvar (bindParameter bindings parameter element) name) ∧
          PremiseHolds S sites good (scopeOf visible parameter) result body

variable (relEnv : RelationEnv) (language : LanguageDef) in
/-- **What premises state** under the bindings of an instance, read along them from the names bound before the first. -/
def Hold (S : Pattern → Pattern → Prop) (sites : Pattern) (good : Bindings → Prop) (bindings : Bindings) :
    List String → List Premise → Prop
  | _, [] => True
  | bound, premise :: premises => PremiseHolds relEnv language S sites good bound bindings premise ∧
      Hold S sites good bindings (nextBound bound premise) premises

open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine in
theorem resolve_iff (bindings : Bindings) (varName name : String) :
    resolveFreshVarName bindings varName = some name ↔ lookupOrFvar bindings varName = .fvar name := by
  simp only [resolveFreshVarName, Bindings.lookup, lookupOrFvar, applyBindings]
  cases bindings.find? (·.1 == varName) with
  | none => simp
  | some entry =>
      obtain ⟨key, value⟩ := entry
      cases value <;> simp

open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine in
/-- **The evaluator passes a freshness condition** exactly when it holds, and keeps the bindings. -/
theorem fresh_mem {relEnv : RelationEnv} {language : LanguageDef} {bindings result : Bindings}
    {condition : FreshnessCondition} :
    result ∈ premiseStepWithEnv relEnv language bindings (.freshness condition) ↔
      result = bindings ∧ FreshHolds bindings condition := by
  simp only [premiseStepWithEnv]
  constructor
  · intro inside
    split at inside
    · rename_i name resolved
      split at inside
      · rename_i checked
        exact ⟨List.mem_singleton.mp inside, name, (resolve_iff bindings condition.varName name).mp resolved, checked⟩
      · exact absurd inside List.not_mem_nil
    · exact absurd inside List.not_mem_nil
  · rintro ⟨rfl, name, looked, checked⟩
    rw [(resolve_iff result condition.varName name).mpr looked]
    simp only
    rw [if_pos checked]
    exact List.mem_singleton_self _

/-- **The shape of a triple** (left side, right side, premises) whose instances are read off its bindings: the right
side carries no binder names, every rest of the right side is a rest of the left side of the same kind, and the
premises are read in their shapes from the left side's names. A name of the right side that nothing binds stands for
itself. Every rule the compiler accepts is one, and so is each orientation of an equation it accepts. -/
structure TripleShape (left right : Pattern) (premises : List Premise) : Prop where
  rightCanonical : right.hasCanonicalBinderMetadata = true
  restsWithin : ∀ rest ∈ vectorRests right, rest ∈ vectorRests left
  bagsWithin : ∀ pair ∈ bagRests right, pair ∈ bagRests left
  flows : ∃ last, Flows (vectorRests left) (bagRests left) (names left) premises last

variable {relEnv : RelationEnv} {language : LanguageDef}

/-! ## What premises state -/

theorem nextBound_step {bound : List String} {premise : Premise} {source target : Pattern}
    (endpoints : stepEndpoints premise = some (source, target)) : nextBound bound premise = bound ++ names target := by
  cases premise <;> simp_all [stepEndpoints, nextBound]

/-- What is bound at the end of premises read in their shapes is what they bind. -/
theorem Flows.last_eq :
    ∀ {settled : List String} {bags : List (String × CollType)} {bound : List String} {premises : List Premise}
      {last : List String}, Flows settled bags bound premises last → last = boundAfter bound premises
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .query _ _ flows => by
      simp only [boundAfter, nextBound]
      exact Flows.last_eq flows
  | _, _, _, _, _, .step endpoints _ _ _ _ flows => by
      rw [boundAfter, nextBound_step endpoints]
      exact Flows.last_eq flows
  | _, _, _, _, _, .fresh _ _ flows => by
      simp only [boundAfter, nextBound]
      exact Flows.last_eq flows
  | _, _, _, _, _, .forAll _ flows => by
      simp only [boundAfter, nextBound]
      exact Flows.last_eq flows

theorem premiseHolds_step {S : Pattern → Pattern → Prop} {sites : Pattern} {good : Bindings → Prop}
    {visible : List String} {bindings : Bindings} {premise : Premise} {source target : Pattern}
    (endpoints : stepEndpoints premise = some (source, target)) :
    PremiseHolds relEnv language S sites good visible bindings premise ↔
      S (applyBindingsScoped sites (restrict bindings visible) (stepDepth sites premise) source)
        (applyBindings bindings target) := by
  cases premise <;> simp_all [stepEndpoints, PremiseHolds]

theorem PremiseHolds.mono {S S' : Pattern → Pattern → Prop} (wider : ∀ u v, S u v → S' u v) {sites : Pattern}
    {good good' : Bindings → Prop} (better : ∀ bindings, good bindings → good' bindings) :
    ∀ {visible : List String} {bindings : Bindings} (premise : Premise),
      PremiseHolds relEnv language S sites good visible bindings premise →
      PremiseHolds relEnv language S' sites good' visible bindings premise
  | _, _, .relationQuery _ _, holds => holds
  | _, _, .freshness _, holds => holds
  | _, _, .congruence _ _, holds => wider _ _ holds
  | _, _, .scopedStep _, holds => wider _ _ holds
  | _, _, .forAll _ _ body, ⟨kind, elements, looked, each⟩ => ⟨kind, elements, looked, fun element inside =>
      (each element inside).imp fun result found =>
        ⟨better result found.1, found.2.1, PremiseHolds.mono wider better body found.2.2⟩⟩

theorem Hold.mono {S S' : Pattern → Pattern → Prop} (wider : ∀ u v, S u v → S' u v) {sites : Pattern}
    {good good' : Bindings → Prop} (better : ∀ bindings, good bindings → good' bindings) {bindings : Bindings} :
    ∀ {bound : List String} (premises : List Premise),
      Hold relEnv language S sites good bindings bound premises →
        Hold relEnv language S' sites good' bindings bound premises
  | _, [], _ => trivial
  | _, premise :: premises, ⟨here, later⟩ =>
      ⟨PremiseHolds.mono wider better premise here, Hold.mono wider better premises later⟩

/-- A freshness condition depends only on the values of its name and of its term's names. -/
theorem freshHolds_agree {first second : Bindings} {condition : FreshnessCondition}
    (shape : ordered condition.term = true)
    (agree : ∀ name ∈ condition.varName :: names condition.term, lookupOrFvar first name = lookupOrFvar second name)
    (holds : FreshHolds first condition) : FreshHolds second condition := by
  obtain ⟨name, looked, checked⟩ := holds
  refine ⟨name, (agree _ List.mem_cons_self).symm.trans looked, ?_⟩
  rw [← instance_agree condition.term shape fun other inside => agree other (List.mem_cons_of_mem _ inside)]
  exact checked

/-! ## A parameter bound to an element -/

theorem find?_filter_ne (bindings : Bindings) {parameter name : String} (differ : name ≠ parameter) :
    (bindings.filter (·.1 != parameter)).find? (·.1 == name) = bindings.find? (·.1 == name) := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      by_cases keyIs : key = parameter
      · subst keyIs
        have notName : (key == name) = false := by simpa [beq_iff_eq] using fun same => differ same.symm
        simp [notName, ih]
      · have kept : (key != parameter) = true := by simpa using keyIs
        simp only [List.filter_cons, kept, ↓reduceIte, List.find?_cons, ih]

theorem find_bindParameter (bindings : Bindings) (parameter : String) (element : Pattern) (name : String) :
    (bindParameter bindings parameter element).find? (·.1 == name) =
      if name = parameter then some (parameter, element) else bindings.find? (·.1 == name) := by
  by_cases same : name = parameter
  · subst same
    simp [bindParameter]
  · have notHere : (parameter == name) = false := by simpa [beq_iff_eq] using fun h => same h.symm
    simp only [bindParameter, List.find?_cons, notHere, if_neg same, find?_filter_ne bindings same]

theorem lookupOrFvar_bindParameter (bindings : Bindings) (parameter : String) (element : Pattern) (name : String) :
    lookupOrFvar (bindParameter bindings parameter element) name =
      if name = parameter then element else lookupOrFvar bindings name := by
  by_cases same : name = parameter
  · subst same
    simp [lookupOrFvar, applyBindings, find_bindParameter]
  · simp only [lookupOrFvar, applyBindings, find_bindParameter, if_neg same]

theorem lookupOrFvar_of_lookup {bindings : Bindings} {name : String} {value : Pattern}
    (looked : bindings.lookup name = some value) : lookupOrFvar bindings name = value := by
  simp only [Bindings.lookup, Option.map_eq_some_iff] at looked
  obtain ⟨⟨key, value'⟩, found, rfl⟩ := looked
  simp [lookupOrFvar, applyBindings, found]

theorem lookup_of_lookupOrFvar {bindings : Bindings} {name : String} {kind : CollType} {elements : List Pattern}
    (looked : lookupOrFvar bindings name = .collection kind elements none) :
    bindings.lookup name = some (.collection kind elements none) := by
  simp [Bindings.lookup, CollectionMatching.find_of_lookup_collection looked]

theorem bindParameter_covers {bindings : Bindings} {bound : List String} (covered : Covers bindings bound)
    (parameter : String) (element : Pattern) :
    Covers (bindParameter bindings parameter element) (scopeOf bound parameter) := by
  intro name inside
  rw [find_bindParameter]
  split
  · exact ⟨element, by simp_all⟩
  · rename_i differ
    exact covered name ((mem_scopeOf.mp inside).resolve_left differ)

theorem bindParameter_data {bindings : Bindings} (values : DataOn bindings) (parameter : String) {element : Pattern}
    (data : isData element = true) : DataOn (bindParameter bindings parameter element) := by
  intro name value found
  rw [find_bindParameter] at found
  split at found
  · simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨-, rfl⟩ := found
    exact data
  · exact values name value found

/-- Binding a parameter keeps every rest settled but one of its name, which it shadows. -/
theorem bindParameter_settled {bindings : Bindings} {rests : List String} (settled : Settled bindings rests)
    (parameter : String) (element : Pattern) :
    Settled (bindParameter bindings parameter element) (rests.filter (· ≠ parameter)) := by
  intro rest inside
  obtain ⟨inRests, differ⟩ := List.mem_filter.mp inside
  rw [find_bindParameter, if_neg (by simpa using differ)]
  exact settled rest inRests

theorem bindParameter_bags {bindings : Bindings} {bags : List (String × CollType)} (settled : BagSettled bindings bags)
    (parameter : String) (element : Pattern) :
    BagSettled (bindParameter bindings parameter element) (bags.filter (·.1 ≠ parameter)) := by
  intro pair inside
  obtain ⟨inBags, differ⟩ := List.mem_filter.mp inside
  rw [find_bindParameter, if_neg (by simpa using differ)]
  exact settled pair inBags

theorem bindParameter_keys {bindings : Bindings} {bound : List String}
    (keys : ∀ x v, (x, v) ∈ bindings → x ∈ bound) (parameter : String) (element : Pattern) :
    ∀ x v, (x, v) ∈ bindParameter bindings parameter element → x ∈ scopeOf bound parameter := by
  intro x v inside
  simp only [bindParameter, List.mem_cons, Prod.mk.injEq, List.mem_filter] at inside
  rcases inside with ⟨rfl, -⟩ | ⟨inside, -⟩
  · exact mem_scopeOf.mpr (.inl rfl)
  · exact mem_scopeOf.mpr (.inr (keys x v inside))

/-! ## Premise witnesses -/

/-- **A step witness inside a premise witness**, at any depth of quantified premises. -/
inductive StepWithin : Witness → Witness → Prop
  | here {step : Witness} {candidate : Pattern} {matched result : Bindings} :
      StepWithin step (.premiseStep step candidate matched result)
  | forAll {step body : Witness} {bodies : List Witness} : body ∈ bodies → StepWithin step body →
      StepWithin step (.forAll bodies)

theorem StepWithin.lt : ∀ {step witness : Witness}, StepWithin step witness → sizeOf step < sizeOf witness
  | _, _, .here => by simp only [Witness.premiseStep.sizeOf_spec]; omega
  | _, _, .forAll inside within => by
      have inner := within.lt
      have member := List.sizeOf_lt_of_mem inside
      simp only [Witness.forAll.sizeOf_spec]
      omega

/-- A step a premise witnesses is smaller than the rule's witness around it. -/
theorem nested_lt {index : ℕ} {initial : Bindings} {witnesses : List Witness} {step : Witness}
    (inside : ∃ witness ∈ witnesses, StepWithin step witness) :
    sizeOf step < sizeOf (Witness.rule index initial witnesses) := by
  obtain ⟨witness, member, within⟩ := inside
  have inner := within.lt
  have below := List.sizeOf_lt_of_mem member
  simp only [Witness.rule.sizeOf_spec]
  omega

/-- **A witness of a premise the evaluator decides** is its result, which the evaluator offers. -/
theorem premiseValid_base {sites : Pattern} {bindings result : Bindings} {premise : Premise} {witness : Witness}
    (base : isBase premise = true) (valid : PremiseValid relEnv language sites bindings premise witness result) :
    witness = .base result ∧ result ∈ premiseStepWithEnv relEnv language bindings premise := by
  cases valid with
  | base _ found => exact ⟨rfl, found⟩
  | step endpoints _ _ _ => cases premise <;> simp_all [isBase, stepEndpoints]
  | forAll _ _ => simp [isBase] at base

/-- **A witness of a step premise** steps the source, instantiated scope-correctly at the premise's depth, to a
candidate that the target matches. -/
theorem premiseValid_step {sites : Pattern} {bindings result : Bindings} {premise : Premise} {source target : Pattern}
    {witness : Witness} (endpoints : stepEndpoints premise = some (source, target))
    (valid : PremiseValid relEnv language sites bindings premise witness result) :
    ∃ step candidate matched, witness = .premiseStep step candidate matched result ∧
      StepValid relEnv language (applyBindingsScoped sites bindings (stepDepth sites premise) source) step candidate ∧
      matched ∈ matchPattern target candidate ∧ mergeBindings bindings matched = some result := by
  cases valid with
  | base base _ => cases premise <;> simp_all [isBase, stepEndpoints]
  | step endpoints' stepped matched merged =>
      rw [endpoints] at endpoints'
      simp only [Option.some.injEq, Prod.mk.injEq] at endpoints'
      obtain ⟨rfl, rfl⟩ := endpoints'
      exact ⟨_, _, _, rfl, stepped, matched, merged⟩
  | forAll _ _ => simp [stepEndpoints] at endpoints

/-- **A witness of a quantified premise** keeps the bindings and holds the body at each element. -/
theorem premiseValid_forAll {sites : Pattern} {bindings result : Bindings} {collection parameter : String}
    {body : Premise} {witness : Witness}
    (valid : PremiseValid relEnv language sites bindings (.forAll collection parameter body) witness result) :
    result = bindings ∧ ∃ bodies kind elements, witness = .forAll bodies ∧
      bindings.lookup collection = some (.collection kind elements none) ∧
      ForAllValid relEnv language sites bindings parameter body elements bodies := by
  cases valid with
  | base base _ => simp [isBase] at base
  | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
  | forAll looked each => exact ⟨rfl, _, _, _, rfl, looked, each⟩

theorem forAllValid_mem {sites : Pattern} {bindings : Bindings} {parameter : String} {body : Premise} :
    ∀ {elements : List Pattern} {bodies : List Witness},
      ForAllValid relEnv language sites bindings parameter body elements bodies → ∀ element ∈ elements,
        ∃ witness ∈ bodies, ∃ result,
          PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result
  | _, _, .nil, _, inside => absurd inside List.not_mem_nil
  | _, _, .cons here later, element, inside => by
      rcases List.mem_cons.mp inside with rfl | inLater
      · exact ⟨_, List.mem_cons_self, _, here⟩
      · obtain ⟨witness, member, result, valid⟩ := forAllValid_mem later element inLater
        exact ⟨witness, List.mem_cons_of_mem _ member, result, valid⟩

theorem forAllValid_of {sites : Pattern} {bindings : Bindings} {parameter : String} {body : Premise} :
    ∀ {elements : List Pattern}, (∀ element ∈ elements, ∃ witness result,
      PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result) →
      ∃ bodies, ForAllValid relEnv language sites bindings parameter body elements bodies
  | [], _ => ⟨[], .nil⟩
  | element :: elements, each => by
      obtain ⟨witness, result, here⟩ := each element List.mem_cons_self
      obtain ⟨bodies, later⟩ := forAllValid_of fun other inside => each other (List.mem_cons_of_mem _ inside)
      exact ⟨witness :: bodies, .cons here later⟩

/-! ## What the witnesses establish -/

/-- Ordered arguments read alike under bindings that read alike at every name. -/
theorem instances_agree {first second : Bindings} : ∀ {arguments : List Pattern}, orderedList arguments = true →
    (∀ name, lookupOrFvar first name = lookupOrFvar second name) →
    arguments.map (applyBindings first) = arguments.map (applyBindings second)
  | [], _, _ => rfl
  | argument :: rest, shape, agree => by
      simp only [orderedList, Bool.and_eq_true] at shape
      rw [List.map_cons, List.map_cons, instance_agree argument shape.1 (fun name _ => agree name),
        instances_agree shape.2 agree]

/-- The names a query binds are the names of its arguments. -/
theorem arguments_keys : ∀ {arguments values : List Pattern} {seed extension : Bindings},
    orderedList arguments = true → extension ∈ matchRelationArgs seed arguments values →
    ∀ x v, (x, v) ∈ extension → x ∈ namesList arguments
  | [], [], _, _, _, matched, x, v, inside => by
      simp only [matchRelationArgs, List.mem_singleton] at matched
      subst matched
      exact absurd inside List.not_mem_nil
  | [], _ :: _, _, _, _, matched, _, _, _ => by simp [matchRelationArgs] at matched
  | _ :: _, [], _, _, _, matched, _, _, _ => by simp [matchRelationArgs] at matched
  | argument :: rest, value :: values, seed, extension, shape, matched, x, v, inside => by
      simp only [orderedList, Bool.and_eq_true] at shape
      simp only [matchRelationArgs, List.mem_flatMap] at matched
      obtain ⟨head, headMatched, remaining⟩ := matched
      split at remaining
      · simp at remaining
      · rename_i extended merged
        obtain ⟨tail, tailMatched, combined⟩ := List.mem_filterMap.mp remaining
        rcases List.mem_append.mp
            (Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection.merge_members combined inside) with inHead | inTail
        · simp only [namesList, List.mem_append]
          refine .inl ?_
          cases argument with
          | fvar name =>
              simp only [matchRelationArgument] at headMatched
              split at headMatched
              · split at headMatched
                · simp only [List.mem_singleton] at headMatched
                  subst headMatched
                  exact absurd inHead List.not_mem_nil
                · exact absurd headMatched List.not_mem_nil
              · simp only [List.mem_singleton] at headMatched
                subst headMatched
                simp only [List.mem_singleton, Prod.mk.injEq] at inHead
                simp [names, inHead.1]
          | _ =>
              simp only [matchRelationArgument] at headMatched
              exact (MatchesAndInstances.match_functional _ (matchPattern_sound headMatched)).2 x v inHead
        · simp only [namesList, List.mem_append]
          exact .inr (arguments_keys shape.2 tailMatched x v inTail)

/-- **What the premises' witnesses establish holds**, for any relation `S` holding of the steps they witness. -/
theorem premises_sound (dataRows : DataRows relEnv language)
    {S : Pattern → Pattern → Prop} (keeps : ∀ u v, isData u = true → S u v → isData v = true)
    {rests : List String} {bags : List (String × CollType)} {bound last : List String} {premises : List Premise}
    (flows : Flows rests bags bound premises last) {sites : Pattern} :
    ∀ {seed final : Bindings} {witnesses : List Witness},
      (∀ step, (∃ witness ∈ witnesses, StepWithin step witness) →
        ∀ u v, StepValid relEnv language u step v → S u v) →
      Covers seed bound → (∀ x v, (x, v) ∈ seed → x ∈ bound) → DataOn seed → Settled seed rests →
      BagSettled seed bags →
      PremisesValid relEnv language sites seed premises witnesses final →
      BindingsExtends seed final ∧ Covers final last ∧ (∀ x v, (x, v) ∈ final → x ∈ last) ∧ DataOn final ∧
        Hold relEnv language S sites DataOn final bound premises := by
  induction flows with
  | nil =>
    intro seed final witnesses _ covered keys values _ _ found
    cases found
    exact ⟨extends_refl _, covered, keys, values, trivial⟩
  | @query _ _ bound last relation arguments premises shape restsSettled _ ih =>
    intro seed final witnesses nested covered keys values settled bagsSettled found
    cases found with
    | @cons _ _ next _ _ _ witness rest head tail =>
      obtain ⟨rfl, asked⟩ := premiseValid_base rfl head
      obtain ⟨row, offered, extension, matched, merged⟩ := mem_query.mp asked
      have seedNext := fun name value held => mergeBindings_subsumed_left merged (x := name) (v := value) held
      have rowData := dataRows relation _ row offered
        (instanceList_data values arguments shape fun name member => settled name (restsSettled name member))
      have nextCovered : Covers next (bound ++ namesList arguments) := by
        intro name member
        rcases List.mem_append.mp member with before | here
        · exact covers_extends covered seedNext name before
        · exact arguments_binds shape matched seedNext
            (fun _ _ held => mergeBindings_subsumed_right merged held) name here
      have nextKeys : ∀ x v, (x, v) ∈ next → x ∈ bound ++ namesList arguments := by
        intro x v inside
        rcases List.mem_append.mp
            (Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection.merge_members merged inside) with inSeed | inExtension
        · exact List.mem_append_left _ (keys x v inSeed)
        · exact List.mem_append_right _ (arguments_keys shape matched x v inExtension)
      obtain ⟨nextFinal, finalCovered, finalKeys, finalData, hold⟩ := ih
        (fun step ⟨w, inside, within⟩ => nested step ⟨w, List.mem_cons_of_mem _ inside, within⟩) nextCovered
        nextKeys (DataOn.merge merged values (arguments_data shape rowData matched)) (settled.extends_ seedNext)
        (bagsSettled.extends_ seedNext) tail
      have seedFinal := extends_trans seedNext nextFinal
      have rowIs : arguments.map (applyBindings final) = row := arguments_sound shape rowData matched seedFinal
        (fun _ _ held => nextFinal _ _ (mergeBindings_subsumed_right merged held))
      subst rowIs
      refine ⟨seedFinal, finalCovered, finalKeys, finalData, ?_, hold⟩
      show _ ∈ queryRows relEnv language relation (arguments.map (applyBindings (restrict final bound)))
      rw [← instances_agree shape fun name => lookupOrFvar_point keys
        (fun _ member => lookup_of_extends covered seedFinal member) name]
      exact offered
  | @step _ _ bound last premise source target premises endpoints sourceCanonical targetShape restsSettled
      bagsWithin _ ih =>
    intro seed final witnesses nested covered keys values settled bagsSettled found
    cases found with
    | @cons _ _ next _ _ _ witness rest head tail =>
      obtain ⟨step, candidate, matched, rfl, stepped, matchedIn, merged⟩ := premiseValid_step endpoints head
      have seedNext := fun name value held => mergeBindings_subsumed_left merged (x := name) (v := value) held
      have sourceData : isData (applyBindingsScoped sites seed (stepDepth sites premise) source) = true :=
        Instantiation.scoped_data values sites _ source sourceCanonical
          (fun rest inside => settled rest (restsSettled rest (List.mem_append_left _ inside)))
          (fun pair inside => bagsSettled pair (bagsWithin pair inside))
      have related' := nested step ⟨_, List.mem_cons_self, .here⟩ _ _ stepped
      have candidateData := keeps _ _ sourceData related'
      have related := matchPattern_sound matchedIn
      obtain ⟨targetCovered, _⟩ := match_binds target targetShape related
      have nextCovered : Covers next (bound ++ names target) := by
        intro name member
        rcases List.mem_append.mp member with before | here
        · exact covers_extends covered seedNext name before
        · exact covers_extends targetCovered (fun _ _ held => mergeBindings_subsumed_right merged held) name here
      have nextKeys : ∀ x v, (x, v) ∈ next → x ∈ bound ++ names target := by
        intro x v inside
        rcases List.mem_append.mp
            (Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection.merge_members merged inside) with inSeed | inFound
        · exact List.mem_append_left _ (keys x v inSeed)
        · exact List.mem_append_right _ ((MatchesAndInstances.match_functional target related).2 x v inFound)
      obtain ⟨nextFinal, finalCovered, finalKeys, finalData, hold⟩ := ih
        (fun step' ⟨w, inside, within⟩ => nested step' ⟨w, List.mem_cons_of_mem _ inside, within⟩) nextCovered
        nextKeys (DataOn.merge merged values (match_data target targetShape candidateData related))
        (settled.extends_ seedNext) (bagsSettled.extends_ seedNext) tail
      have seedFinal := extends_trans seedNext nextFinal
      have sourceIs : applyBindingsScoped sites (restrict final bound) (stepDepth sites premise) source =
          applyBindingsScoped sites seed (stepDepth sites premise) source :=
        Instantiation.applyBindingsScoped_agree sites _ source fun name _ =>
          (lookupOrFvar_point keys (fun _ member => lookup_of_extends covered seedFinal member) name).symm
      have targetIs : applyBindings final target = candidate :=
        match_exact target targetShape candidateData related
          (extends_trans (fun _ _ held => mergeBindings_subsumed_right merged held) nextFinal)
      refine ⟨seedFinal, finalCovered, finalKeys, finalData, (premiseHolds_step endpoints).mpr ?_, ?_⟩
      · rw [sourceIs, targetIs]
        exact related'
      · rw [nextBound_step endpoints]
        exact hold
  | @fresh _ _ bound last condition premises termShape _ _ ih =>
    intro seed final witnesses nested covered keys values settled bagsSettled found
    cases found with
    | @cons _ _ next _ _ _ witness rest head tail =>
      obtain ⟨rfl, offered⟩ := premiseValid_base rfl head
      obtain ⟨rfl, holds⟩ := fresh_mem.mp offered
      obtain ⟨seedFinal, finalCovered, finalKeys, finalData, hold⟩ := ih
        (fun step ⟨w, inside, within⟩ => nested step ⟨w, List.mem_cons_of_mem _ inside, within⟩) covered keys
        values settled bagsSettled tail
      refine ⟨seedFinal, finalCovered, finalKeys, finalData, ?_, hold⟩
      exact freshHolds_agree termShape (fun name _ => lookupOrFvar_point keys
        (fun _ member => lookup_of_extends covered seedFinal member) name) holds
  | @forAll _ _ bound last inner collection parameter body premises _ _ ihBody ih =>
    intro seed final witnesses nested covered keys values settled bagsSettled found
    cases found with
    | @cons _ _ next _ _ _ witness rest head tail =>
      obtain ⟨nextIs, bodies, kind, elements, rfl, looked, each⟩ := premiseValid_forAll head
      subst next
      obtain ⟨seedFinal, finalCovered, finalKeys, finalData, hold⟩ := ih
        (fun step ⟨w, inside, within⟩ => nested step ⟨w, List.mem_cons_of_mem _ inside, within⟩) covered keys
        values settled bagsSettled tail
      have seedLooked := lookupOrFvar_of_lookup looked
      have collectionData : isData (.collection kind elements none) = true := by
        rw [← seedLooked]
        exact Instantiation.lookupOrFvar_data values collection
      refine ⟨seedFinal, finalCovered, finalKeys, finalData, ⟨kind, elements, ?_, fun element inside => ?_⟩, hold⟩
      · rw [← lookupOrFvar_point keys (fun _ member => lookup_of_extends covered seedFinal member)]
        exact seedLooked
      · obtain ⟨bodyWitness, member, result, valid⟩ := forAllValid_mem each element inside
        have elementData : isData element = true := by
          simp only [isData, Option.isNone_none, Bool.true_and] at collectionData
          exact isDataList_iff.mp collectionData element inside
        obtain ⟨above, -, -, resultData, bodyHold⟩ := ihBody
          (seed := bindParameter seed parameter element) (witnesses := [bodyWitness])
          (fun step ⟨w, inW, within⟩ => nested step ⟨.forAll bodies, List.mem_cons_self,
            .forAll (by rw [List.mem_singleton.mp inW]; exact member) within⟩)
          (bindParameter_covers covered parameter element) (bindParameter_keys keys parameter element)
          (bindParameter_data values parameter elementData)
          (bindParameter_settled settled parameter element) (bindParameter_bags bagsSettled parameter element)
          (.cons valid (.nil result))
        refine ⟨result, resultData, fun name nameInside => ?_, bodyHold.1⟩
        rw [← lookup_of_extends (bindParameter_covers covered parameter element) above
          (mem_scopeOf.mpr ((List.mem_cons.mp nameInside).imp id id)),
          lookupOrFvar_bindParameter, lookupOrFvar_bindParameter]
        split
        · rfl
        · rename_i differ
          exact lookup_of_extends covered seedFinal ((List.mem_cons.mp nameInside).resolve_left differ)

/-- **What holds has witnesses**, when the steps it states are reference steps. -/
theorem premises_complete {good : Bindings → Prop} (witness : Bindings)
    {rests : List String} {bags : List (String × CollType)} {bound last : List String} (settled : Settled witness rests)
    (restsBound : ∀ rest ∈ rests, rest ∈ bound)
    {premises : List Premise} (flows : Flows rests bags bound premises last) {sites : Pattern} :
    ∀ {seed : Bindings}, Covers seed bound → (∀ x v, (x, v) ∈ seed → x ∈ bound) →
      BindingsValued seed (lookupOrFvar witness) →
      Hold relEnv language (Step relEnv language) sites good witness bound premises →
      ∃ final witnesses, PremisesValid relEnv language sites seed premises witnesses final ∧
        Covers final last ∧ (∀ x v, (x, v) ∈ final → x ∈ last) ∧ BindingsValued final (lookupOrFvar witness) := by
  induction flows generalizing witness with
  | nil =>
    intro seed covered keys valued _
    exact ⟨seed, [], .nil seed, covered, keys, valued⟩
  | @query _ _ bound last relation arguments premises shape restsSettled _ ih =>
    intro seed covered keys valued hold
    have offered : arguments.map (applyBindings witness) ∈
        queryRows relEnv language relation (arguments.map (applyBindings seed)) := by
      rw [instances_agree shape fun name => lookupOrFvar_point keys
        (fun _ member => lookup_of_valued valued covered member) name]
      exact hold.1
    obtain ⟨extension, matched, extensionValued⟩ := arguments_complete witness valued shape
      fun name member => settled name (restsSettled name member)
    obtain ⟨next, merged, nextValued⟩ := mergeBindings_some_of_valued seed extension _ valued extensionValued
    have seedNext : BindingsExtends seed next := fun _ _ held => mergeBindings_subsumed_left merged held
    have nextCovered : Covers next (bound ++ namesList arguments) := by
      intro name member
      rcases List.mem_append.mp member with before | here
      · exact covers_extends covered seedNext name before
      · exact arguments_binds shape matched seedNext
          (fun _ _ held => mergeBindings_subsumed_right merged held) name here
    have nextKeys : ∀ x v, (x, v) ∈ next → x ∈ bound ++ namesList arguments := by
      intro x v inside
      rcases List.mem_append.mp
          (Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection.merge_members merged inside) with inSeed | inExtension
      · exact List.mem_append_left _ (keys x v inSeed)
      · exact List.mem_append_right _ (arguments_keys shape matched x v inExtension)
    obtain ⟨final, witnesses, found, finalCovered, finalKeys, finalValued⟩ := ih witness settled
      (fun rest inside => List.mem_append_left _ (restsBound rest inside)) nextCovered nextKeys nextValued hold.2
    exact ⟨final, .base next :: witnesses, .cons (.base rfl (mem_query.mpr ⟨_, offered, extension, matched, merged⟩))
      found, finalCovered, finalKeys, finalValued⟩
  | @step _ _ bound last premise source target premises endpoints sourceCanonical targetShape restsSettled
      bagsWithin _ ih =>
    intro seed covered keys valued hold
    have sourceIs : applyBindingsScoped sites seed (stepDepth sites premise) source =
        applyBindingsScoped sites (restrict witness bound) (stepDepth sites premise) source :=
      Instantiation.applyBindingsScoped_agree sites _ source fun name _ =>
        lookupOrFvar_point keys (fun _ member => lookup_of_valued valued covered member) name
    obtain ⟨step, stepped⟩ := (premiseHolds_step endpoints).mp hold.1
    obtain ⟨found, related, foundValued⟩ := match_complete witness target targetShape fun rest member =>
      settled rest (restsSettled rest (List.mem_append_right _ member))
    obtain ⟨next, merged, nextValued⟩ := mergeBindings_some_of_valued seed found _ valued foundValued
    have seedNext : BindingsExtends seed next := fun _ _ held => mergeBindings_subsumed_left merged held
    have nextCovered : Covers next (bound ++ names target) := by
      intro name member
      rcases List.mem_append.mp member with before | here
      · exact covers_extends covered seedNext name before
      · exact covers_extends (match_binds target targetShape related).1
          (fun _ _ held => mergeBindings_subsumed_right merged held) name here
    have nextKeys : ∀ x v, (x, v) ∈ next → x ∈ bound ++ names target := by
      intro x v inside
      rcases List.mem_append.mp
          (Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection.merge_members merged inside) with inSeed | inFound
      · exact List.mem_append_left _ (keys x v inSeed)
      · exact List.mem_append_right _ ((MatchesAndInstances.match_functional target related).2 x v inFound)
    obtain ⟨final, witnesses, rest, finalCovered, finalKeys, finalValued⟩ := ih witness settled
      (fun rest inside => List.mem_append_left _ (restsBound rest inside)) nextCovered nextKeys nextValued
      (by rw [← nextBound_step endpoints]; exact hold.2)
    refine ⟨final, .premiseStep step _ found next :: witnesses,
      .cons (.step endpoints (sourceIs ▸ stepped) (matchPattern_iff_matchRel.mpr related) merged) rest,
      finalCovered, finalKeys, finalValued⟩
  | @fresh _ _ bound last condition premises termShape _ _ ih =>
    intro seed covered keys valued hold
    obtain ⟨final, witnesses, found, finalCovered, finalKeys, finalValued⟩ :=
      ih witness settled restsBound covered keys valued hold.2
    refine ⟨final, .base seed :: witnesses, .cons (.base rfl (fresh_mem.mpr ⟨rfl, ?_⟩)) found, finalCovered,
      finalKeys, finalValued⟩
    exact freshHolds_agree termShape (fun name _ => (lookupOrFvar_point keys
      (fun _ member => lookup_of_valued valued covered member) name).symm) hold.1
  | @forAll rests' _ bound last inner collection parameter body premises _ _ ihBody ih =>
    intro seed covered keys valued hold
    obtain ⟨kind, elements, looked, each⟩ := hold.1
    have seedLooked : lookupOrFvar seed collection = .collection kind elements none :=
      (lookupOrFvar_point keys (fun _ member => lookup_of_valued valued covered member) collection).trans looked
    obtain ⟨bodies, forAllValid⟩ := forAllValid_of (relEnv := relEnv) (language := language) (sites := sites)
      (bindings := seed) (parameter := parameter) (body := body) (elements := elements) fun element inside => by
        obtain ⟨result, -, agree, bodyHolds⟩ := each element inside
        have resultSettled : Settled result (rests'.filter (· ≠ parameter)) := fun rest restInside => by
          obtain ⟨inRests, differ⟩ := List.mem_filter.mp restInside
          have differ : rest ≠ parameter := by simpa using differ
          obtain ⟨tail, found⟩ := settled rest inRests
          have value : lookupOrFvar witness rest = .collection .vec tail none := by
            simp [lookupOrFvar, applyBindings, found]
          have atResult := agree rest (List.mem_cons_of_mem _ (restsBound rest inRests))
          rw [lookupOrFvar_bindParameter, if_neg differ, value] at atResult
          exact ⟨tail, CollectionMatching.find_of_lookup_collection atResult⟩
        have bodyValued : BindingsValued (bindParameter seed parameter element) (lookupOrFvar result) := by
          intro x v inside
          simp only [bindParameter, List.mem_cons, Prod.mk.injEq, List.mem_filter] at inside
          rcases inside with ⟨rfl, rfl⟩ | ⟨inSeed, notParameter⟩
          · rw [agree x List.mem_cons_self, lookupOrFvar_bindParameter, if_pos rfl]
          · have differ : x ≠ parameter := by simpa using notParameter
            rw [agree x (List.mem_cons_of_mem _ (keys x v inSeed)), lookupOrFvar_bindParameter, if_neg differ]
            exact valued x v inSeed
        obtain ⟨final, witnesses, found, -, -, -⟩ := ihBody result resultSettled
          (fun rest inside => mem_scopeOf.mpr (.inr (restsBound rest (List.mem_filter.mp inside).1)))
          (bindParameter_covers covered parameter element) (bindParameter_keys keys parameter element) bodyValued
          ⟨bodyHolds, trivial⟩
        cases found with
        | cons here rest =>
            cases rest
            exact ⟨_, _, here⟩
    obtain ⟨final, witnesses, found, finalCovered, finalKeys, finalValued⟩ :=
      ih witness settled restsBound covered keys valued hold.2
    exact ⟨final, .forAll bodies :: witnesses, .cons (.forAll (lookup_of_lookupOrFvar seedLooked) forAllValid) found,
      finalCovered, finalKeys, finalValued⟩

/-! ## Instances of a triple -/

variable (relEnv language) in
/-- **An instance of a triple**: the left side matches the source, the premises have witnesses at the triple's
binding sites, and the right side instantiated scope-correctly by what they bound is the target. -/
def TripleAt (left right : Pattern) (premises : List Premise) (s t : Pattern) : Prop :=
  ∃ initial final witnesses, MatchRel left s initial ∧
    PremisesValid relEnv language (captureSitesOf left premises) initial premises witnesses final ∧
      applyBindingsScoped (captureSitesOf left premises) final 0 right = t

/-- **A reference step is an instance of one rule's triple.** -/
theorem step_iff {s t : Pattern} :
    Step relEnv language s t ↔
      ∃ rule ∈ language.rewrites, TripleAt relEnv language rule.left rule.right rule.premises s t := by
  constructor
  · rintro ⟨witness, valid⟩
    cases valid with
    | rule found matched passed =>
      rename_i index rule initial final witnesses
      rw [matchPatternForRule_eq_syntactic] at matched
      exact ⟨rule, List.mem_iff_getElem?.mpr ⟨index, found⟩, initial, final, witnesses, matchPattern_sound matched,
        passed, rfl⟩
  · rintro ⟨rule, member, initial, final, witnesses, matched, passed, rfl⟩
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    exact ⟨_, .rule found (by rw [matchPatternForRule_eq_syntactic]; exact matchPattern_iff_matchRel.mpr matched)
      passed⟩

/-- **A triple instance from data passes its premises at data bindings, and its target is data**, when the steps its
witnesses take keep data. -/
theorem triple_data (dataRows : DataRows relEnv language)
    {left right : Pattern} {premises : List Premise} (shape : TripleShape left right premises)
    {S : Pattern → Pattern → Prop} (keeps : ∀ u v, isData u = true → S u v → isData v = true)
    {s : Pattern} (data : isData s = true) {initial final : Bindings} {witnesses : List Witness}
    (nested : ∀ step, (∃ witness ∈ witnesses, StepWithin step witness) →
      ∀ u v, StepValid relEnv language u step v → S u v)
    (matched : MatchRel left s initial)
    (passed : PremisesValid relEnv language (captureSitesOf left premises) initial premises witnesses final) :
    BindingsExtends initial final ∧ DataOn final ∧
      Hold relEnv language S (captureSitesOf left premises) DataOn final (names left) premises ∧
      isData (applyBindingsScoped (captureSitesOf left premises) final 0 right) = true := by
  obtain ⟨last, flows⟩ := shape.flows
  obtain ⟨covered, settled, bags⟩ := MatchesAndInstances.match_binds left matched
  obtain ⟨above, -, -, finalData, hold⟩ := premises_sound dataRows keeps flows nested covered
    (MatchesAndInstances.match_functional left matched).2 (MatchesAndInstances.match_data left data matched) settled
    bags passed
  exact ⟨above, finalData, hold, Instantiation.scoped_data finalData _ 0 right shape.rightCanonical
    (fun rest member => (settled.extends_ above) rest (shape.restsWithin rest member))
    (fun pair member => (bags.extends_ above) pair (shape.bagsWithin pair member))⟩

/-- **What a triple instance binds is what its left side and premises bind.** -/
theorem triple_keys (dataRows : DataRows relEnv language)
    {left right : Pattern} {premises : List Premise} (shape : TripleShape left right premises)
    {S : Pattern → Pattern → Prop} (keeps : ∀ u v, isData u = true → S u v → isData v = true)
    {s : Pattern} (data : isData s = true) {initial final : Bindings} {witnesses : List Witness}
    (nested : ∀ step, (∃ witness ∈ witnesses, StepWithin step witness) →
      ∀ u v, StepValid relEnv language u step v → S u v)
    (matched : MatchRel left s initial)
    (passed : PremisesValid relEnv language (captureSitesOf left premises) initial premises witnesses final) :
    ∀ x v, (x, v) ∈ final → x ∈ boundAfter (names left) premises := by
  obtain ⟨last, flows⟩ := shape.flows
  obtain ⟨covered, settled, bags⟩ := MatchesAndInstances.match_binds left matched
  obtain ⟨-, -, finalKeys, -, -⟩ := premises_sound dataRows keeps flows nested covered
    (MatchesAndInstances.match_functional left matched).2 (MatchesAndInstances.match_data left data matched) settled
    bags passed
  rw [← Flows.last_eq flows]
  exact finalKeys

/-- **Steps of data are data**, by the size of their witnesses. -/
theorem stepValid_data (dataRows : DataRows relEnv language)
    (shapes : ∀ rule ∈ language.rewrites, TripleShape rule.left rule.right rule.premises) :
    ∀ (n : ℕ) {witness : Witness} {s t : Pattern}, sizeOf witness < n → isData s = true →
      StepValid relEnv language s witness t → isData t = true
  | 0, _, _, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | n + 1, _, _, _, small, data, valid => by
      cases valid with
      | rule found matched passed =>
        rename_i index rule initial final witnesses
        rw [matchPatternForRule_eq_syntactic] at matched
        exact (triple_data dataRows (shapes rule (List.mem_iff_getElem?.mpr ⟨index, found⟩))
          (S := fun u v => ∃ w, sizeOf w < n ∧ StepValid relEnv language u w v)
          (fun _ _ uData ⟨_, wSmall, wValid⟩ => stepValid_data dataRows shapes n wSmall uData wValid) data
          (fun step inside u v stepped =>
            ⟨step, by have := nested_lt (index := index) (initial := initial) inside; omega, stepped⟩)
          (matchPattern_sound matched) passed).2.2.2

theorem step_data (dataRows : DataRows relEnv language)
    (shapes : ∀ rule ∈ language.rewrites, TripleShape rule.left rule.right rule.premises) {s t : Pattern}
    (data : isData s = true) (stepped : Step relEnv language s t) : isData t = true := by
  obtain ⟨witness, valid⟩ := stepped
  exact stepValid_data dataRows shapes (sizeOf witness + 1) (Nat.lt_succ_self _) data valid

end Mettapedia.GSLT.Compilation.Uniform.StepPremises

#print axioms Mettapedia.GSLT.Compilation.Uniform.StepPremises.step_iff
#print axioms Mettapedia.GSLT.Compilation.Uniform.StepPremises.premises_sound
#print axioms Mettapedia.GSLT.Compilation.Uniform.StepPremises.premises_complete
#print axioms Mettapedia.GSLT.Compilation.Uniform.StepPremises.step_data
