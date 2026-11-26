import Mettapedia.GSLT.Compilation.Uniform.OrderedMatching

/-!
# Rules whose premises query relations are instances over a graph

A relation premise is evaluated by the engine at the bindings found so far, and may bind
its outputs. This module gives that evaluation an order-free reading, which a compiler
can lower: at data, a step is an instance of one rule whose queried rows are rows of the
relations (`step_iff_instance`). Patterns are ordered (`OrderedMatching.ordered`):
constructors and vectors, a rest allowed.

Three conditions make the readings agree, and none mentions a compiler or a language:

* `Moded`: which rows answer a query depends only on its input positions, so a row
  answers a query exactly when it is a row (it answers itself) and agrees on the inputs.
* `DataRows`: a query asked with data is answered with data.
* `Flows`: each input position is bound by the left side or an earlier premise, and a
  rest in a query is a rest of the left side.

Controls: the successor relation is moded and answers data (`Controls.successor_moded`,
`Controls.successor_data`). A relation that looks at its output slot is not moded
(`Controls.peek_not_moded`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.QueryPremises

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open OrderedMatching

/-! ## One query -/

theorem argument_sound {seed extension upper : Bindings} {argument value : Pattern}
    (shape : ordered argument = true) (data : isData value = true)
    (matched : extension ∈ matchRelationArgument seed argument value)
    (seedBelow : BindingsExtends seed upper) (below : BindingsExtends extension upper) :
    applyBindings upper argument = value := by
  cases argument with
  | fvar name =>
    simp only [matchRelationArgument, Bindings.lookup] at matched
    cases held : seed.find? (·.1 == name) with
    | none =>
      simp only [held, Option.map_none, List.mem_singleton] at matched
      subst matched
      simp [applyBindings, below name value (by simp)]
    | some entry =>
      simp only [held, Option.map_some] at matched
      split at matched
      · rename_i same
        rw [find_named held] at held
        simp [applyBindings, seedBelow name _ held, same]
      · simp at matched
  | _ =>
    simp only [matchRelationArgument] at matched
    exact match_exact _ shape data (matchPattern_sound matched) below

theorem argument_binds {seed extension upper : Bindings} {argument value : Pattern}
    (shape : ordered argument = true) (matched : extension ∈ matchRelationArgument seed argument value)
    (seedBelow : BindingsExtends seed upper) (below : BindingsExtends extension upper) :
    Covers upper (names argument) := by
  cases argument with
  | fvar name =>
    intro other member
    simp only [names, List.mem_singleton] at member
    subst member
    simp only [matchRelationArgument, Bindings.lookup] at matched
    cases held : seed.find? (·.1 == other) with
    | none =>
      simp only [held, Option.map_none, List.mem_singleton] at matched
      subst matched
      exact ⟨value, below other value (by simp)⟩
    | some entry =>
      rw [find_named held] at held
      exact ⟨entry.2, seedBelow other _ held⟩
  | _ =>
    simp only [matchRelationArgument] at matched
    exact covers_extends (match_binds _ shape (matchPattern_sound matched)).1 below

theorem argument_data {seed extension : Bindings} {argument value : Pattern}
    (shape : ordered argument = true) (data : isData value = true)
    (matched : extension ∈ matchRelationArgument seed argument value) : DataOn extension := by
  cases argument with
  | fvar name =>
    simp only [matchRelationArgument, Bindings.lookup] at matched
    cases held : seed.find? (·.1 == name) with
    | none =>
      simp only [held, Option.map_none, List.mem_singleton] at matched
      subst matched
      exact dataOn_single data
    | some entry =>
      simp only [held, Option.map_some] at matched
      split at matched
      · simp only [List.mem_singleton] at matched
        subst matched
        intro _ _ found
        simp at found
      · simp at matched
  | _ =>
    simp only [matchRelationArgument] at matched
    exact match_data _ shape data (matchPattern_sound matched)

theorem arguments_sound : ∀ {arguments values : List Pattern} {seed extension upper : Bindings},
    orderedList arguments = true → isDataList values = true →
    extension ∈ matchRelationArgs seed arguments values →
    BindingsExtends seed upper → BindingsExtends extension upper →
    arguments.map (applyBindings upper) = values
  | [], [], _, _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, matched, _, _ => by simp [matchRelationArgs] at matched
  | _ :: _, [], _, _, _, _, _, matched, _, _ => by simp [matchRelationArgs] at matched
  | argument :: rest, value :: values, seed, extension, upper, shape, data, matched, seedBelow, below => by
      simp only [orderedList, Bool.and_eq_true] at shape
      simp only [isDataList, Bool.and_eq_true] at data
      simp only [matchRelationArgs, List.mem_flatMap] at matched
      obtain ⟨head, headMatched, remaining⟩ := matched
      split at remaining
      · simp at remaining
      · rename_i extended merged
        obtain ⟨tail, tailMatched, combined⟩ := List.mem_filterMap.mp remaining
        have headBelow : BindingsExtends head upper :=
          fun name held found => below name held (mergeBindings_subsumed_left combined found)
        have tailBelow : BindingsExtends tail upper :=
          fun name held found => below name held (mergeBindings_subsumed_right combined found)
        rw [List.map_cons, argument_sound shape.1 data.1 headMatched seedBelow headBelow,
          arguments_sound shape.2 data.2 tailMatched (extends_merge merged seedBelow headBelow) tailBelow]

/-- After a query every variable of its arguments is bound. -/
theorem arguments_binds : ∀ {arguments values : List Pattern} {seed extension upper : Bindings},
    orderedList arguments = true → extension ∈ matchRelationArgs seed arguments values →
    BindingsExtends seed upper → BindingsExtends extension upper → Covers upper (namesList arguments)
  | [], _, _, _, _, _, _, _, _ => by simp [namesList, Covers]
  | _ :: _, [], _, _, _, _, matched, _, _ => by simp [matchRelationArgs] at matched
  | argument :: rest, value :: values, seed, extension, upper, shape, matched, seedBelow, below => by
      simp only [orderedList, Bool.and_eq_true] at shape
      simp only [matchRelationArgs, List.mem_flatMap] at matched
      obtain ⟨head, headMatched, remaining⟩ := matched
      split at remaining
      · simp at remaining
      · rename_i extended merged
        obtain ⟨tail, tailMatched, combined⟩ := List.mem_filterMap.mp remaining
        have headBelow : BindingsExtends head upper :=
          fun name held found => below name held (mergeBindings_subsumed_left combined found)
        have tailBelow : BindingsExtends tail upper :=
          fun name held found => below name held (mergeBindings_subsumed_right combined found)
        intro name member
        simp only [namesList, List.mem_append] at member
        rcases member with here | later
        · exact argument_binds shape.1 headMatched seedBelow headBelow name here
        · exact arguments_binds shape.2 tailMatched (extends_merge merged seedBelow headBelow) tailBelow name later

theorem arguments_data : ∀ {arguments values : List Pattern} {seed extension : Bindings},
    orderedList arguments = true → isDataList values = true →
    extension ∈ matchRelationArgs seed arguments values → DataOn extension
  | [], [], _, _, _, _, matched => by
      simp only [matchRelationArgs, List.mem_singleton] at matched
      subst matched
      intro _ _ found
      simp at found
  | [], _ :: _, _, _, _, _, matched => by simp [matchRelationArgs] at matched
  | _ :: _, [], _, _, _, _, matched => by simp [matchRelationArgs] at matched
  | argument :: rest, value :: values, seed, extension, shape, data, matched => by
      simp only [orderedList, Bool.and_eq_true] at shape
      simp only [isDataList, Bool.and_eq_true] at data
      simp only [matchRelationArgs, List.mem_flatMap] at matched
      obtain ⟨head, headMatched, remaining⟩ := matched
      split at remaining
      · simp at remaining
      · obtain ⟨tail, tailMatched, combined⟩ := List.mem_filterMap.mp remaining
        exact DataOn.merge combined (argument_data shape.1 data.1 headMatched) (arguments_data shape.2 data.2 tailMatched)

theorem argument_complete (witness : Bindings) {seed : Bindings}
    (valued : BindingsValued seed (lookupOrFvar witness)) {argument : Pattern}
    (shape : ordered argument = true) (settled : Settled witness (restNames argument)) :
    ∃ extension ∈ matchRelationArgument seed argument (applyBindings witness argument),
      BindingsValued extension (lookupOrFvar witness) := by
  cases argument with
  | fvar name =>
    cases held : seed.find? (·.1 == name) with
    | none =>
      refine ⟨[(name, applyBindings witness (.fvar name))], by simp [matchRelationArgument, Bindings.lookup, held], ?_⟩
      intro key value member
      simp only [List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      rfl
    | some entry =>
      have same : entry.2 = applyBindings witness (.fvar name) :=
        valued name entry.2 (List.mem_of_find?_eq_some (held.trans (congrArg some (find_named held))))
      exact ⟨[], by simp [matchRelationArgument, Bindings.lookup, held, same],
        fun _ _ member => nomatch member⟩
  | _ =>
    obtain ⟨extension, matched, extensionValued⟩ := match_complete witness _ shape settled
    exact ⟨extension, by simpa only [matchRelationArgument] using matchPattern_iff_matchRel.mpr matched,
      extensionValued⟩

theorem arguments_complete (witness : Bindings) : ∀ {arguments : List Pattern} {seed : Bindings},
    BindingsValued seed (lookupOrFvar witness) → orderedList arguments = true →
    Settled witness (restNamesList arguments) →
    ∃ extension ∈ matchRelationArgs seed arguments (arguments.map (applyBindings witness)),
      BindingsValued extension (lookupOrFvar witness)
  | [], _, _, _, _ => ⟨[], by simp [matchRelationArgs], fun _ _ member => nomatch member⟩
  | argument :: rest, seed, valued, shape, settled => by
      simp only [orderedList, Bool.and_eq_true] at shape
      obtain ⟨head, headMatched, headValued⟩ := argument_complete witness valued shape.1
        fun name member => settled name (by simp [restNamesList, member])
      obtain ⟨extended, merged, extendedValued⟩ := mergeBindings_some_of_valued seed head _ valued headValued
      obtain ⟨tail, tailMatched, tailValued⟩ := arguments_complete witness extendedValued shape.2
        fun name member => settled name (by simp [restNamesList, member])
      obtain ⟨combined, joined, combinedValued⟩ := mergeBindings_some_of_valued head tail _ headValued tailValued
      refine ⟨combined, ?_, combinedValued⟩
      simp only [List.map_cons, matchRelationArgs, List.mem_flatMap]
      refine ⟨head, headMatched, ?_⟩
      simp only [merged, List.mem_filterMap]
      exact ⟨tail, tailMatched, joined⟩

/-! ## Ordered premises -/

/-- The rows the engine offers to a query. -/
def queryRows (relEnv : RelationEnv) (language : LanguageDef) (relation : String) (asked : List Pattern) :
    List (List Pattern) :=
  builtinRelationTuples language relation asked ++ relEnv.tuples relation asked

/-- **The answers depend on the inputs alone.** -/
def Moded (relEnv : RelationEnv) (language : LanguageDef) (inputs : String → ℕ → Bool) : Prop :=
  ∀ relation asked row, asked.length = row.length →
    (∀ index, inputs relation index = true → asked[index]? = row[index]?) →
    (row ∈ queryRows relEnv language relation asked ↔ row ∈ queryRows relEnv language relation row)

/-- **A query asked with data is answered with data.** -/
def DataRows (relEnv : RelationEnv) (language : LanguageDef) : Prop :=
  ∀ relation asked row, row ∈ queryRows relEnv language relation asked →
    isDataList asked = true → isDataList row = true

/-- **Inputs are bound when asked**, and a rest in a query is one of `settled`; the last
index holds what is bound at the end. -/
inductive Flows (inputs : String → ℕ → Bool) (settled : List String) :
    List String → List Premise → List String → Prop
  | nil {bound : List String} : Flows inputs settled bound [] bound
  | query {bound last : List String} {relation : String} {arguments : List Pattern} {premises : List Premise} :
      orderedList arguments = true →
      (∀ index argument, arguments[index]? = some argument → inputs relation index = true →
        ∀ name ∈ names argument, name ∈ bound) →
      (∀ rest ∈ restNamesList arguments, rest ∈ settled) →
      Flows inputs settled (bound ++ namesList arguments) premises last →
      Flows inputs settled bound (.relationQuery relation arguments :: premises) last

/-- Every queried row is a row of its relation. -/
def Holds (relEnv : RelationEnv) (language : LanguageDef) (bindings : Bindings) (premises : List Premise) : Prop :=
  ∀ relation arguments, Premise.relationQuery relation arguments ∈ premises →
    arguments.map (applyBindings bindings) ∈
      queryRows relEnv language relation (arguments.map (applyBindings bindings))

theorem Flows.noncontextual {inputs : String → ℕ → Bool} {settled bound last : List String}
    {premises : List Premise} (flows : Flows inputs settled bound premises last) : NoncontextualPremises premises := by
  induction flows with
  | nil => exact .nil
  | query _ _ _ _ ih => exact .relationQuery ih

theorem mem_premises_cons (relEnv : RelationEnv) (language : LanguageDef) (premise : Premise)
    (premises : List Premise) (seed final : Bindings) :
    final ∈ applyPremisesWithEnv relEnv language (premise :: premises) seed ↔
      ∃ next ∈ premiseStepWithEnv relEnv language seed premise,
        final ∈ applyPremisesWithEnv relEnv language premises next := by
  have split : ∀ (rest : List Premise) (start : List Bindings),
      rest.foldl (fun found p => found.flatMap fun b => premiseStepWithEnv relEnv language b p) start =
        start.flatMap fun b => applyPremisesWithEnv relEnv language rest b := by
    intro rest
    induction rest with
    | nil => intro start; simp [applyPremisesWithEnv]
    | cons head tail ih =>
      intro start
      have one : ∀ b, applyPremisesWithEnv relEnv language (head :: tail) b =
          (premiseStepWithEnv relEnv language b head).flatMap fun c => applyPremisesWithEnv relEnv language tail c := by
        intro b
        rw [applyPremisesWithEnv, List.foldl_cons, ih]
        simp
      rw [List.foldl_cons, ih, List.flatMap_assoc]
      simp only [one]
  rw [applyPremisesWithEnv, List.foldl_cons, split]
  simp

theorem mem_query {relEnv : RelationEnv} {language : LanguageDef} {seed next : Bindings} {relation : String}
    {arguments : List Pattern} :
    next ∈ premiseStepWithEnv relEnv language seed (.relationQuery relation arguments) ↔
      ∃ row ∈ queryRows relEnv language relation (arguments.map (applyBindings seed)),
        ∃ extension ∈ matchRelationArgs seed arguments row, mergeBindings seed extension = some next := by
  simp [premiseStepWithEnv, relationQueryStep, queryRows, List.mem_flatMap, List.mem_filterMap, exists_or,
    or_and_right]

/-- The input positions of a query are unchanged by what is bound later. -/
theorem inputs_agree {inputs : String → ℕ → Bool} {bound : List String} {relation : String}
    {arguments : List Pattern} (shape : orderedList arguments = true)
    (boundInputs : ∀ index argument, arguments[index]? = some argument → inputs relation index = true →
      ∀ name ∈ names argument, name ∈ bound)
    {first second : Bindings} (agree : ∀ name ∈ bound, lookupOrFvar first name = lookupOrFvar second name)
    (index : ℕ) (input : inputs relation index = true) :
    (arguments.map (applyBindings first))[index]? = (arguments.map (applyBindings second))[index]? := by
  simp only [List.getElem?_map]
  cases found : arguments[index]? with
  | none => rfl
  | some argument =>
    simp only [Option.map_some]
    exact congrArg some (instance_agree argument (orderedList_iff.mp shape _ (List.mem_of_getElem? found))
      fun name member => agree name (boundInputs index argument found input name member))

variable {relEnv : RelationEnv} {language : LanguageDef} {inputs : String → ℕ → Bool}

/-- What the engine finds holds in the relations. -/
theorem premises_sound (moded : Moded relEnv language inputs) (dataRows : DataRows relEnv language)
    {rests bound last : List String} {premises : List Premise} (flows : Flows inputs rests bound premises last) :
    ∀ {seed final : Bindings}, Covers seed bound → DataOn seed → Settled seed rests →
      final ∈ applyPremisesWithEnv relEnv language premises seed →
      BindingsExtends seed final ∧ Covers final last ∧ Holds relEnv language final premises := by
  induction flows with
  | nil =>
    intro seed final covered _ _ found
    obtain rfl : final = seed := by simpa [applyPremisesWithEnv] using found
    exact ⟨extends_refl final, covered, fun _ _ member => nomatch member⟩
  | @query bound last relation arguments premises shape boundInputs restsSettled _ ih =>
    intro seed final covered values settled found
    obtain ⟨next, asked, remaining⟩ := (mem_premises_cons ..).mp found
    obtain ⟨row, offered, extension, matched, merged⟩ := mem_query.mp asked
    have seedNext : BindingsExtends seed next := fun _ _ held => mergeBindings_subsumed_left merged held
    have rowData := dataRows relation _ row offered
      (instanceList_data values arguments shape fun name member => settled name (restsSettled name member))
    have nextCovered : Covers next (bound ++ namesList arguments) := by
      intro name member
      rcases List.mem_append.mp member with before | here
      · exact covers_extends covered seedNext name before
      · exact arguments_binds shape matched seedNext
          (fun _ _ held => mergeBindings_subsumed_right merged held) name here
    obtain ⟨nextFinal, finalCovered, holds⟩ := ih nextCovered
      (DataOn.merge merged values (arguments_data shape rowData matched)) (settled.extends_ seedNext) remaining
    have seedFinal := extends_trans seedNext nextFinal
    have rowIs : arguments.map (applyBindings final) = row := arguments_sound shape rowData matched seedFinal
      (fun _ _ held => nextFinal _ _ (mergeBindings_subsumed_right merged held))
    subst rowIs
    refine ⟨seedFinal, finalCovered, fun other others member => ?_⟩
    rcases List.mem_cons.mp member with here | later
    · cases here
      exact (moded relation _ _ (by simp)
        (inputs_agree shape boundInputs fun _ member => lookup_of_extends covered seedFinal member)).mp offered
    · exact holds other others later

/-- What holds in the relations is found by the engine. -/
theorem premises_complete (moded : Moded relEnv language inputs) (witness : Bindings)
    {rests bound last : List String} (settled : Settled witness rests)
    {premises : List Premise} (flows : Flows inputs rests bound premises last) :
    ∀ {seed : Bindings}, Covers seed bound → BindingsValued seed (lookupOrFvar witness) →
      Holds relEnv language witness premises →
      ∃ final ∈ applyPremisesWithEnv relEnv language premises seed,
        Covers final last ∧ BindingsValued final (lookupOrFvar witness) := by
  induction flows with
  | nil =>
    intro seed covered valued _
    exact ⟨seed, by simp [applyPremisesWithEnv], covered, valued⟩
  | @query bound last relation arguments premises shape boundInputs restsSettled _ ih =>
    intro seed covered valued holds
    have offered := (moded relation (arguments.map (applyBindings seed)) (arguments.map (applyBindings witness))
      (by simp) (inputs_agree shape boundInputs fun _ member => lookup_of_valued valued covered member)).mpr
      (holds relation arguments (List.mem_cons_self ..))
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
    obtain ⟨final, found, finalCovered, finalValued⟩ := ih nextCovered nextValued
      (fun other others member => holds other others (List.mem_cons_of_mem _ member))
    exact ⟨final, (mem_premises_cons ..).mpr
      ⟨next, mem_query.mpr ⟨_, offered, extension, matched, merged⟩, found⟩, finalCovered, finalValued⟩

/-! ## A step is an instance -/

/-- A rule of ordered patterns whose premises are queries with bound inputs. -/
structure QueryRule (inputs : String → ℕ → Bool) (rule : RewriteRule) : Prop where
  left : ordered rule.left = true
  right : ordered rule.right = true
  aligned : ruleDepthAligned rule = true
  flows : ∃ last, Flows inputs (restNames rule.left) (names rule.left) rule.premises last ∧
    ∀ name ∈ names rule.right, name ∈ last

/-- **At data, a step is an instance of one rule whose queried rows are in the relations.** -/
theorem step_iff_instance (moded : Moded relEnv language inputs) (dataRows : DataRows relEnv language)
    (queryRules : ∀ rule ∈ language.rewrites, QueryRule inputs rule) {source : Pattern}
    (data : isData source = true) (target : Pattern) :
    Step (engineBasePremises relEnv) language source target ↔
      ∃ rule ∈ language.rewrites, ∃ bindings : Bindings,
        applyBindings bindings rule.left = source ∧ applyBindings bindings rule.right = target ∧
          Holds relEnv language bindings rule.premises := by
  rw [step_iff_rootStep_of_noncontextualRules fun rule member => by
    obtain ⟨_, flows, _⟩ := (queryRules rule member).flows
    exact flows.noncontextual]
  constructor
  · rintro ⟨rule, member, initial, matched, final, found, made⟩
    rw [matchPatternForRule_eq_syntactic] at matched
    have shape := queryRules rule member
    obtain ⟨last, flows, _⟩ := shape.flows
    have related := matchPattern_sound matched
    obtain ⟨covered, settled⟩ := match_binds rule.left shape.left related
    obtain ⟨above, -, holds⟩ := premises_sound moded dataRows flows covered
      (match_data rule.left shape.left data related) settled found
    exact ⟨rule, member, final, match_exact rule.left shape.left data related above,
      (applyBindingsForRuleUsing_empty_eq_applyBindings rule final shape.aligned).symm.trans made, holds⟩
  · rintro ⟨rule, member, witness, rfl, rfl, holds⟩
    have shape := queryRules rule member
    obtain ⟨last, flows, rightBound⟩ := shape.flows
    have settled := settled_of_data rule.left shape.left data
    obtain ⟨initial, related, valued⟩ := match_complete witness rule.left shape.left settled
    obtain ⟨final, found, finalCovered, finalValued⟩ := premises_complete moded witness settled flows
      (match_binds rule.left shape.left related).1 valued holds
    refine ⟨rule, member, initial,
      by rw [matchPatternForRule_eq_syntactic]; exact matchPattern_iff_matchRel.mpr related, final, found, ?_⟩
    exact (applyBindingsForRuleUsing_empty_eq_applyBindings rule final shape.aligned).trans
      (instance_agree rule.right shape.right fun name inRight =>
        lookup_of_valued finalValued finalCovered (rightBound name inRight))

/-! ## Controls -/

namespace Controls

/-- The first position is the input. -/
def firstInput : String → ℕ → Bool := fun _ index => index == 0

def successor : RelationEnv where
  tuples relation asked :=
    match relation, asked with
    | "next", [value, _] => [[value, .apply "S" [value]]]
    | _, _ => []

/-- **Positive**: the successor relation, beside the built-in equality, is moded. -/
theorem successor_moded (language : LanguageDef) : Moded successor language firstInput := by
  intro relation asked row lengths agree
  rcases asked with _ | ⟨first, _ | ⟨second, _ | ⟨third, others⟩⟩⟩ <;>
    rcases row with _ | ⟨one, _ | ⟨two, _ | ⟨three, more⟩⟩⟩ <;> simp at lengths
  case cons.cons.nil.cons.cons.nil =>
    have input : first = one := by simpa using agree 0 rfl
    subst input
    by_cases isEq : relation = "eq"
    · subst isEq
      simp [queryRows, builtinRelationTuples, successor]
      grind
    · by_cases isNext : relation = "next"
      · subst isNext
        simp [queryRows, builtinRelationTuples, successor]
      · simp [queryRows, builtinRelationTuples, successor, isEq, isNext]
  all_goals simp [queryRows, builtinRelationTuples, successor]

/-- **Positive**: asked with data, it answers with data. -/
theorem successor_data (language : LanguageDef) : DataRows successor language := by
  intro relation asked row offered data
  rcases asked with _ | ⟨first, _ | ⟨second, _ | ⟨third, others⟩⟩⟩
  case cons.cons.nil =>
    simp only [isDataList, Bool.and_eq_true, and_true] at data
    by_cases isEq : relation = "eq"
    · subst isEq
      simp [queryRows, builtinRelationTuples, successor] at offered
      rcases offered with rfl | rfl <;> simp [isDataList, data]
    · by_cases isNext : relation = "next"
      · subst isNext
        simp [queryRows, builtinRelationTuples, successor] at offered
        subst offered
        simp [isDataList, isData, data]
      · simp [queryRows, builtinRelationTuples, successor, isEq, isNext] at offered
  all_goals simp [queryRows, builtinRelationTuples, successor] at offered

/-- A relation that answers only while its output slot is still open. -/
def peek : RelationEnv where
  tuples relation asked :=
    match relation, asked with
    | "peek", [value, .fvar _] => [[value, value]]
    | _, _ => []

/-- **Negative**: looking at the output slot is not moded. -/
theorem peek_not_moded (language : LanguageDef) : ¬ Moded peek language firstInput := by
  intro moded
  have same := moded "peek" [.bvar 0, .fvar "y"] [.bvar 0, .bvar 0] rfl (by
    intro index input
    obtain rfl : index = 0 := by simpa [firstInput] using input
    rfl)
  simp [queryRows, builtinRelationTuples, peek] at same

end Controls

#print axioms step_iff_instance
#print axioms Controls.successor_moded
#print axioms Controls.successor_data
#print axioms Controls.peek_not_moded

end Mettapedia.GSLT.Compilation.Uniform.QueryPremises
