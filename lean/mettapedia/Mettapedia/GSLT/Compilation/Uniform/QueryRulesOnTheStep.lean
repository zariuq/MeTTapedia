import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep
import Mettapedia.GSLT.Compilation.Uniform.OrderedRows
import Mettapedia.GSLT.Compilation.Uniform.QueryPremises
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.GraphRelations

/-!
# Rules with query premises compiled to the transform step

One authored rule is one transform rule with one condition per query, and the only
compiler is `compile`: it reads the rules and the input positions of the relations, and
no language name.

Patterns are ordered (`OrderedMatching.ordered`): constructors and vectors, a rest allowed.

`stepCorrespondence`: on a carrier of data closed under steps (`DataCarrier`), one
authored step is one firing, both ways, along runs of every length. The relations are the
program's, at their graph. The hypotheses are about the presentation alone: its relations
are `Moded` and answer data with data (`DataRows`), and it has such a carrier.

Outside this lowering, and refused with the rule's name: static equations, premises that
are not queries, inputs bound by nothing, binders, bags, sets and explicit substitution.

Controls: a rule that asks the successor relation compiles (`Controls.counter_compiles`)
and so does a rule that takes a vector apart (`Controls.dropping_compiles`). The same
rule asking at an unbound input is refused (`Controls.unbound_refused`), and so is a rule
over a bag (`Controls.bag_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.QueryRulesOnTheStep

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines
open RuleSyntax.ComputedConditions (RuleWithCondition Condition RelationStep relationEvaluation relationGraph
  programSystem specialized rows relationCorrespondence)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open RootRewritesOnTheStep (labelCode labelCode_injective symTerm encode encodeList encode_injective encodeList_inj
  sourceSystem)
open OrderedMatching (ordered orderedList isData isDataList names namesList restNames restNamesList Settled
  settled_of_data)
open OrderedRows (lower? lowerThen? inst_lower inst_lowerThen lower_captures lowerThen_captures exists_witness
  Captured unknowns_lower unknowns_lowerThen)
open QueryPremises (Moded DataRows Flows QueryRule queryRows step_iff_instance)

/-! ## The compiler -/

/-- The variables queried by the premises. -/
def queryVars : List Premise → List String
  | [] => []
  | .relationQuery _ arguments :: premises => namesList arguments ++ queryVars premises
  | _ :: premises => queryVars premises

/-- The rest variables of a rule. -/
def ruleRests (rule : RewriteRule) : List String := restNames rule.left ++ restNames rule.right

/-- One condition per query, in their order. -/
def lowerQueries (rests : List String) : List Premise → Option (List (Condition ℕ Tm))
  | [] => some []
  | .relationQuery relation arguments :: premises =>
      (lowerThen? rests arguments (symTerm 0)).bind fun row => (lowerQueries rests premises).map fun conditions =>
        { name := labelCode relation, arguments := [], value := row } :: conditions
  | _ :: _ => none

/-- Whether every input is bound when it is asked, and what is bound at the end. -/
def boundAfter? (inputs : String → ℕ → Bool) (settled : List String) :
    List String → List Premise → Option (List String)
  | bound, [] => some bound
  | bound, .relationQuery relation arguments :: premises =>
      if orderedList arguments &&
          arguments.zipIdx.all (fun entry => !inputs relation entry.2 ||
            (names entry.1).all fun name => bound.contains name) &&
          (restNamesList arguments).all (fun rest => settled.contains rest) then
        boundAfter? inputs settled (bound ++ namesList arguments) premises
      else none
  | _, _ :: _ => none

/-- Why a presentation is outside this lowering. -/
inductive Refusal where
  | staticEquations
  | movedAcrossBinder (rule : String)
  | premises (rule : String)
  | notOrdered (rule : String)
  | unboundInResult (rule : String)
  deriving DecidableEq, Repr

/-- One transform rule with conditions for one authored rule. -/
def lowerRule (inputs : String → ℕ → Bool) (rule : RewriteRule) : Except Refusal (RuleWithCondition ℕ Tm) :=
  if ruleDepthAligned rule then
    if ordered rule.left && ordered rule.right then
      match lower? (ruleRests rule) rule.left, lower? (ruleRests rule) rule.right with
      | some left, some right =>
          match boundAfter? inputs (restNames rule.left) (names rule.left) rule.premises,
            lowerQueries (ruleRests rule) rule.premises with
          | some bound, some conditions =>
              if (names rule.right).all fun name => bound.contains name then
                .ok { rule := rowRule left right, conditions }
              else .error (.unboundInResult rule.name)
          | _, _ => .error (.premises rule.name)
      | _, _ => .error (.notOrdered rule.name)
    else .error (.notOrdered rule.name)
  else .error (.movedAcrossBinder rule.name)

/-- The rules of a presentation, in their order. -/
def lowerRules (inputs : String → ℕ → Bool) : List RewriteRule → Except Refusal (List (RuleWithCondition ℕ Tm))
  | [] => .ok []
  | rule :: rules =>
      match lowerRule inputs rule with
      | .error reason => .error reason
      | .ok compiled =>
          match lowerRules inputs rules with
          | .error reason => .error reason
          | .ok others => .ok (compiled :: others)

/-- **The compiler.** -/
def compile (inputs : String → ℕ → Bool) (language : LanguageDef) :
    Except Refusal (List (RuleWithCondition ℕ Tm)) :=
  if language.equations.isEmpty && !language.hasAlgebraDeclarations then lowerRules inputs language.rewrites
  else .error .staticEquations

/-! ## Where a compiled rule comes from -/

/-- What a compiled rule keeps of its authored rule. -/
structure Origin (inputs : String → ℕ → Bool) (rule : RewriteRule) (compiled : RuleWithCondition ℕ Tm) : Prop where
  source : QueryRule inputs rule
  sides : ∃ left right conditions, lower? (ruleRests rule) rule.left = some left ∧
    lower? (ruleRests rule) rule.right = some right ∧ compiled = { rule := rowRule left right, conditions }
  conditions : lowerQueries (ruleRests rule) rule.premises = some compiled.conditions
  bound : ∀ name ∈ names rule.right, name ∈ names rule.left ++ queryVars rule.premises

theorem boundAfter_spec {inputs : String → ℕ → Bool} {settled : List String} :
    ∀ {premises : List Premise} {bound last : List String},
    boundAfter? inputs settled bound premises = some last →
      Flows inputs settled bound premises last ∧ ∀ name ∈ last, name ∈ bound ++ queryVars premises
  | [], bound, last, computed => by
      simp only [boundAfter?, Option.some.injEq] at computed
      subst computed
      exact ⟨.nil, by simp [queryVars]⟩
  | .relationQuery relation arguments :: premises, bound, last, computed => by
      simp only [boundAfter?] at computed
      split at computed
      · rename_i checked
        simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          List.contains_iff_mem] at checked
        obtain ⟨flows, within⟩ := boundAfter_spec (premises := premises) computed
        refine ⟨.query checked.1.1 ?_ checked.2 flows, ?_⟩
        · intro index argument found input
          have listed : (argument, index) ∈ arguments.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr found
          rcases checked.1.2 (argument, index) listed with absent | within
          · simp [input] at absent
          · exact within
        · intro name member
          simpa [queryVars, List.append_assoc] using within name member
      · cases computed
  | .freshness _ :: _, _, _, computed => by simp [boundAfter?] at computed
  | .congruence _ _ :: _, _, _, computed => by simp [boundAfter?] at computed
  | .scopedStep _ :: _, _, _, computed => by simp [boundAfter?] at computed
  | .forAll _ _ _ :: _, _, _, computed => by simp [boundAfter?] at computed

theorem lowerRule_origin {inputs : String → ℕ → Bool} {rule : RewriteRule} {compiled : RuleWithCondition ℕ Tm}
    (lowered : lowerRule inputs rule = .ok compiled) : Origin inputs rule compiled := by
  unfold lowerRule at lowered
  split at lowered
  · rename_i aligned
    split at lowered
    · rename_i shapes
      simp only [Bool.and_eq_true] at shapes
      split at lowered
      · rename_i left right leftLowered rightLowered
        split at lowered
        · rename_i bound conditions computed queries
          split at lowered
          · rename_i rightBound
            cases lowered
            simp only [List.all_eq_true, List.contains_iff_mem] at rightBound
            obtain ⟨flows, within⟩ := boundAfter_spec computed
            exact ⟨⟨shapes.1, shapes.2, aligned, bound, flows, rightBound⟩,
              ⟨left, right, conditions, leftLowered, rightLowered, rfl⟩, queries,
              fun name member => within name (rightBound name member)⟩
          · cases lowered
        · cases lowered
      · cases lowered
    · cases lowered
  · cases lowered

theorem lowerRules_origins {inputs : String → ℕ → Bool} :
    ∀ {authored : List RewriteRule} {compiled : List (RuleWithCondition ℕ Tm)},
      lowerRules inputs authored = .ok compiled →
      (∀ rule ∈ authored, ∃ ρ ∈ compiled, Origin inputs rule ρ) ∧
        ∀ ρ ∈ compiled, ∃ rule ∈ authored, Origin inputs rule ρ
  | [], compiled, lowered => by
      simp only [lowerRules, Except.ok.injEq] at lowered
      subst lowered
      simp
  | rule :: authored, compiled, lowered => by
      cases one : lowerRule inputs rule with
      | error reason => simp [lowerRules, one] at lowered
      | ok first =>
        cases more : lowerRules inputs authored with
        | error reason => simp [lowerRules, one, more] at lowered
        | ok others =>
          simp only [lowerRules, one, more, Except.ok.injEq] at lowered
          subst lowered
          have origin := lowerRule_origin one
          obtain ⟨forward, backward⟩ := lowerRules_origins more
          constructor
          · intro other member
            rcases List.mem_cons.mp member with rfl | later
            · exact ⟨first, List.mem_cons_self .., origin⟩
            · exact (forward other later).imp fun _ found => ⟨List.mem_cons_of_mem _ found.1, found.2⟩
          · intro ρ member
            rcases List.mem_cons.mp member with rfl | later
            · exact ⟨rule, List.mem_cons_self .., origin⟩
            · exact (backward ρ later).imp fun _ found => ⟨List.mem_cons_of_mem _ found.1, found.2⟩

variable {inputs : String → ℕ → Bool} {language : LanguageDef} {program : List (RuleWithCondition ℕ Tm)}

theorem compile_origins (compiled : compile inputs language = .ok program) :
    (∀ rule ∈ language.rewrites, ∃ ρ ∈ program, Origin inputs rule ρ) ∧
      ∀ ρ ∈ program, ∃ rule ∈ language.rewrites, Origin inputs rule ρ := by
  unfold compile at compiled
  split at compiled
  · exact lowerRules_origins compiled
  · cases compiled

theorem condition_query {rests : List String} : ∀ {premises : List Premise} {conditions : List (Condition ℕ Tm)},
    lowerQueries rests premises = some conditions → ∀ c ∈ conditions, ∃ relation arguments,
      Premise.relationQuery relation arguments ∈ premises ∧ lowerThen? rests arguments (symTerm 0) = some c.value ∧
        c.name = labelCode relation ∧ c.arguments = []
  | [], conditions, lowered => by
      simp only [lowerQueries, Option.some.injEq] at lowered
      subst lowered
      simp
  | .relationQuery relation arguments :: premises, conditions, lowered => by
      simp only [lowerQueries, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨row, rowLowered, others, othersLowered, rfl⟩ := lowered
      intro c member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨relation, arguments, List.mem_cons_self .., rowLowered, rfl, rfl⟩
      · obtain ⟨name, asked, inside, rest⟩ := condition_query othersLowered c later
        exact ⟨name, asked, List.mem_cons_of_mem _ inside, rest⟩
  | .freshness _ :: _, _, lowered => by simp [lowerQueries] at lowered
  | .congruence _ _ :: _, _, lowered => by simp [lowerQueries] at lowered
  | .scopedStep _ :: _, _, lowered => by simp [lowerQueries] at lowered
  | .forAll _ _ _ :: _, _, lowered => by simp [lowerQueries] at lowered

theorem query_condition {rests : List String} : ∀ {premises : List Premise} {conditions : List (Condition ℕ Tm)},
    lowerQueries rests premises = some conditions → ∀ relation arguments,
      Premise.relationQuery relation arguments ∈ premises → ∃ c ∈ conditions,
        lowerThen? rests arguments (symTerm 0) = some c.value ∧ c.name = labelCode relation
  | [], _, _, _, _, member => nomatch member
  | .relationQuery first firstArguments :: premises, conditions, lowered, relation, arguments, member => by
      simp only [lowerQueries, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨row, rowLowered, others, othersLowered, rfl⟩ := lowered
      rcases List.mem_cons.mp member with here | later
      · cases here
        exact ⟨_, List.mem_cons_self .., rowLowered, rfl⟩
      · exact (query_condition othersLowered relation arguments later).imp
          fun _ found => ⟨List.mem_cons_of_mem _ found.1, found.2⟩
  | .freshness _ :: _, _, lowered, _, _, _ => by simp [lowerQueries] at lowered
  | .congruence _ _ :: _, _, lowered, _, _, _ => by simp [lowerQueries] at lowered
  | .scopedStep _ :: _, _, lowered, _, _, _ => by simp [lowerQueries] at lowered
  | .forAll _ _ _ :: _, _, lowered, _, _, _ => by simp [lowerQueries] at lowered

theorem mem_queryVars : ∀ {premises : List Premise} {name : String}, name ∈ queryVars premises →
    ∃ relation arguments, Premise.relationQuery relation arguments ∈ premises ∧ name ∈ namesList arguments
  | [], _, member => nomatch member
  | .relationQuery relation arguments :: premises, name, member => by
      simp only [queryVars, List.mem_append] at member
      rcases member with here | later
      · exact ⟨relation, arguments, List.mem_cons_self .., here⟩
      · obtain ⟨other, asked, inside, found⟩ := mem_queryVars later
        exact ⟨other, asked, List.mem_cons_of_mem _ inside, found⟩
  | .freshness _ :: _, _, member => by
      obtain ⟨other, asked, inside, found⟩ := mem_queryVars (by simpa only [queryVars] using member)
      exact ⟨other, asked, List.mem_cons_of_mem _ inside, found⟩
  | .congruence _ _ :: _, _, member => by
      obtain ⟨other, asked, inside, found⟩ := mem_queryVars (by simpa only [queryVars] using member)
      exact ⟨other, asked, List.mem_cons_of_mem _ inside, found⟩
  | .scopedStep _ :: _, _, member => by
      obtain ⟨other, asked, inside, found⟩ := mem_queryVars (by simpa only [queryVars] using member)
      exact ⟨other, asked, List.mem_cons_of_mem _ inside, found⟩
  | .forAll _ _ _ :: _, _, member => by
      obtain ⟨other, asked, inside, found⟩ := mem_queryVars (by simpa only [queryVars] using member)
      exact ⟨other, asked, List.mem_cons_of_mem _ inside, found⟩

theorem queryVars_of_mem {relation : String} {arguments : List Pattern} {name : String} :
    ∀ {premises : List Premise}, Premise.relationQuery relation arguments ∈ premises →
      name ∈ namesList arguments → name ∈ queryVars premises
  | [], member, _ => nomatch member
  | premise :: premises, member, inArguments => by
      rcases List.mem_cons.mp member with rfl | later
      · exact List.mem_append_left _ inArguments
      · have found := queryVars_of_mem later inArguments
        cases premise <;> simp only [queryVars] <;> first | exact List.mem_append_right _ found | exact found

/-! ## Exactness -/

/-- The rows of the presentation's relations, as relations of the step. -/
def relations (relEnv : RelationEnv) (language : LanguageDef) : ComputedConditions.Relations :=
  fun f arguments value => arguments = [] ∧ ∃ relation row, f = labelCode relation ∧ value = encodeList row ∧
    row ∈ queryRows relEnv language relation row

variable {relEnv : RelationEnv}

/-- **A carrier of data closed under the steps**: all data, or the configurations of a machine. -/
structure DataCarrier (relEnv : RelationEnv) (language : LanguageDef) (carrier : Pattern → Prop) : Prop where
  data : ∀ term, carrier term → isData term = true
  closed : ∀ source target, carrier source → Step (engineBasePremises relEnv) language source target →
    carrier target

/-- What an unknown is given under a witness. -/
def valueRow (rests : List String) (witness : Bindings) (name : String) : Expr :=
  if name ∈ rests then
    match lookupOrFvar witness name with
    | .collection .vec tail none => encodeList tail
    | _ => .sym 0
  else encode (lookupOrFvar witness name)

/-- An authored step is a firing of the compiled rule. -/
theorem relationStep_of_step (moded : Moded relEnv language inputs) (dataRows : DataRows relEnv language)
    (compiled : compile inputs language = .ok program) {source target : Pattern}
    (data : isData source = true) (targetData : isData target = true)
    (stepped : Step (engineBasePremises relEnv) language source target) :
    ∃ ρ ∈ program, RelationStep (relations relEnv language) ρ {encode source} {encode target} := by
  obtain ⟨forward, -⟩ := compile_origins compiled
  obtain ⟨rule, member, bindings, rfl, rfl, queried⟩ := (step_iff_instance moded dataRows
    (fun rule member => (forward rule member).elim fun _ found => found.2.source) data target).mp stepped
  obtain ⟨ρ, inProgram, origin⟩ := forward rule member
  obtain ⟨left, right, lowered, leftLowered, rightLowered, rfl⟩ := origin.sides
  have settled : Settled bindings (ruleRests rule) := by
    intro rest inRests
    rcases List.mem_append.mp inRests with inLeft | inRight
    · exact settled_of_data rule.left origin.source.left data rest inLeft
    · exact settled_of_data rule.right origin.source.right targetData rest inRight
  let θ : ℕ → Expr := Function.extend labelCode (valueRow (ruleRests rule) bindings) (fun _ => .sym 0)
  have agree : ∀ name, OrderedRows.Holds (ruleRests rule) θ bindings name := by
    intro name
    have valued : θ (labelCode name) = valueRow (ruleRests rule) bindings name :=
      labelCode_injective.extend_apply _ _ name
    unfold OrderedRows.Holds
    split
    · rename_i inRests
      obtain ⟨tail, found⟩ := settled name inRests
      have value : lookupOrFvar bindings name = .collection .vec tail none := by
        simp [lookupOrFvar, applyBindings, found]
      exact ⟨tail, value, by rw [valued, valueRow, if_pos inRests, value]⟩
    · rename_i outside
      rw [valued, valueRow, if_neg outside]
  refine ⟨_, inProgram, θ, 0, ?_, by simp [rowRule], by simp [rowRule, equationsOf], ?_, ?_⟩
  · simp [rowRule, inst_lower rule.left leftLowered fun name _ => agree name]
  · intro c inConditions
    obtain ⟨relation, arguments, inPremises, lowered, named, noArguments⟩ :=
      condition_query origin.conditions c inConditions
    exact ⟨by simp [noArguments], relation, arguments.map (applyBindings bindings), named,
      by simpa using inst_lowerThen arguments lowered (fun name _ => agree name) (tail := []) (by simp [encodeList]),
      queried relation arguments inPremises⟩
  · simp [rowRule, inst_lower rule.right rightLowered fun name _ => agree name]

/-- **A firing at a data row is an authored step, and its result is a source row.** -/
theorem relationStep_image (moded : Moded relEnv language inputs) (dataRows : DataRows relEnv language)
    (compiled : compile inputs language = .ok program) {source : Pattern} (data : isData source = true)
    {after : Multiset Expr} {ρ : RuleWithCondition ℕ Tm} (inProgram : ρ ∈ program)
    (fired : RelationStep (relations relEnv language) ρ {encode source} after) :
    ∃ target, Step (engineBasePremises relEnv) language source target ∧
      after = {encode target} := by
  obtain ⟨forward, backward⟩ := compile_origins compiled
  obtain ⟨rule, member, origin⟩ := backward ρ inProgram
  obtain ⟨left, right, lowered, leftLowered, rightLowered, rfl⟩ := origin.sides
  obtain ⟨θ, rest, split, -, -, conditions, rfl⟩ := fired
  have taken : (([inst θ left] : List Expr) : Multiset Expr) + rest = {encode source} := by
    simpa [rowRule] using split
  obtain ⟨met, rfl⟩ := row_of_singleton taken
  have captured : ∀ name ∈ names rule.left ++ queryVars rule.premises, Captured (ruleRests rule) θ name := by
    intro name inside
    rcases List.mem_append.mp inside with inLeft | inQuery
    · exact lower_captures rule.left leftLowered met name inLeft
    · obtain ⟨relation, arguments, inPremises, inArguments⟩ := mem_queryVars inQuery
      obtain ⟨c, inConditions, lowered, -⟩ := query_condition origin.conditions relation arguments inPremises
      obtain ⟨-, _, row, -, valueIs, -⟩ := conditions c inConditions
      exact (lowerThen_captures arguments lowered valueIs).1 name inArguments
  obtain ⟨bindings, bound⟩ := exists_witness _ captured
  have leftIs := inst_lower rule.left leftLowered fun name inLeft => bound name (List.mem_append_left _ inLeft)
  have rightIs := inst_lower rule.right rightLowered fun name inRight => bound name (origin.bound name inRight)
  refine ⟨applyBindings bindings rule.right, (step_iff_instance moded dataRows
    (fun rule member => (forward rule member).elim fun _ found => found.2.source) data _).mpr
      ⟨rule, member, bindings, encode_injective (leftIs.symm.trans met), rfl, ?_⟩, ?_⟩
  · intro relation arguments inPremises
    obtain ⟨c, inConditions, lowered, named⟩ := query_condition origin.conditions relation arguments inPremises
    obtain ⟨-, found, row, code, valueIs, inRows⟩ := conditions c inConditions
    obtain rfl : relation = found := labelCode_injective (named.symm.trans code)
    have instances := inst_lowerThen arguments lowered
      (fun name inArguments => bound name (List.mem_append_right _ (queryVars_of_mem inPremises inArguments)))
      (tail := []) (by simp [encodeList])
    have rowIs : arguments.map (applyBindings bindings) = row :=
      encodeList_inj _ _ (by simpa using instances.symm.trans valueIs)
    rw [rowIs]
    exact inRows
  · simp [rowRule, rightIs]

/-- A term of the carrier is hosted by the bag of its row. -/
def EncodedBag (carrier : Pattern → Prop) (source : Pattern) (bag : Multiset Expr) : Prop :=
  carrier source ∧ bag = {encode source}

/-- The presentation and firings with related conditions. -/
def encodedCorrespondence (moded : Moded relEnv language inputs) (dataRows : DataRows relEnv language)
    {carrier : Pattern → Prop} (carried : DataCarrier relEnv language carrier)
    (compiled : compile inputs language = .ok program) :
    OperationalCorrespondence (sourceSystem relEnv language)
      (relationEvaluation (relations relEnv language) {ρ | ρ ∈ program}) where
  related := EncodedBag carrier
  readStep := by
    intro source bag next same stepped
    obtain ⟨inCarrier, rfl⟩ := same
    obtain ⟨ρ, inProgram, fired⟩ := stepped
    obtain ⟨target, sourceStep, targetBag⟩ := relationStep_image moded dataRows compiled
      (carried.data source inCarrier) inProgram fired
    exact Or.inr ⟨target, sourceStep, carried.closed source target inCarrier sourceStep, targetBag⟩
  forward := by
    intro source target bag same stepped
    obtain ⟨inCarrier, rfl⟩ := same
    have targetIn := carried.closed source target inCarrier stepped
    exact ⟨({encode target} : Multiset Expr), (executionPath_nonempty_iff_multiStep _ _ _).mpr
      (.step (relationStep_of_step moded dataRows compiled (carried.data source inCarrier)
        (carried.data target targetIn) stepped) (.refl _)), targetIn, rfl⟩

theorem compiled_restricted (compiled : compile inputs language = .ok program) :
    ∀ ρ ∈ {ρ | ρ ∈ program}, ρ.RangeRestrictedWith := by
  intro ρ inProgram
  obtain ⟨rule, -, origin⟩ := (compile_origins compiled).2 ρ inProgram
  obtain ⟨left, right, lowered, leftLowered, rightLowered, rfl⟩ := origin.sides
  intro t inWritten x inVars
  obtain rfl : t = right := by simpa [written, rowRule] using inWritten
  have coded := mem_unknowns _ inVars
  rw [unknowns_lower rule.right rightLowered] at coded
  obtain ⟨name, inRight, rfl⟩ := List.mem_map.mp coded
  rcases List.mem_append.mp (origin.bound name inRight) with inLeft | inQuery
  · refine Or.inl ⟨left, by simp [rowRule], vars_of_mem_unknowns left ?_⟩
    rw [unknowns_lower rule.left leftLowered]
    exact List.mem_map_of_mem inLeft
  · obtain ⟨relation, arguments, inPremises, inArguments⟩ := mem_queryVars inQuery
    obtain ⟨c, inConditions, lowered, -⟩ := query_condition origin.conditions relation arguments inPremises
    refine Or.inr ⟨c, inConditions, vars_of_mem_unknowns c.value ?_⟩
    rw [unknowns_lowerThen arguments lowered]
    exact List.mem_append_left _ (List.mem_map_of_mem inArguments)

/-- **GSLT to transform, with query premises**: on the carrier, one step for one firing, both ways. -/
def stepCorrespondence {O : Type} [DecidableEq O] [Infinite O] (moded : Moded relEnv language inputs)
    (dataRows : DataRows relEnv language) {carrier : Pattern → Prop}
    (carried : DataCarrier relEnv language carrier)
    (compiled : compile inputs language = .ok program) :
    OperationalCorrespondence (sourceSystem relEnv language)
      (programSystem O (specialized rows (relationGraph (relations relEnv language)) {ρ | ρ ∈ program})) :=
  (encodedCorrespondence moded dataRows carried compiled).comp (relationCorrespondence
    (fun ρ inProgram => by
      obtain ⟨_, -, origin⟩ := (compile_origins compiled).2 ρ inProgram
      obtain ⟨_, _, _, -, -, rfl⟩ := origin.sides
      simp [rowRule])
    (fun ρ inProgram => by
      obtain ⟨_, -, origin⟩ := (compile_origins compiled).2 ρ inProgram
      obtain ⟨_, _, _, -, -, rfl⟩ := origin.sides
      simp [rowRule])
    (compiled_restricted compiled))

/-! ## Controls -/

namespace Controls

/-- A number steps to what the successor relation answers at `asked`. -/
def counting (asked : String) : RewriteRule where
  name := "count"
  typeContext := []
  premises := [.relationQuery "next" [.fvar asked, .fvar "y"]]
  left := .apply "N" [.fvar "x"]
  right := .apply "N" [.fvar "y"]

def counter (asked : String) : LanguageDef := { LanguageDef.empty "counter" with rewrites := [counting asked] }

/-- **Positive**: the input is bound by the left side. -/
theorem counter_compiles :
    ∃ program, compile QueryPremises.Controls.firstInput (counter "x") = .ok program := by
  simp [compile, counter, counting, LanguageDef.empty, LanguageDef.hasAlgebraDeclarations, lowerRules, lowerRule,
    ruleRests, ordered, orderedList, names, namesList, restNames, restNamesList, lower?, lowerThen?, lowerQueries,
    boundAfter?, ruleDepthAligned, depthAligned, depthAlignedList, captureDepth, captureDepthList,
    QueryPremises.Controls.firstInput]

/-- **Negative**: an input bound by nothing is refused, by the rule's name. -/
theorem unbound_refused :
    compile QueryPremises.Controls.firstInput (counter "z") = .error (.premises "count") := by
  simp [compile, counter, counting, LanguageDef.empty, LanguageDef.hasAlgebraDeclarations, lowerRules, lowerRule,
    ruleRests, ordered, orderedList, names, namesList, restNames, restNamesList, lower?, lowerThen?, lowerQueries,
    boundAfter?, ruleDepthAligned, depthAligned, depthAlignedList, captureDepth, captureDepthList,
    QueryPremises.Controls.firstInput]

/-- A collection steps to what is left without one element. -/
def dropping (kind : CollType) : LanguageDef :=
  { LanguageDef.empty "dropping" with
    rewrites := [{ name := "drop", typeContext := [], premises := []
                   left := .apply "L" [.collection kind [.fvar "head"] (some "tail")]
                   right := .apply "L" [.collection kind [] (some "tail")] }] }

/-- **Positive**: a vector with a rest. -/
theorem dropping_compiles :
    ∃ program, compile QueryPremises.Controls.firstInput (dropping .vec) = .ok program := by
  simp [compile, dropping, LanguageDef.empty, LanguageDef.hasAlgebraDeclarations, lowerRules, lowerRule,
    ruleRests, ordered, orderedList, names, namesList, restNames, restNamesList, lower?, lowerThen?, lowerQueries,
    boundAfter?, ruleDepthAligned, depthAligned, depthAlignedList, captureDepth, captureDepthList]

/-- **Negative**: a bag is not ordered, and is refused by the rule's name. -/
theorem bag_refused :
    compile QueryPremises.Controls.firstInput (dropping .hashBag) = .error (.notOrdered "drop") := by
  simp [compile, dropping, LanguageDef.empty, LanguageDef.hasAlgebraDeclarations, lowerRules, lowerRule,
    ordered, orderedList, ruleDepthAligned, depthAligned, depthAlignedList, captureDepth, captureDepthList]

end Controls

#print axioms stepCorrespondence
#print axioms Controls.counter_compiles
#print axioms Controls.unbound_refused
#print axioms Controls.dropping_compiles
#print axioms Controls.bag_refused

end Mettapedia.GSLT.Compilation.Uniform.QueryRulesOnTheStep
