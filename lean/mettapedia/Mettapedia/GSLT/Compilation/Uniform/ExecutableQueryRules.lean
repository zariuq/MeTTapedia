import Mettapedia.GSLT.Compilation.Uniform.QueryRulesOnTheStep
import Mettapedia.GSLT.Compilation.Uniform.RowReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Executable

/-!
# Executing the compiled query rules

The relational compilation gives each premise its full row pattern. Its
executable form also supplies the declared input fields to the built-in
relation. The same row pattern matches the answer, preserving bindings and
enforcing agreement between repeated variables. A result can be enumerated
using just the finite rule list and the given executable built-in relations.

The mode law says that the membership of a row in a built-in relation's answers can
be tested on the declared inputs alone. The lowering uses that law to
establish both directions of the relational correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.ExecutableQueryRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic.LP (Term)
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm inst toTerm inst_toTerm head tail vars_toTerm Bound written)
open RuleSyntax.Machines (rowRule mem_unknowns vars_of_mem_unknowns)
open RuleSyntax.ComputedConditions
open RootRewritesOnTheStep (appTerm symTerm labelCode encode encodeList encodeList_inj)
open QueryPremises (queryRows Moded DataRows)
open QueryRulesOnTheStep (DataCarrier)

/-- Fill the output positions of a call while retaining its arity. -/
def fillOutputs {α : Type} (isInput : ℕ → Bool) (blank : α) (fields : List α) : List α :=
  fields.mapIdx fun i field => if isInput i then field else blank

@[simp] theorem length_fillOutputs {α : Type} (isInput : ℕ → Bool) (blank : α) (fields : List α) :
    (fillOutputs isInput blank fields).length = fields.length := by simp [fillOutputs]

theorem get_input {α : Type} (isInput : ℕ → Bool) (blank : α) (fields : List α) (i : ℕ)
    (input : isInput i = true) : (fillOutputs isInput blank fields)[i]? = fields[i]? := by
  rw [fillOutputs, List.getElem?_mapIdx]
  cases fields[i]? <;> simp [input]

theorem map_fillOutputs {α β : Type} (f : α → β) (isInput : ℕ → Bool) (blank : α) (fields : List α) :
    (fillOutputs isInput blank fields).map f = fillOutputs isInput (f blank) (fields.map f) := by
  apply List.ext_getElem?
  intro i
  simp only [fillOutputs, List.getElem?_map, List.getElem?_mapIdx]
  cases fields[i]? <;> cases isInput i <;> rfl

private def blank : Pattern := .apply "" []

/-- Read the fixed-arity, right-nested tuple pattern produced by the compiler. -/
def tupleFields : Tm → Option (List Tm)
  | .const (.sym 0) => some []
  | .app .app args => (tupleFields (args tail)).map (args head :: ·)
  | _ => none

@[simp] theorem fields_app (first rest : Tm) :
    tupleFields (appTerm first rest) = (tupleFields rest).map (first :: ·) := rfl

private def pack : List Expr → Expr
  | [] => .sym 0
  | first :: rest => .app first (pack rest)

private theorem pack_injective : Function.Injective pack := by
  intro left
  induction left with
  | nil =>
      intro right eq
      cases right <;> simp_all [pack]
  | cons first rest ih =>
      intro right eq
      cases right with
      | nil => simp [pack] at eq
      | cons other others =>
          simp only [pack, Expr.app.injEq] at eq
          exact congrArg₂ List.cons eq.1 (ih eq.2)

private theorem pack_encode (row : List Pattern) : pack (row.map encode) = encodeList row := by
  induction row with
  | nil => rfl
  | cons first rest ih => simp [pack, encodeList, ih]

private theorem pack_fields (θ : ℕ → Expr) : ∀ {row : Tm} {fields : List Tm},
    tupleFields row = some fields → pack (fields.map (inst θ)) = inst θ row
  | .const (.sym 0), fields, found => by
      change some [] = some fields at found
      cases found
      rfl
  | .app .app args, _, found => by
      simp only [tupleFields, Option.map_eq_some_iff] at found
      obtain ⟨rest, lowered, rfl⟩ := found
      simp [pack, pack_fields θ lowered, inst]
  | .const (.sym (_ + 1)), _, found => by simp [tupleFields] at found
  | .const (.name _), _, found => by simp [tupleFields] at found
  | .var _, _, found => by simp [tupleFields] at found
  | .app .code _, _, found => by simp [tupleFields] at found

private def key (input : String → ℕ → Bool) (call : Condition ℕ Tm) : Option (Condition ℕ Tm) :=
  (tupleFields call.value).map fun fields =>
    { call with arguments := fillOutputs (input (RowReadback.label call.name)) (toTerm (encode blank)) fields }

/-- Executable built-in relations for a declared presentation. -/
def builtins (relEnv : RelationEnv) (language : LanguageDef) : Executable.Builtins :=
  fun name arguments =>
    match RowReadback.readArguments arguments with
    | some asked => (queryRows relEnv language (RowReadback.label name) asked).map encodeList
    | none => []

variable {relEnv : RelationEnv} {language : LanguageDef} {input : String → ℕ → Bool}

private theorem key_exact (moded : Moded relEnv language input)
    {call keyed : Condition ℕ Tm} {name : String}
    (unkeyed : call.arguments = []) (named : call.name = labelCode name)
    (lowered : key input call = some keyed) (θ : ℕ → Expr) :
    (builtins relEnv language).relates keyed.name (keyed.arguments.map (inst θ)) (inst θ keyed.value) ↔
      QueryRulesOnTheStep.relations relEnv language call.name (call.arguments.map (inst θ)) (inst θ call.value) := by
  obtain ⟨fields, split, rfl⟩ := Option.map_eq_some_iff.mp lowered
  have valueOf (row : List Pattern) (value : inst θ call.value = encodeList row) :
      fields.map (inst θ) = row.map encode :=
    pack_injective ((pack_fields θ split).trans (value.trans (pack_encode row).symm))
  have argumentsOf (row : List Pattern) (value : inst θ call.value = encodeList row) :
      (fillOutputs (input (RowReadback.label call.name)) (toTerm (encode blank)) fields).map (inst θ) =
        (fillOutputs (input name) blank row).map encode := by
    rw [named, RowReadback.label_code, map_fillOutputs, inst_toTerm, valueOf row value]
    rw [map_fillOutputs]
  have membership (row : List Pattern) :
      row ∈ queryRows relEnv language name (fillOutputs (input name) blank row) ↔
        row ∈ queryRows relEnv language name row :=
    moded _ _ _ (length_fillOutputs _ _ _) fun i => get_input _ _ _ i
  constructor
  · intro accepted
    change inst θ call.value ∈ builtins relEnv language call.name
      ((fillOutputs (input (RowReadback.label call.name)) (toTerm (encode blank)) fields).map (inst θ)) at accepted
    obtain ⟨asked, read⟩ : ∃ asked, RowReadback.readArguments
        ((fillOutputs (input (RowReadback.label call.name)) (toTerm (encode blank)) fields).map (inst θ)) =
          some asked := by
      unfold builtins at accepted
      split at accepted
      · rename_i asked read
        exact ⟨asked, read⟩
      · simp at accepted
    unfold builtins at accepted
    rw [read, named, RowReadback.label_code] at accepted
    obtain ⟨row, inRows, encoded⟩ := List.mem_map.mp accepted
    have askedIs : asked = fillOutputs (input name) blank row := by
      rw [argumentsOf row encoded.symm, RowReadback.readArguments_encode] at read
      exact (Option.some.inj read).symm
    refine ⟨by simp [unkeyed], name, row, named, encoded.symm, membership row |>.mp ?_⟩
    rwa [← askedIs]
  · rintro ⟨-, other, row, otherName, encoded, admitted⟩
    obtain rfl : name = other := RootRewritesOnTheStep.labelCode_injective (named.symm.trans otherName)
    unfold Executable.Builtins.relates
    change inst θ call.value ∈ builtins relEnv language call.name
      ((fillOutputs (input (RowReadback.label call.name)) (toTerm (encode blank)) fields).map (inst θ))
    rw [argumentsOf row encoded, builtins, RowReadback.readArguments_encode, named, RowReadback.label_code]
    exact List.mem_map.mpr ⟨row, (membership row).mpr admitted, encoded.symm⟩

private theorem mapM_members {α β : Type} (f : α → Option β) :
    ∀ {source : List α} {target : List β}, source.mapM f = some target →
      (∀ a ∈ source, ∃ b ∈ target, f a = some b) ∧ (∀ b ∈ target, ∃ a ∈ source, f a = some b)
  | [], _, converted => by
      simp at converted
      subst converted
      simp
  | a :: rest, target, converted => by
      cases one : f a with
      | none => simp [List.mapM_cons, one] at converted
      | some b =>
          cases more : rest.mapM f with
          | none => simp [List.mapM_cons, one, more] at converted
          | some bs =>
              simp only [List.mapM_cons, one, more] at converted
              change some (b :: bs) = some target at converted
              cases converted
              obtain ⟨forward, backward⟩ := mapM_members f more
              constructor
              · intro x inside
                rcases List.mem_cons.mp inside with rfl | later
                · exact ⟨b, List.mem_cons_self, one⟩
                · obtain ⟨y, member, computed⟩ := forward x later
                  exact ⟨y, List.mem_cons_of_mem _ member, computed⟩
              · intro y inside
                rcases List.mem_cons.mp inside with rfl | later
                · exact ⟨a, List.mem_cons_self, one⟩
                · obtain ⟨x, member, computed⟩ := backward y later
                  exact ⟨x, List.mem_cons_of_mem _ member, computed⟩

private def keyRule (input : String → ℕ → Bool) (rule : RuleWithCondition ℕ Tm) : Option Executable.Schema :=
  match rule.rule.body.take, rule.rule.body.produce with
  | [left], [right] => (rule.conditions.mapM (key input)).map fun conditions => ⟨left, conditions, right⟩
  | _, _ => none

inductive Refusal where
  | source (reason : QueryRulesOnTheStep.Refusal)
  | malformedRule
  deriving Repr

/-- Reuse the relational compiler and extract the executable input fields. -/
def compile (input : String → ℕ → Bool) (language : LanguageDef) :
    Except Refusal (List Executable.Schema) :=
  match QueryRulesOnTheStep.compile input language with
  | .error reason => .error (.source reason)
  | .ok rules =>
      match rules.mapM (keyRule input) with
      | none => .error .malformedRule
      | some schemas => .ok schemas

private theorem compile_spec {schemas : List Executable.Schema}
    (compiled : compile input language = .ok schemas) :
    ∃ rules, QueryRulesOnTheStep.compile input language = .ok rules ∧
      rules.mapM (keyRule input) = some schemas := by
  unfold compile at compiled
  cases source : QueryRulesOnTheStep.compile input language with
  | error reason => simp [source] at compiled
  | ok rules =>
      cases converted : rules.mapM (keyRule input) with
      | none => simp [source, converted] at compiled
      | some others =>
          simp only [source, converted, Except.ok.injEq] at compiled
          subst others
          exact ⟨rules, rfl, converted⟩

private theorem tupleFields_lower {rests : List String} :
    ∀ (patterns : List Pattern) {row : Tm},
      OrderedRows.lowerThen? rests patterns (symTerm 0) = some row →
      ∃ fields, tupleFields row = some fields ∧
        ∀ (i : ℕ) field, fields[i]? = some field →
          ∃ pattern, patterns[i]? = some pattern ∧ OrderedRows.lower? rests pattern = some field
  | [], _, lowered => by
      simp only [OrderedRows.lowerThen?, Option.some.injEq] at lowered
      subst lowered
      exact ⟨[], rfl, by simp⟩
  | pattern :: patterns, _, lowered => by
      simp only [OrderedRows.lowerThen?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨first, firstLowered, rest, restLowered, rfl⟩ := lowered
      obtain ⟨fields, restFields, readField⟩ := tupleFields_lower patterns restLowered
      refine ⟨first :: fields, by simp [restFields], ?_⟩
      intro i field found
      cases i with
      | zero =>
          have same : first = field := Option.some.inj found
          exact ⟨pattern, rfl, same ▸ firstLowered⟩
      | succ i =>
          obtain ⟨p, member, lowered⟩ := readField i field found
          exact ⟨p, member, lowered⟩

private theorem field_is_input {isInput : ℕ → Bool} {hole : Tm}
    {fields : List Tm} {field : Tm} (member : field ∈ fillOutputs isInput hole fields) :
    field = hole ∨ ∃ i, fields[i]? = some field ∧ isInput i = true := by
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
  rw [fillOutputs, List.getElem?_mapIdx] at found
  cases original : fields[i]? with
  | none => simp [original] at found
  | some term =>
      cases needed : isInput i <;> simp [original, needed] at found
      · exact Or.inl found.symm
      · exact Or.inr ⟨i, by rw [original, found], needed⟩

private theorem variables_in_row {rests : List String} (p : Pattern) {term : Tm}
    (lowered : OrderedRows.lower? rests p = some term) {name : String}
    (member : name ∈ OrderedMatching.names p) :
    labelCode name ∈ term.freeVars := by
  apply vars_of_mem_unknowns
  rw [OrderedRows.unknowns_lower p lowered]
  exact List.mem_map_of_mem member

private theorem keyQueries_ready {rests settled bound last : List String} {premises : List Premise}
    (flows : QueryPremises.Flows input settled bound premises last) :
    ∀ {conditions : List (Condition ℕ Tm)} {available : List Tm},
      QueryRulesOnTheStep.lowerQueries rests premises = some conditions →
      (∀ name ∈ bound, ∃ u ∈ available, labelCode name ∈ u.freeVars) →
      ∃ keyed, conditions.mapM (key input) = some keyed ∧
        RuleWithCondition.WellModedAfter available keyed := by
  induction flows with
  | nil =>
      intro conditions available lowered _
      simp only [QueryRulesOnTheStep.lowerQueries, Option.some.injEq] at lowered
      subst lowered
      exact ⟨[], rfl, trivial⟩
  | @query bound last relation arguments premises ordered inputsBound settledRest flows ih =>
      intro conditions available lowered known
      simp only [QueryRulesOnTheStep.lowerQueries, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨row, rowLowered, others, othersLowered, rfl⟩ := lowered
      obtain ⟨fields, split, readField⟩ := tupleFields_lower arguments rowLowered
      let original : Condition ℕ Tm := { name := labelCode relation, arguments := [], value := row }
      let call : Condition ℕ Tm :=
        { original with arguments := fillOutputs (input relation) (toTerm (encode blank)) fields }
      have callLowered : key input original = some call := by
        simp [key, original, split, call]
      have nowKnown : ∀ name ∈ bound ++ OrderedMatching.namesList arguments,
          ∃ u ∈ available ++ [row], labelCode name ∈ u.freeVars := by
        intro name member
        rcases List.mem_append.mp member with prior | new
        · obtain ⟨u, inside, boundHere⟩ := known name prior
          exact ⟨u, List.mem_append_left _ inside, boundHere⟩
        · refine ⟨row, List.mem_append_right _ (List.mem_singleton_self _), vars_of_mem_unknowns _ ?_⟩
          rw [OrderedRows.unknowns_lowerThen arguments rowLowered]
          exact List.mem_append_left _ (List.mem_map_of_mem new)
      obtain ⟨more, converted, ready⟩ := ih othersLowered nowKnown
      refine ⟨call :: more, ?_, ?_⟩
      · change (original :: others).mapM (key input) = _
        rw [List.mapM_cons, callLowered, converted]
        rfl
      · refine ⟨?_, ready⟩
        intro term member x used
        change term ∈ fillOutputs (input relation) (toTerm (encode blank)) fields at member
        rcases field_is_input member with rfl | ⟨i, found, needed⟩
        · exact False.elim (vars_toTerm _ x used)
        · obtain ⟨pattern, atIndex, lower⟩ := readField i term found
          have occurrence := mem_unknowns term used
          rw [OrderedRows.unknowns_lower pattern lower] at occurrence
          obtain ⟨name, inPattern, rfl⟩ := List.mem_map.mp occurrence
          exact known name (inputsBound i pattern atIndex needed name inPattern)

private theorem keyRule_ready {authored : RewriteRule} {rule : RuleWithCondition ℕ Tm}
    (origin : QueryRulesOnTheStep.Origin input authored rule)
    (restricted : rule.RangeRestrictedWith) :
    ∃ schema, keyRule input rule = some schema ∧
      Executable.Ready schema.right [schema.left] schema.conditions := by
  obtain ⟨left, right, conditions, leftLowered, -, rfl⟩ := origin.sides
  obtain ⟨_, conditionsFlow, _⟩ := origin.source.flows
  obtain ⟨keyed, compiled, modes⟩ := keyQueries_ready conditionsFlow origin.conditions
    (available := [left]) fun name member =>
      ⟨left, List.mem_singleton_self _, variables_in_row authored.left leftLowered member⟩
  refine ⟨⟨left, keyed, right⟩, ?_, modes, ?_⟩
  · simp [keyRule, rowRule, compiled]
  · intro x used
    have bound := restricted right (by simp [rowRule, written]) x used
    rcases bound with input | ⟨c, member, occurs⟩
    · exact ⟨left, List.mem_append_left _ (List.mem_singleton_self _),
        by simpa [Bound, rowRule] using input⟩
    · obtain ⟨d, inKeyed, compiledCall⟩ := (mapM_members _ compiled).1 c member
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp compiledCall
      exact ⟨c.value, List.mem_append_right _ (List.mem_map.mpr ⟨_, inKeyed, rfl⟩), occurs⟩

private theorem convert_rules {rules : List (RuleWithCondition ℕ Tm)}
    (each : ∀ rule ∈ rules, ∃ schema, keyRule input rule = some schema) :
    ∃ schemas, rules.mapM (keyRule input) = some schemas ∧ schemas.length = rules.length := by
  induction rules with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons rule rest ih =>
      obtain ⟨schema, one⟩ := each rule List.mem_cons_self
      obtain ⟨schemas, converted, size⟩ := ih fun r inside => each r (List.mem_cons_of_mem _ inside)
      refine ⟨schema :: schemas, ?_, by simp [size]⟩
      rw [List.mapM_cons, one, converted]
      rfl

/-- Every presentation admitted by the uniform query compiler also compiles
to a finite executable program, with one schema per compiled rule. -/
theorem compile_complete {rules : List (RuleWithCondition ℕ Tm)}
    (authored : QueryRulesOnTheStep.compile input language = .ok rules) :
    ∃ schemas, compile input language = .ok schemas ∧ schemas.length = rules.length := by
  obtain ⟨schemas, converted, length⟩ := convert_rules (input := input) fun rule inside => by
    obtain ⟨_, _, origin⟩ := (QueryRulesOnTheStep.compile_origins authored).2 rule inside
    obtain ⟨schema, lowered, _⟩ := keyRule_ready origin (QueryRulesOnTheStep.compiled_restricted authored rule inside)
    exact ⟨schema, lowered⟩
  exact ⟨schemas, by simp [compile, authored, converted], length⟩

private theorem keyRule_exact (moded : Moded relEnv language input)
    {authored : RewriteRule} {rule : RuleWithCondition ℕ Tm} {schema : Executable.Schema}
    (origin : QueryRulesOnTheStep.Origin input authored rule)
    (converted : keyRule input rule = some schema) (source target : Expr) :
    RelationStep (builtins relEnv language).relates schema.rule {source} {target} ↔
      RelationStep (QueryRulesOnTheStep.relations relEnv language) rule {source} {target} := by
  obtain ⟨left, right, conditions, -, -, rfl⟩ := origin.sides
  unfold keyRule at converted
  change (conditions.mapM (key input)).map (fun cs => Executable.Schema.mk left cs right) = some schema at converted
  obtain ⟨keyed, mapped, rfl⟩ := Option.map_eq_some_iff.mp converted
  obtain ⟨forward, backward⟩ := mapM_members _ mapped
  have equivalent (θ : ℕ → Expr) (c : Condition ℕ Tm) (member : c ∈ conditions)
      (d : Condition ℕ Tm) (keyed : key input c = some d) :
      (builtins relEnv language).relates d.name (d.arguments.map (inst θ)) (inst θ d.value) ↔
        QueryRulesOnTheStep.relations relEnv language c.name (c.arguments.map (inst θ)) (inst θ c.value) := by
    obtain ⟨name, _, _, _, named, unkeyed⟩ :=
      QueryRulesOnTheStep.condition_query origin.conditions c member
    exact key_exact (name := name) moded unkeyed named keyed θ
  constructor
  · rintro ⟨θ, rest, taken, read, guards, held, made⟩
    refine ⟨θ, rest, taken, read, guards, ?_, made⟩
    intro c member
    obtain ⟨d, newMember, lowered⟩ := forward c member
    exact (equivalent θ c member d lowered).mp (held d newMember)
  · rintro ⟨θ, rest, taken, read, guards, held, made⟩
    refine ⟨θ, rest, taken, read, guards, ?_, made⟩
    intro d member
    obtain ⟨c, oldMember, lowered⟩ := backward d member
    exact (equivalent θ c oldMember d lowered).mpr (held c oldMember)

/-- The executable program has the same successors as the authored rules on
the presentation's invariant carrier. In particular, a successful enumeration
uses no semantic relation membership test beyond running its declared built-in relations. -/
theorem mem_successors (moded : Moded relEnv language input) (dataRows : DataRows relEnv language)
    {carrier : Pattern → Prop} (carried : DataCarrier relEnv language carrier)
    {schemas : List Executable.Schema} (compiled : compile input language = .ok schemas)
    {source : Pattern} (member : carrier source) (target : Expr) :
    target ∈ Executable.successors (builtins relEnv language) schemas (encode source) ↔
      ∃ result, Step (engineBasePremises relEnv) language source result ∧ target = encode result := by
  obtain ⟨rules, oldCompiled, converted⟩ := compile_spec compiled
  obtain ⟨forward, backward⟩ := mapM_members _ converted
  have ready (schema : Executable.Schema) (inside : schema ∈ schemas) :
      Executable.Ready schema.right [schema.left] schema.conditions := by
    obtain ⟨rule, oldMember, lowered⟩ := backward schema inside
    obtain ⟨_, _, origin⟩ := (QueryRulesOnTheStep.compile_origins oldCompiled).2 rule oldMember
    obtain ⟨expected, same, wellModed⟩ :=
      keyRule_ready origin (QueryRulesOnTheStep.compiled_restricted oldCompiled rule oldMember)
    have eq : schema = expected := Option.some.inj (lowered.symm.trans same)
    cases eq
    exact wellModed
  rw [Executable.mem_program_successors _ _ ready]
  constructor
  · rintro ⟨schema, inside, fired⟩
    obtain ⟨rule, oldMember, lowered⟩ := backward schema inside
    obtain ⟨_, _, origin⟩ := (QueryRulesOnTheStep.compile_origins oldCompiled).2 rule oldMember
    obtain ⟨result, reduction, readback⟩ :=
      QueryRulesOnTheStep.relationStep_image moded dataRows oldCompiled (carried.data _ member) oldMember
        ((keyRule_exact moded origin lowered _ _).mp fired)
    exact ⟨result, reduction, by simpa using readback⟩
  · rintro ⟨result, stepped, rfl⟩
    have resultData := carried.data result (carried.closed source result member stepped)
    obtain ⟨rule, inRules, fired⟩ := QueryRulesOnTheStep.relationStep_of_step
      moded dataRows oldCompiled (carried.data _ member) resultData stepped
    obtain ⟨schema, inSchemas, lowered⟩ := forward rule inRules
    obtain ⟨_, _, origin⟩ := (QueryRulesOnTheStep.compile_origins oldCompiled).2 rule inRules
    exact ⟨schema, inSchemas, (keyRule_exact moded origin lowered _ _).mpr fired⟩

/-- Read the successors back as terms of the authored language. -/
def successorPatterns (relEnv : RelationEnv) (language : LanguageDef)
    (schemas : List Executable.Schema) (source : Pattern) : List Pattern :=
  (Executable.successors (builtins relEnv language) schemas (encode source)).filterMap RowReadback.readPattern

theorem mem_successorPatterns (moded : Moded relEnv language input) (dataRows : DataRows relEnv language)
    {carrier : Pattern → Prop} (carried : DataCarrier relEnv language carrier)
    {schemas : List Executable.Schema} (compiled : compile input language = .ok schemas)
    {source : Pattern} (member : carrier source) (target : Pattern) :
    target ∈ successorPatterns relEnv language schemas source ↔
      Step (engineBasePremises relEnv) language source target := by
  rw [successorPatterns, List.mem_filterMap]
  constructor
  · rintro ⟨row, inside, read⟩
    obtain ⟨result, stepped, rfl⟩ :=
      (mem_successors moded dataRows carried compiled member row).mp inside
    rw [RowReadback.readPattern_encode] at read
    cases read
    exact stepped
  · intro stepped
    exact ⟨encode target,
      (mem_successors moded dataRows carried compiled member _).mpr ⟨target, stepped, rfl⟩,
      RowReadback.readPattern_encode target⟩

private def iterate {State : Type} (next : State → List State) : ℕ → State → List State
  | 0, source => [source]
  | n + 1, source => (next source).flatMap (iterate next n)

private theorem mem_iterate (theory : GSLT.{0}) (next : theory.Term → List theory.Term)
    (carrier : theory.Term → Prop)
    (correct : ∀ source, carrier source → ∀ target, target ∈ next source ↔ theory.Step source target)
    (closed : ∀ source target, carrier source → theory.Step source target → carrier target) :
    ∀ (steps : ℕ) {source : theory.Term}, carrier source → ∀ target : theory.Term,
      target ∈ iterate next steps source ↔ ∃ path : theory.RewritePath source target, path.length = steps := by
  intro steps
  induction steps with
  | zero =>
      intro source _ target
      constructor
      · intro member
        have same : target = source := List.mem_singleton.mp member
        cases same
        exact ⟨.nil source, rfl⟩
      · rintro ⟨path, length⟩
        cases path with
        | nil => exact List.mem_singleton_self _
        | cons _ _ => simp [GSLT.RewritePath.length] at length
  | succ n ih =>
      intro source valid target
      simp only [iterate, List.mem_flatMap]
      constructor
      · rintro ⟨middle, member, rest⟩
        have first := (correct source valid middle).mp member
        have nextValid := closed source middle valid first
        obtain ⟨path, length⟩ := (ih nextValid target).mp rest
        exact ⟨.cons first path, by simp [GSLT.RewritePath.length, length, Nat.add_comm]⟩
      · rintro ⟨path, length⟩
        cases path with
        | nil => simp [GSLT.RewritePath.length] at length
        | cons first rest =>
            have nextValid := closed source _ valid first
            refine ⟨_, (correct source valid _).mpr first,
              (ih nextValid target).mpr ⟨rest, ?_⟩⟩
            rw [GSLT.RewritePath.length] at length
            omega

/-- Enumerate the configurations at the end of exactly the given number of firings. -/
def frontier (relEnv : RelationEnv) (language : LanguageDef) (schemas : List Executable.Schema) :
    ℕ → Pattern → List Pattern :=
  iterate (successorPatterns relEnv language schemas)

theorem mem_frontier (moded : Moded relEnv language input) (dataRows : DataRows relEnv language)
    {carrier : Pattern → Prop} (carried : DataCarrier relEnv language carrier)
    {schemas : List Executable.Schema} (compiled : compile input language = .ok schemas) :
    ∀ (steps : ℕ) {source : Pattern}, carrier source → ∀ target : Pattern,
      target ∈ frontier relEnv language schemas steps source ↔
        ∃ path : (RootRewritesOnTheStep.sourceSystem relEnv language).RewritePath source target,
          path.length = steps :=
  mem_iterate (RootRewritesOnTheStep.sourceSystem relEnv language) _ carrier
    (fun _ valid => mem_successorPatterns moded dataRows carried compiled valid) carried.closed

#print axioms mem_successors
#print axioms mem_frontier
#print axioms compile_complete

end Mettapedia.GSLT.Compilation.Uniform.ExecutableQueryRules
