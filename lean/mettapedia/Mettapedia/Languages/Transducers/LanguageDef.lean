import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.DecimalNames
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Moore and Mealy machines as language definitions

A finite-state transducer reads a stream of input symbols and emits one
output per symbol read.  The two classical disciplines differ in what the
output function reads: a Moore machine's output is a function of its state; a
Mealy machine's output is a function of its state and of the symbol it has
just consumed.

Both are authored here as one family of language definitions indexed by the
discipline.  A configuration is the control state fed a stream, `Feed`.  The
single rule at which the control meets the stream consumes the first symbol,
emits the output term and continues in the next state:

* Moore: `Feed(q, Next(a, rest)) ⟶ Emit(Out(q), Feed(Delta(q, a), rest))`;
* Mealy: `Feed(q, Next(a, rest)) ⟶ Emit(Out(q, a), Feed(Delta(q, a), rest))`.

The transition table and the output table are further rewrites, one per
entry, which evaluate `Delta` and `Out` on numbered states and symbols.  The
remaining rules say where evaluation may take place.

States, input symbols and output symbols are unary numerals of their own
sorts, so the signature depends only on the discipline.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Transducers

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL

/-- What the output function reads. -/
inductive Discipline where
  /-- The output is a function of the state. -/
  | moore
  /-- The output is a function of the state and the consumed symbol. -/
  | mealy
deriving DecidableEq, Repr

/-- One entry of the transition table: in `state`, consuming `input`, the
control enters `next`. -/
structure Transition where
  state : Nat
  input : Nat
  next : Nat
deriving DecidableEq, Repr

/-- The argument of the output function under each discipline. -/
abbrev OutputKey : Discipline → Type
  | .moore => Nat
  | .mealy => Nat × Nat

/-- A transducer: its transition table and its output table, over numbered
states, input symbols and output symbols. -/
structure Machine (discipline : Discipline) where
  transitions : List Transition
  outputs : List (OutputKey discipline × Nat)

/-- The state numbered `index`. -/
def stateTerm (index : Nat) : Pattern := Pattern.unary "QZero" "QSucc" index

/-- The input symbol numbered `index`. -/
def inputTerm (index : Nat) : Pattern := Pattern.unary "IZero" "ISucc" index

/-- The output symbol numbered `index`. -/
def outputTerm (index : Nat) : Pattern := Pattern.unary "OZero" "OSucc" index

/-- The parameters of the output function under each discipline. -/
def outputParameters : Discipline → List TermParam
  | .moore => [.simple "state" (.base "State")]
  | .mealy => [.simple "state" (.base "State"), .simple "input" (.base "Input")]

/-- The constructors.  `Feed` builds a configuration from the control state
and the stream; `Emit` prefixes a configuration with an emitted output;
`Delta` and `Out` are the transition and output functions awaiting
evaluation. -/
def terms (discipline : Discipline) : List GrammarRule := [
    { label := "QZero", category := "State", params := [], syntaxPattern := [] },
    { label := "QSucc", category := "State",
      params := [.simple "state" (.base "State")],
      syntaxPattern := [.nonTerminal "state"] },
    { label := "IZero", category := "Input", params := [], syntaxPattern := [] },
    { label := "ISucc", category := "Input",
      params := [.simple "input" (.base "Input")],
      syntaxPattern := [.nonTerminal "input"] },
    { label := "OZero", category := "Output", params := [], syntaxPattern := [] },
    { label := "OSucc", category := "Output",
      params := [.simple "output" (.base "Output")],
      syntaxPattern := [.nonTerminal "output"] },
    { label := "Delta", category := "State",
      params := [.simple "state" (.base "State"), .simple "input" (.base "Input")],
      syntaxPattern := [.nonTerminal "state", .nonTerminal "input"] },
    { label := "Out", category := "Output",
      params := outputParameters discipline,
      syntaxPattern := (outputParameters discipline).map fun parameter =>
        .nonTerminal (TermParam.bodyName parameter) },
    { label := "Done", category := "Stream", params := [], syntaxPattern := [] },
    { label := "Next", category := "Stream",
      params := [.simple "input" (.base "Input"), .simple "rest" (.base "Stream")],
      syntaxPattern := [.nonTerminal "input", .nonTerminal "rest"] },
    { label := "Feed", category := "Config",
      params := [.simple "control" (.base "State"), .simple "stream" (.base "Stream")],
      syntaxPattern := [.nonTerminal "control", .nonTerminal "stream"] },
    { label := "Emit", category := "Config",
      params := [.simple "output" (.base "Output"), .simple "rest" (.base "Config")],
      syntaxPattern := [.nonTerminal "output", .nonTerminal "rest"] }
  ]

/-- A configuration: the control fed a stream. -/
def feed (control stream : Pattern) : Pattern := .apply "Feed" [control, stream]

/-- A stream with a first symbol. -/
def next (input rest : Pattern) : Pattern := .apply "Next" [input, rest]

/-- The exhausted stream. -/
def done : Pattern := .apply "Done" []

/-- A configuration that has emitted an output. -/
def emit (output rest : Pattern) : Pattern := .apply "Emit" [output, rest]

/-- The transition function awaiting evaluation. -/
def delta (state input : Pattern) : Pattern := .apply "Delta" [state, input]

/-- The output function applied to what the discipline lets it read. -/
def outputCall : Discipline → Pattern → Pattern → Pattern
  | .moore, state, _ => .apply "Out" [state]
  | .mealy, state, input => .apply "Out" [state, input]

/-- The rule at which the control meets the stream. -/
def feedRule (discipline : Discipline) : RewriteRule where
  name := "Feed"
  typeContext := [("q", .base "State"), ("a", .base "Input"), ("rest", .base "Stream")]
  premises := []
  left := feed (.fvar "q") (next (.fvar "a") (.fvar "rest"))
  right := emit (outputCall discipline (.fvar "q") (.fvar "a"))
    (feed (delta (.fvar "q") (.fvar "a")) (.fvar "rest"))

/-- The emitted output may be evaluated. -/
def emitValueRule : RewriteRule where
  name := "EmitValue"
  typeContext := [("c", .base "Config")]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := emit (.fvar "S") (.fvar "c")
  right := emit (.fvar "T") (.fvar "c")

/-- The run continues beneath an emitted output. -/
def emitRestRule : RewriteRule where
  name := "EmitRest"
  typeContext := [("o", .base "Output")]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := emit (.fvar "o") (.fvar "S")
  right := emit (.fvar "o") (.fvar "T")

/-- The control state may be evaluated. -/
def feedControlRule : RewriteRule where
  name := "FeedControl"
  typeContext := [("stream", .base "Stream")]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := feed (.fvar "S") (.fvar "stream")
  right := feed (.fvar "T") (.fvar "stream")

/-- The state argument of the transition function may be evaluated. -/
def deltaControlRule : RewriteRule where
  name := "DeltaControl"
  typeContext := [("a", .base "Input")]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := delta (.fvar "S") (.fvar "a")
  right := delta (.fvar "T") (.fvar "a")

/-- The state argument of the output function may be evaluated. -/
def outControlRule (discipline : Discipline) : RewriteRule where
  name := "OutControl"
  typeContext :=
    match discipline with
    | .moore => []
    | .mealy => [("a", .base "Input")]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := outputCall discipline (.fvar "S") (.fvar "a")
  right := outputCall discipline (.fvar "T") (.fvar "a")

/-- The rules every transducer of a discipline has. -/
def fixedRules (discipline : Discipline) : List RewriteRule :=
  [feedRule discipline, emitValueRule, emitRestRule, feedControlRule, deltaControlRule,
    outControlRule discipline]

/-- One entry of the transition table as a rewrite. -/
def transitionRule (index : Nat) (entry : Transition) : RewriteRule where
  name := "Transition" ++ toString index
  typeContext := []
  premises := []
  left := delta (stateTerm entry.state) (inputTerm entry.input)
  right := stateTerm entry.next

/-- The left side of an output-table entry. -/
def outputEntryCall : (discipline : Discipline) → OutputKey discipline → Pattern
  | .moore, state => .apply "Out" [stateTerm state]
  | .mealy, (state, input) => .apply "Out" [stateTerm state, inputTerm input]

/-- One entry of the output table as a rewrite. -/
def outputRule (discipline : Discipline) (index : Nat)
    (entry : OutputKey discipline × Nat) : RewriteRule where
  name := "Reading" ++ toString index
  typeContext := []
  premises := []
  left := outputEntryCall discipline entry.1
  right := outputTerm entry.2

/-- The rewrites of a transducer. -/
def rewrites {discipline : Discipline} (machine : Machine discipline) : List RewriteRule :=
  fixedRules discipline ++ machine.transitions.mapIdx transitionRule ++
    machine.outputs.mapIdx (outputRule discipline)

/-- The presentation of a finite-state transducer. -/
def transducer {discipline : Discipline} (machine : Machine discipline) : LanguageDef :=
  { name := "Transducer"
    types := ["State", "Input", "Output", "Stream", "Config"]
    terms := terms discipline
    equations := []
    rewrites := rewrites machine }

/-! ## Validation -/

/-- The signature of a discipline, with no rule. -/
def signature (discipline : Discipline) : LanguageDef :=
  { name := "Transducer"
    types := ["State", "Input", "Output", "Stream", "Config"]
    terms := terms discipline
    equations := []
    rewrites := [] }

/-- The constructors of a discipline's signature with their arities. -/
def signatureReferences (discipline : Discipline) : List (String × Nat) :=
  [("QZero", 0), ("QSucc", 1), ("IZero", 0), ("ISucc", 1), ("OZero", 0), ("OSucc", 1),
    ("Delta", 2), ("Out", (outputParameters discipline).length), ("Done", 0), ("Next", 2),
    ("Feed", 2), ("Emit", 2)]

theorem signatureReferences_declared (discipline : Discipline) :
    ∀ reference ∈ signatureReferences discipline,
      LanguageDef.referenceDeclared (terms discipline) reference = true := by
  cases discipline <;> decide

/-- Discharge the side conditions of a rule with a reduction hypothesis between
the metavariables `S` and `T`. -/
local macro "validate_congruence_rule" definition:ident : tactic =>
  `(tactic|
    (apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
       (target := "T")
     · rfl
     · simp [$definition:ident, transducer, LanguageDef.typeNames, TypeExpr.baseNames,
         TypeDecl.plain]
     · intro reference membership
       apply signatureReferences_declared
       simp [$definition:ident, feed, emit, delta, Pattern.constructorRefs,
         Pattern.constructorRefsList] at membership
       simp only [signatureReferences, List.mem_cons, List.not_mem_nil, or_false]
       tauto
     · intro reference membership
       apply signatureReferences_declared
       simp [$definition:ident, feed, emit, delta, Pattern.constructorRefs,
         Pattern.constructorRefsList] at membership
       simp only [signatureReferences, List.mem_cons, List.not_mem_nil, or_false]
       tauto
     · intro context
       simp [$definition:ident, transducer, terms, feed, emit, delta,
         LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
         Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
         LanguageDef.patternBinderNames, LanguageDef.premiseLocallyScoped,
         LanguageDef.premiseFvarNames, LanguageDef.premisePatterns,
         LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames]))

theorem emitValueRule_validates {discipline : Discipline} (machine : Machine discipline) :
    LanguageDef.validateRewrite (transducer machine) emitValueRule = [] := by
  validate_congruence_rule emitValueRule

theorem emitRestRule_validates {discipline : Discipline} (machine : Machine discipline) :
    LanguageDef.validateRewrite (transducer machine) emitRestRule = [] := by
  validate_congruence_rule emitRestRule

theorem feedControlRule_validates {discipline : Discipline} (machine : Machine discipline) :
    LanguageDef.validateRewrite (transducer machine) feedControlRule = [] := by
  validate_congruence_rule feedControlRule

theorem deltaControlRule_validates {discipline : Discipline} (machine : Machine discipline) :
    LanguageDef.validateRewrite (transducer machine) deltaControlRule = [] := by
  validate_congruence_rule deltaControlRule

theorem feedRule_validates {discipline : Discipline} (machine : Machine discipline) :
    LanguageDef.validateRewrite (transducer machine) (feedRule discipline) = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
  · rfl
  · simp [feedRule, transducer, LanguageDef.typeNames, TypeExpr.baseNames, TypeDecl.plain]
  · intro reference membership
    apply signatureReferences_declared
    simp [feedRule, feed, next, Pattern.constructorRefs, Pattern.constructorRefsList]
      at membership
    simp only [signatureReferences, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro reference membership
    apply signatureReferences_declared
    cases discipline <;>
      simp [feedRule, feed, emit, delta, outputCall, Pattern.constructorRefs,
        Pattern.constructorRefsList] at membership <;>
      simp only [signatureReferences, outputParameters, List.length_cons, List.length_nil,
        List.mem_cons, List.not_mem_nil, or_false] <;>
      tauto
  · intro context
    cases discipline <;>
      simp [feedRule, transducer, terms, feed, next, emit, delta, outputCall,
        LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
        LanguageDef.patternBinderNames]

theorem outControlRule_validates {discipline : Discipline} (machine : Machine discipline) :
    LanguageDef.validateRewrite (transducer machine) (outControlRule discipline) = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
    (target := "T")
  · rfl
  · cases discipline <;>
      simp [outControlRule, transducer, LanguageDef.typeNames, TypeExpr.baseNames,
        TypeDecl.plain]
  · intro reference membership
    apply signatureReferences_declared
    cases discipline <;>
      simp [outControlRule, outputCall, Pattern.constructorRefs, Pattern.constructorRefsList]
        at membership <;>
      simp only [signatureReferences, outputParameters, List.length_cons, List.length_nil,
        List.mem_cons, List.not_mem_nil, or_false] <;>
      tauto
  · intro reference membership
    apply signatureReferences_declared
    cases discipline <;>
      simp [outControlRule, outputCall, Pattern.constructorRefs, Pattern.constructorRefsList]
        at membership <;>
      simp only [signatureReferences, outputParameters, List.length_cons, List.length_nil,
        List.mem_cons, List.not_mem_nil, or_false] <;>
      tauto
  · intro context
    cases discipline <;>
      simp [outControlRule, transducer, terms, outputCall, LanguageDef.validateRulePatterns,
        Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
        LanguageDef.patternFvarNames, Pattern.freeFvarNames, LanguageDef.patternBinderNames,
        LanguageDef.premiseLocallyScoped, LanguageDef.premiseFvarNames,
        LanguageDef.premisePatterns, LanguageDef.premiseForAllParams,
        LanguageDef.premiseProducedFvarNames]

/-- The rules shared by every transducer of a discipline validate. -/
theorem fixedRules_validate {discipline : Discipline} (machine : Machine discipline) :
    ∀ rewrite ∈ fixedRules discipline,
      LanguageDef.validateRewrite (transducer machine) rewrite = [] := by
  intro rewrite membership
  simp only [fixedRules, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · exact feedRule_validates machine
  · exact emitValueRule_validates machine
  · exact emitRestRule_validates machine
  · exact feedControlRule_validates machine
  · exact deltaControlRule_validates machine
  · exact outControlRule_validates machine

theorem transitionRule_validates {discipline : Discipline} (machine : Machine discipline)
    (index : Nat) (entry : Transition) :
    LanguageDef.validateRewrite (transducer machine) (transitionRule index entry) = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
  · rfl
  · intro entry membership
    cases membership
  · intro reference membership
    apply signatureReferences_declared
    simp [transitionRule, delta, stateTerm, inputTerm, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.constructorRefs_unary] at membership
    simp only [signatureReferences, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro reference membership
    apply signatureReferences_declared
    simp [transitionRule, stateTerm, Pattern.constructorRefs_unary] at membership
    simp only [signatureReferences, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro context
    simp [transitionRule, delta, stateTerm, inputTerm, LanguageDef.validateRulePatterns,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      LanguageDef.patternFvarNames, Pattern.freeFvarNames, LanguageDef.patternBinderNames]

theorem outputRule_validates {discipline : Discipline} (machine : Machine discipline)
    (index : Nat) (entry : OutputKey discipline × Nat) :
    LanguageDef.validateRewrite (transducer machine) (outputRule discipline index entry) = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
  · rfl
  · intro entry membership
    cases membership
  · intro reference membership
    apply signatureReferences_declared
    cases discipline
    · obtain ⟨state, output⟩ := entry
      change Nat at state
      simp [outputRule, outputEntryCall, stateTerm, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.constructorRefs_unary] at membership
      simp only [signatureReferences, outputParameters, List.length_cons, List.length_nil,
        List.mem_cons, List.not_mem_nil, or_false]
      tauto
    · obtain ⟨⟨state, input⟩, output⟩ := entry
      simp [outputRule, outputEntryCall, stateTerm, inputTerm, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.constructorRefs_unary] at membership
      simp only [signatureReferences, outputParameters, List.length_cons, List.length_nil,
        List.mem_cons, List.not_mem_nil, or_false]
      tauto
  · intro reference membership
    apply signatureReferences_declared
    simp [outputRule, outputTerm, Pattern.constructorRefs_unary] at membership
    simp only [signatureReferences, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro context
    cases discipline
    · obtain ⟨state, output⟩ := entry
      change Nat at state
      simp [outputRule, outputEntryCall, outputTerm, stateTerm,
        LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
        LanguageDef.patternBinderNames]
    · obtain ⟨⟨state, input⟩, output⟩ := entry
      simp [outputRule, outputEntryCall, outputTerm, stateTerm, inputTerm,
        LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
        LanguageDef.patternBinderNames]

/-- Every rewrite of a transducer validates against its presentation. -/
theorem rewrites_validate {discipline : Discipline} (machine : Machine discipline) :
    ∀ rewrite ∈ (transducer machine).rewrites,
      LanguageDef.validateRewrite (transducer machine) rewrite = [] := by
  intro rewrite membership
  rcases List.mem_append.mp membership with rest | output
  · rcases List.mem_append.mp rest with fixed | transition
    · exact fixedRules_validate machine rewrite fixed
    · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp transition
      exact transitionRule_validates machine index _
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp output
    exact outputRule_validates machine index _

/-- The names of the rewrites. -/
theorem rewrites_names {discipline : Discipline} (machine : Machine discipline) :
    (rewrites machine).map (·.name) =
      ["Feed", "EmitValue", "EmitRest", "FeedControl", "DeltaControl", "OutControl"] ++
        (List.range machine.transitions.length).map
          (fun index => "Transition" ++ toString index) ++
        (List.range machine.outputs.length).map (fun index => "Reading" ++ toString index) := by
  unfold rewrites
  rw [List.map_append, List.map_append]
  congr 1
  · congr 1
    apply List.ext_getElem
    · simp
    · intro index first second
      simp [transitionRule]
  · apply List.ext_getElem
    · simp
    · intro index first second
      simp [outputRule]

theorem rewrites_names_nodup {discipline : Discipline} (machine : Machine discipline) :
    ((rewrites machine).map (·.name)).Nodup := by
  rw [rewrites_names]
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨by decide,
    DecimalNames.prefixed_range_nodup _ _, ?_⟩, DecimalNames.prefixed_range_nodup _ _, ?_⟩
  · intro fixed fixedMember generated generatedMember
    obtain ⟨index, -, rfl⟩ := List.mem_map.mp generatedMember
    intro same
    revert fixedMember
    rw [same]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (literal | literal | literal | literal | literal | literal) <;>
      exact DecimalNames.prefixed_ne_literal "Transition" _ _
        (by intro tail same; simp at same) literal
  · intro earlier earlierMember generated generatedMember
    obtain ⟨second, -, rfl⟩ := List.mem_map.mp generatedMember
    rcases List.mem_append.mp earlierMember with fixed | transition
    · intro same
      revert fixed
      rw [same]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (literal | literal | literal | literal | literal | literal) <;>
        exact DecimalNames.prefixed_ne_literal "Reading" _ _
          (by intro tail same; simp at same) literal
    · obtain ⟨first, -, rfl⟩ := List.mem_map.mp transition
      apply DecimalNames.literal_ne (leftChars := "Transition".toList)
        (rightChars := "Reading".toList) rfl rfl
      intro leftTail rightTail same
      simp at same

/-- The presentation of every transducer passes the declaration gate. -/
theorem transducer_validate_eq_nil {discipline : Discipline} (machine : Machine discipline) :
    (transducer machine).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · show (["State", "Input", "Output", "Stream", "Config"] : List String).Nodup
    decide
  · show ((terms discipline).map (·.label)).Nodup
    cases discipline <;> decide
  · exact rewrites_names_nodup machine
  · show ∀ term ∈ terms discipline,
      term.category ∈ (["State", "Input", "Output", "Stream", "Config"] : List String)
    cases discipline <;> decide
  · show ∀ term ∈ terms discipline, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ (["State", "Input", "Output", "Stream", "Config"] : List String)
    cases discipline <;> decide
  · show ∀ term ∈ terms discipline, term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param))
    cases discipline <;> decide +kernel
  · exact rewrites_validate machine

/-! ## The shape of the rules -/

/-- Every rewrite of a transducer is an ordinary constructor application headed
by one of four constructors: the feed, the emission, the transition function
or the output function. -/
theorem rewrites_headed {discipline : Discipline} (machine : Machine discipline) :
    ∀ rewrite ∈ (transducer machine).rewrites,
      ∃ label arguments, rewrite.left = .apply label arguments ∧
        label ∈ ["Feed", "Emit", "Delta", "Out"] := by
  intro rewrite membership
  rcases List.mem_append.mp membership with rest | output
  · rcases List.mem_append.mp rest with fixed | transition
    · simp only [fixedRules, List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨"Feed", _, rfl, by decide⟩
      · exact ⟨"Emit", _, rfl, by decide⟩
      · exact ⟨"Emit", _, rfl, by decide⟩
      · exact ⟨"Feed", _, rfl, by decide⟩
      · exact ⟨"Delta", _, rfl, by decide⟩
      · cases discipline <;> exact ⟨"Out", _, rfl, by decide⟩
    · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp transition
      exact ⟨"Delta", _, rfl, by decide⟩
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp output
    cases discipline
    · exact ⟨"Out", _, rfl, by decide⟩
    · exact ⟨"Out", _, rfl, by decide⟩

/-! ## Two machines that run -/

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- A Moore machine tracking the parity of the ones it has read.  Its output is
its state. -/
def parity : Machine .moore where
  transitions :=
    [ { state := 0, input := 0, next := 0 }, { state := 0, input := 1, next := 1 },
      { state := 1, input := 0, next := 1 }, { state := 1, input := 1, next := 0 } ]
  outputs := [(0, 0), (1, 1)]

/-- A Mealy machine reporting whether the symbol it reads differs from the one
before.  Its state is the last symbol read; its output depends on the state
and on the symbol being consumed. -/
def change : Machine .mealy where
  transitions :=
    [ { state := 0, input := 0, next := 0 }, { state := 0, input := 1, next := 1 },
      { state := 1, input := 0, next := 0 }, { state := 1, input := 1, next := 1 } ]
  outputs := [((0, 0), 0), ((0, 1), 1), ((1, 0), 1), ((1, 1), 0)]

/-- The even state fed a one. -/
def parityStart : Pattern := feed (stateTerm 0) (next (inputTerm 1) done)

/-- The control has met the stream: an output call is emitted and the next
state awaits evaluation. -/
def parityMet : Pattern :=
  emit (.apply "Out" [stateTerm 0]) (feed (delta (stateTerm 0) (inputTerm 1)) done)

/-- The emitted output has been evaluated from the state alone. -/
def parityEmitted : Pattern :=
  emit (outputTerm 0) (feed (delta (stateTerm 0) (inputTerm 1)) done)

/-- The next state has been evaluated. -/
def parityDone : Pattern := emit (outputTerm 0) (feed (stateTerm 1) done)

theorem parity_meets : Step base (transducer parity) parityStart parityMet :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

theorem parity_emits : Step base (transducer parity) parityMet parityEmitted :=
  exists_mem_rewriteAt_iff_step.mp ⟨2, by decide +kernel⟩

theorem parity_advances : Step base (transducer parity) parityEmitted parityDone :=
  exists_mem_rewriteAt_iff_step.mp ⟨3, by decide +kernel⟩

/-- State zero fed a one. -/
def changeStart : Pattern := feed (stateTerm 0) (next (inputTerm 1) done)

/-- The control has met the stream: the output call mentions the consumed
symbol. -/
def changeMet : Pattern :=
  emit (.apply "Out" [stateTerm 0, inputTerm 1])
    (feed (delta (stateTerm 0) (inputTerm 1)) done)

/-- The emitted output has been evaluated from the state and the symbol. -/
def changeEmitted : Pattern :=
  emit (outputTerm 1) (feed (delta (stateTerm 0) (inputTerm 1)) done)

theorem change_meets : Step base (transducer change) changeStart changeMet :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

theorem change_emits : Step base (transducer change) changeMet changeEmitted :=
  exists_mem_rewriteAt_iff_step.mp ⟨2, by decide +kernel⟩

end Mettapedia.Languages.Transducers
