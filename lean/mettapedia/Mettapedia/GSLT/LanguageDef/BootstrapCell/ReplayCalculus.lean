import Mettapedia.GSLT.LanguageDef.BootstrapCell.Replay
import Mettapedia.Util.LinearHash

/-!
# The reflexive cell: replay presented as a calculus that NIK checks

NIK checks a raw certificate for a goal by replaying it against a validated
calculus.  This module presents that checking judgment itself as an ordinary
calculus, `Accepts(goal, code)`, whose rules are NIK's replay rules for the
checked calculus, and proves that the generic checker, run on the
presentation, agrees exactly with the generic checker run on the calculus.

**The presentation.**  For every rule `ρ` of the checked calculus, the replay
calculus has one rule `replayRule ρ` with the same identifier and side
conditions.
* Its formals are `ρ`'s formals followed by one child formal per premise.
* Its premises say that each child code is accepted for the corresponding
  premise of `ρ`.
* Its conclusion says that the certificate code built from the rule atom,
  the arguments and the child codes is accepted for `ρ`'s conclusion.

An argument declared at depth `d` is quoted under `d` canonical binders
(`bindAt`), so that every formal keeps its exact occurrence depth, as the
checker's schema validation requires.

**Codes.**  `quoteProof` sends a raw certificate to its code, and
`replayProof` sends it to the certificate of the replay calculus that checks
it.  The replay certificate is the same tree, with each node's argument
vector extended by the codes of its children.

**The correspondence** (for every validated calculus and every validated
presentation of its replay rules):
* `replay_sound`: every derivation of `Accepts(goal, code)` in the replay
  calculus comes from a raw certificate that the calculus accepts for `goal`,
  whose code is `code`, and whose replay certificate is the derivation's
  erasure;
* `replay_complete`: every derivation of the calculus yields a derivation of
  its acceptance judgment in the replay calculus, with the replay certificate
  as erasure;
* `checkRaw_replayProof`: the generic checker accepts the replay certificate
  for the acceptance judgment exactly when it accepts the certificate for the
  goal.

The replay calculus is itself a validated calculus, so the construction
iterates: each level presents the checking of the level below, and no level
presents its own checking.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## The presentation -/

/-- The judgment head and the certificate constructor of a replay calculus.
Different levels of a tower use different judgment heads. -/
structure CellProfile where
  accepts : String
  certificate : String
deriving Repr, DecidableEq

/-- `depth` canonical binders around a pattern. -/
def bindAt : Nat → Pattern → Pattern
  | 0, pattern => pattern
  | depth + 1, pattern => .lambda none (bindAt depth pattern)

/-- A rule identifier as a nullary constructor. -/
def ruleAtom (id : RuleId) : Pattern := .apply id.value []

/-- Name of the child formal with the given index. -/
def childName (index : Nat) : String := "#" ++ toString index

/-- One child formal per premise, at depth zero, numbered from `next`. -/
def childFormalsFrom (next : Nat) : List Pattern → List (String × Nat)
  | [] => []
  | _ :: premises => (childName next, 0) :: childFormalsFrom (next + 1) premises

/-- Each formal as a pattern at its declared depth. -/
def boundVariables (formals : List (String × Nat)) : List Pattern :=
  formals.map fun formal => bindAt formal.2 (.fvar formal.1)

/-- Quote an argument vector against the declared depths of its formals. -/
def bindArguments : List Nat → List Pattern → List Pattern
  | depth :: depths, argument :: arguments =>
      bindAt depth argument :: bindArguments depths arguments
  | _, arguments => arguments

/-- The declared depths of a rule's formals, read from the checked calculus. -/
def formalDepths (definition : CalculusLanguageDef) (id : RuleId) : List Nat :=
  match definition.lookupRule? id with
  | some rule => rule.metavariables.map (·.2)
  | none => []

section Presentation

variable (profile : CellProfile)

/-- The acceptance judgment `Accepts(goal, code)`. -/
def acceptsJudgment (goal code : Pattern) : Pattern :=
  .apply profile.accepts [goal, code]

/-- The code of one certificate node. -/
def certificateCode (id : RuleId) (arguments children : List Pattern) : Pattern :=
  .apply profile.certificate
    [ruleAtom id, .collection .vec arguments none, .collection .vec children none]

/-- The replay premises: each child code is accepted for its premise. -/
def replayPremisesFrom (next : Nat) : List Pattern → List Pattern
  | [] => []
  | premise :: premises =>
      acceptsJudgment profile premise (.fvar (childName next)) ::
        replayPremisesFrom (next + 1) premises

/-- The replay rule of one inference rule. -/
def replayRule (rule : RuleSchema) : RuleSchema where
  id := rule.id
  metavariables :=
    rule.metavariables ++ childFormalsFrom rule.metavariables.length rule.premises
  premises := replayPremisesFrom profile rule.metavariables.length rule.premises
  conclusion :=
    acceptsJudgment profile rule.conclusion
      (certificateCode profile rule.id (boundVariables rule.metavariables)
        (boundVariables (childFormalsFrom rule.metavariables.length rule.premises)))
  sideConditions := rule.sideConditions

/-- The replay rules of a rule table, in the same order. -/
def replayRules (rules : List RuleSchema) : List RuleSchema :=
  rules.map (replayRule profile)

mutual

/-- The code of a raw certificate. -/
def quoteProof (definition : CalculusLanguageDef) : RawProof → Pattern
  | .node label children =>
      certificateCode profile label.ruleId
        (bindArguments (formalDepths definition label.ruleId) label.arguments)
        (quoteProofs definition children)
termination_by structural certificate => certificate

/-- Codes of ordered children. -/
def quoteProofs (definition : CalculusLanguageDef) : List RawProof → List Pattern
  | [] => []
  | child :: children => quoteProof definition child :: quoteProofs definition children
termination_by structural children => children

end

mutual

/-- The replay certificate: the same tree, each argument vector extended by
the codes of the node's children. -/
def replayProof (definition : CalculusLanguageDef) : RawProof → RawProof
  | .node label children =>
      .node
        { ruleId := label.ruleId
          arguments := label.arguments ++ quoteProofs profile definition children }
        (replayProofs definition children)
termination_by structural certificate => certificate

/-- Replay certificates of ordered children. -/
def replayProofs (definition : CalculusLanguageDef) : List RawProof → List RawProof
  | [] => []
  | child :: children => replayProof definition child :: replayProofs definition children
termination_by structural children => children

end

@[simp] theorem quoteProof_node (definition : CalculusLanguageDef) (label : RuleInstance)
    (children : List RawProof) :
    quoteProof profile definition (.node label children) =
      certificateCode profile label.ruleId
        (bindArguments (formalDepths definition label.ruleId) label.arguments)
        (quoteProofs profile definition children) := by
  rw [quoteProof]

@[simp] theorem quoteProofs_nil (definition : CalculusLanguageDef) :
    quoteProofs profile definition [] = [] := by
  rw [quoteProofs]

@[simp] theorem quoteProofs_cons (definition : CalculusLanguageDef) (child : RawProof)
    (children : List RawProof) :
    quoteProofs profile definition (child :: children) =
      quoteProof profile definition child :: quoteProofs profile definition children := by
  rw [quoteProofs]

@[simp] theorem replayProof_node (definition : CalculusLanguageDef) (label : RuleInstance)
    (children : List RawProof) :
    replayProof profile definition (.node label children) =
      .node
        { ruleId := label.ruleId
          arguments := label.arguments ++ quoteProofs profile definition children }
        (replayProofs profile definition children) := by
  rw [replayProof]

@[simp] theorem replayProofs_nil (definition : CalculusLanguageDef) :
    replayProofs profile definition [] = [] := by
  rw [replayProofs]

@[simp] theorem replayProofs_cons (definition : CalculusLanguageDef) (child : RawProof)
    (children : List RawProof) :
    replayProofs profile definition (child :: children) =
      replayProof profile definition child :: replayProofs profile definition children := by
  rw [replayProofs]

theorem quoteProofs_eq_map (definition : CalculusLanguageDef) :
    (children : List RawProof) →
      quoteProofs profile definition children = children.map (quoteProof profile definition)
  | [] => by rw [quoteProofs_nil, List.map_nil]
  | child :: children => by
      rw [quoteProofs_cons, List.map_cons, quoteProofs_eq_map definition children]

theorem replayProofs_eq_map (definition : CalculusLanguageDef) :
    (children : List RawProof) →
      replayProofs profile definition children = children.map (replayProof profile definition)
  | [] => by rw [replayProofs_nil, List.map_nil]
  | child :: children => by
      rw [replayProofs_cons, List.map_cons, replayProofs_eq_map definition children]

end Presentation

/-! ## Small facts about the construction -/

theorem bindAt_injective (depth : Nat) : Function.Injective (bindAt depth) := by
  induction depth with
  | zero => intro first second equal; exact equal
  | succ depth inductionHypothesis =>
      intro first second equal
      simp only [bindAt, Pattern.lambda.injEq, true_and] at equal
      exact inductionHypothesis equal

theorem bindArguments_length : (depths : List Nat) → (arguments : List Pattern) →
    (bindArguments depths arguments).length = arguments.length
  | _ :: depths, _ :: arguments => by
      simp [bindArguments, bindArguments_length depths arguments]
  | [], _ => by simp [bindArguments]
  | _ :: _, [] => by simp [bindArguments]

theorem bindArguments_injective (depths : List Nat) :
    (first second : List Pattern) →
      bindArguments depths first = bindArguments depths second → first = second := by
  induction depths with
  | nil => intro first second equal; simpa [bindArguments] using equal
  | cons depth depths inductionHypothesis =>
      intro first second equal
      cases first with
      | nil =>
          cases second with
          | nil => rfl
          | cons _ _ => simp [bindArguments] at equal
      | cons argument arguments =>
          cases second with
          | nil => simp [bindArguments] at equal
          | cons argument' arguments' =>
              simp only [bindArguments, List.cons.injEq] at equal
              rw [bindAt_injective depth equal.1,
                inductionHypothesis arguments arguments' equal.2]

theorem childFormalsFrom_length : (next : Nat) → (premises : List Pattern) →
    (childFormalsFrom next premises).length = premises.length
  | _, [] => rfl
  | next, _ :: premises => by
      simp [childFormalsFrom, childFormalsFrom_length (next + 1) premises]

theorem isGroundAt_bindAt : (depth offset : Nat) → (pattern : Pattern) →
    (bindAt depth pattern).isGroundAt offset = pattern.isGroundAt (offset + depth)
  | 0, offset, pattern => by simp [bindAt]
  | depth + 1, offset, pattern => by
      simp only [bindAt, Pattern.isGroundAt]
      rw [isGroundAt_bindAt depth (offset + 1) pattern]
      congr 1
      omega

theorem hasCanonicalBinderMetadata_bindAt : (depth : Nat) → (pattern : Pattern) →
    (bindAt depth pattern).hasCanonicalBinderMetadata = pattern.hasCanonicalBinderMetadata
  | 0, pattern => by simp [bindAt]
  | depth + 1, pattern => by
      simp only [bindAt, Pattern.hasCanonicalBinderMetadata, Option.isNone_none,
        Bool.true_and]
      exact hasCanonicalBinderMetadata_bindAt depth pattern


/-! ## Length bookkeeping without classical arithmetic lemmas -/

theorem length_nil_ne_cons {α β : Type} {head : β} {tail : List β} :
    ([] : List α).length ≠ (head :: tail).length :=
  fun equal => Nat.succ_ne_zero _ equal.symm

theorem length_cons_ne_nil {α β : Type} {head : α} {tail : List α} :
    (head :: tail).length ≠ ([] : List β).length :=
  fun equal => Nat.succ_ne_zero _ equal

theorem length_tail_eq {α β : Type} {head : α} {tail : List α} {head' : β} {tail' : List β}
    (equal : (head :: tail).length = (head' :: tail').length) : tail.length = tail'.length :=
  Nat.succ.inj equal

/-! ## Rule lookup in a replay table -/

theorem lookupRule?_replayRules (profile : CellProfile) (definition : CalculusLanguageDef)
    (cell : CalculusLanguageDef)
    (rulesEq : cell.rules = replayRules profile definition.rules) (id : RuleId) :
    cell.lookupRule? id = (definition.lookupRule? id).map (replayRule profile) := by
  unfold CalculusLanguageDef.lookupRule?
  rw [rulesEq, replayRules, List.find?_map]
  rfl

theorem lookupRule?_id {definition : CalculusLanguageDef} {id : RuleId} {rule : RuleSchema}
    (lookup : definition.lookupRule? id = some rule) : rule.id = id := by
  unfold CalculusLanguageDef.lookupRule? at lookup
  simpa using List.find?_some lookup

theorem lookupRule?_mem {definition : CalculusLanguageDef} {id : RuleId} {rule : RuleSchema}
    (lookup : definition.lookupRule? id = some rule) : rule ∈ definition.rules := by
  unfold CalculusLanguageDef.lookupRule? at lookup
  exact List.mem_of_find?_eq_some lookup

theorem formalDepths_of_lookup {definition : CalculusLanguageDef} {id : RuleId}
    {rule : RuleSchema} (lookup : definition.lookupRule? id = some rule)
    :
    formalDepths definition id = rule.metavariables.map (·.2) := by
  rw [formalDepths, lookup]

/-! ## Argument environments that extend a prefix -/

theorem lookupArgumentAt?_append_of_mem :
    (formals : List (String × Nat)) → (arguments : List Pattern) →
    (extraFormals : List (String × Nat)) → (extraArguments : List Pattern) →
    (name : String) → (depth : Nat) →
    (name, depth) ∈ formals → formals.length = arguments.length →
      lookupArgumentAt? (formals ++ extraFormals) (arguments ++ extraArguments) name depth =
        lookupArgumentAt? formals arguments name depth
  | [], _, _, _, _, _, member, _ => nomatch member
  | _ :: _, [], _, _, _, _, _, lengths => absurd lengths length_cons_ne_nil
  | formal :: formals, argument :: arguments, extraFormals, extraArguments,
      name, depth, member, lengths => by
      simp only [List.cons_append, lookupArgumentAt?]
      by_cases found : formal = (name, depth)
      · rw [if_pos found, if_pos found]
      · rw [if_neg found, if_neg found]
        have member' : (name, depth) ∈ formals := by
          rcases List.mem_cons.mp member with equal | member'
          · exact absurd equal.symm found
          · exact member'
        exact lookupArgumentAt?_append_of_mem formals arguments extraFormals
          extraArguments name depth member' (length_tail_eq lengths)

theorem lookupArgumentAt?_append_of_not_mem :
    (formals : List (String × Nat)) → (arguments : List Pattern) →
    (extraFormals : List (String × Nat)) → (extraArguments : List Pattern) →
    (name : String) → (depth : Nat) →
    (name, depth) ∉ formals → formals.length = arguments.length →
      lookupArgumentAt? (formals ++ extraFormals) (arguments ++ extraArguments) name depth =
        lookupArgumentAt? extraFormals extraArguments name depth
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, lengths => absurd lengths length_nil_ne_cons
  | _ :: _, [], _, _, _, _, _, lengths => absurd lengths length_cons_ne_nil
  | formal :: formals, argument :: arguments, extraFormals, extraArguments,
      name, depth, absent, lengths => by
      simp only [List.cons_append, lookupArgumentAt?]
      have notHead : formal ≠ (name, depth) := fun equal =>
        absent (equal ▸ List.mem_cons_self)
      rw [if_neg notHead]
      exact lookupArgumentAt?_append_of_not_mem formals arguments extraFormals
        extraArguments name depth (fun member => absent (List.mem_cons_of_mem _ member))
        (length_tail_eq lengths)

theorem lookupArgumentAt?_head (formals : List (String × Nat)) (arguments : List Pattern)
    (name : String) (depth : Nat) (argument : Pattern) :
    lookupArgumentAt? ((name, depth) :: formals) (argument :: arguments) name depth =
      some argument := by
  simp [lookupArgumentAt?]

theorem argumentsValidAt_append :
    (formals : List (String × Nat)) → (arguments : List Pattern) →
    (extraFormals : List (String × Nat)) → (extraArguments : List Pattern) →
    formals.length = arguments.length →
      argumentsValidAt (formals ++ extraFormals) (arguments ++ extraArguments) =
        (argumentsValidAt formals arguments && argumentsValidAt extraFormals extraArguments)
  | [], [], _, _, _ => by simp [argumentsValidAt]
  | [], _ :: _, _, _, lengths => absurd lengths length_nil_ne_cons
  | _ :: _, [], _, _, lengths => absurd lengths length_cons_ne_nil
  | formal :: formals, argument :: arguments, extraFormals, extraArguments, lengths => by
      simp only [List.cons_append, argumentsValidAt]
      rw [argumentsValidAt_append formals arguments extraFormals extraArguments
        (length_tail_eq lengths), Bool.and_assoc]

/-- A successful check against a concatenated formal list splits its
arguments at the length of the first part. -/
theorem argumentsValidAt_split (formals extraFormals : List (String × Nat))
    (arguments : List Pattern)
    (valid : argumentsValidAt (formals ++ extraFormals) arguments = true) :
    arguments = arguments.take formals.length ++ arguments.drop formals.length ∧
      (arguments.take formals.length).length = formals.length := by
  have lengths := argumentsValidAt_length valid
  refine ⟨(List.take_append_drop _ _).symm, ?_⟩
  rw [List.length_take]
  simp only [List.length_append] at lengths
  omega

theorem getElem?_append_of_isSome {α β : Type} (formals : List α) (arguments extra : List β)
    (lengths : formals.length = arguments.length) {index : Nat}
    (present : (formals[index]?).isSome = true) :
    (arguments ++ extra)[index]? = arguments[index]? := by
  have bound : index < formals.length := by
    by_contra outside
    rw [List.getElem?_eq_none (by omega)] at present
    exact absurd present Bool.false_ne_true
  exact List.getElem?_append_left (by omega)

theorem sideCondition_holds_append (formals : List (String × Nat))
    (arguments extra : List Pattern) (lengths : formals.length = arguments.length)
    (condition : RuleSideCondition)
    (valid : RuleSideCondition.isValidFor formals condition = true) :
    RuleSideCondition.holds (arguments ++ extra) condition =
      RuleSideCondition.holds arguments condition := by
  cases condition with
  | explicitSubstitution depth body replacement result =>
      simp only [RuleSideCondition.isValidFor] at valid
      have bodySome : (formals[body]?).isSome = true := by
        cases h : formals[body]? <;> simp_all
      have replacementSome : (formals[replacement]?).isSome = true := by
        cases h : formals[replacement]? <;> cases formals[body]? <;> simp_all
      have resultSome : (formals[result]?).isSome = true := by
        cases h : formals[result]? <;> cases formals[body]? <;>
          cases formals[replacement]? <;> simp_all
      simp only [RuleSideCondition.holds,
        getElem?_append_of_isSome formals arguments extra lengths bodySome,
        getElem?_append_of_isSome formals arguments extra lengths replacementSome,
        getElem?_append_of_isSome formals arguments extra lengths resultSome]
  | unusedBinderElimination depth body result =>
      simp only [RuleSideCondition.isValidFor] at valid
      have bodySome : (formals[body]?).isSome = true := by
        cases h : formals[body]? <;> simp_all
      have resultSome : (formals[result]?).isSome = true := by
        cases h : formals[result]? <;> cases formals[body]? <;> simp_all
      simp only [RuleSideCondition.holds,
        getElem?_append_of_isSome formals arguments extra lengths bodySome,
        getElem?_append_of_isSome formals arguments extra lengths resultSome]

/-! ## Schema instantiation in an extended environment -/

section Instantiation

variable (formals : List (String × Nat)) (arguments : List Pattern)

theorem instantiate_bvar (depth index : Nat) :
    instantiateSchemaAt? formals arguments depth (.bvar index) = some (.bvar index) := by
  rw [instantiateSchemaAt?]

theorem instantiate_fvar (depth : Nat) (name : String) :
    instantiateSchemaAt? formals arguments depth (.fvar name) =
      lookupArgumentAt? formals arguments name depth := by
  rw [instantiateSchemaAt?]

theorem instantiate_apply (depth : Nat) (constructor : String) (schemas : List Pattern) :
    instantiateSchemaAt? formals arguments depth (.apply constructor schemas) =
      (instantiateSchemasAt? formals arguments depth schemas).map (.apply constructor) := by
  rw [instantiateSchemaAt?]
  cases instantiateSchemasAt? formals arguments depth schemas <;> rfl

theorem instantiate_lambda (depth : Nat) (binder : Option String) (body : Pattern) :
    instantiateSchemaAt? formals arguments depth (.lambda binder body) =
      (instantiateSchemaAt? formals arguments (depth + 1) body).map (.lambda binder) := by
  rw [instantiateSchemaAt?]
  cases instantiateSchemaAt? formals arguments (depth + 1) body <;> rfl

theorem instantiate_multiLambda (depth arity : Nat) (binders : List String) (body : Pattern) :
    instantiateSchemaAt? formals arguments depth (.multiLambda arity binders body) =
      (instantiateSchemaAt? formals arguments (depth + arity) body).map
        (.multiLambda arity binders) := by
  rw [instantiateSchemaAt?]
  cases instantiateSchemaAt? formals arguments (depth + arity) body <;> rfl

theorem instantiate_subst (depth : Nat) (body replacement : Pattern) :
    instantiateSchemaAt? formals arguments depth (.subst body replacement) =
      (instantiateSchemaAt? formals arguments (depth + 1) body).bind fun bodyResult =>
        (instantiateSchemaAt? formals arguments depth replacement).map (.subst bodyResult) := by
  rw [instantiateSchemaAt?]
  cases instantiateSchemaAt? formals arguments (depth + 1) body <;>
    cases instantiateSchemaAt? formals arguments depth replacement <;> rfl

theorem instantiate_collection_none (depth : Nat) (collectionType : CollType)
    (schemas : List Pattern) :
    instantiateSchemaAt? formals arguments depth (.collection collectionType schemas none) =
      (instantiateSchemasAt? formals arguments depth schemas).map
        (fun results => .collection collectionType results none) := by
  rw [instantiateSchemaAt?]
  cases instantiateSchemasAt? formals arguments depth schemas <;> rfl

theorem instantiate_collection_some (depth : Nat) (collectionType : CollType)
    (schemas : List Pattern) (rest : String) :
    instantiateSchemaAt? formals arguments depth
        (.collection collectionType schemas (some rest)) = none := by
  rw [instantiateSchemaAt?]

theorem instantiates_nil (depth : Nat) :
    instantiateSchemasAt? formals arguments depth [] = some [] := by
  rw [instantiateSchemasAt?]

theorem instantiates_cons (depth : Nat) (schema : Pattern) (schemas : List Pattern) :
    instantiateSchemasAt? formals arguments depth (schema :: schemas) =
      (instantiateSchemaAt? formals arguments depth schema).bind fun result =>
        (instantiateSchemasAt? formals arguments depth schemas).map (result :: ·) := by
  rw [instantiateSchemasAt?]
  cases instantiateSchemaAt? formals arguments depth schema <;>
    cases instantiateSchemasAt? formals arguments depth schemas <;> rfl

end Instantiation

theorem instantiate_bindAt (formals : List (String × Nat)) (arguments : List Pattern) :
    (depth offset : Nat) → (name : String) →
      instantiateSchemaAt? formals arguments offset (bindAt depth (.fvar name)) =
        (lookupArgumentAt? formals arguments name (offset + depth)).map (bindAt depth)
  | 0, offset, name => by
      rw [bindAt, instantiate_fvar]
      cases lookupArgumentAt? formals arguments name (offset + 0) <;> rfl
  | depth + 1, offset, name => by
      rw [bindAt, instantiate_lambda, instantiate_bindAt formals arguments depth (offset + 1) name]
      rw [show offset + 1 + depth = offset + (depth + 1) by omega]
      cases lookupArgumentAt? formals arguments name (offset + (depth + 1)) <;> rfl

theorem patternMetavariableOccurrencesAt_fvar (depth : Nat) (name : String) :
    patternMetavariableOccurrencesAt depth (.fvar name) = [(name, depth)] := by
  rw [patternMetavariableOccurrencesAt]

mutual

/-- Instantiation of a schema whose formal occurrences all lie in a prefix of
the environment is unchanged by extending the environment. -/
theorem instantiateSchemaAt?_append (formals extraFormals : List (String × Nat))
    (arguments extraArguments : List Pattern) (lengths : formals.length = arguments.length) :
    (depth : Nat) → (schema : Pattern) →
    (∀ occurrence ∈ patternMetavariableOccurrencesAt depth schema, occurrence ∈ formals) →
      instantiateSchemaAt? (formals ++ extraFormals) (arguments ++ extraArguments) depth schema =
        instantiateSchemaAt? formals arguments depth schema
  | depth, .bvar index, _ => by rw [instantiate_bvar, instantiate_bvar]
  | depth, .fvar name, inScope => by
      rw [instantiate_fvar, instantiate_fvar]
      apply lookupArgumentAt?_append_of_mem _ _ _ _ _ _ _ lengths
      apply inScope
      rw [patternMetavariableOccurrencesAt_fvar]
      exact List.mem_singleton_self _
  | depth, .apply constructor schemas, inScope => by
      rw [instantiate_apply, instantiate_apply,
        instantiateSchemasAt?_append formals extraFormals arguments extraArguments lengths
          depth schemas (by
            intro occurrence member
            apply inScope
            rw [patternMetavariableOccurrencesAt]
            exact member)]
  | depth, .lambda binder body, inScope => by
      rw [instantiate_lambda, instantiate_lambda,
        instantiateSchemaAt?_append formals extraFormals arguments extraArguments lengths
          (depth + 1) body (by
            intro occurrence member
            apply inScope
            rw [patternMetavariableOccurrencesAt]
            exact member)]
  | depth, .multiLambda arity binders body, inScope => by
      rw [instantiate_multiLambda, instantiate_multiLambda,
        instantiateSchemaAt?_append formals extraFormals arguments extraArguments lengths
          (depth + arity) body (by
            intro occurrence member
            apply inScope
            rw [patternMetavariableOccurrencesAt]
            exact member)]
  | depth, .subst body replacement, inScope => by
      rw [instantiate_subst, instantiate_subst,
        instantiateSchemaAt?_append formals extraFormals arguments extraArguments lengths
          (depth + 1) body (by
            intro occurrence member
            apply inScope
            rw [patternMetavariableOccurrencesAt]
            exact List.mem_append_left _ member),
        instantiateSchemaAt?_append formals extraFormals arguments extraArguments lengths
          depth replacement (by
            intro occurrence member
            apply inScope
            rw [patternMetavariableOccurrencesAt]
            exact List.mem_append_right _ member)]
  | depth, .collection collectionType schemas none, inScope => by
      rw [instantiate_collection_none, instantiate_collection_none,
        instantiateSchemasAt?_append formals extraFormals arguments extraArguments lengths
          depth schemas (by
            intro occurrence member
            apply inScope
            rw [patternMetavariableOccurrencesAt]
            exact member)]
  | depth, .collection collectionType schemas (some rest), _ => by
      rw [instantiate_collection_some, instantiate_collection_some]
termination_by structural _ schema => schema

/-- The same for ordered schema lists. -/
theorem instantiateSchemasAt?_append (formals extraFormals : List (String × Nat))
    (arguments extraArguments : List Pattern) (lengths : formals.length = arguments.length) :
    (depth : Nat) → (schemas : List Pattern) →
    (∀ occurrence ∈ patternsMetavariableOccurrencesAt depth schemas, occurrence ∈ formals) →
      instantiateSchemasAt? (formals ++ extraFormals) (arguments ++ extraArguments) depth
          schemas =
        instantiateSchemasAt? formals arguments depth schemas
  | depth, [], _ => by rw [instantiates_nil, instantiates_nil]
  | depth, schema :: schemas, inScope => by
      rw [instantiates_cons, instantiates_cons,
        instantiateSchemaAt?_append formals extraFormals arguments extraArguments lengths
          depth schema (by
            intro occurrence member
            apply inScope
            rw [patternsMetavariableOccurrencesAt]
            exact List.mem_append_left _ member),
        instantiateSchemasAt?_append formals extraFormals arguments extraArguments lengths
          depth schemas (by
            intro occurrence member
            apply inScope
            rw [patternsMetavariableOccurrencesAt]
            exact List.mem_append_right _ member)]
termination_by structural _ schemas => schemas

end

/-! ## The local step of a replay rule -/

/-- The facts about one inference rule that the replay correspondence uses:
the replay rule's formal names are distinct, every formal occurrence of the
rule lies among its own formals, and every side condition indexes its own
formals. -/
structure ReplayRuleFacts (rule : RuleSchema) : Prop where
  namesNodup :
    ((rule.metavariables ++ childFormalsFrom rule.metavariables.length rule.premises).map
      Prod.fst).Nodup
  premisesInScope : ∀ premise ∈ rule.premises,
    ∀ occurrence ∈ patternMetavariableOccurrencesAt 0 premise,
      occurrence ∈ rule.metavariables
  conclusionInScope : ∀ occurrence ∈ patternMetavariableOccurrencesAt 0 rule.conclusion,
    occurrence ∈ rule.metavariables
  sideConditionsValid : ∀ condition ∈ rule.sideConditions,
    RuleSideCondition.isValidFor rule.metavariables condition = true

theorem not_mem_of_nodup_names {formals rest : List (String × Nat)} {name : String}
    {depth : Nat}
    (nodup : ((formals ++ (name, depth) :: rest).map Prod.fst).Nodup) :
    (name, depth) ∉ formals := by
  intro member
  rw [List.map_append, List.nodup_append] at nodup
  exact nodup.2.2 name (List.mem_map_of_mem (f := Prod.fst) member) name
    (by simp) rfl

/-- The pattern of a middle segment of formals, instantiated in an
environment whose names are distinct, is the matching segment of arguments
quoted at their depths. -/
theorem instantiate_boundVariables :
    (prefixFormals : List (String × Nat)) → (prefixArguments : List Pattern) →
    (formals : List (String × Nat)) → (arguments : List Pattern) →
    (extraFormals : List (String × Nat)) → (extraArguments : List Pattern) →
    prefixFormals.length = prefixArguments.length → formals.length = arguments.length →
    ((prefixFormals ++ formals).map Prod.fst).Nodup →
      instantiateSchemasAt? (prefixFormals ++ formals ++ extraFormals)
          (prefixArguments ++ arguments ++ extraArguments) 0 (boundVariables formals) =
        some (bindArguments (formals.map (·.2)) arguments)
  | _, _, [], [], _, _, _, _, _ => by
      simp [boundVariables, bindArguments, instantiates_nil]
  | _, _, [], _ :: _, _, _, _, lengths, _ => absurd lengths length_nil_ne_cons
  | _, _, _ :: _, [], _, _, _, lengths, _ => absurd lengths length_cons_ne_nil
  | prefixFormals, prefixArguments, (name, depth) :: formals, argument :: arguments,
      extraFormals, extraArguments, prefixLengths, lengths, nodup => by
      have absent : (name, depth) ∉ prefixFormals := not_mem_of_nodup_names nodup
      have headLookup :
          lookupArgumentAt? (prefixFormals ++ (name, depth) :: formals ++ extraFormals)
              (prefixArguments ++ argument :: arguments ++ extraArguments) name depth =
            some argument := by
        rw [List.append_assoc, List.append_assoc,
          lookupArgumentAt?_append_of_not_mem _ _ _ _ _ _ absent prefixLengths]
        exact lookupArgumentAt?_head _ _ _ _ _
      have tail := instantiate_boundVariables (prefixFormals ++ [(name, depth)])
        (prefixArguments ++ [argument]) formals arguments extraFormals extraArguments
        (by rw [List.length_append, List.length_append, prefixLengths]; rfl)
        (length_tail_eq lengths) (by rw [List.append_assoc]; exact nodup)
      simp only [List.append_assoc, List.singleton_append] at tail
      simp only [boundVariables, List.map_cons, instantiates_cons]
      rw [instantiate_bindAt, Nat.zero_add, headLookup]
      simp only [Option.map_some, Option.bind_some]
      rw [show List.map (fun formal : String × Nat => bindAt formal.2 (.fvar formal.1)) formals =
          boundVariables formals from rfl]
      simp only [List.append_assoc, List.cons_append] at tail ⊢
      rw [tail]
      rfl

theorem childFormalsFrom_depths : (next : Nat) → (premises : List Pattern) →
    (childFormalsFrom next premises).map (·.2) = List.replicate premises.length 0
  | _, [] => rfl
  | next, _ :: premises => by
      simp [childFormalsFrom, childFormalsFrom_depths (next + 1) premises,
        List.replicate_succ]

theorem bindArguments_zeros : (count : Nat) → (arguments : List Pattern) →
    arguments.length = count → bindArguments (List.replicate count 0) arguments = arguments
  | 0, [], _ => rfl
  | 0, _ :: _, lengths => absurd lengths (Nat.succ_ne_zero _)
  | _ + 1, [], lengths => absurd lengths.symm (Nat.succ_ne_zero _)
  | count + 1, argument :: arguments, lengths => by
      simp only [List.replicate_succ, bindArguments, bindAt]
      rw [bindArguments_zeros count arguments (Nat.succ.inj lengths)]

theorem all_congr_of_mem {α : Type} {values : List α} {first second : α → Bool}
    (pointwise : ∀ value ∈ values, first value = second value) :
    values.all first = values.all second := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.all_cons, pointwise value List.mem_cons_self,
        inductionHypothesis fun other member => pointwise other (List.mem_cons_of_mem _ member)]

section Step

variable (profile : CellProfile)

/-- The replay premises instantiate to the acceptance of each child code for
the corresponding instantiated premise. -/
theorem instantiate_replayPremises
    (formals : List (String × Nat)) (arguments : List Pattern)
    (lengths : formals.length = arguments.length) :
    (kidPrefix : List (String × Nat)) → (codePrefix : List Pattern) →
    (next : Nat) → (premises : List Pattern) → (codes : List Pattern) →
    kidPrefix.length = codePrefix.length →
    (childFormalsFrom next premises).length = codes.length →
    ((formals ++ kidPrefix ++ childFormalsFrom next premises).map Prod.fst).Nodup →
    (∀ premise ∈ premises, ∀ occurrence ∈ patternMetavariableOccurrencesAt 0 premise,
      occurrence ∈ formals) →
      instantiateSchemasAt? (formals ++ (kidPrefix ++ childFormalsFrom next premises))
          (arguments ++ (codePrefix ++ codes)) 0 (replayPremisesFrom profile next premises) =
        (instantiateSchemasAt? formals arguments 0 premises).map
          (fun results => List.zipWith (acceptsJudgment profile) results codes)
  | _, _, _, [], [], _, _, _, _ => by
      simp [replayPremisesFrom, instantiates_nil]
  | _, _, _, [], _ :: _, _, codeLengths, _, _ => absurd codeLengths length_nil_ne_cons
  | _, _, _, _ :: _, [], _, codeLengths, _, _ => absurd codeLengths length_cons_ne_nil
  | kidPrefix, codePrefix, next, premise :: premises, code :: codes,
      prefixLengths, codeLengths, nodup, inScope => by
      have premiseInstance :
          instantiateSchemaAt? (formals ++ (kidPrefix ++ childFormalsFrom next (premise :: premises)))
              (arguments ++ (codePrefix ++ code :: codes)) 0 premise =
            instantiateSchemaAt? formals arguments 0 premise :=
        instantiateSchemaAt?_append formals _ arguments _ lengths 0 premise
          (inScope premise List.mem_cons_self)
      have kidAbsent : (childName next, 0) ∉ formals ++ kidPrefix := by
        apply not_mem_of_nodup_names (rest := childFormalsFrom (next + 1) premises)
        exact nodup
      have kidLookup :
          lookupArgumentAt? (formals ++ (kidPrefix ++ childFormalsFrom next (premise :: premises)))
              (arguments ++ (codePrefix ++ code :: codes)) (childName next) 0 = some code := by
        rw [← List.append_assoc, ← List.append_assoc]
        rw [childFormalsFrom, lookupArgumentAt?_append_of_not_mem _ _ _ _ _ _ kidAbsent
          (by rw [List.length_append, List.length_append, lengths, prefixLengths])]
        exact lookupArgumentAt?_head _ _ _ _ _
      have tail := instantiate_replayPremises formals arguments lengths
        (kidPrefix ++ [(childName next, 0)]) (codePrefix ++ [code]) (next + 1) premises codes
        (by rw [List.length_append, List.length_append, prefixLengths]; rfl)
        (length_tail_eq codeLengths)
        (by
          simp only [List.append_assoc, List.singleton_append, childFormalsFrom] at nodup ⊢
          exact nodup)
        (fun premise' member => inScope premise' (List.mem_cons_of_mem _ member))
      simp only [List.append_assoc, List.singleton_append] at tail
      rw [show childFormalsFrom next (premise :: premises) =
          (childName next, 0) :: childFormalsFrom (next + 1) premises from rfl] at premiseInstance kidLookup ⊢
      simp only [replayPremisesFrom, acceptsJudgment, instantiates_cons, instantiate_apply,
        instantiate_fvar]
      rw [premiseInstance, kidLookup, tail, instantiates_nil]
      cases instantiateSchemaAt? formals arguments 0 premise <;>
        cases instantiateSchemasAt? formals arguments 0 premises <;> rfl

/-- The replay conclusion instantiates to the acceptance of the node's code
for the instantiated conclusion. -/
theorem instantiate_replayConclusion (rule : RuleSchema) (facts : ReplayRuleFacts rule)
    (arguments codes : List Pattern) (lengths : rule.metavariables.length = arguments.length)
    (codeLengths : (childFormalsFrom rule.metavariables.length rule.premises).length =
      codes.length) :
    instantiateSchemaAt? (replayRule profile rule).metavariables (arguments ++ codes) 0
        (replayRule profile rule).conclusion =
      (instantiateSchemaAt? rule.metavariables arguments 0 rule.conclusion).map
        (fun conclusion => acceptsJudgment profile conclusion
          (certificateCode profile rule.id
            (bindArguments (rule.metavariables.map (·.2)) arguments) codes)) := by
  have conclusionInstance :=
    instantiateSchemaAt?_append rule.metavariables
      (childFormalsFrom rule.metavariables.length rule.premises) arguments codes lengths 0
      rule.conclusion facts.conclusionInScope
  have argumentVector :=
    instantiate_boundVariables [] [] rule.metavariables arguments
      (childFormalsFrom rule.metavariables.length rule.premises) codes rfl lengths
      (by
        have nodup := facts.namesNodup
        rw [List.map_append] at nodup
        simpa using (List.nodup_append.mp nodup).1)
  have childVector :=
    instantiate_boundVariables rule.metavariables arguments
      (childFormalsFrom rule.metavariables.length rule.premises) codes [] [] lengths
      codeLengths facts.namesNodup
  simp only [List.nil_append] at argumentVector
  simp only [List.append_nil] at childVector
  rw [childFormalsFrom_depths, bindArguments_zeros _ _
    (by rw [← codeLengths, childFormalsFrom_length])] at childVector
  simp only [replayRule, acceptsJudgment, certificateCode, ruleAtom, instantiate_apply,
    instantiates_cons, instantiate_collection_none, instantiates_nil]
  rw [conclusionInstance, argumentVector, childVector]
  cases instantiateSchemaAt? rule.metavariables arguments 0 rule.conclusion <;> rfl

theorem sideConditionsHold_replayRule (rule : RuleSchema) (facts : ReplayRuleFacts rule)
    (arguments codes : List Pattern) (lengths : rule.metavariables.length = arguments.length) :
    RuleSchema.sideConditionsHold (replayRule profile rule) (arguments ++ codes) =
      RuleSchema.sideConditionsHold rule arguments := by
  unfold RuleSchema.sideConditionsHold
  change rule.sideConditions.all (RuleSideCondition.holds (arguments ++ codes)) =
    rule.sideConditions.all (RuleSideCondition.holds arguments)
  exact all_congr_of_mem fun condition member =>
    sideCondition_holds_append rule.metavariables arguments codes lengths condition
      (facts.sideConditionsValid condition member)

/-- **The local step.**  A replay rule instance whose arguments split into the
rule's arguments and one code per premise succeeds exactly when the child
codes are closed and the underlying rule instance succeeds; its premises are
the acceptance judgments of the child codes and its conclusion is the
acceptance judgment of the node's code. -/
theorem instantiateRule?_replay (definition cell : ValidatedCalculusLanguageDef)
    (rulesEq : cell.1.rules = replayRules profile definition.1.rules)
    {id : RuleId} {rule : RuleSchema} (lookup : definition.1.lookupRule? id = some rule)
    (facts : ReplayRuleFacts rule) (arguments codes : List Pattern)
    (lengths : arguments.length = rule.metavariables.length) :
    instantiateRule? cell ⟨id, arguments ++ codes⟩ =
      if argumentsValidAt (childFormalsFrom rule.metavariables.length rule.premises) codes then
        (instantiateRule? definition ⟨id, arguments⟩).map fun result =>
          (List.zipWith (acceptsJudgment profile) result.1 codes,
            acceptsJudgment profile result.2
              (certificateCode profile id
                (bindArguments (rule.metavariables.map (·.2)) arguments) codes))
      else none := by
  have ruleId : rule.id = id := lookupRule?_id lookup
  have cellLookup : cell.1.lookupRule? id = some (replayRule profile rule) := by
    rw [lookupRule?_replayRules profile definition.1 cell.1 rulesEq, lookup]
    rfl
  simp only [instantiateRule?, cellLookup, lookup]
  change (if argumentsValidAt
        (rule.metavariables ++ childFormalsFrom rule.metavariables.length rule.premises)
        (arguments ++ codes) = true then _ else _) = _
  rw [argumentsValidAt_append _ _ _ _ lengths.symm,
    sideConditionsHold_replayRule profile rule facts arguments codes lengths.symm]
  by_cases childrenValid :
      argumentsValidAt (childFormalsFrom rule.metavariables.length rule.premises) codes = true
  · have codeLengths := argumentsValidAt_length childrenValid
    have premisesInstance :=
      instantiate_replayPremises profile rule.metavariables arguments lengths.symm [] []
        rule.metavariables.length rule.premises codes rfl codeLengths
        (by simpa using facts.namesNodup) facts.premisesInScope
    simp only [List.nil_append] at premisesInstance
    have conclusionInstance :=
      instantiate_replayConclusion profile rule facts arguments codes lengths.symm codeLengths
    rw [if_pos childrenValid]
    simp only [childrenValid, Bool.and_true]
    by_cases argumentsValid : argumentsValidAt rule.metavariables arguments = true
    · rw [if_pos argumentsValid, if_pos argumentsValid]
      by_cases sideValid : RuleSchema.sideConditionsHold rule arguments = true
      · rw [if_pos sideValid, if_pos sideValid]
        unfold instantiateSchemas? instantiateSchema?
        change (do
            let premises ← instantiateSchemasAt?
              (rule.metavariables ++ childFormalsFrom rule.metavariables.length rule.premises)
              (arguments ++ codes) 0 (replayPremisesFrom profile rule.metavariables.length
                rule.premises)
            let conclusion ← instantiateSchemaAt? (replayRule profile rule).metavariables
              (arguments ++ codes) 0 (replayRule profile rule).conclusion
            some (premises, conclusion)) = _
        rw [premisesInstance, conclusionInstance, ruleId]
        cases instantiateSchemasAt? rule.metavariables arguments 0 rule.premises <;>
          cases instantiateSchemaAt? rule.metavariables arguments 0 rule.conclusion <;> rfl
      · rw [if_neg sideValid, if_neg sideValid]
        rfl
    · rw [if_neg argumentsValid, if_neg argumentsValid]
      rfl
  · rw [if_neg childrenValid]
    simp only [Bool.not_eq_true] at childrenValid
    simp [childrenValid]

end Step

/-! ## The rule facts follow from validity -/

theorem mem_patternsMetavariableOccurrencesAt {depth : Nat} {schema : Pattern}
    {occurrence : String × Nat} :
    (schemas : List Pattern) → schema ∈ schemas →
      occurrence ∈ patternMetavariableOccurrencesAt depth schema →
      occurrence ∈ patternsMetavariableOccurrencesAt depth schemas
  | [], member, _ => by simp at member
  | head :: schemas, member, occurs => by
      rw [patternsMetavariableOccurrencesAt]
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_append_left _ occurs
      · exact List.mem_append_right _
          (mem_patternsMetavariableOccurrencesAt schemas member occurs)

/-- The facts consumed by the correspondence hold for every rule of a
validated calculus whose replay rules form a validated presentation. -/
theorem replayRuleFacts_of_mem (profile : CellProfile)
    (definition cell : ValidatedCalculusLanguageDef)
    (rulesEq : cell.1.rules = replayRules profile definition.1.rules)
    {rule : RuleSchema} (member : rule ∈ definition.1.rules) : ReplayRuleFacts rule := by
  have cellMember : replayRule profile rule ∈ cell.1.rules := by
    rw [rulesEq, replayRules]
    exact List.mem_map_of_mem member
  have cellValid := rule_isValidIn_of_mem cell cellMember
  have ruleValid := rule_isValidIn_of_mem definition member
  simp only [RuleSchema.isValidIn, Bool.and_eq_true] at cellValid ruleValid
  have cellLocal := cellValid.1
  have ruleLocal := ruleValid.1
  simp only [RuleSchema.isLocallyValid, Bool.and_eq_true] at cellLocal ruleLocal
  have occurrencesInScope :
      ∀ occurrence ∈ RuleSchema.occurrences rule, occurrence ∈ rule.metavariables := by
    intro occurrence member
    exact List.contains_iff_mem.mp
      ((List.all_eq_true.mp ruleLocal.1.1.1.1.2) occurrence member)
  refine
    { namesNodup := ?_
      premisesInScope := ?_
      conclusionInScope := ?_
      sideConditionsValid := ?_ }
  · have nodup :=
      (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mp
        cellLocal.1.1.1.1.1.2
    simpa [RuleSchema.metavariableNames, replayRule] using nodup
  · intro premise premiseMember occurrence occurs
    apply occurrencesInScope
    unfold RuleSchema.occurrences RuleSchema.patterns
    exact mem_patternsMetavariableOccurrencesAt _ (List.mem_append_left _ premiseMember) occurs
  · intro occurrence occurs
    apply occurrencesInScope
    unfold RuleSchema.occurrences RuleSchema.patterns
    exact mem_patternsMetavariableOccurrencesAt _
      (List.mem_append_right _ (List.mem_singleton_self _)) occurs
  · intro condition conditionMember
    exact (List.all_eq_true.mp ruleValid.2.2) condition conditionMember

/-! ## Codes of accepted certificates are closed -/

theorem isGroundListAt_of_forall {depth : Nat} :
    (patterns : List Pattern) → (∀ pattern ∈ patterns, pattern.isGroundAt depth = true) →
      Pattern.isGroundListAt depth patterns = true
  | [], _ => by rw [Pattern.isGroundListAt]
  | pattern :: patterns, ground => by
      rw [Pattern.isGroundListAt, ground pattern List.mem_cons_self,
        isGroundListAt_of_forall patterns
          (fun other member => ground other (List.mem_cons_of_mem _ member))]
      rfl

theorem hasCanonicalBinderMetadataList_of_forall :
    (patterns : List Pattern) → (∀ pattern ∈ patterns, pattern.hasCanonicalBinderMetadata = true) →
      Pattern.hasCanonicalBinderMetadataList patterns = true
  | [], _ => by rw [Pattern.hasCanonicalBinderMetadataList]
  | pattern :: patterns, canonical => by
      rw [Pattern.hasCanonicalBinderMetadataList, canonical pattern List.mem_cons_self,
        hasCanonicalBinderMetadataList_of_forall patterns
          (fun other member => canonical other (List.mem_cons_of_mem _ member))]
      rfl

theorem bindArguments_valid :
    (formals : List (String × Nat)) → (arguments : List Pattern) →
    argumentsValidAt formals arguments = true →
      ∀ pattern ∈ bindArguments (formals.map (·.2)) arguments, argumentValidAt 0 pattern = true
  | [], [], _, _, member => by simp [bindArguments] at member
  | [], _ :: _, valid, _, _ => by simp [argumentsValidAt] at valid
  | _ :: _, [], valid, _, _ => by simp [argumentsValidAt] at valid
  | (name, depth) :: formals, argument :: arguments, valid, pattern, member => by
      simp only [argumentsValidAt, Bool.and_eq_true] at valid
      simp only [List.map_cons, bindArguments, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [argumentValidAt, Bool.and_eq_true] at valid ⊢
        rw [isGroundAt_bindAt, Nat.zero_add, hasCanonicalBinderMetadata_bindAt]
        exact valid.1
      · exact bindArguments_valid formals arguments valid.2 pattern member

theorem argumentValidAt_certificateCode (profile : CellProfile) (id : RuleId)
    (arguments children : List Pattern)
    (argumentsValid : ∀ pattern ∈ arguments, argumentValidAt 0 pattern = true)
    (childrenValid : ∀ pattern ∈ children, argumentValidAt 0 pattern = true) :
    argumentValidAt 0 (certificateCode profile id arguments children) = true := by
  simp only [argumentValidAt, Bool.and_eq_true] at argumentsValid childrenValid ⊢
  simp only [certificateCode, ruleAtom, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
    Option.isNone_none, Bool.and_true, Bool.true_and, Bool.and_eq_true]
  exact ⟨⟨isGroundListAt_of_forall _ fun pattern member => (argumentsValid pattern member).1,
      isGroundListAt_of_forall _ fun pattern member => (childrenValid pattern member).1⟩,
    hasCanonicalBinderMetadataList_of_forall _ fun pattern member => (argumentsValid pattern member).2,
    hasCanonicalBinderMetadataList_of_forall _ fun pattern member => (childrenValid pattern member).2⟩

/-- A successful rule instance exposes its looked-up rule, the length of its
argument vector, the validity of its arguments, and the length of its
premise list. -/
theorem instantiateRule?_some_facts {definition : ValidatedCalculusLanguageDef}
    {id : RuleId} {arguments : List Pattern} {premises : List Pattern} {conclusion : Pattern}
    (step : instantiateRule? definition ⟨id, arguments⟩ = some (premises, conclusion)) :
    ∃ rule, definition.1.lookupRule? id = some rule ∧
      argumentsValidAt rule.metavariables arguments = true ∧
      premises.length = rule.premises.length := by
  cases lookup : definition.1.lookupRule? id with
  | none => simp [instantiateRule?, lookup] at step
  | some rule =>
      simp only [instantiateRule?, lookup] at step
      by_cases valid : argumentsValidAt rule.metavariables arguments = true
      · rw [if_pos valid] at step
        by_cases side : RuleSchema.sideConditionsHold rule arguments = true
        · rw [if_pos side] at step
          unfold instantiateSchemas? at step
          cases premisesResult : instantiateSchemasAt? rule.metavariables arguments 0 rule.premises with
          | none =>
              rw [premisesResult] at step
              exact absurd step (by simp)
          | some results =>
              rw [premisesResult] at step
              cases conclusionResult : instantiateSchema? rule.metavariables arguments rule.conclusion with
              | none =>
                  rw [conclusionResult] at step
                  exact absurd step (by simp)
              | some result =>
                  rw [conclusionResult] at step
                  have pairEq : (results, result) = (premises, conclusion) := Option.some.inj step
                  refine ⟨rule, rfl, valid, ?_⟩
                  rw [← (Prod.mk.inj pairEq).1]
                  exact (instantiateSchemasAt?_length_eq premisesResult).symm
        · rw [if_neg side] at step
          exact absurd step (by simp)
      · rw [if_neg valid] at step
        exact absurd step (by simp)

section Correspondence

variable (profile : CellProfile) (definition : ValidatedCalculusLanguageDef)

mutual

/-- The code of the erasure of a derivation is closed and canonical. -/
theorem quoteProof_erase_valid : {goal : Pattern} →
    (derivation : (nikSignature definition).Deriv goal) →
      argumentValidAt 0 (quoteProof profile definition.1 derivation.erase) = true
  | _, .byStep ⟨id, arguments⟩ step children => by
      obtain ⟨rule, lookup, argumentsValid, _⟩ := instantiateRule?_some_facts step
      rw [ReplaySignature.Deriv.erase_byStep, quoteProof_node]
      simp only
      rw [formalDepths_of_lookup lookup]
      exact argumentValidAt_certificateCode profile id _ _
        (bindArguments_valid rule.metavariables arguments argumentsValid)
        (quoteProofs_erase_valid children)

/-- The same for ordered children. -/
theorem quoteProofs_erase_valid : {goals : List Pattern} →
    (derivations : (nikSignature definition).DerivList goals) →
      ∀ pattern ∈ quoteProofs profile definition.1 derivations.erase,
        argumentValidAt 0 pattern = true
  | _, .nil => by
      intro pattern member
      rw [ReplaySignature.DerivList.erase_nil, quoteProofs_nil] at member
      simp at member
  | _, .cons head tail => by
      intro pattern member
      rw [ReplaySignature.DerivList.erase_cons, quoteProofs_cons] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact quoteProof_erase_valid head
      · exact quoteProofs_erase_valid tail pattern member

end

theorem argumentsValidAt_of_forall :
    (formals : List (String × Nat)) → (arguments : List Pattern) →
    formals.length = arguments.length → (∀ formal ∈ formals, formal.2 = 0) →
    (∀ argument ∈ arguments, argumentValidAt 0 argument = true) →
      argumentsValidAt formals arguments = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, lengths, _, _ => absurd lengths length_nil_ne_cons
  | _ :: _, [], lengths, _, _ => absurd lengths length_cons_ne_nil
  | (name, depth) :: formals, argument :: arguments, lengths, depths, valid => by
      have depthZero : depth = 0 := depths (name, depth) List.mem_cons_self
      subst depthZero
      simp only [argumentsValidAt, Bool.and_eq_true]
      exact ⟨valid argument List.mem_cons_self,
        argumentsValidAt_of_forall formals arguments (length_tail_eq lengths)
          (fun formal member => depths formal (List.mem_cons_of_mem _ member))
          (fun other member => valid other (List.mem_cons_of_mem _ member))⟩

theorem childFormalsFrom_depth_zero : (next : Nat) → (premises : List Pattern) →
    ∀ formal ∈ childFormalsFrom next premises, formal.2 = 0
  | _, [], _, member => nomatch member
  | next, _ :: premises, formal, member => by
      simp only [childFormalsFrom, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact childFormalsFrom_depth_zero (next + 1) premises formal member

theorem DerivList.length_eq {σ : ReplaySignature} : {goals : List σ.Goal} →
    (derivations : σ.DerivList goals) → derivations.erase.length = goals.length
  | _, .nil => by rw [ReplaySignature.DerivList.erase_nil]; rfl
  | _, .cons _ tail => by
      rw [ReplaySignature.DerivList.erase_cons, List.length_cons, List.length_cons,
        DerivList.length_eq tail]

mutual

/-- **Completeness of the reflexive cell.**  Every derivation of the checked
calculus yields a derivation of its acceptance judgment in the replay
calculus, and that derivation's erasure is the replay certificate. -/
theorem replay_complete (cell : ValidatedCalculusLanguageDef)
    (rulesEq : cell.1.rules = replayRules profile definition.1.rules) :
    {goal : Pattern} → (derivation : (nikSignature definition).Deriv goal) →
      ∃ lifted : (nikSignature cell).Deriv
          (acceptsJudgment profile goal (quoteProof profile definition.1 derivation.erase)),
        lifted.erase = replayProof profile definition.1 derivation.erase
  | goal, .byStep ⟨id, arguments⟩ step children => by
      obtain ⟨rule, lookup, argumentsValid, premisesLength⟩ := instantiateRule?_some_facts step
      have facts := replayRuleFacts_of_mem profile definition cell rulesEq
        (lookupRule?_mem lookup)
      have lengths : arguments.length = rule.metavariables.length :=
        (argumentsValidAt_length argumentsValid).symm
      have childrenValid :
          argumentsValidAt (childFormalsFrom rule.metavariables.length rule.premises)
            (quoteProofs profile definition.1 children.erase) = true := by
        apply argumentsValidAt_of_forall
        · rw [childFormalsFrom_length, quoteProofs_eq_map, List.length_map,
            DerivList.length_eq children, premisesLength]
        · exact childFormalsFrom_depth_zero _ _
        · exact quoteProofs_erase_valid profile definition children
      have cellStep := instantiateRule?_replay profile definition cell rulesEq lookup facts
        arguments (quoteProofs profile definition.1 children.erase) lengths
      rw [if_pos childrenValid] at cellStep
      change instantiateRule? definition ⟨id, arguments⟩ = _ at step
      rw [step] at cellStep
      simp only [Option.map_some] at cellStep
      obtain ⟨liftedChildren, childrenErased⟩ := replay_completeList cell rulesEq children
      rw [ReplaySignature.Deriv.erase_byStep, quoteProof_node, replayProof_node]
      simp only
      rw [formalDepths_of_lookup lookup]
      exact ⟨.byStep ⟨id, arguments ++ quoteProofs profile definition.1 children.erase⟩
          cellStep liftedChildren, by
        rw [ReplaySignature.Deriv.erase_byStep, childrenErased]⟩

/-- Completeness for ordered children. -/
theorem replay_completeList (cell : ValidatedCalculusLanguageDef)
    (rulesEq : cell.1.rules = replayRules profile definition.1.rules) :
    {goals : List Pattern} → (derivations : (nikSignature definition).DerivList goals) →
      ∃ lifted : (nikSignature cell).DerivList
          (List.zipWith (acceptsJudgment profile) goals
            (quoteProofs profile definition.1 derivations.erase)),
        lifted.erase = replayProofs profile definition.1 derivations.erase
  | _, .nil => ⟨.nil, rfl⟩
  | _, .cons head tail => by
      obtain ⟨liftedHead, headErased⟩ := replay_complete cell rulesEq head
      obtain ⟨liftedTail, tailErased⟩ := replay_completeList cell rulesEq tail
      exact ⟨.cons liftedHead liftedTail, by
        show liftedHead.erase :: liftedTail.erase =
          replayProof profile definition.1 head.erase ::
            replayProofs profile definition.1 tail.erase
        rw [headErased, tailErased]⟩

end

theorem zipWith_eq_nil_of_length {goals codes : List Pattern}
    (lengths : goals.length = codes.length)
    (empty : List.zipWith (acceptsJudgment profile) goals codes = []) :
    goals = [] ∧ codes = [] := by
  cases goals with
  | nil => cases codes with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => exact absurd lengths length_nil_ne_cons
  | cons _ _ => cases codes with
    | nil => exact absurd lengths length_cons_ne_nil
    | cons _ _ => exact nomatch empty

mutual

/-- **Soundness of the reflexive cell.**  Every derivation of an acceptance
judgment in the replay calculus comes from a raw certificate that the checked
calculus accepts for the goal, whose code is the judgment's code, and whose
replay certificate is the derivation's erasure. -/
theorem replay_sound (cell : ValidatedCalculusLanguageDef)
    (rulesEq : cell.1.rules = replayRules profile definition.1.rules) :
    {judgment : Pattern} → (derivation : (nikSignature cell).Deriv judgment) →
    ∀ goal code, judgment = acceptsJudgment profile goal code →
      ∃ certificate : RawProof,
        (nikSignature definition).replay goal certificate = true ∧
          code = quoteProof profile definition.1 certificate ∧
          derivation.erase = replayProof profile definition.1 certificate
  | _, .byStep ⟨id, fullArguments⟩ step children, goal, code, judgmentEq => by
      change instantiateRule? cell ⟨id, fullArguments⟩ = _ at step
      obtain ⟨metaRule, cellLookup, fullValid, _⟩ := instantiateRule?_some_facts step
      rw [lookupRule?_replayRules profile definition.1 cell.1 rulesEq] at cellLookup
      cases lookup : definition.1.lookupRule? id with
      | none => rw [lookup] at cellLookup; exact absurd cellLookup (by simp)
      | some rule =>
          rw [lookup] at cellLookup
          simp only [Option.map_some, Option.some.injEq] at cellLookup
          subst cellLookup
          have facts := replayRuleFacts_of_mem profile definition cell rulesEq
            (lookupRule?_mem lookup)
          obtain ⟨split, splitLength⟩ :=
            argumentsValidAt_split rule.metavariables
              (childFormalsFrom rule.metavariables.length rule.premises) fullArguments fullValid
          set arguments := fullArguments.take rule.metavariables.length
          set codes := fullArguments.drop rule.metavariables.length
          rw [split] at step
          have cellStep := instantiateRule?_replay profile definition cell rulesEq lookup facts
            arguments codes splitLength
          rw [cellStep] at step
          by_cases childrenValid :
              argumentsValidAt (childFormalsFrom rule.metavariables.length rule.premises) codes = true
          · rw [if_pos childrenValid] at step
            cases objectStep : instantiateRule? definition ⟨id, arguments⟩ with
            | none => rw [objectStep] at step; exact absurd step (by simp)
            | some result =>
                obtain ⟨objectPremises, objectConclusion⟩ := result
                rw [objectStep] at step
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at step
                obtain ⟨premisesEq, conclusionEq⟩ := step
                rw [← conclusionEq] at judgmentEq
                simp only [acceptsJudgment, Pattern.apply.injEq, List.cons.injEq, and_true,
                  true_and] at judgmentEq
                obtain ⟨goalEq, codeEq⟩ := judgmentEq
                obtain ⟨objectRule, objectLookup, _, objectPremisesLength⟩ :=
                  instantiateRule?_some_facts objectStep
                rw [lookup] at objectLookup
                cases Option.some.inj objectLookup
                have codesLength : objectPremises.length = codes.length := by
                  rw [objectPremisesLength, ← childFormalsFrom_length rule.metavariables.length,
                    argumentsValidAt_length childrenValid]
                obtain ⟨certificates, childrenAccepted, codesEq, childrenErased⟩ :=
                  replay_soundList cell rulesEq children objectPremises codes codesLength
                    premisesEq.symm
                refine ⟨.node ⟨id, arguments⟩ certificates, ?_, ?_, ?_⟩
                · rw [ReplaySignature.replay_node]
                  simp only [objectStep, goalEq, decide_true, Bool.true_and]
                  exact childrenAccepted
                · rw [← codeEq, quoteProof_node]
                  simp only
                  rw [formalDepths_of_lookup lookup, ← codesEq]
                · rw [ReplaySignature.Deriv.erase_byStep, replayProof_node, childrenErased]
                  simp only
                  rw [← codesEq, ← split]
          · rw [if_neg childrenValid] at step
            exact absurd step (by simp)

/-- Soundness for ordered children. -/
theorem replay_soundList (cell : ValidatedCalculusLanguageDef)
    (rulesEq : cell.1.rules = replayRules profile definition.1.rules) :
    {judgments : List Pattern} → (derivations : (nikSignature cell).DerivList judgments) →
    ∀ goals codes, goals.length = codes.length →
      judgments = List.zipWith (acceptsJudgment profile) goals codes →
      ∃ certificates : List RawProof,
        (nikSignature definition).replayAll goals certificates = true ∧
          codes = quoteProofs profile definition.1 certificates ∧
          derivations.erase = replayProofs profile definition.1 certificates
  | _, .nil, goals, codes, lengths, judgmentsEq => by
      obtain ⟨rfl, rfl⟩ := zipWith_eq_nil_of_length profile lengths judgmentsEq.symm
      exact ⟨[], rfl, by rw [quoteProofs_nil], by
        rw [ReplaySignature.DerivList.erase_nil, replayProofs_nil]⟩
  | _, .cons head tail, goals, codes, lengths, judgmentsEq => by
      cases goals with
      | nil => exact nomatch judgmentsEq
      | cons goal goals =>
          cases codes with
          | nil => exact absurd lengths length_cons_ne_nil
          | cons code codes =>
              simp only [List.zipWith_cons_cons, List.cons.injEq] at judgmentsEq
              obtain ⟨headEq, tailEq⟩ := judgmentsEq
              obtain ⟨certificate, headAccepted, codeEq, headErased⟩ :=
                replay_sound cell rulesEq head goal code headEq
              obtain ⟨certificates, tailAccepted, codesEq, tailErased⟩ :=
                replay_soundList cell rulesEq tail goals codes (length_tail_eq lengths) tailEq
              refine ⟨certificate :: certificates, ?_, ?_, ?_⟩
              · rw [ReplaySignature.replayAll_cons_cons, headAccepted, tailAccepted]
                rfl
              · rw [quoteProofs_cons, ← codeEq, ← codesEq]
              · rw [ReplaySignature.DerivList.erase_cons, headErased, tailErased,
                  replayProofs_cons]

end

end Correspondence

mutual

theorem replayProof_injective (profile : CellProfile) (definition : CalculusLanguageDef) :
    (first second : RawProof) →
      replayProof profile definition first = replayProof profile definition second →
        first = second
  | .node label children, .node label' children', equal => by
      rw [replayProof_node, replayProof_node] at equal
      injection equal with labelEq childrenEq
      have childrenEq' := replayProofs_injective profile definition children children' childrenEq
      subst childrenEq'
      injection labelEq with idEq argumentsEq
      have argumentsEq' := List.append_cancel_right argumentsEq
      cases label
      cases label'
      simp only at idEq argumentsEq'
      rw [idEq, argumentsEq']

theorem replayProofs_injective (profile : CellProfile) (definition : CalculusLanguageDef) :
    (first second : List RawProof) →
      replayProofs profile definition first = replayProofs profile definition second →
        first = second
  | [], [], _ => rfl
  | [], _ :: _, equal => by rw [replayProofs_nil, replayProofs_cons] at equal; simp at equal
  | _ :: _, [], equal => by rw [replayProofs_nil, replayProofs_cons] at equal; simp at equal
  | child :: children, child' :: children', equal => by
      rw [replayProofs_cons, replayProofs_cons] at equal
      injection equal with headEq tailEq
      rw [replayProof_injective profile definition child child' headEq,
        replayProofs_injective profile definition children children' tailEq]

end


theorem ruleAtom_injective {first second : RuleId} (equal : ruleAtom first = ruleAtom second) :
    first = second := by
  simp only [ruleAtom, Pattern.apply.injEq, and_true] at equal
  cases first
  cases second
  simp only at equal
  rw [equal]

mutual

/-- Quotation is injective: a code determines its certificate. -/
theorem quoteProof_injective (profile : CellProfile) (definition : CalculusLanguageDef) :
    (first second : RawProof) →
      quoteProof profile definition first = quoteProof profile definition second →
        first = second
  | .node label children, .node label' children', equal => by
      rw [quoteProof_node, quoteProof_node] at equal
      simp only [certificateCode, Pattern.apply.injEq, List.cons.injEq, true_and,
        Pattern.collection.injEq, and_true] at equal
      obtain ⟨atomEq, argumentsEq, childrenEq⟩ := equal
      have idEq := ruleAtom_injective atomEq
      rw [idEq] at argumentsEq
      have argumentsEq' := bindArguments_injective _ _ _ argumentsEq
      have childrenEq' := quoteProofs_injective profile definition children children' childrenEq
      cases label
      cases label'
      simp only at idEq argumentsEq'
      rw [idEq, argumentsEq', childrenEq']

theorem quoteProofs_injective (profile : CellProfile) (definition : CalculusLanguageDef) :
    (first second : List RawProof) →
      quoteProofs profile definition first = quoteProofs profile definition second →
        first = second
  | [], [], _ => rfl
  | [], _ :: _, equal => by rw [quoteProofs_nil, quoteProofs_cons] at equal; simp at equal
  | _ :: _, [], equal => by rw [quoteProofs_nil, quoteProofs_cons] at equal; simp at equal
  | child :: children, child' :: children', equal => by
      rw [quoteProofs_cons, quoteProofs_cons] at equal
      injection equal with headEq tailEq
      rw [quoteProof_injective profile definition child child' headEq,
        quoteProofs_injective profile definition children children' tailEq]

end

section Checking

variable (profile : CellProfile) (definition cell : ValidatedCalculusLanguageDef)
    (rulesEq : cell.1.rules = replayRules profile definition.1.rules)
include rulesEq

/-- **The reflexive cell, as checking.**  The generic checker accepts the
replay certificate for the acceptance judgment exactly when it accepts the
certificate for the goal. -/
theorem checkRaw_replayProof (goal : Pattern) (certificate : RawProof) :
    checkRaw cell (acceptsJudgment profile goal (quoteProof profile definition.1 certificate))
        (replayProof profile definition.1 certificate) =
      checkRaw definition goal certificate := by
  rw [checkRaw_eq_replay, checkRaw_eq_replay]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    obtain ⟨derivation, erased⟩ := ReplaySignature.exists_deriv_of_replay _ _ accepted
    obtain ⟨certificate', accepted', _, erased'⟩ :=
      replay_sound profile definition cell rulesEq derivation goal _ rfl
    rw [erased] at erased'
    rw [replayProof_injective profile definition.1 _ _ erased']
    exact accepted'
  · intro accepted
    obtain ⟨derivation, erased⟩ := ReplaySignature.exists_deriv_of_replay _ _ accepted
    subst erased
    obtain ⟨lifted, liftedErased⟩ := replay_complete profile definition cell rulesEq derivation
    rw [← liftedErased]
    exact lifted.replay_erase

/-- **The presented package's derivations coincide with the checking
derivations.**  An acceptance judgment is derivable in the replay calculus
exactly when its code quotes a certificate that the checked calculus accepts
for its goal. -/
theorem accepts_derivable_iff (goal code : Pattern) :
    Nonempty (Derivation cell (acceptsJudgment profile goal code)) ↔
      ∃ certificate : RawProof,
        code = quoteProof profile definition.1 certificate ∧
          checkRaw definition goal certificate = true := by
  constructor
  · rintro ⟨derivation⟩
    obtain ⟨certificate, accepted, codeEq, _⟩ :=
      replay_sound profile definition cell rulesEq (toDeriv derivation) goal code rfl
    exact ⟨certificate, codeEq, by rw [checkRaw_eq_replay]; exact accepted⟩
  · rintro ⟨certificate, rfl, accepted⟩
    rw [checkRaw_eq_replay] at accepted
    obtain ⟨derivation, rfl⟩ := ReplaySignature.exists_deriv_of_replay _ _ accepted
    obtain ⟨lifted, _⟩ := replay_complete profile definition cell rulesEq derivation
    exact ⟨ofDeriv lifted⟩


/-- **The reflexive cell is proof-irrelevant.**  An acceptance judgment has at
most one derivation in the replay calculus: the code determines the
certificate, and the certificate determines the derivation. -/
theorem replay_deriv_subsingleton (goal code : Pattern) :
    Subsingleton ((nikSignature cell).Deriv (acceptsJudgment profile goal code)) := by
  refine ⟨fun first second => ?_⟩
  obtain ⟨certificate, _, codeEq, firstErased⟩ :=
    replay_sound profile definition cell rulesEq first goal code rfl
  obtain ⟨certificate', _, codeEq', secondErased⟩ :=
    replay_sound profile definition cell rulesEq second goal code rfl
  have sameCertificate :=
    quoteProof_injective profile definition.1 certificate certificate' (codeEq.symm.trans codeEq')
  subst sameCertificate
  exact ReplaySignature.Deriv.eq_of_erase_eq first second (firstErased.trans secondErased.symm)

end Checking

end Mettapedia.GSLT.LanguageDef.BootstrapCell
