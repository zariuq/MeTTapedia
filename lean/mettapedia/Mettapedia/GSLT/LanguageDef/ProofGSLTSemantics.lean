import Mettapedia.GSLT.LanguageDef.ProofGSLTInterpretation

/-!
# Set-valued semantics of proof-GSLT presentations

A proof-theoretic presentation is intensional: it declares judgments and the
rules generating their derivations.  A model realizes that presentation by a
family of carrier types, one for each ground judgment, together with an action
of every admitted rule application on the carriers of its ordered premises.

Derivations fold into every such model.  Open derivations denote functions of
their premise environment, and plugging is interpreted by ordinary function
composition.  A derivation-valued interpretation consequently pulls target
models back to source models; this is the semantic content of proof transport.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

universe u

mutual

/-- Values realizing an ordered vector of judgments in a set-valued model. -/
inductive RealizationList (carrier : Pattern → Type u) :
    List Pattern → Type u where
  | nil : RealizationList carrier []
  | cons {judgment : Pattern} {judgments : List Pattern}
      (head : carrier judgment)
      (tail : RealizationList carrier judgments) :
      RealizationList carrier (judgment :: judgments)

end

namespace RealizationList

/-- Select one semantic value by its ordered judgment occurrence. -/
def get {carrier : Pattern → Type u} {judgments : List Pattern} :
    RealizationList carrier judgments →
      (index : Fin judgments.length) → carrier (judgments.get index)
  | .nil, index => Fin.elim0 index
  | .cons head tail, index =>
      Fin.cases head (fun tailIndex => tail.get tailIndex) index

/-- Build an ordered semantic environment from position-indexed values. -/
def ofFn {carrier : Pattern → Type u} :
    (judgments : List Pattern) →
      ((index : Fin judgments.length) → carrier (judgments.get index)) →
      RealizationList carrier judgments
  | [], _ => .nil
  | _ :: _, values =>
      .cons (values ⟨0, Nat.zero_lt_succ _⟩)
        (ofFn _ fun index => values index.succ)

@[simp] theorem ofFn_get {carrier : Pattern → Type u}
    {judgments : List Pattern}
    (values : RealizationList carrier judgments) :
    ofFn judgments (fun index => values.get index) = values := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp only [ofFn, get]
      change RealizationList.cons head
          (ofFn _ fun index => tail.get index) =
        RealizationList.cons head tail
      rw [ofFn_get tail]

end RealizationList

/-- A set-valued model of a validated semantic presentation. -/
structure Model (object : Object) where
  carrier : Pattern → Type u
  onRule :
    ∀ (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern},
      RuleApplication object.presentation ruleInstance premises conclusion →
        RealizationList carrier premises → carrier conclusion

namespace Model

mutual

/-- Fold a closed derivation into a model. -/
def denote {object : Object} (model : Model.{u} object)
    {goal : Pattern} :
    Derivation object.presentation goal → model.carrier goal
  | .byRule ruleInstance application children =>
      model.onRule ruleInstance application (model.denoteList children)

/-- Fold ordered closed premise derivations pointwise. -/
def denoteList {object : Object} (model : Model.{u} object)
    {goals : List Pattern} :
    DerivationList object.presentation goals →
      RealizationList model.carrier goals
  | .nil => .nil
  | .cons head tail => .cons (model.denote head) (model.denoteList tail)

end

mutual

/-- Interpret an open derivation in a semantic environment for its premise
occurrences. -/
def denoteOpen {object : Object} (model : Model.{u} object)
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation object.presentation context goal)
    (environment : RealizationList model.carrier context) :
    model.carrier goal :=
  match derivation with
  | .assumption index => environment.get index
  | .byRule ruleInstance application children =>
      model.onRule ruleInstance application
        (model.denoteOpenList children environment)

/-- Interpret an ordered vector of open derivations pointwise. -/
def denoteOpenList {object : Object} (model : Model.{u} object)
    {context goals : List Pattern}
    (derivations : OpenDerivationList object.presentation context goals)
    (environment : RealizationList model.carrier context) :
    RealizationList model.carrier goals :=
  match derivations with
  | .nil => .nil
  | .cons head tail =>
      .cons (model.denoteOpen head environment)
        (model.denoteOpenList tail environment)

end

/-- Interpreting a pointwise-built derivation vector is pointwise semantic
interpretation. -/
theorem denoteOpenList_ofFn {object : Object} (model : Model.{u} object)
    {context goals : List Pattern}
    (entries : (index : Fin goals.length) →
      OpenDerivation object.presentation context (goals.get index))
    (environment : RealizationList model.carrier context) :
    model.denoteOpenList (OpenDerivationList.ofFn goals entries) environment =
      RealizationList.ofFn goals
        (fun index => model.denoteOpen (entries index) environment) := by
  induction goals with
  | nil => rfl
  | cons goal goals inductionHypothesis =>
      simp only [OpenDerivationList.ofFn, denoteOpenList,
        RealizationList.ofFn]
      congr
      exact inductionHypothesis (fun index => entries index.succ)

/-- The semantic value of the identity premise environment is the supplied
environment itself. -/
@[simp] theorem denoteOpenList_assumptionEnvironment
    {object : Object} (model : Model.{u} object)
    {context : List Pattern}
    (environment : RealizationList model.carrier context) :
    model.denoteOpenList
        (assumptionEnvironment object.presentation context) environment =
      environment := by
  rw [assumptionEnvironment, denoteOpenList_ofFn]
  simpa only [denoteOpen] using RealizationList.ofFn_get environment

mutual

/-- Semantic interpretation sends syntactic plugging to semantic
composition. -/
theorem denoteOpen_bind {object : Object} (model : Model.{u} object)
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (derivation :
      OpenDerivation object.presentation sourceContext goal)
    (substitution :
      OpenDerivationList object.presentation targetContext sourceContext)
    (environment : RealizationList model.carrier targetContext) :
    model.denoteOpen (derivation.bind substitution) environment =
      model.denoteOpen derivation
        (model.denoteOpenList substitution environment) := by
  cases derivation with
  | assumption index =>
      simp only [OpenDerivation.bind, denoteOpen]
      exact (denoteOpenList_get model substitution environment index).symm
  | byRule ruleInstance application children =>
      simp only [OpenDerivation.bind, denoteOpen]
      congr 1
      exact denoteOpenList_bind model children substitution environment

/-- Plugging semantics holds pointwise for ordered derivation vectors. -/
theorem denoteOpenList_bind {object : Object} (model : Model.{u} object)
    {sourceContext targetContext goals : List Pattern}
    (derivations :
      OpenDerivationList object.presentation sourceContext goals)
    (substitution :
      OpenDerivationList object.presentation targetContext sourceContext)
    (environment : RealizationList model.carrier targetContext) :
    model.denoteOpenList (derivations.bind substitution) environment =
      model.denoteOpenList derivations
        (model.denoteOpenList substitution environment) := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.bind, denoteOpenList]
      rw [denoteOpen_bind model head substitution environment,
        denoteOpenList_bind model tail substitution environment]

/-- Semantic lookup commutes with pointwise open interpretation. -/
theorem denoteOpenList_get {object : Object} (model : Model.{u} object)
    {context goals : List Pattern}
    (derivations :
      OpenDerivationList object.presentation context goals)
    (environment : RealizationList model.carrier context)
    (index : Fin goals.length) :
    (model.denoteOpenList derivations environment).get index =
      model.denoteOpen (derivations.get index) environment := by
  cases derivations with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact denoteOpenList_get model tail environment tailIndex

end

/-- A target model restricts along a derivation-valued interpretation.  Each
source primitive rule is interpreted by its target open derivation. -/
def pullback {source target : Object}
    (interpretation : Interpretation source target)
    (targetModel : Model.{u} target) : Model.{u} source where
  carrier := targetModel.carrier
  onRule := fun ruleInstance _ _ application values =>
    targetModel.denoteOpen
      (interpretation.onRule ruleInstance application) values

/-- Identity interpretation induces the identity operation on models. -/
@[simp] theorem pullback_id {object : Object}
    (model : Model.{u} object) :
    pullback (Interpretation.id object) model = model := by
  cases model with
  | mk carrier onRule =>
      simp only [pullback]
      congr
      funext ruleInstance premises conclusion application values
      simp [Interpretation.id, denoteOpen]

mutual

/-- Translating an open derivation and then evaluating it agrees with
evaluating it in the pulled-back model. -/
theorem denoteOpen_map {source target : Object}
    (interpretation : Interpretation source target)
    (targetModel : Model.{u} target)
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation source.presentation context goal)
    (environment : RealizationList targetModel.carrier context) :
    targetModel.denoteOpen (interpretation.mapOpen derivation) environment =
      (pullback interpretation targetModel).denoteOpen derivation environment := by
  cases derivation with
  | assumption index => rfl
  | byRule ruleInstance application children =>
      simp only [Interpretation.mapOpen, denoteOpen, pullback]
      rw [denoteOpen_bind]
      congr 1
      exact denoteOpenList_map interpretation targetModel children environment

/-- The same naturality equation holds pointwise for ordered vectors. -/
theorem denoteOpenList_map {source target : Object}
    (interpretation : Interpretation source target)
    (targetModel : Model.{u} target)
    {context goals : List Pattern}
    (derivations :
      OpenDerivationList source.presentation context goals)
    (environment : RealizationList targetModel.carrier context) :
    targetModel.denoteOpenList
        (interpretation.mapOpenList derivations) environment =
      (pullback interpretation targetModel).denoteOpenList
        derivations environment := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [Interpretation.mapOpenList, denoteOpenList]
      rw [denoteOpen_map interpretation targetModel head environment,
        denoteOpenList_map interpretation targetModel tail environment]
      rfl

end

/-- Pullback reverses composition of presentation interpretations. -/
theorem pullback_comp {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    (model : Model.{u} last) :
    pullback (Interpretation.comp earlier later) model =
      pullback earlier (pullback later model) := by
  cases model with
  | mk carrier onRule =>
      simp only [pullback]
      congr
      funext ruleInstance premises conclusion application values
      exact denoteOpen_map later
        { carrier := carrier, onRule := onRule }
        (earlier.onRule ruleInstance application) values

mutual

/-- The open embedding of a closed derivation has the same denotation in the
unique empty environment. -/
@[simp] theorem denoteOpen_ofClosed {object : Object}
    (model : Model.{u} object) {goal : Pattern}
    (derivation : Derivation object.presentation goal) :
    model.denoteOpen (OpenDerivation.ofClosed (context := []) derivation)
        .nil =
      model.denote derivation := by
  cases derivation with
  | byRule ruleInstance application children =>
      simp only [OpenDerivation.ofClosed, denoteOpen, denote]
      congr 1
      exact denoteOpenList_ofClosed model children

/-- Pointwise closed/open denotation agreement. -/
@[simp] theorem denoteOpenList_ofClosed {object : Object}
    (model : Model.{u} object) {goals : List Pattern}
    (derivations : DerivationList object.presentation goals) :
    model.denoteOpenList
        (OpenDerivationList.ofClosed (context := []) derivations) .nil =
      model.denoteList derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.ofClosed, denoteOpenList, denoteList]
      rw [denoteOpen_ofClosed model head,
        denoteOpenList_ofClosed model tail]

end

mutual

/-- Closing an empty-context open derivation preserves its denotation. -/
theorem denote_close {object : Object} (model : Model.{u} object)
    {goal : Pattern}
    (derivation : OpenDerivation object.presentation [] goal) :
    model.denote derivation.close =
      model.denoteOpen derivation .nil := by
  cases derivation with
  | assumption index => exact Fin.elim0 index
  | byRule ruleInstance application children =>
      simp only [OpenDerivation.close, denote, denoteOpen]
      congr 1
      exact denoteList_close model children

/-- Closing an empty-context vector preserves pointwise denotation. -/
theorem denoteList_close {object : Object} (model : Model.{u} object)
    {goals : List Pattern}
    (derivations : OpenDerivationList object.presentation [] goals) :
    model.denoteList derivations.close =
      model.denoteOpenList derivations .nil := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.close, denoteList, denoteOpenList]
      rw [denote_close model head, denoteList_close model tail]

end

/-- Closed proof translation is semantically the pullback action on models. -/
theorem denote_mapDerivation {source target : Object}
    (interpretation : Interpretation source target)
    (targetModel : Model.{u} target) {goal : Pattern}
    (derivation : Derivation source.presentation goal) :
    targetModel.denote (interpretation.mapDerivation derivation) =
      (pullback interpretation targetModel).denote derivation := by
  unfold Interpretation.mapDerivation
  rw [denote_close targetModel,
    denoteOpen_map interpretation targetModel]
  exact denoteOpen_ofClosed (pullback interpretation targetModel) derivation

end Model

end Mettapedia.GSLT.LanguageDef.ProofGSLT
