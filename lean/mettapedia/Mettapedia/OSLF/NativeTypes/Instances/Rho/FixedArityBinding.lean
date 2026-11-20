import Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry
import Mettapedia.OSLF.MeTTaIL.GeneralRhoReflection

open Mettapedia.OSLF.Framework

/-!
# Scoped interpretation of communication without a remainder

The companion retains every source pattern and declaration of the paper rule.
Its dependency specification restricts the existing received-name interface
to the variables actually declared in that rule. Independent traced matching
and scoped instantiation characterize the resulting execution for arbitrary
ambient contexts and scoped bodies; ordinary matching is not assumed equal
to capture under a binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open RuleBinding ScopedRuleMatching GeneralScopedMatchMachine
open Mettapedia.GSLT.Examples.ScopedRhoBinding (scopedCommBindingSpec)
open Mettapedia.GSLT.LanguageDef.ReflectionExtension (rhoReflectionProfile)
open GeneralRho (recover_root recover_body instantiate_root instantiate_body)
open GeneratedHypercubeInstances (rhoCommPaper)

def bindingSpec : RuleBindingSpec :=
  { scopedCommBindingSpec with
    dependencies := scopedCommBindingSpec.dependencies.filter (fun entry =>
      (rhoCommPaper.typeContext.map Prod.fst).contains entry.1) }

def comm : RewriteRule := {rhoCommPaper with bindings := some bindingSpec}

def language : LanguageDef := {rhoCalc with rewrites := [comm]}

theorem original_source_is_retained :
    comm.name = rhoCommPaper.name ∧ comm.typeContext = rhoCommPaper.typeContext ∧
      comm.premises = rhoCommPaper.premises ∧ comm.left = rhoCommPaper.left ∧
      comm.right = rhoCommPaper.right := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem original_grammar_is_retained :
    language.types = rhoCalc.types ∧ language.terms = rhoCalc.terms ∧
      language.equations = rhoCalc.equations := ⟨rfl, rfl, rfl⟩

theorem binding_admitted : admittedFor comm bindingSpec = true := by decide +kernel

theorem dependency_sorts_declared : dependencySortsDeclared language bindingSpec = true := by
  decide +kernel

theorem actual_received_dependency : dependencies? bindingSpec "p" = some [.base "Name"] := by
  decide +kernel

theorem remainder_has_no_dependency : dependencies? bindingSpec "rest" = none := by decide +kernel

def snapshot : GeneralExecutionAdmission.Snapshot := ⟨language, [], ⟨[], [], []⟩⟩

def permissions : GeneralExecutionAdmission.Permissions :=
  {sites := .all, ruleIndices := some [0], equationIndices := some [],
    includeDerivedEquations := false, reflection := rhoReflectionProfile}

def declaration : GeneralExecutionAdmission.RulePlan :=
  ⟨0, comm, ⟨bindingSpec, .authored⟩⟩

theorem binding_compiled : GeneralRuleBindingInference.compile? language comm =
    some declaration.binding := by
  simp only [GeneralRuleBindingInference.compile?, show comm.bindings = some bindingSpec from rfl,
    binding_admitted, dependency_sorts_declared, Bool.true_and, ↓reduceIte]
  rfl

theorem substitution_selected :
    ReflectiveSubstitution.substitutionPresentationForRule? rhoReflectionProfile comm =
      some rhoReflectivePresentation.toReflectivePresentationDecl := by decide +kernel

theorem binder_operation : ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm =
    ScopedRuleInstantiation.reflectiveOperation rhoReflectivePresentation.toReflectivePresentationDecl := by
  simp only [ScopedReflectiveExecution.binderOperation, substitution_selected]

def source (channel body payload : Pattern) : Pattern := GeneralRho.source channel body payload []

def captured (ambient : Nat) (channel body payload : Pattern) : ScopedRuleMatching.Assignment :=
  [("q", GeneralRho.rootValue ambient payload), ("p", GeneralRho.bodyValue ambient body),
    ("n", GeneralRho.rootValue ambient channel)]

private theorem dependencies_n : dependencies? bindingSpec "n" = some [] := by decide +kernel
private theorem dependencies_q : dependencies? bindingSpec "q" = some [] := by decide +kernel
private theorem input_n_arguments : arguments? comm bindingSpec "n" .left [0, 0] = some [] := by decide +kernel
private theorem input_p_arguments : arguments? comm bindingSpec "p" .left [0, 1, 0] = some [.bvar 0] := by decide +kernel
private theorem output_n_arguments : arguments? comm bindingSpec "n" .left [1, 0] = some [] := by decide +kernel
private theorem output_q_arguments : arguments? comm bindingSpec "q" .left [1, 1] = some [] := by decide +kernel
private theorem target_p_arguments : arguments? comm bindingSpec "p" .right [0, 0] = some [.bvar 0] := by decide +kernel
private theorem target_q_arguments : arguments? comm bindingSpec "q" .right [0, 1, 0] = some [] := by decide +kernel

private theorem input_n_capture {ambient : Nat} {channel : Pattern}
    (safe : channel.isWellScopedAt ambient = true) :
    capture? comm bindingSpec ambient 0 .left [0, 0] [] "n" channel =
      some [("n", GeneralRho.rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_n, input_n_arguments,
    Option.bind_some, recover_root safe]
  rfl

private theorem input_p_capture {ambient : Nat} {channel body : Pattern}
    (safe : body.isWellScopedAt (ambient + 1) = true) :
    capture? comm bindingSpec ambient 1 .left [0, 1, 0]
      [("n", GeneralRho.rootValue ambient channel)] "p" body =
      some [("p", GeneralRho.bodyValue ambient body), ("n", GeneralRho.rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, actual_received_dependency, input_p_arguments,
    Option.bind_some, recover_body safe]
  rfl

private theorem output_n_capture {ambient : Nat} {channel body : Pattern}
    (safe : channel.isWellScopedAt ambient = true) :
    capture? comm bindingSpec ambient 0 .left [1, 0]
      [("p", GeneralRho.bodyValue ambient body), ("n", GeneralRho.rootValue ambient channel)] "n" channel =
      some [("p", GeneralRho.bodyValue ambient body), ("n", GeneralRho.rootValue ambient channel)] := by
  simp only [Option.bind_eq_bind, capture?, dependencies_n, output_n_arguments,
    Option.bind_some, recover_root safe]
  simp [assign, lookup]

private theorem output_q_capture {ambient : Nat} {channel body payload : Pattern}
    (safe : payload.isWellScopedAt ambient = true) :
    capture? comm bindingSpec ambient 0 .left [1, 1]
      [("p", GeneralRho.bodyValue ambient body), ("n", GeneralRho.rootValue ambient channel)] "q" payload =
      some (captured ambient channel body payload) := by
  simp only [Option.bind_eq_bind, capture?, dependencies_q, output_q_arguments,
    Option.bind_some, recover_root safe]
  rfl

private theorem input_matching {ambient : Nat} {channel body : Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (bodySafe : body.isWellScopedAt (ambient + 1) = true) :
    TracedMatches comm bindingSpec ambient .left [0] 0 []
      (.apply "PInput" [.fvar "n", .lambda none (.fvar "p")]) (GeneralRho.input channel body) []
      [("p", GeneralRho.bodyValue ambient body), ("n", GeneralRho.rootValue ambient channel)] :=
  .constructor (.cons (.capture (input_n_capture channelSafe))
    (.cons (.binder (.capture (input_p_capture bodySafe))) .nil))

private theorem output_matching {ambient : Nat} {channel body payload : Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (payloadSafe : payload.isWellScopedAt ambient = true) :
    TracedMatches comm bindingSpec ambient .left [1] 0
      [("p", GeneralRho.bodyValue ambient body), ("n", GeneralRho.rootValue ambient channel)]
      (.apply "POutput" [.fvar "n", .fvar "q"]) (GeneralRho.output channel payload) []
      (captured ambient channel body payload) :=
  .constructor (.cons (.capture (output_n_capture channelSafe))
    (.cons (.capture (output_q_capture payloadSafe)) .nil))

/-- Every scoped body and payload is captured with the received Name
dependency. The collection has no unmatched remainder to bind or discard. -/
theorem source_matching {ambient : Nat} {channel body payload : Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true) :
    TracedMatches comm bindingSpec ambient .left [] 0 [] comm.left
      (source channel body payload) GeneralRho.commTrace (captured ambient channel body payload) := by
  apply TracedMatches.bag (by decide)
  apply TracedBag.cons (headTrace := []) (tailTrace := [{path := [1], selected := 0}]) 0 (by simp)
  · exact input_matching channelSafe bodySafe
  · apply TracedBag.cons (headTrace := []) (tailTrace := []) 0 (by simp)
    · exact output_matching channelSafe payloadSafe
    · exact .nil

/-- The actual authored RHS reads the retained body in its dependency
context before eliminating the received binder by the selected operation. -/
theorem reduct_readout (operation : Pattern → Pattern → Pattern)
    {ambient : Nat} {channel body payload : Pattern}
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true) :
    reductWith? operation comm bindingSpec ambient (captured ambient channel body payload) =
      some (.collection .hashBag [operation (.apply "NQuote" [payload]) body] none) := by
  have bodyFound : lookup (captured ambient channel body payload) "p" =
      some (GeneralRho.bodyValue ambient body) := rfl
  have payloadFound : lookup (captured ambient channel body payload) "q" =
      some (GeneralRho.rootValue ambient payload) := rfl
  unfold reductWith?
  change instantiateWith? operation comm bindingSpec ambient .right [] 0
    (captured ambient channel body payload)
    (.collection .hashBag [.subst (.fvar "p") (.apply "NQuote" [.fvar "q"])] none) = _
  simp only [instantiateWith?, instantiateArgsWith?, Option.bind_eq_bind,
    List.nil_append, List.cons_append, bodyFound, payloadFound,
    target_p_arguments, target_q_arguments, instantiate_body bodySafe,
    instantiate_root payloadSafe, Option.bind_some, Nat.zero_add]

theorem reflective_reduct {ambient : Nat} {channel body payload : Pattern}
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true) :
    reductWith? (ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm)
      comm bindingSpec ambient (captured ambient channel body payload) =
      some (.collection .hashBag [GeneralRho.reflectiveBody body payload] none) := by
  rw [reduct_readout _ bodySafe payloadSafe, binder_operation]
  rfl

/-- On the independently sorted source syntax, the companion reads exactly
the paper-facing received-name substitution, for every body in the
literal-quotation fiber and every payload. -/
theorem reduct_agrees_with_original_semantic_substitution
    {free : DerivedPresentationSyntax.FreeSortContext} {channel body payload : Pattern}
    (bodyTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation free ["Name"] body)
    (fiber : Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.quotesLiteral rhoReflectivePresentation body = true)
    (payloadTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation free [] payload) :
    reductWith? (ScopedReflectiveExecution.binderOperation rhoReflectionProfile comm)
      comm bindingSpec 0 (captured 0 channel body payload) =
      some (.collection .hashBag
        [Mettapedia.Languages.ProcessCalculi.RhoCalculus.semanticCommSubst body payload] none) := by
  have bodySafe : body.isWellScopedAt 1 = true := (GeneralRho.derived_process_typed bodyTyped).isWellScopedAt
  have payloadSafe : payload.isWellScopedAt 0 = true := (GeneralRho.derived_process_typed payloadTyped).isWellScopedAt
  have original := GeneralRho.reflective_reduct_semantic (channel := channel) (rest := []) bodyTyped payloadTyped rfl
    fiber
  rw [GeneralRho.reflective_reduct bodySafe payloadSafe rfl] at original
  rw [reflective_reduct bodySafe payloadSafe]
  exact original

/-- The original rule's omitted received-name metadata is reconstructed from
the grammar. The actual occurrence contexts agree on both sides of the
substitution, and no extra variable declarations are required. -/
theorem source_received_binding_is_inferred :
    (GeneralRuleBindingInference.compile? language rhoCommPaper).map (·.origin) =
        some (.inferredGrammar []) ∧
      (GeneralRuleBindingInference.compile? language rhoCommPaper).map (·.implicitTypes) =
        some [] ∧
      (GeneralRuleBindingInference.compile? language rhoCommPaper).bind (fun plan =>
        dependencies? plan.spec "p") = some [.base "Name"] ∧
      (GeneralRuleBindingInference.compile? language rhoCommPaper).bind (fun plan =>
        arguments? (plan.elaborate rhoCommPaper) plan.spec "p" .left [0, 1, 0]) =
        some [.bvar 0] ∧
      (GeneralRuleBindingInference.compile? language rhoCommPaper).bind (fun plan =>
        arguments? (plan.elaborate rhoCommPaper) plan.spec "p" .right [0, 0]) =
        some [.bvar 0] ∧
      (GeneralRuleBindingInference.compile? language rhoCommPaper).map (fun plan =>
        (plan.elaborate rhoCommPaper).typeContext) = some rhoCommPaper.typeContext := by
  have underBinder : GeneralRuleBindingInference.rootInput 0 rhoCommPaper.left = false := by
    simp [GeneralRuleBindingInference.rootInput, GeneralRuleBindingInference.rootArguments, rhoCommPaper]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [GeneralRuleBindingInference.compile?, show rhoCommPaper.bindings = none from rfl,
      underBinder, Bool.false_and, Bool.false_eq_true, if_false] <;>
    decide +kernel

theorem inferred_source_binding_admitted {plan : GeneralRuleBindingInference.BindingPlan}
    (compiled : GeneralRuleBindingInference.compile? language rhoCommPaper = some plan) :
    admittedFor (plan.elaborate rhoCommPaper) plan.spec = true ∧
      dependencySortsDeclared language plan.spec = true :=
  GeneralRuleBindingInference.compile_admitted compiled

theorem inferred_source_patterns_retained (plan : GeneralRuleBindingInference.BindingPlan) :
    (plan.elaborate rhoCommPaper).name = rhoCommPaper.name ∧
      (plan.elaborate rhoCommPaper).left = rhoCommPaper.left ∧
      (plan.elaborate rhoCommPaper).right = rhoCommPaper.right ∧
      (plan.elaborate rhoCommPaper).premises = rhoCommPaper.premises :=
  GeneralRuleBindingInference.elaborate_source plan rhoCommPaper

def erasedDependencies : RuleBindingSpec :=
  { bindingSpec with dependencies := bindingSpec.dependencies.map (fun entry => (entry.1, [])) }

theorem erasing_received_dependency_rejects_capture :
    capture? comm erasedDependencies 0 1 .left [0, 1, 0] [] "p"
      (.apply "PDrop" [.bvar 0]) = none := by decide +kernel

def matchingRequest (ambient : Nat) (channel body payload : Pattern) : Request :=
  ⟨comm, bindingSpec, ambient, .left, [], 0, [], comm.left, source channel body payload⟩

/-- The independently justified scoped interpretation is eventually found
by the actual interruptible matcher, at every admitted ambient context. -/
theorem matching_eventually {ambient : Nat} {channel body payload : Pattern}
    (channelSafe : channel.isWellScopedAt ambient = true)
    (bodySafe : body.isWellScopedAt (ambient + 1) = true)
    (payloadSafe : payload.isWellScopedAt ambient = true) :
    ∃ budget, complete (run (matchingRequest ambient channel body payload) budget
        (start (matchingRequest ambient channel body payload))) = true ∧
      {assignment := captured ambient channel body payload, trace := GeneralRho.commTrace} ∈
        (run (matchingRequest ambient channel body payload) budget
          (start (matchingRequest ambient channel body payload))).answers := by
  obtain ⟨budget, finished, exactAnswers⟩ := completedEventually (matchingRequest ambient channel body payload)
  exact ⟨budget, finished, (exactAnswers _).mpr (source_matching channelSafe bodySafe payloadSafe)⟩

end Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding
