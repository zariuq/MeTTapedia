import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.BindingResolutionReadCache
import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.HE.ModuleSpace
import Mettapedia.Languages.MeTTa.HE.ModuleInvalidation
import Mettapedia.Languages.MeTTa.HE.Matching
import Mettapedia.Languages.MeTTa.HE.TypeCheck
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa
import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Outcome
import Mettapedia.Languages.MeTTa.HE.SyntaxSpec
import Mettapedia.Languages.MeTTa.HE.Properties
import Mettapedia.Languages.MeTTa.HE.DeclarativeSpec
import Mettapedia.Languages.MeTTa.HE.LookupPlan
import Mettapedia.Languages.MeTTa.HE.ExecutionContract
import Mettapedia.Languages.MeTTa.HE.TransitionSpec
import Mettapedia.Languages.MeTTa.HE.RewriteIR
import Mettapedia.Languages.MeTTa.HE.RewriteIRV2
import Mettapedia.Languages.MeTTa.HE.Eval
import Mettapedia.Languages.MeTTa.HE.ArgumentResultCorrectness
import Mettapedia.Languages.MeTTa.HE.ArgumentResultControls
import Mettapedia.Languages.MeTTa.HE.RetainedArgumentSpecification
import Mettapedia.Languages.MeTTa.HE.NativeSelectedTypeScan
import Mettapedia.Languages.MeTTa.HE.NativeArgumentProjectionControls
import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlControls
import Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafService
import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
import Mettapedia.Languages.MeTTa.HE.ExecutableBoundary
import Mettapedia.Languages.MeTTa.HE.Certification
import Mettapedia.Languages.MeTTa.HE.SemanticForms
import Mettapedia.Languages.MeTTa.HE.CoreFragment
import Mettapedia.Languages.MeTTa.HE.LetChainResumption
import Mettapedia.Languages.MeTTa.HE.CollapseCollector
import Mettapedia.Languages.MeTTa.HE.ArgTraversal
import Mettapedia.Languages.MeTTa.HE.ArgTraversalControls
import Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecution
import Mettapedia.Languages.MeTTa.HE.TypedApplyDataExecutionControls
import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness
import Mettapedia.Languages.MeTTa.HE.RecursiveControls
import Mettapedia.Languages.MeTTa.HE.RecursiveService
import Mettapedia.Languages.MeTTa.HE.BulkTransferSoundness
import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.SmallStepSound
import Mettapedia.Languages.MeTTa.HE.SmallStepQuiescence
import Mettapedia.Languages.MeTTa.HE.SmallStepContext
import Mettapedia.Languages.MeTTa.HE.SmallStepMaster
import Mettapedia.Languages.MeTTa.HE.MatcherBridge
import Mettapedia.Languages.MeTTa.HE.OutcomeListContracts
import Mettapedia.Languages.MeTTa.HE.LanguageDefRuleInventory
import Mettapedia.Languages.MeTTa.HE.NativeGroundFastPath
import Mettapedia.Languages.MeTTa.HE.HOLContract
import Mettapedia.Languages.MeTTa.HE.CompletedDelivery
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues

/-!
# Independent HE semantics and abstract-machine mathematics

The source judgments specify the admitted HE profiles independently of any
runtime. The contextual abstract machine retains pending evaluation and is
parameterized by explicit semantic policies. Component models and executable
realizations must justify their connection to those judgments.

The main boundaries are:

* `Spec.Eval`, `Spec.Eval.Minimal`, and `Spec.Eval.Outcome`: fuel-free source
  judgments, abstract host services, and semantic versus resource outcomes;
* `Spec.Type` and `TypeGrounding`: declared typing profiles and their
  independently stated mathematical interpretations;
* `RecursiveMachine`, `RecursiveExecution`, and `RecursiveService`: retained
  control, source correspondence, and validated service interaction;
* argument, binding, and traversal components: local mathematical laws for
  explicit representations, rather than the definition of HE meaning.

HE answer observation preserves multiplicity while forgetting enumeration
order. An ordered component history describes that component's chosen
realization; it does not impose a language-wide answer-order guarantee.

Implementation comparisons require explicit downstream imports. In
particular, LeaTTa studies are neither part of this umbrella nor a reference
implementation for the HE judgments. PeTTa remains a distinct dialect with
separately stated search and observation policies.
-/
