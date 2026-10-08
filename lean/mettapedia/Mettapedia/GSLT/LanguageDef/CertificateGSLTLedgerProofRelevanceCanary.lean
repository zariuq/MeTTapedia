import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRepresentableProofs
import Mettapedia.GSLT.LanguageDef.CertificateGSLTCanonicalRouteTrinity
import Mettapedia.GSLT.LanguageDef.CertificateGSLTIndependentSearch
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedPresheafSigmaRoute
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedPresheafCwfBridge
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFunctionPredicate
import Mettapedia.GSLT.Core.PolicyFamilySufficiency

/-!
# Two distinct proofs in one exact-ledger fibre

Two authored axioms have different rule identities but the same judgment and
no premises. Both therefore inhabit the *same* fixed goal-and-ledger fibre.
The fibre retains the rule choice, whereas its OSLF completion observation
forgets it to existence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.Core
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.Computability.ComputationalTrinityDependentDescent
open OpenSearchMachine

private def judgment : Pattern := .apply "LedgerProof-A" []

private def firstRule : RuleSchema :=
  { id := ⟨"ledger-proof-first"⟩
    metavariables := []
    premises := []
    conclusion := judgment }

private def secondRule : RuleSchema :=
  { id := ⟨"ledger-proof-second"⟩
    metavariables := []
    premises := []
    conclusion := judgment }

private def presentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend (LanguageDef.empty "ledger-proof-relevance")
    { judgments := [{ head := "LedgerProof-A", arity := 0 }]
      rules := [firstRule, secondRule] }

private theorem presentation_valid : presentation.isValid = true := by
  decide +kernel

private def validated : ValidatedCalculusLanguageDef :=
  ⟨presentation, presentation_valid⟩

private def firstInstance : RuleInstance :=
  ⟨⟨"ledger-proof-first"⟩, []⟩

private def secondInstance : RuleInstance :=
  ⟨⟨"ledger-proof-second"⟩, []⟩

private theorem first_instantiates :
    instantiateRule? validated firstInstance = some ([], judgment) := by
  decide +kernel

private theorem second_instantiates :
    instantiateRule? validated secondInstance = some ([], judgment) := by
  decide +kernel

private def firstProof : OpenDerivation validated [] judgment :=
  .byRule firstInstance
    (instantiateRule?_eq_some_iff_application.mp first_instantiates)
    .nil

private def secondProof : OpenDerivation validated [] judgment :=
  .byRule secondInstance
    (instantiateRule?_eq_some_iff_application.mp second_instantiates)
    .nil

private def context : ClassifyingContext validated := ⟨[]⟩

def firstReceipt : exactDerivationFibre validated context judgment [] :=
  ⟨firstProof, rfl⟩

def secondReceipt : exactDerivationFibre validated context judgment [] :=
  ⟨secondProof, rfl⟩

private def rootRuleId {context : List Pattern} {goal : Pattern}
    (proof : OpenDerivation validated context goal) : Option RuleId :=
  match proof with
  | .assumption _ => none
  | .byRule rule _ _ => some rule.ruleId

/-- The two inhabitants have the same judgment and empty ledger, yet retain
distinct authored rule identities. -/
theorem same_fibre_distinct_proofs : firstReceipt ≠ secondReceipt := by
  intro equal
  have proofs : firstProof = secondProof := congrArg Subtype.val equal
  have ruleIds := congrArg rootRuleId proofs
  simp [rootRuleId, firstProof, secondProof, firstInstance, secondInstance]
    at ruleIds

/-- The dependent proof-and-completed-route sum retains two authored rule
choices even at the same exact goal and occurrence ledger. -/
theorem dependent_sigma_retains_rule_choice :
    exactProofCompletedRouteReceipt validated context judgment [] firstReceipt ≠
      exactProofCompletedRouteReceipt validated context judgment [] secondReceipt := by
  intro equal
  have sameFirst := congrArg Sigma.fst equal
  exact same_fibre_distinct_proofs
    ((exactDerivationDisplayedFamily_at validated context judgment []).symm.injective
      sameFirst)

theorem exact_fibre_not_subsingleton :
    ¬ Subsingleton (exactDerivationFibre validated context judgment []) := by
  intro thin
  exact same_fibre_distinct_proofs (Subsingleton.elim firstReceipt secondReceipt)

/-- The canonical map to predicate support actually identifies the two
different checked rule proofs. Its failure to be injective is witnessed in
the authored calculus, not just by a constant two-element example. -/
theorem predicate_support_map_not_injective :
    ¬ Function.Injective
      ((Mettapedia.GSLT.Topos.mapToTrivialFamily
        (exactDerivationDisplayedFamily validated)
        (Mettapedia.GSLT.Topos.support (exactDerivationDisplayedFamily validated))
        le_rfl).app ⟨Opposite.op context, (judgment, [])⟩) := by
  intro injective
  have same := injective
    (a₁ := (exactDerivationDisplayedFamily_at validated context judgment []).symm
      firstReceipt)
    (a₂ := (exactDerivationDisplayedFamily_at validated context judgment []).symm
      secondReceipt) (by rfl)
  exact same_fibre_distinct_proofs
    ((exactDerivationDisplayedFamily_at validated context judgment []).symm.injective same)

#print axioms predicate_support_map_not_injective

/-- The actual total presheaf keeps the two closed proofs distinct even
though its comprehension projection sends them to the same goal and ledger. -/
theorem total_comprehension_retains_rule_choice :
    let totalIso := (exactDerivationTotalIso validated).app (Opposite.op context)
    let first := totalIso.inv ⟨judgment, firstProof⟩
    let second := totalIso.inv ⟨judgment, secondProof⟩
    first ≠ second ∧
      (Mettapedia.TypeTheory.DisplayedPresheafComprehension.totalProjection
        (exactDerivationDisplayedFamily validated)).app
          (Opposite.op context) first =
        (Mettapedia.TypeTheory.DisplayedPresheafComprehension.totalProjection
          (exactDerivationDisplayedFamily validated)).app
            (Opposite.op context) second := by
  dsimp only
  constructor
  · intro same
    have proofAnswers :=
      ((exactDerivationTotalIso validated).app
        (Opposite.op context)).toEquiv.symm.injective same
    exact same_fibre_distinct_proofs
      (Subtype.ext (eq_of_heq (Sigma.mk.inj proofAnswers).2))
  · rfl

/-- The observation's self-pullback contains a genuine off-diagonal
comparison: two different authored certificates share one exact goal and
ledger. Pullback equality is a relation between proofs, not proof identity. -/
theorem goalLedger_selfComparison_offDiagonal :
    let observation := derivationToGoalLedger validated
    let first : (derivationTotalFace validated).obj (Opposite.op context) :=
      ⟨judgment, firstProof⟩
    let second : (derivationTotalFace validated).obj (Opposite.op context) :=
      ⟨judgment, secondProof⟩
    let comparison := selfComparisonPoint observation
      (Opposite.op context) first second rfl
    (totalProjection
      (reindexDisplayed observation
        (observationFibreFamily observation))).app
          (Opposite.op context) comparison ≠
      (totalReindexMap observation (observationFibreFamily observation) ≫
        (observationTotalIso observation).hom).app
          (Opposite.op context) comparison := by
  have different :
      (⟨judgment, firstProof⟩ :
        (derivationTotalFace validated).obj (Opposite.op context)) ≠
        ⟨judgment, secondProof⟩ := by
    intro same
    have proofs : firstProof = secondProof :=
      eq_of_heq (Sigma.mk.inj same).2
    exact same_fibre_distinct_proofs (Subtype.ext proofs)
  exact selfComparisonPoint_offDiagonal
    (derivationToGoalLedger validated) (Opposite.op context)
    ⟨judgment, firstProof⟩ ⟨judgment, secondProof⟩ rfl different

/-- The concrete goal-and-ledger observation cannot license global
reflection of ordinary proof equality; its self-comparison has the
off-diagonal point exhibited above. -/
theorem goalLedger_not_pointwiseInjective :
    ¬ PointwiseInjective (derivationToGoalLedger validated) := by
  intro injective
  have allDiagonal :=
    (pointwiseInjective_iff_selfComparison_diagonal
      (derivationToGoalLedger validated)).mp injective
  exact goalLedger_selfComparison_offDiagonal
    (allDiagonal (Opposite.op context)
      (selfComparisonPoint (derivationToGoalLedger validated)
        (Opposite.op context)
        ⟨judgment, firstProof⟩ ⟨judgment, secondProof⟩ rfl))

/-- Yoneda's representable proof presheaf keeps the two source certificate
elements distinct at the same context, although the modal truth is shared. -/
theorem yoneda_retains_rule_choice :
    openProofYonedaEquiv validated context judgment firstProof ≠
      openProofYonedaEquiv validated context judgment secondProof := by
  intro equal
  have proofs : firstProof = secondProof :=
    (openProofYonedaEquiv validated context judgment).injective equal
  exact same_fibre_distinct_proofs (Subtype.ext proofs)

private def oneGoal : ClassifyingContext validated := ⟨[judgment]⟩

private def firstClosed : context ⟶ oneGoal :=
  openProofYonedaEquiv validated context judgment firstProof

private def secondClosed : context ⟶ oneGoal :=
  openProofYonedaEquiv validated context judgment secondProof

/-- The property generated by the first closed authored proof, with all
its contextual weakenings. This is a genuine substitution-stable predicate. -/
private def firstProofPredicate : Subfunctor (yoneda.obj oneGoal) :=
  Subfunctor.range (yoneda.map firstClosed)

private theorem firstClosed_mem_predicate :
    firstClosed ∈ firstProofPredicate.obj (Opposite.op context) :=
  ⟨𝟙 context, Category.id_comp firstClosed⟩

private theorem secondClosed_not_mem_predicate :
    secondClosed ∉ firstProofPredicate.obj (Opposite.op context) := by
  rintro ⟨environment, equal⟩
  have unique : environment = 𝟙 context := by
    cases environment
    rfl
  change environment ≫ firstClosed = secondClosed at equal
  rw [unique, Category.id_comp] at equal
  exact yoneda_retains_rule_choice equal

/-- Returning the actual argument proof satisfies its proof-sensitive
function contract, under every contextual substitution. -/
theorem argument_program_preserves_authored_proof :
    ClassifyingContext.sndProjection oneGoal oneGoal ∈
      (contextualFunctionPredicate oneGoal oneGoal
        firstProofPredicate firstProofPredicate).obj (Opposite.op oneGoal) :=
  argument_program_preserves_predicate oneGoal oneGoal firstProofPredicate

/-- A same-typed program returning its captured environment proof instead
of its argument fails that contract. Both proofs exist; the failure is
which authored rule was used, not absence of a proof of the goal. -/
theorem captured_program_fails_authored_proof_contract :
    ClassifyingContext.fstProjection oneGoal oneGoal ∉
      (contextualFunctionPredicate oneGoal oneGoal
        firstProofPredicate firstProofPredicate).obj (Opposite.op oneGoal) := by
  intro accepted
  have output := (mem_contextualFunctionPredicate oneGoal oneGoal oneGoal
    firstProofPredicate firstProofPredicate _).mp accepted
      context secondClosed firstClosed firstClosed_mem_predicate
  rw [ClassifyingContext.pair_fst] at output
  exact secondClosed_not_mem_predicate output

/-- Reification of the transformer preserving every property rejects the
captured-proof program for the same concrete authored-proof counterexample. -/
theorem captured_program_fails_preserve_all :
    ClassifyingContext.fstProjection oneGoal oneGoal ∉
      (reifyContextualPredicate oneGoal oneGoal id).obj (Opposite.op oneGoal) := by
  intro held
  exact captured_program_fails_authored_proof_contract
    ((mem_reifyContextualPredicate oneGoal oneGoal oneGoal id _).mp held
      firstProofPredicate)

/-- Evaluation of the two source programs returns the two distinct
authored proofs, using exactly the same environment and argument. -/
theorem argument_and_capture_evaluate_distinctly :
    ClassifyingContext.pair secondClosed firstClosed ≫
        ClassifyingContext.sndProjection oneGoal oneGoal = firstClosed ∧
      ClassifyingContext.pair secondClosed firstClosed ≫
        ClassifyingContext.fstProjection oneGoal oneGoal = secondClosed ∧
      firstClosed ≠ secondClosed :=
  ⟨ClassifyingContext.pair_snd _ _, ClassifyingContext.pair_fst _ _,
    yoneda_retains_rule_choice⟩

private def firstRoute :
    Route (OpenSearchMachine.Step validated [])
      ⟨[judgment], []⟩ ⟨[], []⟩ :=
  .cons (.rule firstInstance
    (instantiateRule?_eq_some_iff_application.mp first_instantiates)
    [] []) (.refl _)

private def secondRoute :
    Route (OpenSearchMachine.Step validated [])
      ⟨[judgment], []⟩ ⟨[], []⟩ :=
  .cons (.rule secondInstance
    (instantiateRule?_eq_some_iff_application.mp second_instantiates)
    [] []) (.refl _)

private theorem firstRoute_reconstructs :
    OpenSearchMachine.derivationOfCompleteRoute firstRoute = firstProof := by
  rfl

private theorem secondRoute_reconstructs :
    OpenSearchMachine.derivationOfCompleteRoute secondRoute = secondProof := by
  rfl

theorem operational_routes_reconstruct :
    OpenSearchMachine.derivationOfCompleteRoute firstRoute = firstProof ∧
      OpenSearchMachine.derivationOfCompleteRoute secondRoute = secondProof :=
  ⟨firstRoute_reconstructs, secondRoute_reconstructs⟩

private def firstRouteRuleId
    {source target : OpenSearchMachine.State []}
    (route : Route (OpenSearchMachine.Step validated []) source target) :
    Option RuleId :=
  match route with
  | .refl _ => none
  | .cons step _ =>
      match step with
      | .rule rule _ _ _ => some rule.ruleId
      | .assumption _ _ _ => none

/-- The operational face also retains the alternative authored rule event;
the collapse happens only at the propositional closure-modal readout. -/
theorem operational_routes_distinct : firstRoute ≠ secondRoute := by
  intro equal
  have ruleIds := congrArg firstRouteRuleId equal
  simp [firstRouteRuleId, firstRoute, secondRoute,
    firstInstance, secondInstance] at ruleIds

/-- Two genuinely different completed machine routes at the same goal and
ledger remain different after entering the proof-indexed dependent sum. -/
theorem dependent_total_retains_distinct_routes :
    completedExecutionToDependentTotal validated context
        ⟨judgment, ⟨[], firstRoute⟩⟩ ≠
      completedExecutionToDependentTotal validated context
        ⟨judgment, ⟨[], secondRoute⟩⟩ := by
  intro same
  have canonicalEqual :=
    (canonicalExecutionToDependentTotal_injective validated context) same
  have rawEqual :=
    (completedRouteAnswerEquiv validated context).injective canonicalEqual
  have receiptsEqual :
      (⟨[], firstRoute⟩ :
        Σ ledger : List (Fin context.judgments.length),
          Route (OpenSearchMachine.Step validated context.judgments)
            ⟨[judgment], []⟩ ⟨[], ledger⟩) =
        ⟨[], secondRoute⟩ :=
    eq_of_heq (Sigma.mk.inj rawEqual).2
  exact operational_routes_distinct
    (eq_of_heq (Sigma.mk.inj receiptsEqual).2)

/-- The common extensional completion receipt is inhabited, but it cannot
identify the two actual rule certificates in the exact proof fibre. -/
theorem completion_forgets_rule_choice :
    gsltDiamond
        (OpenSearchModalAdequacy.theory validated []).closure
        (fun candidate => candidate =
          (⟨[], []⟩ : OpenSearchMachine.State []))
        ⟨[judgment], []⟩ ∧
      firstReceipt ≠ secondReceipt := by
  constructor
  · exact (exactDerivationFibre_nonempty_iff_closureDiamond validated
      context judgment []).mp ⟨firstReceipt⟩
  · exact same_fibre_distinct_proofs

/-- The actual exact-completion modal readout sends each retained proof to
one proof of reachability. Its codomain is proof-irrelevant, whereas the
source fibre has distinct authored certificates. -/
theorem completionObservation
    (receipt : exactDerivationFibre validated context judgment []) :
    gsltDiamond
      (OpenSearchModalAdequacy.theory validated []).closure
      (fun candidate => candidate =
        (⟨[], []⟩ : OpenSearchMachine.State []))
      ⟨[judgment], []⟩ :=
  (exactDerivationFibre_nonempty_iff_closureDiamond validated
    context judgment []).mp ⟨receipt⟩

/-- Observational equality at exact completion cannot reflect intensional
certificate identity even when the goal and ordered ledger are fixed. -/
theorem completionObservation_not_injective :
    ¬ Function.Injective completionObservation := by
  intro reflective
  have observedEqual :
      completionObservation firstReceipt =
        completionObservation secondReceipt := Subsingleton.elim _ _
  exact same_fibre_distinct_proofs (reflective observedEqual)

/-- The genuine canonical-route/derivation/goal-ledger trinity comparison
loses authored rule choice only at its spatial observation edge. -/
theorem canonicalRouteComparison_losesProgramInformation :
    (canonicalRouteComparison validated).LosesProgramInformation := by
  let index : (ClassifyingContext validated)ᵒᵖ := Opposite.op context
  let firstAnswer : (canonicalRouteComparison validated).program.obj index :=
    canonicalRouteOfProof ⟨judgment, firstProof⟩
  let secondAnswer : (canonicalRouteComparison validated).program.obj index :=
    canonicalRouteOfProof ⟨judgment, secondProof⟩
  refine ⟨index, firstAnswer, secondAnswer, ?_, ?_⟩
  · intro equal
    have proofAnswers := congrArg
      (canonicalRouteProofEquiv validated context).toFun equal
    have proofPair :
        (⟨judgment, firstProof⟩ :
          Σ goal : Pattern, OpenDerivation validated [] goal) =
          ⟨judgment, secondProof⟩ := by
      change
        (⟨judgment,
          derivationOfCompleteRoute (runToCompletion firstProof)⟩ :
          Σ goal : Pattern, OpenDerivation validated [] goal) =
          ⟨judgment,
            derivationOfCompleteRoute (runToCompletion secondProof)⟩
        at proofAnswers
      simpa only [derivationOfCompleteRoute_runToCompletion] using proofAnswers
    have proofs : firstProof = secondProof :=
      eq_of_heq (Sigma.mk.inj proofPair).2
    exact same_fibre_distinct_proofs (Subtype.ext proofs)
  · rfl

/-- No natural isomorphism with this actual program-to-space map can turn
the lossy goal-and-ledger observation into an exact trinity edge. -/
theorem canonicalRouteComparison_no_programSpace_iso :
    ¬ ∃ comparisonIso : canonicalRouteFace validated ≅
        goalLedgerFace validated,
      comparisonIso.hom =
        (canonicalRouteComparison validated).programToSpace := by
  rintro ⟨comparisonIso, sameMap⟩
  obtain ⟨index, left, right, distinct, sameObservation⟩ :=
    canonicalRouteComparison_losesProgramInformation
  have sameIso : comparisonIso.hom.app index left =
      comparisonIso.hom.app index right := by
    rw [sameMap]
    exact sameObservation
  exact distinct ((comparisonIso.app index).toEquiv.injective sameIso)

/-- The same two canonical routes also collapse at the actual OSLF
closure-modal support face, not merely after forgetting to ledger data. -/
theorem canonicalRouteModalComparison_losesProgramInformation :
    (canonicalRouteModalComparison validated).LosesProgramInformation := by
  obtain ⟨index, left, right, distinct, sameLedger⟩ :=
    canonicalRouteComparison_losesProgramInformation
  refine ⟨index, left, right, distinct, ?_⟩
  apply Subtype.ext
  have leftForget :
      ((canonicalRouteModalComparison validated).programToSpace.app
        index left).val =
      (canonicalRouteComparison validated).programToSpace.app index left := by
    have square := congrArg
      (fun transformation => transformation.app index left)
      (canonicalRouteModalComparison_forget validated)
    change
      ((canonicalRouteModalComparison validated).programToSpace.app
        index left).val =
      (canonicalRouteComparison validated).programToSpace.app index left
      at square
    exact square
  have rightForget :
      ((canonicalRouteModalComparison validated).programToSpace.app
        index right).val =
      (canonicalRouteComparison validated).programToSpace.app index right := by
    have square := congrArg
      (fun transformation => transformation.app index right)
      (canonicalRouteModalComparison_forget validated)
    change
      ((canonicalRouteModalComparison validated).programToSpace.app
        index right).val =
      (canonicalRouteComparison validated).programToSpace.app index right
      at square
    exact square
  exact leftForget.trans (sameLedger.trans rightForget.symm)

theorem canonicalRouteModalComparison_no_programSpace_iso :
    ¬ ∃ comparisonIso : canonicalRouteFace validated ≅
        completionSupportFace validated,
      comparisonIso.hom =
        (canonicalRouteModalComparison validated).programToSpace := by
  rintro ⟨comparisonIso, sameMap⟩
  obtain ⟨index, left, right, distinct, sameObservation⟩ :=
    canonicalRouteModalComparison_losesProgramInformation
  have sameIso : comparisonIso.hom.app index left =
      comparisonIso.hom.app index right := by
    rw [sameMap]
    exact sameObservation
  exact distinct ((comparisonIso.app index).toEquiv.injective sameIso)

/-- Extensional closure-modal equality cannot be reflected into equality
of authored proofs, even though operational routes and proofs are naturally
isomorphic on the canonical fragment. -/
theorem modalObservation_does_not_reflect_proof_identity :
    ¬ ∀ (index : (ClassifyingContext validated)ᵒᵖ)
      (left right : (canonicalRouteModalComparison validated).program.obj index),
      (canonicalRouteModalComparison validated).programToSpace.app index left =
        (canonicalRouteModalComparison validated).programToSpace.app index right →
      (canonicalRouteModalComparison validated).programToLogic.app index left =
        (canonicalRouteModalComparison validated).programToLogic.app index right := by
  intro reflects
  obtain ⟨index, left, right, distinct, sameObservation⟩ :=
    canonicalRouteModalComparison_losesProgramInformation
  have sameProof := reflects index left right sameObservation
  have sameRoute : left = right :=
    ((canonicalRouteProofIso validated).app index).toEquiv.injective sameProof
  exact distinct sameRoute

/-! ## Observer-relative answer views -/

/-- A contextual successful route with its context retained. -/
private abbrev ContextualRouteAnswer :=
  Σ index : (ClassifyingContext validated)ᵒᵖ,
    (canonicalRouteModalComparison validated).program.obj index

/-- The closure-modal observation retains its context but not its route. -/
private abbrev ContextualModalAnswer :=
  Σ index : (ClassifyingContext validated)ᵒᵖ,
    (canonicalRouteModalComparison validated).space.obj index

/-- The authored proof observation retains its context and rule choices. -/
private abbrev ContextualProofAnswer :=
  Σ index : (ClassifyingContext validated)ᵒᵖ,
    (canonicalRouteModalComparison validated).logic.obj index

private abbrev ContextualGoalLedgerAnswer :=
  Σ index : (ClassifyingContext validated)ᵒᵖ,
    (goalLedgerFace validated).obj index

private def modalAnswerView : ContextualRouteAnswer → ContextualModalAnswer
  | ⟨index, route⟩ =>
      ⟨index, (canonicalRouteModalComparison validated).programToSpace.app
        index route⟩

private def proofAnswerView : ContextualRouteAnswer → ContextualProofAnswer
  | ⟨index, route⟩ =>
      ⟨index, (canonicalRouteModalComparison validated).programToLogic.app
        index route⟩

private def goalLedgerAnswerView :
    ContextualRouteAnswer → ContextualGoalLedgerAnswer
  | ⟨index, route⟩ =>
      ⟨index, (canonicalRouteComparison validated).programToSpace.app
        index route⟩

/-- A client that requests the contextual goal and exact occurrence ledger. -/
private def goalLedgerPolicy : PolicyFamily ContextualRouteAnswer where
  Policy := Unit
  Result := fun _ => ContextualGoalLedgerAnswer
  decide := fun _ => goalLedgerAnswerView

/-- A client that requests the actual contextual authored proof. -/
private def proofInspectionPolicy : PolicyFamily ContextualRouteAnswer where
  Policy := Unit
  Result := fun _ => ContextualProofAnswer
  decide := fun _ => proofAnswerView

/-- The supported modal answer still serves a client that inspects the
goal and exact occurrence ledger, through the proved forgetful square. -/
theorem modalAnswerView_supports_goalLedgerPolicy :
    goalLedgerPolicy.SupportsReadout modalAnswerView := by
  refine ⟨{
    run := fun _ answer =>
      ⟨answer.1, (forgetCompletionSupport validated).app answer.1 answer.2⟩
    agrees := ?_ }⟩
  intro policy answer
  cases answer with
  | mk index route =>
      have square := congrArg
        (fun transformation => transformation.app index route)
        (canonicalRouteModalComparison_forget validated)
      exact congrArg (Sigma.mk index) square

/-- The same readout cannot serve a client allowed to inspect the authored
proof: the two-axiom canary collides in modal support but not in proof. -/
theorem modalAnswerView_refuses_proofInspectionPolicy :
    ¬ proofInspectionPolicy.SupportsReadout modalAnswerView := by
  obtain ⟨index, left, right, distinct, sameObservation⟩ :=
    canonicalRouteModalComparison_losesProgramInformation
  apply proofInspectionPolicy.not_supportsReadout_of_policy_collision
    modalAnswerView (first := ⟨index, left⟩) (second := ⟨index, right⟩)
    (congrArg (Sigma.mk index) sameObservation) ()
  intro sameProofAnswer
  have sameProof :
      (canonicalRouteModalComparison validated).programToLogic.app index left =
        (canonicalRouteModalComparison validated).programToLogic.app index right :=
    eq_of_heq (Sigma.mk.inj sameProofAnswer).2
  have sameRoute : left = right :=
    ((canonicalRouteProofIso validated).app index).toEquiv.injective sameProof
  exact distinct sameRoute

/-- A concrete validated pair of closed rule proofs admits two different
independent schedules, both returning the very same authored proof pair. -/
theorem independent_schedules_same_proofs :
    let leftFirst := Interleaving.leftThenRight
      (runToCompletion firstProof) (runToCompletion secondProof)
    let rightFirst := Interleaving.rightThenLeft
      (runToCompletion firstProof) (runToCompletion secondProof)
    leftFirst ≠ rightFirst ∧
      IndependentSearch.proofPair leftFirst = (firstProof, secondProof) ∧
      IndependentSearch.proofPair rightFirst = (firstProof, secondProof) :=
  IndependentSearch.same_proofs_distinct_schedules firstProof secondProof

/-- In this inhabited closed-proof example, a schedule-sensitive consumer
cannot be recovered after forgetting to the exact proof pair. -/
theorem proof_pair_cannot_recover_schedule :
    ¬ ∃ observe : (OpenDerivation validated [] judgment ×
        OpenDerivation validated [] judgment) → List Bool,
      ∀ route : IndependentSearch.CompletedRoute
        (leftDefinition := validated) (rightDefinition := validated)
        (leftContext := []) (rightContext := [])
        (leftGoal := judgment) (rightGoal := judgment) [] [],
        observe (IndependentSearch.proofPair route) =
          Route.trace Interleaving.side route :=
  IndependentSearch.schedule_does_not_factor_through_proofPair
    firstProof secondProof

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.same_fibre_distinct_proofs
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.dependent_sigma_retains_rule_choice
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.dependent_total_retains_distinct_routes
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.independent_schedules_same_proofs
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.proof_pair_cannot_recover_schedule
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.exact_fibre_not_subsingleton
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.total_comprehension_retains_rule_choice
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.goalLedger_selfComparison_offDiagonal
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.goalLedger_not_pointwiseInjective
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.yoneda_retains_rule_choice
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.argument_program_preserves_authored_proof
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.captured_program_fails_authored_proof_contract
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.captured_program_fails_preserve_all
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.argument_and_capture_evaluate_distinctly
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.operational_routes_distinct
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.operational_routes_reconstruct
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.completion_forgets_rule_choice
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.completionObservation_not_injective
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.canonicalRouteComparison_losesProgramInformation
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.canonicalRouteComparison_no_programSpace_iso
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.canonicalRouteModalComparison_losesProgramInformation
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.canonicalRouteModalComparison_no_programSpace_iso
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.modalObservation_does_not_reflect_proof_identity
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.modalAnswerView_supports_goalLedgerPolicy
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ProofRelevanceCanary.modalAnswerView_refuses_proofInspectionPolicy
