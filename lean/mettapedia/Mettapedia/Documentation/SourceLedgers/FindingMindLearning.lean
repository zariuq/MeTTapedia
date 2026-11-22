import Mathlib.Data.Finset.Basic

/-!
# Finding Mind Chapter 21 source inventory

Each numbered entry has one reference, its source location, mathematical scope,
explicit hypotheses, exact declaration references and the remaining gap.
Coverage is metadata about those named declarations, not a proof of the source
statement. Checked corrections have only the extent recorded in evidence and
in the gap. Definitions and interpretative remarks are not theorem closures.
The predation correction retains its restricted compiler and reaction profiles;
the original full-context source claim remains partial.
-/

set_option autoImplicit false

namespace Mettapedia.Documentation.SourceLedgers.FindingMindLearning

inductive Kind where
  | definitionEntry | lemmaEntry | propositionEntry | theoremEntry
  | corollaryEntry | conjectureEntry | remarkEntry
  deriving DecidableEq

inductive Coverage where
  | exactCoverage | correctedCoverage | partialCoverage | openCoverage | interpretativeCoverage
  deriving DecidableEq

structure Evidence where
  moduleName : String
  declaration : String
  scope : String

structure Entry where
  kind : Kind
  number : Nat
  title : String
  sourceSection : String
  page : Nat
  sourceLine : Nat
  statement : String
  hypotheses : List String
  sourceProof : String
  evidence : List Evidence
  coverage : Coverage
  gap : String

def sourceRevision : String := "1f7bd34b11e65d707dde4b3638d08a181e1b8028"
def sourcePdfSha256 : String := "ce82c37693fb47864d9649cac480c31a2cba07bbca6a05b7e4da9a0d1b1fee6d"

def entries : List Entry := [
  { kind := .remarkEntry
    number := 1
    title := "Adequate for which relation"
    sourceSection := "21.1.5"
    page := 219
    sourceLine := 7349
    statement := "For a stated observation signature Ob, the generated structural/modal logic should characterize bisimilarity in Obs(S,Ob), not ordinary base-theory bisimilarity."
    hypotheses := ["The observation signature and permitted proper interactions are fixed.", "Adequacy is relative to the chosen syntax, equations, interface and modal expressiveness."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase", "Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase.instrumented_partial_adequacy", "Actual original scoped rho proper-interaction base: scoped logical equivalence iff instrumented bisimilarity for any partial constructor kit. The logic is the independently defined scoped infinitary logic."⟩,
      ⟨"Mettapedia.OSLF.Framework.SortedTypedInstrumentKitModalComparison", "Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit.Modal.actual_ipo_iff_modal_observation_of_generated", "Finitary interface-modal equivalence iff actual IPO bisimilarity for a hereditarily generated left value, a supported right value and nonempty native origins."⟩]
    coverage := .partialCoverage
    gap := "The scoped and generated-value adequacy theorems have explicit profiles; no single comparison identifies all of Chapter 21 namespace logic, including H and graded separation, with the complete printed observer extension." },
  { kind := .remarkEntry
    number := 2
    title := "Three restrictions, and only the third is a budget"
    sourceSection := "21.1.6"
    page := 220
    sourceLine := 7376
    statement := "Full structural capability, a restricted instrument kit and finite funding impose separate observational restrictions; increasing money does not create a missing instrument."
    hypotheses := ["A fixed instrumented theory and a separately specified funding procedure.", "Full reconstruction requires the full admitted constructor kit; smaller kits need not be strictly coarser in every model."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase", "Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase.instrumented_reconstruction", "A complete constructor kit gives bisimilarity iff EqClosure rhoSourceE; larger_kit_refines separately proves monotonicity for arbitrary partial kits."⟩,
      ⟨"Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission", "Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission.prepared_response", "Every actual funded structural response proves complete question admission, its exact readout, affordability and purse balance."⟩,
      ⟨"Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission", "Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission.Controls.funding_does_not_supply_missing_instrument", "For the fixed independently supplied paired-tree question, the empty kit rejects at every budget; separate controls show an admitted complete kit can remain underfunded."⟩]
    coverage := .partialCoverage
    gap := "The three restrictions are individually realized, but the full Chapter 21 learner/observer/paid-execution comparison is not assembled. Strict loss from each restriction is model dependent." },
  { kind := .remarkEntry
    number := 3
    title := "Restriction is sugar"
    sourceSection := "21.3.1"
    page := 223
    sourceLine := 7508
    statement := "As printed, new is decentralized structural name manufacture with scope-relative freshness; name predicates see into names, name size incurs running cost, and concealment is price rather than secrecy. A central registry is said to contradict isolation."
    hypotheses := ["The reflective rho name representation.", "A chosen decentralized manufacturing scheme and an explicit scope/freshness condition.", "A separately imposed sensing/maintenance tariff if name size is to incur ongoing cost."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation", "Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation.fresh_above_namespace_bound", "A concrete quoted structural name stream stays inequivalent to every member of a bounded finite public namespace when the starting index exceeds all its communication counts."⟩,
      ⟨"Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmission", "Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmission.original_structural_test_is_interactive", "For held constructor instruments, a structural node test is equivalent to ask/get interactions with child tests."⟩]
    coverage := .partialCoverage
    gap := "No theorem supplies the chapter-wide new sugar, decentralized freshness against arbitrary future manufacture, or size-based running cost. The claim that any central name server contradicts interaction-only isolation does not follow merely from being an interacting server." },
  { kind := .definitionEntry
    number := 1
    title := "Depth"
    sourceSection := "21.3.2"
    page := 223
    sourceLine := 7535
    statement := "Define structural depth recursively by top=0, in/out/H adding one, separation taking max and quotation adding zero."
    hypotheses := ["A structural-formula syntax containing the displayed constructors.", "Quotation is intentionally graded as free access to an already-held name."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Framework.InstrumentTestDecision", "Mettapedia.OSLF.Framework.InstrumentObservations.structuralDepth", "Actual finite-arity structural-test syntax: top has depth zero, negation preserves depth, conjunction takes max, headed constructor tests add one to the maximum child depth."⟩]
    coverage := .partialCoverage
    gap := "The existing structuralDepth is for first-order constructor tests, not the exact full rho namespace syntax with the special H, parallel and zero-cost quotation clauses. No exact syntax-translation/depth comparison was found." },
  { kind := .definitionEntry
    number := 2
    title := "Sensing, and its price"
    sourceSection := "21.3.2"
    page := 223
    sourceLine := 7542
    statement := "For W ≡ S|E, S may evaluate a structural formula φ against E whenever d(φ)≤α, debiting κsense(d(φ)); κsense is monotone and α is whatever depth S can currently afford. Remark 21.4 additionally holds its instrument signature fixed."
    hypotheses := ["A declared monotone sensing schedule.", "The relevant instruments are held, as required by Remark 21.4.", "A finite maximum affordable depth requires more than monotonicity alone, such as an unbounded tariff."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Framework.StructuralInspectionAssays", "Mettapedia.OSLF.Framework.InstrumentObservations.maximal_paid_inspection", "An affordable maximal actual resource-system path produces its earned structural truth/refutation certificate and unique verdict."⟩,
      ⟨"Mettapedia.OSLF.Framework.StructuralInspectionAssays", "Mettapedia.OSLF.Framework.InstrumentObservations.inspection_fee_conserved", "The paid inspection debits exactly the independently computed traversalWork."⟩,
      ⟨"Mettapedia.OSLF.Framework.InstrumentTestExecution", "Mettapedia.OSLF.Framework.InstrumentObservations.inspection_at_fixed_depth_can_exceed", "At structural depth zero, true tests can have arbitrarily high computed inspection work; a depth-only tariff is not a derived execution-cost bound."⟩]
    coverage := .partialCoverage
    gap := "Paid sensing exists with actual traversal accounts, but not the exact tariff/acuity definition on W ≡ S|E. A monotone tariff need not determine a finite acuity, and formula depth alone does not bound execution work." },
  { kind := .remarkEntry
    number := 4
    title := "Senses are instruments, and instruments are held"
    sourceSection := "21.3.2"
    page := 224
    sourceLine := 7555
    statement := "Structural senses are admitted destructuring instruments in an observer extension; capability and price are independent, and checking work depends on branching and strategy as well as structural depth."
    hypotheses := ["Explicit constructor permission Ob.", "An admitted observer extension and separately chosen evaluation strategy."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmission", "Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmission.original_structural_test_is_interactive", "A structural constructor test with a permitted constructor is characterized by actual ask/get interactions and all child predicates in the original scoped rho base."⟩,
      ⟨"Mettapedia.OSLF.Framework.InstrumentQuestionAdmission", "Mettapedia.OSLF.Framework.InstrumentQuestionAdmission.check_iff", "Executable checking of all constructor permissions exactly characterizes complete formula admission."⟩,
      ⟨"Mettapedia.OSLF.Framework.InstrumentTestExecution", "Mettapedia.OSLF.Framework.InstrumentObservations.inspection_at_fixed_depth_can_exceed", "An explicit negative control proves that fixed structural depth alone cannot bound complete inspection work."⟩]
    coverage := .partialCoverage
    gap := "The held-instrument and depth/cost distinctions are proved for actual profiles; the exact chapter-wide H/graded-separation operational translation and its full observer conservativity still need a joined source comparison." },
  { kind := .definitionEntry
    number := 3
    title := "Assay"
    sourceSection := "21.4.2"
    page := 225
    sourceLine := 7622
    statement := "An assay is a pair (K,φ) realized by a probe K together with two parallel receipts on the same probe channel p, guarded by φ(x) and ¬φ(x), whose continuations emit confirm!(*x) and refute!(*x), respectively."
    hypotheses := ["An operationally admitted and decidable guard on received data.", "A probe channel and independently supplied delivery/probe mechanism.", "For eventual output, sufficient funds and completion/scheduling conditions beyond guard exclusivity."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.GSLT.Causality.ComplementaryAssay", "Mettapedia.GSLT.Causality.ComplementaryAssay.system", "Concrete linear resource rules consume a session message and the uniquely matching receiver and emit the addressed result; enabled_fields proves the selected branch."⟩,
      ⟨"Mettapedia.OSLF.Framework.RhoScopedReactionAssayReceipts", "Mettapedia.OSLF.Framework.RhoScopedReactionAssayReceipts.complementary_guards_never_race", "Opposite Boolean guards cannot both hold on rho-equation-equivalent raw terms for a genuine unfolding guard."⟩,
      ⟨"Mettapedia.OSLF.Framework.RhoScopeWhereNativeReceipts", "Mettapedia.OSLF.Framework.RhoScopeWhereNativeReceipts.nativeReceipt", "An actual admitted guarded rho firing yields the corresponding native scope decision receipt, retaining captured payload conditions."⟩,
      ⟨"Mettapedia.OSLF.Framework.RhoScopeWhereFundedComparison", "Mettapedia.OSLF.Framework.RhoScopeWhereFundedComparison.response_agrees_with_actual_rho", "For two independently authored confirm/refute specimens, a paid response agrees with the actual guarded rho rewrite and retains the ledger; this is readout comparison, not arbitrary probe operational refinement."⟩]
    coverage := .partialCoverage
    gap := "No complete lowering/refinement of arbitrary source probe K and full namespace guard into one metered rho world is established. The displayed definition does not itself provide progress, scheduler fairness or affordability." },
  { kind := .propositionEntry
    number := 1
    title := "Trichotomy"
    sourceSection := "21.4.2"
    page := 226
    sourceLine := 7638
    statement := "As printed, for an assay (K,φ) whose received-term guard is decidable within the ambient budget, exactly one guard is enabled for each arriving message, and the outcome is CONFIRM, REFUTE or ⊥, with ⊥ iff no message arrived before budget exhaustion. The proved resource-system correction additionally requires affordable maximal/completed execution to infer a verdict and separates waiting from underfunding."
    hypotheses := ["A total Boolean decider agrees with φ on the received payload.", "The delivered message and designated receivers are present.", "Affordability and maximality/completion are needed to infer an emitted verdict from enablement."]
    sourceProof := "sketch"
    evidence := [⟨"Mettapedia.GSLT.Causality.ComplementaryAssay", "Mettapedia.GSLT.Causality.ComplementaryAssay.enabled_fields", "Every enabled instance on the ready one-message marking has exactly the supplied session/origin/payload and verdictOf(test payload)."⟩,
      ⟨"Mettapedia.GSLT.Causality.FundedAssayCompletion", "Mettapedia.GSLT.Causality.ComplementaryAssay.maximal_affordable_verdict", "Every affordable maximal occurrence path from a ready assay emits the unique verdict and has one firing."⟩,
      ⟨"Mettapedia.GSLT.Causality.FundedAssayCompletion", "Mettapedia.GSLT.Causality.ComplementaryAssay.paid_path_cases", "An arbitrary finite funded prefix may have zero firings even with a delivered message; an actual firing requires the price bound."⟩,
      ⟨"Mettapedia.GSLT.Causality.FundedAssayCompletion", "Mettapedia.GSLT.Causality.ComplementaryAssay.underfunded_prefix_quiet", "A delivered but underfunded message gives no verdict in every permitted prefix."⟩]
    coverage := .correctedCoverage
    gap := "The resource-system correction is proved. The printed unqualified outcome claim is not: enabled is not fired, and silence is not by itself no arrival. Arbitrary rho-probe operational adequacy remains separate." },
  { kind := .propositionEntry
    number := 2
    title := "Asymmetry of the modalities"
    sourceSection := "21.4.3"
    page := 226
    sourceLine := 7657
    statement := "As printed: (1) an existential over redex positions has a finite confirmation witness but refutation requires every position; a universal has a one-position finite refutation and no finite-run confirmation; (2) for a fixed position, a firing confirms ⟨Kj⟩ψ but its negation has no finite witness because enabling may occur later. The original current-step and eventual-future readings are not equivalent."
    hypotheses := ["The semantics must distinguish current one-step modalities from eventual enabling over arbitrary futures.", "The support of positions/successors may be finite and effectively complete.", "Postcondition decidability is also required; a step alone does not decide an arbitrary ψ."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.OSLF.Framework.RhoScopedFundedInspection", "Mettapedia.OSLF.Framework.RhoScopedFundedInspection.inspection_falsehood", "A complete finite HML inspection on the actual scoped rho successor presentation characterizes negated modal satisfaction; inspection_truth gives the positive comparison."⟩,
      ⟨"Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase", "Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase.proper_targets_finite", "For a fixed original rho label and term, the entire target support is finite via the actual reaction catalogue."⟩,
      ⟨"Mettapedia.OSLF.Syntax.RhoScopedNativeAbsence", "Mettapedia.OSLF.Binding.RhoScopedNativeAbsence.full_absence_iff_future", "Full native absence quantifies over every future syntactic substitution."⟩,
      ⟨"Mettapedia.OSLF.Syntax.RhoScopedNativeAbsence", "Mettapedia.OSLF.Binding.RhoScopedNativeAbsence.permitted_absence_iff_current", "Only on the explicit retractable-future category does native absence reduce to current reaction absence."⟩]
    coverage := .partialCoverage
    gap := "The source proposition as written is false without qualifications: complete finite support can settle universal current-step claims and their negations. Existing results formalize the required distinctions, not the universal impossibility assertion." },
  { kind := .remarkEntry
    number := 5
    title := "Which asymmetry does which job"
    sourceSection := "21.4.3"
    page := 226
    sourceLine := 7672
    statement := "As printed, position quantification bounds the testable fragment through modal depth, and unbounded waiting explains why complementary guards are necessary; the two asymmetries must not be conflated and both are asserted true. The unqualified assertions inherit Proposition 21.2's finite-support/future-semantics problem."
    hypotheses := ["The corrected modal distinctions of Proposition 21.2.", "A budget and an explicit completion condition for guard evaluation."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.GSLT.Causality.FundedAssayCompletion", "Mettapedia.GSLT.Causality.ComplementaryAssay.pending_prefix_quiet", "A session with no offered message cannot emit a verdict along any actual finite funded prefix."⟩,
      ⟨"Mettapedia.OSLF.Syntax.RhoScopedNativeAbsence", "Mettapedia.OSLF.Binding.RhoScopedNativeAbsence.full_absence_iff_future", "Future-stable absence has explicit universal future quantification, rather than being identified with a failed current guard."⟩]
    coverage := .partialCoverage
    gap := "The source sentence that both of Proposition 21.2 conclusions hold without qualification inherits its error. Modal depth is not specifically alternation depth, and the complete learner fragment cannot be inferred from depth alone." },
  { kind := .definitionEntry
    number := 4
    title := "Revision"
    sourceSection := "21.5"
    page := 227
    sourceLine := 7712
    statement := "A hypothesis revision is a step in a specified logical-strength relaxation order, deleting or restoring conjunctive information; a policy generates a walk in that order."
    hypotheses := ["A characteristic-formula relaxation order and its orientation are specified.", "The meet/conjunct presentation is distinguished from syntactic and semantic formula equality."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Framework.FiniteAssayLearner", "Mettapedia.OSLF.Framework.FiniteAssayLearner.revise", "Finite hypothesis candidate filtering from actual Boolean response packets; this removes inconsistent candidates, not conjuncts in a characteristic formula."⟩,
      ⟨"Mettapedia.OSLF.Framework.NuRevisionMetric", "Mettapedia.OSLF.Framework.NuRevision.scheme", "Hypothesis observations are genuine positive-body greatest-fixed-point unfolding predicates; no relaxation-lattice operation is defined here."⟩]
    coverage := .partialCoverage
    gap := "Finite candidate elimination and actual unfolding observations exist, but neither defines the printed relaxation lattice or its weakening/restoration moves." },
  { kind := .definitionEntry
    number := 5
    title := "Stratified distance"
    sourceSection := "21.5"
    page := 227
    sourceLine := 7718
    statement := "As printed, if two formulas first disagree at ν-unfolding stage n then d(φ,ψ)=2^(-n), and this is an ultrametric. The proved correction assigns zero to full stage agreement and obtains a genuine metric on the quotient by agreement of all approximants, rather than raw syntax or mere equality of the limit predicate."
    hypotheses := ["Positive finite modal bodies give the chosen ν-unfolding stages.", "Equality means equality of each approximant denotation over a fixed LTS.", "For a genuine metric, quotient by complete unfolding-sequence agreement."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Framework.NuRevisionMetric", "Mettapedia.OSLF.Framework.NuRevision.scheme", "The stage observations are actual satisfaction sets of capture-avoiding ν-unfoldings, not freely authored placeholder sequences."⟩,
      ⟨"Mettapedia.OSLF.Framework.LogicalMetric", "Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.distance_eq", "On distinct observation sequences the distance is exactly (1/2)^separatingRank."⟩,
      ⟨"Mettapedia.OSLF.Framework.LogicalMetric", "Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.quotientMetricSpace", "A genuine metric is constructed on the observation-kernel quotient; quotient_distance_triangle_nonarch proves its strong triangle law."⟩,
      ⟨"Mettapedia.OSLF.Framework.FundedNuAssayControls", "Mettapedia.OSLF.Framework.FundedNuAssayControls.equal_limits_do_not_give_zero_revision_distance", "Two independently authored positive modal bodies have equal greatest-fixed-point predicates but distinct actual approximation sequences, so limit equivalence is not the metric quotient."⟩]
    coverage := .correctedCoverage
    gap := "The first-difference construction is proved for genuine positive HML unfoldings. The source omits zero-distance identification and calls raw formula syntax an ultrametric; equality of limit denotations is also insufficient. Full namespace-logic syntax remains a separate comparison." },
  { kind := .propositionEntry
    number := 3
    title := "The limit of inquiry is unaffordable"
    sourceSection := "21.5"
    page := 228
    sourceLine := 7730
    statement := "For an environment E whose behavior is not eventually structural, described as recursion following reduction rather than a finite structural cycle, χE is claimed inexact at every finite unfolding and impossible for any finite-token scientist to install as a guard."
    hypotheses := ["Non-stabilization must be a mathematical condition, not merely the phrase recursion follows reduction.", "A specified observer class and metering procedure.", "Installing finite syntax must be distinguished from deciding its semantics."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.OSLF.Framework.NuInfiniteUnfoldingControls", "Mettapedia.OSLF.Framework.NuInfiniteUnfoldingControls.no_finite_stage_is_the_original_predicate", "For the actual Option Nat family of finite chains and a persistent loop, no finite continuation ν-unfolding equals the original predicate despite successor lists of size at most one."⟩,
      ⟨"Mettapedia.OSLF.Framework.FundedNuBudgetSeparation", "Mettapedia.OSLF.Framework.FundedNuBudgetSeparation.bounded_profile_does_not_classify_limit", "No classifier of the complete bounded-budget continuation-test profile decides its original ν predicate; this uses actual instruction receipts and spent counts."⟩]
    coverage := .partialCoverage
    gap := "These are genuine restricted-observer impossibility examples, not a theorem for every non-eventually-structural rho environment or arbitrary guard installation. Finite syntax can denote an infinite fixed point; the source argument conflates writing it with deciding it." },
  { kind := .remarkEntry
    number := 6
    title := "When a finite theory is complete"
    sourceSection := "21.5"
    page := 228
    sourceLine := 7740
    statement := "As printed, recursion following structure is exact at a finite unfolding, with ν(2n)=ν for a diagram having 2n arcs, and a finite theory is complete exactly when the environment's regularity is structural; recursion following reduction is claimed unbounded."
    hypotheses := ["Finite state carrier for the existing ν stabilization theorem.", "Complete structural instruments for full finite-tree characteristic tests.", "The referenced 2n-arc diagram-specific bound has its own source hypotheses."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.Logic.ModalNuUnfoldings", "Mettapedia.Logic.ModalMuCalculus.Unfolding.finite_stage_equals_original", "On any finite State and any positive HML body, every stage at least Nat.card State equals the original ν predicate; this includes dynamically defined finite transition systems."⟩,
      ⟨"Mettapedia.OSLF.Framework.InstrumentShapeTests", "Mettapedia.OSLF.Framework.InstrumentObservations.shapeFormula_spec", "The recursively constructed complete finite-tree test holds exactly of its given tree; admission requires the relevant constructor kit."⟩]
    coverage := .partialCoverage
    gap := "No proved necessary-and-sufficient structural/nonstructural criterion or exact 2n-arc comparison is present. General finite-state stabilization shows that following reduction does not alone force an unbounded unfolding." },
  { kind := .remarkEntry
    number := 7
    title := "There is no gradient"
    sourceSection := "21.6.1"
    page := 229
    sourceLine := 7768
    statement := "As printed, gradient methods are not well typed on the hypothesis ultrametric because it lacks arbitrarily small directional interpolation, so available search is tree search. The existing mathematical support establishes ultrametric confinement, not a universal prohibition of additional optimization structures."
    hypotheses := ["Only the metric/order structure declared for hypotheses is available.", "No additional differentiable or interpolation structure has been chosen."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.OSLF.Framework.LogicalMetric", "Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.distance_triangle_nonarch", "The actual observation distance satisfies the strong ultrametric inequality."⟩,
      ⟨"Mettapedia.OSLF.Framework.AssayRevisionMetric", "Mettapedia.OSLF.Framework.AssayRevision.finite_walk_confined", "Finite walks whose every move lies below one fixed dyadic radius stay inside it."⟩]
    coverage := .interpretativeCoverage
    gap := "No theorem rules out every possible gradient-like method or proves that all policies must be tree search; the source uses absence of additional structure as a methodological interpretation." },
  { kind := .propositionEntry
    number := 4
    title := "Confinement"
    sourceSection := "21.6.1"
    page := 229
    sourceLine := 7779
    statement := "For every finite revision walk and n, if each consecutive distance is strictly below 2^(-n), then the first-to-last distance is strictly below 2^(-n)."
    hypotheses := ["A fixed first-difference observation ultrametric, including the genuine ν-unfolding scheme.", "The same strict dyadic radius bounds every step of the finite walk."]
    sourceProof := "proof"
    evidence := [⟨"Mettapedia.OSLF.Framework.AssayRevisionMetric", "Mettapedia.OSLF.Framework.AssayRevision.finite_walk_confined", "Exactly the universal finite-walk/dyadic-radius statement; induction applies the earned strong triangle inequality, with no assumed endpoint closeness."⟩,
      ⟨"Mettapedia.OSLF.Framework.NuRevisionMetric", "Mettapedia.OSLF.Framework.NuRevision.finite_walk_certificate_preserved", "Instantiates the confinement law for genuine ν-unfolding predicates and transports their actual earlier stage certificates along the walk."⟩]
    coverage := .exactCoverage
    gap := "No gap in the stated finite-walk confinement law. It proves neither a policy-selection claim nor any price/distance identity." },
  { kind := .definitionEntry
    number := 6
    title := "Revision move"
    sourceSection := "21.6.2"
    page := 229
    sourceLine := 7797
    statement := "A revision move is a formula-tree locus together with weakening or strengthening at that locus; the locus is claimed to fix direction and its depth to fix the metric distance."
    hypotheses := ["A concrete formula-tree context and edit semantics.", "A comparison from the selected syntactic locus to changed ν approximants."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Framework.NuRevisionMetric", "Mettapedia.OSLF.Framework.NuRevision.scheme", "Measures first semantic approximation change of positive bodies; it does not identify a syntactic edit locus with that rank."⟩]
    coverage := .partialCoverage
    gap := "No exact locus-plus-operation revision datatype or comparison theorem was found. Syntactically changing a redundant/equivalent clause need not change any denotation, so locus depth alone cannot unconditionally fix distance." },
  { kind := .propositionEntry
    number := 5
    title := "Cost is monotone in distance"
    sourceSection := "21.6.2"
    page := 230
    sourceLine := 7818
    statement := "Evidence from a modal-depth-k assay is claimed to bear on approximants k and above; a distance-2^(-n) revision therefore allegedly invalidates exactly the confirmations at depths n or greater, with the invalidation count nondecreasing in distance."
    hypotheses := ["A fixed ν-unfolding observation scheme.", "Any discarded-evidence policy and ledger must be explicitly defined and distinguished from logical invalidity.", "An actual testing algorithm is needed for testing costs."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.OSLF.Framework.NuRevisionMetric", "Mettapedia.OSLF.Framework.NuRevision.earlier_certificate_preserved", "Certificates are transported only at stages guaranteed equal by the distance bound; no theorem says all other certificates fail."⟩,
      ⟨"Mettapedia.OSLF.Framework.AssayRevisionControls", "Mettapedia.OSLF.Framework.AssayRevision.Controls.prices_remain_different", "Two structural hypotheses with identical semantic stage answers have independently computed prices 1 and 11."⟩,
      ⟨"Mettapedia.OSLF.Framework.AssayRevisionControls", "Mettapedia.OSLF.Framework.AssayRevision.Controls.exact_agreement_does_not_supply_testing_funds", "At the same purse, semantically agreeing compact and verbose structural tests respectively answer and remain silent."⟩]
    coverage := .partialCoverage
    gap := "The printed exact-invalidation and consequent monotone cost claim are not established and do not follow from first difference. Later-stage truths can remain valid, and semantic distance does not determine traversal work." },
  { kind := .remarkEntry
    number := 8
    title := "Two gradings, one poset"
    sourceSection := "21.6.2"
    page := 230
    sourceLine := 7829
    statement := "Logical-strength order and semantic unfolding distance are distinct gradings: a syntactic weakening step need not have a fixed metric size."
    hypotheses := ["A separately defined relaxation order, and a specified unfolding scheme."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.OSLF.Framework.NuRevisionMetric", "Mettapedia.OSLF.Framework.NuRevision.scheme", "Defines the actual depth-indexed denotation sequence used by the metric."⟩,
      ⟨"Mettapedia.OSLF.Framework.FundedNuAssayControls", "Mettapedia.OSLF.Framework.FundedNuAssayControls.equal_limits_do_not_give_zero_revision_distance", "Equality of limit predicates need not identify their unfolding trajectories."⟩]
    coverage := .partialCoverage
    gap := "No joint relaxation-poset/edit-locus development or formal comparison of one-conjunct deletions at stages 1 and 5 was found." },
  { kind := .remarkEntry
    number := 9
    title := "Yield, not truth"
    sourceSection := "21.6.3"
    page := 231
    sourceLine := 7879
    statement := "The ecology is claimed to select for nutritive hypotheses so that lineages drift toward yield-oriented direction choice and away from discrimination-oriented choice wherever they conflict; search is steered by what pays."
    hypotheses := ["A population/lineage dynamics model.", "A defined yield and reproductive fitness relationship.", "Comparison of candidate policies in the same environment."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "No evolutionary dynamics, policy payoff or selection-drift theorem supporting this prose was found." },
  { kind := .propositionEntry
    number := 6
    title := "Bounded branching"
    sourceSection := "21.6.4"
    page := 232
    sourceLine := 7899
    statement := "The number of formula siblings a scientist can evaluate before committing to a move is at most its stack divided by the cost of one check; effective search branching is then claimed a function of wealth rather than logic. The actual paid-campaign result uses a positive uniform lower cost and counts completed tests."
    hypotheses := ["Positive uniform per-test lower bound c.", "Delivery and inspection both count in the paid ledger.", "A sequential campaign transfers exactly the previous remaining purse into the next round."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.GSLT.Causality.PaidProbeCampaign", "Mettapedia.GSLT.Causality.ProbeCampaign.Campaign.paid_branching_division", "For actual supplied paid rounds, positive minimum cost and a uniform delivery-plus-inspection lower bound imply completedTests ≤ budget/minimum."⟩,
      ⟨"Mettapedia.GSLT.Causality.PaidProbeCampaign", "Mettapedia.GSLT.Causality.ProbeCampaign.Campaign.ledger", "The retained real occurrence paths satisfy initial budget = remaining + spent across the campaign."⟩]
    coverage := .partialCoverage
    gap := "The numerical bound is proved for actual paid campaigns, but the chapter-specific formula sibling enumeration/search/commitment operation is not connected. Effective branching also depends on held instruments and logic, not wealth alone." },
  { kind := .corollaryEntry
    number := 1
    title := "Poverty is confining"
    sourceSection := "21.6.4"
    page := 232
    sourceLine := 7906
    statement := "A scientist able to afford few evaluations per move is claimed likelier to choose the cheapest moves, identified via Proposition 21.5 with the shortest; uniform short moves are confined by Proposition 21.4, and escape allegedly requires a later move the scientist could not afford to evaluate."
    hypotheses := ["An explicit probabilistic/choice policy if likelier is to be a claim.", "A justified relationship between price and move distance.", "One uniform radius bound for the confinement inference."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.GSLT.Causality.PaidProbeCampaign", "Mettapedia.GSLT.Causality.ProbeCampaign.Campaign.paid_branching_division", "Budget limits the number of paid tests under a positive lower price."⟩,
      ⟨"Mettapedia.OSLF.Framework.AssayRevisionMetric", "Mettapedia.OSLF.Framework.AssayRevision.finite_walk_confined", "Confinement follows once a uniform small-step policy is supplied."⟩]
    coverage := .partialCoverage
    gap := "No policy or probability law proves the poverty-to-cheapest-move implication, and Proposition 21.5 does not supply the needed cost/distance relation. A blind large jump may require no prior candidate survey." },
  { kind := .remarkEntry
    number := 10
    title := "Science is entropy production"
    sourceSection := "21.7.1"
    page := 233
    sourceLine := 7946
    statement := "The aggregate activity of scientists is interpreted as converting free tokens into history, with spent tokens constituting the record; predation is said to be redistribution of remaining time rather than global profit."
    hypotheses := ["Closed world with no minting or external replenishment.", "The actual code/resource separation invariant excludes hidden purse release.", "A chosen additive valuation interprets signatures as token amounts."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.stored_signatures_balance", "From ResourceSeparated source, actual CostStepPath satisfies source.storedSignatures = target.storedSignatures + sum demanded signatures."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Conservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostPath.receipt_rawMeasure_eq_emitted_spend", "The independently constructed causal receipt has raw total measure equal to actual executable path spends."⟩]
    coverage := .partialCoverage
    gap := "Actual conservation and receipt accounting are present. Thermodynamic entropy, a full ecological aggregate and predatory transfers are not consequences of the account identity alone." },
  { kind := .definitionEntry
    number := 7
    title := "Metabolic channel"
    sourceSection := "21.7.2"
    page := 233
    sourceLine := 7960
    statement := "A specified internalizing encoding should represent each located token stack as a rho message on a metabolic name and implement a funded reclaim/debit/reissue cycle with strictly positive burn."
    hypotheses := ["A stack-preserving internalizing encoding J[-], not an erasure.", "A precise payload/token representation and arithmetic implementation.", "A positive debit policy and an operational invariant for the cycle."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Erasure", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostTerm.erase_purse", "Negative boundary: current cost erasure maps a located purse to empty parallel composition, not a message."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.physical_purse_occurrences_preserved", "Located source purse occurrences survive actual funded paths under ResourceSeparated; their contents decrease."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicStackInternalization", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.StackInternalization.canonical_payload_readout", "Countably encoded signing atoms and ordered stack cells are independently recovered from the actual canonical rho payload, including repeated atoms and atom zero."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicFundingExecution", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.FundingExecution.all_emitted_signature", "Every selected source debit has an actual isolated reclaim/pop execution; the multiset of emitted signature readouts sums to the selected source demand. Positive burn uses the source-valid nonempty-head condition."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicReflection", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic.live_step_reflects", "All public successors in the closed live phase reflect to its protocol COMM, rather than only one chosen schedule."⟩]
    coverage := .partialCoverage
    gap := "The stack protocol is internalized. Source locations remain dependent receipt data rather than target channel encodings, and selected purses run in separate isolated sessions. A full cost-term/context compiler and shared-channel composition are additional obligations. The paid learner controller is initialized for a supplied finite path." },
  { kind := .remarkEntry
    number := 11
    title := "Metabolism is a race condition"
    sourceSection := "21.7.2"
    page := 233
    sourceLine := 7968
    statement := "Under the metabolic message cycle of Definition 21.7, living requires briefly exposing the stack as a message and computing is therefore described as racing other processes to reclaim one's own stack."
    hypotheses := ["An actual stack-to-message protocol as in Definition 21.7.", "A competitor has the same channel and an enabled compatible receive.", "The token message is linear and currently available."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicCompetition", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic.Competition.enabled_owner_and_competitor", "An actual owner receive and actual contextual transfer receive are both enabled for the same supplied stack output occurrence."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourceClaimHistory", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourceClaimHistory.public_execution_exclusive_claims", "Every supplied public finite execution lifts to an occurrence history in which each initially distinct consumed key occurs at most once; reissued resources carry fresh keys."⟩]
    coverage := .correctedCoverage
    gap := "Checked race/exclusivity for a linear available output and an enabled compatible competitor. Channel possession alone does not make a receiver enabled, and this does not assert universal competition for every computation." },
  { kind := .definitionEntry
    number := 8
    title := "Harvest, death"
    sourceSection := "21.7.2"
    page := 233
    sourceLine := 7975
    statement := "Harvest is a target-rho receive on P's metabolic name that transfers its funding message; death means P has no resources sufficient for its next admitted step."
    hypotheses := ["The metabolic encoding and currently live funding message.", "No alternative purse, replenishment, remaining prepaid activity or resurrection for the claimed fatality.", "Every relevant subsequent subject step is charged to the stolen funding resource."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.length_zero_of_no_cells", "A resource-separated source with zero purse cells has no funded firing; explicitly excludes unmetered normalization and replenishment."⟩,
      ⟨"Mettapedia.GSLT.Causality.ComplementaryAssay", "Mettapedia.GSLT.Causality.ComplementaryAssay.selected_fire", "Ordinary linear message/receiver consumption gives its unique result in the isolated assay resource system, without establishing rho metabolic transfer."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation.ProtectedResource", "Distinct, initially present computation-owned output occurrence; independent of future harvesting."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation.matching_occurrences_harvest", "Independently specified matching occurrences construct an actual public COMM step and a finite contextual harvest; no starvation or profitability claim."⟩,
      ⟨"Mettapedia.OSLF.Learning.ResourceInterferenceControls", "Mettapedia.OSLF.Learning.ResourceInterferenceControls.actual_harvesting_communication", "Concrete selected contextual receiver consumes the supplied protected message in the complete closed COMM semantics."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicCompetition", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic.Competition.canonical_transfer_result", "The actual contextual COMM transfers the complete ordered stack payload to the acquisition channel."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicCompetition", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic.Competition.transferred_every_public_execution_quiet", "After transfer the isolated source owner has no public reaction: its sole matching funding message is absent and no alternative replenishment is present."⟩]
    coverage := .partialCoverage
    gap := "Complete stack transfer and subsequent blocking are proved for the isolated owner profile. General cost-term/context internalization, alternative resources, shared sessions and replenishment require additional comparisons; physiological death is not inferred from protocol blocking." },
  { kind := .remarkEntry
    number := 12
    title := "One ledger"
    sourceSection := "21.7.2"
    page := 234
    sourceLine := 7984
    statement := "Use decorated-calculus costs as the unique ecological accounting convention; target rho internalization is used for transfer mechanics, with any simulation overhead kept as a separate quantity."
    hypotheses := ["A declared choice of ecological ledger.", "If target and source execution are compared, an explicit refinement rather than equality of their raw step counts."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.OSLF.Framework.RhoScopeWhereFundedComparison", "Mettapedia.OSLF.Framework.RhoScopeWhereFundedComparison.response_agrees_with_actual_rho", "A concrete paid resource-response readout agrees with actual unpriced rho execution and retains independent delivery/inspection charges; no state-by-state cost refinement is asserted."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Conservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostPath.trace_account_eq_totalCost", "Decorated source receipt valuation equals the sum of that source path's event spends."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicFundingExecution", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.FundingExecution.Controls.atom_burn_and_communication_counts_are_distinct", "An actual valid head burns three signing atoms in two administrative COMM occurrences, so the two accounts are not identified."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicValidityControls", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.ValidityControls.communication_does_not_create_funding", "A structurally executable empty-signature cell takes two COMM occurrences but emits zero signing atoms and is rejected by source funding admission."⟩]
    coverage := .interpretativeCoverage
    gap := "This is an accounting convention, not a proved preservation of ratios under the missing general internalizing encoding. Current code explicitly keeps operational and paid readout comparisons separate." },
  { kind := .theoremEntry
    number := 1
    title := "Predators are non-image contexts"
    sourceSection := "21.7.3"
    page := 234
    sourceLine := 8007
    statement := "For J[-]:C(rho)→rho and a rho context C, the source claims: if C is the encoding of a source context it cannot harvest any plugged encoded process's stack; if C is outside the context image and holds the metabolic name it may harvest; hence predatory contexts are exactly the non-image contexts holding a metabolic name. The final iff is stronger than image-context safety plus existence of a bare receiving attacker."
    hypotheses := ["A genuine internalizing encoding of terms and contexts with a precisely stated operational hosting/reflection theorem.", "The source funding/authority discipline excludes unauthorized stack transfer.", "A live target stack message and an enabled target receiver, not mere occurrence/possession of the name.", "The class called predatory and the meaning of preserved must distinguish owner-authorized debits from theft."]
    sourceProof := "sketch"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Located", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.LocatedTokenCover.wrong_location_not_selected", "A purse at a different funding location cannot be among the selected source purse occurrences; this is only a local source funding statement."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.physical_purse_occurrences_preserved", "Source funded paths preserve physical purse occurrence count under ResourceSeparated, while contents may be debited."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Erasure", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostTerm.erase_purse", "The established erasure deletes purse data, so it is not the claimed stack-message internalization J[-]."⟩,
      ⟨"Mettapedia.OSLF.Learning.ResourceInterferenceControls", "Mettapedia.OSLF.Learning.ResourceInterferenceControls.compiled_frame_never_harvests", "All finite occurrence-annotated executions under the existing output-only typed compiler frame preserve absence of contextual receipt. Legitimate spending remains possible."⟩,
      ⟨"Mettapedia.OSLF.Learning.ResourceInterferenceControls", "Mettapedia.OSLF.Learning.ResourceInterferenceControls.compiled_frame_protection", "Fresh frame keys preserve the designated initial resource; separate origin projections realize the independently emitted raw frame and supplied computation, with finite-execution protection."⟩,
      ⟨"Mettapedia.OSLF.Learning.ResourceInterferenceControls", "Mettapedia.OSLF.Learning.ResourceInterferenceControls.operational_possession_separator", "A real closed non-image holder, its origin-respecting context realization and designated initial resource, cannot harvest in any finite closed execution."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation.public_history_lifts", "Every equation-saturated public closed COMM execution can retain actual occurrence and origin receipts."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation.Firing.consumed_key_never_reappears", "The monotone allocation reservation prevents reuse of a consumed occurrence key along every finite future history."⟩,
      ⟨"Mettapedia.OSLF.Learning.ResourceInterferenceControls", "Mettapedia.OSLF.Learning.ResourceInterferenceControls.receiver_in_larger_protocol_image", "The bare receiver belongs to the separately defined ResourceProtocol syntax image; the output-only image must not be widened to that profile."⟩,
      ⟨"Mettapedia.OSLF.Learning.ResourceInterferenceControls", "Mettapedia.OSLF.Learning.ResourceInterferenceControls.same_endpoint_different_receiver_origins", "Legitimate spending and contextual harvest may have identical endpoints, so endpoint reflection alone does not establish provenance protection."⟩]
    coverage := .partialCoverage
    gap := "Original row remains partial. The corrected output-only-frame boundary and closed possession separator are proved, but this frame is not all encoded C(rho) contexts. The missing bridge is an explicitly specified located-stack/context internalizer with occurrence-preserving reflection and an earned source ownership-protection discipline. Existing nominal funding locality and endpoint Hosting do not provide that bridge." },
  { kind := .definitionEntry
    number := 9
    title := "The game"
    sourceSection := "21.7.3"
    page := 235
    sourceLine := 8025
    statement := "A game selects an admitted class A of target rho contexts containing the image of all decorated source contexts and contained in the ambient target context class."
    hypotheses := ["Specified source/target context carriers and a context encoding J[-].", "A membership predicate A with the two stated inclusions."]
    sourceProof := "definition"
    evidence := []
    coverage := .openCoverage
    gap := "No exact admitted ecological context-class definition tied to a stack-message J[-] was found; generic set-inclusion or permission interfaces would not establish this concrete game." },
  { kind := .definitionEntry
    number := 10
    title := "Capability gating"
    sourceSection := "21.7.3"
    page := 235
    sourceLine := 8033
    statement := "Capability-gated admission requires a traceable derivation of the metabolic name from allowed perception, and excludes capabilities furnished as unexplained initial gifts."
    hypotheses := ["A derivability/provenance judgment for metabolic names.", "A fixed held-instrument kit and paid perception rules.", "A precise boundary distinguishing initial holdings from earned discoveries."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission", "Mettapedia.OSLF.Framework.FundedInstrumentQuestionAdmission.prepare?_sound", "Admission constructs only fully permitted structural questions and retains request identity and offered data; it does not derive metabolic names."⟩,
      ⟨"Mettapedia.OSLF.Framework.RhoScopeWhereNativeReceipts", "Mettapedia.OSLF.Framework.RhoScopeWhereNativeReceipts.retained_capture_and_history", "Actual guarded rho capture/history is retained for supplied encoded payloads; this is not a no-gift capability provenance theorem."⟩]
    coverage := .partialCoverage
    gap := "Instrument permission and receipts exist, but no metabolic-name derivation/admission discipline implements the printed capability game." },
  { kind := .propositionEntry
    number := 7
    title := "Foraging inequality"
    sourceSection := "21.7.4"
    page := 235
    sourceLine := 8051
    statement := "With a successful recovered amount σP and exactly the declared sensing, assay and break-in debits, strictly positive net gain requires σP > κsense(δP)+κassay+κbreak."
    hypotheses := ["A concrete transfer and debit ledger with no omitted fees, refunds or retained credits.", "Sufficient prefix funding to reach the successful harvest.", "Strictly positive net gain, rather than mere nonnegative gain."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Conservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostPath.PrefixAccepted.final_cost_le", "Every prefix-accepted actual source account has final spend within the initial budget; the generic source ledger has no ecological prey-to-predator credit."⟩,
      ⟨"Mettapedia.GSLT.Causality.PaidProbeCampaign", "Mettapedia.GSLT.Causality.ProbeCampaign.Campaign.ledger", "Paid inquiry campaign conserves initial purse into remaining plus spend; it has no harvest credit component."⟩]
    coverage := .partialCoverage
    gap := "No joined operational harvest-credit ledger identifies the three printed fees and recovered stack. Arithmetic of a postulated payoff would not close the chapter's concrete claim." },
  { kind := .corollaryEntry
    number := 2
    title := "The profitable band"
    sourceSection := "21.7.4"
    page := 235
    sourceLine := 8059
    statement := "Because rich computations can afford deeper concealment and poor ones offer little recovered stack, the source concludes that profitable prey occupy a band: sufficiently poor prey are not worth opening and sufficiently rich prey are not worth cracking."
    hypotheses := ["A specified relation between prey wealth, chosen concealment and discovery/break-in cost.", "Both low-wealth and high-wealth exclusion hypotheses, plus nonempty profitable middle region."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "The foraging inequality and the ability to afford deeper hiding do not imply a band: rich prey may choose shallow exposure, or recovered wealth may grow faster than concealment cost. No band theorem or ecological strategy model was found." },
  { kind := .propositionEntry
    number := 8
    title := "One specimen, one measurement"
    sourceSection := "21.8"
    page := 236
    sourceLine := 8075
    statement := "For any mortal computation P harvested by S, no further assay can be run against P, and a hypothesis about the individual P has zero expected yield after its first test."
    hypotheses := ["Irreversible death with no alternate funding, revival or reproduction identified with the same individual.", "An assay notion requiring live funded subject activity.", "A defined expected-yield measure; external structural inspection of remains must be distinguished."]
    sourceProof := "sketch"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.length_zero_of_no_cells", "After all cells are absent in a resource-separated source, every actual funded source path has length zero; this does not erase residual structural surface or forbid an external observer inspecting it."⟩]
    coverage := .partialCoverage
    gap := "The source proof incorrectly infers no further surface from no funded transitions. Existing instruments inspect inert syntax. No general harvest/death/no-further-assay or expected-yield theorem has been connected." },
  { kind := .corollaryEntry
    number := 3
    title := "Induction is forced"
    sourceSection := "21.8"
    page := 236
    sourceLine := 8089
    statement := "In an ecology with destructive assay, the source claims that only hypotheses about classes of computations have positive expected yield, and therefore the language must describe collections by properties rather than by enumeration."
    hypotheses := ["A long-run/repeated-use objective, not merely positive yield of one initial hunt.", "A population containing reusable kinds and a defined expected payoff.", "A separate expressiveness requirement if intensional properties rather than finite enumeration are necessary."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "Destructive sampling alone does not prove the printed only-hypotheses claim. A singleton prediction can pay on its first test; an enumerated finite class can support multiple one-shot harvests. No ecological induction theorem was found." },
  { kind := .remarkEntry
    number := 13
    title := "The biological reading"
    sourceSection := "21.8"
    page := 236
    sourceLine := 8101
    statement := "Destructive experiments motivate reuse of conclusions across a strain/cohort/genotype, as an analogy to the proposed namespace-based ecology."
    hypotheses := ["An empirical analogy to biological methodology.", "The restricted repeated-yield interpretation of Corollary 21.3."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "This is empirical/modeling prose, not a numbered mathematical theorem. The analogy supplies no missing proof of the stronger induction assertion." },
  { kind := .lemmaEntry
    number := 1
    title := "Exposure"
    sourceSection := "21.9.1"
    page := 237
    sourceLine := 8124
    statement := "For a mortal P with strictly positive burn and no free names, P never harvests, its stack decreases monotonically and it dies after finitely many steps. The proof reinterprets no free names as structural disjointness from all other loci and invokes a minimum debit ε to bound lifetime by ceil(σP/ε)."
    hypotheses := ["Finite initial budget.", "A uniform strictly positive minimum debit, not only a pointwise positive rate.", "Persistent absence of matching external metabolic channels/credits over the run.", "A notion of death tied to inability to take another funded step rather than elapsed wall time."]
    sourceProof := "sketch"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.length_add_remaining_cells_le", "For actual resource-separated closed source paths, length plus remaining physical purse cells is at most initial physical cells; each funded firing consumes at least one cell."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.length_zero_of_no_cells", "No initial physical cells imply no funded steps."⟩,
      ⟨"Mettapedia.OSLF.Syntax.RhoScopedChannelSeparation", "Mettapedia.OSLF.Binding.RhoScopedChannelSeparation.channels_agree_of_original_reaction", "For the actual original communication profile, a send/input pair can react only when their scoped channel classes agree."⟩]
    coverage := .partialCoverage
    gap := "The lifetime bound is proved for a closed resource-separated cost profile. The printed no-free-names premise is reinterpreted as structural disjointness only in the proof; current disjointness need not persist under future decentralized manufacture. No mortality/harvest bridge establishes the full lemma." },
  { kind := .remarkEntry
    number := 14
    title := "Closure is luck, not construction"
    sourceSection := "21.9.1"
    page := 237
    sourceLine := 8137
    statement := "Decentralized manufacture permits independent production of structurally equal names; the source therefore says a locus cannot construct guaranteed closure, can only observe current closure, and cannot purchase perfect isolation."
    hypotheses := ["Equal structural recipes may be chosen independently.", "The claim must distinguish unrestricted future adversaries from an explicitly bounded known namespace."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation", "Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation.allocatedName_equiv_iff", "The actual quoted name stream has structural congruence exactly when the supplied indices are equal."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation", "Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation.fresh_above_namespace_bound", "A constructive relative-freshness guarantee exists against a stated bounded finite namespace; a blanket impossibility of construction would be too strong."⟩]
    coverage := .partialCoverage
    gap := "The unrestricted-collision warning is plausible, but no impossibility theorem for all decentralized isolation constructions is supplied. Existing relative freshness results require a narrower reading than closure is only luck." },
  { kind := .corollaryEntry
    number := 4
    title := "Concealment is a luxury of the starving"
    sourceSection := "21.9.1"
    page := 237
    sourceLine := 8147
    statement := "Any indefinitely surviving computation is claimed to expose observable surface, hence to be perceivable, predictable in principle and edible in principle."
    hypotheses := ["A nonvacuous indefinite-survival model or a conditional argument in the finite conserved world.", "A proved exposure/no-credit lifetime theorem.", "Enough held instruments and funds for name discovery; a successful receiving attack."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.length_add_remaining_cells_le", "Actual closed finite-purse source paths have a finite step bound; this gives no inference from generic observable surface to a target metabolic capability."⟩]
    coverage := .partialCoverage
    gap := "No theorem connects indefinite survival to accessible metabolic names. In the chapter's globally finite conserved pool with positive burn, indefinite survival may be impossible for every organism, making the antecedent vacuous. Perceivable does not imply predictable or edible without extra premises." },
  { kind := .propositionEntry
    number := 9
    title := "The opposition is monotone"
    sourceSection := "21.9.2"
    page := 238
    sourceLine := 8175
    statement := "Along the perception/assay/break-in ladder, yielded information is claimed nondecreasing, residual subject life nonincreasing, and only break-in credits the scientist's stack."
    hypotheses := ["A common information preorder comparing all three kinds of observations.", "A residual-life measure and an execution comparison on the same subject.", "A concrete metabolic credit ledger for all engagements."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No common ladder semantics, information/refinement proof or lifetime/credit comparison was found. Structure, sampled behavior and a dead interior are not automatically comparable information sets; the table is a modeling assertion." },
  { kind := .propositionEntry
    number := 10
    title := "Scientists are preferred prey"
    sourceSection := "21.10"
    page := 239
    sourceLine := 8206
    statement := "Every scientist is claimed to expose more surface than a passive mortal because inquiry requires dialogue depth at least two while metabolism only requires harvest access; it is therefore supposedly easier to perceive and derive its metabolic name, with no stack-size or burn-rate normalization needed."
    hypotheses := ["A formally specified scientist and passive-mortal class.", "An ordered measure of observable surface and comparable capabilities/channels.", "A demonstrated relationship between dialogue exposure and the particular metabolic channel."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No theorem realizes the asserted ordering. Passive mortals can expose many channels, scientific dialogue may reuse a channel, and visible dialogue need not reveal the metabolic channel. The later dialogue-depth claim alone cannot supply a global prey preference theorem." },
  { kind := .propositionEntry
    number := 11
    title := "When imagination pays"
    sourceSection := "21.10"
    page := 239
    sourceLine := 8232
    statement := "Simulation of a hunt is claimed viable iff κsim < Pr[failed hunt]·(κsense+κassay+κbreak), interpreted as simulation cost being below the expected error cost it prevents."
    hypotheses := ["A probability model of failed hunts.", "The fraction of failures prevented by the simulation, and all simulation/remaining hunt costs.", "Positive expected net savings is distinguished from prefix affordability and survival viability."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No stochastic hunt/simulation payoff model or actual nested-budget simulation theorem was found. The displayed iff assumes avoided errors equal all failed hunts and omits solvency/survival constraints; it is not implied by Turing completeness and reflection." },
  { kind := .definitionEntry
    number := 11
    title := "Source and prey"
    sourceSection := "21.11.2"
    page := 240
    sourceLine := 8280
    statement := "Classify a metabolic channel as prey when a linear send offers its entire stack for one exclusive receipt, and as source when a persistent emitter offers bounded quanta at an emitter-controlled rate to nonexclusive receivers."
    hypotheses := ["A metabolic-channel encoding and stack interpretation are fixed.", "Linear sends are distinguished from replicated or contract-driven emitters.", "The text says quanta are delivered indefinitely, while section 21.11.6 and the appendix require finite total reserves; the intended timescale needs specification."]
    sourceProof := "definition"
    evidence := []
    coverage := .openCoverage
    gap := "No declaration defining these two metabolic access profiles, the persistent source process, or its bounded-rate/nonexclusive laws was found. Ordinary COMM alone does not establish a source profile." },
  { kind := .remarkEntry
    number := 15
    title := "Trophic type is a fact about the cut"
    sourceSection := "21.11.2"
    page := 241
    sourceLine := 8291
    statement := "Whether an accessible stack counts as external energy or another organism depends on the chosen interaction cut and granularity; trophic type is not an intrinsic substance classification."
    hypotheses := ["A world decomposition P | E and its organism boundary are chosen.", "A source/prey access-profile interpretation is supplied."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "This is a relative ecological reading of the cut. Existing general scope structures do not define trophic classification or prove its change under recutting." },
  { kind := .propositionEntry
    number := 12
    title := "The two sciences"
    sourceSection := "21.11.3"
    page := 241
    sourceLine := 8310
    statement := "Source-feeding is claimed to admit a complete finite-unfolding environmental theory and convergent inquiry followed by fixed-formula rent; prey-feeding is claimed to require permanently incomplete finite theories and continuing paid revision."
    hypotheses := ["The text invokes Remark 21.6 for structurally recursive exact finite descriptions and Proposition 21.3 for reduction-following recursion.", "Sources must have the former description property and prey the latter, revising adversarially.", "A model of inquiry convergence, theory completeness and holding/revision charges is needed."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No theorem links the source/prey multiplicities of Definition 21.11 to the required characterization or nonconvergence properties. A linear prey can be simple; being adaptive alone does not establish the universal impossibility of a finite exact theory." },
  { kind := .corollaryEntry
    number := 5
    title := "Intelligence is a heterotroph’s expense"
    sourceSection := "21.11.3"
    page := 241
    sourceLine := 8318
    statement := "Claim that source-feeder strategies have bounded standing epistemic cost, prey-feeder strategies have unbounded standing epistemic cost, and continuing inquiry earns its holding cost only for the latter."
    hypotheses := ["Proposition 21.12 is assumed.", "Standing versus cumulative cost and the horizon over which boundedness is measured must be fixed.", "A payoff comparison must connect epistemic expenses to improved harvests."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "Neither the cost sequence nor the source/prey theorem is implemented. Permanent positive rent does not by itself establish unbounded per-step cost, and an unbounded expense does not itself prove inquiry is worthwhile." },
  { kind := .propositionEntry
    number := 13
    title := "The mixed strategy is the worst of both"
    sourceSection := "21.11.4"
    page := 242
    sourceLine := 8363
    statement := "Claim that an atomic computation using both trophic profiles must pay the prey-feeder revision expense while retaining the source-feeder collecting surface, exposing it to the vulnerability identified by Lemma 21.1 and Proposition 21.10."
    hypotheses := ["Both access profiles are harvested by one computation.", "Source yield requires a large collecting surface.", "The prey-feeder revision-cost premise of Proposition 21.12 holds.", "Surface exposure must imply metabolic-name derivability in the admitted context class."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No formal geometry-to-yield law, mixed strategy, viability comparison, or dominance theorem is present. Section 21.18 itself lists mixed-diet dominance as an open ensemble test; the displayed premises do not quantify costs and benefits." },
  { kind := .propositionEntry
    number := 14
    title := "Composite resolution"
    sourceSection := "21.11.5"
    page := 243
    sourceLine := 8388
    statement := "Claim that parallel specialist components sharing a restricted metabolic channel pool their yields, so the mixed-strategy disadvantage of Proposition 21.13 does not apply to that composite."
    hypotheses := ["Two specialists P and Q can be composed with a shared metabolic name.", "The channel admits the intended pooling while the components retain their access profiles.", "The comparison must include the composite interface, coordination and maintenance expenses."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "Parallel composition is available, but no theorem proves specialist pooling or exemption from the mixed-strategy costs. The source does not supply a quantitative dominance criterion; this is also identified as a test in section 21.18." },
  { kind := .propositionEntry
    number := 15
    title := "Trophic succession"
    sourceSection := "21.11.6"
    page := 243
    sourceLine := 8408
    statement := "Claim a succession from source-feeding to prey-feeding and then universal foraging failure as finite source reserves decline and irreversible expenditure accumulates."
    hypotheses := ["A closed finite reserve has no minting.", "Source harvests initially satisfy Proposition 21.7.", "Source yield falls below its foraging threshold before prey yield does.", "Continued activity consumes a strictly positive bounded-below resource amount."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.stored_signatures_balance", "For an actual CostStepPath source target and source.ResourceSeparated, source.storedSignatures = target.storedSignatures + path.demands.sum. This is physical signature conservation along existing funded rho steps; it does not construct ecological births or population dynamics."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.length_add_remaining_cells_le", "For an actual CostStepPath source target with source.ResourceSeparated, path.length + target.physicalPurseCells <= source.physicalPurseCells. It bounds funded firings, not independently defined dialogue alternations or lifelong external replenishment."⟩]
    coverage := .partialCoverage
    gap := "Funded paths have genuine conservation and length bounds, but neither relative depletion order nor trophic dominance follows from those laws. No ecological trajectory or source/prey yield law has been connected to the cost calculus." },
  { kind := .propositionEntry
    number := 16
    title := "Sex attacks the predator’s hypothesis language"
    sourceSection := "21.12.1"
    page := 244
    sourceLine := 8450
    statement := "Claim that homologous recombination changes the metabolic-name namespace described by a predator hypothesis, whereas continuation-only variation leaves that targeting namespace intact."
    hypotheses := ["The admitted game requires derivation of metabolic names as in Definition 21.9.", "Predator hypotheses describe namespaces as in Corollary 21.3.", "The chosen recombination actually changes observable names; continuation edits do not change their construction."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No recombination operator or theorem about predator hypotheses exists here. Identical-parent choices need not perturb any name, and reflective continuations can construct future names; the source needs a scoped observable-namespace restriction." },
  { kind := .definitionEntry
    number := 12
    title := "Genome, phenotype"
    sourceSection := "21.12.2"
    page := 245
    sourceLine := 8468
    statement := "For process code P, name its genome @P and its phenotype *@P."
    hypotheses := ["P is a process in the chosen sorted rho syntax.", "This is the naming definition only; inertness, transmission, inspection and costs are separate properties."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Syntax.RhoPayloadPresentation", "Mettapedia.OSLF.Binding.RhoPayloadPresentation.quoT", "For every context Gamma, quoT maps Term sig Gamma Srt.pr to Term sig Gamma Srt.nm and is the quote constructor applied to P."⟩,
      ⟨"Mettapedia.OSLF.Syntax.RhoPayloadPresentation", "Mettapedia.OSLF.Binding.RhoPayloadPresentation.drpT", "For every context Gamma, drpT maps Term sig Gamma Srt.nm to Term sig Gamma Srt.pr; drpT (quoT P) is precisely *@P."⟩]
    coverage := .exactCoverage
    gap := "The two sorted constructors express this definition exactly. This does not claim that a mortal-agent, inheritance or population model has been constructed." },
  { kind := .remarkEntry
    number := 16
    title := "What we do and do not claim here"
    sourceSection := "21.12.2"
    page := 245
    sourceLine := 8488
    statement := "Held quotations and executing processes have different charging behavior, but this does not establish a Weismann barrier or prohibit transmitting acquired hypotheses."
    hypotheses := ["Names are inert data and running steps are metered.", "The biological inheritance question is explicitly left open by the source."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.OSLF.Syntax.RhoPayloadConstruction", "Mettapedia.OSLF.Binding.RhoPayloadPresentation.output_inert", "For strict [comm, parCong] and book [comm, parCong, drop] profiles, an isolated output carrying any code has no Steps transition. This does not make all storage or external holding charges zero."⟩]
    coverage := .interpretativeCoverage
    gap := "The inert-code theorem supports the distinction; no formal heredity barrier is asserted or established. No theorem analyzes acquired-hypothesis transmission prices." },
  { kind := .remarkEntry
    number := 17
    title := "Persistence and reproduction are distinguished by the ledger"
    sourceSection := "21.12.2"
    page := 246
    sourceLine := 8502
    statement := "Classify a reinstatement drawing from the parent metabolic channel as soma, and a copy needing a separate endowment transferred from the parent as offspring."
    hypotheses := ["A ledger identifies the parent purse and ownership/transfer of the offspring endowment.", "The distinction is by provisioning, not merely term syntax."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.OSLF.Syntax.RhoPayloadConstruction", "Mettapedia.OSLF.Binding.RhoPayloadPresentation.birth_presented", "Constructs a concrete two-step birth in the presented strict rho calculus by sending open child code, receiving its name and dropping it. There is no budget, parent-purse debit or child endowment in this theorem."⟩]
    coverage := .interpretativeCoverage
    gap := "No named parent/offspring ledger classification or endowment-transfer rule has been built. The existing birth example establishes code activation, not this metabolic distinction." },
  { kind := .definitionEntry
    number := 13
    title := "Locus, allele"
    sourceSection := "21.12.3"
    page := 246
    sourceLine := 8524
    statement := "A locus of P is the one-hole context obtained by deleting one parand from its recursively nested prime tree, with the deleted parand as the allele; channel-path position identifies the occurrence."
    hypotheses := ["A representative or canonical occurrence tree modulo structural congruence is specified.", "The deletion selects a particular occurrence, not just a repeated channel name."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Syntax.ScopedBindingContexts", "Mettapedia.OSLF.Binding.ScopedEncoding.BindingContext", "A BindingContext is a path of intrinsically scoped, single-hole operator frames. The frame records the selected argument and all siblings and tracks the binder-extended hole scope. It does not define genetic loci, channel-path homology or simultaneous swaps."⟩]
    coverage := .partialCoverage
    gap := "Intrinsically scoped single-hole paths exist, but the exact genetic locus/allele relation over rho prime trees and its channel-path identification have not been defined. Repeated channels can give distinct loci with identical channel sequences, so occurrence identity requires care." },
  { kind := .propositionEntry
    number := 17
    title := "Loci versus labels"
    sourceSection := "21.12.3"
    page := 246
    sourceLine := 8540
    statement := "Every process modal-label position is claimed to be a genetic locus, with strict inclusion and equality exactly at holes occupied by communicating pairs."
    hypotheses := ["The modal labels and process-relative locus sets must be specified in one compatible context grammar.", "Communicating pairs are as in Definition 21.16."]
    sourceProof := "sketch"
    evidence := [⟨"Mettapedia.OSLF.Syntax.RhoScopedReactionReadout", "Mettapedia.OSLF.Binding.RhoScopedReactionReadout.Reading.communication", "A communication reading carries an actual equation-class channel, payload and name-bound continuation; Reading.source is the parallel composition of their output and input. This is the unguarded core rho pair, not a genetic graph or arbitrary pattern-compatibility discipline."⟩]
    coverage := .openCoverage
    gap := "No inclusion/equality theorem was found. The proof sketch removes a pair although Definition 21.13 deletes one parand. Reactive labels are enabling contexts, not automatically redex-position addresses; book rho also has reflection redexes that are not communication pairs." },
  { kind := .definitionEntry
    number := 14
    title := "Homology"
    sourceSection := "21.12.3"
    page := 247
    sourceLine := 8552
    statement := "Mother and father loci are homologous when both their root-to-hole channel paths and the pattern-variable binding environments along those paths agree."
    hypotheses := ["Channel equality, binder equality or alpha-equivalence, and occurrence paths are fixed.", "Alleles may refer only to names bound in the target hole scope."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Syntax.ScopedBindingContexts", "Mettapedia.OSLF.Binding.ScopedEncoding.BindingContext", "A BindingContext is a path of intrinsically scoped, single-hole operator frames. The frame records the selected argument and all siblings and tracks the binder-extended hole scope. It does not define genetic loci, channel-path homology or simultaneous swaps."⟩]
    coverage := .partialCoverage
    gap := "Typed frames retain exact binder scopes, but no homology relation compares rho channel paths or proves the claimed partial tree isomorphism. Repeated paths and permutation of parallel primes remain to be handled." },
  { kind := .propositionEntry
    number := 18
    title := "Species is a namespace formula"
    sourceSection := "21.12.3"
    page := 247
    sourceLine := 8560
    statement := "Claim that interbreeding is characterized by agreement of homologous path sets, reproductive isolation by namespace disjointness, and conspecificity by a generated contextual formula."
    hypotheses := ["Recombination is admitted only at homologous loci.", "A species/interbreeding criterion and namespace of loci are defined.", "The logic can express the required path-set and binding agreement."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No species formula or equivalence is present. Having some homologous loci is not automatically a full reproductive compatibility criterion, and ordinary channel-namespace overlap does not encode binding-compatible path overlap." },
  { kind := .definitionEntry
    number := 15
    title := "Crossover"
    sourceSection := "21.12.4"
    page := 247
    sourceLine := 8569
    statement := "Given homologous loci H of mother and father and a selector chi:H->{M,F}, fill each locus with the selected parental allele, preserving send/receive polarity and the target binding environment at guard/body splits."
    hypotheses := ["The selected loci must have an unambiguous simultaneous filling policy, particularly when nested or overlapping.", "Both selected alleles inhabit the target hole scope.", "Polarity is preserved."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Syntax.ScopedBindingContexts", "Mettapedia.OSLF.Binding.ScopedEncoding.BindingFrame.fill", "Fills one intrinsically scoped operator-argument hole with a term of its precise source scope, returning a term of the target scope. It does not select parental alleles or fill overlapping loci."⟩]
    coverage := .partialCoverage
    gap := "A single scoped frame can be filled without scope errors, but no simultaneous homologous-locus crossover construction, conflict policy or well-formedness theorem is supplied." },
  { kind := .propositionEntry
    number := 19
    title := "Effect size is graded by depth"
    sourceSection := "21.12.4"
    page := 247
    sourceLine := 8582
    statement := "Claim that replacing a locus at depth d perturbs only detail after d prefix levels and that the resulting effect size is non-increasing as locus depth grows."
    hypotheses := ["A quantitative perturbation metric and a comparison between swaps are fixed.", "The intended fragment excludes recursive/global effects.", "Prefix-tree depth must control the selected observation metric."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "There is no genetic edit metric or depth-monotonicity theorem. The text gives no definition of effect size; even nonrecursive deep continuations may have large observable consequences, so syntax depth alone is insufficient." },
  { kind := .definitionEntry
    number := 16
    title := "Interaction graph, communicating pair"
    sourceSection := "21.12.5"
    page := 248
    sourceLine := 8605
    statement := "Build a genome interaction graph with prime occurrences as vertices and compatible same-channel send/receive pairs as edges; a communicating pair consists of an edge and its endpoints. This uses syntactic compatibility rather than future reachability."
    hypotheses := ["Occurrences, scope and pattern compatibility are represented.", "Edges distinguish simultaneous syntactic availability from future communication."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.OSLF.Syntax.RhoScopedReactionReadout", "Mettapedia.OSLF.Binding.RhoScopedReactionReadout.Reading.communication", "A communication reading carries an actual equation-class channel, payload and name-bound continuation; Reading.source is the parallel composition of their output and input. This is the unguarded core rho pair, not a genetic graph or arbitrary pattern-compatibility discipline."⟩,
      ⟨"Mettapedia.OSLF.Syntax.RhoScopedFiniteReactions", "Mettapedia.OSLF.Binding.RhoScopedFiniteReactions.mem_catalogue", "An admitted reading belongs to the finite catalogue exactly when its source inventory is included in the whole and its rule is admitted. Includes core communication and reflection; not a genetic graph."⟩]
    coverage := .partialCoverage
    gap := "Core rho communication readings and finite root-redex catalogues are implemented, but there is no recursive genome graph with arbitrary guarded patterns, hereditary units or the claimed screening-cost impossibility." },
  { kind := .propositionEntry
    number := 20
    title := "The discipline aligns the two address spaces"
    sourceSection := "21.12.5"
    page := 248
    sourceLine := 8624
    statement := "Claim that restricting crossover to communicating-pair positions makes its admissible loci exactly the genome modal labels, yielding a well-defined characteristic-formula transport of every swap."
    hypotheses := ["The locus/label characterization of Proposition 21.17 holds in the selected profile.", "The characteristic-formula construction carries chosen term occurrences to corresponding formula occurrences."]
    sourceProof := "sketch"
    evidence := []
    coverage := .openCoverage
    gap := "No crossover-to-formula transport or address-space bijection is implemented. The source sketch depends on Proposition 21.17, including its single-parand versus pair inconsistency and its omission of reflection redexes." },
  { kind := .propositionEntry
    number := 21
    title := "Balance is preserved exactly by degree-preserving swaps"
    sourceSection := "21.12.5"
    page := 249
    sourceLine := 8652
    statement := "Replacing a communicating pair on c by one on c is claimed to preserve all channel send/receive counts, leave no prime orphaned and preserve race arity; replacing it on a different c-prime can orphan residuals and destroy balance."
    hypotheses := ["The initial genome is balanced in the intended sense.", "The swap removes and adds one send and one receive.", "To infer incidence preservation, compatibility with residual patterns and all channels in moved continuations must also be controlled."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No swap/count/balance theorem exists. Equal channel counts alone do not imply unchanged compatible-edge degrees when payloads and receive patterns vary. Same-channel swaps can change matches with residual primes; the source title also states an exactly-if characterization stronger than the displayed may-fail converse." },
  { kind := .remarkEntry
    number := 18
    title := "Discipline substitutes for screening"
    sourceSection := "21.12.5"
    page := 249
    sourceLine := 8662
    statement := "Claim that a balance-preserving pair discipline avoids per-offspring balance screening by paying for the constraint mechanism once, provided eligibility is checked syntactically."
    hypotheses := ["A genuinely balance-preserving crossover operator is established.", "An implementation cost model separates operator construction, per-swap checks and full screening."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "This is a proposed design/cost consequence of the still-unproved balance and screening claims. No operator or amortized screening theorem is present." },
  { kind := .remarkEntry
    number := 19
    title := "A dial, and it is the dial of §21.6"
    sourceSection := "21.12.5"
    page := 250
    sourceLine := 8678
    statement := "Compare unrestricted parand swaps, pair swaps and degree-preserving pair swaps as progressively smaller variation spaces with stronger viability guarantees; escape from individual revision confinement requires a sufficiently shallow rebranch."
    hypotheses := ["The three allowed-swap sets and a variation-distance measure are fixed.", "The claimed pair/balance guarantees hold.", "Population viability and offspring loss are included in the objective."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "No hierarchy of crossover policies or measured viability/distance comparison is defined. The text explicitly leaves the ecological optimum to the ensemble, and the claimed guarantee for the middle and last disciplines requires the missing compatibility conditions." },
  { kind := .remarkEntry
    number := 20
    title := "What the discipline does not simplify"
    sourceSection := "21.12.5"
    page := 250
    sourceLine := 8690
    statement := "The interaction graph can contain overlapping edges, so a pair swap changes endpoints that may have other incident edges; preserving multiple-channel balance requires simultaneous relevant degree preservation."
    hypotheses := ["Interaction graph vertices are occurrences, and edge incidence includes all applicable patterns/channels.", "The single-channel degree claim is interpreted with the scope limitations of Proposition 21.21."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "Core communication permits shared endpoints, but no genome graph or multi-channel swap preservation theorem was found. This remark correctly limits the preceding intended discipline; it does not itself supply that theorem." },
  { kind := .definitionEntry
    number := 17
    title := "Channel types"
    sourceSection := "21.12.6"
    page := 250
    sourceLine := 8704
    statement := "Relative to W=P|E, call a channel internal when P has a matching pair and E contains no equal name, external when E contains an equal name and P has no matching pair, and both when both properties hold."
    hypotheses := ["Name equality and occurrence are evaluated at a specified structural scope.", "The term matching-pair includes the intended pattern-compatibility criterion."]
    sourceProof := "definition"
    evidence := []
    coverage := .openCoverage
    gap := "No cut-relative channel classifier with these predicates was found. The three listed cases omit an occurring channel with neither an internal pair nor an environment occurrence; dynamic classification and tau/interaction soundness also require operational proofs." },
  { kind := .remarkEntry
    number := 21
    title := "This is the surface, made syntactic"
    sourceSection := "21.12.6"
    page := 251
    sourceLine := 8718
    statement := "Claim that external and both channels are exactly context-observable surface features, and that an all-internal computation cannot forage and therefore starves; identify this trichotomy with the three earlier access grades."
    hypotheses := ["The admitted context class and observer instruments are fixed.", "External-name availability characterizes permitted observation.", "The isolated computation has positive burn and no replenishment."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "No exact surface/classifier theorem is present. A fixed environment lacking a name differs from quantification over all admissible contexts, and observer extensions can expose structure beyond this raw channel partition." },
  { kind := .definitionEntry
    number := 18
    title := "Dialogue, and its depth"
    sourceSection := "21.12.6"
    page := 251
    sourceLine := 8730
    statement := "A dialogue is a chain of external-or-both channel steps separated by causally dependent internal reductions, where each subsequent external availability depends on the preceding external step; its depth counts alternations."
    hypotheses := ["There is an operational causal-dependence relation, not just a chronological path.", "The changing world cut and channel classification along the path are specified."]
    sourceProof := "definition"
    evidence := []
    coverage := .openCoverage
    gap := "No declaration combines these causal, channel-type and alternation conditions into the source dialogue notion. Generic traces or causal paths would not by themselves establish this definition." },
  { kind := .propositionEntry
    number := 22
    title := "Conversation is bounded by the stack"
    sourceSection := "21.12.6"
    page := 251
    sourceLine := 8741
    statement := "Claim that token supply bounds dialogue alternation depth because each alternation pays for its causal internal chain, and that the same supply bounds observable modal distinguishing depth."
    hypotheses := ["Every counted alternation incurs a strictly positive debit in the specified units.", "The counted supply includes all replenishment, or the dialogue segment has none.", "Dialogue alternations embed in actual funded firings.", "A modal-depth-to-funded-observation comparison is supplied."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.length_add_remaining_cells_le", "For an actual CostStepPath source target with source.ResourceSeparated, path.length + target.physicalPurseCells <= source.physicalPurseCells. It bounds funded firings, not independently defined dialogue alternations or lifelong external replenishment."⟩]
    coverage := .partialCoverage
    gap := "A strong bound on actual funded firings is available, but the dialogue object, its injection into firings, positivity of internal chains and the modal-depth bridge have not been defined. Empty internal chains and replenishment must be handled explicitly." },
  { kind := .propositionEntry
    number := 23
    title := "Inquiry has a structural signature"
    sourceSection := "21.12.6"
    page := 251
    sourceLine := 8748
    statement := "Claim that inquiry requires an out/in/out chain on both-type channels with causal conditioning, hence dialogue depth at least two, expressed by Sci := exists j.<K_j>(exists j-prime.<K_j-prime>(exists j-double-prime.<K_j-double-prime> top)) with out/in/out position restrictions."
    hypotheses := ["The labels name actual out/in/out positions, all on both-type channels.", "The second output causally depends on the received result.", "Inquiry and revision have a defined operational meaning."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No Sci formula or scientist-characterization theorem is present. Three nested existential modalities express an executable sequence but do not alone encode causal dependence, result conditioning, stored hypotheses or revision; the direction and intended iff must be separated." },
  { kind := .propositionEntry
    number := 24
    title := "No neutral variation"
    sourceSection := "21.12.6"
    page := 252
    sourceLine := 8789
    statement := "Claim that internal-pair swaps preserve weak bisimulation and every contextual/predator observation, while necessarily affecting metered resource use; thus no variation is simultaneously behaviorally and metabolically neutral."
    hypotheses := ["Weak bisimulation and admissible observations are fixed.", "The swap must preserve externally observable continuations and future name exposure.", "The ledger comparison must distinguish an actual cost difference from merely charging both alternatives."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "There is no such invariance or non-neutrality theorem. Internal communication can enable different external continuations, so an internal channel does not guarantee behavioral equivalence; two silent variants can also incur identical costs. The source universal conclusion needs major strengthening of premises." },
  { kind := .corollaryEntry
    number := 6
    title := "Cryptic variation and its release"
    sourceSection := "21.12.6"
    page := 252
    sourceLine := 8797
    statement := "Claim that internal variation stays behaviorally irrelevant until a channel acquires an equal name across the cut, and recombination can trigger that exposure, releasing previously cryptic variation."
    hypotheses := ["Propositions 21.24 and 21.26 hold for the chosen variation semantics.", "No other mechanism exposes or propagates the variation.", "The low-cost accumulation claim has a specified resource comparison."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "Neither the internal-variation equivalence nor recombination release mechanism is implemented. The exactly-when claim excludes continuation effects and other observer capabilities without a proof." },
  { kind := .remarkEntry
    number := 22
    title := "Dialogue is where the impact is"
    sourceSection := "21.12.6"
    page := 253
    sourceLine := 8814
    statement := "Claim that redex-restricted recombination concentrates changes on interactions and therefore on ecologically consequential dialogue, especially at both-type channels."
    hypotheses := ["A distribution or selection discipline on redex swaps is defined.", "Observable dialogue positions are a distinguished subset of allowed redexes."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "The implication is not established: internal pairs are also redexes, so redex restriction alone does not restrict to dialogue or increase the proportion of observable changes. No quantitative concentration statement is defined." },
  { kind := .propositionEntry
    number := 25
    title := "Growth is slaved to term size"
    sourceSection := "21.12.7"
    page := 253
    sourceLine := 8831
    statement := "The source asserts that no process contains its own quoted name and that every contained name is strictly smaller than its enclosing process, bounding desugaring-generated name growth by term growth."
    hypotheses := ["Raw finite syntax supports proper-subterm size comparisons.", "Any version stated modulo rho equations must account for @(*n)=n.", "A specific admissible desugaring and representative/size convention are required for growth claims."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.OSLF.Syntax.RhoPayloadConstruction", "Mettapedia.OSLF.Binding.RhoPayloadPresentation.self_code_through_drop", "Proves cls(quoT(drpT(quoT nilT))) = cls(quoT nilT) and the same after adjoining parallel nil. Thus a process can contain a name equal to its own quotation modulo the source equations."⟩,
      ⟨"Mettapedia.OSLF.Framework.GeneratedScope", "Mettapedia.OSLF.Framework.GeneratedScope.sizeOf_quote_lt_left", "A raw Pattern quotation of one child has smaller sizeOf than the quotation of their parallel pair. This is a concrete structural recursion measure, not the asserted theorem modulo equation classes."⟩,
      ⟨"Mettapedia.OSLF.Syntax.RhoPayloadConstruction", "Mettapedia.OSLF.Binding.RhoPayloadPresentation.quote_injective", "Quotation reflects process-class equality only when both codes have key = none; the adjacent quote_not_injective theorem proves failure without the single-drop qualification."⟩]
    coverage := .correctedCoverage
    gap := "The unrestricted no-self-code premise fails modulo the actual rho name law: *@0 contains @0, and @(*@0)=@0. Existing checked negative evidence supplies this correction. Raw-subterm size descent does not prove a uniform dynamic lineage-growth bound or a bound for all admissible decentralized desugarings." },
  { kind := .propositionEntry
    number := 26
    title := "Decentralization makes recombination generative"
    sourceSection := "21.12.7"
    page := 254
    sourceLine := 8848
    statement := "Claim that locally generated private parental names can coincide structurally, so inheriting both can create a shared offspring channel and interactions absent in either parent."
    hypotheses := ["Freshness is relative to each parent scope rather than globally allocated atoms.", "A defined crossover brings compatible same-name endpoints together.", "Parental isolation and newly enabled offspring interaction are proved at a common observation."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.OSLF.Syntax.RhoPayloadConstruction", "Mettapedia.OSLF.Binding.RhoPayloadPresentation.lift_constructs_name", "One COMM sends process code and receives its quotation into a name-hole context, filling the enclosing scope before sealing the code. Establishes local code/name construction, not fresh-name uniqueness or recombination."⟩,
      ⟨"Mettapedia.OSLF.Syntax.RhoScopedReactionReadout", "Mettapedia.OSLF.Binding.RhoScopedReactionReadout.Reading.communication", "A communication reading carries an actual equation-class channel, payload and name-bound continuation; Reading.source is the parallel composition of their output and input. This is the unguarded core rho pair, not a genetic graph or arbitrary pattern-compatibility discipline."⟩]
    coverage := .partialCoverage
    gap := "Name construction and same-name communication are concrete, but no two-parent isolation/recombination example or novelty theorem was found. The source possibility is plausible only after an explicit crossover and scope comparison." },
  { kind := .remarkEntry
    number := 23
    title := "Accumulation, and a reading of senescence"
    sourceSection := "21.12.7"
    page := 254
    sourceLine := 8859
    statement := "Under a discipline that accumulates structure without reclamation, claim that increased sensing costs eventually exhaust the budget; a birth-time condensation/renaming pass is proposed to reset inherited weight at genome-linear cost."
    hypotheses := ["The source expressly labels this discipline-dependent prose rather than a theorem.", "Accumulation must increase the cost of required operations without compensating yield.", "Renaming private names must preserve their relevant equality/capability relations."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "No accumulation policy, priced garbage collector, condensation algorithm or linear-cost theorem exists. Growing term size does not automatically increase every required operation cost, and canonical renaming is nontrivial when structural name equality creates interactions." },
  { kind := .propositionEntry
    number := 27
    title := "Selection is post hoc because screening is priced"
    sourceSection := "21.12.8"
    page := 254
    sourceLine := 8884
    statement := "Claim that n homologous loci produce 2^n recombinants and that exhaustive paid screening against the parental stack is unaffordable, preventing a parent from emitting only viable offspring."
    hypotheses := ["There are n independently selectable binary loci.", "To count distinct offspring, choices must produce distinct terms and not conflict at nested loci.", "A positive per-check charge and a bound relating stack size to 2^n are required."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No recombinant enumeration or screening lower bound is implemented. Binary choice functions number 2^n, but distinct genomes need not; pricing alone does not imply unaffordability for a fixed finite n or rule out emitting one previously known viable child." },
  { kind := .propositionEntry
    number := 28
    title := "Minimum viable endowment"
    sourceSection := "21.12.9"
    page := 255
    sourceLine := 8905
    statement := "An offspring whose endowment is below its least first-successful-harvest outlay cannot reach that harvest; if every offspring needs a positive floor e and provisioning draws from one parent stack B, the number simultaneously endowed is at most floor(B/e)."
    hypotheses := ["The floor is the minimum actual path debit to a first successful harvest, identified with sense+assay+break for the available shallowest prey.", "The floor is positive and there is no interim external replenishment or free harvest.", "Parent provisioning is additive and limited to the specified stack."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.GSLT.Weighting.ConfiguredFundingRates", "Mettapedia.GSLT.Weighting.ConfiguredFunding.affordable_iff_paid_history", "For a given event, price profile, weight map and purse amount, price <= amount iff a PaidHistory retaining that event and input map exists. This is one paid occurrence, not minimum cost over all first-harvest paths."⟩,
      ⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.stored_signatures_balance", "For an actual CostStepPath source target and source.ResourceSeparated, source.storedSignatures = target.storedSignatures + path.demands.sum. This is physical signature conservation along existing funded rho steps; it does not construct ecological births or population dynamics."⟩]
    coverage := .partialCoverage
    gap := "Existing funding gates and conserved paths support the resource premise. No offspring/endowment transfer, minimum harvest path or division-bound theorem is implemented, and the source death-before-eating conclusion requires an operational death convention." },
  { kind := .corollaryEntry
    number := 7
    title := "Inquiry trades against fecundity"
    sourceSection := "21.12.9"
    page := 255
    sourceLine := 8918
    statement := "For a fixed total stack and positive offspring endowment floor, paying more for inquiry leaves less capacity for offspring; the source applies this to the prey-feeder ongoing-cost claim."
    hypotheses := ["Corollary 21.5 and Proposition 21.28 hold.", "Total available budget and other expenses are held fixed, including any additional harvest caused by inquiry.", "Strictly fewer offspring additionally requires crossing an integral provisioning threshold."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No allocation/fecundity comparison is present. Deep inquiry may increase later harvest, and increased expense need not strictly reduce the integer offspring count; a ceteris-paribus weak bound is distinct from the source unconditional conclusion." },
  { kind := .propositionEntry
    number := 29
    title := "Kinds are the condition of inquiry"
    sourceSection := "21.12.10"
    page := 256
    sourceLine := 8958
    statement := "Claim that destructive assay without reproduction eventually eliminates every hypothesis extension, while reproduction sustains namespace populations whenever their foraging inequality holds, preserving live instances of kind hypotheses."
    hypotheses := ["A finite population and destructive harvest process are fixed.", "Without births, all relevant individuals are eventually harvested rather than merely a chosen subpopulation.", "With births, reproductive success and rate compensate losses, not merely positive foraging yield."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "No population process or namespace persistence theorem exists. Positive foraging profit alone does not ensure mating, adequate birth rate, nonextinction or continued membership in the same hypothesis namespace." },
  { kind := .remarkEntry
    number := 24
    title := "What reproduction does not do"
    sourceSection := "21.12.10"
    page := 256
    sourceLine := 8966
    statement := "Reproduction redistributes rather than creates conserved tokens; the source further claims that births create carrying-capacity dynamics that can occupy the viable phase longer than a generation."
    hypotheses := ["Birth transitions must conserve the same physical ledger as other transitions.", "A population dynamics and carrying-capacity model are supplied."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostStepPath.stored_signatures_balance", "For an actual CostStepPath source target and source.ResourceSeparated, source.storedSignatures = target.storedSignatures + path.demands.sum. This is physical signature conservation along existing funded rho steps; it does not construct ecological births or population dynamics."⟩]
    coverage := .partialCoverage
    gap := "Conservation is proved for existing funded paths, but birth/endowment transitions have not been connected to those paths. Carrying capacity and multigeneration persistence are not consequences of conservation alone." },
  { kind := .definitionEntry
    number := 19
    title := "Configuration, ecology"
    sourceSection := "21.13.1"
    page := 257
    sourceLine := 8990
    statement := "A configuration is a finite multiset of mortal computations and bare stacks, stack sizes summing to Theta, with selected revision policies; an ecology adds a distribution over its reachable configurations."
    hypotheses := ["A finite configuration carrier and revision-policy designation are defined.", "Reachability, distributions and the treatment of spent tokens kappa in the conserved total are fixed."]
    sourceProof := "definition"
    evidence := [⟨"Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Step", "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.CostConfig", "CostConfig Ground abbreviates Multiset (CostTerm Ground). It contains no scientist designation, fixed-Theta proof or probability distribution."⟩,
      ⟨"Mettapedia.GSLT.Weighting.WeightTheory", "Mettapedia.GSLT.Weighting.Augmented.coalgebra", "Given a keyed interaction presentation, Augmented weight update data, a funding predicate, a semiring, finite enabled-event sets and decidable equality of configurations, sums weighted enabled redexes by target configuration. This is a coefficient-valued coalgebra on theory.Term x WeightMap, not a constructed category/fibration of ecologies or a probability law over reachable mortal-agent configurations."⟩]
    coverage := .partialCoverage
    gap := "The current CostConfig is a multiset of cost terms and the weighting construction has explicit program/weight configurations. Neither defines the stated mortal-agent ecology, Theta partition with revision policies, or a probability distribution supported on its reachability set." },
  { kind := .propositionEntry
    number := 30
    title := "A fibration, not a functor"
    sourceSection := "21.15.1"
    page := 261
    sourceLine := 9154
    statement := "Claim that ecologies decorated over cost-accounted GSLTs form a fibration Eco -> GSLT_C, and that distribution assignment is functorial from its Grothendieck total category but not determined by an undecorated base object."
    hypotheses := ["A category of cost-accounted GSLTs and a contravariant decoration functor/pseudofunctor with reindexing are fixed.", "Ecology objects and morphisms, cartesian lifts and a distribution/coalgebra target functor are constructed.", "Weights/funding data satisfy the appropriate positivity and transport conditions."]
    sourceProof := "none"
    evidence := [⟨"Mettapedia.GSLT.Weighting.WeightTheory", "Mettapedia.GSLT.Weighting.Augmented.coalgebra", "Given a keyed interaction presentation, Augmented weight update data, a funding predicate, a semiring, finite enabled-event sets and decidable equality of configurations, sums weighted enabled redexes by target configuration. This is a coefficient-valued coalgebra on theory.Term x WeightMap, not a constructed category/fibration of ecologies or a probability law over reachable mortal-agent configurations."⟩]
    coverage := .partialCoverage
    gap := "A real weighted coalgebra exists and pricing/weights are independent data. No Eco category, decoration Grothendieck construction, cartesian-lifting law or distribution functor was found; unrelated presheaf Grothendieck constructions do not close this claim." },
  { kind := .remarkEntry
    number := 25
    title := "Cost is not already a weighting"
    sourceSection := "21.15.2"
    page := 261
    sourceLine := 9169
    statement := "Withdraw identification of cost with stochastic weight: a cost controls funding admission through a debit comparison, while an independent rate controls propensity; an unaffordable positive-rate event is silent."
    hypotheses := ["A price profile, weight/rate map and actual purse amount are separate inputs.", "Funding gates multiply or suppress rates only after an affordability decision."]
    sourceProof := "prose"
    evidence := [⟨"Mettapedia.GSLT.Weighting.ConfiguredFundingRates", "Mettapedia.GSLT.Weighting.ConfiguredFunding.fundedRate_nonzero_iff", "Over a semiring without zero divisors, fundedRate is nonzero iff a paid history exists and both independent weight and geometric factors are nonzero."⟩,
      ⟨"Mettapedia.GSLT.Weighting.ConfiguredFundingControls", "Mettapedia.GSLT.Weighting.ConfiguredFundingControls.actual_paid_rates", "The same actual program redex under a common unit price has paid rate 4 after one weighting history and 3 after another; cost does not determine rate."⟩,
      ⟨"Mettapedia.GSLT.Weighting.ConfiguredFundingControls", "Mettapedia.GSLT.Weighting.ConfiguredFundingControls.empty_purse_blocks_positive_rates", "The positive-rate example with budget zero has no paid history and its funded rate is zero."⟩,
      ⟨"Mettapedia.GSLT.Weighting.ConfiguredFundingControls", "Mettapedia.GSLT.Weighting.ConfiguredFundingControls.zero_rate_retains_a_funded_history", "A unit-priced event with sufficient budget retains its paid history even with zero rate; zero propensity does not diagnose exhaustion."⟩]
    coverage := .exactCoverage
    gap := "The operational price/rate distinction and its positive and negative controls are proved. This numbered remark does not itself construct the unnumbered following paragraph's sections of Eco, nor is such a fibration supplied here." },
  { kind := .propositionEntry
    number := 31
    title := "The logic-preserving maps are bisimulation-preserving maps of the extension"
    sourceSection := "21.15.3"
    page := 262
    sourceLine := 9213
    statement := "Under the reconstruction/logical-correspondence hypotheses of Chapter 20, preservation of structural logical equivalence coincides with preservation of observer-extension contextual bisimilarity; the source additionally claims ecology functoriality on observer-image morphisms."
    hypotheses := ["S satisfies Conditions 20.1 and 20.2, has admissible equations E, and opens all Sigma constructors as in Theorem 20.1.", "Corollary 20.1 also requires Theorem 20.2; its relation equality is on closed Sigma terms.", "The phrase preserves the generated logic must distinguish preservation of logical equivalence from satisfaction/formula translation.", "Functoriality requires separately compatible decoration, cost and distribution morphisms."]
    sourceProof := "proof"
    evidence := [⟨"Mettapedia.OSLF.Framework.SortedTypedStructuralObservations", "Mettapedia.OSLF.Framework.SortedTypedInstruments.StructuralObservations.logicalEquivalent_iff_payloadObserver_bisimilar", "For any declared sorted constructor signature, designated AC1 parallel sorts, sourceRules and nonempty origin type, independently defined structural logical equivalence equals payload-observer firing-system bisimilarity on embedded source classes. The module explicitly excludes additional authored equations, binders and reflective RUN congruence."⟩,
      ⟨"Mettapedia.OSLF.Framework.SortedCommutativeFullObserverSeparation", "Mettapedia.OSLF.Framework.SortedCommutativeInstruments.full_observer_raw_bisimilar_iff_source_equation", "For the module's designated-AC1 source values and a nonempty origin type, full observer IPOBisimilar iff the source Equation relation. No ecology morphism or distribution transport is part of this theorem."⟩]
    coverage := .partialCoverage
    gap := "The exact structural-equivalence/observer-bisimilarity equality is proved for the closed first-order designated-AC1 grammar, not all binding/reflective rho or arbitrary admissible E. Equivalence-preserving functions need not preserve individual formulas or costs, and no ecology functor is constructed." },
  { kind := .conjectureEntry
    number := 1
    title := "Laxity"
    sourceSection := "21.15.3"
    page := 263
    sourceLine := 9236
    statement := "Conjecture that logic-preserving encodings induce only a lax distribution map, with added rewrite costs producing distortion and stochastic dominance providing the appropriate order."
    hypotheses := ["The encoding, cost comparison and distribution pushforward are defined.", "A state or outcome order supports the chosen stochastic-dominance relation.", "A chosen cost-to-rate map connects inflated debit to ordered stochastic behavior."]
    sourceProof := "none"
    evidence := []
    coverage := .openCoverage
    gap := "Explicit source conjecture, with no claim of proof. No ecological lax functor or stochastic-dominance transport theorem was found. Cost inflation alone does not determine a stochastic order without a rate mapping and target observable." },
  { kind := .remarkEntry
    number := 26
    title := "The pragmatist’s objection, and surplus"
    sourceSection := "21.16"
    page := 263
    sourceLine := 9267
    statement := "Interpret nonpaying inquiry as an expenditure affordable from surplus above the foraging horizon, competing with offspring provisioning; call this curiosity/basic research a metabolic luxury."
    hypotheses := ["A required foraging reserve and an excess balance are defined.", "Surplus allocation competes with the offspring endowment floor."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "No reserve-horizon or curiosity allocation theorem exists. This is the source's acknowledged pragmatic and normative interpretation, not a closure target supplied by generic budget arithmetic." },
  { kind := .remarkEntry
    number := 27
    title := "A correction, made in place"
    sourceSection := "21.17.1"
    page := 264
    sourceLine := 9309
    statement := "Correct the network/transducer slogan: quotation and dereference provide the proposed builtin transduction, while a learned front end proposes which host-world distinctions receive builtin names; coverage and causal-state criteria are deferred to Chapter 65."
    hypotheses := ["A builtin sort has already been chosen and embedded with an appropriate quote/drop law.", "The host-world proposal/coverage problem is separate from the internal representation roundtrip."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "Core rho quotation and dereference exist, but an arbitrary host-world builtin extension and a lossless encoder are not constructed by this remark. Its later-chapter coverage/causal-state task remains expressly outside this bounded inventory." },
  { kind := .remarkEntry
    number := 28
    title := "What this argument is standing on"
    sourceSection := "21.17.3"
    page := 266
    sourceLine := 9388
    statement := "Limit the effectiveness-of-reason argument to ontologically isolated computational agents whose environments share the computational substrate; applying it to noncomputational host phenomena requires a new grounding argument."
    hypotheses := ["The environment is represented entirely in the same computational ontology.", "The generated logic is adequate for the chosen accessible relation.", "The claim expressly does not establish a host-world encoder."]
    sourceProof := "prose"
    evidence := []
    coverage := .interpretativeCoverage
    gap := "This is a stated scope restriction and philosophical interpretation. Internal structural adequacy is available in specified fragments but does not prove the external ontology premise or re-derive grounding for rooms, markets or physical bodies." }]

def identifier (entry : Entry) : Kind × Nat := (entry.kind, entry.number)

def expectedIdentifiers : List (Kind × Nat) :=
  (List.range 19).map (fun index => (.definitionEntry, index + 1)) ++
  [(.lemmaEntry, 1)] ++
  (List.range 31).map (fun index => (.propositionEntry, index + 1)) ++
  [(.theoremEntry, 1)] ++
  (List.range 7).map (fun index => (.corollaryEntry, index + 1)) ++
  [(.conjectureEntry, 1)] ++
  (List.range 28).map (fun index => (.remarkEntry, index + 1))

/-- Inventory coverage only: every numbered source reference occurs once. -/
theorem inventory_complete :
    (entries.map identifier).toFinset = expectedIdentifiers.toFinset := by decide

theorem inventory_unique : (entries.map identifier).Nodup := by decide

theorem inventory_count : entries.length = 88 := by decide

def coverageCount (coverage : Coverage) : Nat :=
  (entries.filter (fun entry => entry.coverage == coverage)).length

/-- These are source-coverage counts, not counts of proved theorems. -/
theorem coverage_counts :
    coverageCount .exactCoverage = 3 ∧ coverageCount .correctedCoverage = 4 ∧
    coverageCount .partialCoverage = 39 ∧ coverageCount .openCoverage = 26 ∧
    coverageCount .interpretativeCoverage = 16 := by decide

/-- The corrected predation result does not silently close the full image claim. -/
theorem original_predation_stays_partial :
    ∃ entry ∈ entries, entry.kind = .theoremEntry ∧ entry.number = 1 ∧
      entry.coverage = .partialCoverage := by decide

end Mettapedia.Documentation.SourceLedgers.FindingMindLearning
