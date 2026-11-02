import Init.Data.String.Lemmas.IsEmpty

/-!
# The source-obligation ledger

The completion contract for the OSLF work is a ledger over the source's
obligations, not a module count, a theorem count or a build count.  This module
is that ledger, with mechanically checked metadata and explicitly cited evidence.

One row per obligation, carrying what the contract asks for: where the source
states it, what it says, the general construction that answers it, the theorem
that discharges it together with its explicit assumptions, an inhabited instance,
an adversarial control, and its standing.

`rowIntegrity` checks that a proved row names a theorem, an instance and a
control. It checks filled fields, not that the theorem's type discharges the
source statement. Statement fidelity and the adequacy of each cited instance
require a separate mathematical audit.

`openHere` means the obligation is not discharged by the cited evidence. Related
constructions may still be named in the row. `constructedHere` records a partial
construction, not a completed source theorem.

`sourceProves` records something a ledger over someone else's book has to record
separately: whether the *source* proves what it states.  A statement the source
asserts without proof is not thereby a gap in this development, and it must not
be turned into an axiom, a premise or a placeholder in order to look closed.

Chapters six to ten and sixteen to twenty are inventoried below. The recorded
definition, remark, proposition, theorem and corollary counts stay in
`chapterObligationCount`; claims a chapter makes in prose are entered as section
rows beside them.
Conditions 20.1 (redex RPOs) and 20.2 (context congruence) are additional source
preconditions, not rows in that denominator, and require their own certification.
-/

namespace Mettapedia.Documentation.SourceLedgers.FindingMind

set_option autoImplicit false

/-- Where an obligation stands in *this* development. -/
inductive Standing where
  /-- Proved here, with an instance and a control. -/
  | provedHere
  /-- A related construction exists; the full source obligation is not discharged. -/
  | constructedHere
  /-- Observed on kernel-checked instances only; no general theorem. -/
  | observedHere
  /-- The cited evidence does not discharge the obligation. -/
  | openHere
  /-- The source states it and this development has **refuted** it, with a
  counterexample.  A ledger over someone else's book needs this standing: a row
  can fail in a way that is a result rather than a gap. -/
  | refutedHere
  /-- The obligation is a **constraint on what may be claimed** rather than a
  statement to prove, and this development respects it, with the guard named.
  Most of the source's remarks are of this kind; marking them open would report
  a caveat as an unbuilt construction. -/
  | respectedHere
deriving DecidableEq, Repr

/-- One source obligation. -/
structure Obligation where
  /-- Chapter of the pinned source. -/
  chapter : Nat
  /-- Its citation, as the source numbers it. -/
  citation : String
  /-- What it says, stated faithfully rather than as we would prefer it. -/
  statement : String
  /-- Whether this row records a source proof. A false value does not establish
  that no proof exists in the source. -/
  sourceProves : Bool
  /-- The general construction here that answers it, if any. -/
  construction : String
  /-- The theorem that discharges it, with its explicit assumptions. -/
  provedTheorem : String
  /-- A nontrivial inhabited instance. -/
  instanceWitness : String
  /-- A control capable of falsifying the intended claim. -/
  negativeControl : String
  /-- Whether a row-level search for coverage was recorded. This flag does not
  certify semantic fidelity or exhaustiveness of the search. -/
  audited : Bool
  /-- Its standing here. -/
  standing : Standing
deriving Repr

/-- Recorded counts of definitions, remarks, propositions, theorems and
corollaries at the source revision. Numbered source conditions are not included. -/
def chapterObligationCount : List (Nat × Nat) :=
  [(6, 0), (7, 5), (8, 3), (9, 7), (10, 8), (16, 9), (17, 5), (18, 11), (19, 7), (20, 28)]

/-- Publication revision supplying the draft-26 obligation numbering. -/
def sourceRevision : String := "1f7bd34b11e65d707dde4b3638d08a181e1b8028"

/-- The compiled source carrying these chapter and section numbers. -/
def sourceDocument : String := "FindingMind/draft26/finding_mind.pdf"

/-- The denominator: eighty-three numbered obligations across chapters six to
ten and sixteen to twenty. -/
def totalObligations : Nat :=
  (chapterObligationCount.map (·.2)).foldl (· + ·) 0

theorem totalObligations_eq : totalObligations = 83 := by decide

/-! ## Chapter 6

The chapter numbers no environment. It fixes the running example and previews
the three definitions of the following chapters, and both are entered as
section rows.
-/

/-- Chapter 6's rows. -/
def chapter6 : List Obligation :=
  [ { chapter := 6, citation := "Section 6.2, the three definitions in advance"
      statement :=
        "A GSLT is any rewrite theory; an interactive GSLT names the site at "
        ++ "which two things meet and separates the base rule from the context "
        ++ "rules; a continued interactive GSLT presents that site as a meterable "
        ++ "cut. A Turing machine is a GSLT and is not interactive; a lambda "
        ++ "calculus is interactive with an asymmetric site; rho is interactive "
        ++ "with a symmetric one."
      sourceProves := false
      construction := "From the library root: "
        ++ "GSLT/LanguageDef/Interaction/Presentability.lean: IsBaseRewrite / "
        ++ "IsInteractive; GSLT/LanguageDef/Continued/Presentation.lean: "
        ++ "IsContinued. The three definitions are the rows of Chapters 8 and 9"
      provedTheorem := "Languages/TuringMachine/NotInteractive.lean: "
        ++ "turingMachine_not_interactive; "
        ++ "GSLT/LanguageDef/Interaction/BaseInteractions.lean: "
        ++ "lambdaCalc_isInteractive / rhoCalc_isInteractive / "
        ++ "rho_parCong_not_base (the base rule apart from the context rule); "
        ++ "GSLT/LanguageDef/Interaction/Surfaces.lean: lambda_surface_structural "
        ++ "(the ordered site) / rho_pair_swaps (the symmetric one)"
      instanceWitness := "Languages/TuringMachine/LanguageDef.lean: "
        ++ "appendOne_first_step; GSLT/LanguageDef/Continued/Presentation.lean: "
        ++ "lambda_isContinued"
      negativeControl := "Languages/Calculator/Interaction.lean: "
        ++ "calculator_not_interactive; "
        ++ "GSLT/LanguageDef/Interaction/Controls/ContextualOnly.lean: "
        ++ "contextualOnly_not_interactive"
      audited := true
      standing := .provedHere }
  , { chapter := 6, citation := "Section 6.3, the rho calculus"
      statement :=
        "Processes are 0, for(y <- x) P, x!(Q), P | Q and *x, and names are @P, "
        ++ "with y bound in for(y <- x) P. Structural equivalence is the least "
        ++ "equivalence containing alpha-equivalence and making (P, |, 0) a "
        ++ "commutative monoid. The single reduction rule is "
        ++ "for(y <- x) P | x!(Q) --> P{@Q/y}."
      sourceProves := false
      construction := "Syntax/RhoPayloadPresentation.lean: the input binds the "
        ++ "received process p, the received name is quo p and its drop is p, so "
        ++ "COMM is ordinary substitution; the equations are the commutative "
        ++ "monoid on par and the name law of Section 7.11. "
        ++ "Syntax/RhoPayloadTranslation.lean: tName/tProc from the authored "
        ++ "patterns, resolving @*n as a whole name before a literal quote"
      provedTheorem := "Syntax/RhoPayloadTranslation.lean: "
        ++ "translate_semanticSubst (executor substitution is exact environment "
        ++ "extension), translate_bind (environments are substitutions up to the "
        ++ "name law), translate_semanticCommSubst (P{@Q/y} translates to the "
        ++ "continuation instantiated at Q, up to the name law)"
      instanceWitness := "Syntax/RhoPayloadExecutorComparison.lean: "
        ++ "control_received_name -- for(x <- @0){x!(0)} receiving @0!(0) sends "
        ++ "on @{@0!(0)}, the instantiated continuation"
      negativeControl := "Syntax/RhoPayloadExecutorComparison.lean: "
        ++ "control_literal_closed -- a literal quote naming an enclosing bound "
        ++ "index is outside the translated fragment; control_free_quoteDrop -- "
        ++ "@*x for a free x is untouched by communication"
      audited := true
      standing := .provedHere }
  ]

/-! ## Chapter 7

Definition 7.1 and four remarks are numbered. The claims of Sections 7.4 to
7.6 and the four worked presentations of Sections 7.8 to 7.11 are entered as
section rows.
-/

/-- Chapter 7's rows. -/
def chapter7 : List Obligation :=
  [ { chapter := 7, citation := "Definition 7.1"
      statement :=
        "A graph-structured lambda theory is a triple G = (Sigma, E, R) of a "
        ++ "signature Sigma that is in general a lambda theory, so that terms may "
        ++ "contain variables; a set E of equations imposing a structural "
        ++ "congruence; and a set R of rewrite rules."
      sourceProves := false
      construction := "Syntax/BindingSignature.lean: Signature with binding "
        ++ "arities, EqAxiom over contextual metavariables; "
        ++ "Syntax/IntrinsicScopedConditionalPolynomial.lean: Rule, a positioned "
        ++ "conclusion with ordered binder-local premises"
      provedTheorem := "Syntax/IntrinsicScopedConditionalSubstitutionModels.lean: "
        ++ "SubstitutionOperationalModel.presentedIsInitial -- the equation "
        ++ "quotient with its free firing trees and their substitution action is "
        ++ "initial among models of the signature, equations, binders, rules and "
        ++ "substitution"
      instanceWitness := "Syntax/IntrinsicLambdaFourRulePresentation.lean: "
        ++ "initial; Syntax/RhoPayloadPresentation.lean: strictInitial, "
        ++ "bookInitial"
      negativeControl := "Syntax/IntrinsicScopedConditionalSubstitutionModels.lean: "
        ++ "no_rules_no_reduction -- a presentation without rules has no firing "
        ++ "tree, even after substitution"
      audited := true
      standing := .provedHere }
  , { chapter := 7, citation := "Remark 7.1"
      statement :=
        "The theory written G = (Sigma, E, R) in this part is written "
        ++ "S = (T, E, R) in later parts; nothing turns on the difference."
      sourceProves := false
      construction := "One presentation structure serves both spellings: "
        ++ "Syntax/BindingSignature.lean Signature and EqAxiom, and "
        ++ "Syntax/IntrinsicScopedConditionalPolynomial.lean Rule"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 7, citation := "Section 7.4, lambda theories and not Lawvere theories"
      statement :=
        "A Lawvere theory absorbs variables into arities and cannot present a "
        ++ "binder; lambda theories generate term languages with variables, and in "
        ++ "how the variables get used they are cartesian closed categories, which "
        ++ "is why the classifying form carries a chosen cartesian closed "
        ++ "structure."
      sourceProves := false
      construction := "Syntax/LawvereContextBoundary.lean for the context "
        ++ "category of a signature; Syntax/BoundTermExponential.lean and "
        ++ "Syntax/IntrinsicScopedConditionalPresheaf.lean for binder bodies as "
        ++ "exponentials by representables in the presheaf category. The closed "
        ++ "structure lives in the presheaf category, not in the context category"
      provedTheorem := "Syntax/BoundTermExponential.lean: boundTermHomEquiv; "
        ++ "Syntax/IntrinsicScopedConditionalPresheaf.lean: binderBodiesIso and "
        ++ "monoidalClosed"
      instanceWitness := "Syntax/IntrinsicLambdaFourRulePresentation.lean: the "
        ++ "LamCong premise is a child judgment under its own binder "
        ++ "(lamCongChild)"
      negativeControl := "Syntax/LawvereContextBoundary.lean: notCartesianClosed "
        ++ "and noRepresentingExponential -- the context category has variables "
        ++ "but no exponentials"
      audited := true
      standing := .provedHere }
  , { chapter := 7, citation := "Section 7.5, adjoined and not enriched"
      statement :=
        "The rewrites are adjoined to the theory as a graph: sources and targets "
        ++ "are given and the source and target maps satisfy the minimal requisite "
        ++ "equations, so that rewrite events can be quantified over."
      sourceProves := false
      construction := "Syntax/IntrinsicScopedConditionalSubstitution.lean: "
        ++ "firing trees indexed by their endpoints, with substTree acting on "
        ++ "them; Syntax/IntrinsicScopedConditionalPresheaf.lean: events, source, "
        ++ "target and graph"
      provedTheorem := "Syntax/IntrinsicScopedConditionalSubstitution.lean: "
        ++ "substTree_identity and substTree_comp; "
        ++ "Syntax/IntrinsicScopedConditionalSubstitutionModels.lean: "
        ++ "reduces_substitute and reduces_map -- source and target commute with "
        ++ "substitution and with every model map"
      instanceWitness := "Syntax/RhoPayloadPresentation.lean: steps_comm and "
        ++ "steps_parCong, rho firing trees between equation classes"
      negativeControl := "Syntax/FreePresheafEventImage.lean: "
        ++ "duplicated_endpoint_map_not_injective; "
        ++ "Syntax/LambdaEventImageMultiplicity.lean: "
        ++ "firstCopy_not_event_surjective -- distinct events may share endpoints, "
        ++ "so events are not a subobject of pairs of terms"
      audited := true
      standing := .provedHere }
  , { chapter := 7, citation := "Remark 7.2"
      statement :=
        "Lambda theory captures term languages with variables; graph-structured "
        ++ "captures the rewrite rules; a GSLT is a term language with variables "
        ++ "together with an adjoined graph of rewrites over it."
      sourceProves := false
      construction := "The Definition 7.1 and Section 7.5 rows"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 7, citation := "Remark 7.3"
      statement :=
        "Because the graph structure is adjoined, the rewrites block of a "
        ++ "specification is more algebraic structure over the same signature as "
        ++ "the terms block."
      sourceProves := false
      construction := "Syntax/IntrinsicScopedConditionalPolynomial.lean: a Rule "
        ++ "is written over withMetas of the same signature as the terms"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 7, citation := "Section 7.6, the classifying structure"
      statement :=
        "The classifying theory of a presentation is a category with finite limits "
        ++ "and a chosen cartesian closed structure, its subobject fibration, a "
        ++ "distinguished object Pr of programs and a distinguished subobject of "
        ++ "one-step reduction of Pr x Pr, with entailments generating the base "
        ++ "rewrites and their closure under the term formers; the source calls "
        ++ "that subobject the adjoined graph seen semantically."
      sourceProves := false
      construction := "Syntax/IntrinsicScopedLocalActedPresheafSetting.lean: "
        ++ "presheaves on the actual combined authored classifier, with finite "
        ++ "limits, full cartesian closed structure, the predicate projection "
        ++ "fibration and its subobject comparison. "
        ++ "Syntax/IntrinsicScopedLocalActedYonedaStructured.lean: the "
        ++ "structured generic program/event interpretation. "
        ++ "Syntax/IntrinsicScopedLocalActedPresheafEvents.lean: individually "
        ++ "retained firing events and their paired endpoint image, indexed by "
        ++ "every context and sort. The graph is distinct from its reduction "
        ++ "subobject; finite limits alone do not construct images"
      provedTheorem := "Syntax/IntrinsicScopedLocalActedPresheafSetting.lean: "
        ++ "hasFiniteLimits, closedStructure, predicateSubobjectEquiv, "
        ++ "predicateProjection_fibered, predicateLift_factorization; "
        ++ "Syntax/IntrinsicScopedLocalActedYonedaStructured.lean: "
        ++ "yonedaClassifyingIso, yoneda_firing_evaluate; "
        ++ "Syntax/IntrinsicScopedLocalActedPresheafEvents.lean: "
        ++ "mem_genericReduction_iff, genericReduction_eq_image, "
        ++ "generic_diamond_spec, generic_diamond_box_adjunction and "
        ++ "generic_box_spec. The right adjoint is the past-step box, "
        ++ "quantifying over further restrictions, not forward necessity"
      instanceWitness := "Syntax/IntrinsicScopedLocalActedPresheafLambdaControl.lean "
        ++ "and Syntax/IntrinsicScopedOperationalPresheafExtensionControls.lean: "
        ++ "actual extended binder-local LamCong and the original ordered "
        ++ "operational rule action"
      negativeControl := "Syntax/IntrinsicScopedLocalActedPresheafMultiplicityControl.lean: "
        ++ "two_firings_same_reduction; "
        ++ "Syntax/PresheafEventImageComparisonControls.lean: "
        ++ "future_reduction_box_rejects and addedStep_diamond_not_natural; "
        ++ "Syntax/IntrinsicScopedLocalActedPresheafCoproductControl.lean: "
        ++ "the two-summand retained-event presheaf and actual extension"
      audited := true
      standing := .provedHere }
  , { chapter := 7, citation := "Section 7.6, the classifying property"
      statement :=
        "The classifying structure interprets the authored presentation by "
        ++ "structure-preserving functors. Precisely: the combined context "
        ++ "classifier C_P classifies independently defined models in targets "
        ++ "with chosen finite products, selected binder-arity exponentials and "
        ++ "the event-projection pullbacks. Its presheaf category T_P carries "
        ++ "finite limits, full cartesian closure and the reduction subobject. "
        ++ "For suitably cocomplete targets, models are classified by "
        ++ "cocontinuous functors from T_P whose Yoneda restrictions preserve "
        ++ "the specified structure. This qualifies the draft's unqualified "
        ++ "description rather than asserting that an arbitrary extension "
        ++ "preserves all finite limits, exponentials or images."
      sourceProves := false
      construction := "Syntax/IntrinsicScopedLocalActedClassifier.lean: C_P "
        ++ "combines equation-context assignments and free firing trees over "
        ++ "each rule's declared telescope; event leaves carry their "
        ++ "substitution. Syntax/IntrinsicScopedLocalActedCategoricalModels.lean "
        ++ "defines program and retained-event models independently of functors. "
        ++ "Syntax/IntrinsicScopedLocalActedYonedaStructured.lean supplies the "
        ++ "actual structured Yoneda interpretation, with represented binder "
        ++ "powers, all constructors and event pullbacks, then recovers its "
        ++ "model. Syntax/IntrinsicScopedLocalActedPresheafExtension.lean "
        ++ "constructs genuine restriction and density-colimit extension. "
        ++ "Syntax/IntrinsicScopedOperationalPresheafInterpretation.lean "
        ++ "connects the original clone-presheaf model's programs, events, "
        ++ "substitution and every ordered binder-local rule action. Its "
        ++ "shared-telescope adapter is unpruned and retains full assignments"
      provedTheorem := "Syntax/IntrinsicScopedLocalActedEquivalence.lean: "
        ++ "classificationEquivalence, on all maps with natural unit/counit; "
        ++ "Syntax/IntrinsicScopedLocalActedBindingRestriction.lean: "
        ++ "bindingRestrictionIso; "
        ++ "Syntax/IntrinsicScopedLocalActedTypeComparisonNaturality.lean: "
        ++ "classificationSetNatIso; "
        ++ "Syntax/IntrinsicScopedLocalActedTargetTransport.lean: "
        ++ "targetClassificationIso; "
        ++ "Syntax/IntrinsicScopedLocalActedTargetClassificationFold.lean: "
        ++ "targetClassification_rep_freeFold; "
        ++ "Syntax/IntrinsicScopedLocalActedYonedaStructured.lean: "
        ++ "yonedaClassifyingIso, yoneda_firing_evaluate; "
        ++ "Syntax/IntrinsicScopedLocalActedPresheafExtension.lean: "
        ++ "CocontinuousInterpretation.classificationEquivalence, under "
        ++ "HasColimitsOfSize and the stated colimit preservation, "
        ++ "classificationRestrictionIso and generator_comparison; "
        ++ "Syntax/IntrinsicScopedLocalActedPresheafEvents.lean: "
        ++ "mem_genericReduction_iff, generic_diamond_box_adjunction; "
        ++ "Syntax/IntrinsicScopedOperationalPresheafInterpretation.lean: "
        ++ "extension_section_iff; the reduction comparison "
        ++ "is epi/sectionwise onto its endpoint image, and isIso additionally "
        ++ "requires preservation of the relevant mono"
      instanceWitness := "Syntax/IntrinsicScopedJsonClassifiedInstance.lean "
        ++ "and Syntax/IntrinsicScopedMonoidClassifiedInstance.lean: the actual "
        ++ "authored carriers, equations and empty rewrite inventories; "
        ++ "Syntax/IntrinsicScopedLambdaClassifiedInstance.lean: "
        ++ "extension_iff_step for all four rules and ordinary contexts, "
        ++ "including LamCong's ordered binder-local premise; "
        ++ "Syntax/IntrinsicScopedRhoClassifiedInstance.lean: extension_iff_steps "
        ++ "for strict COMM/ParCong and the declared book Drop profile; "
        ++ "Syntax/IntrinsicScopedRhoExecutorClassifiedInstance.lean: simulation "
        ++ "and reflection with successful well-sorted translation, admitted "
        ++ "closed sources, structural congruence and target-class equality. "
        ++ "The legacy Lambda adapter retains its five declared parameters; "
        ++ "reduction support does not assert an executor-history bijection"
      negativeControl := "Syntax/IntrinsicScopedLambdaClassifiedMultiplicity.lean: "
        ++ "actual distinct quotient trees/event sections with equal endpoints, "
        ++ "and equal doubled-graph images without first-copy event surjectivity; "
        ++ "Syntax/IntrinsicScopedClassifiedTelescopeCoverageControl.lean: "
        ++ "the genuinely own-telescope token firing survives while the "
        ++ "unpruned unused-global assignment is impossible; "
        ++ "Syntax/IntrinsicScopedClassifiedSubstitutionGapControl.lean: "
        ++ "the underlying rule-algebra flip is not a substitution-model map; "
        ++ "Syntax/PresheafEventImageComparisonControls.lean: the shared "
        ++ "predicate interface exposes newly available events and failure "
        ++ "of exact diamond transport after an additional target step"
      audited := true
      standing := .provedHere }
  , { chapter := 7, citation := "Section 7.8, rung one: JSON"
      statement :=
        "With no equations and no rewrites, a presentation is a multi-sorted "
        ++ "signature whose terms are the inhabitants of an algebraic data type; "
        ++ "the Json presentation is one."
      sourceProves := false
      construction := "Syntax/Mettapedia/OSLF/Syntax/AlgebraicOperationalInstances.lean: the "
        ++ "Json presentation through the common construction"
      provedTheorem := "Syntax/Mettapedia/OSLF/Syntax/AlgebraicOperationalInstances.lean: "
        ++ "jsonInitial"
      instanceWitness := "Syntax/Mettapedia/OSLF/Syntax/AlgebraicOperationalInstances.lean: "
        ++ "jsonInitial"
      negativeControl := "Syntax/Mettapedia/OSLF/Syntax/AlgebraicOperationalInstances.lean: "
        ++ "jsonNoFiring and jsonExecutorEmpty -- no firing and no executor step"
      audited := true
      standing := .provedHere }
  , { chapter := 7, citation := "Section 7.9, rung two: Monoid"
      statement :=
        "With equations, terms are quotiented by a congruence and the presentation "
        ++ "is a finitely presentable algebra; the Monoid presentation with "
        ++ "associativity and both unit laws is one."
      sourceProves := false
      construction := "Syntax/Mettapedia/OSLF/Syntax/AlgebraicOperationalInstances.lean: the "
        ++ "Monoid presentation through the common construction"
      provedTheorem := "Syntax/Mettapedia/OSLF/Syntax/AlgebraicOperationalInstances.lean: "
        ++ "monoidInitial"
      instanceWitness := "Syntax/Mettapedia/OSLF/Syntax/AlgebraicOperationalInstances.lean: "
        ++ "monoidInitial"
      negativeControl := "Syntax/Mettapedia/OSLF/Syntax/AlgebraicOperationalInstances.lean: "
        ++ "monoidNoFiring and monoidExecutorEmpty"
      audited := true
      standing := .provedHere }
  , { chapter := 7, citation := "Section 7.10, rung three: Lambda"
      statement :=
        "With rewrites, the presentation describes a language with behaviour; the "
        ++ "Lambda presentation with Beta, AppCongL, AppCongR and LamCong is the "
        ++ "lambda calculus with one base rule and three congruence rules."
      sourceProves := false
      construction := "Syntax/IntrinsicLambdaFourRulePresentation.lean: one "
        ++ "intrinsic rule list for the four rules over arbitrary bodies and "
        ++ "arguments"
      provedTheorem := "Syntax/IntrinsicLambdaFourRulePresentation.lean: "
        ++ "sourceStep_iff_reduces and initial"
      instanceWitness := "Syntax/IntrinsicLambdaFourRulePresentation.lean: "
        ++ "authoredBeta_matches_intrinsic and the three congruence comparisons"
      negativeControl := "Syntax/IntrinsicLambdaFourRulePresentation.lean: "
        ++ "variable_has_no_intrinsic_firing"
      audited := true
      standing := .provedHere }
  , { chapter := 7, citation := "Remark 7.4"
      statement :=
        "A reader arriving at rung three from rung one crosses from data to "
        ++ "computation without changing tools."
      sourceProves := false
      construction := "The Section 7.8 to 7.11 rows use one construction"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 7, citation := "Section 7.11, the rho calculus"
      statement :=
        "The RhoCalc presentation has sorts Proc and Name, terms PZero, PDrop, "
        ++ "POutput, PInput binding a name, PPar over a hash bag and NQuote, the "
        ++ "equation QuoteDrop, and the rewrites Comm, Drop and ParCong."
      sourceProves := false
      construction := "Syntax/RhoPayloadPresentation.lean: the payload "
        ++ "presentation, strict profile [comm, parCong] and book profile "
        ++ "[comm, parCong, drop]; Syntax/RhoPayloadTranslation.lean and "
        ++ "Syntax/RhoPayloadExecutorComparison.lean: the translation from the "
        ++ "authored patterns and the comparison with the authored executor"
      provedTheorem := "Syntax/RhoPayloadExecutorComparison.lean: "
        ++ "rhoStep_simulation and rhoStepWithDrop_simulation -- each executor "
        ++ "step of a well-sorted translated process is one step between equation "
        ++ "classes; strict_reflection and book_reflection -- each such step is "
        ++ "an executor step from a structurally congruent rearrangement; "
        ++ "closed_admitted_translates -- every admitted closed process translates; "
        ++ "Syntax/RhoPayloadConstruction.lean: lift_constructs_name -- a context "
        ++ "with a name hole is reached from sending code and receiving its name "
        ++ "in one COMM, the hole filled by the quotation of the code as filled "
        ++ "when sent; output_inert -- code in flight has no step; "
        ++ "quote_injective -- injectivity requires both codes to have no "
        ++ "single-drop key; quote_not_injective proves the exact failure "
        ++ "without that qualification; self_code_through_drop -- under the "
        ++ "name law the drop *@0 has "
        ++ "the name @0 that it contains"
      instanceWitness := "Syntax/RhoPayloadExecutorComparison.lean: "
        ++ "control_received_name, control_bound_quoteDrop, control_received_drop, "
        ++ "control_nested; Syntax/RhoPayloadConstruction.lean: birth_first_step, "
        ++ "birth_second_step and birth_presented -- the birth of Chapter 21 with its "
        ++ "offspring code sent as a process rather than as a quotation in a process "
        ++ "position, two executor steps and two presented steps"
      negativeControl := "Syntax/RhoPayloadPresentation.lean: drop_inert_strict "
        ++ "and drop_runs_book; Syntax/RhoPayloadExecutorComparison.lean: "
        ++ "control_free_drop, control_literal_closed and "
        ++ "bound_quoteDrop_translated_not_admitted"
      audited := true
      standing := .provedHere }
  ]

/-! ## Chapter 8

Definitions 8.1 and 8.2 and Remark 8.1 are numbered. The interaction cut of
Section 8.2, the two claims of Section 8.3, the two non-examples and the
distinction of Section 8.7 are entered as section rows. Paths in the rows of
Chapters 8 to 10 are relative to the library root.
-/

/-- Chapter 8's rows: interactive theories, their category, the cut, and the
machines that are not interactive. -/
def chapter8 : List Obligation :=
  [ { chapter := 8, citation := "Definition 8.1"
      statement :=
        "A GSLT is interactive when it carries a distinguished interacting sort "
        ++ "of programs, a binary interaction constructor whose environment "
        ++ "operand is of the interacting sort, and at least one base rewrite "
        ++ "rule whose left-hand side features that constructor, generating a "
        ++ "transition system on which bisimulation is the intended equivalence."
      sourceProves := false
      construction := "GSLT/LanguageDef/InteractiveCategory.lean: InteractivePresentation / IsBaseRewrite / "
        ++ "BaseInteraction; GSLT/LanguageDef/SemanticCategory.lean: IGSLT / baseInteraction / toGSLT. An IGSLT "
        ++ "now requires the selected rule to be a base interaction; the structural presentation alone does not."
      provedTheorem := "GSLT/LanguageDef/Interaction/Presentability.lean: IGSLT.isInteractive / "
        ++ "not_step_of_rewrites_ask_reduction / not_admitsInteractivePresentation_iff. The base-rule "
        ++ "requirement excludes a contextual-only rule system with no finite reduction derivation."
      instanceWitness := "GSLT/LanguageDef/Interaction/BaseInteractions.lean: "
        ++ "rhoCalc_isInteractive / lambdaCalc_isInteractive; "
        ++ "Languages/ProcessCalculi/CCS/Interaction.lean: ccsCalc_isInteractive "
        ++ "/ handshake_semantic_step; Languages/InteractionCategory/Interaction.lean"
      negativeControl := "GSLT/LanguageDef/Interaction/Controls/ContextualOnly.lean: contextualOnly_not_interactive / "
        ++ "contextualOnly_no_step / contextualOnly_not_IGSLT; Languages/Calculator/Interaction.lean: "
        ++ "calculator_not_interactive / calculatorRewriting_isInteractive, distinguishing equational arithmetic "
        ++ "from directed arithmetic rules."
      audited := true
      standing := .provedHere }
  , { chapter := 8, citation := "Definition 8.2"
      statement :=
        "iGSLT is the category whose objects are interactive GSLTs and whose "
        ++ "morphisms are theory maps, sort- and operator-preserving translations "
        ++ "respecting the equations and the rules, that are "
        ++ "bisimulation-preserving on the interacting sort."
      sourceProves := false
      construction := "GSLT/LanguageDef/SemanticCategory.lean: IGSLT.Morphism / Category IGSLT / semantics, over "
        ++ "operator-preserving maps of declarations with reduction-bisimilarity preservation. Syntactic "
        ++ "declaration transport does not automatically give semantic equation transport when built-in premise "
        ++ "relations or declared algebra units are renamed."
      provedTheorem := "GSLT/Core/FunctionalBisimulation.lean: GSLT.bisimilar_map_of_zigzag; "
        ++ "GSLT/LanguageDef/Contexts/Structural.lean: preservesEquations_default / preservesSteps_default, with "
        ++ "explicit equality-relation and declared-unit conditions. No theorem identifies all recorded IGSLT "
        ++ "arrows with semantic theory homomorphisms without these conditions."
      instanceWitness := "GSLT/LanguageDef/Interaction/Controls/ContactMorphisms.lean: "
        ++ "collapse / collapse_identifies / collapse_ne_id; "
        ++ "GSLT/LanguageDef/Contexts/Controls/ReductionBisimilarity.lean: "
        ++ "toMarking. Before these the category had identities only"
      negativeControl := "GSLT/LanguageDef/Interaction/Controls/ContactMorphisms.lean: "
        ++ "inclusion_not_semantic (a map of declarations preserving the selected "
        ++ "sort, contact and rule over which no morphism lies)"
      audited := true
      standing := .constructedHere }
  , { chapter := 8, citation := "Remark 8.1"
      statement :=
        "Binding is not the point: substitution through a binder is one mode by "
        ++ "which a datum migrates from the environment continuation into the "
        ++ "program continuation, and CCS realises the cut with no migration."
      sourceProves := false
      construction := "GSLT/LanguageDef/Interaction/Migration.lean: MigrationMode "
        ++ "/ ContractionSchema.mode / InteractionCutPresentation.migrationMode, "
        ++ "read from the authored contractum"
      provedTheorem := "GSLT/LanguageDef/Interaction/Migration.lean: "
        ++ "exists_subst_of_bindsInto / "
        ++ "ContractionSchema.program_released_of_mode_ne_binding; "
        ++ "Languages/ProcessCalculi/CCS/Cut.lean: ccs_migrationMode; "
        ++ "GSLT/LanguageDef/Interaction/MigrationInstances.lean: "
        ++ "rho_migrationMode / lambda_migrationMode"
      instanceWitness := "Languages/ProcessCalculi/CCS/Cut.lean: ccs_releases"
      negativeControl := "GSLT/LanguageDef/Interaction/MigrationInstances.lean: "
        ++ "lambda_residual_depends_on_argument / rho_binds_through_substitution"
      audited := true
      standing := .provedHere }
  , { chapter := 8, citation := "Section 8.2, the interaction cut"
      statement :=
        "The generating rule has the shape of an interaction cut: the interaction "
        ++ "constructor brings together two introductions, each separating a "
        ++ "surface that must match from a continuation, and a contraction "
        ++ "combines the continuations into residuals."
      sourceProves := false
      construction := "GSLT/LanguageDef/InteractionCut.lean: "
        ++ "InteractionCutPresentation, naming parts of the authored rule"
      provedTheorem := "GSLT/LanguageDef/Continued/CutShape.lean: "
        ++ "InteractionCutPresentation.operands_of_binary_left / "
        ++ "CIGSLT.contractum_head_ne_introductions"
      instanceWitness := "Languages/ProcessCalculi/CCS/Cut.lean: ccsInteractionCut; "
        ++ "Languages/Calculator/Cut.lean: successorCut; "
        ++ "Languages/ProcessCalculi/Ambient/Interaction.lean: dissolutionCut; "
        ++ "Languages/ProcessCalculi/PiCalculus/Synchronous.lean: piSyncInteractionCut"
      negativeControl := "GSLT/LanguageDef/Interaction/BaseInteractions.lean: "
        ++ "mettaCalc_no_interactionCut; GSLT/LanguageDef/Continued/NotContinued.lean: "
        ++ "deep_no_cut (a rule that looks inside an operand has no cut)"
      audited := true
      standing := .provedHere }
  , { chapter := 8, citation := "Section 8.3, nominal and structural surfaces"
      statement :=
        "A surface is carried nominally, as an explicit subject that must match, "
        ++ "or structurally, by the rigidity of a free interaction constructor, "
        ++ "whose position is then unforgeable. The lambda calculus is the "
        ++ "structural case; rho and CCS are nominal."
      sourceProves := false
      construction := "GSLT/LanguageDef/Interaction/Freeness.lean: "
        ++ "EquationHeadsAvoid / InteractivePresentation.RigidContact"
      provedTheorem := "GSLT/LanguageDef/Interaction/Freeness.lean: "
        ++ "InteractivePresentation.position_invariant / equationEquiv_binary_iff"
      instanceWitness := "GSLT/LanguageDef/Interaction/Surfaces.lean: "
        ++ "lambda_surface_structural"
      negativeControl := "GSLT/LanguageDef/Interaction/Surfaces.lean: "
        ++ "rho_surface_nominal / rho_pair_swaps; "
        ++ "Languages/ProcessCalculi/CCS/Surface.lean: ccs_surface_nominal / "
        ++ "handshake_swaps"
      audited := true
      standing := .provedHere }
  , { chapter := 8, citation := "Section 8.3, equations forge position"
      statement :=
        "An equation on the interaction constructor rewrites adjacency without "
        ++ "firing a cut: associativity re-brackets, a unit law inserts and "
        ++ "deletes neighbours, idempotence copies them, and "
        ++ "associative-commutativity dissolves position. Only a free "
        ++ "constructor admits no such move."
      sourceProves := false
      construction := "GSLT/LanguageDef/Interaction/Controls/EquationalContact.lean: "
        ++ "contactWith laws, one signature and one rule with a varying list of "
        ++ "equations"
      provedTheorem := "GSLT/LanguageDef/Interaction/Controls/EquationalContact.lean: "
        ++ "assoc_changes_adjacency / unit_forges_contact / idem_forges_contact / "
        ++ "ac_changes_adjacency, each with its no-cut-fires companion"
      instanceWitness := "GSLT/LanguageDef/Interaction/Controls/EquationalContact.lean: "
        ++ "free_position_invariant"
      negativeControl := "GSLT/LanguageDef/Interaction/Controls/EquationalContact.lean: "
        ++ "collapse_forges_contact (an equation that never mentions the "
        ++ "constructor still forges a contact: freedom from equations on the "
        ++ "constructor alone is not rigidity)"
      audited := true
      standing := .provedHere }
  , { chapter := 8, citation := "Non-example 8.1"
      statement :=
        "The Turing machine has no naive presentation as an interactive GSLT: "
        ++ "the cut would be between automaton and tape, which are of different "
        ++ "kinds."
      sourceProves := false
      construction := "Languages/TuringMachine/LanguageDef.lean: turingMachine, "
        ++ "authored for every transition table"
      provedTheorem := "Languages/TuringMachine/NotInteractive.lean: "
        ++ "turingMachine_not_interactive / turingMachine_no_contact / "
        ++ "run_is_ordered_binary_contact / run_is_not_same_sort_contact"
      instanceWitness := "Languages/TuringMachine/LanguageDef.lean: "
        ++ "turingMachine_validate_eq_nil / appendOne_first_step; "
        ++ "Languages/TuringMachine/NotInteractive.lean: appendOne_semantic_step"
      negativeControl := "Languages/ProcessCalculi/CCS/Interaction.lean: "
        ++ "ccsCalc_isInteractive (the same criteria admit a calculus with a "
        ++ "same-sort contact)"
      audited := true
      standing := .provedHere }
  , { chapter := 8, citation := "Non-example 8.2"
      statement :=
        "Neither a Moore nor a Mealy machine has a naive presentation as an "
        ++ "interactive GSLT, for the reason of Non-example 8.1. Under a forced "
        ++ "reading they would occupy the null-migration and binding-migration "
        ++ "positions respectively."
      sourceProves := false
      construction := "Languages/Transducers/LanguageDef.lean: transducer; "
        ++ "GSLT/LanguageDef/Interaction/HeterogeneousCut.lean: "
        ++ "HeterogeneousCutReading; Languages/Transducers/ForcedReading.lean: "
        ++ "emissionReading / controlReading"
      provedTheorem := "Languages/Transducers/NotInteractive.lean: "
        ++ "transducer_not_interactive / transducer_no_contact; "
        ++ "Languages/Transducers/ForcedReading.lean: moore_dataMode / mealy_dataMode "
        ++ "/ moore_emitted_independent_of_stream / mealy_emitted_depends_on_symbol / "
        ++ "mealy_contractum_reads_stream / feed_operands_not_both_configurations; "
        ++ "GSLT/LanguageDef/Interaction/HeterogeneousCut.lean: "
        ++ "HeterogeneousCutReading.rule_not_interaction (the rule read is the "
        ++ "interaction rule of no interactive presentation of its language) / "
        ++ "HeterogeneousCutReading.operands_not_both_of_sort / "
        ++ "HeterogeneousCutReading.contractum_reads_environment; "
        ++ "GSLT/LanguageDef/Interaction/Strength.lean: "
        ++ "InteractivePresentation.not_everyRuleIsCut_of_heterogeneousReading"
      instanceWitness := "Languages/Transducers/NotInteractive.lean: "
        ++ "parity_semantic_step / change_semantic_step"
      negativeControl := "Languages/Transducers/ForcedReading.lean: "
        ++ "control_dataMode (the next control state reads the consumed symbol "
        ++ "under both disciplines, so the null position holds for the emitted "
        ++ "value only)"
      audited := true
      standing := .provedHere }
  , { chapter := 8, citation := "Section 8.7, presentation versus encoding"
      statement :=
        "A theory having an interactive presentation differs from a theory "
        ++ "admitting an encoding into one that does: the interaction sites of "
        ++ "an encoded machine are the sites of the target."
      sourceProves := false
      construction := "Languages/TuringMachine/OneSort.lean: oneSortMachine, the "
        ++ "constructors and rules of the machine with all its sorts merged into one, "
        ++ "authored for every transition table; Languages/TuringMachine/Hosted.lean: "
        ++ "hostingMorphism, the map of declarations from the machine into it, as a "
        ++ "morphism of theories. The source's own example, an encoding into rho with "
        ++ "the tape as processes, is not formalized"
      provedTheorem := "Languages/TuringMachine/Hosted.lean: "
        ++ "presentation_versus_encoding (for every non-empty table the machine "
        ++ "admits no interactive presentation, its one-sort presentation is "
        ++ "interactive, and the map between them preserves and reflects transitions, "
        ++ "is hosting, and is not exhausting) / hostingMorphism_hosting / "
        ++ "hostingMorphism_not_exhausting; Languages/TuringMachine/OneSort.lean: "
        ++ "oneSortMachine_isInteractive / oneSort_step_iff", instanceWitness := "Languages/TuringMachine/OneSort.lean: "
        ++ "oneSortMachine_validate_eq_nil; Languages/TuringMachine/Steps.lean: "
        ++ "step_iff_machineStep / step_sorted"
      negativeControl := "Languages/TuringMachine/OneSort.lean: "
        ++ "oneSortMachine_empty_not_interactive (with an empty table no rule is "
        ++ "headed by the contact); "
        ++ "GSLT/LanguageDef/Interaction/StrengthInstances.lean: "
        ++ "turingMachine_second_without_first"
      audited := true
      standing := .provedHere }
  ]

/-! ## Chapter 9

Four definitions, one proposition and two remarks are numbered. The two
tables of Section 9.4 are entered as section rows.
-/

/-- Chapter 9's rows: sections, wrappability, continued interactive theories,
the forgetful functor, and the tables of instances. -/
def chapter9 : List Obligation :=
  [ { chapter := 9, citation := "Definition 9.1"
      statement :=
        "An interactive GSLT is section-equipped when it comes with a computable "
        ++ "section of the quotient of the interacting sort by structural "
        ++ "congruence: a computable canonical-form function."
      sourceProves := false
      construction := "GSLT/LanguageDef/CanonicalSection.lean: "
        ++ "ComputableCanonicalSection, a function with two laws; "
        ++ "GSLT/LanguageDef/EffectiveSection.lean: Effective, tracking by a "
        ++ "computable function on injective term codes. The record alone asks "
        ++ "nothing about how the function is obtained: "
        ++ "ComputableCanonicalSection.ofChoice inhabits it for every theory. "
        ++ "OSLF/MeTTaIL/PatternCodeRecursion.lean: bottomUpCode, the tracking on "
        ++ "codes of a rewriting from the leaves up"
      provedTheorem := "GSLT/LanguageDef/EffectiveSection.lean: "
        ++ "Effective.computablePred (an effective section decides the static "
        ++ "equivalence along every computable family of terms); "
        ++ "OSLF/MeTTaIL/PatternCodeRecursion.lean: bottomUpCode_primrec / "
        ++ "bottomUpCode_patternCode; GSLT/LanguageDef/BagNormalFormEffective.lean: "
        ++ "normalFormCode_primrec / bagCanonicalSection_effective (the normal form "
        ++ "of a bag, with or without a unit, is tracked by a primitive recursive "
        ++ "function on codes)"
      instanceWitness := "GSLT/LanguageDef/EffectiveSection.lean: "
        ++ "lambdaCanonicalSection_effective; "
        ++ "GSLT/LanguageDef/Continued/EffectiveInstances.lean: "
        ++ "table_sections_effective; Languages/Calculator/EffectiveSection.lean: "
        ++ "calculatorSection_effective; "
        ++ "Languages/ProcessCalculi/RhoCalculus/CanonicalSectionEffective.lean: "
        ++ "rhoCanonicalSection_effective, for the section of the reflective relation"
      negativeControl := "Languages/PartrecMachine/UndecidableEquivalence.lean: "
        ++ "equivalence_not_computable / historyTheory_no_effective_section; "
        ++ "Languages/PartrecMachine/HistoryIsomorphism.lean: "
        ++ "no_effective_section_of_iso"
      audited := true
      standing := .provedHere }
  , { chapter := 9, citation := "Definition 9.2"
      statement :=
        "The contraction is wrappable when it is well-sorted as an operation on "
        ++ "wrapped continuations, mapping decorated inputs to decorated outputs."
      sourceProves := false
      construction := "GSLT/LanguageDef/Continued/ContinuationDecoration.lean: ContinuationDecorationSlot / "
        ++ "ContinuationDecorationProfile / Wrappable / RedexRetypable. A finite bundle selects actual authored "
        ++ "parameter positions and opaque schema occurrences; constructor closure is independent. This "
        ++ "certifies the generated sorting problem for a selected rule, not generalized Cost activation, "
        ++ "no-leak or iteration."
      provedTheorem := "ContinuationDecorationProfile.programAdditional_result / environmentAdditional_result / "
        ++ "ofRetypingPlan_wrappable_iff / ofRetypingPlan_redexRetypable_iff; "
        ++ "Languages/ProcessCalculi/RhoCalculus/SynchronousDecoration.lean: "
        ++ "communicationDecoration_redexRetypable / communicationDecoration_wrappable; "
        ++ "Languages/InteractionCategory/Decoration.lean: visibleDecoration_wrappable."
      instanceWitness := "SynchronousDecoration.lean: communicationDecoration, wrapping the input body, message and output "
        ++ "continuation; InteractionCategory/Decoration.lean: visibleDecoration, including the rebuilt action "
        ++ "prefix in its declared closure."
      negativeControl := "SynchronousDecoration.lean: decoration_separates_two_slots; InteractionCategory/Decoration.lean: "
        ++ "decoration_separates_constructor_closure. These exclude the restrictive two-slot or non-principal "
        ++ "profiles, not every possible continuation decoration."
      audited := true
      standing := .constructedHere }
  , { chapter := 9, citation := "Definition 9.3"
      statement :=
        "A continued interactive GSLT is an interactive GSLT equipped with a "
        ++ "presentation of its dynamics in interaction-cut form, a section, and "
        ++ "wrappability. Morphisms are theory maps that are "
        ++ "bisimulation-preserving on the interacting sort and quote-faithful."
      sourceProves := false
      construction := "GSLT/LanguageDef/Continued/Presentation.lean: ContinuedPresentation / IsContinued, for one selected "
        ++ "authored cut, an algebraic section and finite continuation decoration. Continued/Effective.lean: "
        ++ "IsEffectivelyContinued supplies code tracking for that section. These records do not quantify over a "
        ++ "cut family covering all dynamics. ContinuedCategory.lean: CIGSLT / CIGSLT.Morphism retain the "
        ++ "stronger reflective, hereditary Cost profile; this category is not identified with the full source "
        ++ "model class."
      provedTheorem := "Continued/Presentation.lean: CIGSLT.toContinuedPresentation, conditional on absence of added "
        ++ "reflective presentations; Continued/Effective.lean: IsEffectivelyContinued.computablePred; "
        ++ "Continued/NotContinued.lean: deep_not_continued. No equivalence with the independently specified "
        ++ "effective, whole-dynamics source category is proved."
      instanceWitness := "Continued/Presentation.lean: lambda_isContinued / bare_isContinued; CCS/Continued.lean: "
        ++ "ccs_isContinued; Ambient/Continued.lean: ambient_isContinued; InteractionCategory/Continued.lean: "
        ++ "visible_isEffectivelyContinued; Continued/InstanceTable.lean: rhoSync_isContinued, with an "
        ++ "explicitly noncomputable ordinary-quotient section, not an effectiveness result."
      negativeControl := "Continued/NotContinued.lean: deep_no_cut / deep_not_continued; "
        ++ "Languages/PartrecMachine/HistoryContinued.lean: history_not_effectivelyContinued. Legacy-plan "
        ++ "obstruction is separately isEmpty_retypingPlan_of_contractum_headed_by_program."
      audited := true
      standing := .constructedHere }
  , { chapter := 9, citation := "Definition 9.4"
      statement :=
        "The forgetful functor sends a continued interactive GSLT to its "
        ++ "underlying interactive GSLT and acts as the identity on the "
        ++ "underlying theory map of a morphism."
      sourceProves := false
      construction := "GSLT/LanguageDef/ContinuedCategory.lean: CIGSLT.forget, on the recorded stronger Cost category; "
        ++ "Continued/Forget.lean: forgetUpToTheoryMap, on morphisms identified when their underlying theory "
        ++ "maps agree. An effective category with whole-dynamics cut coverage has not been identified with "
        ++ "these carriers."
      provedTheorem := "GSLT/LanguageDef/Continued/Forget.lean: "
        ++ "CIGSLT.Morphism.canonicalKeyMap_eq_of_underlying_eq (morphisms over "
        ++ "one theory map act alike on canonical keys)"
      instanceWitness := "GSLT/LanguageDef/Continued/Sections.lean: "
        ++ "lambda_at_both_levels; "
        ++ "GSLT/LanguageDef/Interaction/Controls/ContactContinued.lean: "
        ++ "bareContinued_forget"
      negativeControl := "GSLT/LanguageDef/Continued/Forget.lean: "
        ++ "lambdaRenamedIdentity_over_identity (two morphisms over the identity "
        ++ "theory map: the recorded morphism carries a datum the theory map does "
        ++ "not determine)"
      audited := true
      standing := .constructedHere }
  , { chapter := 9, citation := "Proposition 9.1"
      statement :=
        "The forgetful functor is faithful but neither full nor essentially "
        ++ "surjective; hence continued interactive GSLTs form a genuine, proper "
        ++ "subcategory of interactive GSLTs."
      sourceProves := true
      construction := "GSLT/LanguageDef/Continued/Forget.lean, NotFull.lean, "
        ++ "NotEssentiallySurjective.lean"
      provedTheorem := "Continued/Forget.lean: forgetUpToTheoryMap_faithful for the quotient by underlying theory maps, and "
        ++ "forget_not_faithful for the richer recorded arrows. Continued/NotFull.lean: collapse_has_no_lift / "
        ++ "forget_not_full; NotEssentiallySurjective.lean: forget_not_essSurj / deep_not_underlying, for the "
        ++ "recorded CIGSLT category. Successor and synchronous-rho obstructions there concern its restrictive "
        ++ "Cost plans. PartrecMachine/HistoryContinued.lean and HistoryIsomorphism.lean: "
        ++ "history_not_effectivelyContinued / not_effectivelyContinued_of_iso under the named equality-relation "
        ++ "condition. These are distinct categories and contracts, not the three source assertions about one "
        ++ "independently matched category."
      instanceWitness := "GSLT/LanguageDef/Continued/Effective.lean: "
        ++ "lambda_isEffectivelyContinued; "
        ++ "GSLT/LanguageDef/Continued/EffectiveInstances.lean: "
        ++ "effectivelyContinued_rows; "
        ++ "GSLT/LanguageDef/Interaction/Controls/ContactContinued.lean: "
        ++ "bareContinued"
      negativeControl := "Continued/Sections.lean: continuedPresentation_underlying_not_injective; Continued/Forget.lean: "
        ++ "lambdaRenamedIdentity_over_identity. Added object choices and independently stored arrow data "
        ++ "prevent interpreting this forgetful functor as a literal subcategory inclusion."
      audited := true
      standing := .constructedHere }
  , { chapter := 9, citation := "Remark 9.1"
      statement :=
        "The lambda calculus is an interactive GSLT as such and becomes a "
        ++ "continued one only once the added structure is chosen: continued is "
        ++ "added structure, not a property read off the interactive GSLT."
      sourceProves := false
      construction := "GSLT/LanguageDef/LambdaContinuedInteraction.lean: lambdaIGSLT / lambdaCIGSLT. The carrier is locally "
        ++ "nameless with alpha-equivalence already erased; the source example choosing different named alpha "
        ++ "representatives has not been constructed."
      provedTheorem := "Continued/Sections.lean: lambda_at_both_levels / ccs_two_continuedPresentations / "
        ++ "continuedPresentation_underlying_not_injective. The added-structure distinction is proved on CCS, "
        ++ "with the canonical form of its restriction blocks and its reversal as the two sections, while the "
        ++ "exact named-lambda example remains open."
      instanceWitness := "GSLT/LanguageDef/Continued/Sections.lean: "
        ++ "ccs_sections_differ (two sections of one theory)"
      negativeControl := "GSLT/LanguageDef/Continued/Presentation.lean: "
        ++ "lambda_section_unique (on the locally nameless carrier the lambda "
        ++ "calculus has exactly one section, so the choice the remark speaks of "
        ++ "is exhibited on CCS)"
      audited := true
      standing := .constructedHere }
  , { chapter := 9, citation := "Remark 9.2"
      statement :=
        "The instances are ordered by how much information the contraction moves "
        ++ "from the environment continuation into the program continuation: no "
        ++ "migration, migration by binding, migration by spatial restructuring, "
        ++ "and migration as interface composition."
      sourceProves := false
      construction := "GSLT/LanguageDef/Interaction/Migration.lean: MigrationMode "
        ++ "with the four modes, computed from the authored contractum"
      provedTheorem := "GSLT/LanguageDef/Continued/InstanceTable.lean: "
        ++ "migration_spectrum"
      instanceWitness := "Languages/ProcessCalculi/CCS/Cut.lean: ccs_migrationMode; "
        ++ "Languages/ProcessCalculi/PiCalculus/Synchronous.lean: piSync_migrationMode; "
        ++ "Languages/ProcessCalculi/Ambient/Interaction.lean: "
        ++ "dissolution_migrationMode; Languages/InteractionCategory/Interaction.lean: "
        ++ "silent_migrationMode / visible_migrationMode"
      negativeControl := "Languages/ProcessCalculi/Ambient/Interaction.lean: "
        ++ "dissolution_none_without_location (the spatial mode is read from the "
        ++ "reduction positions of the theory); the interaction categories are "
        ++ "null-migrating in the silent reading and interface-composing in the "
        ++ "visible one"
      audited := true
      standing := .provedHere }
  , { chapter := 9, citation := "Table 9.1"
      statement :=
        "The interaction-cut data of each instance: the interaction constructor, "
        ++ "its equations, the surfaces, the continuations and the mode of the "
        ++ "contraction, for CCS, the interaction categories, rho and pi "
        ++ "synchronous and asynchronous, lambda and the ambients."
      sourceProves := false
      construction := "GSLT/LanguageDef/Continued/InstanceTable.lean: authored cut data for the listed presentations. "
        ++ "Synchronous rho includes the full three-payload decoration. The interaction-category presentation is "
        ++ "a concrete operational model with silent/visible readings; no comparison with the general "
        ++ "interaction-category model of the source is proved."
      provedTheorem := "GSLT/LanguageDef/Continued/InstanceTable.lean: ccs_row / "
        ++ "ccs_contact_laws / interactionCategory_silent_row / rho_row / pi_row / "
        ++ "piSync_row / lambda_row / ambient_row"
      instanceWitness := "Languages/ProcessCalculi/CCS/Cut.lean: ccs_releases"
      negativeControl := "Languages/ProcessCalculi/RhoCalculus/SynchronousDecoration.lean: decoration_separates_two_slots; "
        ++ "Languages/InteractionCategory/Decoration.lean: decoration_separates_constructor_closure. Both are "
        ++ "controls on chosen decoration profiles, not negative source verdicts."
      audited := true
      standing := .constructedHere }
  , { chapter := 9, citation := "Table 9.2"
      statement :=
        "Verdicts: the calculator and the three machines are GSLTs only; CCS, "
        ++ "the interaction categories, rho and pi synchronous and asynchronous, "
        ++ "lambda and the ambients are continued interactive."
      sourceProves := false
      construction := "GSLT/LanguageDef/Continued/InstanceTable.lean: distinct algebraic, effective and restrictive Cost "
        ++ "verdicts. The asynchronous-rho row identifies a reflective CIGSLT underlying object; it does not "
        ++ "provide an ordinary-equation IsContinued or effective witness. The synchronous ordinary-equation "
        ++ "witness uses choice, and no computable section is inferred from it. Whole-dynamics coverage and the "
        ++ "general interaction-category comparison remain separate obligations."
      provedTheorem := "Continued/InstanceTable.lean: calculator_row / ccs_row / interactionCategory_silent_row / "
        ++ "interactionCategory_visible_row / rho_row / rhoSync_row / pi_row / piSync_row / lambda_row / "
        ++ "ambient_row / turing_row / transducer_row. Continued/EffectiveInstances.lean: the explicit "
        ++ "effectivelyContinued_rows / table_sections_effective conjunctions; "
        ++ "InteractionCategory/Continued.lean: visible_isEffectivelyContinued. These conjunctions do not "
        ++ "certify every newly listed section."
      instanceWitness := "GSLT/LanguageDef/Continued/InstanceTable.lean: "
        ++ "transducer_forced_reading"
      negativeControl := "SynchronousDecoration.lean: decoration_separates_two_slots; InteractionCategory/Decoration.lean: "
        ++ "decoration_separates_constructor_closure; Continued/InstanceTable.lean: calculatorRewriting_row. The "
        ++ "first two distinguish restrictive profiles from actual positive algebraic continuation decoration."
      audited := true
      standing := .constructedHere }
  ]

/-! ## Chapter 10

Four definitions and four remarks are numbered. The three defects of
Section 10.1 and the construction of Section 10.2 are entered as section rows.
-/

/-- Chapter 10's rows: the defects of the naive definition, contexts as the
primary structure, morphisms of theories, hosting and exhausting. -/
def chapter10 : List Obligation :=
  [ { chapter := 10, citation := "Section 10.1, the constant map"
      statement :=
        "Under the naive definition the map sending every term to one term "
        ++ "preserves bisimulation trivially, so it is a morphism from anything "
        ++ "to anything and the category orders nothing."
      sourceProves := true
      construction := "GSLT/Contexts/ConstantMap.lean: GSLT.Morphism.constant, "
        ++ "for the morphisms of GSLT/Core/GSLT.lean"
      provedTheorem := "GSLT/Contexts/ConstantMap.lean: GSLT.nonempty_hom / "
        ++ "GSLT.nonempty_hom_both"
      instanceWitness := "GSLT/LanguageDef/Contexts/Controls/ConstantMap.lean: constantToCCS, a static map sending terms to "
        ++ "the inactive process and contexts to parallel composition of their holes. It preserves image "
        ++ "bisimilarity, but this alone does not supply the transition transport now required of "
        ++ "ContextMorphism."
      negativeControl := "GSLT/Contexts/ConstantMap.lean: ContextMap.constant_requires_self_transition; "
        ++ "LanguageDef/Contexts/Controls/ConstantMap.lean: constantToCCS_not_hosting. A constant map "
        ++ "transporting a genuine source step must have a self-transition at its target value."
      audited := true
      standing := .provedHere }
  , { chapter := 10, citation := "Section 10.1, an encoding is not a map of terms"
      statement :=
        "The canonical encoding of the lambda calculus into the pi calculus "
        ++ "sends a term to a process parameterised by a name, and no "
        ++ "constructor to a single operator, so requiring morphisms to be "
        ++ "signature homomorphisms excludes the motivating example. Defined on "
        ++ "contexts, such an encoding is expressible: the parameterisation is "
        ++ "the interface."
      sourceProves := true
      construction := "GSLT/LanguageDef/Encodings/PatternShape.lean: patternShape / nodeCount; "
        ++ "PiCalculus/ProcessContext.lean: ProcessContext. The exact parameterized lambda-to-pi motivating "
        ++ "encoding is not formalized. The implemented pi-to-rho carrier encoding supplies related shape and "
        ++ "context controls, with a restriction-free forward-simulation theorem and explicit failures under "
        ++ "restriction."
      provedTheorem := "GSLT/LanguageDef/Encodings/PatternShape.lean: "
        ++ "patternShape_mapPattern / mapPattern_ne_of_shape_ne (a map of symbols "
        ++ "preserves the shape of a term); "
        ++ "Languages/ProcessCalculi/PiCalculus/EncodingNotSignatureMap.lean: "
        ++ "encode_not_signatureMap / encode_not_igsltMorphism / "
        ++ "no_parameter_free_translation; "
        ++ "Languages/ProcessCalculi/PiCalculus/EncodingEquivariance.lean: "
        ++ "ProcessContext.encode_fill / ProcessContext.encode_comp (the encoding "
        ++ "commutes with plugging on the nose, the name parameter threaded "
        ++ "through the context)"
      instanceWitness := "Languages/ProcessCalculi/PiCalculus/EncodingStepRF.lean: "
        ++ "step_preserved_rf / contextStep_preserved_rf (without restriction and "
        ++ "replication one step is sent to one step)"
      negativeControl := "Languages/ProcessCalculi/PiCalculus/EncodingTransitions.lean: "
        ++ "restricted_step_not_preserved / listener_step_not_reflected / "
        ++ "congruent_sources_separated_by_image; "
        ++ "Languages/ProcessCalculi/PiCalculus/FullEncodingTransitions.lean: "
        ++ "fullEncode_nu_step_not_matched / nu_nil_not_respected. This encoding "
        ++ "is therefore not a morphism in the sense of Definition 10.1: "
        ++ "transitions are not preserved under restriction, and its term map "
        ++ "does not respect the static equivalence"
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Section 10.1, target contexts observe too much"
      statement :=
        "A context of the target may observe the syntactic form of what it is "
        ++ "handed, so bisimulation computed over all target contexts separates "
        ++ "images that no source context separates."
      sourceProves := true
      construction := "GSLT/LanguageDef/Contexts/Controls/OverObservation.lean: "
        ++ "the contact theory and its extension by a constructor Test with the "
        ++ "rule Test(A) --> Nil"
      provedTheorem := "GSLT/LanguageDef/Contexts/Controls/OverObservation.lean: "
        ++ "over_observation (two constants bisimilar over all source contexts; "
        ++ "their images bisimilar over the images of those contexts and not "
        ++ "over all target contexts)"
      instanceWitness := "GSLT/LanguageDef/Contexts/Controls/OverObservation.lean: "
        ++ "toProbingMorphism / constants_bisimilar"
      negativeControl := "GSLT/LanguageDef/Contexts/Controls/OverObservation.lean: "
        ++ "images_not_bisimilar / images_not_bisimilar_targetProbe"
      audited := true
      standing := .provedHere }
  , { chapter := 10, citation := "Section 10.2, contexts as the primary structure"
      statement :=
        "A theory presents a symmetric multicategory of contexts: its objects "
        ++ "are interfaces, recording the sort of a hole, its binding stage and "
        ++ "its interaction surface; its multimorphisms are contexts with holes "
        ++ "of given interfaces; composition is plugging; terms are the nullary "
        ++ "contexts. Transitions are labelled by contexts, and bisimulation is "
        ++ "taken over them."
      sourceProves := false
      construction := "OSLF/MeTTaIL/MultiHoleContext.lean: typed linear contexts with fill / bind / plug. "
        ++ "GSLT/Contexts/ContextTheory.lean: context action, equations, selected operational relation and "
        ++ "probes. LanguageDef/Contexts/Presented.lean: interfaces record type and binding stage, not an "
        ++ "interaction-surface invariant. The symmetric laws are proved through filling; an ambient "
        ++ "contextual-equation multicategory matching all source interfaces has not been identified."
      provedTheorem := "OSLF/MeTTaIL/MultiHoleContext.lean: fill_bind / bind_bind / "
        ++ "Linear.plug / exists_oneHole; GSLT/Contexts/ContextTheory.lean: "
        ++ "fill_plug_plug / constant_fill_equiv / Probe.Bisimilar.apply; "
        ++ "GSLT/LanguageDef/Contexts/Presented.lean: exists_oneHole_of_label; "
        ++ "GSLT/LanguageDef/Contexts/Interacting.lean: gslt_bisimilar_iff / "
        ++ "presentedBisimilar_of_fullProbe; "
        ++ "GSLT/Contexts/RelativeEquivalence.lean: endoProbe_bisimilar_iff_relEquiv"
      instanceWitness := "GSLT/LanguageDef/Contexts/TypedLabels.lean: "
        ++ "labelOfOccurrence (the context around an occurrence in a well-sorted "
        ++ "term is a label); GSLT/LanguageDef/Contexts/Controls/OverObservation.lean: "
        ++ "testLabel"
      negativeControl := "OSLF/MeTTaIL/MultiHoleContext.lean: "
        ++ "not_linear_of_duplicate; GSLT/LanguageDef/Interaction/Fire.lean: "
        ++ "fill_injective"
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Definition 10.1"
      statement :=
        "A morphism of GSLTs is a pseudofunctor of context multicategories that "
        ++ "is bisimulation-preserving for context-labelled transitions, where "
        ++ "the bisimulation on the target is computed only over the image of "
        ++ "the source's contexts."
      sourceProves := false
      construction := "GSLT/Contexts/ContextMorphism.lean: ContextMap / ContextEquivOnImage / ContextMorphism. A morphism "
        ++ "now requires forward transition transport and bisimilarity preservation for every source probe. "
        ++ "Equivariance yields identity, plugging and equation laws on image fillings only; it does not "
        ++ "identify an ambient context pseudofunctor. Contexts/TransitionProfile.lean: withRewrites / "
        ++ "nonemptyReduction, an explicit nonempty finite-computation profile, not weak silent-action "
        ++ "semantics."
      provedTheorem := "ContextMap.context_resp_on_image / context_identity_on_image / context_plug_on_image / "
        ++ "bisimilar_push_of_transitions; Contexts/TransitionProfile.lean: preservesTransitions_iff_rewrites / "
        ++ "reflectsTransitions_iff_rewrites / preservesNonemptyReduction. LanguageDef/Contexts/Structural.lean "
        ++ "reuses these laws for structural translations. Declaration simulation transports conditional "
        ++ "premises and equations with explicit evaluator conditions and complete algebra metadata transport; no injectivity is needed."
      instanceWitness := "GSLT/LanguageDef/Contexts/Controls/Hosting.lean: "
        ++ "collapseMorphism / ofReflectingIGSLTMorphism / ofIGSLTMorphism; "
        ++ "GSLT/LanguageDef/Contexts/Controls/OverObservation.lean: "
        ++ "toProbingMorphism; GSLT/LanguageDef/Contexts/Controls/Renaming.lean: "
        ++ "swapMorphism; Languages/TuringMachine/Hosted.lean: hostingMorphism; "
        ++ "GSLT/LanguageDef/Contexts/Controls/EquationTransport.lean: "
        ++ "addCommutativity_preservesEquations (authored equations on both sides); "
        ++ "Languages/TransitionSystem/Extension.lean: Table.inclusionMorphism (an "
        ++ "inclusion that adds moves at one state and is a morphism for every probe, "
        ++ "without reflecting transitions)"
      negativeControl := "Contexts/Controls/ImageAction.lean: identity_not_on_target, a valid abstract ContextMorphism whose "
        ++ "identity law holds only on image terms. LanguageDef/Contexts/Controls/ReductionBisimilarity.lean: "
        ++ "reduction_bisimilarity_insufficient / toMarking_not_contextMorphism; "
        ++ "Controls/EquationTransport.lean: collection_unit_metadata_required; Controls/TransitionProfile.lean: "
        ++ "profiles_distinguish_cost / reply_no_macroStep."
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Remark 10.1"
      statement :=
        "A morphism is a pair of a map on terms and a functor on contexts, with "
        ++ "an equivariance condition up to the equivalence and preservation of "
        ++ "transitions along the functor; the restriction of the target's "
        ++ "observers to the image is a consequence of naming the functor. "
        ++ "Faithfulness of the functor should be a property and not part of "
        ++ "morphism-hood."
      sourceProves := false
      construction := "GSLT/Contexts/ContextMorphism.lean: static ContextMap with equivariant, plus "
        ++ "ContextMorphism.transitions and per-probe bisimilarity preservation. Faithfulness, forward transport "
        ++ "and backward lifting are separately named properties. An ambient functor on context classes is not "
        ++ "inferred from the pair of image actions."
      provedTheorem := "GSLT/Contexts/ContextMorphism.lean: "
        ++ "ContextMap.apply_equivariant / ContextMorphism.ofTransitions; "
        ++ "GSLT/Contexts/ImageObservation.lean: "
        ++ "ContextMap.bisimilar_push_iff_of_transitions (a map that preserves and "
        ++ "reflects transitions neither adds nor loses bisimilarity, as any probe "
        ++ "sees it)"
      instanceWitness := "GSLT/LanguageDef/Contexts/Controls/Hosting.lean: "
        ++ "collapseMorphism (a morphism that is not hosting)"
      negativeControl := "Contexts/Controls/ImageAction.lean: identity_not_on_target; "
        ++ "LanguageDef/Contexts/Controls/ReductionBisimilarity.lean: faithfulness_does_not_reflect; "
        ++ "Controls/LongerRun.lean: lengthen_faithful / lengthen_not_hosting."
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Definition 10.2"
      statement :=
        "GSLT is the category whose 0-cells are GSLTs and whose morphisms are "
        ++ "the maps of Definition 10.1: bisimulation-preserving for the "
        ++ "context-labelled transition relation, which is thereby a congruence."
      sourceProves := false
      construction := "GSLT/Contexts/ContextMorphism.lean: Category ContextTheory, with id / comp and explicit transition "
        ++ "transport. Contextual bisimilarity is a congruence for probes closed under observer composition. "
        ++ "This is the checked category of image-action morphisms; its identification with source "
        ++ "pseudofunctors remains unproved."
      provedTheorem := "GSLT/Contexts/ContextTheory.lean: Probe.Bisimilar.apply "
        ++ "(bisimilarity as a closed probe sees it is preserved by every "
        ++ "observer) / fullProbe_closed"
      instanceWitness := "GSLT/LanguageDef/Contexts/Controls/OverObservation.lean: "
        ++ "constants_bisimilar"
      negativeControl := "GSLT/LanguageDef/Contexts/Controls/ReductionBisimilarity.lean: "
        ++ "images_not_bisimilar_over_image"
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Definition 10.3"
      statement :=
        "A morphism is hosting, faithful, when the target can run the source: "
        ++ "the encoding reflects as well as preserves the context-labelled "
        ++ "transition structure, so that no branching present in the source is "
        ++ "lost in the target."
      sourceProves := false
      construction := "GSLT/Contexts/ContextMorphism.lean: Hosting separately requires context faithfulness, forward "
        ++ "transition transport and backward lifting at the selected operational profile. Faithful is "
        ++ "equivalent to ReflectsEquations for the recorded action on contexts; it does not imply backward "
        ++ "lifting. Identification with hosting morphisms of the ambient source context category remains "
        ++ "unproved alongside Definition 10.1."
      provedTheorem := "ContextMap.hosting_iff / faithful_iff_reflectsEquations / Hosting.branches / Hosting.comp; "
        ++ "Contexts/ImageObservation.lean: Hosting.bisimilar_push_iff. Invertible.lean: Inverse.hosting, under "
        ++ "preservation of equations and reductions in both directions."
      instanceWitness := "GSLT/LanguageDef/Contexts/Controls/Hosting.lean: "
        ++ "toProbing_hosting; GSLT/LanguageDef/Contexts/Controls/Renaming.lean: "
        ++ "swap_hosting_exhausting; Languages/TuringMachine/Hosted.lean: "
        ++ "hostingMorphism_hosting"
      negativeControl := "Controls/Hosting.lean: collapse_not_hosting; Controls/ReductionBisimilarity.lean: "
        ++ "faithfulness_does_not_reflect / toMarking_not_hosting; Controls/LongerRun.lean: lengthen_faithful / "
        ++ "lengthen_not_hosting. Static faithfulness and per-probe bisimilarity preservation do not imply "
        ++ "backward transition lifting."
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Definition 10.4"
      statement :=
        "A morphism is exhausting, dense, when the target is nothing the source "
        ++ "cannot assemble: every context of the target relevant to the image "
        ++ "is, up to the equivalence, in the image of a context of the source."
      sourceProves := false
      construction := "GSLT/Contexts/ContextMorphism.lean: ContextMap.Exhausting, "
        ++ "contexts of the target between images of interfaces being compared with "
        ++ "images by their action on images; GSLT/Contexts/ImageObservation.lean: "
        ++ "ContextMap.targetProbe, the probe of those contexts. The elementary action and observation results "
        ++ "below are proved; identification with the ambient source context functor remains unproved "
        ++ "alongside Definition 10.1."
      provedTheorem := "GSLT/Contexts/ContextMorphism.lean: "
        ++ "ContextMap.Exhausting.term_surjective / ContextMap.Exhausting.comp; "
        ++ "GSLT/Contexts/ImageObservation.lean: "
        ++ "ContextMap.Exhausting.bisimilar_targetProbe_iff (under an exhausting map, "
        ++ "bisimilarity over the image of the source's contexts is bisimilarity over "
        ++ "the contexts of the target) / "
        ++ "ContextMap.Exhausting.bisimilar_targetProbe_iff_source / "
        ++ "ContextMorphism.preserves_targetProbe; "
        ++ "GSLT/LanguageDef/Contexts/Invertible.lean: Inverse.exhausting"
      instanceWitness := "GSLT/Contexts/ContextMorphism.lean: "
        ++ "ContextMap.exhausting_id; "
        ++ "GSLT/LanguageDef/Contexts/Controls/Renaming.lean: swap_hosting_exhausting "
        ++ "/ swap_moves_a_term / swap_bisimilar_iff (the exchange of two constants: "
        ++ "hosting, exhausting, and not the identity)"
      negativeControl := "GSLT/LanguageDef/Contexts/Controls/Hosting.lean: "
        ++ "toProbing_not_exhausting / collapse_not_exhausting; "
        ++ "GSLT/LanguageDef/Contexts/Controls/OverObservation.lean: "
        ++ "targetProbe_sees_more (for the inclusion, which is not exhausting, the "
        ++ "contexts of the target see more than the images of the source's "
        ++ "contexts); Languages/TuringMachine/Hosted.lean: "
        ++ "hostingMorphism_not_exhausting"
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Remark 10.2"
      statement :=
        "Hosting is faithfulness of the functor on contexts and exhausting is "
        ++ "its density. The constant map fails hosting immediately. Together "
        ++ "the conditions induce a preorder on theories."
      sourceProves := false
      construction := "GSLT/Contexts/ContextMorphism.lean: ContextTheory.Embeds with strong hosting and exhausting. "
        ++ "Contexts/Traces.lean: TraceEmbeds with the same hosting obligations. The identification of hosting "
        ++ "with bare faithfulness is not valid for the recorded context maps; it omits operational "
        ++ "correspondence."
      provedTheorem := "ContextMap.hosting_iff / faithful_iff_reflectsEquations / ContextTheory.embeds_refl / embeds_trans; "
        ++ "Contexts/Traces.lean: Hosting.preservesTraces / ContextTheory.traceEmbeds_iff_embeds / "
        ++ "traceEmbeds_refl / traceEmbeds_trans. Under the same strong hosting contract, the embedding "
        ++ "preorders coincide even though trace equivalence on terms is strictly coarser than bisimilarity. A "
        ++ "separate weaker input/output trace-collapse preorder has not been constructed."
      instanceWitness := "GSLT/LanguageDef/Contexts/Controls/Hosting.lean: "
        ++ "hosting_exhausting_separated"
      negativeControl := "Controls/ConstantMap.lean: constantToCCS_not_hosting; Controls/LongerRun.lean: lengthen_faithful / "
        ++ "lengthen_not_reflectsTransitions / lengthen_not_hosting / morphism_need_not_preserve_traces. This is "
        ++ "a general-morphism counterexample, not a counterexample to equality of the strong hosting preorders. "
        ++ "Turing completeness as a degree of a weaker trace comparison remains open."
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Remark 10.3"
      statement :=
        "Expressiveness is not anchored to Turing completeness, a statement "
        ++ "about the input/output relation; Definition 10.1 replaces the "
        ++ "yardstick with a relative property: fix a probe and ask what that "
        ++ "probe can see."
      sourceProves := false
      construction := "GSLT/Contexts/ContextTheory.lean: Probe / Probe.Bisimilar / "
        ++ "reductionProbe / fullProbe; GSLT/Contexts/Traces.lean: Probe.Path / "
        ++ "Probe.HasTrace / Probe.TraceEquivalent; "
        ++ "GSLT/Contexts/RelativeEquivalence.lean: endoProbe. The comparison with "
        ++ "Turing completeness is not formalized"
      provedTheorem := "GSLT/Contexts/ContextTheory.lean: "
        ++ "reductionProbe_bisimilar_iff / bisimilar_toGSLT / "
        ++ "Probe.Bisimilar.restrict; GSLT/Contexts/Traces.lean: "
        ++ "Probe.Bisimilar.traceEquivalent (for every probe the comparison by traces "
        ++ "is the coarser one) / reductionProbe_traceEquivalent_iff / "
        ++ "ContextMap.traceEquivalent_push_iff_of_transitions"
      instanceWitness := "GSLT/LanguageDef/Contexts/Controls/Branching.lean: "
        ++ "early_late_traceEquivalent", negativeControl := "GSLT/LanguageDef/Contexts/Controls/Branching.lean: "
        ++ "traceEquivalent_not_bisimilar (two terms with the same traces that are "
        ++ "not bisimilar)"
      audited := true
      standing := .constructedHere }
  , { chapter := 10, citation := "Remark 10.4"
      statement :=
        "A note on complexity: equivalence of regular languages is "
        ++ "PSPACE-complete and the corresponding bisimulation problem is "
        ++ "polynomial; equivalence of context-free languages is undecidable and "
        ++ "the corresponding bisimulation problem is tractable."
      sourceProves := false
      construction := "", provedTheorem := "", instanceWitness := ""
      negativeControl := ""
      audited := true
      standing := .openHere }
  ]

/-! ## Chapter 19

The chapter the construction is centred on states almost nothing numbered: one
proposition and six remarks, no definitions, no theorems, and no algorithm
environment.  Its algorithm therefore has to be read off the prose, and the four
generated rule forms are entered below under the section that introduces them.
-/

/-- Chapter 19's rows. -/
def chapter19 : List Obligation :=
  [ { chapter := 19
      citation := "Proposition 19.1"
      statement :=
        "There is a forgetful functor U from the category of theories equipped "
        ++ "with the modal, structural and propositional layers to the category "
        ++ "of theories in classifying form, a left adjoint F freely adjoining "
        ++ "those layers, and the induced endofunctor K = U after F is a monad: "
        ++ "for each theory T, K(T) is the underlying theory of its free "
        ++ "extension by generated type formers."
      sourceProves := false
      construction := "GSLT/Core/RelativeClosedBareLogicalAdjunction.lean: "
        ++ "freeObject, freeMap and free generate named native predicates, "
        ++ "positioned-rule modalities and structural constructor images, "
        ++ "with finite conjunction, implication and both quantifiers at "
        ++ "every generated arrow. The source is independently supplied "
        ++ "closed program/reduction theories; maps are taken modulo "
        ++ "compatible whole-context isomorphisms. This is the explicit "
        ++ "connective profile of the free-extension statement, not an "
        ++ "unqualified extension by every possible logical capability. "
        ++ "NativeTypes/Semantics/Presheaf/AuthoredProgramReduction.lean "
        ++ "constructs the admitted binding generator's actual carrier and "
        ++ "receipt-image source theory. AuthoredNativeFreeExtensionSyntax.lean, "
        ++ "AuthoredNativeFreeExtensionReadout.lean and "
        ++ "AuthoredNativeFreeExtensionFibres.lean connect its generated "
        ++ "constructor graphs and dependent response families to the "
        ++ "existing qualified relative fragment. The full dependent "
        ++ "contextual native grammar retains its separate classification"
      provedTheorem := "GSLT/Core/RelativeClosedBareLogicalAdjunction.lean: "
        ++ "homEquiv, homEquiv_natural_left_symm, homEquiv_natural_right "
        ++ "and adjunction earn the natural hom correspondence and actual "
        ++ "Mathlib free/forgetful adjunction, with left_triangle and "
        ++ "right_triangle. RelativeClosedBareLogicalMonad.lean: "
        ++ "Construction.monad is the induced monad; right_unit, left_unit "
        ++ "and associativity give its laws. complete_program_readout, "
        ++ "complete_event_readout, folds_universal, folds_existential "
        ++ "and folds_complete_implication retain the full operations "
        ++ "under multiplication. AuthoredProgramReductionReceipts.lean: "
        ++ "image_iff_scoped_receipt and image_recovers_scoped_firing "
        ++ "compare with the original scoped semantics and specified target. "
        ++ "AuthoredNativeFreeExtensionSyntax.lean: reading_complete and "
        ++ "reading_composition retain independent raw interpretation and "
        ++ "composition. AuthoredNativeFreeExtensionFibres.lean: "
        ++ "structuralFibreEquiv, responseWitnessEquiv, "
        ++ "generated_structural_type_read, generated_response_type_read, "
        ++ "generated_substituted_response_read and response_baseChange "
        ++ "preserve the generated graph/response witnesses and the "
        ++ "actual substituted continuation"
      instanceWitness := "GSLT/Core/RelativeClosedBareLogicalControls.lean: "
        ++ "actual_zero_pair_source, actual_zero_pair_reduct, "
        ++ "complete_selected_firing and entire_constructor_function "
        ++ "recover an independently renamed successor rewrite, its "
        ++ "authored firing and complete constructor functions; "
        ++ "actual_quantifier_created_arrow_folds checks both quantifiers "
        ++ "over an arrow generated by the first extension"
      negativeControl := "GSLT/Core/RelativeClosedBareLogicalControls.lean: "
        ++ "incorrect_unrenamed_reduct_rejected prevents omission of the "
        ++ "program comparison. RelativeClosedConjunctiveAdjunctionControls.lean: "
        ++ "actual_monad_is_not_the_identity_up_to_natural_isomorphism "
        ++ "separates the free conjunctive extension from an identity "
        ++ "construction. Framework/TypeFormerExtension.lean: "
        ++ "rhoTwice_rejected remains a counterexample to obtaining "
        ++ "this monad from unchecked declaration growth alone"
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Section 19.3, authored rewrite and redex generation"
      statement := "Generate each authored rewrite at every one-hole redex position, retaining the focus, "
        ++ "rely variables, matched variables and declaration origin. Every independently typed "
        ++ "occurrence has a finite checked annotation; executable schemas additionally require "
        ++ "the original declaration's operational admission."
      sourceProves := false
      construction := "NativeTypes/Generation/Occurrences.lean: generate and decompositions enumerate raw syntax, "
        ++ "including binders, substitution nodes and collection tails. Mettapedia/OSLF/NativeTypes/Generation/TypedOccurrences.lean "
        ++ "supplies the separate typed schematic derivative. Mettapedia/OSLF/NativeTypes/Generation/Core.lean compiles the "
        ++ "actual selected declarations. Mettapedia/OSLF/NativeTypes/Generation/Annotated/Sources.lean checks complete "
        ++ "source and descent annotations, including arbitrary arrow and substitution types, "
        ++ "before Mettapedia/OSLF/NativeTypes/Generation/Annotated/Schemas.lean finds the actual operational declaration."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate_spec, generated_source_reconstructed, generated_focus_readback, "
        ++ "rely_names_spec and hidden_names_spec; Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate_spec and "
        ++ "Mettapedia.OSLF.NativeTypes.Modal.CatalogueCoverage.schemas_program_typedAt_complete. The latter covers "
        ++ "independently TypedAt occurrences at every declared program carrier for computationally "
        ++ "classifying, substitution-free sources; it derives carrier-list membership and context "
        ++ "permission. The broader checked route is Mettapedia.OSLF.NativeTypes.Modal.Annotations.annotation_exists_iff, "
        ++ "descent_annotation_exists_iff and Mettapedia.OSLF.NativeTypes.Generation.every_generated_typed_site_has_annotation: "
        ++ "every independently TypedAt occurrence is checkable, without a finite carrier restriction. "
        ++ "annotated_source_engine_complete derives schema admission from actual plan membership."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Instances.Rho.SchemaConsumer.original_rest_source_is_typed, "
        ++ "computed_typed_continuation_preserves_tail and same_generator_types_and_executes_comm "
        ++ "retain the unchanged REST-bearing COMM. Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer covers independently "
        ++ "licensed binder occurrences."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls exposes genuinely typed arrow roots outside "
        ++ "automatic carrier inference. Explicit annotations address that inference boundary; "
        ++ "missing operational declarations still return unresolvedOperationalDeclaration, "
        ++ "rather than a certified empty schema catalogue."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Section 19.4, M-FORM"
      statement := "For a rewrite rule and an admissible redex position, form the modality from typed rely "
        ++ "codes and an assignment-indexed continuation at the computed output sort, before "
        ++ "requiring any inhabitant."
      sourceProves := false
      construction := "NativeTypes/Generation/ModalCodes.lean: Generated.modalFormer? consumes the actual "
        ++ "catalogue, original declaration and computed slot parameters. "
        ++ "Mettapedia/OSLF/NativeTypes/SortProfiles/Source/ModalCodes.lean retains classified rely-code syntax and the "
        ++ "complete continuation family. Generated.annotatedModalFormer? uses the same computed "
        ++ "slots and gates for computationally checked annotated schemas."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Generation.generated_m_form and generated_modal_same_output_sort form every "
        ++ "catalogue member under accepted equation admission and typed input codes. "
        ++ "Mettapedia.OSLF.NativeTypes.SortProfiles.Source carrier_read_exact, kind_read_exact and universes_disjoint provide "
        ++ "independent carrier/universe judgments; generated_equation_modal_formation_complete "
        ++ "returns syntax-bearing outputs, and equation_modal_code_native_comparison compares them "
        ++ "with the actual semantic former. annotated_modal_formation_complete and "
        ++ "annotated_modal_result_slot and generated_annotated_m_form cover every checked "
        ++ "annotation instance, with computed coordinate completeness. "
        ++ "Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes interprets formed outputs in the chosen program-sort "
        ++ "subobject. Joint E/R compilation is a separate stronger contract. "
        ++ "NativeTypes/Generation/AuthoredNativeClassifying.lean: generated_family_header "
        ++ "and generated_operation_header identify actual free contextual grammar headers. "
        ++ "AuthoredNativeSemantics.checked_semantic_sound interprets accepted finite certificates "
        ++ "in the computed original binding/event presheaf model for the admitted equation-free profile."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.computed_continuation_schema and "
        ++ "Mettapedia.OSLF.NativeTypes.Instances.Rho.SchemaConsumer.continuation_parameters_are_computed recover the actual "
        ++ "continuation carrier and input coordinates from generated catalogues."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Generation.generated_schema_rejected refuses a missing or different schema "
        ++ "fingerprint; Mettapedia.OSLF.NativeTypes.SortProfiles.Source.wrong_universe_is_refused separates well-carried "
        ++ "expressions from malformed universe formation."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Section 19.4, M-INTRO"
      statement := "The generated introduction law types the authored focus when every admitted rely "
        ++ "instance has the specified reduct in the continuation after substitution. Conditional "
        ++ "rules retain their actual premise witnesses."
      sourceProves := false
      construction := "NativeTypes/Modal/SourceIntroduction.lean computes scoped matcher answers and base "
        ++ "introductions. Mettapedia/OSLF/NativeTypes/Modal/Rules.lean constructs the actual primitive firing receipt "
        ++ "and the dependent response family."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction.baseIntroductions_spec and m_intro_computed, together "
        ++ "with Mettapedia.OSLF.NativeTypes.Modal.Rules.m_intro. The introduction premises are independently specified "
        ++ "matching, scoped assignments, ordered premise derivations, source/target typing and "
        ++ "continuation witnesses; no assumed modal inhabitant or supplied step oracle occurs. "
        ++ "Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction.introduce computes the same construction inside "
        ++ "the chosen sort model, using independently stated constructor closure and primitive "
        ++ "equation interpretation; equation_sort_transport derives conversion closure. "
        ++ "NativeTypes/Generation/AuthoredNativeEventCoverage.lean: every_receipt_has_native_event "
        ++ "constructs the actual installed native event from every valid original receipt; "
        ++ "NativeBindingGeneratedFrameCoverage.checker_covers_every_firing earns every generated "
        ++ "nonroot frame from scoped matching and typing under computed tree/header admission. "
        ++ "AuthoredNativeReceiptChecking.checkReceiptFrame?_complete and "
        ++ "checkReceiptFrame?_independent_exact join the executable authored source decoder to "
        ++ "the generated frame checker for every actual receipt, without a supplied source term."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.all_proper_bodies_execute and all_proper_bodies_inhabit hold "
        ++ "for every independently admitted function body and ambient context; "
        ++ "Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding checks actual continuation substitution. "
        ++ "Mettapedia.OSLF.NativeTypes.Semantics.Sorted.LambdaControls discharges the model conditions for disjoint "
        ++ "proper variable and compound-term domains, with actual lambda reduction."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Modal.ConditionalControls proves that a typed reduct alone cannot discharge a "
        ++ "missing relation-query premise. Mettapedia.OSLF.NativeTypes.Modal.HiddenAssignments.no_rely_only_contractum "
        ++ "shows why matched variables must remain in the continuation assignment."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Section 19.4, M-STEP"
      statement := "For every inhabitant of the generated modality, filling its context with rely values "
        ++ "steps to the specified authored right-hand-side instance."
      sourceProves := false
      construction := "The literal rule is incompatible with the existential-successor interpretation in Stay "
        ++ "and Wells Section 7. NativeTypes/Modal/Rules.lean supplies the corrected "
        ++ "specified-contractum interpretation, retaining matched variables, equation conversions "
        ++ "and an actual firing receipt."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.literal_m_step_refuted and "
        ++ "existential_comparison_is_strict kernel-refute the literal existential interpretation. "
        ++ "The corrected law is Mettapedia.OSLF.NativeTypes.Modal.Rules.m_step; "
        ++ "Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.elimination_contract retains the exact authored RHS and "
        ++ "all conversions, not an arbitrary successor. "
        ++ "NativeTypes/Generation/AuthoredBindingNativeReadout.target_readout reads the exact "
        ++ "original receipt target in the computed binding model. AuthoredNativeEventCoverage "
        ++ "nativeEventValue_decode and nativeEventValue_read retain the full frame and ordered payload. "
        ++ "AuthoredNativeReceiptChecking.checkReceiptFrame?_target and "
        ++ "checkReceiptFrame?_native_read compare each computationally checked frame with the "
        ++ "actual model's exact target and complete native receipt readout."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Modal.Counterexamples uses Alpha = Beta, Beta -> Done and Other -> Alpha with an "
        ++ "equation-invariant continuation. Other inhabits the existential modality but cannot step "
        ++ "to Done. Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding supplies a binder-dependent authored RHS consumer."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.corrected_modality_rejects_other; "
        ++ "Mettapedia.OSLF.NativeTypes.Modal.ContextControls shows that focus conversion cannot be lifted through an "
        ++ "unlicensed context."
      audited := true
      standing := .refutedHere }
  , { chapter := 19
      citation := "Section 19.4, M-ELIM"
      statement := "The specified authored right-hand-side instance inhabits the continuation after the rely "
        ++ "substitution."
      sourceProves := false
      construction := "The existential-successor meaning does not imply membership of the specified RHS. The "
        ++ "corrected dependent modality retains the complete matched/rely assignment and a "
        ++ "continuation certificate at that exact RHS."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.literal_m_elim_refuted kernel-refutes the literal "
        ++ "existential interpretation. Mettapedia.OSLF.NativeTypes.Modal.Rules.m_elim proves the specified-contractum "
        ++ "correction; Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.elimination_contract and "
        ++ "direct_elimination_agrees compare its native witness and readout. "
        ++ "Mettapedia.OSLF.NativeTypes.Modal.Possibility.possibility_iff_existential_step supplies the separate "
        ++ "empty-context possibility law under equation-invariant support. "
        ++ "NativeTypes/Generation/AuthoredBindingNativeReadout.response_type_read and "
        ++ "substituted_response_type_read compare the actual native continuation with its "
        ++ "specified target, before and after arbitrary native dependent substitution."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Modal.SourceProfile.all_proper_bodies_inhabit and the rho authored substitution "
        ++ "consumer retain actual certificates, rather than only target support."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Modal.HiddenAssignments proves that equal rely values do not determine a "
        ++ "contractum when matched variables differ; elimination_preserves_origins retains receipt "
        ++ "origins."
      audited := true
      standing := .refutedHere }
  , { chapter := 19
      citation := "Section 19.5, structural and propositional generation"
      statement := "Each constructor freely induces a structural former whose inhabitants are exactly terms "
        ++ "with that representative root; binary constructors induce positional or "
        ++ "associative-commutative splits, and connectives are supplied at the selected logical "
        ++ "strength."
      sourceProves := false
      construction := "The representative-root assertion is false modulo root-changing equations. The "
        ++ "correction classifies the typed constructor image up to the authored equation relation. "
        ++ "NativeTypes/Structural/Formers.lean, Mettapedia/OSLF/NativeTypes/Structural/Semantics.lean and "
        ++ "Mettapedia/OSLF/NativeTypes/Structural/Logic.lean implement that interpretation; actual declarations "
        ++ "generate the formers."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Structural.Controls.authored_equation_changes_representative_root refutes "
        ++ "the literal root assertion. The correction is structural_former_exact and "
        ++ "structural_equation_invariant; structural_free_root recovers the free case. "
        ++ "authored_ac_split_commutative and authored_ac_split_associative derive the split laws "
        ++ "from detected authored equations; Mettapedia.OSLF.NativeTypes.SortProfiles.Source.constructor_meaning_exact "
        ++ "compares actual recursive native code syntax with the generated structural former. "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.checkFormation_exact computes independent carrier/universe "
        ++ "formation. Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.readout_exact, top_exact, "
        ++ "complement_exact and generated_readout_transport interpret and transport generated "
        ++ "operations inside the chosen actual sort subobject. "
        ++ "NativeTypes/Generation/CurriedNativeStructuralMeaning.structuralTermFibreEquiv "
        ++ "identifies graph inhabitants with original constructor terms across every ambient "
        ++ "binding context under the earned source-model admission."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Structural.Controls.binder_root_executes and detected_ac_separating_laws; "
        ++ "Mettapedia.OSLF.NativeTypes.Structural.RhoSpatial exercises rho bare-bag structure through actual "
        ++ "declarations. Mettapedia.OSLF.NativeTypes.Structural.DecompositionControls executes free and rho splits "
        ++ "through the generated checker. Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls separates actual "
        ++ "program-sort complements from carrier-wide complements."
      negativeControl := "free_split_is_positional rejects the reversed free split; absent_ac_law_is_not_detected "
        ++ "does not infer commutativity from a unit equation; binder_representation_rejected "
        ++ "rejects a wrongly represented abstraction."
      audited := true
      standing := .refutedHere }
  , { chapter := 19
      citation := "Section 19.6, sort slots and the equational center"
      statement := "Each modal former has one slot per rely input and one output slot. Equations and rewrite "
        ++ "laws restrict the generated cube to stable assignments in the chosen sort interpretation. "
        ++ "The precise local interpretation here is partial typed formation; full operation-table "
        ++ "models have a separate center and are not identified with local profiles."
      sourceProves := false
      construction := "NativeTypes/SortProfiles/Slots.lean computes local coordinates from generated sites. "
        ++ "Mettapedia/OSLF/NativeTypes/SortProfiles/EquationalCenter.lean computes full finite operation-table models. "
        ++ "Mettapedia/OSLF/NativeTypes/SortProfiles/Coherence/StableSource.lean checks formation-preserving local profiles against "
        ++ "original authored laws. Mettapedia/OSLF/NativeTypes/Generation/CertifiedCenter.lean enumerates the actual "
        ++ "generator's joint equation/rewrite center and retains accepted, rejected and unresolved "
        ++ "vertices. Its independent source contract makes support conditions structural and "
        ++ "checks every typed formation judgment. Mettapedia.OSLF.NativeTypes.Generation.GuardedCenter additionally reads "
        ++ "actual finite nullary-query guards; Mettapedia.OSLF.NativeTypes.Generation.BindingCenter checks original "
        ++ "binding laws in finite complete-function models with source-derived carrier candidates."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.mem_center_iff and "
        ++ "selected_source_stability_original prove exact computed membership against the original "
        ++ "selected declarations. center_intersection separates equation and directed stability; "
        ++ "center_rename proves source-variable renaming invariance, and partial_operation_graph "
        ++ "specifies the local slots' actual partial interpretation. "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.member_modal_equation_universe and "
        ++ "member_modal_directed_universe preserve every computed rely and substituted-continuation "
        ++ "coordinate under the selected code-law relations, without asserting semantic-set equality. "
        ++ "Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.mem_center_iff separately proves the full-table contract. "
        ++ "Mettapedia.OSLF.NativeTypes.SortProfiles.Source "
        ++ "generated_native_equation_universe and generated_native_directed_universe require "
        ++ "jointAdmission = some true and transfer laws to constructor-code universe judgments. "
        ++ "They do not by themselves supply a chosen native Pattern model. Renaming invariance is "
        ++ "stable_profile_center_rename. Mettapedia.OSLF.NativeTypes.Generation.BindingCenter.check_law_exact and "
        ++ "generated_binding_equations_exact compare executable checks to independent intrinsic "
        ++ "binding valuations, keeping this model center distinct from kind formation. "
        ++ "Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.CenterStability.accepted_equation_descendants derives full contextual "
        ++ "binding-equation congruence from complete-function satisfaction; "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.generated_binding_consequences_sound joins actual selected law streams."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenterControls.proper_nonempty_actual_generated_center "
        ++ "derives a proper joint center from actual authored equation and rewrite streams. "
        ++ "nonidentity_code_law_preserves_generated_universe checks an actual code-law instance. "
        ++ "Mettapedia.OSLF.NativeTypes.SortProfiles.Source has disjoint code universes and "
        ++ "syntax-bearing semantic outputs. Mettapedia.OSLF.NativeTypes.Generation.BindingEquationControls checks the entire "
        ++ "original scoped equation stream and refutes an incorrect binder law at every vertex."
      negativeControl := "guarded_vertex_retained_as_unresolved and guarded_vertex_is_not_refuted "
        ++ "preserve unresolved uniform laws. lawful_source_table_is_not_a_constant_output_profile "
        ++ "distinguishes interpretations rather than refuting the source paragraph. "
        ++ "no_equations_accepts_equation_check_but_rejects_joint_check separates E-only admission "
        ++ "from R preservation. The guarded route admits finite nullary-query guards, while "
        ++ "Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardDescent shows that general argument-query truth cannot be inferred "
        ++ "from the sort readout. Non-finite binding carriers and unsupported premise forms remain "
        ++ "unresolved; these boundaries do not refute a richer arbitrary-language construction."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Section 19.7, rho continuation cube and channel face"
      statement := "The no-tail arity-one COMM continuation has two rely inputs and one output, seven "
        ++ "nonempty lifting directions, and the four-corner Barendregt square at the fixed channel "
        ++ "slot."
      sourceProves := false
      construction := "NativeTypes/Instances/Rho/CommunicationGeometry.lean computes the continuation site, rely inputs and "
        ++ "carrier slots from the authored no-tail rule through Mettapedia.OSLF.NativeTypes.Generation. "
        ++ "Mettapedia/OSLF/NativeTypes/SortProfiles/Slots.lean derives axes and the fixed-first-coordinate equivalence."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.actual_family_inputs, actual_channel_is_first, "
        ++ "computed_three_slots, seven_generated_axes, channelSquare_four_corners and "
        ++ "channelSquareEquiv. These identify the actual channel coordinate, rather than only "
        ++ "matching a face cardinality."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer executes no-tail COMM using the same generator and retains the "
        ++ "authored continuation, channel and payload readout."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.original_rest_rule_has_an_extra_input and "
        ++ "Mettapedia.OSLF.NativeTypes.Instances.Rho.SchemaConsumer.rest_schema_has_one_extra_slot distinguish the original "
        ++ "REST-bearing rule. Its actual rely names yield four slots, not the chapter example's "
        ++ "three."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Remark 19.1"
      statement := "Generating a type system alone does not establish adequacy for its operational "
        ++ "observations."
      sourceProves := true
      construction := "NativeTypes/Generation/ObservationBoundary.lean interprets all independently formed formulas of "
        ++ "a selected conjunctive fragment, beside the independently generated GSLT steps."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Generation.ObservationBoundary.generated_fragment_need_not_be_adequate: every formed question "
        ++ "of that fragment agrees at two actual typed states, while one state has an outgoing step "
        ++ "and the other has none."
      instanceWitness := "The Alpha/Beta/Other/Done language has a real equation and actual generated execution. "
        ++ "The theorem quantifies over independent formula formation, not a hand-written question "
        ++ "list."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Structural.ObservationControls supplies a separately indexed instrument extension that "
        ++ "distinguishes shapes; adequacy is not silently transferred from that richer observation "
        ++ "index."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Remark 19.2"
      statement := "Adequacy is relative to a chosen observation index."
      sourceProves := true
      construction := "NativeTypes/Structural/ObservationControls.lean compares the actual generated reduction "
        ++ "system, structural questions and the authored ask/get instrument extension."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Structural.ObservationControls.Instrument.observer_index_strictly_changes_equivalence and "
        ++ "negation_free_generated_adequacy: bare reductions equate two inert constructors, while "
        ++ "admitted structural questions and instrument steps separate them. The instrument "
        ++ "adequacy proof uses the independently defined extended relation."
      instanceWitness := "Both structural questions execute through the actual generated checker; an actual ask "
        ++ "step witnesses the changed observation index."
      negativeControl := "The checked bare-reduction bisimulation cannot be reused as an instrument bisimulation. "
        ++ "The formula readout theorem ranges over the complete formed fragment."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Remark 19.3"
      statement := "An interaction cut privileges a family of positions; the generator is obtained by "
        ++ "considering every position rather than privileging a family."
      sourceProves := true
      construction := "NativeTypes/Generation/Occurrences.lean derives one-hole decompositions from syntax. Typed "
        ++ "schematic positions and the operational site-permission policy remain separate "
        ++ "constructions."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate_spec and Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate_spec; "
        ++ "Mettapedia.OSLF.NativeTypes.Modal.CatalogueCoverage.schemas_program_typedAt_complete. The raw theorem covers "
        ++ "every authored occurrence. The typed theorem states and derives the precise "
        ++ "classifying-program admission and preserves binder contexts and collection tails. "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.every_generated_typed_site_has_annotation covers the broader "
        ++ "checked instance family, including explicit substitutions and arbitrary arrows."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Instances.Rho.SchemaConsumer computed continuation typing and Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer "
        ++ "binder descent recover non-root positions through the generator."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Modal.ContextControls exhibits a raw surrounding context whose operational "
        ++ "permissions do not license conversion; raw occurrence generation is not an assertion "
        ++ "that every context is a reduction context."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Remark 19.4"
      statement := "The specification supplies the categorical/connective fragment; finite limits give a "
        ++ "conjunctive fragment, and refusal to elaborate an unavailable connective is distinct "
        ++ "from falsehood."
      sourceProves := true
      construction := "NativeTypes/Structural/Logic.lean takes a chosen connective-strength fragment and "
        ++ "independently specifies formula formation. Mettapedia/OSLF/NativeTypes/Generation/Core.lean consumes that "
        ++ "fragment. This does not infer categorical strength merely from an enum or from raw "
        ++ "LanguageDef syntax."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Structural.elaborate_success_iff and unsupported_connective_refused; "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.Controls.connective_refusal_is_not_false. Accepted formulas have the "
        ++ "supplied fragment's independent formation derivation. Mettapedia.OSLF.NativeTypes.Generation.ReadoutSound "
        ++ "proves the actual positive and negative semantic readouts. "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.generated_propositional_formation_complete and "
        ++ "generated_propositional_formation_sound additionally retain actual expression syntax, "
        ++ "input carriers and universe coordinates; generated_propositional_readout gives their "
        ++ "native predicate meaning. Sort-relative interpretation is separate from code-kind "
        ++ "classification and assumes a chosen carrier-bounded classifying model."
      instanceWitness := "The same generated F/G language refuses negation in the finite-limit fragment and "
        ++ "decides bottom as false in the supplied Heyting fragment. "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls.actual_star_top_readout and actual_box_top_readout "
        ++ "exercise distinct nonempty sort subobjects; bottom_forms_but_is_uninhabited keeps "
        ++ "formation refusal separate from falsehood."
      negativeControl := "Mettapedia.OSLF.NativeTypes.Structural.Controls.unsupported_true_formula_refused proves a true "
        ++ "property may be refused for its vocabulary; admitted_false_formula proves an admitted "
        ++ "false property still elaborates. Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls: "
        ++ "wrong_universe_is_formation_refusal and carrier_only_complement_would_admit_box_term "
        ++ "separate malformed code kinds from an overly broad complement interpretation."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Remark 19.5"
      statement := "Without built-in equations the E-center is the whole raw cube; the lambda example does "
        ++ "not require an equational restriction."
      sourceProves := true
      construction := "NativeTypes/SortProfiles/EquationalCenter.lean, Mettapedia/OSLF/NativeTypes/SortProfiles/Coherence/StableSource.lean and "
        ++ "Mettapedia/OSLF/NativeTypes/Generation/EquationAdmission.lean keep the empty equation system independent of the "
        ++ "directed-rule system."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.no_equations_center; "
        ++ "Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.no_authored_equations_stable_whole_cube; "
        ++ "Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.no_equations_whole_cube; "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.no_authored_equations_generate_every_vertex. These are general "
        ++ "empty-equation theorems, not lambda ground checks."
      instanceWitness := "Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer executes the authored beta rule and derives its generated schema "
        ++ "geometry; Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry separately identifies the channel-fixed square."
      negativeControl := "Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.no_equations_do_not_force_rewrite_sort_equality prevents "
        ++ "promoting the E-center theorem to unconditional directed-law equality."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Section 19.9, independent dials and budgeted checking"
      statement := "Language fragment, connective fragment and cube vertex independently control one "
        ++ "generator; a checking budget prevents runaway search without turning exhaustion into "
        ++ "falsehood."
      sourceProves := false
      construction := "NativeTypes/Generation/Core.lean implements generate with the three inputs, actual "
        ++ "operational compilation and generated catalogues. Mettapedia/OSLF/NativeTypes/Generation/Checking.lean calls "
        ++ "the certified frontier engine; the structural/propositional readouts retain its state. "
        ++ "Mettapedia/OSLF/NativeTypes/Generation/ModalChecking.lean checks specified-contractum instances with actual "
        ++ "source execution and target conversion paths. Mettapedia/OSLF/NativeTypes/Generation/Annotated/Checking.lean "
        ++ "extends that same engine route to computationally checked annotations."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Generation.Controls language_selection_changes_the_actual_signature, "
        ++ "language_rule_selection_changes_the_actual_executor, "
        ++ "changing_connectives_preserves_execution_input and "
        ++ "cube_changes_actual_produced_code_sorts. "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.BudgetControls.funded_target_persists, "
        ++ "resumed_query_preserves_actual_state, unknown_does_not_certify_absence and "
        ++ "every_sorted_object_has_complete_generated_execution derive the budget/completeness laws "
        ++ "from actual paths and finite coverage. Universal rely membership is not inferred from "
        ++ "one checked assignment. Mettapedia.OSLF.NativeTypes.Generation.generated_annotated_instance_positive_sound, "
        ++ "generated_annotated_instance_negative_sound and generated_annotated_response_native_origin "
        ++ "extend the actual engine and retained receipt laws to checked annotation instances. "
        ++ "NativeTypes/Generation/AuthoredPipeline.Installed.check_exact characterizes complete "
        ++ "finite native certificates with vocabulary admission. AuthoredNativeSearch.Prepared "
        ++ "resume_add, stable, sound and discovery prove retained fair search and an explicit "
        ++ "wire-size discovery bound for every admitted certificate. Exhaustion remains unknown; "
        ++ "finite derivability is not identified with unrestricted semantic truth."
      instanceWitness := "The same generator runs rho COMM, nested lambda beta reduction and the authored "
        ++ "proper-center theory. Budget controls pause before discovering an actual firing and "
        ++ "resume to its retained receipt."
      negativeControl := "The zero-budget empty state is unknown despite a proved outgoing step. Disabling rules "
        ++ "changes execution, changing connective strength changes elaboration, and changing a cube "
        ++ "vertex changes actual code sorts."
      audited := true
      standing := .provedHere }
  , { chapter := 19
      citation := "Remark 19.6"
      statement := "Adequacy requires negation; choosing a finitely checkable fragment generally leaves the "
        ++ "adequate region."
      sourceProves := true
      construction := "The universal necessity claim is false. NativeTypes/Structural/ObservationControls.lean "
        ++ "supplies a nontrivial finite instrument language with adequate negation-free generated "
        ++ "questions and checked finite readouts. The source's typical trade-off remains a "
        ++ "qualified observation, not an unconditional impossibility theorem."
      provedTheorem := "Mettapedia.OSLF.NativeTypes.Structural.ObservationControls.Instrument.universal_negation_necessity_refuted, "
        ++ "negation_free_generated_adequacy and generated_check_conclusive. "
        ++ "Mettapedia.OSLF.NativeTypes.Generation.ObservationBoundary.generated_fragment_need_not_be_adequate separately shows that "
        ++ "a weaker chosen fragment can lose operational distinctions."
      instanceWitness := "The finite example has two actual constructors, genuine ask/get observations and "
        ++ "independently formed formulas. Its complete finite checker is proved over every closed "
        ++ "term of the language."
      negativeControl := "Bare reductions alone do not distinguish the constructors; instrument extension does. "
        ++ "This prevents changing the observation index silently when claiming adequacy."
      audited := true
      standing := .refutedHere }
  ]


/-! ## Chapter 16 -/

/-- Chapter 16's rows: contexts, context-decorated HML, adequacy, the metric. -/
def chapter16 : List Obligation :=
  [ { chapter := 16, citation := "Definition 16.1"
      statement := "A context for a theory is a term with a distinguished hole; "
        ++ "it is minimal for a term and a rule when it enables a reduction and "
        ++ "no proper sub-context does."
      sourceProves := true
      construction := "Framework/RedexPosition.lean: Position / positions / "
        ++ "subtermAt / plug; Syntax/RhoScopedParallelContexts.lean: the "
        ++ "category of original rho source-equation process classes, at "
        ++ "every ambient scope, has relative pushouts through its independently "
        ++ "constructed typed prime-inventory equivalence"
      provedTheorem := "Framework/RedexPosition.lean: position enumeration "
        ++ "soundness and completeness for the binder-free fragment, not a "
        ++ "minimal enabling-context universal property; "
        ++ "Syntax/RhoScopedParallelReactiveSystem.lean: least_transition / "
        ++ "firing_normal_form / actIPO_iff_computed earn the universal least "
        ++ "parallel label and residue for every process and admitted original "
        ++ "scoped root. RhoScopedParallelSourceAdequacy.lean: "
        ++ "parallelStepModE_iff_actIPO_identity compares the independently "
        ++ "authored closed COMM/Drop/ParCong rules in both directions"
      instanceWitness := "Languages/ProcessCalculi/RhoCalculus/PlatformLabels.lean; "
        ++ "Syntax/RhoScopedParallelReactiveControls.lean: actual_comm_label / "
        ++ "actual_comm_transition / open_comm_retains_caller"
      negativeControl := "Syntax/ContextualSplitting.lean: shape_does_not_locate; "
        ++ "Syntax/RhoScopedParallelReactiveControls.lean: "
        ++ "padded_same_root_rejected / identification_changes_minimality. "
        ++ "The latter is an original process-class bound, not an authored "
        ++ "COMM occurrence; operational events themselves commute with substitution"
      audited := true
      standing := .constructedHere }
  , { chapter := 16, citation := "Remark 16.1"
      statement := "Minimality is a universal property, and the ambient object "
        ++ "goes."
      sourceProves := true
      construction := "GSLT/Logic/BagRelativePushout.lean and "
        ++ "GSLT/Logic/RedexRelativeEnabling.lean: the minimality the labels "
        ++ "need is built as a relative pushout, which is the universal "
        ++ "property itself rather than a stand-in for it"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 16, citation := "Remark 16.2"
      statement := "Labels carry processes and are matched up to bisimilarity."
      sourceProves := true
      construction := "GSLT/Logic/HigherOrderBisimulation.lean: Vocabulary / "
        ++ "Label.Relates / System.progressHom / System.Bisimilar. Skeletons "
        ++ "agree literally; payloads at corresponding declared interfaces "
        ++ "use the same greatest-fixed-point relation as successors. The "
        ++ "actual reflective label decomposition, its binding/substitution "
        ++ "laws and its contextual congruence are not yet instantiated"
      provedTheorem := "HigherOrderBisimulation.System.progress_mono / "
        ++ "bisimilar_unfold / bisimilar_refl / bisimilar_symm / bisimilar_trans / "
        ++ "quotientStep_from_class_iff / bisimilar_classLabel_iff; the latter "
        ++ "recovers ordinary literal-label bisimulation over behavioral label "
        ++ "classes, not an executable class-computation algorithm. "
        ++ "ipo_bisimilar_iff recovers the existing "
        ++ "literal IPO relation at empty payload families, not higher-order "
        ++ "congruence for the reflective calculus"
      instanceWitness := "HigherOrderBisimulation.PayloadControls: "
        ++ "nested_payloads_are_bisimilar; TypedPayloadControls: "
        ++ "false_computes_zero / true_computes_one, with Bool and Nat payload "
        ++ "interfaces and two positional slots"
      negativeControl := "HigherOrderBisimulation.PayloadControls: "
        ++ "literal_matching_is_stricter / different_channels_are_distinguished / "
        ++ "observed_payloads_are_distinguished / class_step_needs_label_class; "
        ++ "TypedPayloadControls: wrong_input_is_rejected / "
        ++ "constant_result_is_rejected / successor_classes_are_distinct"
      audited := true
      standing := .constructedHere }
  , { chapter := 16, citation := "Remark 16.3"
      statement := "The congruence is relative to a class of contexts."
      sourceProves := true
      construction := "Languages/ProcessCalculi/RhoCalculus/AdmissibleContexts.lean; "
        ++ "Logic/DerivationClosure.lean: actual least finite rule closure; "
        ++ "GSLT/Logic/HigherOrderContextClosure.lean: respectful closure and "
        ++ "checked up-to certificates for the original interface-indexed "
        ++ "higher-order progression, subject to local constructor replay. "
        ++ "GSLT/Logic/RedexRelativeCongruence.lean derives its literal-label "
        ++ "context rule by actual RPO decomposition, residual and pasting, "
        ++ "then uses this same finite closure for congruence. "
        ++ "The reflective language's own label/binding and residual "
        ++ "correspondence are not discharged by this generic theorem. "
        ++ "Syntax/RhoScopedParallelReactiveSystem.lean now derives "
        ++ "context_congruence for original rho classes and every parallel "
        ++ "partner from its earned scoped RPOs; this uses literal IPO labels, "
        ++ "not behavioral payload matching or every reflective observer"
      provedTheorem := "FinitaryClosure.respectful / close_gfp_le / "
        ++ "coinduction_up_to; HigherOrderBisimulation.System."
        ++ "finite_closure_bisimilar / certificate_bisimilar; "
        ++ "ContextClosureControls.locally_respectful proves the local "
        ++ "obligation for actual send transitions; "
        ++ "RedexRelativeCongruence.contextRules_locally_respectful proves it "
        ++ "for literal IPO labels under relative-pushout existence, "
        ++ "not for every higher-order signature"
      instanceWitness := "Languages/ProcessCalculi/RhoCalculus/"
        ++ "PlatformLabels.lean: platform_congruence; "
        ++ "HigherOrderContextClosureControls.nested_certificate_bisimilar "
        ++ "consumes a retained three-node certificate with nested payloads"
      negativeControl := "Languages/ProcessCalculi/RhoCalculus/"
        ++ "AdmissibleContexts.lean: quoting_context_separates; "
        ++ "ContextClosureControls: wrong_channel_rejected / "
        ++ "missing_child_rejected / wrong_child_rejected / "
        ++ "unchecked_constructor_is_not_respectful"
      audited := true
      standing := .constructedHere }
  , { chapter := 16, citation := "Definition 16.2"
      statement := "The formulae of context-decorated Hennessy-Milner logic, "
        ++ "whose diamond is indexed by a context label."
      sourceProves := true
      construction := "GSLT/Logic/ContextHML.lean: HMLFormula / "
        ++ "HMLFormula.satisfies; the diamond retains a MinimalContext label; "
        ++ "Syntax/RhoScopedParallelModalAdequacy.lean: Complete.Holds / "
        ++ "Finitary.Holds independently interpret actual computed missing "
        ++ "parallel partners and retained original scoped root instances"
      provedTheorem := "GSLT/Logic/HennessyMilnerDirections.lean: "
        ++ "sat_toLabeled / hmlEquiv_iff_logicallyEquivalent / "
        ++ "contextBisimilar_iff_hmlEquiv, under explicit plug compatibility "
        ++ "and contextual image-finiteness; "
        ++ "Syntax/RhoScopedParallelModalAdequacy.lean: "
        ++ "Complete.holds_iff_interface / logicallyEquivalent_iff_bisimilar "
        ++ "join source-derived original rho parallel IPO labels without a "
        ++ "branching hypothesis; Finitary.logicallyEquivalent_iff_bisimilar "
        ++ "uses an explicit finite cover of actual successors by their "
        ++ "earned IPO behavior. Wider reflective label-payload matching "
        ++ "retains its separate observation admission"
      instanceWitness := "Syntax/RhoScopedParallelModalControls.lean: "
        ++ "input_answers_outputQuery / input_receives_an_inert_result -- "
        ++ "the actual source-equation waiting input accepts its missing "
        ++ "output, including a nonconstant dynamic postcondition"
      negativeControl := "GSLT/Logic/HennessyMilnerDirections.lean: "
        ++ "ReductionBisimilarityCanary.not_hmlEquiv / "
        ++ "ReductionBisimilarityCanary.reduction_bisimilarity_insufficient; "
        ++ "Syntax/RhoScopedParallelModalControls.lean: "
        ++ "input_zero_reduction_bisimilar / input_zero_not_ipo_bisimilar / "
        ++ "false_postcondition_rejected -- an actual scoped rho separator"
      audited := true
      standing := .constructedHere }
  , { chapter := 16, citation := "Remark 16.4"
      statement := "Which logic this is adequate for: the observation index is "
        ++ "part of the claim."
      sourceProves := true
      construction := "Framework/EnumeratedAdequacy.lean"
      provedTheorem := ""
      instanceWitness := "Framework/EnumeratedAdequacy.lean: "
        ++ "imageFiniteModulo_of_enumeration"
      negativeControl := ""
      audited := true
      standing := .constructedHere }
  , { chapter := 16, citation := "Theorem 16.1"
      statement := "Adequacy: for a theory equipped with the "
        ++ "Milner-Sewell-Leifer labels, logical equivalence in "
        ++ "context-decorated HML coincides with bisimilarity."
      sourceProves := true
      construction := "Framework/EnumeratedAdequacy.lean: "
        ++ "forwardEquivalent_iff_bisimilar_of_enumeration / "
        ++ "contextBisimilar_iff_hmlEquiv_of_enumeration; "
        ++ "GSLT/Logic/InterfaceInfinitaryModalLogic.lean / "
        ++ "InterfaceModalAdequacy.lean retain actual changing interfaces"
      provedTheorem := "Framework/EnumeratedAdequacy.lean: "
        ++ "contextBisimilar_iff_hmlEquiv_of_enumeration, under an explicit "
        ++ "enumeration hypothesis supplying image-finiteness modulo the "
        ++ "equations, for identical-label matching; "
        ++ "Syntax/RhoScopedParallelModalAdequacy.lean: complete-conjunction "
        ++ "adequacy for actual computed original rho parallel IPO firings, "
        ++ "with no branching assumption; Syntax/RhoScopedFiniteSuccessors.lean: "
        ++ "finite_successor_cover / finitary_adequacy earn the exact finite "
        ++ "successor catalogue of the original scoped COMM and separate Drop "
        ++ "rules at every ambient context. Finitary adequacy for these rules "
        ++ "requires no additional branching assumption; identity_diamond_source_iff "
        ++ "attaches arbitrary complete postconditions to independently "
        ++ "authored closed COMM/Drop/ParCong steps. The source's "
        ++ "coinductive higher-order label-payload comparison is not "
        ++ "instantiated by this theorem"
      instanceWitness := "Syntax/RhoScopedParallelModalControls.lean: "
        ++ "input_receives_an_inert_result; "
        ++ "RhoScopedParallelModalAdequacy.Complete.context_congruence "
        ++ "retains every original scoped parallel partner; "
        ++ "RhoScopedReactionReceiptControls.actual_quoted_bound_outcome "
        ++ "covers the original input-bound name inside an unsealed quotation"
      negativeControl := "Framework/ImageFinite.lean -- image-finiteness is "
        ++ "sufficient for the uniform finitary theorem; the counterexample "
        ++ "shows that omitting it without replacement is unsound, not that "
        ++ "every individual adequate system must satisfy it; "
        ++ "RhoScopedReactionReceiptControls.actual_receipt_fibre_infinite "
        ++ "separates finite outcomes from infinitely many authored assignments"
      audited := true
      standing := .constructedHere }
  , { chapter := 16, citation := "Definition 16.3"
      statement := "The logical metric on terms modulo bisimilarity, given by "
        ++ "the least formula rank separating two terms."
      sourceProves := true
      construction := "Framework/LogicalMetric.lean: ObservationScheme / "
        ++ "reading / separatingRank / distance -- the source's formula, "
        ++ "obtained by pulling back Mathlib's first-difference ultrametric "
        ++ "along the reading of a term as its sequence of answers; hmlScheme "
        ++ "-- the reading by an enumeration of the context-decorated formulae; "
        ++ "Syntax/RhoScopedParallelModalEnumeration.lean earns countability "
        ++ "and complete enumeration of actual original rho finite questions"
      provedTheorem := "Framework/LogicalMetric.lean: "
        ++ "hmlScheme_distance_eq_zero_iff_bisimilar -- for an enumeration of "
        ++ "every formula of a theory with enumerable successor classes, "
        ++ "distance zero is contextual bisimilarity; distance_eq -- on a "
        ++ "separated pair the distance is two to the minus the separating rank; "
        ++ "Syntax/RhoScopedParallelModalMetric.lean: distance_eq_scheme / "
        ++ "distance_eq_zero_iff / distance_eq_zero_iff_bisimilar -- the "
        ++ "independently computed firing answers give an actual metric on "
        ++ "question classes; Syntax/RhoScopedFiniteSuccessors.lean: "
        ++ "zero_distance_iff_bisimilar / metric_quotient_eq_iff_bisimilar "
        ++ "identify that metric's zero kernel with actual original scoped "
        ++ "IPO behavior using the earned finite successor catalogue"
      instanceWitness := "Syntax/RhoScopedParallelModalMetricControls.lean: "
        ++ "interactionFirst_distance / truthFirst_distance -- the same "
        ++ "actual waiting input and zero have distances one and one half"
      negativeControl := "Framework/LogicalMetric.lean: enumeration_matters -- "
        ++ "the same questions in a different order give the same pair "
        ++ "different distances, so the enumeration is a parameter; "
        ++ "Syntax/RhoScopedParallelModalMetricControls.lean: "
        ++ "enumeration_changes_actual_distance / kernels_agree -- complete "
        ++ "enumerations of actual rho questions retain the zero kernel "
        ++ "while changing numerical ranks"
      audited := true
      standing := .provedHere }
  , { chapter := 16, citation := "Proposition 16.1"
      statement := "The logical metric is an ultrametric on terms modulo "
        ++ "bisimilarity; terms differing only at greater rank are closer."
      sourceProves := true
      construction := "Framework/LogicalMetric.lean: distance"
      provedTheorem := "Framework/LogicalMetric.lean: "
        ++ "distance_triangle_nonarch -- the strong triangle inequality, with "
        ++ "distance_eq_zero_iff showing the metric is genuine modulo the "
        ++ "logic and distance_triangle showing nothing is lost"
      instanceWitness := "Syntax/RhoScopedParallelModalMetric.lean: "
        ++ "metricSpace / quotient_distance_readout / quotient_eq_iff_bisimilar "
        ++ "-- an actual original rho question quotient, with its behavior "
        ++ "identification under the stated finite cover"
      negativeControl := "Framework/LogicalMetric.lean: "
        ++ "distance_lt_of_rank_lt -- the locality reading stated as a "
        ++ "theorem, so a pair separated later is strictly closer; "
        ++ "depthScheme_agreement_iff_lt_separatingRank -- whole-fragment "
        ++ "quotient observations identify the least separating modal depth, "
        ++ "without a depth-monotone enumeration of formula syntax; "
        ++ "ObservationScheme.quotientMetricSpace -- an actual metric space "
        ++ "on observation classes, identified with contextual bisimilarity "
        ++ "by depthScheme_classes_eq_iff_bisimilar under adequacy"
      audited := true
      standing := .provedHere }
  ]

/-! ## Chapter 17 -/

/-- Chapter 17's rows: the context type, splittings, the bundle of events. -/
def chapter17 : List Obligation :=
  [ { chapter := 17, citation := "Remark 17.1"
      statement := "The state of this chapter: its constructions are indicated "
        ++ "rather than completed."
      sourceProves := true
      construction := "Syntax/ContextualSplitting.lean and "
        ++ "Syntax/FireSparseness.lean construct algebraic cuts and a concrete "
        ++ "sparsity witness. The structural derivative and its connection "
        ++ "to linear executable locations remain obligations"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 17, citation := "Definition 17.1"
      statement := "The context type of a theory, as the structural derivative "
        ++ "of its term type presented as a polynomial functor over its "
        ++ "signature."
      sourceProves := true
      construction := "Framework/RedexPosition.lean: Position / children / "
        ++ "positions; Syntax/ContextualSplitting.lean"
      provedTheorem := "Framework/RedexPosition.lean: enumeration completeness "
        ++ "for the binder-free fragment; this is not a structural-derivative "
        ++ "characterization for the signature term functor"
      instanceWitness := "Syntax/ContextualSplitting.lean: fire_gives_a_step"
      negativeControl := "Syntax/ContextualSplitting.lean: shape_does_not_locate"
      audited := true
      standing := .constructedHere }
  , { chapter := 17, citation := "Definition 17.2"
      statement := "A splitting of a term is a context paired with a subterm "
        ++ "that plugs into it to give the term back."
      sourceProves := true
      construction := "Syntax/ContextualSplitting.lean: Splitting / plug, on the "
        ++ "intrinsically scoped carrier. On language definitions, from the "
        ++ "library root: GSLT/LanguageDef/Interaction/Fire.lean: Splitting / "
        ++ "Splitting.root / Splitting.ofZipper, whose contexts have one hole by "
        ++ "construction"
      provedTheorem := "GSLT/LanguageDef/Interaction/Fire.lean: "
        ++ "Splitting.context_mem_zippersAt (the fibre of plugging over a term "
        ++ "is enumerated by its zippers). Syntax/ContextualSplitting.lean: "
        ++ "positionOfFibre_fibreOfPosition / fibreOfPosition_positionOfFibre "
        ++ "are record-level round trips for algebraic substitution cuts, whose "
        ++ "context field does not require exactly one hole"
      instanceWitness := "Syntax/ContextualSplitting.lean: fire_source; "
        ++ "GSLT/LanguageDef/Interaction/FireInstances.lean: handshakeRoot_fires"
      negativeControl := "Syntax/ContextualSplitting.lean: shape_does_not_locate; "
        ++ "GSLT/LanguageDef/Interaction/Fire.lean: fill_injective"
      audited := true
      standing := .provedHere }
  , { chapter := 17, citation := "Remark 17.2"
      statement := "Dedekind's move: the pattern of identifying an object with "
        ++ "the family of its splittings."
      sourceProves := true
      construction := "Syntax/ContextualSplitting.lean: "
        ++ "positionOfFibre_fibreOfPosition and "
        ++ "fibreOfPosition_positionOfFibre -- a bijection between a term's "
        ++ "algebraic cuts and their plug fibres. These record-level round "
        ++ "trips do not identify the context carrier with a structural "
        ++ "derivative or its cuts with linear syntactic occurrences"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 17, citation := "Definition 17.3"
      statement := "The bundle of available events is the subbundle of "
        ++ "splittings whose subterm matches a rule."
      sourceProves := true
      construction := "Syntax/ContextualSplitting.lean: Fire / residual, for one "
        ++ "positioned rule. On language definitions, from the library root: "
        ++ "GSLT/LanguageDef/Interaction/Fire.lean: Splitting.ExposesRedex (the "
        ++ "subterm matches the left side of a base rewrite in the sense of "
        ++ "Chapter 8) / Splitting.Fires / Splitting.FiresTo (and the context is "
        ++ "one in which rewrites fire: GSLT/LanguageDef/ReactiveContexts.lean: "
        ++ "Reactive)"
      provedTheorem := "GSLT/LanguageDef/ReactiveContexts.lean: "
        ++ "step_iff_baseStep_in_context; GSLT/LanguageDef/Interaction/Fire.lean: "
        ++ "step_iff_exists_firesTo (the reductions of a state are its available "
        ++ "events, for every language whose rules are base rewrites or "
        ++ "congruences) / Splitting.headed_of_exposesRedex (exposed redexes are "
        ++ "headed by the family of the base rewrites). "
        ++ "Syntax/ContextualSplitting.lean: fire_gives_a_step requires "
        ++ "holeCount K = 1 separately"
      instanceWitness := "Syntax/FireSparseness.lean: liveCut_fires; "
        ++ "GSLT/LanguageDef/Interaction/FireInstances.lean: handshakeRoot_fires / "
        ++ "openingInsideContent_firesTo / ambient_step_iff_exists_firesTo"
      negativeControl := "Syntax/FireSparseness.lean: deadCut_is_inert / "
        ++ "fire_is_sparse; GSLT/LanguageDef/Interaction/FireInstances.lean: "
        ++ "handshake_fires_iff / guarded_exposed_not_available (a redex beneath "
        ++ "a prefix matches a base rewrite and the state cannot move) / "
        ++ "contended_one_cut_two_events (with a contact carried by a bag one "
        ++ "cut carries two events)"
      audited := true
      standing := .provedHere }
  ]

/-! ## Chapter 18 -/

/-- Chapter 18's rows: scopes, fixed points, strata and generator length. -/
def chapter18 : List Obligation :=
  [ { chapter := 18, citation := "Definition 18.1"
      statement := "A scope is a name predicate; its extension is the set of "
        ++ "names satisfying it."
      sourceProves := true
      construction := "Framework/GeneratedScope.lean / GeneratedScopeSignature.lean; "
        ++ "Framework/RhoScopeOperationalFutures.lean constructs original "
        ++ "enabled-event atoms and their generated native scope on the full "
        ++ "scoped equation quotient. Syntax/RhoScopedNativeAbsence.lean "
        ++ "compares actual current absence with native future negation "
        ++ "on the independently constructed split-substitution category"
      provedTheorem := "Framework/RhoScopeOperationalFutures.lean: "
        ++ "generated_substitution / permitted_membership_iff / "
        ++ "supplied_receipt_readouts; Syntax/RhoScopedNativeAbsence.lean: "
        ++ "permitted_absence_iff_current / full_absence_iff_future"
      instanceWitness := "Framework/RhoScopeOperationalFutureControls.lean: "
        ++ "future_actual_scope_admitted / supplied_two_occurrences_retained"
      negativeControl := "Syntax/RhoScopedNativeAbsenceControls.lean: "
        ++ "current_guard_is_not_full_native_absence / "
        ++ "activating_substitution_has_no_section"
      audited := true
      standing := .constructedHere }
  , { chapter := 18, citation := "Remark 18.1"
      statement := "The extensional version is the flat case: a finite set of "
        ++ "channels is a scope."
      sourceProves := true
      construction := "Framework/GeneratedScope.lean: generatedScope takes flat "
        ++ "atom predicates as the base of its least fixed point, so the "
        ++ "extensional case is the base case rather than a separate notion"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 18, citation := "Proposition 18.1"
      statement := "Unique decomposition of a composite scope under disjoint "
        ++ "extensions and grade-zero separation: its parts are determined "
        ++ "up to structural congruence."
      sourceProves := true
      construction := "Syntax/RhoScopedScopeDecomposition.lean earns faithful "
        ++ "canonical quotation readback on exposed bodies and unique halves "
        ++ "under complete component separation in arbitrary source contexts. "
        ++ "Syntax/RhoScopedNameSeparatedDecomposition.lean identifies actual "
        ++ "canonical channel supports with complete inventory supports, then "
        ++ "derives component separation under explicit NamesDetect. The "
        ++ "original injectivity and channel-only uniqueness sketch is not "
        ++ "credited without these earned conditions"
      provedTheorem := "Syntax/RhoScopedScopeDecomposition.lean: "
        ++ "quote_injective_on_exposed / composite_unique / "
        ++ "exposedComposites_of_nonempty; "
        ++ "Syntax/RhoScopedNameSeparatedDecomposition.lean: "
        ++ "channelSupport_eq_inventory / named_quoted_decomposition_unique"
      instanceWitness := "Syntax/RhoScopedScopeDecompositionControls.lean: "
        ++ "actual_quoted_scope_has_unique_components / "
        ++ "fast_readback_preserves_duplicate_occurrences retain two equal "
        ++ "output occurrences and an output on a distinct actual quoted channel"
      negativeControl := "Syntax/RhoScopeQuotientControls.lean: "
        ++ "scope_disjointness_and_support_do_not_give_unique_components "
        ++ "retains distinct process origins of one name. "
        ++ "Syntax/RhoScopedScopeUnnamedControls.lean: "
        ++ "scope_name_images_are_disjoint / "
        ++ "complete_scope_channel_supports_are_disjoint / "
        ++ "disjoint_scopes_and_channels_do_not_determine_quoted_halves "
        ++ "exhibit reassignment of an actual unnamed nonzero rho component "
        ++ "even with exposed bodies; original_name_detection_is_not_automatic"
      audited := true
      standing := .constructedHere }
  , { chapter := 18, citation := "Corollary 18.1"
      statement := "Under the preceding proposition's hypotheses, description "
        ++ "length is additive up to a constant and membership testing "
        ++ "decomposes."
      sourceProves := true
      construction := "Syntax/RhoScopedScopeDecision.lean compares single "
        ++ "canonical-body partitioning with independent quoted scope membership "
        ++ "under supported colours and exposed composites; complete finite "
        ++ "search handles arbitrary decidable predicates. Framework/"
        ++ "RhoScopeExpressionDecomposition.lean joins these to actual sorted "
        ++ "formula semantics. Framework/RhoScopeBinaryDescription.lean "
        ++ "constructs an independently decoded binary grammar including mu "
        ++ "and arbitrary variable indices. Quoted parallel descriptions add "
        ++ "six bits, earning a semantic minimum upper bound. No additive "
        ++ "lower bound or cost of predicate evaluation is inferred"
      provedTheorem := "Syntax/RhoScopedScopeDecision.lean: "
        ++ "verdict_iff_composite / composite_iff_catalogue_nonempty / "
        ++ "admittedCatalogue_singleton; Framework/RhoScopeBinaryDescription.lean: "
        ++ "decodeBinary_encode / decodeClosed_encode / "
        ++ "quoted_parallel_description_length; "
        ++ "Framework/RhoScopeExpressionDecomposition.lean: "
        ++ "formula_membership_iff_fast_verdict / "
        ++ "formula_membership_iff_complete_search / composite_minimum_upper_bound"
      instanceWitness := "Syntax/RhoScopedScopeDecompositionControls.lean: "
        ++ "independent_search_is_exactly_the_recovered_pair; "
        ++ "Framework/RhoScopeDescriptionControls.lean: "
        ++ "closed_fixed_point_is_admitted / actual_formula_membership / "
        ++ "constructive_minimum_upper_bound"
      negativeControl := "Syntax/RhoScopedScopeDecompositionControls.lean: "
        ++ "fast_search_can_miss_an_admitted_origin / "
        ++ "complete_search_retains_distinct_origins; "
        ++ "Framework/RhoScopeDescriptionControls.lean: "
        ++ "wrong_sort_and_underflow_are_rejected / "
        ++ "unbound_variable_is_rejected_by_closed_admission / "
        ++ "shared_primitive_can_make_the_composite_shorter / "
        ++ "equal_predicates_can_have_unbounded_distinct_descriptions"
      audited := true
      standing := .constructedHere }
  , { chapter := 18, citation := "Remark 18.2"
      statement := "Overlap is where you pay, and it is the same payment as "
        ++ "before."
      sourceProves := true
      construction := "Syntax/UniqueDecompositionRepaired.lean: SupportedBy -- "
        ++ "the support-closure hypothesis the repaired decomposition needs is "
        ++ "exactly the payment the overlap exacts"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 18, citation := "Definition 18.2"
      statement := "A generated scope is the least fixed point of a formula in "
        ++ "a scope variable."
      sourceProves := true
      construction := "Framework/GeneratedScope.lean: scopeStep / "
        ++ "generatedScope := lfp scopeStep -- the least fixed point, not the "
        ++ "greatest, as Remark 18.4 insists. Framework/"
        ++ "RhoEquationGeneratedScope.lean supplies the part-level atoms, "
        ++ "drop coercion and cuts on the original scoped equation quotient"
      provedTheorem := "Framework/GeneratedScope.lean: scope_induction -- the "
        ++ "induction principle of the structural variant; Framework/"
        ++ "RhoEquationGeneratedScope.lean: generated_induction / "
        ++ "certificate_sound; Framework/RhoScopeOperationalFutures.lean: "
        ++ "generated_substitution / permitted_membership_iff"
      instanceWitness := "Framework/GeneratedScopeRho.lean: scopeStep over the "
        ++ "reflective calculus' quote and parallel formers"
      negativeControl := "Framework/GeneratedScopeRho.lean: no_selfCode_left / "
        ++ "no_selfCode_right -- a name is never its own code under a part"
      audited := true
      standing := .constructedHere }
  , { chapter := 18, citation := "Definition 18.3"
      statement := "The stratum of a name is the number of unfoldings needed to "
        ++ "reach it."
      sourceProves := true
      construction := "Framework/ScopeStratum.lean: stratum -- the number of "
        ++ "unfoldings in the structural scope variant, descending on literal "
        ++ "subterms. Framework/RhoScopeMinimumReceipts.lean constructs "
        ++ "minimum-depth certificates on the original equation quotient. "
        ++ "Framework/RhoScopeFutureAssays.lean preserves that independently "
        ++ "selected grade through substitutions with a section"
      provedTheorem := "Framework/ScopeStratum.lean: stratum_quote_par and "
        ++ "stratum_join_le -- syntactic unfolding bounds, not an invariant "
        ++ "stratum for the source scope modulo equations; Framework/"
        ++ "RhoScopeMinimumReceipts.lean: minimumReceipt?_depth_readout / "
        ++ "minimumReceipt?_least; Framework/RhoScopeFutureAssays.lean: "
        ++ "minimum_grade_preserved / grade_price_preserved / "
        ++ "completed_responses_preserved / candidate_retention_preserved"
      instanceWitness := "Framework/ScopeStratum.lean: stratum_tower -- every "
        ++ "stratum is inhabited, so the grading is not eventually empty; "
        ++ "Framework/RhoScopeFutureAssayControls.lean: "
        ++ "actual_minimum_grade_zero / actual_confirmation_survives_fresh_context / "
        ++ "scope_revision_survives_fresh_context"
      negativeControl := "Framework/ScopeStratum.lean: stratum_constant -- an "
        ++ "atom has stratum zero, as the source requires, so the measure is "
        ++ "not uniformly positive"
      audited := true
      standing := .constructedHere }
  , { chapter := 18, citation := "Remark 18.3"
      statement := "What is doing the work: two hypotheses carry the descent "
        ++ "and neither is free."
      sourceProves := true
      construction := "Framework/GeneratedScopeRho.lean: quote_par_injective "
        ++ "and no_selfCode_left / no_selfCode_right -- the two hypotheses, "
        ++ "discharged for the reflective calculus rather than assumed"
      provedTheorem := ""
      instanceWitness := "Framework/GeneratedScopeRho.lean"
      negativeControl := ""
      audited := true
      standing := .constructedHere }
  , { chapter := 18, citation := "Proposition 18.2"
      statement := "Membership in a generated scope is decidable by descent."
      sourceProves := true
      construction := "Framework/GeneratedScope.lean: inScope -- the deciding "
        ++ "procedure, descending on the structural measure"
      provedTheorem := "Framework/GeneratedScope.lean: inScope_iff -- the "
        ++ "procedure and the structural scope agree on representatives. "
        ++ "This does not prove quotient-level decidability or equivalence "
        ++ "with the literal source scope formula"
      instanceWitness := "Framework/GeneratedScopeRho.lean"
      negativeControl := "Framework/GeneratedScope.lean: sizeOf_quote_lt_left / "
        ++ "sizeOf_quote_lt_right -- the descent measure the procedure needs"
      audited := true
      standing := .constructedHere }
  , { chapter := 18, citation := "Remark 18.4"
      statement := "The least fixed point rather than the greatest, and that is "
        ++ "a claim rather than a convention."
      sourceProves := true
      construction := "Framework/GeneratedScope.lean: generatedScope is the lfp "
        ++ "of scopeStep -- the least fixed point, so the claim is honoured by "
        ++ "the construction rather than noted beside it"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 18, citation := "Definition 18.4"
      statement := "The generator length of a generated scope."
      sourceProves := true
      construction := "Framework/ScopeStratum.lean: generatorLength -- the "
        ++ "skeleton and the two atom lengths, with the skeleton a parameter "
        ++ "rather than an invented symbol count"
      provedTheorem := "Framework/ScopeStratum.lean: description_is_cheap -- "
        ++ "past any bound some stratum's inhabitant is larger, while the "
        ++ "generator's length has no stratum argument at all"
      instanceWitness := "Framework/ScopeStratum.lean: towerBody / "
        ++ "two_pow_le_sizeOf_towerBody"
      negativeControl := "Framework/ScopeStratum.lean: join_injective -- the "
        ++ "growth is not an artefact of repeated names, since joining is "
        ++ "injective"
      audited := true
      standing := .constructedHere }
  ]


/-! ## Chapter 20 -/

/-- Chapter 20's rows: the measure, admissible equations, the observer
extension, exposure and reconstruction, the gap, and the characterization
conjecture with its three obstacles. -/
def chapter20 : List Obligation :=
  [ { chapter := 20, citation := "Remark 20.1"
      statement := "Three things to keep apart."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Remark 20.2"
      statement := "What is not being claimed."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Definition 20.1"
      statement := "The measure of a term is the least constructor count among "
        ++ "its equational representatives."
      sourceProves := true
      construction := "StructuralModal/AdmissibleEquations.lean"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Definition 20.2"
      statement := "An equation set is admissible when leanness is hereditary "
        ++ "with a strictly decreasing measure and the sort does not move."
      sourceProves := true
      construction := "StructuralModal/AdmissibleEquations.lean: Admissible"
      provedTheorem := "StructuralModal/AdmissibleEquations.lean: "
        ++ "Admissible.leanInduction"
      instanceWitness := "", negativeControl := ""
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Remark 20.3"
      statement := "Why the size-respecting condition is not free."
      sourceProves := true
      construction := "StructuralModal/AdmissibleEquations.lean: the hereditary "
        ++ "measure is carried explicitly rather than replaced by a "
        ++ "size-respecting assumption, which is the substitution the remark "
        ++ "warns against"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 20, citation := "Remark 20.4"
      statement := "Not lists, and not Turing completeness."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Definition 20.3"
      statement := "The observer extension of a theory by an observation "
        ++ "signature: the authored theory with instrument vocabulary adjoined "
        ++ "per opened constructor."
      sourceProves := true
      construction := "Framework/ObserverExtension.lean: observerExtension / "
        ++ "instrumentRules / ObAdmissible / AdministrativeFresh. The opening rule is "
        ++ "a cut with a nullary request, as in the source; the projection and build "
        ++ "rules are unary formers applied to the bundle, where the source writes "
        ++ "cuts with nullary probes (from the library root: "
        ++ "GSLT/LanguageDef/Interaction/ObserverStrength.lean: "
        ++ "observerExtension_not_everyRuleIsCut)"
      provedTheorem := "Framework/ObserverExtension.lean: "
        ++ "rewriteAt_eq_of_authored_head -- executable conservativity on "
        ++ "authored heads conditional on administrative freshness, not a "
        ++ "sorted free extension or preservation of derived minimal labels"
      instanceWitness := "Framework/ObserverExtension.lean: "
        ++ "Gap.inertPair_conservative / Gap.inertPair_fresh"
      negativeControl := "Framework/ObserverExtension.lean: "
        ++ "Gap.collidingPair_not_fresh -- freshness is a decidable condition "
        ++ "that a presentation can fail"
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Proposition 20.1"
      statement := "The observer extension is still an interactive theory."
      sourceProves := true
      construction := "Framework/ObserverExtension.lean: mem_terms_of_mem / "
        ++ "step_of_base / step_mono / openedRules_mono. From the library root: "
        ++ "GSLT/LanguageDef/Interaction/Strength.lean: the three strengths of "
        ++ "interactive; GSLT/LanguageDef/Interaction/ObserverStrength.lean: "
        ++ "InteractivePresentation.observed"
      provedTheorem := "GSLT/LanguageDef/Interaction/ObserverStrength.lean: "
        ++ "observed_isInteractive (given its validity the extension has the "
        ++ "same contact and base interaction rule) / "
        ++ "observerExtension_baseRewritesHeaded (its base rewrites are headed "
        ++ "by the contact and the adjoined formers) / "
        ++ "observerExtension_not_everyRuleIsCut (its projection and build "
        ++ "rules are formers applied to the bundle and not cuts, so the "
        ++ "strength fixed in Section 20.3 is not kept by this construction)"
      instanceWitness := "Languages/ProcessCalculi/CCS/Observed.lean: "
        ++ "observedCCS_validate_eq_nil / observedCCS_isInteractive / "
        ++ "observedCCS_handshake_steps"
      negativeControl := "Languages/ProcessCalculi/CCS/Observed.lean: "
        ++ "observedCCS_not_everyRuleIsCut"
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Remark 20.5"
      statement := "Equations, or rewrite pairs."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Lemma 20.1"
      statement := "Minimal opening-request labels enumerate a term's "
        ++ "top-level E-decompositions; argument projection is deterministic "
        ++ "up to E."
      sourceProves := true
      construction := "Framework/ObserverExtension.lean: "
        ++ "openingRule_match_iff; Framework/ObserverReconstruction.lean: "
        ++ "reads_head_iff / projection_response; "
        ++ "Syntax/RhoScopedParallelPathReadout.lean: "
        ++ "complete_path_readout / every_surrounding_realized describe both "
        ++ "directions of original scoped parallel paths, and "
        ++ "RhoScopedParallelEvents.lean compares their independently authored "
        ++ "event support with roots and surrounding process classes. This "
        ++ "reaction-context profile does not derive the ask/get/build labels "
        ++ "of the book's wider observer extension"
      provedTheorem := "Framework/ObserverReconstruction.lean: reads_head_iff "
        ++ "-- a raw opening request reaches the constructor's bundle exactly "
        ++ "when the term is an application of it, under ObserverSetting. "
        ++ "Minimal labeled exposure of all E-decompositions is not proved"
      instanceWitness := "Languages/ProcessCalculi/RhoCalculus/"
        ++ "PlatformLabels.lean: rhoPlatform_observerSetting"
      negativeControl := "Framework/ObserverReconstruction.lean: "
        ++ "Interference.transition_does_not_determine_head / "
        ++ "Determinacy.request_has_two_responses / "
        ++ "Citation.rigidity_alone_insufficient -- counterexamples to "
        ++ "unrestricted exposure when a guard is dropped, not universal "
        ++ "necessity theorems for every individual presentation"
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Lemma 20.2"
      statement := "Calibration: equal terms are bisimilar in the extension."
      sourceProves := true
      construction := "Framework/SortedInstrumentCongruenceSystem.lean: system -- a "
        ++ "many-sorted first-order signature, any congruence as the "
        ++ "equations, any authored labelled system respecting them, and a "
        ++ "policy admitting constructors; its states, labels and steps "
        ++ "satisfy the respect laws of the generic labelled system"
      provedTheorem := "Framework/SortedInstrumentCongruenceSystem.lean: "
        ++ "bisimilar_of_rel -- for every congruence, every authored "
        ++ "system and every policy, on the labelled steps Lemma 20.1 "
        ++ "attributes to the kit (ask, get and build beside the authored "
        ++ "steps, targets closed under the equations). Deriving those "
        ++ "steps as least context labels is the row of Lemma 20.1"
      instanceWitness := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "unfolded_bisimilar -- a replicated atom and its unfolding, "
        ++ "whose roots and sizes differ"
      negativeControl := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "complete_kit_separates -- unequal terms are not thereby "
        ++ "related"
      audited := true
      standing := .provedHere }
  , { chapter := 20, citation := "Theorem 20.1"
      statement := "With admissible E and the complete observation signature, "
        ++ "observer-extension context-labeled bisimilarity coincides with "
        ++ "equality modulo E on closed authored first-order terms."
      sourceProves := true
      construction := "Framework/SortedInstrumentCongruenceSystem.lean: "
        ++ "rel_of_related -- recursion on the supplied left-hand term, "
        ++ "with an arbitrary matching decomposition on the right at each "
        ++ "opening. No measure and no lean representative is used, so "
        ++ "admissibility is not a hypothesis. "
        ++ "Framework/InstrumentEquationReconstruction.lean proves the "
        ++ "single-sorted case by least-count descent; "
        ++ "Framework/InstrumentCutKitEquationComparison.lean and "
        ++ "Framework/SortedTypedInstrumentKitPayloadReconstruction.lean "
        ++ "derive the labels from actual relative pushouts for the "
        ++ "unary-unit and the designated associative-commutative-unit "
        ++ "languages"
      provedTheorem := "Framework/SortedInstrumentCongruenceSystem.lean: "
        ++ "bisimilar_iff_rel -- for every congruence and every authored "
        ++ "system, with every constructor admitted, on the labelled steps "
        ++ "Lemma 20.1 attributes to the kit (ask, get and build beside "
        ++ "the authored steps, targets closed under the equations). For "
        ++ "arbitrary equations the derivation of those steps from "
        ++ "relative pushouts is the source Conditions 20.1 and 20.2 and "
        ++ "the row of Lemma 20.1. "
        ++ "Framework/ScopedBindingInstrumentLogic.lean: "
        ++ "bisimilar_iff_equation extends the reconstruction to original "
        ++ "intrinsically scoped binding terms and every substitution "
        ++ "congruence. ScopedBindingInstrumentComparison.cover earns "
        ++ "complete state, observation and outgoing-step coverage; "
        ++ "projection retains the declared binder context and variable "
        ++ "probes retain actual positions. These are explicit instrument "
        ++ "steps, not an automatic derivation of least enabling labels"
      instanceWitness := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "bang_answers_parallel_probe / "
        ++ "bang_answers_through_larger_representative -- openings through "
        ++ "an equation that changes root and size"
      negativeControl := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "complete_kit_separates / gap"
      audited := true
      standing := .provedHere }
  , { chapter := 20, citation := "Remark 20.6"
      statement := "Domains: the reconstruction theorem is about a restricted "
        ++ "relation, and the restriction is part of the statement."
      sourceProves := true
      construction := "Framework/ObserverReconstruction.lean: ReadableByKit "
        ++ "names the restriction inside the theorem rather than around it, and "
        ++ "Framework/SortedInstrumentCongruenceSystem.lean: bisimilar_iff_rel "
        ++ "states the complete constructor policy explicitly. Theorem 20.1 "
        ++ "is recorded at that domain, with least-context-label derivation "
        ++ "kept as a separate source precondition"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 20, citation := "Remark 20.7"
      statement := "Infinite branching is not a problem."
      sourceProves := true
      construction := "Framework/ObserverReconstruction.lean: reconstruction is "
        ++ "proved by structural induction on the term -- not on transition "
        ++ "depth, and through no Hennessy-Milner characterization -- which is "
        ++ "exactly the remark's claim, visible in the proof rather than "
        ++ "asserted beside it.  The contrast is in the tree as well: "
        ++ "Framework/ImageFinite.lean marks where image-finiteness genuinely "
        ++ "is required, namely the adequacy result of an earlier chapter, so "
        ++ "the two situations are distinguished rather than conflated"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 20, citation := "Remark 20.8"
      statement := "Binding, and the largest gap: for a binding constructor the "
        ++ "arguments are abstractions rather than closed terms, and the kit "
        ++ "has no instrument for them."
      sourceProves := true
      construction := "Framework/ObserverExtension.lean: projectablePositions "
        ++ "admits only parameters that are terms of a base sort, so an "
        ++ "abstraction parameter gets no projection rule -- the gap is "
        ++ "excluded by construction rather than assumed away. "
        ++ "Framework/ScopedBindingInstrumentSystem.lean separately "
        ++ "constructs an inspection protocol on the existing intrinsically "
        ++ "scoped terms: operator arguments are opened in their declared "
        ++ "binder contexts and variable probes retain exact positions. "
        ++ "Framework/RhoScopedInstrumentProperBase.lean joins the original "
        ++ "COMM/Drop IPO labels through their complete firing and computed "
        ++ "least-label comparisons; structural ask/get still belong to the "
        ++ "explicit inspection extension"
      provedTheorem := "Framework/ScopedBindingInstrumentLogic.lean: "
        ++ "bisimilar_iff_equation / logicallyEquivalent_iff_bisimilar / "
        ++ "characteristic_iff; the new inspection protocol earns these "
        ++ "for every binding substitution congruence and authored "
        ++ "equation-respecting system. It does not identify inspection "
        ++ "permission with reaction permission. "
        ++ "Framework/RhoScopedInstrumentAdmission.lean: "
        ++ "complete_context_congruence / complete_substitution_congruence; "
        ++ "Framework/ScopedBindingInstrumentAdmission.lean: "
        ++ "structural_iff_interactions retains complete binder postconditions; "
        ++ "Framework/RhoScopedInstrumentQuestionTranslation.lean: "
        ++ "translation_truth / stage_truth compare every closed finite modal "
        ++ "question with original operational truth at every ambient scope"
      instanceWitness := "Framework/ScopedBindingInstrumentControls.lean: "
        ++ "binder_projects / input_projects_under_binder / "
        ++ "rho_reconstruction / actual_communication; "
        ++ "Framework/RhoScopedInstrumentAdmissionControls.lean: "
        ++ "original_comm_is_proper / original_drop_is_proper / "
        ++ "input_test_has_actual_ask_get_trace / "
        ++ "complete_kit_replacement_under_actual_input; "
        ++ "Framework/RhoScopedInstrumentAssayControls.lean: "
        ++ "paid_original_target_satisfies_observer_question"
      negativeControl := "Framework/ScopedBindingInstrumentControls.lean: "
        ++ "capture_projection_rejected / capture_not_bisimilar / "
        ++ "empty_kit_loses_capture; "
        ++ "Framework/RhoScopedInstrumentAdmissionControls.lean: "
        ++ "body_postcondition_rejects_capture; "
        ++ "Framework/RhoScopedPartialObserverControls.lean: "
        ++ "partial_agreement_is_not_contextual_replacement; "
        ++ "Syntax/RhoScopedFiringSubstitutionControls.lean: "
        ++ "complete_ipo_receipt_cannot_keep_both_mapped_readouts"
      audited := true
      standing := .respectedHere }
  , { chapter := 20, citation := "Proposition 20.2"
      statement := "Bisimilarity in the twice-extended and once-extended "
        ++ "theories agrees on terms of the once-extended signature."
      sourceProves := true
      construction := "Framework/ObserverIdempotence.lean: "
        ++ "rewriteAt_eq_of_second_extension -- conservativity applied a second "
        ++ "time, reading the once-extended theory as the authored one"
      provedTheorem := "Framework/ObserverIdempotence.lean: "
        ++ "rewriteAt_eq_of_two_extensions -- the original theory, its "
        ++ "extension and the extension of its extension agree on terms of the "
        ++ "original signature, under both rounds' freshness and premise "
        ++ "closure. This is not the source's bisimilarity agreement on "
        ++ "the once-extended signature"
      instanceWitness := "Framework/ObserverIdempotence.lean: "
        ++ "disjoint_second_round_is_fresh -- a second round that really "
        ++ "adjoins instruments, for a constructor the first left alone"
      negativeControl := "Framework/ObserverIdempotence.lean: "
        ++ "repeating_a_round_is_not_fresh and "
        ++ "reopening_one_constructor_is_not_fresh -- the name suggests the "
        ++ "construction may be applied twice unconditionally; it may not, "
        ++ "since re-opening an instrumented constructor collides with the "
        ++ "vocabulary already adjoined"
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Theorem 20.2"
      statement := "Structural separation for closed terms of the authored "
        ++ "signature under an admissible equation set."
      sourceProves := true
      construction := "Framework/SortedInstrumentCongruenceLogic.lean: Formula / "
        ++ "Holds / characteristic -- sorted formulas with one structural "
        ++ "connective per constructor, satisfied through every "
        ++ "decomposition the equation theory provides; the characteristic "
        ++ "formula is read off the supplied term itself"
      provedTheorem := "Framework/SortedInstrumentCongruenceLogic.lean: "
        ++ "rel_iff_structural -- for every congruence: two closed terms "
        ++ "are equal exactly when every purely structural formula true of "
        ++ "the first is true of the second. holds_resp proves that "
        ++ "satisfaction respects the equations. Admissibility is not used"
      instanceWitness := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "characteristic_crosses_roots -- the formula of a replicated "
        ++ "atom holds of a term whose root is parallel composition"
      negativeControl := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "characteristic_separates"
      audited := true
      standing := .provedHere }
  , { chapter := 20, citation := "Remark 20.9"
      statement := "What the direct proof buys."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Corollary 20.1"
      statement := "Logical correspondence, under the hypotheses of the two "
        ++ "theorems."
      sourceProves := true
      construction := "Framework/SortedInstrumentCongruenceLogic.lean: correspondence"
      provedTheorem := "Framework/SortedInstrumentCongruenceLogic.lean: correspondence "
        ++ "-- with every constructor admitted, equality in the equation "
        ++ "theory, bisimilarity in the instrument system, equivalence in "
        ++ "the full logic and transfer of purely structural formulas "
        ++ "coincide, for every congruence and every authored system, on "
        ++ "the labelled steps Lemma 20.1 attributes to the kit (ask, get "
        ++ "and build beside the authored steps, targets closed under the "
        ++ "equations)"
      instanceWitness := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "unfolded_bisimilar / characteristic_crosses_roots"
      negativeControl := "Framework/SortedInstrumentCongruenceControls.lean: gap -- the "
        ++ "same two terms are related by the empty kit and separated by "
        ++ "the complete one"
      audited := true
      standing := .provedHere }
  , { chapter := 20, citation := "Proposition 20.3"
      statement := "The gap is generically nonempty: a theory with two distinct "
        ++ "inert constructors has terms the authored theory cannot "
        ++ "separate and the instruments can."
      sourceProves := true
      construction := "Framework/SortedInstrumentCongruenceSystem.lean: "
        ++ "BaseSystem.Bisimilar / refinement_strict; "
        ++ "Framework/ObserverExtension.lean: Gap"
      provedTheorem := "Framework/SortedInstrumentCongruenceSystem.lean: "
        ++ "refinement_strict -- terms the authored system cannot tell "
        ++ "apart, lying in different equation classes, are related by the "
        ++ "empty kit and separated by the complete one. That two inert "
        ++ "constants are bisimilar in the authored system is a hypothesis "
        ++ "here; it is not derived from the absence of the constants in a "
        ++ "rule set"
      instanceWitness := "Framework/SortedInstrumentCongruenceControls.lean: gap, with "
        ++ "silent_bisimilar supplying the hypothesis"
      negativeControl := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "unfolded_bisimilar -- terms in one class are not separated"
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Example 20.1"
      statement := "Replication, and a caveat."
      sourceProves := true
      construction := "Syntax/UnfoldingBreaksDecomposition.lean: unfolding a "
        ++ "replication puts every count in one class, which is the caveat the "
        ++ "example raises, exhibited rather than described"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 20, citation := "Remark 20.10"
      statement := "Why minimality is load-bearing for the gap result."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Proposition 20.4"
      statement := "Monotonicity: enlarging the instrument set refines the "
        ++ "bisimilarity."
      sourceProves := true
      construction := "Framework/SortedInstrumentCongruenceSystem.lean: "
        ++ "Act.iff_permitted -- a smaller kit has exactly the larger kit "
        ++ "steps at the labels it permits"
      provedTheorem := "Framework/SortedInstrumentCongruenceSystem.lean: "
        ++ "bisimilar_mono, with both ends: bisimilar_closed_iff (nothing "
        ++ "admitted gives the authored system bisimilarity) and "
        ++ "bisimilar_iff_rel (everything admitted gives the equation "
        ++ "theory), on the labelled steps Lemma 20.1 attributes to the "
        ++ "kit (ask, get and build beside the authored steps, targets "
        ++ "closed under the equations)"
      instanceWitness := "Framework/SortedInstrumentCongruenceControls.lean: gap"
      negativeControl := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "parallel_probe_cannot_separate / atom_probe_separates -- two "
        ++ "one-probe kits with different reach"
      audited := true
      standing := .provedHere }
  , { chapter := 20, citation := "Conjecture 20.1"
      statement := "Partial characterization: bisimilarity in the observer "
        ++ "extension coincides with logical equivalence in the fragment "
        ++ "of the generated logic whose structural connectives are those "
        ++ "of the observation signature.  The source names three "
        ++ "obstacles: a formula may inspect an opened constructor sitting "
        ++ "beneath an unopened one; equations may relate terms whose "
        ++ "roots lie on opposite sides of the signature; and a binder may "
        ++ "move material across an apparent structural boundary.  "
        ++ "Relativizing the reconstruction theorem handles none of them."
      sourceProves := false
      construction := "Framework/SortedInstrumentCongruenceLogic.lean: Fragment / "
        ++ "Fragment.equivalent_iff_bisimilar -- the structural connective "
        ++ "for a constructor reads an ask step followed by one get step "
        ++ "per position, so the logic with the connectives of the kit and "
        ++ "the authored diamonds is adequate whenever its conjunctions "
        ++ "cover the branching"
      provedTheorem := "Framework/SortedInstrumentCongruenceLogic.lean: "
        ++ "logicallyEquivalent_iff_bisimilar -- for every policy, every "
        ++ "congruence and every authored system, with arbitrary "
        ++ "conjunction; finitaryEquivalent_iff_bisimilar -- with finite "
        ++ "conjunction, when authored successors and admitted "
        ++ "decompositions are finite up to the equations. First-order "
        ++ "carrier, on the labelled steps Lemma 20.1 attributes to the "
        ++ "kit (ask, get and build beside the authored steps, targets "
        ++ "closed under the equations); the first two named obstacles are "
        ++ "covered. Framework/ScopedBindingInstrumentLogic.lean: "
        ++ "logicallyEquivalent_iff_bisimilar / "
        ++ "finitaryEquivalent_iff_bisimilar extend the comparison to the "
        ++ "existing original scoped binding terms and argument lists, "
        ++ "including binder-extended interfaces and exact variable "
        ++ "positions. Least context labels remain a separate admission "
        ++ "obligation; finite conjunctions retain both finite-cover "
        ++ "hypotheses"
      instanceWitness := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "finitary_logic_separates"
      negativeControl := "Framework/SortedInstrumentCongruenceBranchingControls.lean: "
        ++ "finite_conjunctions_inadequate -- with nothing admitted, two "
        ++ "terms agree on every admitted formula with finite conjunctions "
        ++ "and are not bisimilar; "
        ++ "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "empty_kit_needs_authored_diamond -- structural connectives "
        ++ "alone do not suffice for a partial kit"
      audited := true
      standing := .provedHere }
  , { chapter := 20, citation := "Proposition 20.5"
      statement := "Downward closure: the conjecture holds when the observation "
        ++ "signature is closed under the subterm relation of lean "
        ++ "representatives."
      sourceProves := true
      construction := "Syntax/SortedConstructorCongruences.lean: Supported -- every "
        ++ "constructor of the term is admitted"
      provedTheorem := "Framework/SortedInstrumentCongruenceLogic.lean: "
        ++ "correspondence_of_supported -- for a supported term against "
        ++ "every term of its sort, equality, bisimilarity under the "
        ++ "policy, equivalence in the logic and transfer of the purely "
        ++ "structural formulas of the policy coincide; "
        ++ "Framework/SortedInstrumentCongruenceSystem.lean: "
        ++ "bisimilar_iff_rel_of_supported. The condition is on the "
        ++ "supplied term, not on lean representatives"
      instanceWitness := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "atom_probe_separates"
      negativeControl := "Framework/SortedInstrumentCongruenceControls.lean: "
        ++ "parallel_probe_cannot_separate -- an unsupported term is not "
        ++ "separated"
      audited := true
      standing := .provedHere }
  , { chapter := 20, citation := "Remark 20.11"
      statement := "Three restrictions, kept apart: an agent observing its "
        ++ "environment faces three different limits and collapsing them "
        ++ "loses information."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Remark 20.12"
      statement := "The factory is an import."
      sourceProves := true
      construction := "Framework/ObserverExtension.lean: the minting apparatus "
        ++ "is excluded by an explicit capability condition rather than by "
        ++ "assumption, so what the remark calls an import is a parameter"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 20, citation := "Remark 20.13"
      statement := "Factories resist the construction: the extension must not "
        ++ "be applied to a minting former, since a token that can be opened "
        ++ "can be rebuilt, and one that can be rebuilt can be forged."
      sourceProves := true
      construction := "Framework/ObserverExtension.lean: ObAdmissible / "
        ++ "no_opening_for_minting / no_instrument_rules_for_minting"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .constructedHere }
  ]

/-- The ledger: chapters six, seven and sixteen to twenty of the pinned source. -/
def ledger : List Obligation :=
  chapter6 ++ chapter7 ++ chapter8 ++ chapter9 ++ chapter10 ++ chapter16 ++ chapter17
    ++ chapter18 ++ chapter19 ++ chapter20

/-! ## The discipline the ledger enforces -/

/-- A row's standing must pay for itself.  Proved requires a named theorem, an
inhabited instance and a control; constructed requires a named construction. -/
def rowIntegrity (row : Obligation) : Bool :=
  match row.standing with
  | .provedHere =>
      !row.provedTheorem.isEmpty && !row.instanceWitness.isEmpty
        && !row.negativeControl.isEmpty
  | .constructedHere => !row.construction.isEmpty
  | .observedHere => !row.instanceWitness.isEmpty
  | .refutedHere => !row.negativeControl.isEmpty
  | .respectedHere => !row.construction.isEmpty || !row.negativeControl.isEmpty
  | .openHere => true

private theorem string_isEmpty_append (s t : String) :
    (s ++ t).isEmpty = (s.isEmpty && t.isEmpty) := by
  apply Bool.eq_iff_iff.mpr
  simp [String.isEmpty_iff, String.append_eq_empty_iff]

/-- Chapter 6 satisfies the ledger's named-field requirements. -/
theorem chapter6_integrity : chapter6.all rowIntegrity = true := by
  simp only [chapter6, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Chapter 7 satisfies the ledger's named-field requirements. -/
theorem chapter7_integrity : chapter7.all rowIntegrity = true := by
  simp only [chapter7, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Chapter 8 satisfies the ledger's named-field requirements. -/
theorem chapter8_integrity : chapter8.all rowIntegrity = true := by
  simp only [chapter8, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Chapter 9 satisfies the ledger's named-field requirements. -/
theorem chapter9_integrity : chapter9.all rowIntegrity = true := by
  simp only [chapter9, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Chapter 10 satisfies the ledger's named-field requirements. -/
theorem chapter10_integrity : chapter10.all rowIntegrity = true := by
  simp only [chapter10, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Chapter 16 satisfies the ledger's named-field requirements. -/
theorem chapter16_integrity : chapter16.all rowIntegrity = true := by
  simp only [chapter16, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Chapter 17 satisfies the ledger's named-field requirements. -/
theorem chapter17_integrity : chapter17.all rowIntegrity = true := by
  simp only [chapter17, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Chapter 18 satisfies the ledger's named-field requirements. -/
theorem chapter18_integrity : chapter18.all rowIntegrity = true := by
  simp only [chapter18, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Chapter 19 satisfies the ledger's named-field requirements. -/
theorem chapter19_integrity : chapter19.all rowIntegrity = true := by
  simp only [chapter19, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append,
    Bool.and_eq_true]
  repeat' constructor <;> decide +kernel

/-- Chapter 20 satisfies the ledger's named-field requirements. -/
theorem chapter20_integrity : chapter20.all rowIntegrity = true := by
  simp only [chapter20, List.all_cons, List.all_nil, rowIntegrity, string_isEmpty_append]
  decide

/-- Every row satisfies the named-field requirements for its recorded standing.
The proof composes separately checked chapter metadata; it does not certify
the mathematical adequacy of the cited evidence. -/
theorem ledger_integrity : ledger.all rowIntegrity = true := by
  simp only [ledger, List.all_append, chapter6_integrity, chapter7_integrity,
    chapter8_integrity, chapter9_integrity, chapter10_integrity, chapter16_integrity, chapter17_integrity, chapter18_integrity, chapter19_integrity,
    chapter20_integrity, Bool.and_self]

/-- Rows entered so far, against the denominator. -/
def entered : Nat := ledger.length

theorem entered_eq : entered = 114 := by decide

/-- Chapter 19's numbered obligations are one proposition and six remarks; the
remaining rows are the algorithm's own steps, which the chapter states in prose
rather than as numbered statements. -/
def chapter19NumberedCitations : List String :=
  ["Proposition 19.1", "Remark 19.1", "Remark 19.2", "Remark 19.3",
   "Remark 19.4", "Remark 19.5", "Remark 19.6"]

theorem chapter19_numbered_count :
    (ledger.filter
      (fun row => chapter19NumberedCitations.contains row.citation)).length = 7
      ∧ chapter19NumberedCitations.length = 7 := by
  refine ⟨by decide, by decide⟩

/-- The recorded source row cites no source proof of the central proposition.
The Boolean metadata does not establish an absence theorem about the source. -/
theorem proposition_19_1_source_proof_not_cited :
    (ledger.filter (fun row => row.citation == "Proposition 19.1")).all
      (fun row => row.sourceProves == false) = true := by decide

/-- The recorded adjunction and monad are proved at the explicit logical profile.
This metadata check does not replace their universal-property proofs. -/
theorem proposition_19_1_recorded_proved :
    (ledger.filter (fun row => row.citation == "Proposition 19.1")).all
      (fun row => row.standing == Standing.provedHere) = true := by decide


/-! ## What the ledger currently reports -/

/-- The nine rows that are algorithm steps rather than numbered statements: the
chapter the construction turns on states its algorithm in prose. -/
def algorithmRowCitations : List String :=
  ["Section 19.4, M-FORM", "Section 19.4, M-INTRO", "Section 19.4, M-STEP",
   "Section 19.4, M-ELIM", "Section 19.6, sort slots and the equational center",
   "Section 19.3, authored rewrite and redex generation",
   "Section 19.5, structural and propositional generation",
   "Section 19.7, rho continuation cube and channel face",
   "Section 19.9, independent dials and budgeted checking"]

/-- The prose claims, non-examples and tables of chapters six to ten, entered
as section rows. -/
def sectionRowCitations : List String :=
  ["Section 6.2, the three definitions in advance", "Section 6.3, the rho calculus",
   "Section 7.4, lambda theories and not Lawvere theories",
   "Section 7.5, adjoined and not enriched",
   "Section 7.6, the classifying structure", "Section 7.6, the classifying property",
   "Section 7.8, rung one: JSON", "Section 7.9, rung two: Monoid",
   "Section 7.10, rung three: Lambda", "Section 7.11, the rho calculus",
   "Section 8.2, the interaction cut", "Section 8.3, nominal and structural surfaces",
   "Section 8.3, equations forge position", "Non-example 8.1", "Non-example 8.2",
   "Section 8.7, presentation versus encoding", "Table 9.1", "Table 9.2",
   "Section 10.1, the constant map",
   "Section 10.1, an encoding is not a map of terms",
   "Section 10.1, target contexts observe too much",
   "Section 10.2, contexts as the primary structure"]

/-- Numbered rows meet the recorded eighty-three-row denominator. This
arithmetic does not certify exhaustive source coverage, including the separate
conditions. -/
theorem numbered_entered :
    (ledger.filter
      (fun row => !algorithmRowCitations.contains row.citation
        && !sectionRowCitations.contains row.citation)).length
        = totalObligations
      ∧ totalObligations = 83 := by
  refine ⟨by decide, by decide⟩

/-- How many rows carry each standing. -/
def countBy (st : Standing) : Nat :=
  (ledger.filter (fun row => row.standing == st)).length

/-- Exact counts of recorded standings, not a semantic completion certificate. -/
theorem standing_tally :
    countBy .provedHere = 46 ∧ countBy .constructedHere = 40
      ∧ countBy .refutedHere = 4 ∧ countBy .respectedHere = 16
      ∧ countBy .openHere = 8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Every Chapter 7 row records a proof or a respected constraint.
This is a status check on cited evidence, not a substitute for checking it. -/
theorem chapter7_recorded_closed :
    chapter7.all (fun row => row.standing == Standing.provedHere ||
      row.standing == Standing.respectedHere) = true := by decide

/-- Chapters 8 to 10: every row but the note on complexity records a proof, a
construction or a respected constraint. This is a status check on cited
evidence, not a substitute for checking it. -/
theorem chapters8to10_recorded :
    (chapter8 ++ chapter9 ++ chapter10).all (fun row =>
      row.standing != Standing.openHere || row.citation == "Remark 10.4") = true := by decide

/-- The tally accounts for every row. -/
theorem tally_is_total :
    countBy .provedHere + countBy .constructedHere + countBy .refutedHere
      + countBy .observedHere + countBy .respectedHere + countBy .openHere
      = entered := by decide

/-- Every Chapter 19 row records a proof or a named source refutation.
This metadata statement does not widen the admitted theorem profiles. -/
theorem chapter19_recorded_resolved :
    chapter19.all (fun row => row.standing == Standing.provedHere ||
      row.standing == Standing.refutedHere) = true := by decide

/-- Exact source claims carrying kernel-checked separating counterexamples. -/
theorem chapter19_refuted_claims :
    (ledger.filter (fun row => row.standing == Standing.refutedHere)).map (·.citation) =
      ["Section 19.4, M-STEP", "Section 19.4, M-ELIM",
       "Section 19.5, structural and propositional generation",
       "Remark 19.6"] := by decide

/-- Rows for which a search for existing coverage has been made. -/
def auditedCount : Nat := (ledger.filter (·.audited)).length

/-- Open rows split by whether they have been audited. -/
def openAudited : Nat :=
  (ledger.filter (fun row => row.standing == Standing.openHere && row.audited)).length

/-- Open rows not yet audited. -/
def openUnaudited : Nat :=
  (ledger.filter (fun row => row.standing == Standing.openHere && !row.audited)).length

/-- Counts of recorded audit flags. Flags do not establish exhaustive absence
of coverage or discharge the source obligations. -/
theorem audit_coverage :
    auditedCount = 114 ∧ openAudited = 8 ∧ openUnaudited = 0
      ∧ openAudited + openUnaudited = countBy .openHere := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Mettapedia.Documentation.SourceLedgers.FindingMind
