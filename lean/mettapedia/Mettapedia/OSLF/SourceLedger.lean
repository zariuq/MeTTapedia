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

All five chapters are inventoried below. The recorded definition, remark,
proposition, theorem and corollary counts stay in `chapterObligationCount`.
Conditions 20.1 (redex RPOs) and 20.2 (context congruence) are additional source
preconditions, not rows in that denominator, and require their own certification.
-/

namespace Mettapedia.OSLF.SourceLedger

set_option autoImplicit false
set_option maxRecDepth 400000

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
  [(16, 9), (17, 5), (18, 11), (19, 7), (20, 28)]

/-- Publication revision supplying the draft-26 obligation numbering. -/
def sourceRevision : String := "1f7bd34b11e65d707dde4b3638d08a181e1b8028"

/-- The compiled source carrying these chapter and section numbers. -/
def sourceDocument : String := "FindingMind/draft26/finding_mind.pdf"

/-- The denominator: sixty numbered obligations across chapters sixteen to
twenty. -/
def totalObligations : Nat :=
  (chapterObligationCount.map (·.2)).foldl (· + ·) 0

theorem totalObligations_eq : totalObligations = 60 := by decide

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
      construction := "Framework/TypeFormerExtension.lean: "
        ++ "typeFormerExtension -- declaration-level extension with one "
        ++ "unstratified parameterized declaration per enumerated site. "
        ++ "Generated typing rules, structural/propositional layers, a "
        ++ "morphism action and the free-extension universal property remain "
        ++ "unbuilt; GeneratedLayerAdjunction.lean compares object-level data"
      provedTheorem := "Framework/TypeFormerExtension.lean: "
        ++ "extends_a_theory_with_a_site -- the composite is not the identity "
        ++ "on any theory with a redex site. Declaration growth does not "
        ++ "prove freeness, an adjunction or the monad laws"
      instanceWitness := "Framework/TypeFormerExtension.lean: "
        ++ "rhoCalc_strictly_extended, and rhoOnce_validate_eq_nil -- the "
        ++ "extended reflective calculus passes the validation gate"
      negativeControl := "Framework/GeneratedLayerAdjunction.lean: "
        ++ "reading_one_extends_nothing; and in "
        ++ "Framework/TypeFormerExtension.lean, no_formers_without_sites -- "
        ++ "the construction manufactures no former out of nothing -- together "
        ++ "with rhoTwice_not_label_distinct and rhoTwice_rejected, which show "
        ++ "a second application is not inert but invalid, re-adjoining every "
        ++ "former the first "
        ++ "declared, so the construction needs a freshness discipline before "
        ++ "it can be a monad"
      audited := true
      standing := .constructedHere }
  , { chapter := 19
      citation := "Section 19.4, M-FORM"
      statement :=
        "For a rewrite rule and an admissible redex position, the generated "
        ++ "modality is formed from the typed one-hole context, its rely "
        ++ "variables and its result sort."
      sourceProves := false
      construction := "Framework/GeneratedModality.lean: RelyPossibly; "
        ++ "Framework/RedexPosition.lean: relyVars / hiddenVars / slotCount. "
        ++ "These construct a raw predicate and slot data, not the sorted "
        ++ "formation judgment of the source"
      provedTheorem := ""
      instanceWitness := "Framework/GeneratedHypercubeInstances.lean: "
        ++ "rhoCommPaper_square_is_face; Framework/WMCalculusGeneratedRely.lean: "
        ++ "evidenceAdd_focus / evidenceAdd_stable / evidenceAdd_relyVars / "
        ++ "evidenceAdd_slotCount / evidenceAdd_relyPossibly / "
        ++ "specimen_fires / specimen_modal_step -- one non-root WM rule-schema instance"
      negativeControl := "Languages/ProcessCalculi/RhoCalculus/"
        ++ "PlatformModalFamily.lean: rhoCalc_fails_check; "
        ++ "Framework/WMCalculusGeneratedRely.lean: empty_rely_satisfied / "
        ++ "empty_bindings_fire -- the pattern-level guard does not require "
        ++ "the computed rely variable to be bound; "
        ++ "Framework/WMCalculusSortedBoundary.lean: missingGrammar_validation_first_diagnostics / "
        ++ "missingGrammar_evidenceAdd_not_sorted / same_name_not_both_sorted / "
        ++ "binary_probe_application_sorted / binary_probe_has_no_cross_sort_path -- WM "
        ++ "core constructors now validate and sort; removing their declarations fails. The encoder "
        ++ "conflates equal raw state/query names; even a well-sorted binary "
        ++ "constructor gives no path in the unary constructor category, "
        ++ "so the operational WM instance is not a sorted M-FORM witness"
      audited := true
      standing := .constructedHere }
  , { chapter := 19
      citation := "Section 19.4, M-INTRO"
      statement :=
        "The generated introduction law types a term at the modality when "
        ++ "every admissible rely instance types its specified reduct at the "
        ++ "substituted continuation type."
      sourceProves := false
      construction := "Framework/GeneratedModality.lean: relyPossibly_intro"
      provedTheorem := "Framework/GeneratedModality.lean: relyPossibly_intro, "
        ++ "for a stable authored focus, assuming every rely-satisfying "
        ++ "firing instance has its repaired right-hand side in the "
        ++ "continuation predicate; this is a raw relational introduction law"
      instanceWitness := "Framework/GeneratedHypercubeInstances.lean: "
        ++ "rhoCommPaper_square_card -- face cardinality, not an inhabited "
        ++ "typing judgment for the generated introduction law"
      negativeControl := "Framework/GeneratedModality.lean: "
        ++ "not_relyPossibly_of_result_empty"
      audited := true
      standing := .constructedHere }
  , { chapter := 19
      citation := "Section 19.4, M-STEP"
      statement :=
        "Placing an inhabitant into the selected context executes to the "
        ++ "specified right-hand-side instance."
      sourceProves := false
      construction := "Framework/GeneratedModality.lean: relyPossibly_step"
      provedTheorem := "Framework/GeneratedModality.lean: "
        ++ "relyPossibly_step_authored, for the selected authored focus over "
        ++ "the repaired instantiation. The general inhabitant theorem gives "
        ++ "some successor, not necessarily that specified instance"
      instanceWitness := "Framework/GeneratedModalityRho.lean"
      negativeControl := "Framework/GeneratedModality.lean: "
        ++ "rhsOnlyRelyPossibly_result_independent_of_term"
      audited := true
      standing := .constructedHere }
  , { chapter := 19
      citation := "Section 19.4, M-ELIM"
      statement :=
        "The specified right-hand-side instance inhabits the substituted "
        ++ "continuation type."
      sourceProves := false
      construction := "Framework/GeneratedModality.lean: relyPossibly_elim"
      provedTheorem := "Framework/GeneratedModality.lean: relyPossibly_elim "
        ++ "yields some continuation-satisfying successor, not the source's "
        ++ "specified right-hand-side instance"
      instanceWitness := "Framework/GeneratedHypercubeInstances.lean"
      negativeControl := "Framework/GeneratedModality.lean: "
        ++ "relyPossibly_mono_result"
      audited := true
      standing := .constructedHere }
  , { chapter := 19
      citation := "Section 19.6, sort slots and the equational center"
      statement :=
        "Each generated modality has one sort slot per rely input and one for "
        ++ "its output; preservation of the equational axioms and base rewrite "
        ++ "laws cuts the assignment cube down to an equational center."
      sourceProves := false
      construction := "Framework/ModalHypercube.lean: ModalPresentation / "
        ++ "equationalCenter; Framework/GeneratedHypercube.lean: "
        ++ "derivedAdmissible / derivedPresentation / derivedCenter"
      provedTheorem := "Framework/ModalHypercube.lean: "
        ++ "equationalCenter_subset proves only that the computed filter is "
        ++ "a subset of the raw cube. The analyzer ignores uninterpreted "
        ++ "obligations and does not check all base rewrite laws; no source "
        ++ "admissibility soundness/completeness theorem is established"
      instanceWitness := "Framework/GeneratedHypercubeInstances.lean: "
        ++ "rhoComm_center_card"
      negativeControl := "Framework/GeneratedHypercubeInstances.lean: "
        ++ "rhoComm_square_needs_two_conditions"
      audited := true
      standing := .constructedHere }
  , { chapter := 19
      citation := "Remark 19.1"
      statement :=
        "The Hypercube algorithm generates a type system and offers no "
        ++ "adequacy theorem for it; type systems are not generally adequate "
        ++ "for the calculi they type."
      sourceProves := true
      construction := "Framework/EnumeratedAdequacy.lean -- every adequacy "
        ++ "result here carries an explicit enumeration hypothesis, and no "
        ++ "unconditional adequacy is claimed for a generated type system"
      provedTheorem := "", instanceWitness := ""
      negativeControl := "Framework/ImageFinite.lean -- a counterexample "
        ++ "shows the sufficient finitary adequacy hypothesis cannot simply "
        ++ "be dropped from the unrestricted theorem"
      audited := true
      standing := .respectedHere }
  , { chapter := 19
      citation := "Remark 19.2"
      statement := "Adequate for what: the observation index is a parameter of "
        ++ "any adequacy claim, not a constant."
      sourceProves := true
      construction := "Framework/IndexedOperationalAdequacy.lean and "
        ++ "Framework/EnumeratedAdequacy.lean: every adequacy statement here "
        ++ "carries its observation index rather than leaving it implicit"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 19
      citation := "Remark 19.3"
      statement := "The generated modality's relationship to the interaction "
        ++ "cut."
      sourceProves := true
      construction := "Framework/GeneratedModalFamily.lean: mem_redexSites_iff "
        ++ "-- the site enumeration is the set of redex positions rather than a "
        ++ "selection from it, with root_site_mem showing no rule is skipped.  "
        ++ "The remark says the interaction cut is the special case that "
        ++ "privileges a family of positions and that the algorithm is what one "
        ++ "gets by not privileging them; the coverage theorem is that "
        ++ "non-privileging, proved rather than assumed"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .respectedHere }
  , { chapter := 19
      citation := "Remark 19.4"
      statement :=
        "What a specification must supply: the connectives of a generated "
        ++ "logic are determined by the classifying theory's own structure, so "
        ++ "a theory with finite limits and no more yields a conjunctive "
        ++ "fragment, and a property may fail to elaborate for that reason "
        ++ "rather than because it is false."
      sourceProves := true
      construction := "Framework/GSLTTypeSynthesis.lean constructs the full "
        ++ "invariant-predicate frame. A generator parameterized by the "
        ++ "chosen categorical/connective fragment is not established"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .openHere }
  , { chapter := 19
      citation := "Remark 19.5"
      statement := "Why the Lambda calculus needed no equational center."
      sourceProves := true
      construction := "Framework/ModalHypercube.lean and "
        ++ "Framework/GeneratedHypercubeInstances.lean: the fixed-channel "
        ++ "face is computed for the authored rule. rhoCommPaperSquare "
        ++ "instead fixes the output slot, not the source's channel slot; "
        ++ "equal cardinality alone does not identify the source face"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .constructedHere }
  , { chapter := 19
      citation := "Remark 19.6"
      statement := "Adequacy and checkability pull against each other."
      sourceProves := true
      construction := ""
      provedTheorem := ""
      instanceWitness := ""
      negativeControl := ""
      audited := true
      standing := .openHere }
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
        ++ "subtermAt / plug"
      provedTheorem := "Framework/RedexPosition.lean: position enumeration "
        ++ "soundness and completeness for the binder-free fragment, not a "
        ++ "minimal enabling-context universal property"
      instanceWitness := "Languages/ProcessCalculi/RhoCalculus/PlatformLabels.lean"
      negativeControl := "Syntax/ContextualSplitting.lean: shape_does_not_locate"
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
        ++ "correspondence are not discharged by this generic theorem"
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
        ++ "HMLFormula.satisfies; the diamond retains a MinimalContext label"
      provedTheorem := "GSLT/Logic/HennessyMilnerDirections.lean: "
        ++ "sat_toLabeled / hmlEquiv_iff_logicallyEquivalent / "
        ++ "contextBisimilar_iff_hmlEquiv, under explicit plug compatibility "
        ++ "and contextual image-finiteness; the source-derived enabling "
        ++ "context instance remains open"
      instanceWitness := "GSLT/Logic/HennessyMilnerDirections.lean: "
        ++ "ReductionBisimilarityCanary.inertGSLT; this is a context-label "
        ++ "separation control, not the missing presented-rho instance"
      negativeControl := "GSLT/Logic/HennessyMilnerDirections.lean: "
        ++ "ReductionBisimilarityCanary.not_hmlEquiv / "
        ++ "ReductionBisimilarityCanary.reduction_bisimilarity_insufficient"
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
        ++ "contextBisimilar_iff_hmlEquiv_of_enumeration"
      provedTheorem := "Framework/EnumeratedAdequacy.lean: "
        ++ "contextBisimilar_iff_hmlEquiv_of_enumeration, under an explicit "
        ++ "enumeration hypothesis supplying image-finiteness modulo the "
        ++ "equations, for identical-label matching. The source's "
        ++ "coinductive higher-order label-payload comparison is not "
        ++ "instantiated by this theorem"
      instanceWitness := "Languages/ProcessCalculi/RhoCalculus/PlatformLabels.lean"
      negativeControl := "Framework/ImageFinite.lean -- image-finiteness is "
        ++ "sufficient for the uniform finitary theorem; the counterexample "
        ++ "shows that omitting it without replacement is unsound, not that "
        ++ "every individual adequate system must satisfy it"
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
        ++ "-- the reading by an enumeration of the context-decorated formulae"
      provedTheorem := "Framework/LogicalMetric.lean: "
        ++ "hmlScheme_distance_eq_zero_iff_bisimilar -- for an enumeration of "
        ++ "every formula of a theory with enumerable successor classes, "
        ++ "distance zero is contextual bisimilarity; distance_eq -- on a "
        ++ "separated pair the distance is two to the minus the separating rank"
      instanceWitness := "Framework/LogicalMetric.lean: cheapFirst / "
        ++ "cheapSecond, with their ranks computed"
      negativeControl := "Framework/LogicalMetric.lean: enumeration_matters -- "
        ++ "the same questions in a different order give the same pair "
        ++ "different distances, so the enumeration is a parameter"
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
      instanceWitness := "Framework/LogicalMetric.lean: cheapFirst"
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
      construction := "Syntax/ContextualSplitting.lean: Splitting / plug"
      provedTheorem := "Syntax/ContextualSplitting.lean: "
        ++ "positionOfFibre_fibreOfPosition / fibreOfPosition_positionOfFibre "
        ++ "are record-level round trips for algebraic substitution cuts. "
        ++ "Their context field does not require exactly one hole"
      instanceWitness := "Syntax/ContextualSplitting.lean: fire_source"
      negativeControl := "Syntax/ContextualSplitting.lean: shape_does_not_locate"
      audited := true
      standing := .constructedHere }
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
      construction := "Syntax/ContextualSplitting.lean: Fire / residual"
      provedTheorem := "Syntax/ContextualSplitting.lean: fire_gives_a_step "
        ++ "requires holeCount K = 1 separately. Fire as defined does not "
        ++ "supply that condition"
      instanceWitness := "Syntax/FireSparseness.lean: liveCut_fires"
      negativeControl := "Syntax/FireSparseness.lean: deadCut_is_inert / "
        ++ "fire_is_sparse"
      audited := true
      standing := .constructedHere }
  ]

/-! ## Chapter 18 -/

/-- Chapter 18's rows: scopes, fixed points, strata and generator length. -/
def chapter18 : List Obligation :=
  [ { chapter := 18, citation := "Definition 18.1"
      statement := "A scope is a name predicate; its extension is the set of "
        ++ "names satisfying it."
      sourceProves := true
      construction := "Framework/GeneratedScope.lean / GeneratedScopeSignature.lean"
      provedTheorem := ""
      instanceWitness := "Framework/GeneratedScopeRho.lean"
      negativeControl := ""
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
      construction := "Syntax/UniqueDecompositionRepaired.lean: "
        ++ "unique_decomposition_of_disjoint_support -- uniqueness under "
        ++ "disjoint support and cover. This does not identify that condition "
        ++ "with the source's shared-name grade-zero separation"
      provedTheorem := "Syntax/UniqueDecompositionRepaired.lean: "
        ++ "unique_decomposition_of_disjoint_support, assuming disjoint support "
        ++ "and cover"
      instanceWitness := "Syntax/UniqueDecompositionRepaired.lean: "
        ++ "eq_of_countOut_eq"
      negativeControl := "Syntax/UniqueDecompositionFails.lean: "
        ++ "unique_decomposition_fails -- disjoint predicates and no steps "
        ++ "still admit two congruent splittings with differing halves. "
        ++ "No source shared-name grade-zero theorem is supplied; "
        ++ "corrected_hypothesis_excludes_the_counterexample, which shows the "
        ++ "repair is not vacuous"
      audited := true
      standing := .constructedHere }
  , { chapter := 18, citation := "Corollary 18.1"
      statement := "Under the preceding proposition's hypotheses, description "
        ++ "length is additive up to a constant and membership testing "
        ++ "decomposes."
      sourceProves := true
      construction := "No description-length theorem or counterexample is "
        ++ "established. Failure of a proposed decomposition proof does not "
        ++ "by itself refute the additivity conclusion"
      provedTheorem := ""
      instanceWitness := ""
      negativeControl := ""
      audited := true
      standing := .openHere }
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
        ++ "greatest, as Remark 18.4 insists"
      provedTheorem := "Framework/GeneratedScope.lean: scope_induction -- the "
        ++ "induction principle of the structural variant, not the source's "
        ++ "part-level atoms, drop coercion and equation-invariant cuts"
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
        ++ "subterms. Alignment with the source's coercions and cuts modulo "
        ++ "equations is not established"
      provedTheorem := "Framework/ScopeStratum.lean: stratum_quote_par and "
        ++ "stratum_join_le -- syntactic unfolding bounds, not an invariant "
        ++ "stratum for the source scope modulo equations"
      instanceWitness := "Framework/ScopeStratum.lean: stratum_tower -- every "
        ++ "stratum is inhabited, so the grading is not eventually empty"
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
        ++ "instrumentRules / ObAdmissible / AdministrativeFresh"
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
        ++ "step_of_base / step_mono / openedRules_mono"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
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
        ++ "reads_head_iff / projection_response"
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
      construction := "Framework/ObserverIdempotence.lean: equations_preserved "
        ++ "and authored_retained -- the presentation-level half, that the "
        ++ "extension adjoins and takes nothing away, so the theory being "
        ++ "calibrated is the one calibrating it.  The semantic half needs the "
        ++ "extension's step relation to respect the equations, which is not "
        ++ "established, so this row is constructed rather than proved"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Theorem 20.1"
      statement := "With admissible E and the complete observation signature, "
        ++ "observer-extension context-labeled bisimilarity coincides with "
        ++ "equality modulo E on closed authored first-order terms."
      sourceProves := true
      construction := "Framework/ObserverReconstruction.lean: ReadableByKit / "
        ++ "reconstruction / IsInstrumentBisimulation / argument_agreement"
      provedTheorem := "Framework/ObserverReconstruction.lean: reconstruction "
        ++ "-- terms related by the raw instrument bisimulation and "
        ++ "hereditarily readable by the kit are syntactically equal. The "
        ++ "principal rho readability instance is empty; calibration and "
        ++ "quotient/context-label correspondence are not established"
      instanceWitness := ""
      negativeControl := "Framework/ObserverReconstruction.lean: "
        ++ "isInstrumentBisimulation_not_total"
      audited := true
      standing := .constructedHere }
  , { chapter := 20, citation := "Remark 20.6"
      statement := "Domains: the reconstruction theorem is about a restricted "
        ++ "relation, and the restriction is part of the statement."
      sourceProves := true
      construction := "Framework/ObserverReconstruction.lean: ReadableByKit "
        ++ "names the restriction inside the theorem rather than around it, and "
        ++ "this ledger's Theorem 20.1 row is constructed rather than proved "
        ++ "precisely because that restriction has no inhabitant yet"
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
        ++ "excluded by construction rather than assumed away"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
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
      construction := "Route audited and named, not built.  Every ingredient "
        ++ "the source's proof uses is present: "
        ++ "StructuralModal/AdmissibleEquations.lean supplies Admissible with "
        ++ "leanInduction for the induction on the measure and "
        ++ "measure_lt_of_lean_singleton for the descent, plus a worked "
        ++ "admissible instance; StructuralModal/SeparatingConjunction.lean "
        ++ "supplies the structural connectives with sepConj_resp, which is the "
        ++ "easy direction's content; StructuralModal/Formula.lean supplies the "
        ++ "formula language and its satisfaction.  What is absent is the "
        ++ "characteristic formula itself and the proof that satisfaction in "
        ++ "the structural fragment respects the equations -- and building "
        ++ "either requires first choosing which fragment and which reduction "
        ++ "span, which is a design decision rather than a proof obligation"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .openHere }
  , { chapter := 20, citation := "Remark 20.9"
      statement := "What the direct proof buys."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Corollary 20.1"
      statement := "Logical correspondence, under the hypotheses of the two "
        ++ "theorems."
      sourceProves := true
      construction := "Stated under the hypotheses of the two theorems of this "
        ++ "chapter, so its route runs through both: the reconstruction "
        ++ "theorem, whose restricted fragment has no inhabitant at the "
        ++ "instantiated setting, and the structural separation theorem, whose "
        ++ "characteristic formula is not built"
      provedTheorem := "", instanceWitness := "", negativeControl := ""
      audited := true
      standing := .openHere }
  , { chapter := 20, citation := "Proposition 20.3"
      statement := "The gap is generically nonempty: a theory with two distinct "
        ++ "inert constructors has terms the authored theory cannot separate "
        ++ "and the instruments can."
      sourceProves := true
      construction := "Framework/ObserverExtension.lean: Gap"
      provedTheorem := "Framework/ObserverExtension.lean: Gap.withC_steps / "
        ++ "Gap.withD_no_step -- one raw opening request separates the chosen "
        ++ "inertPair instance. Generic authored bisimilarity and instrument "
        ++ "separation under source minimal-context labels are not proved"
      instanceWitness := "Framework/ObserverExtension.lean: "
        ++ "Gap.inertPair_no_step / Gap.inertPair_fresh"
      negativeControl := "Framework/ObserverExtension.lean: "
        ++ "Gap.collidingPair_not_fresh"
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
      construction := "Framework/ObserverBisimilarity.lean: Setting / "
        ++ "AgreeingFragment / restrict"
      provedTheorem := "Framework/ObserverBisimilarity.lean: bisimilar_iff "
        ++ "compares relations agreeing on a step-closed fragment; it does "
        ++ "not prove monotonicity under enlargement of the instrument set"
      instanceWitness := "Framework/ObserverBisimilarity.lean: "
        ++ "Instance.readings_agree"
      negativeControl := "Framework/ObserverBisimilarity.lean: "
        ++ "Instance.canStep_separates / box_not_forwardOnly -- the past "
        ++ "modality lies outside the fragment the agreement covers"
      audited := true
      standing := .openHere }
  , { chapter := 20, citation := "Conjecture 20.1"
      statement := "Partial characterization: bisimilarity in the observer "
        ++ "extension coincides with logical equivalence in the fragment of "
        ++ "the generated logic whose structural connectives are those of the "
        ++ "observation signature.  The source names three obstacles: a formula "
        ++ "may inspect an opened constructor sitting beneath an unopened one; "
        ++ "equations may relate terms whose roots lie on opposite sides of the "
        ++ "signature; and a binder may move material across an apparent "
        ++ "structural boundary.  Relativizing the reconstruction theorem "
        ++ "handles none of them."
      sourceProves := false
      construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
  , { chapter := 20, citation := "Proposition 20.5"
      statement := "Downward closure: the conjecture holds when the observation "
        ++ "signature is closed under the subterm relation of lean "
        ++ "representatives."
      sourceProves := true, construction := "", provedTheorem := ""
      audited := true
      instanceWitness := "", negativeControl := "", standing := .openHere }
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

/-- The ledger: chapters sixteen to twenty of the pinned source. -/
def ledger : List Obligation :=
  chapter16 ++ chapter17 ++ chapter18 ++ chapter19 ++ chapter20

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

/-- Every row satisfies the named-field requirements for its recorded standing.
This does not certify the mathematical adequacy of those fields. -/
theorem ledger_integrity : ledger.all rowIntegrity = true := by decide

/-- Rows entered so far, against the denominator. -/
def entered : Nat := ledger.length

theorem entered_eq : entered = 65 := by decide

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

/-- The reading with content now has a construction; its adjunction and monad
laws do not. -/
theorem proposition_19_1_is_constructed_not_proved :
    (ledger.filter (fun row => row.citation == "Proposition 19.1")).all
      (fun row => row.standing == Standing.constructedHere) = true := by decide


/-! ## What the ledger currently reports -/

/-- The five rows that are algorithm steps rather than numbered statements: the
chapter the construction turns on states its algorithm in prose. -/
def algorithmRowCitations : List String :=
  ["Section 19.4, M-FORM", "Section 19.4, M-INTRO", "Section 19.4, M-STEP",
   "Section 19.4, M-ELIM", "Section 19.6, sort slots and the equational center"]

/-- Non-algorithm rows meet the recorded sixty-row denominator. This arithmetic
does not certify exhaustive source coverage, including the separate conditions. -/
theorem numbered_entered :
    (ledger.filter
      (fun row => !algorithmRowCitations.contains row.citation)).length
        = totalObligations
      ∧ totalObligations = 60 := by
  refine ⟨by decide, by decide⟩

/-- How many rows carry each standing. -/
def countBy (st : Standing) : Nat :=
  (ledger.filter (fun row => row.standing == st)).length

/-- Exact counts of recorded standings, not a semantic completion certificate. -/
theorem standing_tally :
    countBy .provedHere = 2 ∧ countBy .constructedHere = 33
      ∧ countBy .refutedHere = 0 ∧ countBy .respectedHere = 15
      ∧ countBy .openHere = 15 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The tally accounts for every row. -/
theorem tally_is_total :
    countBy .provedHere + countBy .constructedHere + countBy .refutedHere
      + countBy .observedHere + countBy .respectedHere + countBy .openHere
      = entered := by decide

/-- No full source obligation is currently recorded as refuted. The restricted
AC1 counterexample remains cited without omitting the source's grade hypothesis. -/
theorem refuted_rows_empty :
    ledger.filter (fun row => row.standing == Standing.refutedHere) = [] := by decide


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
    auditedCount = 65 ∧ openAudited = 15 ∧ openUnaudited = 0
      ∧ openAudited + openUnaudited = countBy .openHere := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Mettapedia.OSLF.SourceLedger
