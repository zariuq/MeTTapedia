import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.GroundableUpTo
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Changes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.TwoKinds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Survival
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.QuotientDiscipline
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.BudgetedConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Qualification

/-!
# When types apply: the map

Each row is a kind of material on the step; each column asks one question of it. Every cell cites a
theorem (checked below to exist) or says "open". Names are relative to the step's namespace
(`WhenTypesApply.*`, `Distinctions.*`, and the other folders of the step).

**Columns.** *Applies*: is there a type here, and which classes are types. *Kind*:
constructor-defined (least class closed under declared rules), finitary, fixed-point, or infinitary
only. *Survives*: the changes it is stable under. *Destroyed by*: a change that breaks it, with its
control. *Membership*: decided, groundable (found at a finite stage), refutable only (refuted at a
finite stage), or neither.

| Material | Applies | Kind | Survives | Destroyed by | Membership |
|---|---|---|---|---|---|
| **Data built from declared constructors** | Yes: the class the declared rules generate (`ThatsAll.Generated`); its closure clause holds in an open world exactly on an owned region (`ThatsAll.closedReadingSurvives_iff_owned`). | Constructor-defined: a least fixed point reached at a finite stage (`TwoKinds.generated_iff_exists_stage`). | Every growth (`TwoKinds.generated_mono`); every step through the constructors (`ThatsAll.generated_survives`); every step of another party on an owned region (`ThatsAll.publication_closedReadingSurvives`); removal by others (`ThatsAll.removing_owned`). | Another party creating a row no rule makes (`ThatsAll.adding_breaks_generated`); the closure clause, by any creation by another party (`ThatsAll.adding_overturns`, `ThatsAll.sharing_breaks_closedReading`). | Groundable: a finite stage finds every member (`TwoKinds.generated_iff_exists_stage`). Refuting needs the closure clause, sound only when owned. Decided in general: open. |
| **Functions given by equations in an open space** | Only for the positively generated classes (`Changes.step_stable_iff_positive`); "these are all its equations" is no type that survives (`Changes.onlyEquations_not_stable`). | Positively generated: unions and intersections of presence readings, no none query, no exact count (`Changes.positive_iff_generated`); the exact condition is readings a join keeps true whose order growth realizes (`Changes.stable_iff_positive_of_realizes`). | Every growth, exactly for positively generated types (`Changes.stable_iff_positive`). | A later equation (`Changes.onlyEquations_not_stable`); a later row overturns a refutation (`ThatsAll.later_row_overturns`). | "Convertible" groundable with a budget, sound, complete in the limit on normalizing terms of a Church–Rosser package (`Budgeted.check_equal`, `Budgeted.check_eventually`). "Not convertible" holds only for the current declaration (`ThatsAll.later_row_overturns`). |
| **Functions on an owned signature** | Yes, constructor-defined, closure clause sound (`ThatsAll.publication_closedReadingSurvives`; `QuotientDiscipline.published_witnessed`). | Constructor-defined. | Every step of another actor (`ThatsAll.publication_owned`; a system whose other actor acts, `ThatsAll.tSystem_other_steps`, `ThatsAll.tSystem_owned`); along runs every protected row stays derivable (`PublicationAuthority.System.run_allDerivable`). | A second writer (`QuotientDiscipline.writer_publishes_without_evidence`). | Decided on a qualified package (`Computing.Qualified.decide`); with a budget, three sound outcomes, monotone in the budget (`Budgeted.check_undecided_iff`, `Budgeted.check_mono`). |
| **Knowledge with none queries or counting** | Yes as types of a lens that reads none queries or counts (`Changes.noU_isConcept`, `Changes.exactlyOneT_isConcept`); not as types that survive growth. | Finitary, observer-defined; not positively generated (`Changes.noU_not_stable` with `Changes.step_stable_iff_positive`). | More observers (`Distinctions.ObserverConcepts.concepts_subset_iff`); growth only on an owned region (`ThatsAll.closedReadingSurvives_iff_owned`; none queries on a union holds exactly on each part, `NullsOnTheStep.Composition.none_union_iff`). | Growth by another party (`Changes.noU_not_stable`, `Changes.exactlyOneT_not_stable`, `NullsOnTheStep.Composition.none_not_monotone`); knowledge that identifies more rows changes counts (`EqualityOnTheStep.Options.Observability.conservative_iff`). | The none query decided at the store at hand by a finite search (`Changes.noU_decided`); exact counts likewise a finite check, not stated as a theorem: open. Never stable under growth (row's controls). |
| **Behaviour under a finite program** | Yes: the types are exactly the bisimulation-closed classes (`Distinctions.StepConcepts.program_isConcept_iff_bisimClosed`). Fixed-point formulas denote types exactly with positive bodies (`FixpointTypes.FixFormula.bisimClosed`; control `FixpointTypes.Controls.nonpositive_splits`). | All three, strictly: finitary when finitely determined (`Distinctions.StepConcepts.denoted_iff_finitelyDetermined`); fixed-point not finitary (`Ladder.evenReachFormula_holds`, `Distinctions.ParityBoundary.evenReach_not_denoted`); infinitary only (`Ladder.squareReach_not_fixDenoted`, `Ladder.squareReach_iformula`); together `Ladder.ladder`. On a one-letter chain fixed points are finite automata (`OneLetterChain.exists_machine`) and denote exactly the ultimately periodic sets (`OneLetterChain.denoted_iff_periodic`); on the step, a class of reaches is fixed-point denoted exactly when its reaches are ultimately periodic (`Ladder.reachClass_fixDenoted_iff`). | Possibility and necessity (`Distinctions.Survival.bisimClosed_possibility`, `Distinctions.Survival.bisimClosed_necessity`); firings exactly when invariant, and the invariant core is a type (`Changes.invariant_iff_core_eq`, `Changes.core_bisimClosed`); more observers. | A firing, when not invariant (`Changes.evenReach_not_invariant`); predecessor necessity (`Distinctions.Survival.Past.predecessor_control`). | Least fixed points of plain bodies groundable, greatest ones refutable only (`Groundable.satisfies_mu_iff_exists_stage`, `Groundable.satisfies_nu_iff_forall_stage`), on every finite program, fresh identities included, through the bisimulation quotient (`GroundableUpTo.program_mu_groundable`, `GroundableUpTo.program_nu_refutable`); "take one `T`" is image-finite on the nose (`Groundable.countingKnowledge_imageFinite`) and its even reaches groundable (`Groundable.evenReach_groundable`); the gap never decided (`Groundable.check_gap`); a finite stage never confirms a greatest fixed point (`Groundable.chain_never_confirms`). Bodies with negation or nested fixed points: open. |
| **Behaviour in general** | Yes: the infinitary types are the bisimulation-closed classes on every system (`Distinctions.StepConcepts.isConcept_iformulas_iff`), each denoted by one formula (`Distinctions.StepConcepts.exists_iformula_of_bisimClosed`). | Infinitary; the finitary types are fewer (`Distinctions.StepConcepts.finitary_converse_fails`); fixed-point types lie between (`FixpointTypes.ladder_inclusions`). Finitary adequacy on the unrestricted first-order step: open. | Forward modalities (`Distinctions.Survival.iconcept_possibility`, `Distinctions.Survival.iconcept_necessity`); invariant cores (`Changes.core_bisimClosed`). | The past (`Distinctions.Survival.Past.predecessor_control`); a firing, when not invariant. | Without image-finiteness a least fixed point is not reached at stage ω, and the check stays undecided on a member (`Groundable.stage_omega_not_enough`); the unrestricted ground step is not image-finite even up to bisimilarity (`ProgramAdequacy.base_not_imageFiniteBisimilar`). Whether another finite procedure grounds it: open. |

**Reading the map.** A type applies wherever a class is closed under the admitted observers. Whether
it can be *asserted* in an open world depends on its kind: a constructor-defined type carries a
closure clause, a none statement, sound exactly on an owned region; an observer-defined type
carries no closure clause, persists as a predicate under new observers and new instances, and loses
its list of members. Membership is groundable when the type is a least fixed point of finitely
branching rules or steps, refutable only when it is a greatest one, and neither when branching is
infinite.

The other changes a type meets: substitution keeps every type of the knowledge
(`Changes.instantiate_isConcept`); a new observer can shrink the least type of an instance
(`TwoKinds.five_least_type_shrinks`); a new instance joins the extension and the restriction to the
old instances is unchanged (`TwoKinds.extendType_restricts`); a type asserted from finitely many
examples is determined exactly when the examples cover every class (`TwoKinds.collapsed_iff`),
never on the step's counting program (`TwoKinds.countingKnowledge_never_collapses`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Map

/-! ## Every citation of the table exists -/

-- Data built from declared constructors
#check @ThatsAll.Generated
#check @ThatsAll.closedReadingSurvives_iff_owned
#check @TwoKinds.generated_iff_exists_stage
#check @TwoKinds.generated_mono
#check @ThatsAll.generated_survives
#check @ThatsAll.publication_closedReadingSurvives
#check @ThatsAll.removing_owned
#check @ThatsAll.adding_breaks_generated
#check @ThatsAll.adding_overturns
#check @ThatsAll.sharing_breaks_closedReading

-- Functions given by equations in an open space
#check @Changes.step_stable_iff_positive
#check @Changes.onlyEquations_not_stable
#check @Changes.positive_iff_generated
#check @Changes.stable_iff_positive
#check @Changes.stable_iff_positive_of_realizes
#check @Changes.noU_decided
#check @ThatsAll.later_row_overturns
#check @NativeTypesOnTheStep.Computing.Budgeted.check_equal
#check @NativeTypesOnTheStep.Computing.Budgeted.check_eventually

-- Functions on an owned signature
#check @EqualityOnTheStep.Options.QuotientDiscipline.published_witnessed
#check @EqualityOnTheStep.Options.QuotientDiscipline.writer_publishes_without_evidence
#check @ThatsAll.publication_owned
#check @ThatsAll.tSystem_other_steps
#check @ThatsAll.tSystem_owned
#check @PublicationAuthority.System.run_allDerivable
#check @GroundableUpTo.countDown_mu_groundable
#check @NativeTypesOnTheStep.Computing.Qualified.decide
#check @NativeTypesOnTheStep.Computing.Budgeted.check_undecided_iff
#check @NativeTypesOnTheStep.Computing.Budgeted.check_mono

-- Knowledge with none queries or counting
#check @Changes.noU_isConcept
#check @Changes.exactlyOneT_isConcept
#check @Changes.noU_not_stable
#check @Changes.exactlyOneT_not_stable
#check @Distinctions.ObserverConcepts.concepts_subset_iff
#check @NullsOnTheStep.Composition.none_union_iff
#check @NullsOnTheStep.Composition.none_not_monotone
#check @EqualityOnTheStep.Options.Observability.conservative_iff

-- Behaviour under a finite program
#check @Distinctions.StepConcepts.program_isConcept_iff_bisimClosed
#check @FixpointTypes.FixFormula.bisimClosed
#check @FixpointTypes.Controls.nonpositive_splits
#check @Distinctions.StepConcepts.denoted_iff_finitelyDetermined
#check @Ladder.evenReachFormula_holds
#check @Distinctions.ParityBoundary.evenReach_not_denoted
#check @Ladder.squareReach_not_fixDenoted
#check @Ladder.squareReach_iformula
#check @Ladder.ladder
#check @OneLetterChain.exists_machine
#check @OneLetterChain.denoted_iff_periodic
#check @Ladder.reachClass_fixDenoted_iff
#check @GroundableUpTo.program_mu_groundable
#check @GroundableUpTo.program_nu_refutable
#check @Distinctions.Survival.bisimClosed_possibility
#check @Distinctions.Survival.bisimClosed_necessity
#check @Changes.invariant_iff_core_eq
#check @Changes.core_bisimClosed
#check @Changes.evenReach_not_invariant
#check @Distinctions.Survival.Past.predecessor_control
#check @Groundable.satisfies_mu_iff_exists_stage
#check @Groundable.satisfies_nu_iff_forall_stage
#check @Groundable.countingKnowledge_imageFinite
#check @Groundable.evenReach_groundable
#check @Groundable.check_gap
#check @Groundable.chain_never_confirms

-- Behaviour in general
#check @Distinctions.StepConcepts.isConcept_iformulas_iff
#check @Distinctions.StepConcepts.exists_iformula_of_bisimClosed
#check @Distinctions.StepConcepts.finitary_converse_fails
#check @FixpointTypes.ladder_inclusions
#check @Distinctions.Survival.iconcept_possibility
#check @Distinctions.Survival.iconcept_necessity
#check @Groundable.stage_omega_not_enough
#check @ProgramAdequacy.base_not_imageFiniteBisimilar

-- The other changes
#check @Changes.instantiate_isConcept
#check @TwoKinds.five_least_type_shrinks
#check @TwoKinds.extendType_restricts
#check @TwoKinds.collapsed_iff
#check @TwoKinds.countingKnowledge_never_collapses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Map
