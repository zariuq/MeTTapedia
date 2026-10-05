import Mettapedia.GSLT.Logic.Views
import Mettapedia.Logic.Propositions
import Mettapedia.Computability.ComputationalTrinity
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.Controls

/-!
# Plural views of one subject: instances

The general notions (views, translations as `Factors`, what a translation
forgets as a `NonTrivialFiber`, finest views, common coarsenings and the joint
view) are in `Mettapedia.GSLT.Logic.Views`.  This module asks the pluralist
questions of particular families of views: whether some member is finest, what
each translation keeps and forgets, and on what the views agree.

A finest member is lossless for its family; it is not privileged.  Finest
members come as a class (`Finest.mutual`, `Finest.of_sameFibres`), and in an
exact trinity all three faces are finest (`TrinityFaces.Exact.finest`).  That no
member of a family is finest is a stronger claim; it holds of the proposition
legs and of the table runs.  Restricting the subject to a fragment, a carve-out
in the sense of `Mettapedia.GSLT.Logic.ObserverBubble`, can make incomparable
views coincide: below, the type and the truth view of propositions on the
fragment without disjunction (`type_truth_coincide_on_fragment`), and the Lisp
and the PeTTa run on deterministic tables (`lispRun_eq_pettaRun`).

## Instances, each with what holds and what fails

* **Propositions** (`Mettapedia.Logic.Propositions`).  The Fregean and the
  Russellian leg are each not finest: in Evans's zip example one Fregean
  proposition has two Russellian ones (`julius_fregean_not_finest`), and in
  Frege's morning star one Russellian proposition has two Fregean ones
  (`morningStar_russellian_not_finest`); no leg is finest for every
  interpretation (`no_leg_finest_everywhere`).  Each keeps a feature the other
  forgets: being a priori, being necessary (`legs_keep_different_features`).
  Truth at the actual scenario is a common coarsening
  (`trueIn_commonCoarsening`), and the enriched proposition has the bubble of
  the joint view (`ker_joint_legs`).  Contrast: on the verification axis
  (code, type of proofs, truth value) the views form a chain, and the code is
  finest, that is lossless on the axis (`data_finest`), while the other two are
  not (`type_not_finest`, `truth_not_finest`); on the fragment without
  disjunction the type and the truth view coincide
  (`type_truth_coincide_on_fragment`).
* **The computational trinity** (`Mettapedia.Computability.ComputationalTrinity`).
  In a comparison the spatial view of programs is a function of the logical one
  (`factors_logic_space`), and losing program information is a non-trivial
  fibre of the spatial view (`losesProgramInformation_iff`).  In an exact
  trinity every face is finest (`Exact.finest`): each face can serve as the
  pivot without loss.  Negative example: the first-bit comparison, whose
  spatial face is not finest (`firstBit_space_not_finest`).
* **A value equal to its own negation.**  In the p-bit view of PLN evidence
  (`Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit`, Belnap's four values,
  with the swap of positive and negative evidence as negation) the equation
  `c = ¬c` has models, exactly the evidence with equal positive and negative
  parts (`cdNeg_eq_self_iff`): the `both` and the `neither` evidence
  (`isBoth_or_isNeither_of_cdNeg_eq_self`).  On the same carrier read as a
  Heyting algebra it has none (`compl_ne_self_evidence`); neither in the two
  classical truth values, nor in propositions (`not_eq_self_prop`, a proof that
  uses no axiom), nor among the truth values of the classical set tower, where
  no truth value equals its implication to a false consequent
  (`TowerInterpretation.truthCode_ne_imp_false`, the fact by which a definition
  `c = imp c Q` with `Q` false has no set model,
  `TowerInterpretation.equals_own_negation_no_setModel`).  All of it is
  `refutation_is_view_relative`.  A translation that preserves negation
  carries a model along (`selfNegating_map`), so the p-bit view has no
  negation-preserving translation into any of the others
  (`pBit_not_into_classical`, `pBit_not_into_propositions`,
  `pBit_not_into_heyting`), while the classical view embeds into it
  (`classicalEmbedding_negation`, `classicalEmbedding_injective`).
* **Execution as a view** (the Lisp and PeTTa table interpreters of
  `Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin`).  The Lisp program runs
  every table on every configuration and returns the first matching row's
  successor (`lisp_runs_every_table`): running is defined for all tables, yet
  running alone does not keep a table's structure.  Seen as views of tables,
  the Lisp run and the PeTTa equation run coincide on deterministic tables
  (`lispRun_eq_pettaRun`), where every modal formula of the Lisp run is a
  feature of the PeTTa term (`factors_term_formula`).  Without determinism they
  are incomparable (`runs_incomparable`): the Lisp run forgets a second answer
  (`lispRun_forgets_choices`) and the PeTTa run forgets row order
  (`pettaRun_forgets_order`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ViewPluralism

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.QuotientObservers

universe u v w x

/-! ## Propositions: the Fregean and the Russellian leg -/

namespace PropositionLegs

open Mettapedia.Logic.Propositions

/-- The two legs of what a sentence expresses: its sense and its reference. -/
inductive Leg
  | fregean
  | russellian
  deriving DecidableEq

/-- What each leg takes a sentence to. -/
abbrev Leg.Carrier (S W D : Type u) : Leg → Type u
  | .fregean => FregeanProposition S D
  | .russellian => RussellianProposition W D

variable {S W D : Type u} {N : Type v} {P : Type w}

/-- The two legs as a family of views of sentences. -/
def legs (I : Interpretation S W D N P) (actual : S) :
    (leg : Leg) → Sentence N P → Leg.Carrier S W D leg
  | .fregean => I.fregean
  | .russellian => I.russellian actual

/-- **The legs agree on actual truth**: truth at the actual scenario is a
common coarsening of the two legs. -/
theorem trueIn_commonCoarsening (I : Interpretation S W D N P) (actual : S) :
    CommonCoarsening (legs I actual) (I.TrueIn actual)
  | .fregean =>
      Factors.of_coarsening (fine := I.fregean) (coarsen := FregeanProposition.scenarios)
        (fun sentence => (I.scenarios_fregean sentence).symm) (I.factors_primary_trueIn actual)
  | .russellian =>
      Factors.of_coarsening (fine := I.russellian actual) (coarsen := RussellianProposition.worlds)
        (fun sentence => (I.worlds_russellian actual sentence).symm)
        (I.factors_secondary_trueIn actual)

/-- The enriched proposition determines both legs. -/
theorem factors_enriched_legs (I : Interpretation S W D N P) (actual : S) :
    ∀ leg, Factors (I.enriched actual) (legs I actual leg)
  | .fregean => ⟨EnrichedProposition.fregean, I.fregean_enriched actual⟩
  | .russellian => ⟨EnrichedProposition.russellian, I.russellian_enriched actual⟩

/-- **The enriched proposition is the joint view of the two legs**: the two
have one bubble. -/
theorem ker_joint_legs (I : Interpretation S W D N P) (actual : S) :
    Setoid.ker (joint (legs I actual)) = Setoid.ker (I.enriched actual) := by
  rw [I.ker_enriched_eq_inf actual]
  ext first second
  rw [ker_joint_iff, Setoid.inf_iff_and]
  constructor
  · intro same
    exact ⟨same .fregean, same .russellian⟩
  · rintro ⟨fregeanSame, russellianSame⟩ leg
    cases leg
    · exact fregeanSame
    · exact russellianSame

/-- The witness in Evans's zip example: one Fregean proposition, two
Russellian ones. -/
def juliusFiber :
    NonTrivialFiber Julius.interpretation.fregean (Julius.interpretation.russellian .judsonDid) :=
  ⟨Julius.invented, Julius.actualInventor, Julius.fregean_eq, Julius.russellian_ne⟩

/-- **The Fregean leg is not finest** in the zip example. -/
theorem julius_fregean_not_finest : ¬ Finest (legs Julius.interpretation .judsonDid) .fregean :=
  not_finest_of_fiber _ .russellian juliusFiber

/-- The witness in Frege's puzzle: one Russellian proposition, two Fregean
ones. -/
def morningStarFiber :
    NonTrivialFiber (MorningStar.interpretation.russellian .oneBody)
      MorningStar.interpretation.fregean :=
  ⟨MorningStar.identity, MorningStar.selfIdentity, MorningStar.russellian_identity_eq,
    MorningStar.fregean_identity_ne⟩

/-- **The Russellian leg is not finest** in Frege's puzzle. -/
theorem morningStar_russellian_not_finest :
    ¬ Finest (legs MorningStar.interpretation .oneBody) .russellian :=
  not_finest_of_fiber _ .fregean morningStarFiber

/-- **No leg is finest for every interpretation.** -/
theorem no_leg_finest_everywhere (leg : Leg) :
    ¬ ∀ (S W D N P : Type) (I : Interpretation S W D N P) (actual : S),
      Finest (legs I actual) leg := by
  cases leg
  · exact fun all => julius_fregean_not_finest (all _ _ _ _ _ Julius.interpretation .judsonDid)
  · exact fun all =>
      morningStar_russellian_not_finest (all _ _ _ _ _ MorningStar.interpretation .oneBody)

/-- **Each leg keeps a feature the other forgets**: being a priori is a feature
of Fregean propositions and not of Russellian ones, being necessary the
reverse. -/
theorem legs_keep_different_features :
    (∀ {S W D N P : Type} (I : Interpretation S W D N P), Factors I.fregean I.APriori) ∧
      ¬ Factors (MorningStar.interpretation.russellian .oneBody)
        MorningStar.interpretation.APriori ∧
      (∀ {S W D N P : Type} (I : Interpretation S W D N P) (actual : S),
        Factors (I.russellian actual) (I.Necessary actual)) ∧
      ¬ Factors Julius.interpretation.fregean (Julius.interpretation.Necessary .judsonDid) :=
  ⟨fun I => I.factors_fregean_aPriori, MorningStar.not_factors_russellian_aPriori,
    fun I actual => I.factors_russellian_necessary actual, Julius.not_factors_fregean_necessary⟩

end PropositionLegs

/-! ## Negative example: the verification axis is a chain -/

namespace VerificationReadings

open Mettapedia.Logic.Propositions.Verification
open Mettapedia.TypeTheory.Calculi.BooleanSTLC

/-- How much of a proposition's verification a reading keeps. -/
inductive Reading
  | data
  | type
  | truth
  deriving DecidableEq

abbrev Reading.Carrier : Reading → Type
  | .data => PropCode
  | .type => Quotient proofTypeSetoid
  | .truth => Prop

/-- The three readings of a proposition code. -/
def readings : (reading : Reading) → PropCode → reading.Carrier
  | .data => id
  | .type => asType
  | .truth => asTruth

/-- **The code is finest**: on this axis it loses nothing.  Any reading with its
bubble would be finest as well (`Finest.of_sameFibres`), so this is
losslessness, not privilege. -/
theorem data_finest : Finest readings .data :=
  fun reading => ⟨readings reading, fun _ => rfl⟩

/-- The type of proofs is not finest: `⊤` and `⊤ ∧ ⊤` have one type and two
codes. -/
theorem type_not_finest : ¬ Finest readings .type :=
  not_finest_of_fiber _ .data
    (NonTrivialFiber.ofDetermined (feature := Mettapedia.GSLT.QuotientObservers.isTopCode)
      (view := readings .data) ⟨Mettapedia.GSLT.QuotientObservers.isTopCode, fun _ => rfl⟩
      isTopCodeFiber)

/-- The truth value is not finest: `⊤` and `⊤ ∨ ⊤` are both true, and only the
first has a unique proof. -/
theorem truth_not_finest : ¬ Finest readings .truth :=
  not_finest_of_fiber _ .type
    (NonTrivialFiber.ofDetermined (feature := ProofUnique) (view := readings .type)
      factors_asType_proofUnique proofUniqueFiber)

/-- **Carved to the fragment without disjunction, the type and the truth view
coincide**: two codes of the fragment have one type exactly when they have one
truth value. -/
theorem type_truth_coincide_on_fragment {P Q : PropCode} (inP : P.InFragment)
    (inQ : Q.InFragment) : readings .type P = readings .type Q ↔ readings .truth P = readings .truth Q :=
  Quotient.eq.trans ((sameProofType_iff_of_inFragment inP inQ).trans propext_iff.symm)

end VerificationReadings

/-! ## The computational trinity -/

namespace TrinityFaces

open _root_.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity

variable {Context : Type u} [Category.{v} Context]

/-- The three faces of a comparison. -/
inductive Face
  | program
  | logic
  | space
  deriving DecidableEq

/-- What each face makes of a program at a context. -/
abbrev Face.Carrier (comparison : Comparison.{u, v, w} Context) (context : Contextᵒᵖ) :
    Face → Type w
  | .program => comparison.program.obj context
  | .logic => comparison.logic.obj context
  | .space => comparison.space.obj context

/-- The faces as views of the programs at a context. -/
def faces (comparison : Comparison.{u, v, w} Context) (context : Contextᵒᵖ) :
    (face : Face) → comparison.program.obj context → Face.Carrier comparison context face
  | .program => id
  | .logic => fun program => comparison.programToLogic.app context program
  | .space => fun program => comparison.programToSpace.app context program

/-- **In a comparison the spatial view is a function of the logical view.** -/
theorem factors_logic_space (comparison : Comparison.{u, v, w} Context) (context : Contextᵒᵖ) :
    Factors (faces comparison context .logic) (faces comparison context .space) :=
  ⟨fun logic => comparison.logicToSpace.app context logic, comparison.coherence_apply context⟩

/-- **Losing program information is a non-trivial fibre of the spatial view.** -/
theorem losesProgramInformation_iff (comparison : Comparison.{u, v, w} Context) :
    comparison.LosesProgramInformation ↔
      ∃ context, Nonempty (NonTrivialFiber (faces comparison context .space)
        (faces comparison context .program)) := by
  constructor
  · rintro ⟨context, left, right, distinct, same⟩
    exact ⟨context, ⟨⟨left, right, same, distinct⟩⟩⟩
  · rintro ⟨context, ⟨fiber⟩⟩
    exact ⟨context, fiber.left, fiber.right, fiber.differentValue, fiber.sameShadow⟩

/-- **In an exact trinity every face is finest**: each face can serve as the
pivot without loss. -/
theorem Exact.finest (trinity : Exact.{u, v, w} Context) (context : Contextᵒᵖ) (face : Face) :
    Finest (faces trinity.toComparison context) face := by
  have logicBijective : Function.Bijective (faces trinity.toComparison context .logic) :=
    (trinity.programLogic.app context).toEquiv.bijective
  have spaceBijective : Function.Bijective (faces trinity.toComparison context .space) :=
    trinity.programToSpace_bijective context
  have programBijective : Function.Bijective (faces trinity.toComparison context .program) :=
    Function.bijective_id
  have bijective : ∀ face, Function.Bijective (faces trinity.toComparison context face)
    | .program => programBijective
    | .logic => logicBijective
    | .space => spaceBijective
  intro other
  let equivalence := Equiv.ofBijective _ (bijective face)
  exact ⟨fun shadow => faces trinity.toComparison context other (equivalence.symm shadow),
    fun program => congrArg _ (equivalence.symm_apply_apply program)⟩

/-- **The spatial face of the first-bit comparison is not finest.** -/
theorem firstBit_space_not_finest :
    ¬ Finest (faces FirstBitObservation.comparison
      (Opposite.op (Discrete.mk PUnit.unit))) .space := by
  obtain ⟨context, ⟨fiber⟩⟩ :=
    (losesProgramInformation_iff _).mp FirstBitObservation.comparison_losesProgramInformation
  have unique : context = Opposite.op (Discrete.mk PUnit.unit) := rfl
  subst unique
  exact not_finest_of_fiber _ .program fiber

end TrinityFaces

/-! ## A value equal to its own negation -/

namespace OwnNegation

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding (truthCode)

/-- **In the p-bit view, `c = ¬c` holds exactly of evidence with equal positive
and negative parts.** -/
theorem cdNeg_eq_self_iff (e : BinaryEvidence) : ∼e = e ↔ e.pos = e.neg := by
  constructor
  · intro same
    exact (congrArg BinaryEvidence.pos same).symm
  · intro equal
    exact BinaryEvidence.ext' equal.symm equal

/-- The models of `c = ¬c` are the `both` and the `neither` evidence. -/
theorem isBoth_or_isNeither_of_cdNeg_eq_self {e : BinaryEvidence} (same : ∼e = e) :
    isBoth e ∨ isNeither e := by
  have equal := (cdNeg_eq_self_iff e).mp same
  by_cases zero : e.pos = 0
  · exact .inr ⟨zero, equal ▸ zero⟩
  · have positive : 0 < e.pos := pos_iff_ne_zero.mpr zero
    exact .inl ⟨positive, equal ▸ positive⟩

theorem pTrue_ne_pFalse : pTrue ≠ pFalse := fun same => by
  have := congrArg BinaryEvidence.pos same
  simp [pTrue, pFalse] at this

/-- **On the same carrier read as a Heyting algebra, no evidence equals its
complement.** -/
theorem compl_ne_self_evidence (e : BinaryEvidence) : eᶜ ≠ e :=
  haveI : Nontrivial BinaryEvidence := ⟨⟨pTrue, pFalse, pTrue_ne_pFalse⟩⟩
  compl_ne_self

/-- No proposition is its own negation; the proof is intuitionistic. -/
theorem not_eq_self_prop (P : Prop) : (¬ P) ≠ P := fun same =>
  iff_not_self (Eq.to_iff same).symm

theorem not_ne_self_bool (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

/-- **Whether `c = ¬c` has a model depends on the view.**  It has one among
p-bits with their own negation; none on the same carrier read as a Heyting
algebra, none in the two classical truth values, none among propositions, and
none among the truth values of the set tower, where `¬c` is `c` implying a
false consequent. -/
theorem refutation_is_view_relative :
    (∃ e : BinaryEvidence, ∼e = e) ∧ (∀ e : BinaryEvidence, eᶜ ≠ e) ∧
      (∀ b : Bool, (!b) ≠ b) ∧ (∀ P : Prop, (¬ P) ≠ P) ∧
      (∀ P Q : Prop, ¬ Q → truthCode.{u} P ≠ truthCode (P → Q)) :=
  ⟨⟨pBoth, cdNeg_pBoth⟩, compl_ne_self_evidence, not_ne_self_bool, not_eq_self_prop,
    truthCode_ne_imp_false⟩

/-- **A translation that preserves negation carries a model of `c = ¬c`
along.** -/
theorem selfNegating_map {T : Sort u} {T' : Sort v} {negate : T → T} {negate' : T' → T'}
    {translate : T → T'} (commutes : ∀ c, translate (negate c) = negate' (translate c)) {c : T}
    (same : negate c = c) : negate' (translate c) = translate c := by
  rw [← commutes, same]

theorem no_negation_preserving_translation {T : Sort u} {T' : Sort v} {negate : T → T}
    {negate' : T' → T'} (model : ∃ c, negate c = c) (noModel : ∀ c', negate' c' ≠ c') :
    ¬ ∃ translate : T → T', ∀ c, translate (negate c) = negate' (translate c) := by
  rintro ⟨translate, commutes⟩
  obtain ⟨c, same⟩ := model
  exact noModel _ (selfNegating_map commutes same)

/-- **The p-bit view has no negation-preserving translation into the classical
truth values.** -/
theorem pBit_not_into_classical : ¬ ∃ translate : BinaryEvidence → Bool,
    ∀ e, translate (∼e) = !(translate e) :=
  no_negation_preserving_translation ⟨pBoth, cdNeg_pBoth⟩ not_ne_self_bool

/-- ... nor into propositions ... -/
theorem pBit_not_into_propositions : ¬ ∃ translate : BinaryEvidence → Prop,
    ∀ e, translate (∼e) = ¬ (translate e) :=
  no_negation_preserving_translation ⟨pBoth, cdNeg_pBoth⟩ not_eq_self_prop

/-- ... nor into its own carrier read as a Heyting algebra. -/
theorem pBit_not_into_heyting : ¬ ∃ translate : BinaryEvidence → BinaryEvidence,
    ∀ e, translate (∼e) = (translate e)ᶜ :=
  no_negation_preserving_translation ⟨pBoth, cdNeg_pBoth⟩ compl_ne_self_evidence

/-- The classical truth values inside the p-bits: the `true` and the `false`
corner. -/
def classicalEmbedding : Bool → BinaryEvidence
  | true => pTrue
  | false => pFalse

/-- **The classical view embeds into the p-bit view, preserving negation.** -/
theorem classicalEmbedding_negation (b : Bool) :
    classicalEmbedding (!b) = ∼(classicalEmbedding b) := by
  cases b
  · exact cdNeg_pFalse.symm
  · exact cdNeg_pTrue.symm

theorem classicalEmbedding_injective : Function.Injective classicalEmbedding := by
  intro first second same
  cases first <;> cases second
  · rfl
  · exact absurd same.symm pTrue_ne_pFalse
  · exact absurd same pTrue_ne_pFalse
  · rfl

end OwnNegation

/-! ## Execution as a view: Lisp and PeTTa table runs -/

namespace ExecutionViews

open Mettapedia.Languages.TuringMachine (Machine Configuration Transition)
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.IterationBisimulation
open Mettapedia.GSLT.HennessyMilner

/-- Running a table as an ordinary Lisp program: one complete invocation per
step. -/
def lispRun (machine : Machine) : Configuration → Configuration → Prop :=
  IterationStep machine

/-- Running a table by PeTTa equations, between configurations. -/
def pettaRun (machine : Machine) : Configuration → Configuration → Prop :=
  fun source target =>
    Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Tables.EquationStep machine
      source.term target.term

/-- **The Lisp program runs every table on every configuration**, returning the
successor by the first matching row, or nothing. -/
theorem lisp_runs_every_table (machine : Machine) (configuration : Configuration) :
    Mettapedia.Languages.Chaitin.GSLT.theory.MultiStep
      (Mettapedia.Languages.Chaitin.GSLT.start
        (Mettapedia.Languages.Chaitin.GSLT.TableIteration.program machine configuration))
      (Mettapedia.Languages.Chaitin.GSLT.result
        (Mettapedia.Languages.Chaitin.GSLT.TableIteration.outcome (machine.next? configuration))) :=
  (Mettapedia.Languages.Chaitin.GSLT.TableIteration.returns_iff _ _ _).mpr rfl

/-- **On deterministic tables the two runs coincide.** -/
theorem lispRun_eq_pettaRun (machine : Machine) (deterministic : machine.Deterministic) :
    lispRun machine = pettaRun machine :=
  funext fun source => funext fun target =>
    propext (iterationStep_equationStep_iff machine deterministic source target)

/-- **On deterministic tables every modal formula of the Lisp run is a feature
of the PeTTa term.** -/
theorem factors_term_formula (machine : Machine) (deterministic : machine.Deterministic)
    (formula : Formula Configuration Unit) :
    Factors Configuration.term ((sourceSystem machine).sat formula) :=
  ⟨(targetSystem machine).sat formula,
    fun source => propext (formula_iff machine deterministic formula source).symm⟩

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Controls (oneRow twoChoices)
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.Controls (written otherWrite)

/-- The table with two choices, its rows in the other order. -/
def swappedChoices : Machine :=
  ⟨[⟨0, 0, 2, .right, 1⟩, ⟨0, 0, 1, .right, 1⟩]⟩

/-- The first-match run of the table with two choices is the run of its first
row alone. -/
theorem next?_twoChoices : twoChoices.next? = oneRow.next? := by
  funext configuration
  cases matching : (0 == configuration.state && 0 == configuration.scanned) <;>
    simp [Machine.next?, Machine.entryFor, twoChoices, oneRow, List.find?, matching]

/-- **The Lisp run forgets a second answer**: the table with two choices and its
first row alone have one Lisp run and two PeTTa runs. -/
def lispRun_forgets_choices : NonTrivialFiber lispRun pettaRun where
  left := twoChoices
  right := oneRow
  sameShadow := funext fun source => funext fun target => propext <| by
    simp only [lispRun, iterationStep_iff, next?_twoChoices]
  differentValue := fun same => by
    have answer : pettaRun twoChoices Configuration.blank otherWrite :=
      Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.Controls.first_match_rejects_second_choice.2.2
    rw [same] at answer
    exact Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.Controls.wrong_write_rejected
      ((iterationStep_equationStep_iff oneRow (by decide) _ _).mpr answer)

/-- **The PeTTa run forgets row order**: the table with two choices and its
swap have one PeTTa run and two Lisp runs. -/
def pettaRun_forgets_order : NonTrivialFiber pettaRun lispRun where
  left := twoChoices
  right := swappedChoices
  sameShadow := funext fun source => funext fun target => propext <| by
    simp only [pettaRun,
      Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Tables.equationStep_configuration_iff,
      twoChoices, swappedChoices, List.mem_cons, List.mem_nil_iff, or_false]
    constructor
    · rintro ⟨entry, member, applies, rfl⟩
      exact ⟨entry, member.symm, applies, rfl⟩
    · rintro ⟨entry, member, applies, rfl⟩
      exact ⟨entry, member.symm, applies, rfl⟩
  differentValue := fun same => by
    have swapped : lispRun swappedChoices Configuration.blank otherWrite :=
      (iterationStep_iff _ _ _).mpr (by decide)
    rw [← same] at swapped
    exact Mettapedia.Languages.MeTTa.PeTTa.Bridges.Chaitin.Controls.first_match_rejects_second_choice.2.1
      swapped

/-- **Without determinism the two runs are incomparable views of tables.** -/
theorem runs_incomparable : ¬ Factors lispRun pettaRun ∧ ¬ Factors pettaRun lispRun :=
  ⟨lispRun_forgets_choices.not_factors, pettaRun_forgets_order.not_factors⟩

end ExecutionViews

/-! ## Axiom audit -/

#print axioms PropositionLegs.trueIn_commonCoarsening
#print axioms PropositionLegs.ker_joint_legs
#print axioms PropositionLegs.no_leg_finest_everywhere
#print axioms PropositionLegs.legs_keep_different_features
#print axioms VerificationReadings.data_finest
#print axioms VerificationReadings.type_not_finest
#print axioms VerificationReadings.truth_not_finest
#print axioms VerificationReadings.type_truth_coincide_on_fragment
#print axioms TrinityFaces.losesProgramInformation_iff
#print axioms TrinityFaces.Exact.finest
#print axioms TrinityFaces.firstBit_space_not_finest
#print axioms OwnNegation.not_eq_self_prop
#print axioms OwnNegation.refutation_is_view_relative
#print axioms OwnNegation.pBit_not_into_classical
#print axioms OwnNegation.pBit_not_into_propositions
#print axioms OwnNegation.pBit_not_into_heyting
#print axioms OwnNegation.classicalEmbedding_negation
#print axioms ExecutionViews.lisp_runs_every_table
#print axioms ExecutionViews.lispRun_eq_pettaRun
#print axioms ExecutionViews.factors_term_formula
#print axioms ExecutionViews.runs_incomparable

end Mettapedia.GSLT.ViewPluralism
