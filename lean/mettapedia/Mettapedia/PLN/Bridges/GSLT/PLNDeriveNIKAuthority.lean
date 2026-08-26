import Mettapedia.GSLT.LanguageDef.CertificateGSLTFiniteTraceAuthority
import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions

/-!
# Exact PLN.Derive articles as a GSLT/OSLF/NIK authority

This module isolates the proof-producing part of the PeTTa `PLN.Derive`
loop from its search policy.  A deduction article names three marginal
sentences, two implication sentences, their occurrence identities and
provenance stamps, and one claimed conclusion.  Replay checks all of that
structure and the exact rational truth formula before appending the conclusion
to the ordered belief state.

The rational carrier is a representation-neutral semantic waist.  It makes
replay total and suitable for an implementation independent of Lean; a
concrete numerator/denominator wire codec remains a separate boundary.  A
cast theorem joins its arithmetic to the existing real-valued PLN deduction
formula.
-/

namespace Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open MeasureTheory

set_option autoImplicit false

/-! ## Exact wire-level truth values -/

/-- An exact strength/confidence pair for deterministic semantic replay. -/
structure ExactTV where
  strength : ℚ
  confidence : ℚ
deriving DecidableEq, Repr

/-- Forget exact rational representation into the existing real-valued mirror
of PeTTa's truth-value carrier. -/
def ExactTV.toPeTTa (truth : ExactTV) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV :=
  ⟨(truth.strength : ℝ), (truth.confidence : ℝ)⟩

/-- Both coordinates lie in the closed unit interval. -/
def ExactTV.WellFormed (truth : ExactTV) : Prop :=
  0 ≤ truth.strength ∧ truth.strength ≤ 1 ∧
    0 ≤ truth.confidence ∧ truth.confidence ≤ 1

instance (truth : ExactTV) : Decidable truth.WellFormed := by
  unfold ExactTV.WellFormed
  infer_instance

/-- Exact rational version of the PLN deduction formula away from its
near-one branch. -/
def exactDeductionStrength (sAB sBC sB sC : ℚ) : ℚ :=
  sAB * sBC + (1 - sAB) * (sC - sB * sBC) / (1 - sB)

/-- The exact rational arithmetic embeds into the existing real PLN formula. -/
theorem exactDeductionStrength_cast (sAB sBC sB sC : ℚ) :
    ((exactDeductionStrength sAB sBC sB sC : ℚ) : ℝ) =
      plnDeductionStrength (sAB : ℝ) (sBC : ℝ) (sB : ℝ) (sC : ℝ) := by
  simp [exactDeductionStrength, plnDeductionStrength]

/-- Under the existing PLN screening-off context, exact rational replay is
the corresponding conditional probability whenever its four inputs represent
the four probabilities in that context. -/
theorem exactDeductionStrength_probability_sound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B C : Set Ω} (context : PLNDeductionMeasureContext μ A B C)
    (sAB sBC sB sC : ℚ)
    (hAB : μ.real (B ∩ A) / μ.real A = (sAB : ℝ))
    (hBC : μ.real (C ∩ B) / μ.real B = (sBC : ℝ))
    (hB : μ.real B = (sB : ℝ))
    (hC : μ.real C = (sC : ℝ)) :
    μ.real (C ∩ A) / μ.real A =
      ((exactDeductionStrength sAB sBC sB sC : ℚ) : ℝ) := by
  rw [pln_deduction_from_total_probability_ctx context, hAB, hBC, hB, hC]
  exact (exactDeductionStrength_cast sAB sBC sB sC).symm

/-- Fréchet lower bound for an exact conditional probability. -/
def smallestIntersectionProbability (pA pB : ℚ) : ℚ :=
  max 0 ((pA + pB - 1) / pA)

/-- Fréchet upper bound for an exact conditional probability. -/
def largestIntersectionProbability (pA pB : ℚ) : ℚ :=
  min 1 (pB / pA)

/-- Exact, decidable consistency of a conditional probability with its two
marginals. -/
def conditionalProbabilityConsistency (pA pB sAB : ℚ) : Prop :=
  0 < pA ∧
    smallestIntersectionProbability pA pB ≤ sAB ∧
    sAB ≤ largestIntersectionProbability pA pB

instance (pA pB sAB : ℚ) :
    Decidable (conditionalProbabilityConsistency pA pB sAB) := by
  unfold conditionalProbabilityConsistency
  infer_instance

/-- Exact replay of PeTTa's five-input `Truth_Deduction` on valid probability
inputs.  Inconsistent inputs are rejected rather than converted into PeTTa's
uninformative `(stv 1 0)` fallback. -/
def exactDeduction? (a b c ab bc : ExactTV) : Option ExactTV :=
  if conditionalProbabilityConsistency a.strength b.strength ab.strength ∧
      conditionalProbabilityConsistency b.strength c.strength bc.strength then
    let strength :=
      if (9999 / 10000 : ℚ) < b.strength then
        c.strength
      else
        exactDeductionStrength ab.strength bc.strength b.strength c.strength
    let confidence :=
      min a.confidence
        (min b.confidence (min c.confidence (min ab.confidence bc.confidence)))
    some ⟨strength, confidence⟩
  else
    none

/-! ## Ordered, occurrence-sensitive deduction articles -/

/-- The first exact guest uses the syllogistic fragment exercised by
`PLN.Derive`: atoms and binary implications. -/
inductive Term where
  | atom (name : Nat)
  | implication (antecedent consequent : Nat)
deriving DecidableEq, Repr

/-- One ordered belief occurrence.  Equal terms and truth values remain
distinct when their occurrence or provenance differs. -/
structure Sentence where
  occurrence : Nat
  term : Term
  truth : ExactTV
  stamp : Finset Nat
deriving DecidableEq

/-- The current ordered belief store. -/
structure State where
  beliefs : List Sentence
deriving DecidableEq

namespace State

/-- Occurrence identities are unique within an admitted state. -/
def WellFormed (state : State) : Prop :=
  (state.beliefs.map Sentence.occurrence).Nodup ∧
    ∀ sentence ∈ state.beliefs, sentence.truth.WellFormed

instance (state : State) : Decidable state.WellFormed := by
  unfold State.WellFormed
  infer_instance

/-- Append a checked conclusion chronologically. -/
def append (state : State) (sentence : Sentence) : State :=
  ⟨state.beliefs ++ [sentence]⟩

@[simp] theorem append_beliefs (state : State) (sentence : Sentence) :
    (state.append sentence).beliefs = state.beliefs ++ [sentence] :=
  rfl

end State

/-- A structural deduction article.  Premises are retained in full rather
than replaced by labels, so replay checks occurrence identity and payload. -/
structure DeductionArticle where
  atomA : Nat
  atomB : Nat
  atomC : Nat
  marginalA : Sentence
  marginalB : Sentence
  marginalC : Sentence
  linkAB : Sentence
  linkBC : Sentence
  conclusion : Sentence
deriving DecidableEq

namespace DeductionArticle

/-- Independent declarative meaning of one deduction article. -/
def Valid (article : DeductionArticle) (source : State) : Prop :=
  source.WellFormed ∧
  [ article.marginalA.occurrence, article.marginalB.occurrence,
      article.marginalC.occurrence, article.linkAB.occurrence,
      article.linkBC.occurrence ].Nodup ∧
  article.marginalA ∈ source.beliefs ∧
  article.marginalB ∈ source.beliefs ∧
  article.marginalC ∈ source.beliefs ∧
  article.linkAB ∈ source.beliefs ∧
  article.linkBC ∈ source.beliefs ∧
  article.marginalA.term = .atom article.atomA ∧
  article.marginalB.term = .atom article.atomB ∧
  article.marginalC.term = .atom article.atomC ∧
  article.linkAB.term = .implication article.atomA article.atomB ∧
  article.linkBC.term = .implication article.atomB article.atomC ∧
  Disjoint article.linkAB.stamp article.linkBC.stamp ∧
  exactDeduction? article.marginalA.truth article.marginalB.truth
      article.marginalC.truth article.linkAB.truth article.linkBC.truth =
    some article.conclusion.truth ∧
  article.conclusion.truth.WellFormed ∧
  article.conclusion.term = .implication article.atomA article.atomC ∧
  article.conclusion.stamp = article.linkAB.stamp ∪ article.linkBC.stamp ∧
  article.conclusion.occurrence ∉
    source.beliefs.map Sentence.occurrence

instance (article : DeductionArticle) (source : State) :
    Decidable (article.Valid source) := by
  unfold DeductionArticle.Valid
  infer_instance

/-- The declarative transition induced by a valid article. -/
def Step (source : State) (article : DeductionArticle) (target : State) : Prop :=
  article.Valid source ∧ target = source.append article.conclusion

instance (source : State) (article : DeductionArticle) (target : State) :
    Decidable (Step source article target) := by
  unfold Step
  infer_instance

end DeductionArticle

/-! ## Executable traces and their independent derivation judgment -/

/-- Proof-relevant chronological execution. -/
inductive Exec : State → List DeductionArticle → State → Prop where
  | nil (state : State) : Exec state [] state
  | cons {source target : State} {article : DeductionArticle}
      {rest : List DeductionArticle} :
      article.Valid source →
      Exec (source.append article.conclusion) rest target →
      Exec source (article :: rest) target

/-- Total executable replay of a deduction-article list. -/
def run : State → List DeductionArticle → Option State
  | state, [] => some state
  | state, article :: rest =>
      if article.Valid state then
        run (state.append article.conclusion) rest
      else
        none

theorem run_eq_some_iff_exec
    (source : State) (articles : List DeductionArticle) (target : State) :
    run source articles = some target ↔ Exec source articles target := by
  induction articles generalizing source target with
  | nil =>
      constructor
      · intro equal
        simp only [run, Option.some.injEq] at equal
        subst target
        exact .nil source
      · intro execution
        cases execution
        rfl
  | cons article rest inductionHypothesis =>
      by_cases valid : article.Valid source
      · constructor
        · intro accepted
          simp only [run, valid, if_true] at accepted
          exact .cons valid
            ((inductionHypothesis (source := source.append article.conclusion)
              (target := target)).mp accepted)
        · intro execution
          cases execution with
          | cons executionValid tail =>
              simp only [run, valid, if_true]
              exact (inductionHypothesis
                (source := source.append article.conclusion)
                (target := target)).mpr tail
      · constructor
        · intro accepted
          simp [run, valid] at accepted
        · intro execution
          cases execution with
          | cons executionValid tail => exact (valid executionValid).elim

/-! ## Operational GSLT and OSLF/NTT decision -/

/-- A replay configuration keeps the untrusted article stream explicit. -/
structure Machine where
  state : State
  remaining : List DeductionArticle
deriving DecidableEq

/-- One operational replay tick consumes exactly one valid article. -/
def MachineStep (source target : Machine) : Prop :=
  match source.remaining with
  | [] => False
  | article :: rest =>
      article.Valid source.state ∧
        target = ⟨source.state.append article.conclusion, rest⟩

instance (source target : Machine) : Decidable (MachineStep source target) :=
  by
    unfold MachineStep
    split <;> infer_instance

/-- The exact PLN article-replay GSLT. -/
def deriveGSLT : GSLT where
  Term := Machine
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := MachineStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Exact executable decision for the authored replay step. -/
def stepDecision : EffectiveStructure.StepDecision deriveGSLT where
  decideStep source target := decide (MachineStep source target)
  correct := by
    intro source target
    exact decide_eq_true_iff

/-- The executable decision accepts exactly the OSLF-generated exact-target
native predicate. -/
theorem decideStep_iff_ntt (source target : Machine) :
    stepDecision.decideStep source target = true ↔
      (gsltOSLF deriveGSLT).satisfies source
        (exactTargetNativeType deriveGSLT target).pred := by
  rw [stepDecision.correct,
    satisfies_exactTargetNativeType_iff_step]

/-- Every declarative article trace becomes a finite path in the operational
GSLT. -/
theorem exec_to_multistep {source target : State}
    {articles : List DeductionArticle}
    (execution : Exec source articles target) :
    deriveGSLT.MultiStep ⟨source, articles⟩ ⟨target, []⟩ := by
  induction execution with
  | nil state =>
      exact GSLT.MultiStep.refl (S := deriveGSLT) ⟨state, []⟩
  | @cons source target article rest valid tail inductionHypothesis =>
      exact .step ⟨valid, rfl⟩ inductionHypothesis

/-- The exact local decision is also a complete local OSLF step authority. -/
def localStepAuthority : StepAuthority Unit deriveGSLT where
  id := ()
  Certificate := Unit
  check := fun claim _ => stepDecision.decideStep claim.source claim.target
  sound := by
    intro claim certificate accepted
    exact (stepDecision.correct claim.source claim.target).mp accepted

theorem localStepAuthority_complete : localStepAuthority.Complete := by
  intro claim meaningful
  exact ⟨(), (stepDecision.correct claim.source claim.target).mpr meaningful⟩

/-! ## Native NIK proof system -/

/-- The authority tag names the precise kernel principle implemented here.
It neither requests nor claims authority for Lean typing or for PLN search. -/
inductive AuthorityKind where
  | exactDeductionReplay
deriving DecidableEq

/-- A finite replay claim. -/
structure Claim where
  source : State
  target : State
deriving DecidableEq

/-- The guest's native proof objects are the same chronological articles that
an external PLN search engine can emit. -/
def nativeProofSystem : NativeProofSystem Claim where
  ProofObject := List DeductionArticle
  Judges := fun proof claim => Exec claim.source proof claim.target

/-- A deterministic replay kernel for native PLN deduction articles. -/
def nativeKernel : NativeProofKernel nativeProofSystem where
  decide claim proof := decide (run claim.source proof = some claim.target)
  correct := by
    intro claim proof
    rw [decide_eq_true_iff, run_eq_some_iff_exec]
    rfl

/-- Direct replay is an exact certificate boundary: accepted certificates
and native chronological derivations are equivalent claim by claim. -/
def nativeCertificateEquivalence :
    CertificateEquivalence nativeKernel.toChecker nativeProofSystem :=
  nativeKernel.certificateEquivalence

/-- The PLN replay kernel as one ordinary NIK authority fibre. -/
def family : AuthorityFamily AuthorityKind where
  Claim := fun _ => Claim
  Certificate := fun _ => List DeductionArticle
  checker := fun _ => nativeKernel.toChecker
  Certified := fun _ claim =>
    Nonempty (nativeProofSystem.ProofFibre claim)
  Meaning := fun _ claim =>
    ∃ proof, Exec claim.source proof claim.target
  projection := fun _ =>
    { authority := nativeKernel.authority
      project := by
        intro claim certified
        rcases certified with ⟨⟨proof, judged⟩⟩
        exact ⟨proof, judged⟩ }

/-- NIK acceptance produces both the independent native derivation and its
OSLF/GSLT finite path. -/
theorem accepted_implies_exec_and_multistep
    {claim : Claim} {certificate : List DeductionArticle}
    (accepted : nativeKernel.toChecker.check claim certificate = true) :
    Exec claim.source certificate claim.target ∧
      deriveGSLT.MultiStep ⟨claim.source, certificate⟩ ⟨claim.target, []⟩ := by
  have execution := (nativeKernel.correct claim certificate).mp accepted
  exact ⟨execution, exec_to_multistep execution⟩

/-! ## Executable two-step temporal PLN chain -/

namespace TemporalCanary

def q : Nat := 0
def r : Nat := 1
def m : Nat := 2
def n : Nat := 3

def direct (positive total : ℚ) : ExactTV :=
  ⟨positive / total, total / (total + 1)⟩

def qBase : Sentence := ⟨0, .atom q, direct 9 45, ∅⟩
def rBase : Sentence := ⟨1, .atom r, direct 9 45, ∅⟩
def mBase : Sentence := ⟨2, .atom m, direct 6 45, ∅⟩
def nBase : Sentence := ⟨3, .atom n, direct 9 45, ∅⟩

def qToR : Sentence :=
  ⟨4, .implication q r, direct 7 9, {0, 1, 2, 3, 4, 5, 6}⟩

def rToM : Sentence :=
  ⟨5, .implication r m, direct 5 9, {7, 8, 9, 10, 11}⟩

def mToN : Sentence :=
  ⟨6, .implication m n, direct 1 2, {12, 13}⟩

def initial : State :=
  ⟨[qBase, rBase, mBase, nBase, qToR, rToM, mToN]⟩

/-- First derived sentence: the exact PeTTa temporal-probe value `q → m`. -/
def qToM : Sentence :=
  ⟨7, .implication q m, ⟨71 / 162, 9 / 10⟩, qToR.stamp ∪ rToM.stamp⟩

def firstArticle : DeductionArticle where
  atomA := q
  atomB := r
  atomC := m
  marginalA := qBase
  marginalB := rBase
  marginalC := mBase
  linkAB := qToR
  linkBC := rToM
  conclusion := qToM

/-- Second derived sentence genuinely consumes the first conclusion. -/
def qToN : Sentence :=
  ⟨8, .implication q n, ⟨11 / 36, 2 / 3⟩, qToM.stamp ∪ mToN.stamp⟩

def secondArticle : DeductionArticle where
  atomA := q
  atomB := m
  atomC := n
  marginalA := qBase
  marginalB := mBase
  marginalC := nBase
  linkAB := qToM
  linkBC := mToN
  conclusion := qToN

def certificate : List DeductionArticle := [firstArticle, secondArticle]

def final : State :=
  (initial.append qToM).append qToN

def claim : Claim := ⟨initial, final⟩

@[simp] theorem firstArticle_conclusion : firstArticle.conclusion = qToM :=
  rfl

@[simp] theorem secondArticle_conclusion : secondArticle.conclusion = qToN :=
  rfl

theorem firstArticle_valid : firstArticle.Valid initial := by
  norm_num [DeductionArticle.Valid, State.WellFormed, firstArticle, initial,
    qBase, rBase, mBase, nBase, qToR, rToM, mToN, qToM, q, r, m, n,
    direct, exactDeduction?, conditionalProbabilityConsistency,
    smallestIntersectionProbability, largestIntersectionProbability,
    exactDeductionStrength, ExactTV.WellFormed]

theorem secondArticle_valid :
    secondArticle.Valid (initial.append qToM) := by
  norm_num [DeductionArticle.Valid, State.WellFormed, secondArticle, initial,
    State.append, qBase, rBase, mBase, nBase, qToR, rToM, mToN, qToM,
    qToN, q, r, m, n, direct, exactDeduction?,
    conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability, exactDeductionStrength,
    ExactTV.WellFormed]

/-- Positive witness: two chronological PLN deductions replay exactly. -/
theorem certificate_accepted :
    nativeKernel.toChecker.check claim certificate = true := by
  simp [NativeProofKernel.toChecker, nativeKernel, claim, certificate, run,
    firstArticle_valid, secondArticle_valid, final]

/-- The same accepted certificate is accepted through the typed default NIK
frontend rather than by an untyped external Boolean. -/
theorem defaultNIK_accepts :
    (Frontend.typed family).run
        (⟨.exactDeductionReplay, claim, certificate⟩ : TypedSubmission family) =
      .accepted ⟨.exactDeductionReplay, claim⟩ := by
  have acceptedFamily :
      (family.checker .exactDeductionReplay).check claim certificate = true := by
    simpa [family] using certificate_accepted
  simp [Frontend.run, Frontend.typed, acceptedFamily]

/-- The accepted certificate denotes the GSLT trace generated by its two
OSLF-classified steps. -/
theorem certificate_has_oslf_trace :
    deriveGSLT.MultiStep ⟨initial, certificate⟩ ⟨final, []⟩ :=
  (accepted_implies_exec_and_multistep certificate_accepted).2

/-- The first checked strength is exactly the existing real PLN deduction
formula on the temporal example's rational inputs. -/
theorem qToM_strength_is_plnDeductionStrength :
    ((qToM.truth.strength : ℚ) : ℝ) =
      plnDeductionStrength
        ((qToR.truth.strength : ℚ) : ℝ)
        ((rToM.truth.strength : ℚ) : ℝ)
        ((rBase.truth.strength : ℚ) : ℝ)
        ((mBase.truth.strength : ℚ) : ℝ) := by
  norm_num [qToM, qToR, rToM, rBase, mBase, direct,
    plnDeductionStrength]

/-- The second checked strength is also a genuine PLN formula application,
now using the first checked conclusion as its left link. -/
theorem qToN_strength_is_plnDeductionStrength :
    ((qToN.truth.strength : ℚ) : ℝ) =
      plnDeductionStrength
        ((qToM.truth.strength : ℚ) : ℝ)
        ((mToN.truth.strength : ℚ) : ℝ)
        ((mBase.truth.strength : ℚ) : ℝ)
        ((nBase.truth.strength : ℚ) : ℝ) := by
  norm_num [qToN, qToM, mToN, mBase, nBase, direct,
    plnDeductionStrength]

/-- The first exact article agrees with Mettapedia's independently maintained
real-valued mirror of PeTTa `Truth_Deduction`. -/
theorem qToM_truth_matches_petta :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction
        qBase.truth.toPeTTa rBase.truth.toPeTTa
        mBase.truth.toPeTTa qToR.truth.toPeTTa rToM.truth.toPeTTa =
      qToM.truth.toPeTTa := by
  norm_num [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction,
    ExactTV.toPeTTa, qBase, rBase,
    mBase, qToR, rToM, qToM, direct,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.smallestIntersectionProbability,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.largestIntersectionProbability]

/-- The chained second article also agrees with the PeTTa truth function and
uses the first checked conclusion as a premise. -/
theorem qToN_truth_matches_petta :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction
        qBase.truth.toPeTTa mBase.truth.toPeTTa
        nBase.truth.toPeTTa qToM.truth.toPeTTa mToN.truth.toPeTTa =
      qToN.truth.toPeTTa := by
  norm_num [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthDeduction,
    ExactTV.toPeTTa, qBase, mBase,
    nBase, qToM, mToN, qToN, direct,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.smallestIntersectionProbability,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.largestIntersectionProbability]

/-- Mutating the first probabilistic result is rejected. -/
def wrongFirstArticle : DeductionArticle :=
  { firstArticle with
    conclusion := { qToM with truth := ⟨1 / 3, 9 / 10⟩ } }

def wrongProbabilityClaim : Claim :=
  ⟨initial, initial.append wrongFirstArticle.conclusion⟩

theorem wrongFirstArticle_invalid : ¬ wrongFirstArticle.Valid initial := by
  norm_num [DeductionArticle.Valid, State.WellFormed, wrongFirstArticle,
    firstArticle, initial, qBase, rBase, mBase, nBase, qToR, rToM, mToN,
    qToM, q, r, m, n, direct, exactDeduction?,
    conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability, exactDeductionStrength,
    ExactTV.WellFormed]

theorem wrong_probability_rejected :
    nativeKernel.toChecker.check wrongProbabilityClaim [wrongFirstArticle] = false := by
  simp [NativeProofKernel.toChecker, nativeKernel, wrongProbabilityClaim, run,
    wrongFirstArticle_invalid]

/-- A fully present right link whose stamp overlaps the left link. -/
def overlappingMToN : Sentence :=
  { mToN with stamp := {0, 12, 13} }

def overlappingInitial : State :=
  ⟨[qBase, rBase, mBase, nBase, qToR, rToM, overlappingMToN]⟩

def overlappingQToN : Sentence :=
  { qToN with stamp := qToM.stamp ∪ overlappingMToN.stamp }

def overlappingSecondArticle : DeductionArticle :=
  { secondArticle with
    linkBC := overlappingMToN
    conclusion := overlappingQToN }

def overlappingClaim : Claim :=
  ⟨overlappingInitial,
    (overlappingInitial.append qToM).append overlappingQToN⟩

theorem firstArticle_valid_in_overlappingInitial :
    firstArticle.Valid overlappingInitial := by
  norm_num [DeductionArticle.Valid, State.WellFormed, firstArticle,
    overlappingInitial, qBase, rBase, mBase, nBase, qToR, rToM,
    overlappingMToN, mToN, qToM, q, r, m, n, direct, exactDeduction?,
    conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability, exactDeductionStrength,
    ExactTV.WellFormed]

theorem overlappingSecondArticle_invalid :
    ¬ overlappingSecondArticle.Valid (overlappingInitial.append qToM) := by
  norm_num [DeductionArticle.Valid, State.WellFormed,
    overlappingSecondArticle, secondArticle, overlappingMToN,
    overlappingQToN, overlappingInitial,
    State.append, qBase, rBase, mBase, nBase, qToR, rToM, mToN, qToM,
    qToN, q, r, m, n, direct, exactDeduction?,
    conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability, exactDeductionStrength,
    ExactTV.WellFormed]

theorem overlapping_provenance_rejected :
    nativeKernel.toChecker.check overlappingClaim
      [firstArticle, overlappingSecondArticle] = false := by
  simp [NativeProofKernel.toChecker, nativeKernel, overlappingClaim, run,
    firstArticle_valid_in_overlappingInitial,
    overlappingSecondArticle_invalid]

/-- A fully present right link with the wrong middle atom. -/
def wrongRToM : Sentence :=
  { rToM with term := .implication m r }

def wrongMiddleInitial : State :=
  ⟨[qBase, rBase, mBase, nBase, qToR, wrongRToM, mToN]⟩

def wrongMiddleArticle : DeductionArticle :=
  { firstArticle with linkBC := wrongRToM }

def wrongMiddleClaim : Claim :=
  ⟨wrongMiddleInitial, wrongMiddleInitial.append qToM⟩

theorem wrongMiddleArticle_invalid :
    ¬ wrongMiddleArticle.Valid wrongMiddleInitial := by
  norm_num [DeductionArticle.Valid, State.WellFormed, wrongMiddleArticle,
    wrongMiddleInitial, wrongRToM, firstArticle, qBase, rBase, mBase,
    nBase, qToR, rToM, mToN, qToM, q, r, m, n, direct, exactDeduction?,
    conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability, exactDeductionStrength,
    ExactTV.WellFormed]

theorem wrong_middle_rejected :
    nativeKernel.toChecker.check wrongMiddleClaim [wrongMiddleArticle] = false := by
  simp [NativeProofKernel.toChecker, nativeKernel, wrongMiddleClaim, run,
    wrongMiddleArticle_invalid]

end TemporalCanary

#print axioms exactDeductionStrength_cast
#print axioms exactDeductionStrength_probability_sound
#print axioms decideStep_iff_ntt
#print axioms accepted_implies_exec_and_multistep
#print axioms TemporalCanary.certificate_accepted
#print axioms TemporalCanary.qToM_strength_is_plnDeductionStrength
#print axioms TemporalCanary.qToN_strength_is_plnDeductionStrength
#print axioms TemporalCanary.qToM_truth_matches_petta
#print axioms TemporalCanary.qToN_truth_matches_petta

end Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority
