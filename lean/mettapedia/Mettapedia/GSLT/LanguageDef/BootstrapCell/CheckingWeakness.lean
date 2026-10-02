import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCalculusCalibration
import Mettapedia.Logic.TheoryModel.Weakness

/-!
# The weakest kernel

The theory–model Galois connection, read at the level of checking.

* A **sentence** is a checking fact: a calculus of a presented family, a goal
  of that calculus, and a raw certificate.
* A **model** is a kernel: a Boolean checker for every calculus of the family.
* A kernel **satisfies** a checking fact when it accepts the certificate for
  the goal.
* A class of kernels is **admissible** when every kernel in it accepts every
  derivable fact, that is, every certificate that some derivation erases to.

The theory of a single kernel is the set of facts it accepts; such a theory
is always closed (`consequences_acceptance`).

**Main theorem** (`isWeakestAdmissible_iff_faithful`).  The theory of a kernel
is the weakest admissible theory exactly when the kernel is faithful: it
accepts precisely the derivable facts.  Admissibility is completeness, and
weakness is soundness.

**Instances.**
* The replay kernel of any family is faithful, so its theory is the weakest
  admissible one (`replayKernel_isWeakestAdmissible`).  By W3's
  `isWeakestAdmissible_iff`, its model class, the class of all complete
  kernels, is the largest admissible elementary class.
* For validated calculi, the replay kernel is the generic inference checker
  (`checkRawKernel_isWeakestAdmissible`).

**Controls**, on the modus ponens package.
* A kernel that also accepts one non-derivable fact is admissible but not
  weakest (`tooStrong_admissible`, `tooStrong_not_weakest`).
* A kernel that rejects everything is not admissible
  (`rejectAll_not_admissible`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell.CheckingWeakness

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Logic.TheoryModel

universe u

variable {Index : Type} (calculus : Index → ReplaySignature.{u})

/-- A checking fact: a calculus, a goal of it, and a raw certificate. -/
structure CheckingFact where
  index : Index
  goal : (calculus index).Goal
  certificate : RawProof

/-- A kernel checks every calculus of the family. -/
abbrev Kernel := (index : Index) → (calculus index).Goal → RawProof → Bool

/-- A kernel satisfies a checking fact when it accepts the certificate for the
goal. -/
def Accepts (kernel : Kernel calculus) (fact : CheckingFact calculus) : Prop :=
  kernel fact.index fact.goal fact.certificate = true

/-- The facts that some derivation erases to. -/
def Derivable : Set (CheckingFact calculus) :=
  {fact | ∃ derivation : (calculus fact.index).Deriv fact.goal,
    derivation.erase = fact.certificate}

/-- Admissible classes of kernels: every kernel of the class accepts every
derivable fact. -/
def Admissible : Set (Set (Kernel calculus)) :=
  entailing (Accepts calculus) (Derivable calculus)

/-- The facts a kernel accepts. -/
def acceptedFacts (kernel : Kernel calculus) : Set (CheckingFact calculus) :=
  {fact | Accepts calculus kernel fact}

/-- A kernel is faithful when it accepts exactly the derivable facts. -/
def Faithful (kernel : Kernel calculus) : Prop :=
  ∀ fact, Accepts calculus kernel fact ↔ fact ∈ Derivable calculus

/-- The replay kernel of the family. -/
def replayKernel : Kernel calculus := fun index => (calculus index).replay

theorem replayKernel_faithful : Faithful calculus (replayKernel calculus) :=
  fun fact => ReplaySignature.replay_iff fact.goal fact.certificate

variable {calculus}

/-- The theory of one kernel is the set of facts it accepts. -/
theorem theoryOf_singleton (kernel : Kernel calculus) :
    theoryOf (Accepts calculus) {kernel} = acceptedFacts calculus kernel := by
  ext fact
  exact ⟨fun holds => holds rfl, fun accepted _ member => member ▸ accepted⟩

/-- **Acceptance theories are closed.**  Everything entailed by the facts a
kernel accepts is accepted by that kernel. -/
theorem consequences_acceptance (kernel : Kernel calculus) :
    theoryOf (Accepts calculus) (models (Accepts calculus) (acceptedFacts calculus kernel)) =
      acceptedFacts calculus kernel := by
  ext fact
  constructor
  · intro entailed
    exact entailed (fun _ accepted => accepted)
  · intro accepted _ model
    exact model accepted

/-- **The weakest kernel.**  A kernel's theory is the weakest admissible
theory exactly when the kernel is faithful. -/
theorem isWeakestAdmissible_iff_faithful (kernel : Kernel calculus) :
    IsWeakestAdmissible (Accepts calculus) (Admissible calculus)
        (acceptedFacts calculus kernel) ↔ Faithful calculus kernel := by
  constructor
  · rintro ⟨admissible, weakest⟩ fact
    constructor
    · intro accepted
      have entailed := weakest (T' := Derivable calculus)
        (fun _ model => model) accepted
      have replayModel : replayKernel calculus ∈ models (Accepts calculus) (Derivable calculus) :=
        fun _ derivable => (replayKernel_faithful calculus _).mpr derivable
      exact (replayKernel_faithful calculus fact).mp (entailed replayModel)
    · intro derivable
      exact admissible (fun _ accepted => accepted) derivable
  · intro faithful
    refine ⟨fun model modelAccepts fact derivable =>
        modelAccepts ((faithful fact).mpr derivable), ?_⟩
    intro T' admissible fact accepted model modelOfT'
    exact admissible modelOfT' ((faithful fact).mp accepted)

/-- The replay kernel's theory is the weakest admissible theory. -/
theorem replayKernel_isWeakestAdmissible :
    IsWeakestAdmissible (Accepts calculus) (Admissible calculus)
      (acceptedFacts calculus (replayKernel calculus)) :=
  (isWeakestAdmissible_iff_faithful _).mpr (replayKernel_faithful calculus)

/-- Its model class, the class of complete kernels, is the largest
admissible elementary class. -/
theorem replayKernel_models_largest :
    IsLargestAdmissible (Accepts calculus) (Admissible calculus)
      (models (Accepts calculus) (acceptedFacts calculus (replayKernel calculus))) :=
  isWeakestAdmissible_iff.mp replayKernel_isWeakestAdmissible

/-- Every admissible theory entails every fact the replay kernel accepts. -/
theorem admissible_entails_replay {T : Set (CheckingFact calculus)}
    (admissible : models (Accepts calculus) T ∈ Admissible calculus)
    {fact : CheckingFact calculus} (accepted : Accepts calculus (replayKernel calculus) fact) :
    Entails (Accepts calculus) T fact :=
  replayKernel_isWeakestAdmissible.2 admissible accepted

/-! ## The generic inference checker -/

/-- The family of all validated calculi, with the generic checker. -/
abbrev nikFamily : ValidatedCalculusLanguageDef → ReplaySignature.{0} := nikSignature

/-- The generic inference checker as a kernel for every validated calculus. -/
def checkRawKernel : Kernel nikFamily := fun definition => checkRaw definition

theorem checkRawKernel_eq_replayKernel : checkRawKernel = replayKernel nikFamily := by
  funext definition goal certificate
  exact checkRaw_eq_replay definition goal certificate

/-- **The generic checker is the weakest admissible kernel.** -/
theorem checkRawKernel_isWeakestAdmissible :
    IsWeakestAdmissible (Accepts nikFamily) (Admissible nikFamily)
      (acceptedFacts nikFamily checkRawKernel) := by
  rw [checkRawKernel_eq_replayKernel]
  exact replayKernel_isWeakestAdmissible

/-! ## Controls on the modus ponens package -/

section Controls

open Mettapedia.Languages.MeTTa.PrimeCandidates.MinimalCheckingPackage
open Mettapedia.GSLT.LanguageDef.BootstrapCell.Calibration

/-- The one-calculus family of the modus ponens package. -/
abbrev modusPonens : Unit → ReplaySignature.{0} := fun _ => nikSignature mpValidated

/-- A kernel that also accepts the wrong goal `P(A)` for every certificate. -/
def tooStrong : Kernel modusPonens :=
  fun _ goal certificate =>
    checkRaw mpValidated goal certificate || decide (@Eq Pattern goal mpWrongGoal)

/-- A kernel that rejects everything. -/
def rejectAll : Kernel modusPonens := fun _ _ _ => false

theorem mpProofB_derivable :
    (⟨(), mpBGoal, mpProofB⟩ : CheckingFact modusPonens) ∈ Derivable modusPonens := by
  have accepted : (nikSignature mpValidated).replay mpBGoal mpProofB = true := by
    rw [← checkRaw_eq_replay]
    exact mp_proof_b_accepted
  exact (ReplaySignature.replay_iff (σ := nikSignature mpValidated) mpBGoal mpProofB).mp
    accepted

theorem wrongGoal_not_derivable :
    (⟨(), mpWrongGoal, mpProofB⟩ : CheckingFact modusPonens) ∉ Derivable modusPonens := by
  intro derivable
  have accepted := (ReplaySignature.replay_iff (σ := nikSignature mpValidated)
    mpWrongGoal mpProofB).mpr derivable
  rw [← checkRaw_eq_replay, mpWrongGoal_rejected] at accepted
  exact Bool.false_ne_true accepted

/-- The too-strong kernel is complete, so its theory is admissible. -/
theorem tooStrong_admissible :
    models (Accepts modusPonens) (acceptedFacts modusPonens tooStrong) ∈
      Admissible modusPonens := by
  intro model modelAccepts fact derivable
  apply modelAccepts
  obtain ⟨derivation, erased⟩ := derivable
  have accepted : checkRaw mpValidated fact.goal fact.certificate = true := by
    rw [checkRaw_eq_replay, ← erased]
    exact derivation.replay_erase
  show (checkRaw mpValidated fact.goal fact.certificate ||
    decide (@Eq Pattern fact.goal mpWrongGoal)) = true
  rw [accepted, Bool.true_or]

/-- **Negative control.**  Accepting one more fact breaks weakest
admissibility. -/
theorem tooStrong_not_weakest :
    ¬ IsWeakestAdmissible (Accepts modusPonens) (Admissible modusPonens)
      (acceptedFacts modusPonens tooStrong) := by
  intro weakest
  have faithful := (isWeakestAdmissible_iff_faithful tooStrong).mp weakest
  apply wrongGoal_not_derivable
  apply (faithful _).mp
  simp only [Accepts, tooStrong, decide_true, Bool.or_true]

/-- **Negative control.**  Rejecting a derivable fact breaks admissibility. -/
theorem rejectAll_not_admissible :
    models (Accepts modusPonens) (acceptedFacts modusPonens rejectAll) ∉
      Admissible modusPonens := by
  intro admissible
  have accepted := admissible (fun _ member => member) mpProofB_derivable
  exact Bool.false_ne_true accepted

/-- The positive control: the package's own checker is weakest admissible. -/
theorem modusPonens_kernel_isWeakestAdmissible :
    IsWeakestAdmissible (Accepts modusPonens) (Admissible modusPonens)
      (acceptedFacts modusPonens (replayKernel modusPonens)) :=
  replayKernel_isWeakestAdmissible

end Controls

end Mettapedia.GSLT.LanguageDef.BootstrapCell.CheckingWeakness
