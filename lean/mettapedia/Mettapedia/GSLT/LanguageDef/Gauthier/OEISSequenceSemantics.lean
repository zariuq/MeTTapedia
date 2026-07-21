import Mettapedia.GSLT.LanguageDef.Gauthier.BigStepGSLTE2
import Mettapedia.GSLT.LanguageDef.Gauthier.E2Fuel
import Mettapedia.Sequences.OEIS.Basic

namespace Mettapedia.GSLT.LanguageDef.GauthierOEISSequenceSemantics

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.Sequences.OEIS

abbrev Program := GauthierE1.Prog

/-- A frozen campaign program is the exact token stream recognized by the live memo table. -/
structure FrozenCandidate where
  programSha256 : String
  tokens : List Nat
  program : Program
  recognized : GauthierE1.recognize orgMemoSignature tokens = some program

/-- Parse a token stream into a frozen candidate while retaining the parser equation. -/
def frozenCandidate? (programSha256 : String) (tokens : List Nat) :
    Option FrozenCandidate :=
  match recognized : GauthierE1.recognize orgMemoSignature tokens with
  | none => none
  | some program =>
      some
        { programSha256 := programSha256
          tokens := tokens
          program := program
          recognized := recognized }

/-- Extract a frozen candidate only after the kernel has decided that parsing succeeded. -/
def FrozenCandidate.ofTokens (programSha256 : String) (tokens : List Nat)
    (parsed : (frozenCandidate? programSha256 tokens).isSome) : FrozenCandidate :=
  (frozenCandidate? programSha256 tokens).get parsed

/-- Successful scalar evaluation at a zero-based campaign position. -/
def Emits (program : Program) (position : Nat) (value : Int) : Prop :=
  ∃ fuel, GauthierE2.term fuel orgMemoSignature program (Int.ofNat position) = some value

/-- A value is stable once every fuel above one threshold produces it. -/
def EventuallyEmits (program : Program) (position : Nat) (value : Int) : Prop :=
  ∃ threshold, ∀ fuel, threshold ≤ fuel →
    GauthierE2.term fuel orgMemoSignature program (Int.ofNat position) = some value

theorem emits_implies_eventuallyEmits {program : Program} {position : Nat} {value : Int}
    (emits : Emits program position value) : EventuallyEmits program position value := by
  obtain ⟨threshold, success⟩ := emits
  exact ⟨threshold, fun fuel fuelOrder =>
    GauthierE2Fuel.term_mono_of_some fuelOrder success⟩

theorem eventuallyEmits_implies_emits {program : Program} {position : Nat} {value : Int}
    (emits : EventuallyEmits program position value) : Emits program position value := by
  obtain ⟨threshold, stable⟩ := emits
  exact ⟨threshold, stable threshold (le_refl threshold)⟩

theorem emits_iff_eventuallyEmits {program : Program} {position : Nat} {value : Int} :
    Emits program position value ↔ EventuallyEmits program position value :=
  ⟨emits_implies_eventuallyEmits, eventuallyEmits_implies_emits⟩

theorem eventuallyEmits_unique {program : Program} {position : Nat}
    {firstValue secondValue : Int}
    (first : EventuallyEmits program position firstValue)
    (second : EventuallyEmits program position secondValue) :
    firstValue = secondValue := by
  obtain ⟨firstFuel, firstStable⟩ := first
  obtain ⟨secondFuel, secondStable⟩ := second
  let commonFuel := max firstFuel secondFuel
  exact GauthierE2Fuel.term_some_unique
    (firstStable commonFuel (Nat.le_max_left _ _))
    (secondStable commonFuel (Nat.le_max_right _ _))

/-- Full correctness on every campaign position whose OEIS index is in the declared domain. -/
def Realizes (spec : SequenceSpec) (program : Program) : Prop :=
  ∀ position, spec.Domain (spec.index position) →
    EventuallyEmits program position (spec.value (spec.index position))

def CandidateRealizes (spec : SequenceSpec) (candidate : FrozenCandidate) : Prop :=
  Realizes spec candidate.program

def PassesProbe {spec : SequenceSpec} (probe : Probe spec)
    (program : Program) : Prop :=
  EventuallyEmits program probe.position probe.expected

theorem realizes_passes_probe {spec : SequenceSpec} {program : Program}
    (correct : Realizes spec program) (probe : Probe spec) :
    PassesProbe probe program :=
  correct probe.position probe.indexInDomain

/-- A stable wrong output is a kernel-checkable refutation of full realization. -/
structure Counterexample (spec : SequenceSpec) (program : Program) where
  probe : Probe spec
  actual : Int
  actualResult : EventuallyEmits program probe.position actual
  differs : actual ≠ probe.expected

theorem Counterexample.not_realizes {spec : SequenceSpec} {program : Program}
    (counterexample : Counterexample spec program) : ¬ Realizes spec program := by
  intro correct
  have expectedResult := realizes_passes_probe correct counterexample.probe
  have equalValues := eventuallyEmits_unique counterexample.actualResult expectedResult
  exact counterexample.differs equalValues

/-! Positive and negative fixtures over the exact 16-token memo evaluator. -/

def zeroSpec : SequenceSpec where
  offset := 0
  Domain := fun index => 0 ≤ index
  value := fun _ => 0

def zeroCandidate : FrozenCandidate where
  programSha256 := "fixture-zero"
  tokens := [0]
  program := GauthierE2.P.z
  recognized := rfl

theorem zeroCandidate_correct : CandidateRealizes zeroSpec zeroCandidate := by
  intro position indexInDomain
  apply emits_implies_eventuallyEmits
  refine ⟨2, ?_⟩
  dsimp only [GauthierE2.term, GauthierE2.termWithWorld, zeroCandidate,
    zeroSpec, SequenceSpec.index]
  rw [GauthierE2.eval.eq_def]
  rfl

def oneBasedIdentitySpec : SequenceSpec where
  offset := 1
  Domain := fun index => 1 ≤ index
  value := fun index => index - 1

def identityCandidate : FrozenCandidate where
  programSha256 := "fixture-identity"
  tokens := [10]
  program := GauthierE2.P.X
  recognized := rfl

set_option maxHeartbeats 1000000 in
theorem identityCandidate_oneBased_correct :
    CandidateRealizes oneBasedIdentitySpec identityCandidate := by
  intro position indexInDomain
  apply emits_implies_eventuallyEmits
  refine ⟨2, ?_⟩
  dsimp only [GauthierE2.term, GauthierE2.termWithWorld, identityCandidate,
    oneBasedIdentitySpec, SequenceSpec.index]
  have hIndex : (1 : Int) + Int.ofNat position - 1 = Int.ofNat position := by
    ring
  rw [hIndex]
  rw [GauthierE2.eval.eq_def]
  rfl

def identityAgainstZeroCounterexample : Counterexample zeroSpec identityCandidate.program where
  probe :=
    { position := 1
      indexInDomain := by simp [zeroSpec, SequenceSpec.index] }
  actual := 1
  actualResult := by
    apply emits_implies_eventuallyEmits
    refine ⟨2, ?_⟩
    dsimp only [GauthierE2.term, GauthierE2.termWithWorld, identityCandidate]
    rw [GauthierE2.eval.eq_def]
    rfl
  differs := by
    simp [Probe.expected, zeroSpec, SequenceSpec.index]

theorem identityCandidate_not_zero :
    ¬ CandidateRealizes zeroSpec identityCandidate :=
  identityAgainstZeroCounterexample.not_realizes

#print axioms emits_iff_eventuallyEmits
#print axioms Counterexample.not_realizes
#print axioms zeroCandidate_correct
#print axioms identityCandidate_not_zero

end Mettapedia.GSLT.LanguageDef.GauthierOEISSequenceSemantics
