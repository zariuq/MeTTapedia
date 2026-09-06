import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy

/-!
# The backward-branching boundary for rho OSLF

The OSLF modalities form the adjunction `diamond ⊣ box`: `diamond` reads
successors, while its right adjoint `box` reads all predecessors.  Rho has a
finite enumeration of successor classes, but it does not have finitely many
predecessor classes.

The witness below is structural rather than cardinal arithmetic hidden in a
runtime.  For every natural number `n`, construct a closed communication whose
channel quotes a process containing exactly `n` outputs.  The input ignores its
message, so every such communication reduces to the inert process.  Distinct
indices remain inequivalent because structural congruence preserves `ioCount`.

Consequently the full two-direction formula language is sound for rho, while
its usual image-finite Hennessy--Milner completeness hypothesis is false.  The
forward, box-free fragment and the partner-context logic retain their
unconditional adequacy theorems.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.BackwardBranchingBoundary

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Formula.Adequacy
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

set_option autoImplicit false

/-! ## Infinitely many closed channel codes -/

/-- A closed process with exactly `n` output constructors. -/
def outputTowerPattern : Nat → Pattern
  | 0 => .apply "PZero" []
  | n + 1 => .apply "POutput" [closedNilName.1, outputTowerPattern n]

theorem outputTowerPattern_wellSorted : ∀ n,
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
      (outputTowerPattern n)
  | 0 => .unit
  | n + 1 => .output (.quote .unit) (outputTowerPattern_wellSorted n)

theorem outputTowerPattern_binderSafe : ∀ n,
    binderSafeAt "NQuote" 0 (outputTowerPattern n) = true
  | 0 => by simp [outputTowerPattern, binderSafeAt, binderSafeListAt]
  | n + 1 => by
      simp [outputTowerPattern, closedNilName, binderSafeAt, binderSafeListAt,
        outputTowerPattern_binderSafe n]

/-- The typed closed process represented by `outputTowerPattern`. -/
def outputTower (n : Nat) : RhoProcess :=
  ⟨outputTowerPattern n,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨outputTowerPattern_wellSorted n, outputTowerPattern_binderSafe n⟩⟩

/-- Quoting an output tower yields a closed channel. -/
def outputTowerName (n : Nat) : RhoClosedTerm rhoName :=
  ⟨.apply "NQuote" [(outputTower n).1],
    (rhoClosedTermWellSorted_name_iff _).mpr
      ⟨.quote (outputTowerPattern_wellSorted n), by
        change binderSafeAt "NQuote" 0 (outputTowerPattern n) = true
        exact outputTowerPattern_binderSafe n⟩⟩

/-! ## Infinitely many predecessors of nil -/

/-- A communication on the `n`th channel.  Its input body ignores the
received message, so its contractum is the inert process. -/
def nilPredecessor (n : Nat) : RhoProcess :=
  ⟨.collection .hashBag
      [.apply "PInput"
        [(outputTowerName n).1, .lambda none (.apply "PZero" [])],
       .apply "POutput" [(outputTowerName n).1, .apply "PZero" []]] none,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel
          (.cons (.input (.quote (outputTowerPattern_wellSorted n)) .unit)
            (.cons (.output (.quote (outputTowerPattern_wellSorted n)) .unit) .nil)),
        by
          change binderSafeAt "NQuote" 0
            (.collection .hashBag
              [.apply "PInput"
                [.apply "NQuote" [outputTowerPattern n],
                  .lambda none (.apply "PZero" [])],
               .apply "POutput"
                [.apply "NQuote" [outputTowerPattern n], .apply "PZero" []]] none) = true
          simp [binderSafeAt, binderSafeListAt,
            outputTowerPattern_binderSafe n]⟩⟩

/-- The authored communication rule reduces every member of the family to
the singleton spelling of nil. -/
theorem nilPredecessor_reduces_closedCommTarget (n : Nat) :
    rhoRewriteSystem.Reduces (nilPredecessor n) closedCommTarget := by
  have step := RhoStep.comm
    (free := FreeSortContext.empty) (bound := [])
    (outputTowerName n).1 (.apply "PZero" []) (.apply "PZero" []) [] .unit .unit
  change RhoStep (nilPredecessor n).1 closedCommTarget.1
  simpa [nilPredecessor, closedCommTarget, semanticCommSubst,
    semanticSubstProc, semanticNormalizeName, semanticNormalizeProc,
    semanticNormalizeProcList] using step

/-- Hence every member is a semantic predecessor of the inert process under
the modulo-equations `E;R;E` step. -/
theorem nilPredecessor_step_closedNil (n : Nat) :
    rhoLanguageDefGSLT.Step (nilPredecessor n) closedNil := by
  exact ⟨nilPredecessor n, closedCommTarget, rfl,
    nilPredecessor_reduces_closedCommTarget n,
    closedParallelSingleton_equivalent_nil⟩

@[simp]
theorem ioCount_outputTowerPattern : ∀ n,
    ioCount (outputTowerPattern n) = n
  | 0 => by simp [outputTowerPattern, ioCount]
  | n + 1 => by
      simp [outputTowerPattern, closedNilName, ioCount,
        ioCount_outputTowerPattern n]
      omega

@[simp]
theorem ioCount_nilPredecessor (n : Nat) :
    ioCount (nilPredecessor n).1 = 2 * n + 2 := by
  simp [nilPredecessor, outputTowerName, outputTower, ioCount,
    ioCount_outputTowerPattern]
  omega

/-- Different indices give different equation classes. -/
theorem nilPredecessor_index_eq_of_equiv {m n : Nat}
    (equivalent : rhoLanguageDefGSLT.Equiv (nilPredecessor m) (nilPredecessor n)) :
    m = n := by
  have structural : StructuralCongruence (nilPredecessor m).1 (nilPredecessor n).1 :=
    (rhoProcessEquations_iff_structuralCongruence
      (nilPredecessor m) (nilPredecessor n)).mp equivalent
  have countEquality := ioCount_SC structural
  rw [ioCount_nilPredecessor, ioCount_nilPredecessor] at countEquality
  omega

/-- Equation class of the `n`th predecessor. -/
def nilPredecessorClass (n : Nat) : Quotient rhoLanguageDefGSLT.equations :=
  Quotient.mk rhoLanguageDefGSLT.equations (nilPredecessor n)

theorem nilPredecessorClass_injective : Function.Injective nilPredecessorClass := by
  intro m n equalClasses
  exact nilPredecessor_index_eq_of_equiv (Quotient.exact equalClasses)

/-- Rho's backward direction is not image-finite modulo its equations.  This
is independent of the chosen equation-invariant atomic observations. -/
theorem directionalSystem_not_imageFiniteModulo
    (observations : String → EquationPredicate rhoLanguageDefGSLT) :
    ¬ (directionalSystem rhoLanguageDefGSLT observations).ImageFiniteModulo := by
  intro finite
  obtain ⟨representatives, representativesFinite, covers⟩ :=
    finite .backward closedNil
  let representativeClasses : Set (Quotient rhoLanguageDefGSLT.equations) :=
    Quotient.mk rhoLanguageDefGSLT.equations '' representatives
  have representativeClassesFinite : representativeClasses.Finite :=
    representativesFinite.image (Quotient.mk rhoLanguageDefGSLT.equations)
  have allPredecessorClasses : ∀ n : Nat, nilPredecessorClass n ∈ representativeClasses := by
    intro n
    obtain ⟨representative, member, equivalent⟩ :=
      covers (nilPredecessor_step_closedNil n)
    exact ⟨representative, member, (Quotient.sound equivalent).symm⟩
  have representativeClassesInfinite : representativeClasses.Infinite :=
    Set.infinite_of_injective_forall_mem nilPredecessorClass_injective allPredecessorClasses
  exact representativeClassesInfinite representativeClassesFinite

#print axioms nilPredecessor_step_closedNil
#print axioms nilPredecessor_index_eq_of_equiv
#print axioms directionalSystem_not_imageFiniteModulo

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.BackwardBranchingBoundary
