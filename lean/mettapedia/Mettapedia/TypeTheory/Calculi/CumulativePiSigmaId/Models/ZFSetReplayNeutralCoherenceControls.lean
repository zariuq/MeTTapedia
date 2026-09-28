import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayNeutralCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayReductionCoherence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayEnvironmentBoundary

/-!
# Coherent replay of a higher-order pair update

In the context f : Ground → Ground, the program maps f over the first
component of a pair and preserves the second. Two different cumulative
formation trees check the same program. Their meaning agrees by the generic
neutral-elimination theorem, including on raw environments.

Installing the identity function for f introduces a beta redex. Its actual
substituted certificates remain checked, but no longer satisfy the neutral
predicate. Agreement must then follow the certificate-substitution law, not
an assertion that the neutral fragment is closed under substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayNeutralCoherenceControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph sigmaSet)
open ZFSetTraceProducts (traceLam traceApp)
open Mettapedia.SetTheory

universe u

private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n
private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev pairLevel : Tower.Head := .sort (.max Tower.zero Tower.zero)
private abbrev functionLevel : Tower.Head :=
  .sort (.max (.max Tower.zero Tower.zero) (.max Tower.zero Tower.zero))
private abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround

def arrow {n : Nat} : Tower.Tm n := .pi ground ground
def pairType {n : Nat} : Tower.Tm n := .sigma ground ground
def context : Tower.Ctx 1 := .snoc .nil arrow
def contextCode : ContextCode Tower.Head NoConversion 1 :=
  .snoc .nil pairLevel (.piForm zero zero .headType .headType)

private def arrowFormation {n : Nat} : Replay n := .piForm zero zero .headType .headType
private def pairFormation {n : Nat} : Replay n := .sigmaForm zero zero .headType .headType
private def functionFormation {n : Nat} : Replay n :=
  .piForm pairLevel pairLevel pairFormation pairFormation

def program : Tower.Tm 1 :=
  .lam (.pair (.app (.var 1) (.fst (.var 0))) (.snd (.var 0)))
def programType : Tower.Tm 1 := .pi pairType pairType

private def updatedFirstCode : Replay 2 :=
  .appElim ground ground .var (.fstElim ground .var)
private def preservedSecondCode : Replay 2 := .sndElim ground ground .var

def lowerCode : Replay 1 :=
  .lamIntro functionLevel functionFormation
    (.pairIntro pairLevel pairFormation updatedFirstCode preservedSecondCode)

def upperCode : Replay 1 :=
  .lamIntro one (.cumul functionLevel functionFormation)
    (.pairIntro one (.cumul pairLevel pairFormation) updatedFirstCode preservedSecondCode)

theorem context_checked : checkContext Tower.rules noConversionCheck context contextCode = true := by
  decide

theorem lower_checked :
    check Tower.rules noConversionCheck context program programType lowerCode = true := by decide

theorem upper_checked :
    check Tower.rules noConversionCheck context program programType upperCode = true := by decide

theorem lower_neutral : lowerCode.neutralEliminations program programType = true := by decide

theorem upper_neutral : upperCode.neutralEliminations program programType = true := by decide

theorem codes_differ : lowerCode ≠ upperCode := by
  intro same
  have levels : functionLevel = one := by injection same
  exact (by decide : functionLevel ≠ one) levels

noncomputable def programMeaning (heads : Tower.Head → ZFSet.{u}) : Meaning.{u} 1 :=
  .plain (fun env => traceLam (graph (sigmaSet (heads .legacyGround) (fun _ => heads .legacyGround))
    (fun pair => ZFSet.pair (traceApp (env 0) (ZFSetOrderedPair.first pair))
      (ZFSetOrderedPair.second pair))))

theorem lower_assembles (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble heads constants lowerCode program programType = some (programMeaning heads) := rfl

theorem upper_assembles (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    assemble heads constants upperCode program programType = some (programMeaning heads) := rfl

/-- The equality is an instance of general certificate coherence, not a
comparison of two definitions of the same chosen semantic expression. -/
theorem checked_program_meanings_equal (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) (lower upper : Meaning.{u} 1)
    (atLower : assemble heads constants lowerCode program programType = some lower)
    (atUpper : assemble heads constants upperCode program programType = some upper) :
    lower = upper :=
  assemble_neutralEliminations_coherent heads constants Tower.rules lowerCode
    lower_checked lower_neutral atLower upper_checked atUpper (EqualOrHeads.refl _)

/-- An application certificate cannot be used as a projection certificate,
even when its surrounding lambda formation is valid. -/
def malformedCode : Replay 1 :=
  .lamIntro functionLevel functionFormation
    (.pairIntro pairLevel pairFormation (.fstElim ground .var) updatedFirstCode)

theorem malformed_rejected :
    check Tower.rules noConversionCheck context program programType malformedCode = false := by decide

theorem environment_counterexample_excluded :
    ZFSetReplayEnvironmentBoundary.lowerCode.neutralEliminations
      ZFSetReplayEnvironmentBoundary.term ground = false ∧
    ZFSetReplayEnvironmentBoundary.upperCode.neutralEliminations
      ZFSetReplayEnvironmentBoundary.term ground = false := by decide

def identity : Tower.Tm 0 := .lam (.var 0)
def identityCode : Replay 0 := .lamIntro pairLevel arrowFormation .var
def install : Sub Tower.Head 1 0 := fun _ => identity
def installCodes : Fin 1 → Replay 0 := fun _ => identityCode
def installedCode (code : Replay 1) : Replay 0 :=
  code.substitute noConversionRename noConversionSubstitute install installCodes program programType

theorem identity_checked :
    check Tower.rules noConversionCheck .nil identity arrow identityCode = true := by decide

theorem installation_checked :
    check Tower.rules noConversionCheck .nil (subst install program) (subst install programType)
      (installedCode lowerCode) = true ∧
    check Tower.rules noConversionCheck .nil (subst install program) (subst install programType)
      (installedCode upperCode) = true := by decide

theorem installation_creates_redex :
    subst install program =
      .lam (.pair (.app (.lam (.var 0)) (.fst (.var 0))) (.snd (.var 0))) := rfl

theorem installation_not_neutral :
    (installedCode lowerCode).neutralEliminations (subst install program) (subst install programType) = false ∧
    (installedCode upperCode).neutralEliminations (subst install program) (subst install programType) = false := by
  decide

noncomputable def identityMeaning (heads : Tower.Head → ZFSet.{u}) : Meaning.{u} 0 :=
  .plain (fun _ => traceLam (graph (heads .legacyGround) id))

theorem images_assemble (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (index : Fin 1) :
    assemble heads constants (installCodes index) (install index)
      (subst install (context.lookup index)) = some (identityMeaning heads) := by
  have zeroIndex : index = 0 := Fin.eq_zero index
  subst index
  rfl

/-- The exact transformed trees agree despite the newly introduced redex.
The substitution theorem, not normality of the output, supplies this equality. -/
theorem installed_meanings_agree (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ lower upper,
      assemble heads constants (installedCode lowerCode) (subst install program)
        (subst install programType) = some lower ∧
      assemble heads constants (installedCode upperCode) (subst install program)
        (subst install programType) = some upper ∧ lower.value = upper.value := by
  exact assemble_substitute_neutralEliminations_values heads constants Tower.rules
    lowerCode upperCode (programMeaning heads) (programMeaning heads) lower_neutral
    lower_checked upper_checked (lower_assembles heads constants) (upper_assembles heads constants)
    (EqualOrHeads.refl _) install installCodes (fun _ => identityMeaning heads)
    (images_assemble heads constants)

noncomputable def installedMeaning (heads : Tower.Head → ZFSet.{u}) : Meaning.{u} 0 :=
  .plain (fun _ => traceLam (graph (sigmaSet (heads .legacyGround) (fun _ => heads .legacyGround))
    (fun pair => ZFSet.pair
      (traceApp (traceLam (graph (heads .legacyGround) id)) (ZFSetOrderedPair.first pair))
      (ZFSetOrderedPair.second pair))))

theorem installed_lower_assembles (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble heads constants (installedCode lowerCode) (subst install program)
      (subst install programType) = some (installedMeaning heads) := rfl

theorem installed_program_computes (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) (meaning : Meaning.{u} 0)
    (assembled : assemble heads constants (installedCode lowerCode) (subst install program)
      (subst install programType) = some meaning)
    (x y : ZFSet.{u}) (insideX : x ∈ heads .legacyGround) (insideY : y ∈ heads .legacyGround) :
    traceApp (meaning.value Fin.elim0) (ZFSet.pair x y) = ZFSet.pair x y := by
  rw [installed_lower_assembles] at assembled
  cases Option.some.inj assembled
  change traceApp (traceLam (graph (sigmaSet (heads .legacyGround) (fun _ => heads .legacyGround)) _))
    (ZFSet.pair x y) = ZFSet.pair x y
  rw [ZFSetTraceProducts.traceApp_graph_beta _
    (ZFSetDependentProducts.mem_sigmaSet.mpr ⟨x, insideX, y, insideY, rfl⟩)]
  rw [ZFSetOrderedPair.first_pair, ZFSetOrderedPair.second_pair,
    ZFSetTraceProducts.traceApp_graph_beta _ insideX]
  rfl

theorem installed_program_rejects_swap (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) (meaning : Meaning.{u} 0)
    (assembled : assemble heads constants (installedCode lowerCode) (subst install program)
      (subst install programType) = some meaning)
    (x y : ZFSet.{u}) (insideX : x ∈ heads .legacyGround) (insideY : y ∈ heads .legacyGround)
    (distinct : x ≠ y) :
    traceApp (meaning.value Fin.elim0) (ZFSet.pair x y) ≠ ZFSet.pair y x := by
  rw [installed_program_computes heads constants meaning assembled x y insideX insideY]
  exact fun same => distinct (ZFSet.pair_inj.mp same).1

/-- An actual tower model supplies two distinguishable ground values, so
the computation and wrong-order control have inhabited premises. -/
theorem two_element_computation (h : ZFSetUniverseClosure.CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    let heads := ZFSetTraceUniverseInterpretation.interpretHead h ∅
      (ZFSetInterpretation.Controls.twoCode h).1 (fun _ => 0)
    ∃ meaning,
      assemble heads constants (installedCode lowerCode) (subst install program)
        (subst install programType) = some meaning ∧
      traceApp (meaning.value Fin.elim0) (ZFSet.pair ∅ (ZFSet.powerset ∅)) =
        ZFSet.pair ∅ (ZFSet.powerset ∅) ∧
      traceApp (meaning.value Fin.elim0) (ZFSet.pair ∅ (ZFSet.powerset ∅)) ≠
        ZFSet.pair (ZFSet.powerset ∅) ∅ := by
  dsimp only
  let heads := ZFSetTraceUniverseInterpretation.interpretHead h ∅
    (ZFSetInterpretation.Controls.twoCode h).1 (fun _ => 0)
  refine ⟨installedMeaning heads, installed_lower_assembles heads constants, ?_, ?_⟩
  · exact installed_program_computes heads constants _ (installed_lower_assembles heads constants)
      _ _ ZFSetDependentProducts.Controls.empty_mem_two ZFSetDependentProducts.Controls.power_empty_mem_two
  · apply installed_program_rejects_swap heads constants _ (installed_lower_assembles heads constants)
      _ _ ZFSetDependentProducts.Controls.empty_mem_two ZFSetDependentProducts.Controls.power_empty_mem_two
    intro same
    have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := by simp
    rw [← same] at member
    exact ZFSet.notMem_empty _ member

def environmentTarget : Tower.Tm 2 := .var 1

theorem environment_target_checked :
    check Tower.rules noConversionCheck ZFSetReplayEnvironmentBoundary.context
      environmentTarget ground (.var : Replay 2) = true := by decide

theorem environment_target_normal :
    (.var : Replay 2).neutralEliminations environmentTarget ground = true := rfl

/-- Both hidden universe-domain choices reach one independently supplied
normal reduct certificate. The argument is inside each retained domain on
every environment admitted by the checked context. -/
theorem boundary_sources_reach_independent_target
    (h : ZFSetUniverseClosure.CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u})
    (env : ZFSetTypeExpressionInterpretation.Environment.{u} 2)
    (admitted : ZFSetReplayEnvironmentBoundary.valid h env) :
    (ZFSetReplayEnvironmentBoundary.meaning h 0).value env = env 1 ∧
    (ZFSetReplayEnvironmentBoundary.meaning h 1).value env = env 1 := by
  let heads := ZFSetTraceUniverseInterpretation.interpretHead h ∅
    (ZFSetInterpretation.Controls.twoCode h).1 (fun _ => 0)
  let formationMeaning (domainHead : Tower.Head) : Meaning.{u} 2 :=
    ⟨fun _ => ZFSetTraceProducts.tracePiSet (heads domainHead) (fun _ => heads .legacyGround),
      some (fun _ => heads domainHead)⟩
  constructor
  · exact application_lambda_normal_reduct_value heads constants Tower.rules
      ZFSetReplayEnvironmentBoundary.context (.sort (.max (.succ Tower.zero) Tower.zero))
      (.head zero) ground (.var 2) (.var 0)
      (.piForm one zero .headType .headType) .var .var .var
      (formationMeaning zero) (.plain (fun values => values 0))
      (ZFSetReplayEnvironmentBoundary.meaning h 0) (.plain (fun values => values 1))
      (.plain (fun values => values 2)) (fun _ => heads zero)
      ZFSetReplayEnvironmentBoundary.lower_checked environment_target_checked environment_target_normal
      rfl rfl rfl rfl (ZFSetReplayEnvironmentBoundary.lower_assembles h constants) rfl env admitted.2
  · exact application_lambda_normal_reduct_value heads constants Tower.rules
      ZFSetReplayEnvironmentBoundary.context
      (.sort (.max (.succ (.succ Tower.zero)) Tower.zero))
      (.head one) ground (.var 2) (.var 0)
      (.piForm (.sort (.succ (.succ Tower.zero))) zero .headType .headType)
      (.cumul zero .var) .var .var
      (formationMeaning one) (.plain (fun values => values 0))
      (ZFSetReplayEnvironmentBoundary.meaning h 1) (.plain (fun values => values 1))
      (.plain (fun values => values 2)) (fun _ => heads one)
      ZFSetReplayEnvironmentBoundary.upper_checked environment_target_checked environment_target_normal
      rfl rfl rfl rfl (ZFSetReplayEnvironmentBoundary.upper_assembles h constants) rfl env
      (ZFSetInterpretation.universeSet_subset_next h ∅ 0 admitted.2)

def dependentContext : Tower.Ctx 1 := .snoc .nil ground
def dependentFamily : Tower.Tm 2 := .id ground (.var 1) (.var 0)
def dependentPair : Tower.Tm 1 := .pair (.var 0) (.refl (.var 0))
def dependentFormation : Replay 1 :=
  .sigmaForm zero zero .headType (.idForm zero .headType .var .var)
def componentProofCode : Replay 1 := .reflIntro ground .var
def dependentPairCode : Replay 1 :=
  .pairIntro pairLevel dependentFormation .var componentProofCode
def firstProjectionCode : Replay 1 := .fstElim dependentFamily dependentPairCode
def secondProjectionCode : Replay 1 := .sndElim ground dependentFamily dependentPairCode
def secondProjectionType : Tower.Tm 1 := inst0 (.fst dependentPair) dependentFamily
def secondComponentType : Tower.Tm 1 := inst0 (.var 0) dependentFamily

theorem dependent_sources_checked :
    check Tower.rules noConversionCheck dependentContext (.fst dependentPair) ground firstProjectionCode = true ∧
    check Tower.rules noConversionCheck dependentContext (.snd dependentPair)
      secondProjectionType secondProjectionCode = true := by decide

theorem dependent_targets_checked :
    check Tower.rules noConversionCheck dependentContext (.var 0) ground (.var : Replay 1) = true ∧
    check Tower.rules noConversionCheck dependentContext (.refl (.var 0))
      secondComponentType componentProofCode = true := by decide

theorem dependent_targets_normal :
    (.var : Replay 1).neutralEliminations (.var 0) ground = true ∧
    componentProofCode.neutralEliminations (.refl (.var 0)) secondComponentType = true := by decide

/-- The source result mentions the unreduced first projection, whereas the
component result mentions the original value. NoConversion keeps them distinct. -/
theorem dependent_result_types_differ : secondProjectionType ≠ secondComponentType := by decide

theorem component_at_unreduced_projection_type_rejected :
    check Tower.rules noConversionCheck dependentContext (.refl (.var 0))
      secondProjectionType componentProofCode = false := by decide

noncomputable def firstProjectionMeaning : Meaning.{u} 1 :=
  .plain (fun env => ZFSetOrderedPair.first (ZFSet.pair (env 0) ∅))
noncomputable def secondProjectionMeaning : Meaning.{u} 1 :=
  .plain (fun env => ZFSetOrderedPair.second (ZFSet.pair (env 0) ∅))

theorem dependent_projection_assemblies (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble heads constants firstProjectionCode (.fst dependentPair) ground =
      some firstProjectionMeaning ∧
    assemble heads constants secondProjectionCode (.snd dependentPair) secondProjectionType =
      some secondProjectionMeaning := ⟨rfl, rfl⟩

/-- Projection computation is obtained from the generic comparison with
independently checked normal components, at their respective dependent types. -/
theorem dependent_projections_reach_independent_targets
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (env : ZFSetTypeExpressionInterpretation.Environment.{u} 1) :
    firstProjectionMeaning.value env = env 0 ∧ secondProjectionMeaning.value env = ∅ := by
  constructor
  · exact first_pair_normal_reduct_value heads constants Tower.rules
      dependentContext pairLevel ground (.var 0) (.refl (.var 0)) dependentFamily
      dependentFormation .var componentProofCode .var
      (.plain (fun values => values 0)) (.plain (fun _ => ∅))
      firstProjectionMeaning (.plain (fun values => values 0))
      dependent_sources_checked.1 dependent_targets_checked.1 dependent_targets_normal.1
      rfl rfl (dependent_projection_assemblies heads constants).1 rfl env
  · exact second_pair_normal_reduct_value heads constants Tower.rules
      dependentContext pairLevel ground (.var 0) (.refl (.var 0)) dependentFamily
      dependentFormation .var componentProofCode componentProofCode
      (.plain (fun values => values 0)) (.plain (fun _ => ∅))
      secondProjectionMeaning (.plain (fun _ => ∅))
      dependent_sources_checked.2 dependent_targets_checked.2 dependent_targets_normal.2
      rfl rfl (dependent_projection_assemblies heads constants).2 rfl env

def dependentFamilyCode : Replay 2 := .idForm zero .headType .var .var

theorem dependent_family_checked :
    check Tower.rules noConversionCheck (.snoc dependentContext ground)
      dependentFamily (.head zero) dependentFamilyCode = true := by decide

def familyAtProjectionCode : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute dependentFamily (.head zero)
    (.fst dependentPair) dependentFamilyCode firstProjectionCode

def familyAtComponentCode : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute dependentFamily (.head zero)
    (.var 0) dependentFamilyCode .var

/-- The syntactically distinct dependent result types have equal set values
through the actual family-instantiation algorithm. Both generated formation
certificates check; no term-level conversion rule is added. -/
theorem dependent_result_type_values_agree (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) :
    check Tower.rules noConversionCheck dependentContext secondProjectionType
      (.head zero) familyAtProjectionCode = true ∧
    check Tower.rules noConversionCheck dependentContext secondComponentType
      (.head zero) familyAtComponentCode = true ∧
    ∃ source target,
      assemble heads constants familyAtProjectionCode secondProjectionType (.head zero) = some source ∧
      assemble heads constants familyAtComponentCode secondComponentType (.head zero) = some target ∧
      source.value = target.value := by
  exact first_pair_family_values heads constants Tower.rules
    dependentContext pairLevel zero ground (.var 0) (.refl (.var 0)) dependentFamily dependentFamily
    dependentFormation .var componentProofCode dependentFamilyCode
    (.plain (fun values => values 0)) (.plain (fun _ => ∅)) firstProjectionMeaning
    (.plain (fun values => ZFSetTraceProofDecoding.truthCode (values 1 = values 0)))
    dependent_sources_checked.1 dependent_family_checked rfl rfl
    (dependent_projection_assemblies heads constants).1 rfl

#print axioms context_checked
#print axioms lower_checked
#print axioms upper_checked
#print axioms codes_differ
#print axioms checked_program_meanings_equal
#print axioms malformed_rejected
#print axioms environment_counterexample_excluded
#print axioms installation_checked
#print axioms installation_not_neutral
#print axioms installed_meanings_agree
#print axioms installed_program_computes
#print axioms installed_program_rejects_swap
#print axioms two_element_computation
#print axioms environment_target_checked
#print axioms boundary_sources_reach_independent_target
#print axioms dependent_sources_checked
#print axioms dependent_targets_checked
#print axioms dependent_result_types_differ
#print axioms component_at_unreduced_projection_type_rejected
#print axioms dependent_projections_reach_independent_targets
#print axioms dependent_family_checked
#print axioms dependent_result_type_values_agree

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayNeutralCoherenceControls
