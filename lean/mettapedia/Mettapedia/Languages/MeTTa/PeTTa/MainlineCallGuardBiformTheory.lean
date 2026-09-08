import Mettapedia.GSLT.LanguageDef.BiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass

/-!
# The call-guard compiler as a biform theory

Farmer's biform theory pairs an algorithm with the theorems that its
operations mean.  Here the algorithm is the cold call-guard compiler machine,
run to completion, and the meaning of one complete run is one sentence of the
compiler's specification: the compilation of a snapshot at a head and arity
is a stated result.  The specification is the reference compiler
`compileGuards`; semantic validity of a compiled family is, by definition,
exact production by that specification at the current authority.

* Whole-run correctness: every machine run from a start state to a halted
  state halts with the specification's result.  The proof is a denotation
  invariant on control states.
* The logical node is the specification theory: the sentences that hold of
  `compileGuards`.
* The algorithm is proof relevant: an event is a complete run with its data.
* Every event's meaning is a theorem of the node, so the pair is a biform
  theory.
* The cold presentation language runs the same computations on encoded
  states; the encoding is a proof-relevant translation of run algorithms,
  giving a biform route whose meaning square commutes, and the route lies in
  the compatibility locus exactly because that square commutes.
* An altered meaning assignment, declaring every run declined, is refuted by
  the run on an empty snapshot without executing anything else.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardBiformTheory

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass

/-! ## Whole-run correctness of the compiler machine -/

/-- Prepend already accepted plans to a compilation result. -/
def prependPlans (accepted : List GuardPlan) : CompilationResult → CompilationResult
  | .outsideFragment => .outsideFragment
  | .compiled family => .compiled { family with plans := accepted ++ family.plans }

/-- The plan of one declaration from its compiled modes. -/
def buildPlan (declaration : ArrowDeclaration) (modes : List ArgMode)
    (resultMode : ResultMode) : GuardPlan :=
  { declarationOccurrence := declaration.occurrence
    argumentModes := modes
    resultMode := resultMode
    declaration := declaration }

/-- The specification's verdict on a control state: the result the run from
this state will produce. -/
def denote : CompileLanguageControl → CompilationResult
  | .running owner revision head arity remaining accepted =>
      prependPlans accepted (compileRelevantGuards owner revision head arity remaining)
  | .arguments owner revision head arity declaration remaining inputCursor modes accepted =>
      match compileArgumentModes inputCursor, compileResultMode declaration.outputType with
      | some rest, some resultMode =>
          prependPlans (accepted ++ [buildPlan declaration (modes ++ rest) resultMode])
            (compileRelevantGuards owner revision head arity remaining)
      | _, _ => .outsideFragment
  | .result owner revision head arity declaration remaining modes accepted =>
      match compileResultMode declaration.outputType with
      | some resultMode =>
          prependPlans (accepted ++ [buildPlan declaration modes resultMode])
            (compileRelevantGuards owner revision head arity remaining)
      | none => .outsideFragment
  | .halted result => result

@[simp] theorem prependPlans_nil (result : CompilationResult) :
    prependPlans [] result = result := by
  cases result <;> simp [prependPlans]

theorem prependPlans_cons (accepted : List GuardPlan) (plan : GuardPlan)
    (result : CompilationResult) :
    prependPlans accepted
        (match result with
          | .outsideFragment => .outsideFragment
          | .compiled family => .compiled { family with plans := plan :: family.plans }) =
      prependPlans (accepted ++ [plan]) result := by
  cases result <;> simp [prependPlans]

/-- The start state denotes the specification's result. -/
theorem denote_start (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    denote (compileLanguageStart owned head arity) = compileGuards owned head arity := by
  simp [compileLanguageStart, denote, compileGuards]

/-- One machine step preserves the denotation. -/
theorem denote_step {source target : CompileLanguageControl}
    (step : compileLanguageStep? source = some target) :
    denote target = denote source := by
  cases source with
  | halted result => simp [compileLanguageStep?] at step
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil =>
          simp only [compileLanguageStep?, Option.some.injEq] at step
          subst step
          simp [denote, compileRelevantGuards, prependPlans]
      | cons declaration remaining =>
          simp only [compileLanguageStep?] at step
          split at step
          · rename_i relevant
            simp only [Option.some.injEq] at step
            subst step
            simp only [denote, compileRelevantGuards, relevant, if_true, compileGuard]
            cases modes : compileArgumentModes declaration.inputTypes with
            | none => simp [prependPlans]
            | some modes =>
                cases resultMode : compileResultMode declaration.outputType with
                | none => simp [prependPlans]
                | some resultMode =>
                    simp only [Option.pure_def, buildPlan, List.nil_append]
                    exact (prependPlans_cons accepted _ _).symm
          · rename_i irrelevant
            simp only [Option.some.injEq] at step
            subst step
            simp [denote, compileRelevantGuards, irrelevant]
  | arguments owner revision head arity declaration remaining inputCursor modes accepted =>
      cases inputCursor with
      | nil =>
          simp only [compileLanguageStep?, Option.some.injEq] at step
          subst step
          cases resultMode : compileResultMode declaration.outputType <;>
            simp [denote, compileArgumentModes, resultMode]
      | cons expected inputs =>
          simp only [compileLanguageStep?] at step
          cases mode : compileArgMode expected with
          | none =>
              simp only [mode, Option.some.injEq] at step
              subst step
              simp [denote, compileArgumentModes, mode]
          | some mode =>
              simp only [mode, Option.some.injEq] at step
              subst step
              simp only [denote, compileArgumentModes, mode]
              cases rest : compileArgumentModes inputs with
              | none => rfl
              | some rest =>
                  cases compileResultMode declaration.outputType with
                  | none => rfl
                  | some resultMode => simp [List.append_assoc]
  | result owner revision head arity declaration remaining modes accepted =>
      simp only [compileLanguageStep?] at step
      cases resultMode : compileResultMode declaration.outputType with
      | none =>
          simp only [resultMode, Option.some.injEq] at step
          subst step
          simp [denote, resultMode]
      | some resultMode =>
          simp only [resultMode, Option.some.injEq] at step
          subst step
          simp [denote, resultMode, buildPlan]

/-- A run preserves the denotation. -/
theorem denote_multiStep :
    ∀ {source target : compileLanguageGSLT.Term},
      compileLanguageGSLT.MultiStep source target → denote target = denote source
  | _, _, .refl _ => rfl
  | _, _, .step one rest => (denote_multiStep rest).trans (denote_step one)

/-- Whole-run correctness: a machine run from a start state to a halted
state halts with the specification's result. -/
theorem run_halts_with_specification {owned : OwnedSnapshot} {head : String} {arity : Nat}
    {result : CompilationResult}
    (run : compileLanguageGSLT.MultiStep (compileLanguageStart owned head arity)
      (.halted result)) :
    result = compileGuards owned head arity := by
  have preserved := denote_multiStep run
  rw [denote_start] at preserved
  exact preserved

/-! ## The logical node: the compiler's specification -/

/-- A sentence of the specification: the compilation of a snapshot at a
head and arity is a stated result. -/
structure Sentence where
  owned : OwnedSnapshot
  head : String
  arity : Nat
  result : CompilationResult

/-- A sentence holds when the reference compiler agrees. -/
def Sentence.Holds (sentence : Sentence) : Prop :=
  compileGuards sentence.owned sentence.head sentence.arity = sentence.result

/-- The specification as a consequence institution on one signature, with
no consequence beyond membership. -/
def specificationInstitution : PiInstitution.{0, 0, 0} (Discrete Unit) where
  sentence := (Functor.const (Discrete Unit)).obj Sentence
  consequence _ := ClosureOperator.id _
  translation := by
    intro _ _ _ premises
    exact subset_rfl

/-- The closed theory of true specification sentences. -/
def specificationNode : PiInstitution.TheoryObject specificationInstitution where
  signature := ⟨()⟩
  theory := ⟨{ sentence | sentence.Holds }, rfl⟩

theorem mem_specificationNode_iff (sentence : Sentence) :
    sentence ∈ specificationNode.theory.1 ↔ sentence.Holds :=
  Iff.rfl

/-! ## The algorithm: complete runs, proof relevant -/

/-- A complete run of the compiler machine, retaining its data. -/
structure RunEvidence (source target : CompileLanguageControl) : Type where
  owned : OwnedSnapshot
  head : String
  arity : Nat
  result : CompilationResult
  source_eq : source = compileLanguageStart owned head arity
  target_eq : target = .halted result
  run : compileLanguageGSLT.MultiStep source target

/-- Complete runs as a GSLT on control states. -/
def runTheory : GSLT where
  Term := CompileLanguageControl
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := Nonempty (RunEvidence source target)
  rewrites_resp_left := by
    intro source source' target equal run
    cases equal
    exact ⟨target, run, rfl⟩
  rewrites_resp_right := by
    intro source target target' run equal
    cases equal
    exact run

/-- The proof-relevant run algorithm. -/
def runs : ProofRelevantGSLT where
  theory := runTheory
  steps := ⟨RunEvidence, fun _ _ => Iff.rfl⟩

/-- The meaning of one complete run: the specification sentence it decided. -/
def meaning (event : runs.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.head, event.evidence.arity, event.evidence.result⟩

/-- Every run's meaning is a theorem of the specification node. -/
theorem meaning_sound : MeaningSound specificationInstitution specificationNode runs meaning := by
  intro event
  obtain ⟨source, target, owned, head, arity, result, sourceEq, targetEq, run⟩ := event
  subst sourceEq
  subst targetEq
  exact (run_halts_with_specification run).symm

/-- The cold call-guard compiler as a biform theory. -/
def compilerBiform : BiformTheory.{0, 0, 0, 0} specificationInstitution where
  logical := specificationNode
  algorithm := runs
  meaning := meaning
  meaning_sound := meaning_sound

/-! ## The cold presentation language runs the same computations -/

/-- A complete run of the cold presentation language on encoded states. -/
structure ColdRunEvidence (source target : Pattern) : Type where
  owned : OwnedSnapshot
  head : String
  arity : Nat
  result : CompilationResult
  source_eq : source = encodeCompileLanguageControl (compileLanguageStart owned head arity)
  target_eq : target = encodeCompileLanguageControl (.halted result)
  run : coldIR.semantics.MultiStep source target

/-- Complete cold runs as a GSLT on patterns. -/
def coldRunTheory : GSLT where
  Term := Pattern
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := Nonempty (ColdRunEvidence source target)
  rewrites_resp_left := by
    intro source source' target equal run
    cases equal
    exact ⟨target, run, rfl⟩
  rewrites_resp_right := by
    intro source target target' run equal
    cases equal
    exact run

/-- The proof-relevant cold run algorithm. -/
def coldRuns : ProofRelevantGSLT where
  theory := coldRunTheory
  steps := ⟨ColdRunEvidence, fun _ _ => Iff.rfl⟩

/-- The meaning of a cold run is the same specification sentence. -/
def coldMeaning (event : coldRuns.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.head, event.evidence.arity, event.evidence.result⟩

/-- One machine step is one cold step on encodings. -/
theorem coldStep_of_machineStep {source target : CompileLanguageControl}
    (step : compileLanguageStep? source = some target) :
    coldIR.semantics.Step (encodeCompileLanguageControl source)
      (encodeCompileLanguageControl target) :=
  (coldStep_iff _ _).2
    ((language_step_iff_compileLanguageStep source _).2 ⟨target, step, rfl⟩)

/-- A machine run is a cold run on encodings. -/
theorem coldMultiStep_of_machineMultiStep :
    ∀ {source target : compileLanguageGSLT.Term},
      compileLanguageGSLT.MultiStep source target →
        coldIR.semantics.MultiStep (encodeCompileLanguageControl source)
          (encodeCompileLanguageControl target)
  | _, _, .refl _ => .refl _
  | _, _, .step one rest => .step (coldStep_of_machineStep one) (coldMultiStep_of_machineMultiStep rest)

/-- A cold step from an encoded state is the encoding of a machine step. -/
theorem machineStep_of_coldStep {source : CompileLanguageControl} {wire : Pattern}
    (step : coldIR.semantics.Step (encodeCompileLanguageControl source) wire) :
    ∃ target, compileLanguageStep? source = some target ∧
      wire = encodeCompileLanguageControl target :=
  (language_step_iff_compileLanguageStep source wire).1 ((coldStep_iff _ _).1 step)

/-- A cold run from a pattern equal to an encoded state is the encoding of a
machine run. -/
theorem machineMultiStep_of_coldMultiStep' :
    ∀ {start wire : coldIR.semantics.Term}, coldIR.semantics.MultiStep start wire →
      ∀ source : CompileLanguageControl, start = encodeCompileLanguageControl source →
        ∃ target, compileLanguageGSLT.MultiStep source target ∧
          wire = encodeCompileLanguageControl target
  | _, _, .refl _, source, equal => ⟨source, .refl _, equal⟩
  | _, _, .step one rest, source, equal => by
      subst equal
      obtain ⟨middle, step, middleEq⟩ := machineStep_of_coldStep one
      obtain ⟨target, run, targetEq⟩ :=
        machineMultiStep_of_coldMultiStep' rest middle middleEq
      exact ⟨target, .step step run, targetEq⟩

/-- A cold run from an encoded state is the encoding of a machine run. -/
theorem machineMultiStep_of_coldMultiStep {source : CompileLanguageControl} {wire : Pattern}
    (run : coldIR.semantics.MultiStep (encodeCompileLanguageControl source) wire) :
    ∃ target, compileLanguageGSLT.MultiStep source target ∧
      wire = encodeCompileLanguageControl target :=
  machineMultiStep_of_coldMultiStep' run source rfl

/-- Encoding control states is a proof-relevant translation of run
algorithms: every machine run encodes to a cold run, and every cold run from
an encoded start reflects to a machine run with the encoded result. -/
noncomputable def encodeRuns : Translation runs coldRuns where
  mapTerm := encodeCompileLanguageControl
  mapEquiv equal := congrArg encodeCompileLanguageControl equal
  mapEvidence evidence :=
    { owned := evidence.owned
      head := evidence.head
      arity := evidence.arity
      result := evidence.result
      source_eq := congrArg encodeCompileLanguageControl evidence.source_eq
      target_eq := congrArg encodeCompileLanguageControl evidence.target_eq
      run := coldMultiStep_of_machineMultiStep evidence.run }
  liftEvidence := by
    intro source wire evidence
    obtain ⟨owned, head, arity, result, sourceEq, targetEq, run⟩ := evidence
    obtain ⟨target, machineRun, wireEq⟩ :=
      Classical.indefiniteDescription _ (machineMultiStep_of_coldMultiStep run)
    refine ⟨target, ⟨owned, head, arity, result,
      encodeCompileLanguageControl_injective sourceEq, ?_, machineRun⟩, ⟨⟨wireEq.symm⟩⟩⟩
    exact encodeCompileLanguageControl_injective (wireEq.symm.trans targetEq)

/-- The cold presentation language as a biform theory over the same node. -/
def coldBiform : BiformTheory.{0, 0, 0, 0} specificationInstitution where
  logical := specificationNode
  algorithm := coldRuns
  meaning := coldMeaning
  meaning_sound := by
    intro event
    obtain ⟨source, target, owned, head, arity, result, sourceEq, targetEq, run⟩ := event
    subst sourceEq
    subst targetEq
    obtain ⟨halted, machineRun, encoded⟩ := machineMultiStep_of_coldMultiStep run
    have haltedEq : halted = .halted result := encodeCompileLanguageControl_injective encoded.symm
    subst haltedEq
    exact (run_halts_with_specification machineRun).symm

/-- The biform route from the machine to the cold language: the identity on
the specification, the encoding on runs, and the commuting meaning square. -/
noncomputable def encodeRoute : Hom compilerBiform coldBiform where
  logical := PiInstitution.TheoryHom.identity specificationNode
  operational := encodeRuns
  meaning_natural _ := rfl

/-- The route lies in the compatibility locus, and it is the only route with
its logical and operational components. -/
theorem encodeRoute_compatible :
    Compatible (routePair encodeRoute) ∧
      ∀ route : Hom compilerBiform coldBiform,
        routePair route = routePair encodeRoute → route = encodeRoute := by
  refine ⟨jointProjection_map_compatible encodeRoute, fun route equal => ?_⟩
  exact Hom.ext_data (congrArg Prod.fst equal) (congrArg Prod.snd equal)

/-! ## Negative control: an altered meaning assignment -/

/-- Declare every run declined. -/
def declinedMeaning (event : runs.Event) : Sentence :=
  ⟨event.evidence.owned, event.evidence.head, event.evidence.arity, .outsideFragment⟩

/-- An empty snapshot. -/
def emptyOwned : OwnedSnapshot :=
  ⟨⟨0⟩, ⟨0, [], [], []⟩⟩

/-- The one-step run compiling the empty family. -/
def emptyRun : RunEvidence (compileLanguageStart emptyOwned "f" 0)
    (.halted (.compiled ⟨⟨0⟩, 0, "f", 0, []⟩)) where
  owned := emptyOwned
  head := "f"
  arity := 0
  result := .compiled ⟨⟨0⟩, 0, "f", 0, []⟩
  source_eq := rfl
  target_eq := rfl
  run := .step rfl (.refl _)

/-- The altered assignment is not meaning sound: the empty family is
compiled, not declined, and the specification says so without executing. -/
theorem declinedMeaning_not_sound :
    ¬ MeaningSound specificationInstitution specificationNode runs declinedMeaning := by
  intro sound
  have declined : (compileGuards emptyOwned "f" 0 = .outsideFragment) :=
    sound ⟨_, _, emptyRun⟩
  simp [compileGuards, compileRelevantGuards, emptyOwned] at declined

#print axioms run_halts_with_specification
#print axioms compilerBiform
#print axioms encodeRoute
#print axioms encodeRoute_compatible
#print axioms declinedMeaning_not_sound

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardBiformTheory
