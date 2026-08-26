import Mathlib.Tactic

/-!
# Diverse double-compiling

This file formalizes the two principal diverse-double-compiling results from
David A. Wheeler's 2009 dissertation, *Fully Countering Trusting Trust through
Diverse Double-Compiling*.  The names of the premise fields follow Wheeler's
formal proof tables closely.

The first theorem says that an exact DDC match establishes exact
source/executable correspondence.  The second says that a benign claimed
compiler origin necessarily produces an exact DDC match.  The second theorem
does not assume that the parent compiler source successfully compiles the
compiler-under-test source: equality can also hold for equal failures.

Neither theorem establishes that the audited source is desirable or
non-malicious.  Nor does a mismatch identify which premise failed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling

universe u

/-! ## Wheeler's semantic vocabulary -/

/-- The functional compilation/execution vocabulary used in Wheeler's formal
model.  Environment effects remain an explicit compilation and execution
input, so determinism is never obtained merely because `compile` and `run` are
Lean functions. -/
structure Model
    (Source Executable Language Environment Effects Output : Type u) where
  compile : Source -> Executable -> Effects -> Environment -> Environment ->
    Executable
  accuratelyTranslates :
    Executable -> Language -> Source -> Effects -> Environment -> Environment ->
      Prop
  exactlyCorresponds : Executable -> Source -> Language -> Environment -> Prop
  portableAndDeterministic : Source -> Language -> Source -> Prop
  run : Executable -> Source -> Effects -> Environment -> Output
  retarget : Source -> Environment -> Source
  convertText : Output -> Environment -> Environment -> Output
  extract : Output -> Executable

/-- The concrete programs, languages, environments, effects, and two generated
stages of one DDC experiment.

The field correspondence with Wheeler is:
`parentSource = sP`, `compilerSource = sA`, `trustedCompiler = cT`,
`parentCompiler = cP`, `compilerUnderTest = cA`, and
`runtimeEnvironment = eArun`. -/
structure Experiment
    (Source Executable Language Environment Effects : Type u) where
  parentSource : Source
  compilerSource : Source
  trustedCompiler : Executable
  parentCompiler : Executable
  compilerUnderTest : Executable
  stageOne : Executable
  stageTwo : Executable
  parentLanguage : Language
  compilerLanguage : Language
  trustedEnvironment : Environment
  stageEnvironment : Environment
  claimedOriginEnvironment : Environment
  runtimeEnvironment : Environment
  trustedEffects : Effects
  stageEffects : Effects
  claimedOriginEffects : Effects

section General

variable {Source Executable Language Environment Effects Output : Type u}
  (model : Model Source Executable Language Environment Effects Output)
  (experiment : Experiment Source Executable Language Environment Effects)

/-- Exact byte/metadata equality at Wheeler's selected executable observation. -/
def Matches : Prop :=
  experiment.stageTwo = experiment.compilerUnderTest

/-! ## Proof 1: a match establishes source/executable correspondence -/

/-- Wheeler proof 1's five premises.  `parentSourceCompilesCompilerSource` is
the long-form content of the thesis premise named `sP_compiles_sA`. -/
structure ProofOnePremises : Prop where
  defineExactlyCorrespond :
    forall compiler language source effects runOn target,
      model.accuratelyTranslates compiler language source effects runOn target ->
        model.exactlyCorresponds
          (model.compile source compiler effects runOn target)
          source language target
  trustedCompilerTranslatesParent :
    forall effects,
      model.accuratelyTranslates experiment.trustedCompiler
        experiment.parentLanguage experiment.parentSource effects
        experiment.trustedEnvironment experiment.stageEnvironment
  parentSourceCompilesCompilerSource :
    forall goodCompiler makeEffects runOn target effects,
      model.accuratelyTranslates goodCompiler experiment.parentLanguage
          experiment.parentSource makeEffects runOn target ->
        model.accuratelyTranslates
          (model.compile experiment.parentSource goodCompiler makeEffects
            runOn target)
          experiment.compilerLanguage experiment.compilerSource effects target
          experiment.runtimeEnvironment
  definitionStageOne :
    experiment.stageOne =
      model.compile experiment.parentSource experiment.trustedCompiler
        experiment.trustedEffects experiment.trustedEnvironment
        experiment.stageEnvironment
  definitionStageTwo :
    experiment.stageTwo =
      model.compile experiment.compilerSource experiment.stageOne
        experiment.stageEffects experiment.stageEnvironment
        experiment.runtimeEnvironment

namespace ProofOnePremises

/-- Wheeler proof 1 (`source_corresponds_to_executable`): under the five named
premises, an exact stage-two match establishes that the compiler executable
exactly corresponds to its source in the runtime environment. -/
theorem match_implies_sourceCorrespondence
    (premises : ProofOnePremises model experiment)
    (matched : Matches experiment) :
    model.exactlyCorresponds experiment.compilerUnderTest
      experiment.compilerSource experiment.compilerLanguage
      experiment.runtimeEnvironment := by
  have trustedTranslation :=
    premises.trustedCompilerTranslatesParent experiment.trustedEffects
  have stageOneTranslation :=
    premises.parentSourceCompilesCompilerSource
      experiment.trustedCompiler experiment.trustedEffects
      experiment.trustedEnvironment experiment.stageEnvironment
      experiment.stageEffects trustedTranslation
  rw [<- premises.definitionStageOne] at stageOneTranslation
  have stageTwoCorrespondence :=
    premises.defineExactlyCorrespond experiment.stageOne
      experiment.compilerLanguage experiment.compilerSource
      experiment.stageEffects experiment.stageEnvironment
      experiment.runtimeEnvironment stageOneTranslation
  rw [<- premises.definitionStageTwo] at stageTwoCorrespondence
  rw [matched] at stageTwoCorrespondence
  exact stageTwoCorrespondence

end ProofOnePremises

/-! ## Proof 2: a benign claimed origin necessarily matches -/

/-- The eight reusable premises of Wheeler proof 2, excluding the claimed
origin equation `definitionCompilerUnderTest`.  Keeping the origin equation
outside this core makes its necessity directly testable. -/
structure ProofTwoCorePremises : Prop where
  defineExactlyCorrespond :
    forall compiler language source effects runOn target,
      model.accuratelyTranslates compiler language source effects runOn target ->
        model.exactlyCorresponds
          (model.compile source compiler effects runOn target)
          source language target
  trustedCompilerTranslatesParent :
    forall effects,
      model.accuratelyTranslates experiment.trustedCompiler
        experiment.parentLanguage experiment.parentSource effects
        experiment.trustedEnvironment experiment.stageEnvironment
  definitionStageOne :
    experiment.stageOne =
      model.compile experiment.parentSource experiment.trustedCompiler
        experiment.trustedEffects experiment.trustedEnvironment
        experiment.stageEnvironment
  definitionStageTwo :
    experiment.stageTwo =
      model.compile experiment.compilerSource experiment.stageOne
        experiment.stageEffects experiment.stageEnvironment
        experiment.runtimeEnvironment
  parentSourcePortableAndDeterministic :
    model.portableAndDeterministic experiment.parentSource
      experiment.parentLanguage
      (model.retarget experiment.compilerSource experiment.runtimeEnvironment)
  definePortableAndDeterministic :
    forall source language input first second firstEnvironment secondEnvironment
        firstEffects secondEffects target,
      model.portableAndDeterministic source language input ->
      model.exactlyCorresponds first source language firstEnvironment ->
      model.exactlyCorresponds second source language secondEnvironment ->
        model.convertText
            (model.run first input firstEffects firstEnvironment)
            firstEnvironment target =
          model.convertText
            (model.run second input secondEffects secondEnvironment)
            secondEnvironment target
  parentCompilerCorrespondsToSource :
    model.exactlyCorresponds experiment.parentCompiler experiment.parentSource
      experiment.parentLanguage experiment.claimedOriginEnvironment
  defineCompile :
    forall source compiler effects runOn target,
      model.compile source compiler effects runOn target =
        model.extract
          (model.convertText
            (model.run compiler (model.retarget source target) effects runOn)
            runOn target)

/-- All nine premises of Wheeler proof 2. -/
structure ProofTwoPremises : Prop extends ProofTwoCorePremises model experiment where
  definitionCompilerUnderTest :
    experiment.compilerUnderTest =
      model.compile experiment.compilerSource experiment.parentCompiler
        experiment.claimedOriginEffects experiment.claimedOriginEnvironment
        experiment.runtimeEnvironment

namespace ProofTwoPremises

/-- Wheeler proof 2 (`always_equal`): a compiler with the claimed benign origin
must equal the DDC stage-two executable.  The theorem deliberately concludes
exact equality, not merely observational equivalence. -/
theorem always_equal
    (premises : ProofTwoPremises model experiment) :
    Matches experiment := by
  have trustedTranslation :=
    premises.trustedCompilerTranslatesParent experiment.trustedEffects
  have stageOneCorrespondence :=
    premises.defineExactlyCorrespond experiment.trustedCompiler
      experiment.parentLanguage experiment.parentSource
      experiment.trustedEffects experiment.trustedEnvironment
      experiment.stageEnvironment trustedTranslation
  rw [<- premises.definitionStageOne] at stageOneCorrespondence
  have sameRun :=
    premises.definePortableAndDeterministic
      experiment.parentSource experiment.parentLanguage
      (model.retarget experiment.compilerSource experiment.runtimeEnvironment)
      experiment.stageOne experiment.parentCompiler
      experiment.stageEnvironment experiment.claimedOriginEnvironment
      experiment.stageEffects experiment.claimedOriginEffects
      experiment.runtimeEnvironment
      premises.parentSourcePortableAndDeterministic stageOneCorrespondence
      premises.parentCompilerCorrespondsToSource
  calc
    experiment.stageTwo =
        model.compile experiment.compilerSource experiment.stageOne
          experiment.stageEffects experiment.stageEnvironment
          experiment.runtimeEnvironment := premises.definitionStageTwo
    _ = model.extract
          (model.convertText
            (model.run experiment.stageOne
              (model.retarget experiment.compilerSource
                experiment.runtimeEnvironment)
              experiment.stageEffects experiment.stageEnvironment)
            experiment.stageEnvironment experiment.runtimeEnvironment) :=
      premises.defineCompile _ _ _ _ _
    _ = model.extract
          (model.convertText
            (model.run experiment.parentCompiler
              (model.retarget experiment.compilerSource
                experiment.runtimeEnvironment)
              experiment.claimedOriginEffects
              experiment.claimedOriginEnvironment)
            experiment.claimedOriginEnvironment
            experiment.runtimeEnvironment) := congrArg model.extract sameRun
    _ = model.compile experiment.compilerSource experiment.parentCompiler
          experiment.claimedOriginEffects experiment.claimedOriginEnvironment
          experiment.runtimeEnvironment :=
      (premises.defineCompile _ _ _ _ _).symm
    _ = experiment.compilerUnderTest :=
      premises.definitionCompilerUnderTest.symm

end ProofTwoPremises

/-- A DDC mismatch refutes the conjunction of proof 2's nine premises, but the
theorem does not identify which premise failed. -/
theorem mismatch_refutes_proofTwoPremises
    (mismatch : Not (Matches experiment)) :
    Not (ProofTwoPremises model experiment) := by
  intro premises
  exact mismatch premises.always_equal

end General

/-! ## Controls -/

namespace Canary

/-- A small but non-vacuous DDC model: compilation emits the source bit,
correspondence is equality with that source, and execution returns its input.
A wrong executable therefore fails correspondence. -/
def bitModel : Model Bool Bool Unit Bool Bool Bool where
  compile := fun source _compiler _effects _runOn _target => source
  accuratelyTranslates := fun _compiler _language _source _effects _runOn
    _target => True
  exactlyCorresponds := fun executable source _language _environment =>
    executable = source
  portableAndDeterministic := fun _source _language _input => True
  run := fun _executable input _effects _environment => input
  retarget := fun source _target => source
  convertText := fun output _from _to => output
  extract := id

def benignExperiment : Experiment Bool Bool Unit Bool Bool where
  parentSource := false
  compilerSource := true
  trustedCompiler := true
  parentCompiler := false
  compilerUnderTest := true
  stageOne := false
  stageTwo := true
  parentLanguage := ()
  compilerLanguage := ()
  trustedEnvironment := false
  stageEnvironment := true
  claimedOriginEnvironment := false
  runtimeEnvironment := true
  trustedEffects := false
  stageEffects := true
  claimedOriginEffects := false

def benignProofOne : ProofOnePremises bitModel benignExperiment where
  defineExactlyCorrespond := by simp [bitModel]
  trustedCompilerTranslatesParent := by simp [bitModel]
  parentSourceCompilesCompilerSource := by simp [bitModel]
  definitionStageOne := rfl
  definitionStageTwo := rfl

def benignProofTwo : ProofTwoPremises bitModel benignExperiment where
  defineExactlyCorrespond := by simp [bitModel]
  trustedCompilerTranslatesParent := by simp [bitModel]
  definitionStageOne := rfl
  definitionStageTwo := rfl
  parentSourcePortableAndDeterministic := trivial
  definePortableAndDeterministic := by simp [bitModel]
  parentCompilerCorrespondsToSource := rfl
  defineCompile := by simp [bitModel]
  definitionCompilerUnderTest := rfl

theorem benign_match : Matches benignExperiment :=
  benignProofTwo.always_equal

theorem benign_match_establishes_sourceCorrespondence :
    bitModel.exactlyCorresponds benignExperiment.compilerUnderTest
      benignExperiment.compilerSource benignExperiment.compilerLanguage
      benignExperiment.runtimeEnvironment :=
  ProofOnePremises.match_implies_sourceCorrespondence bitModel benignExperiment
    benignProofOne benign_match

/-! ### The claimed-origin equation is material -/

def replacedCompilerExperiment : Experiment Bool Bool Unit Bool Bool :=
  { benignExperiment with compilerUnderTest := false }

/-- All eight reusable proof-two premises still hold after the compiler under
test is replaced. -/
def replacedCompilerCore :
    ProofTwoCorePremises bitModel replacedCompilerExperiment where
  defineExactlyCorrespond := by simp [bitModel]
  trustedCompilerTranslatesParent := by simp [bitModel]
  definitionStageOne := rfl
  definitionStageTwo := rfl
  parentSourcePortableAndDeterministic := trivial
  definePortableAndDeterministic := by simp [bitModel]
  parentCompilerCorrespondsToSource := rfl
  defineCompile := by simp [bitModel]

theorem omitted_origin_equation_allows_mismatch :
    Not (Matches replacedCompilerExperiment) := by
  simp [Matches, replacedCompilerExperiment, benignExperiment]

theorem replacedCompiler_has_no_proofTwoPremises :
    Not (ProofTwoPremises bitModel replacedCompilerExperiment) :=
  mismatch_refutes_proofTwoPremises bitModel replacedCompilerExperiment
    omitted_origin_equation_allows_mismatch

/-! ### Every proof-two premise is material -/

/-- The nine independently stated premises of Wheeler proof 2. -/
inductive ProofTwoRequirement where
  | defineExactlyCorrespond
  | trustedCompilerTranslatesParent
  | definitionStageOne
  | definitionStageTwo
  | parentSourcePortableAndDeterministic
  | definePortableAndDeterministic
  | parentCompilerCorrespondsToSource
  | defineCompile
  | definitionCompilerUnderTest
deriving DecidableEq, Fintype

namespace ProofTwoRequirement

/-- The proposition contributed by one proof-two premise. -/
def Holds
    (requirement : ProofTwoRequirement)
    (model : Model Bool Bool Unit Unit Unit Bool)
    (experiment : Experiment Bool Bool Unit Unit Unit) : Prop :=
  match requirement with
  | .defineExactlyCorrespond =>
      forall compiler language source effects runOn target,
        model.accuratelyTranslates compiler language source effects runOn target ->
          model.exactlyCorresponds
            (model.compile source compiler effects runOn target)
            source language target
  | .trustedCompilerTranslatesParent =>
      forall effects,
        model.accuratelyTranslates experiment.trustedCompiler
          experiment.parentLanguage experiment.parentSource effects
          experiment.trustedEnvironment experiment.stageEnvironment
  | .definitionStageOne =>
      experiment.stageOne =
        model.compile experiment.parentSource experiment.trustedCompiler
          experiment.trustedEffects experiment.trustedEnvironment
          experiment.stageEnvironment
  | .definitionStageTwo =>
      experiment.stageTwo =
        model.compile experiment.compilerSource experiment.stageOne
          experiment.stageEffects experiment.stageEnvironment
          experiment.runtimeEnvironment
  | .parentSourcePortableAndDeterministic =>
      model.portableAndDeterministic experiment.parentSource
        experiment.parentLanguage
        (model.retarget experiment.compilerSource experiment.runtimeEnvironment)
  | .definePortableAndDeterministic =>
      forall source language input first second firstEnvironment secondEnvironment
          firstEffects secondEffects target,
        model.portableAndDeterministic source language input ->
        model.exactlyCorresponds first source language firstEnvironment ->
        model.exactlyCorresponds second source language secondEnvironment ->
          model.convertText
              (model.run first input firstEffects firstEnvironment)
              firstEnvironment target =
            model.convertText
              (model.run second input secondEffects secondEnvironment)
              secondEnvironment target
  | .parentCompilerCorrespondsToSource =>
      model.exactlyCorresponds experiment.parentCompiler experiment.parentSource
        experiment.parentLanguage experiment.claimedOriginEnvironment
  | .defineCompile =>
      forall source compiler effects runOn target,
        model.compile source compiler effects runOn target =
          model.extract
            (model.convertText
              (model.run compiler (model.retarget source target) effects runOn)
              runOn target)
  | .definitionCompilerUnderTest =>
      experiment.compilerUnderTest =
        model.compile experiment.compilerSource experiment.parentCompiler
          experiment.claimedOriginEffects experiment.claimedOriginEnvironment
          experiment.runtimeEnvironment

/-- All proof-two premises other than the selected one. -/
def AllExcept
    (omitted : ProofTwoRequirement)
    (model : Model Bool Bool Unit Unit Unit Bool)
    (experiment : Experiment Bool Bool Unit Unit Unit) : Prop :=
  forall requirement, requirement ≠ omitted ->
    requirement.Holds model experiment

end ProofTwoRequirement

/-- Countermodels use the same two Boolean sources.  The compiler and stage
fields vary only where needed to isolate the selected omitted premise. -/
def proofTwoCounterExperiment
    (omitted : ProofTwoRequirement) :
    Experiment Bool Bool Unit Unit Unit :=
  match omitted with
  | .definitionStageOne =>
      { parentSource := false, compilerSource := true,
        trustedCompiler := true, parentCompiler := true,
        compilerUnderTest := true, stageOne := false, stageTwo := false,
        parentLanguage := (), compilerLanguage := (),
        trustedEnvironment := (), stageEnvironment := (),
        claimedOriginEnvironment := (), runtimeEnvironment := (),
        trustedEffects := (), stageEffects := (), claimedOriginEffects := () }
  | .definitionStageTwo =>
      { parentSource := false, compilerSource := true,
        trustedCompiler := true, parentCompiler := true,
        compilerUnderTest := true, stageOne := true, stageTwo := false,
        parentLanguage := (), compilerLanguage := (),
        trustedEnvironment := (), stageEnvironment := (),
        claimedOriginEnvironment := (), runtimeEnvironment := (),
        trustedEffects := (), stageEffects := (), claimedOriginEffects := () }
  | .definitionCompilerUnderTest =>
      { parentSource := false, compilerSource := true,
        trustedCompiler := true, parentCompiler := true,
        compilerUnderTest := false, stageOne := true, stageTwo := true,
        parentLanguage := (), compilerLanguage := (),
        trustedEnvironment := (), stageEnvironment := (),
        claimedOriginEnvironment := (), runtimeEnvironment := (),
        trustedEffects := (), stageEffects := (), claimedOriginEffects := () }
  | _ =>
      { parentSource := false, compilerSource := true,
        trustedCompiler := false, parentCompiler := true,
        compilerUnderTest := true, stageOne := false, stageTwo := false,
        parentLanguage := (), compilerLanguage := (),
        trustedEnvironment := (), stageEnvironment := (),
        claimedOriginEnvironment := (), runtimeEnvironment := (),
        trustedEffects := (), stageEffects := (), claimedOriginEffects := () }

/-- A finite countermodel family isolating all nine proof-two premises. -/
def proofTwoCounterModel
    (omitted : ProofTwoRequirement) :
    Model Bool Bool Unit Unit Unit Bool where
  compile := fun _source compiler _effects _runOn _target => compiler
  accuratelyTranslates := fun compiler _language source _effects _runOn _target =>
    if omitted = .trustedCompilerTranslatesParent then False
    else compiler = (proofTwoCounterExperiment omitted).trustedCompiler /\
      source = false
  exactlyCorresponds := fun executable _source _language _environment =>
    match omitted with
    | .defineExactlyCorrespond => executable = true
    | .trustedCompilerTranslatesParent => executable = true
    | .parentCompilerCorrespondsToSource => executable = false
    | .parentSourcePortableAndDeterministic => True
    | .definePortableAndDeterministic => True
    | .defineCompile => True
    | _ => executable = (proofTwoCounterExperiment omitted).trustedCompiler
  portableAndDeterministic := fun source _language input =>
    source = false /\ input = true /\
      omitted ≠ .parentSourcePortableAndDeterministic
  run := fun executable _input _effects _environment =>
    if omitted = .defineCompile then false else executable
  retarget := fun source _target => source
  convertText := fun output _from _to => output
  extract := id

/-- Each of Wheeler proof 2's nine premises has a concrete finite model in
which every other premise holds, the selected premise fails, and the DDC match
is false.  Thus none of the nine may be silently omitted. -/
theorem every_proofTwo_requirement_is_material
    (omitted : ProofTwoRequirement) :
    ProofTwoRequirement.AllExcept omitted
        (proofTwoCounterModel omitted) (proofTwoCounterExperiment omitted) /\
      Not (ProofTwoRequirement.Holds omitted
        (proofTwoCounterModel omitted) (proofTwoCounterExperiment omitted)) /\
      Not (Matches (proofTwoCounterExperiment omitted)) := by
  cases omitted
  all_goals
    constructor
    · intro requirement different
      cases requirement <;>
        simp_all [ProofTwoRequirement.Holds, proofTwoCounterModel,
          proofTwoCounterExperiment]
    · constructor <;>
        simp [ProofTwoRequirement.Holds, proofTwoCounterModel,
          proofTwoCounterExperiment, Matches]

/-! ### Every proof-one premise is material -/

inductive ProofOneRequirement where
  | defineExactlyCorrespond
  | trustedCompilerTranslatesParent
  | parentSourceCompilesCompilerSource
  | definitionStageOne
  | definitionStageTwo
deriving DecidableEq, Fintype

namespace ProofOneRequirement

def Holds
    (requirement : ProofOneRequirement)
    (model : Model Bool Bool Unit Unit Unit Bool)
    (experiment : Experiment Bool Bool Unit Unit Unit) : Prop :=
  match requirement with
  | .defineExactlyCorrespond =>
      forall compiler language source effects runOn target,
        model.accuratelyTranslates compiler language source effects runOn target ->
          model.exactlyCorresponds
            (model.compile source compiler effects runOn target)
            source language target
  | .trustedCompilerTranslatesParent =>
      forall effects,
        model.accuratelyTranslates experiment.trustedCompiler
          experiment.parentLanguage experiment.parentSource effects
          experiment.trustedEnvironment experiment.stageEnvironment
  | .parentSourceCompilesCompilerSource =>
      forall goodCompiler makeEffects runOn target effects,
        model.accuratelyTranslates goodCompiler experiment.parentLanguage
            experiment.parentSource makeEffects runOn target ->
          model.accuratelyTranslates
            (model.compile experiment.parentSource goodCompiler makeEffects
              runOn target)
            experiment.compilerLanguage experiment.compilerSource effects target
            experiment.runtimeEnvironment
  | .definitionStageOne =>
      experiment.stageOne =
        model.compile experiment.parentSource experiment.trustedCompiler
          experiment.trustedEffects experiment.trustedEnvironment
          experiment.stageEnvironment
  | .definitionStageTwo =>
      experiment.stageTwo =
        model.compile experiment.compilerSource experiment.stageOne
          experiment.stageEffects experiment.stageEnvironment
          experiment.runtimeEnvironment

def AllExcept
    (omitted : ProofOneRequirement)
    (model : Model Bool Bool Unit Unit Unit Bool)
    (experiment : Experiment Bool Bool Unit Unit Unit) : Prop :=
  forall requirement, requirement ≠ omitted ->
    requirement.Holds model experiment

end ProofOneRequirement

def proofOneCounterExperiment
    (omitted : ProofOneRequirement) :
    Experiment Bool Bool Unit Unit Unit :=
  match omitted with
  | .definitionStageOne =>
      { parentSource := false, compilerSource := true,
        trustedCompiler := true, parentCompiler := false,
        compilerUnderTest := false, stageOne := false, stageTwo := false,
        parentLanguage := (), compilerLanguage := (),
        trustedEnvironment := (), stageEnvironment := (),
        claimedOriginEnvironment := (), runtimeEnvironment := (),
        trustedEffects := (), stageEffects := (), claimedOriginEffects := () }
  | _ =>
      { parentSource := false, compilerSource := true,
        trustedCompiler := false, parentCompiler := false,
        compilerUnderTest := false, stageOne := false, stageTwo := false,
        parentLanguage := (), compilerLanguage := (),
        trustedEnvironment := (), stageEnvironment := (),
        claimedOriginEnvironment := (), runtimeEnvironment := (),
        trustedEffects := (), stageEffects := (), claimedOriginEffects := () }

def proofOneCounterModel
    (omitted : ProofOneRequirement) :
    Model Bool Bool Unit Unit Unit Bool where
  compile := match omitted with
    | .defineExactlyCorrespond =>
        fun _source _compiler _effects _runOn _target => false
    | .trustedCompilerTranslatesParent =>
        fun _source _compiler _effects _runOn _target => false
    | .parentSourceCompilesCompilerSource =>
        fun source compiler _effects _runOn _target => source && compiler
    | .definitionStageOne =>
        fun _source compiler _effects _runOn _target => compiler
    | .definitionStageTwo =>
        fun source _compiler _effects _runOn _target => source
  accuratelyTranslates := match omitted with
    | .trustedCompilerTranslatesParent =>
        fun _compiler _language _source _effects _runOn _target => False
    | .parentSourceCompilesCompilerSource =>
        fun _compiler _language source _effects _runOn _target => source = false
    | .definitionStageOne =>
        fun compiler _language _source _effects _runOn _target => compiler = true
    | _ =>
        fun _compiler _language _source _effects _runOn _target => True
  exactlyCorresponds := match omitted with
    | .definitionStageOne =>
        fun executable _source _language _environment => executable = true
    | _ =>
        fun executable source _language _environment => executable = source
  portableAndDeterministic := fun _source _language _input => True
  run := fun _executable input _effects _environment => input
  retarget := fun source _target => source
  convertText := fun output _from _to => output
  extract := id

/-- Each of proof 1's five premises has a concrete countermodel in which all
other premises and the byte match hold but source correspondence fails. -/
theorem every_proofOne_requirement_is_material
    (omitted : ProofOneRequirement) :
    ProofOneRequirement.AllExcept omitted
        (proofOneCounterModel omitted) (proofOneCounterExperiment omitted) /\
      Not (ProofOneRequirement.Holds omitted
        (proofOneCounterModel omitted) (proofOneCounterExperiment omitted)) /\
      Matches (proofOneCounterExperiment omitted) /\
      Not ((proofOneCounterModel omitted).exactlyCorresponds
        (proofOneCounterExperiment omitted).compilerUnderTest
        (proofOneCounterExperiment omitted).compilerSource
        (proofOneCounterExperiment omitted).compilerLanguage
        (proofOneCounterExperiment omitted).runtimeEnvironment) := by
  cases omitted
  all_goals
    constructor
    · intro requirement different
      cases requirement <;>
        simp_all [ProofOneRequirement.Holds, proofOneCounterModel,
          proofOneCounterExperiment]
    · constructor
      · simp [ProofOneRequirement.Holds, proofOneCounterModel,
          proofOneCounterExperiment]
      · constructor <;>
          simp [proofOneCounterModel, proofOneCounterExperiment, Matches]

/-! ### Thompson's trusting-trust attack -/

inductive AttackSource where
  | compiler
  | login
deriving DecidableEq

inductive AttackExecutable where
  | cleanCompiler
  | infectedCompiler
  | cleanLogin
  | backdooredLogin
deriving DecidableEq

/-- The infected compiler recognizes its own source and perpetuates itself; it
also inserts a payload when compiling the login source. -/
def attackCompile : AttackSource -> AttackExecutable -> AttackExecutable
  | .compiler, .cleanCompiler => .cleanCompiler
  | .compiler, .infectedCompiler => .infectedCompiler
  | .login, .cleanCompiler => .cleanLogin
  | .login, .infectedCompiler => .backdooredLogin
  | .compiler, _ => .cleanCompiler
  | .login, _ => .cleanLogin

def attackModel :
    Model AttackSource AttackExecutable Unit Unit Unit AttackExecutable where
  compile := fun source compiler _effects _runOn _target =>
    attackCompile source compiler
  accuratelyTranslates := fun compiler _language _source _effects _runOn
    _target => compiler = .cleanCompiler
  exactlyCorresponds := fun executable source _language _environment =>
    match source with
    | .compiler => executable = .cleanCompiler
    | .login => executable = .cleanLogin
  portableAndDeterministic := fun _source _language _input => True
  run := fun executable _input _effects _environment => executable
  retarget := fun source _target => source
  convertText := fun output _from _to => output
  extract := id

def trustingTrustExperiment :
    Experiment AttackSource AttackExecutable Unit Unit Unit where
  parentSource := .compiler
  compilerSource := .compiler
  trustedCompiler := .cleanCompiler
  parentCompiler := .infectedCompiler
  compilerUnderTest := .infectedCompiler
  stageOne := .cleanCompiler
  stageTwo := .cleanCompiler
  parentLanguage := ()
  compilerLanguage := ()
  trustedEnvironment := ()
  stageEnvironment := ()
  claimedOriginEnvironment := ()
  runtimeEnvironment := ()
  trustedEffects := ()
  stageEffects := ()
  claimedOriginEffects := ()

/-- Ordinary self-recompilation reproduces the infected compiler exactly and
therefore misses the attack. -/
theorem ordinary_self_recompilation_matches_infected_compiler :
    attackModel.compile trustingTrustExperiment.compilerSource
        trustingTrustExperiment.compilerUnderTest () () () =
      trustingTrustExperiment.compilerUnderTest :=
  rfl

/-- The same infected compiler inserts the distinct login payload. -/
theorem infected_compiler_inserts_login_payload :
    attackCompile .login .infectedCompiler = .backdooredLogin /\
      attackCompile .login .cleanCompiler = .cleanLogin :=
  ⟨rfl, rfl⟩

/-- Diverse double-compiling exposes the infected executable because its
stage-two result differs from the compiler under test. -/
theorem diverse_double_compiling_detects_infected_compiler :
    Not (Matches trustingTrustExperiment) := by
  simp [Matches, trustingTrustExperiment]

/-! ### A match does not certify source benevolence -/

/-- An external source-review predicate, intentionally independent of DDC. -/
def SourceApproved (source : Bool) : Prop := source = false

/-- The DDC match and exact source correspondence both hold while the audited
compiler source fails the independent approval predicate. -/
theorem matching_corresponding_source_can_be_unapproved :
    Matches benignExperiment /\
      bitModel.exactlyCorresponds benignExperiment.compilerUnderTest
        benignExperiment.compilerSource benignExperiment.compilerLanguage
        benignExperiment.runtimeEnvironment /\
      Not (SourceApproved benignExperiment.compilerSource) := by
  exact ⟨benign_match, benign_match_establishes_sourceCorrespondence,
    by simp [SourceApproved, benignExperiment]⟩

/-! ### Equality without the premises is not a trust proof -/

def rejectingCorrespondenceModel : Model Bool Bool Unit Bool Bool Bool :=
  { bitModel with exactlyCorresponds := fun _ _ _ _ => False }

theorem matching_bytes_do_not_supply_proofOnePremises :
    Matches benignExperiment /\
      Not (ProofOnePremises rejectingCorrespondenceModel benignExperiment) := by
  constructor
  · exact benign_match
  · intro premises
    exact ProofOnePremises.match_implies_sourceCorrespondence
      rejectingCorrespondenceModel benignExperiment premises benign_match

end Canary

end Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling

#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.ProofOnePremises.match_implies_sourceCorrespondence
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.ProofTwoPremises.always_equal
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.mismatch_refutes_proofTwoPremises
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.every_proofOne_requirement_is_material
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.every_proofTwo_requirement_is_material
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.ordinary_self_recompilation_matches_infected_compiler
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.diverse_double_compiling_detects_infected_compiler
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.omitted_origin_equation_allows_mismatch
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.matching_bytes_do_not_supply_proofOnePremises
#print axioms Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.matching_corresponding_source_can_be_unapproved
