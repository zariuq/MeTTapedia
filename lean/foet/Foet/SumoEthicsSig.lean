import Foet.EthicsCore

set_option autoImplicit false

namespace Foet

universe u

/-
Back-tracing a *minimal* SUMO-ish signature for the ethics ontology.

This is not a port of SUMO, just a typed interface for the key relations that show up
in the FOET virtue/value/deontic fragments:

  attribute(AGENT, VIRTUE)
  desires(AGENT, FORMULA)
  holdsValue(AGENT, VALUE)

The goal is to let us re-express KIF-style sentences as Lean `Formula World` terms with
type-checkable argument structure.
-/

structure SumoEthicsSig (World : Type u) : Type (u + 1) where
  Agent : Type u
  Process : Type u
  ProcessClass : Type u
  ChoicePoint : Type u
  Situation : Type u
  SituationClass : Type u
  Value : Type u
  VirtueAttribute : Type u
  EthicalPhilosophy : Type u
  UtilityFormulaFn : Type u
  hasAgent : Process → Agent → Formula World
  situationFn : Process → Situation
  part : Situation → Situation → Formula World
  isInstance : Situation → SituationClass → Formula World
  isProcessInstance : Process → ProcessClass → Formula World
  element : ProcessClass → ChoicePoint → Formula World
  choicePointAgentFn : ChoicePoint → Agent
  choicePointSituationFn : ChoicePoint → Situation
  describesSituation : Situation → Formula World → Formula World
  situationFormulaFn : Formula World → Situation
  hasAttribute : Agent → VirtueAttribute → Formula World
  desires : Agent → Formula World → Formula World
  prefers : Agent → Formula World → Formula World → Formula World
  interferesWith : Agent → Formula World → Formula World
  holdsObligation : Formula World → Agent → Formula World
  holdsEthicalPhilosophy : Agent → EthicalPhilosophy → Formula World
  /--
  A “practice / guidance” state: the philosophy has action-guiding force for the agent.

  In SUMO this role is played indirectly via `influences` (often only `Likely`) on decision events;
  here we keep it abstract and typed.
  -/
  practicesEthicalPhilosophy : Agent → EthicalPhilosophy → Formula World
  realizesFormula : Process → Formula World → Formula World
  capableInSituation : ProcessClass → Agent → Situation → Formula World
  holdsValue : Agent → Value → Formula World
  bestActionByUtilityInSituation : ProcessClass → UtilityFormulaFn → Situation → Formula World
  relevantField : VirtueAttribute → SituationClass → Formula World
  relevantProcessClass : VirtueAttribute → ProcessClass → Formula World
  similar : Agent → Situation → Situation → Formula World

def SumoEthicsSig.virtueDesireFormula {World : Type u} (sig : SumoEthicsSig World)
    (v : sig.VirtueAttribute) (φ : Formula World) : Formula World :=
  fun w => ∀ a : sig.Agent, sig.hasAttribute a v w → sig.desires a φ w

def SumoEthicsSig.claimRightTo {World : Type u} (sig : SumoEthicsSig World)
    (holder : sig.Agent) (P : sig.Agent → Formula World) : Formula World :=
  fun w =>
    ∀ other : sig.Agent,
      sig.holdsObligation (fun w' => ¬ sig.interferesWith other (P holder) w') other w

def SumoEthicsSig.inSituation {World : Type u} (sig : SumoEthicsSig World)
    (p : sig.Process) (s : sig.Situation) : Formula World :=
  fun w => sig.part (sig.situationFn p) s w

def SumoEthicsSig.inSituationClass {World : Type u} (sig : SumoEthicsSig World)
    (p : sig.Process) (c : sig.SituationClass) : Formula World :=
  fun w => sig.isInstance (sig.situationFn p) c w

def SumoEthicsSig.processInClassViaPart {World : Type u} (sig : SumoEthicsSig World)
    (p : sig.Process) (c : sig.SituationClass) : Formula World :=
  fun w =>
    ∃ s : sig.Situation, sig.part (sig.situationFn p) s w ∧ sig.isInstance s c w

/-- KIF shape: `(exists (?IPROC) (instance ?IPROC ?CLASS))`. -/
def SumoEthicsSig.actionOfClass {World : Type u} (sig : SumoEthicsSig World)
    (c : sig.ProcessClass) : Formula World :=
  fun w => ∃ p : sig.Process, sig.isProcessInstance p c w

def SumoEthicsSig.obligatedToHoldPhilosophy {World : Type u} (sig : SumoEthicsSig World)
    (a : sig.Agent) (p : sig.EthicalPhilosophy) : Formula World :=
  sig.holdsObligation (sig.holdsEthicalPhilosophy a p) a

def SumoEthicsSig.desiresToPracticeEthicalPhilosophy {World : Type u} (sig : SumoEthicsSig World)
    (a : sig.Agent) (p : sig.EthicalPhilosophy) : Formula World :=
  sig.desires a (sig.practicesEthicalPhilosophy a p)

def SumoEthicsSig.aspirationallyHoldsEthicalPhilosophy {World : Type u} (sig : SumoEthicsSig World)
    (a : sig.Agent) (p : sig.EthicalPhilosophy) : Formula World :=
  fun w =>
    sig.holdsEthicalPhilosophy a p w ∧
      sig.desiresToPracticeEthicalPhilosophy a p w

def SumoEthicsSig.authenticallyHoldsEthicalPhilosophy {World : Type u} (sig : SumoEthicsSig World)
    (a : sig.Agent) (p : sig.EthicalPhilosophy) : Formula World :=
  fun w => sig.holdsEthicalPhilosophy a p w ∧ sig.practicesEthicalPhilosophy a p w

def SumoEthicsSig.agentDoesProcessOfClass {World : Type u} (sig : SumoEthicsSig World)
    (a : sig.Agent) (c : sig.ProcessClass) : Formula World :=
  fun w => ∃ pr : sig.Process, sig.hasAgent pr a w ∧ sig.isProcessInstance pr c w

def SumoEthicsSig.agentDoesProcessOfClassInSituation {World : Type u} (sig : SumoEthicsSig World)
    (a : sig.Agent) (c : sig.ProcessClass) (s : sig.Situation) : Formula World :=
  fun w =>
    ∃ pr : sig.Process, sig.hasAgent pr a w ∧ sig.isProcessInstance pr c w ∧ sig.situationFn pr = s

/-! ## Optional “moral psychology” bridge schemata (keep assumptions explicit) -/

/-- A modal operator on formulas (e.g. identity, “likely”, “normally”, etc.). -/
abbrev Modality (World : Type u) : Type u :=
  Formula World → Formula World

def SumoEthicsSig.holdingImpliesDesiresToPractice {World : Type u} (sig : SumoEthicsSig World) : Formula World :=
  fun w =>
    ∀ (a : sig.Agent) (p : sig.EthicalPhilosophy),
      sig.holdsEthicalPhilosophy a p w → sig.desiresToPracticeEthicalPhilosophy a p w

def SumoEthicsSig.holdingImpliesModalityDesiresToPractice {World : Type u} (sig : SumoEthicsSig World)
    (M : Modality World) : Formula World :=
  fun w =>
    ∀ (a : sig.Agent) (p : sig.EthicalPhilosophy),
      sig.holdsEthicalPhilosophy a p w → M (sig.desiresToPracticeEthicalPhilosophy a p) w

end Foet
