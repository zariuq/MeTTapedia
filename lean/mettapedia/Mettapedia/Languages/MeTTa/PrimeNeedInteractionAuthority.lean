import Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
import Mettapedia.Languages.MeTTa.PrimeNeedReferenceSemantics

/-!
# Occurrence-authenticated interaction authority for Prime Need

Prime's reference transition returns a list rather than a set.  A semantic
event is therefore an exact list occurrence: its index and `getElem?` proof
retain duplicate alternatives even when two successors are equal.

This module exposes that existing machine relation as an interaction
presentation and hence as a NIK authority.  It does not introduce a second
evaluator.  Since a reference machine contains an extensional heap function,
executable NIK replay is parameterized by an exact endpoint identity.  A
concrete serialized realization must supply canonical state packets or
another injective decidable key; an unproved digest is not sufficient.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNeedInteractionAuthority

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
open Mettapedia.Languages.MeTTa.PrimeNeedReference

universe uAuthority uIdentity

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

abbrev PrimeMachine :=
  Machine Origin Local Resume Rule Value StableFault RetryableFault Effect

/-- Endpoint erasure of the occurrence-sensitive reference transition. -/
def machineTheory
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    GSLT where
  Term := PrimeMachine
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => Nonempty (StepOccurrence spec source target)
  rewrites_resp_left := by
    intro source source' target equal edge
    subst source'
    exact ⟨target, edge, rfl⟩
  rewrites_resp_right := by
    intro source target target' edge equal
    subst target'
    exact edge

/-- Type-valued evidence for one exact position in the list-valued machine
transition. -/
structure OccurrenceEvidence
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (index : Nat) (source target : PrimeMachine) : Type where
  successorAt : (step spec source)[index]? = some target

/-- Exact list occurrence is the interaction site. -/
def machinePresentation
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    InteractionPresentation (machineTheory spec) where
  Site := Nat
  Event := OccurrenceEvidence spec
  sound := by
    intro site _source _target occurrence
    exact ⟨{ index := site, successorAt := occurrence.successorAt }⟩

/-- The presentation neither invents nor loses machine-step occurrences. -/
theorem machinePresentation_complete
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (machinePresentation spec).Complete := by
  intro source target edge
  rcases edge with ⟨occurrence⟩
  exact ⟨⟨occurrence.index, ⟨occurrence.successorAt⟩⟩⟩

/-- Repackage an existing reference-machine occurrence as an enabled
interaction event without recomputing the successor list. -/
def StepOccurrence.toEnabled
    {spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {source target : PrimeMachine}
    (occurrence : StepOccurrence spec source target) :
    (machinePresentation spec).Enabled source where
  site := occurrence.index
  target := target
  evidence := ⟨occurrence.successorAt⟩

/-- A concrete Prime realization supplies the exact identity used to replay
machine endpoints. -/
abbrev MachineIdentity
    (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*) :=
  ExactEndpointIdentity.{uIdentity}
    (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- Local NIK authority for one exact reference-machine occurrence. -/
def nikStepAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    (identity : MachineIdentity.{uIdentity} Origin Local Resume Rule Value
      StableFault RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  stepAuthorityByIdentity authorityId identity (machinePresentation spec)

theorem nikStepAuthority_complete {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    (identity : MachineIdentity.{uIdentity} Origin Local Resume Rule Value
      StableFault RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (nikStepAuthority authorityId identity spec).Complete :=
  by
    change (stepAuthorityByIdentity authorityId identity
      (machinePresentation spec)).Complete
    exact stepAuthorityByIdentity_complete authorityId identity
      (machinePresentation_complete spec)

/-- Free finite-trace NIK closure of the exact occurrence authority. -/
def nikFiniteTraceAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    (identity : MachineIdentity.{uIdentity} Origin Local Resume Rule Value
      StableFault RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  finiteTraceAuthorityByIdentity authorityId identity
    (machinePresentation spec)

/-- With an exact endpoint identity, Lean-native certificate existence is
equivalent to finite occurrence-sensitive Prime reachability. -/
theorem nikFiniteTraceAuthority_correspondence
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    (identity : MachineIdentity.{uIdentity} Origin Local Resume Rule Value
      StableFault RetryableFault Effect)
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (claim : TraceClaim (machineTheory spec)) :
    (Exists fun certificate :
        (nikFiniteTraceAuthority authorityId identity spec).Certificate =>
      (nikFiniteTraceAuthority authorityId identity spec).check claim
        certificate = true) ↔ claim.Meaning :=
  by
    change (Exists fun certificate :
        (finiteTraceAuthorityByIdentity authorityId identity
          (machinePresentation spec)).Certificate =>
      (finiteTraceAuthorityByIdentity authorityId identity
        (machinePresentation spec)).check claim certificate = true) ↔
      claim.Meaning
    exact finiteTraceAuthorityByIdentity_correspondence authorityId identity
      (machinePresentation_complete spec) claim

/-! ## Occurrence canaries -/

namespace Canary

def demoSpec : Spec Unit Unit Unit Unit Unit Unit Unit Unit where
  alternatives := fun _ => []
  action := fun _ => .done (.value ())
  afterDemand := fun _ _ => ()
  afterAllocation := fun _ _ => ()

def demoWorld : World Unit Unit Unit Unit Unit Unit where
  lineage := 0
  path := []
  heap := Heap.empty
  receipts := ReceiptGraph.empty
  nextCell := 0
  nextEvaluator := 0

def start : Machine Unit Unit Unit Unit Unit Unit Unit Unit where
  world := demoWorld
  control := .run () []

def next : Machine Unit Unit Unit Unit Unit Unit Unit Unit :=
  finished start demoWorld (.returned (.value ()) []) 0 0 0 0

def firstOccurrence : StepOccurrence demoSpec start next where
  index := 0
  successorAt := rfl

theorem occurrence_is_presented :
    Nonempty ((machinePresentation demoSpec).Event (0 : Nat) start next) :=
  ⟨⟨firstOccurrence.successorAt⟩⟩

/-- Negative canary: a singleton transition has no second occurrence. -/
theorem no_second_occurrence :
    (step demoSpec start)[1]? = none :=
  rfl

end Canary

end Mettapedia.Languages.MeTTa.PrimeNeedInteractionAuthority
