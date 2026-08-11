import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTRhoInternalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Erasure

/-!
# The conserved-credit compiler through the concrete Cost construction

This file gives the conserved-credit administrative language two
interpretations:

* a term in the repository's concrete `CostTerm` syntax; and
* its direct resource-process image in pure rho.

The main naturality theorem proves that actual `CostTerm.erase` commutes with
these interpretations up to rho structural congruence.  The result is then
specialised to the source and target images of every causal-credit action.

Cost wrappers are not used as a second store for learning state here.  Linear
credit remains explicit process structure; the Cost layer accounts for the
same administrative communication without changing its pure-rho image.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTCostImage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
open WeightedGSLTCausalCredit
open WeightedGSLTRhoInternalization

/-! ## Signature encoding and resource syntax -/

/-- Concrete Cost signatures are mapped to the marker name indexed by the sum
of their ground authorities.  Generated resource channels use singleton
signatures, for which this encoding is exact. -/
def creditCostSignatureName (signature : CostSig Nat) : Pattern :=
  markerName signature.sum

@[simp]
theorem creditCostSignatureName_singleton (channel : Nat) :
    creditCostSignatureName ({channel} : CostSig Nat) = markerName channel := by
  simp [creditCostSignatureName]

/-- Every generated signed wrapper carries one nonempty administrative
authority.  Erasure forgets this wrapper while the concrete Cost validator can
still see that it is runtime-valid. -/
def administrativeSignature : CostSig Nat := {0}

/-- Small resource-protocol language shared by the two compiler paths. -/
inductive ResourceProtocol where
  | empty
  | token (channel : Nat)
  | await (channel : Nat) (continuation : ResourceProtocol)
  | parallel (left right : ResourceProtocol)
  deriving DecidableEq

namespace ResourceProtocol

/-- Interpretation into the repository's concrete cost-accounted rho syntax. -/
def toCost : ResourceProtocol → CostTerm Nat
  | .empty => .nil
  | .token channel =>
      .signed
        (.send (.signature {channel}) .nil)
        administrativeSignature
  | .await channel continuation =>
      .signed
        (.recv (.signature {channel}) continuation.toCost)
        administrativeSignature
  | .parallel left right => .par left.toCost right.toCost

/-- Direct interpretation into the pure-rho resource compiler. -/
def toRho : ResourceProtocol → Pattern
  | .empty => rhoZero
  | .token channel => resourceToken channel
  | .await channel continuation =>
      awaitResource channel continuation.toRho
  | .parallel left right =>
      bag [left.toRho, right.toRho]

/-! ## Structural-congruence helpers -/

private theorem output_congr_right (name left right : Pattern)
    (h : StructuralCongruence left right) :
    StructuralCongruence
      (.apply "POutput" [name, left])
      (.apply "POutput" [name, right]) := by
  apply StructuralCongruence.apply_cong
  · rfl
  · intro index leftBound rightBound
    simp at leftBound rightBound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · exact StructuralCongruence.refl name
    · exact h

private theorem input_congr_body (name left right : Pattern)
    (h : StructuralCongruence left right) :
    StructuralCongruence
      (.apply "PInput" [name, .lambda none left])
      (.apply "PInput" [name, .lambda none right]) := by
  apply StructuralCongruence.apply_cong
  · rfl
  · intro index leftBound rightBound
    simp at leftBound rightBound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · exact StructuralCongruence.refl name
    · exact StructuralCongruence.lambda_cong none left right h

private theorem parallel_congr
    (left₁ left₂ right₁ right₂ : Pattern)
    (hLeft : StructuralCongruence left₁ left₂)
    (hRight : StructuralCongruence right₁ right₂) :
    StructuralCongruence
      (bag [left₁, right₁])
      (bag [left₂, right₂]) := by
  apply StructuralCongruence.par_cong
  · rfl
  · intro index leftBound rightBound
    simp at leftBound rightBound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · exact hLeft
    · exact hRight

/-- **Cost-erasure naturality for administrative resources.**  Interpreting a
resource protocol in concrete Cost syntax and then applying the repository's
actual Cost erasure is structurally congruent to compiling it directly into
pure rho. -/
theorem erase_toCost_structurallyCongruent_toRho :
    ∀ protocol : ResourceProtocol,
      StructuralCongruence
        (protocol.toCost.erase creditCostSignatureName)
        protocol.toRho
  | .empty => by
      exact StructuralCongruence.par_empty
  | .token channel => by
      simp only [toCost, CostTerm.erase, CostProc.erase, CostName.erase,
        creditCostSignatureName_singleton, toRho, resourceToken, commOut]
      exact output_congr_right (markerName channel)
        (.collection .hashBag [] none) rhoZero
        StructuralCongruence.par_empty
  | .await channel continuation => by
      simp only [toCost, CostTerm.erase, CostProc.erase, CostName.erase,
        creditCostSignatureName_singleton, toRho, awaitResource, commIn]
      exact input_congr_body (markerName channel)
        (continuation.toCost.erase creditCostSignatureName)
        continuation.toRho
        (erase_toCost_structurallyCongruent_toRho continuation)
  | .parallel left right => by
      simp only [toCost, CostTerm.erase, toRho, bag]
      exact parallel_congr
        (left.toCost.erase creditCostSignatureName) left.toRho
        (right.toCost.erase creditCostSignatureName) right.toRho
        (erase_toCost_structurallyCongruent_toRho left)
        (erase_toCost_structurallyCongruent_toRho right)

/-- Every protocol generated by this compiler lies in the concrete Cost
runtime-supported fragment. -/
theorem toCost_runtimeSupported :
    ∀ protocol : ResourceProtocol, protocol.toCost.RuntimeSupported
  | .empty => by trivial
  | .token channel => by
      simp [toCost, CostTerm.RuntimeSupported, CostProc.RuntimeSupported,
        CostName.RuntimeSupported, CostSig.RuntimeValid,
        administrativeSignature]
  | .await channel continuation => by
      simpa [toCost, CostTerm.RuntimeSupported, CostProc.RuntimeSupported,
        CostName.RuntimeSupported, CostSig.RuntimeValid,
        administrativeSignature] using toCost_runtimeSupported continuation
  | .parallel left right => by
      exact ⟨toCost_runtimeSupported left, toCost_runtimeSupported right⟩

/-! ## Finite parallel families -/

/-- Right-associated parallel assembly, with no redundant singleton wrapper. -/
def parallelList : List ResourceProtocol → ResourceProtocol
  | [] => .empty
  | [protocol] => protocol
  | protocol :: next :: rest =>
      .parallel protocol (parallelList (next :: rest))

/-- The direct image of `parallelList` is structurally congruent to the flat
rho bag used by the existing causal-credit compiler. -/
theorem parallelList_toRho_structurallyCongruent_flat :
    ∀ protocols : List ResourceProtocol,
      StructuralCongruence
        (parallelList protocols).toRho
        (bag (protocols.map toRho))
  | [] => by
      simpa [parallelList, toRho, bag, rhoZero] using
        StructuralCongruence.par_empty.symm
  | [protocol] => by
      simpa [parallelList, toRho, bag] using
        (StructuralCongruence.par_singleton protocol.toRho).symm
  | protocol :: next :: rest => by
      let tail := next :: rest
      have tailCongruence :=
        parallelList_toRho_structurallyCongruent_flat tail
      have nestedCongruence :
          StructuralCongruence
            (bag [protocol.toRho, (parallelList tail).toRho])
            (bag [protocol.toRho, bag (tail.map toRho)]) :=
        parallel_congr protocol.toRho protocol.toRho
          (parallelList tail).toRho (bag (tail.map toRho))
          (StructuralCongruence.refl protocol.toRho) tailCongruence
      have flattenCongruence :
          StructuralCongruence
            (bag [protocol.toRho, bag (tail.map toRho)])
            (bag (protocol.toRho :: tail.map toRho)) := by
        simpa [bag] using
          StructuralCongruence.par_flatten [protocol.toRho] (tail.map toRho)
      exact StructuralCongruence.trans _ _ _
        (by simpa [parallelList, toRho, tail] using nestedCongruence)
        (by simpa [tail] using flattenCongruence)

end ResourceProtocol

/-! ## Replacement and redemption images -/

def replacementProtocol (sourceChannel targetChannel : Nat) : ResourceProtocol :=
  .parallel (.token sourceChannel) (.await sourceChannel (.token targetChannel))

def replacementTargetProtocol (targetChannel : Nat) : ResourceProtocol :=
  .token targetChannel

def redemptionProductsProtocol
    (emptyReceipt emptySignal targetCredit : Nat) : ResourceProtocol :=
  ResourceProtocol.parallelList
    [.token emptyReceipt, .token emptySignal, .token targetCredit]

def redemptionHandlerProtocol
    (receipt signal donorCredit : Nat)
    (emptyReceipt emptySignal targetCredit : Nat) : ResourceProtocol :=
  .await receipt
    (.await signal
      (.await donorCredit
        (redemptionProductsProtocol emptyReceipt emptySignal targetCredit)))

def redemptionProtocol
    (receipt signal donorCredit : Nat)
    (emptyReceipt emptySignal targetCredit : Nat) : ResourceProtocol :=
  ResourceProtocol.parallelList
    [.token receipt,
      redemptionHandlerProtocol receipt signal donorCredit
        emptyReceipt emptySignal targetCredit,
      .token signal,
      .token donorCredit]

def redemptionTargetProtocol
    (emptyReceipt emptySignal targetCredit : Nat) : ResourceProtocol :=
  redemptionProductsProtocol emptyReceipt emptySignal targetCredit

theorem replacementProtocol_toRho
    (sourceChannel targetChannel : Nat) :
    StructuralCongruence
      (replacementProtocol sourceChannel targetChannel).toRho
      (replacementSource sourceChannel targetChannel []) := by
  exact StructuralCongruence.refl _

theorem replacementTargetProtocol_toRho (targetChannel : Nat) :
    StructuralCongruence
      (replacementTargetProtocol targetChannel).toRho
      (replacementTarget targetChannel []) := by
  simpa [replacementTargetProtocol, ResourceProtocol.toRho,
    replacementTarget] using
    (StructuralCongruence.par_singleton (resourceToken targetChannel)).symm

theorem redemptionProductsProtocol_toRho
    (emptyReceipt emptySignal targetCredit : Nat) :
    StructuralCongruence
      (redemptionProductsProtocol emptyReceipt emptySignal targetCredit).toRho
      (redemptionProducts emptyReceipt emptySignal targetCredit) := by
  simpa [redemptionProductsProtocol, redemptionProducts,
    ResourceProtocol.toRho] using
    ResourceProtocol.parallelList_toRho_structurallyCongruent_flat
      ([.token emptyReceipt, .token emptySignal, .token targetCredit] :
        List ResourceProtocol)

private theorem awaitResource_congr (channel : Nat)
    {left right : Pattern} (h : StructuralCongruence left right) :
    StructuralCongruence
      (awaitResource channel left)
      (awaitResource channel right) := by
  exact ResourceProtocol.input_congr_body
    (markerName channel) left right h

theorem redemptionHandlerProtocol_toRho
    (receipt signal donorCredit : Nat)
    (emptyReceipt emptySignal targetCredit : Nat) :
    StructuralCongruence
      (redemptionHandlerProtocol receipt signal donorCredit
        emptyReceipt emptySignal targetCredit).toRho
      (redemptionHandler receipt signal donorCredit
        emptyReceipt emptySignal targetCredit) := by
  apply awaitResource_congr
  apply awaitResource_congr
  apply awaitResource_congr
  exact redemptionProductsProtocol_toRho
    emptyReceipt emptySignal targetCredit

private theorem bag_four_second_congr
    (first second second' third fourth : Pattern)
    (hSecond : StructuralCongruence second second') :
    StructuralCongruence
      (bag [first, second, third, fourth])
      (bag [first, second', third, fourth]) := by
  apply StructuralCongruence.par_cong
  · rfl
  · intro index leftBound rightBound
    simp at leftBound rightBound
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact StructuralCongruence.refl first
    · exact hSecond
    · exact StructuralCongruence.refl third
    · exact StructuralCongruence.refl fourth

theorem redemptionProtocol_toRho
    (receipt signal donorCredit : Nat)
    (emptyReceipt emptySignal targetCredit : Nat) :
    StructuralCongruence
      (redemptionProtocol receipt signal donorCredit
        emptyReceipt emptySignal targetCredit).toRho
      (redemptionSource receipt signal donorCredit
        emptyReceipt emptySignal targetCredit []) := by
  have flatten :=
    ResourceProtocol.parallelList_toRho_structurallyCongruent_flat
      ([.token receipt,
        redemptionHandlerProtocol receipt signal donorCredit
          emptyReceipt emptySignal targetCredit,
        .token signal,
        .token donorCredit] : List ResourceProtocol)
  have handler := redemptionHandlerProtocol_toRho
    receipt signal donorCredit emptyReceipt emptySignal targetCredit
  exact StructuralCongruence.trans _ _ _
    (by simpa [redemptionProtocol] using flatten)
    (by
      simpa [ResourceProtocol.toRho, redemptionSource] using
        bag_four_second_congr
          (resourceToken receipt)
          (redemptionHandlerProtocol receipt signal donorCredit
            emptyReceipt emptySignal targetCredit).toRho
          (redemptionHandler receipt signal donorCredit
            emptyReceipt emptySignal targetCredit)
          (resourceToken signal) (resourceToken donorCredit) handler)

theorem redemptionTargetProtocol_toRho
    (emptyReceipt emptySignal targetCredit : Nat) :
    StructuralCongruence
      (redemptionTargetProtocol emptyReceipt emptySignal targetCredit).toRho
      (redemptionTarget emptyReceipt emptySignal targetCredit []) := by
  simpa [redemptionTargetProtocol, redemptionTarget, redemptionProducts,
    ResourceProtocol.toRho] using
    redemptionProductsProtocol_toRho emptyReceipt emptySignal targetCredit

/-! ## Complete causal-action commuting square -/

noncomputable def causalSourceProtocol
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) : ResourceProtocol :=
  let code : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget → Nat := imageChannelCode
  match action with
  | .fire receiptSlot synapse =>
      replacementProtocol
        (code (receiptChannel source receiptSlot))
        (code (.receiptFull receiptSlot synapse))
  | .signal signalSlot neuron =>
      replacementProtocol
        (code (signalChannel source signalSlot))
        (code (.signalFull signalSlot neuron))
  | .redeem receiptSlot signalSlot creditSlot synapse =>
      redemptionProtocol
        (code (receiptChannel source receiptSlot))
        (code (signalChannel source signalSlot))
        (code (creditChannel source creditSlot))
        (code (.receiptEmpty receiptSlot))
        (code (.signalEmpty signalSlot))
        (code (.creditAt creditSlot (.synapse synapse)))
  | .expireReceipt receiptSlot =>
      replacementProtocol
        (code (receiptChannel source receiptSlot))
        (code (.receiptEmpty receiptSlot))
  | .expireSignal signalSlot =>
      replacementProtocol
        (code (signalChannel source signalSlot))
        (code (.signalEmpty signalSlot))

noncomputable def causalTargetProtocol
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) : ResourceProtocol :=
  let code : CreditImageChannel Synapse Neuron
      receiptSlots signalSlots creditBudget → Nat := imageChannelCode
  match action with
  | .fire receiptSlot _ =>
      replacementTargetProtocol (code (receiptChannel target receiptSlot))
  | .signal signalSlot _ =>
      replacementTargetProtocol (code (signalChannel target signalSlot))
  | .redeem receiptSlot signalSlot creditSlot _ =>
      redemptionTargetProtocol
        (code (receiptChannel target receiptSlot))
        (code (signalChannel target signalSlot))
        (code (creditChannel target creditSlot))
  | .expireReceipt receiptSlot =>
      replacementTargetProtocol (code (receiptChannel target receiptSlot))
  | .expireSignal signalSlot =>
      replacementTargetProtocol (code (signalChannel target signalSlot))

theorem causalSourceProtocol_toRho
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (source : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    StructuralCongruence
      (causalSourceProtocol source action).toRho
      (causalActionSource source action []) := by
  cases action <;>
    simp only [causalSourceProtocol, causalActionSource] <;>
    first
    | exact replacementProtocol_toRho _ _
    | exact redemptionProtocol_toRho _ _ _ _ _ _

theorem causalTargetProtocol_toRho
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    StructuralCongruence
      (causalTargetProtocol target action).toRho
      (causalActionTarget target action []) := by
  cases action <;>
    simp only [causalTargetProtocol, causalActionTarget] <;>
    first
    | exact replacementTargetProtocol_toRho _
    | exact redemptionTargetProtocol_toRho _ _ _

/-- **Actual Cost-image commuting square for the complete causal language.**
Both endpoints obtained by compiling into concrete Cost syntax and applying
`CostTerm.erase` agree up to rho structural congruence with the endpoints of
the direct pure-rho causal-credit compiler. -/
theorem causalCostImage_commutingSquare
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    StructuralCongruence
        ((causalSourceProtocol source action).toCost.erase
          creditCostSignatureName)
        (causalActionSource source action []) ∧
      StructuralCongruence
        ((causalTargetProtocol target action).toCost.erase
          creditCostSignatureName)
        (causalActionTarget target action []) := by
  constructor
  · exact StructuralCongruence.trans _ _ _
      (ResourceProtocol.erase_toCost_structurallyCongruent_toRho _)
      (causalSourceProtocol_toRho source action)
  · exact StructuralCongruence.trans _ _ _
      (ResourceProtocol.erase_toCost_structurallyCongruent_toRho _)
      (causalTargetProtocol_toRho target action)

/-- Both concrete Cost endpoints in the commuting square belong to the
runtime-supported fragment. -/
theorem causalCostImage_runtimeSupported
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    (source target : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (action : CausalCreditAction Synapse Neuron
      receiptSlots signalSlots creditBudget) :
    (causalSourceProtocol source action).toCost.RuntimeSupported ∧
      (causalTargetProtocol target action).toCost.RuntimeSupported :=
  ⟨ResourceProtocol.toCost_runtimeSupported _,
    ResourceProtocol.toCost_runtimeSupported _⟩

end WeightedGSLTCostImage
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
