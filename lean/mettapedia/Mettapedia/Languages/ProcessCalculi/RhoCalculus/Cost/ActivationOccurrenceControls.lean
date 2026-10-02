import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceCover

/-!
# Exact participant and purse occurrence controls

The same cover interface exposes actual ambient borrowing and two-cell split
funding. Equal signing atoms still require two distinct physical cells. The
whole borrowing witness retains an empty purse in its unconsumed frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceControls

def location : RawCostName := .quote .nil

def borrowedConfig (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) : RawCostConfig :=
  [.signed (.par (.recv location body) (.send location payload)) [authority],
   .purse location [], .purse location ([authority] :: tail)]

def borrowedCover (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    RawWholeOccurrenceCover (borrowedConfig body payload authority tail) where
  redex := ⟨0, location, body, payload, [authority]⟩
  source := .signed (.par (.recv location body) (.send location payload)) [authority]
  occurrence := by simp [borrowedConfig, List.zipIdx]
  found := rfl
  selected := [⟨2, location, [authority], tail⟩]
  sourceOrdered := by simp [borrowedConfig, RawCostConfig.purses, collectPursesAux]
  located := by intro purse member; simp only [List.mem_singleton] at member; subst purse; rfl
  exactSpend := by simp [rawSelectedSpend, RawCostSig.toMultiset]

theorem borrowed_cover_enabled (body payload : RawCostTerm) (authority : String) (tail : RawCostStack)
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (tailValid : tail.all RawCostSig.valid = true) :
    (borrowedCover body payload authority tail).runtimeStep ∈
      runtimeCostCandidatesFromConfig (borrowedConfig body payload authority tail) := by
  apply RawWholeOccurrenceCover.enabled
  simp [borrowedConfig, RawCostTerm.wellFormed, RawCostProc.wellFormed, location,
    RawCostName.wellFormed, RawCostSig.valid, bodyValid, payloadValid, tailValid]

theorem borrowed_cover_indices (body payload : RawCostTerm) (authority : String) (tail : RawCostStack) :
    (borrowedCover body payload authority tail).runtimeStep.participantIndices = [0] ∧
    ((borrowedCover body payload authority tail).runtimeStep.selectedPurses.map RawIndexedPurse.index) = [2] ∧
    eraseIndices (borrowedConfig body payload authority tail) [0, 2] = [.purse location []] := by
  simp [borrowedCover, RawWholeOccurrenceCover.runtimeStep, borrowedConfig, eraseIndices, List.zipIdx]

def splitConfig (body payload : RawCostTerm) (authority : String) (recvTail sendTail : RawCostStack) : RawCostConfig :=
  [.signed (.recv location body) [authority], .signed (.send location payload) [authority],
   .purse location ([authority] :: recvTail), .purse location ([authority] :: sendTail)]

def splitCover (body payload : RawCostTerm) (authority : String) (recvTail sendTail : RawCostStack) :
    RawSplitOccurrenceCover (splitConfig body payload authority recvTail sendTail) where
  receiver := ⟨0, location, body, [authority]⟩
  sender := ⟨1, location, payload, [authority]⟩
  recvSource := .signed (.recv location body) [authority]
  sendSource := .signed (.send location payload) [authority]
  recvOccurrence := by simp [splitConfig, List.zipIdx]
  sendOccurrence := by simp [splitConfig, List.zipIdx]
  recvFound := rfl
  sendFound := rfl
  sameLocation := rfl
  selected := [⟨2, location, [authority], recvTail⟩, ⟨3, location, [authority], sendTail⟩]
  sourceOrdered := by simp [splitConfig, RawCostConfig.purses, collectPursesAux]
  located := by
    intro purse member
    simp at member
    rcases member with rfl | rfl <;> rfl
  exactSpend := by
    change rawSelectedSpend
      [⟨2, location, [authority], recvTail⟩, ⟨3, location, [authority], sendTail⟩] =
        (RawCostSig.normalize [authority, authority] : Multiset String)
    rw [RawCostSig.normalize_toMultiset]
    simp [rawSelectedSpend, RawCostSig.toMultiset]
    rfl

theorem split_cover_enabled (body payload : RawCostTerm) (authority : String) (recvTail sendTail : RawCostStack)
    (bodyValid : body.wellFormed = true) (payloadValid : payload.wellFormed = true)
    (recvTailValid : recvTail.all RawCostSig.valid = true) (sendTailValid : sendTail.all RawCostSig.valid = true) :
    (splitCover body payload authority recvTail sendTail).runtimeStep ∈
      runtimeCostCandidatesFromConfig (splitConfig body payload authority recvTail sendTail) := by
  apply RawSplitOccurrenceCover.enabled
  simp [splitConfig, RawCostTerm.wellFormed, RawCostProc.wellFormed, location,
    RawCostName.wellFormed, RawCostSig.valid, bodyValid, payloadValid, recvTailValid, sendTailValid]

theorem split_equal_atoms_keep_two_occurrences
    (body payload : RawCostTerm) (authority : String) (recvTail sendTail : RawCostStack) :
    (splitCover body payload authority recvTail sendTail).runtimeStep.participantIndices = [0, 1] ∧
    ((splitCover body payload authority recvTail sendTail).runtimeStep.selectedPurses.map RawIndexedPurse.index) = [2, 3] ∧
    (decodeCostSig (splitCover body payload authority recvTail sendTail).runtimeStep.spend).card = 2 := by
  refine ⟨rfl, rfl, ?_⟩
  change (RawCostSig.normalize [authority, authority] : Multiset String).card = 2
  rw [RawCostSig.normalize_toMultiset]
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceControls
