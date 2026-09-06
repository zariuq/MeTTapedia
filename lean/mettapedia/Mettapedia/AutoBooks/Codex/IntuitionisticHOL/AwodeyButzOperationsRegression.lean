import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzOperations

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzOperationsRegression

local instance : TopologicalSpace Bool := ⊥

def constTrue : C(Bool, Bool) where
  toFun := fun _ => true
  continuous_toFun := by
    continuity

def idSection : (EtaleSpace.refl Bool).GlobalSection :=
  EtaleSpace.GlobalSection.terminal Bool

def pairedIdSection : (EtaleSpace.prod (EtaleSpace.refl Bool) (EtaleSpace.refl Bool)).GlobalSection :=
  EtaleSpace.GlobalSection.pair idSection idSection

def pulledIdSection :
    (EtaleSpace.reindex constTrue (EtaleSpace.refl Bool)).GlobalSection :=
  EtaleSpace.GlobalSection.pullback constTrue idSection

theorem terminal_apply (b : Bool) :
    idSection.toContinuousMap b = b :=
  rfl

theorem pairedIdSection_fst :
    pairedIdSection.fst = idSection := by
  simp [pairedIdSection, idSection]

theorem pairedIdSection_snd :
    pairedIdSection.snd = idSection := by
  simp [pairedIdSection, idSection]

theorem pairedIdSection_apply_fst (b : Bool) :
    Function.Pullback.fst (pairedIdSection.toContinuousMap b) = b := by
  rfl

theorem pairedIdSection_apply_snd (b : Bool) :
    Function.Pullback.snd (pairedIdSection.toContinuousMap b) = b := by
  rfl

theorem pulledIdSection_apply_fst (b : Bool) :
    Function.Pullback.fst (pulledIdSection.toContinuousMap b) = b := by
  rfl

theorem pulledIdSection_apply_snd (b : Bool) :
    Function.Pullback.snd (pulledIdSection.toContinuousMap b) = true := by
  rfl

theorem pulledIdSection_apply_snd_ne_false (b : Bool) :
    Function.Pullback.snd (pulledIdSection.toContinuousMap b) ≠ false := by
  rw [pulledIdSection_apply_snd]
  intro impossible
  cases impossible

end AwodeyButzOperationsRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
