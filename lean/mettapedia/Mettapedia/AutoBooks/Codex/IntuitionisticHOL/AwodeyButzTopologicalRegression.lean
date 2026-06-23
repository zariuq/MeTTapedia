import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzTopological

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzTopologicalRegression

open TopologicalSpace

abbrev X := Bool

instance : TopologicalSpace X := ⊥

def reflEtale : EtaleSpace X :=
  EtaleSpace.refl X

def trueSection : reflEtale.LocalSection where
  domain := { b : X | b = true }
  isOpen_domain := isOpen_discrete _
  toContinuousMap :=
    { toFun := fun x => x.1
      continuous_toFun := continuous_subtype_val }
  proj_comp := rfl

def emptySection : reflEtale.LocalSection where
  domain := (∅ : Set X)
  isOpen_domain := isOpen_empty
  toContinuousMap :=
    { toFun := fun x => False.elim x.2
      continuous_toFun := continuous_of_discreteTopology }
  proj_comp := by
    funext x
    exact False.elim x.2

theorem reflEtale_proj_continuous : Continuous reflEtale.proj :=
  reflEtale.continuous_proj

theorem reflEtale_proj_isOpenMap : IsOpenMap reflEtale.proj :=
  reflEtale.isOpenMap_proj

theorem trueSection_range :
    trueSection.range = { b : X | b = true } := by
  ext b
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hb
    exact ⟨⟨b, hb⟩, rfl⟩

theorem trueSection_range_isOpen : IsOpen trueSection.range := by
  simpa [trueSection_range] using trueSection.isOpen_range

theorem false_not_mem_trueSection_range : false ∉ trueSection.range := by
  rw [trueSection_range]
  intro h
  cases h

theorem emptySection_range : emptySection.range = (∅ : Set X) := by
  ext b
  constructor
  · rintro ⟨x, _⟩
    exact False.elim x.2
  · intro hb
    exact False.elim hb

theorem reflEtale_discrete : DiscreteTopology reflEtale.Carrier :=
  reflEtale.discreteTopology_of_discrete_base

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzTopologicalRegression
