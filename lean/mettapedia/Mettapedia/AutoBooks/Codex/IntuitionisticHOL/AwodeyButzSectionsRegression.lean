import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSections

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSectionsRegression

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

abbrev X := Bool

instance : TopologicalSpace X := ⊥

def reflEtale : EtaleSpace X :=
  EtaleSpace.refl X

def topSection : reflEtale.GlobalSection where
  toContinuousMap :=
    { toFun := id
      continuous_toFun := continuous_id }
  proj_comp := rfl

def trueOpen : Opens X :=
  ⟨{ b : X | b = true }, isOpen_discrete _⟩

def emptyOpen : Opens X := ⊥

def trueInclTop : trueOpen ⟶ ⊤ :=
  (le_top : trueOpen ≤ ⊤).hom

def emptyInclTrue : emptyOpen ⟶ trueOpen :=
  (bot_le : emptyOpen ≤ trueOpen).hom

def emptyInclTop : emptyOpen ⟶ ⊤ :=
  (le_top : emptyOpen ≤ ⊤).hom

def trueSectionOn : reflEtale.SectionOn trueOpen where
  toContinuousMap :=
    { toFun := fun x => x.1
      continuous_toFun := continuous_subtype_val }
  proj_comp := rfl

def emptySectionOn : reflEtale.SectionOn emptyOpen where
  toContinuousMap :=
    { toFun := fun x => False.elim x.2
      continuous_toFun := continuous_of_discreteTopology }
  proj_comp := by
    funext x
    exact False.elim x.2

theorem topSection_toSectionOnTop_roundtrip :
    EtaleSpace.GlobalSection.ofSectionOnTop topSection.toSectionOnTop = topSection := by
  simp

theorem trueRestriction_of_topSection :
    topSection.toSectionOnTop.restrict trueInclTop = trueSectionOn := by
  ext x
  rfl

theorem emptyRestriction_of_topSection :
    topSection.toSectionOnTop.restrict emptyInclTop = emptySectionOn := by
  ext x
  exact False.elim x.2

theorem topSection_restrict_id :
    topSection.toSectionOnTop.restrict (𝟙 ⊤) = topSection.toSectionOnTop := by
  simp

theorem topSection_restrict_comp :
    (topSection.toSectionOnTop.restrict trueInclTop).restrict emptyInclTrue =
      topSection.toSectionOnTop.restrict (emptyInclTrue ≫ trueInclTop) := by
  exact topSection.toSectionOnTop.restrict_comp emptyInclTrue trueInclTop

theorem false_not_mem_trueRestriction_range :
    false ∉
      ((topSection.toSectionOnTop.restrict trueInclTop).toLocalSection.range : Set reflEtale.Carrier) := by
  rw [trueRestriction_of_topSection]
  intro hfalse
  rcases hfalse with ⟨x, hx⟩
  rcases x with ⟨b, hb⟩
  cases b <;> simp [trueOpen, trueSectionOn, EtaleSpace.SectionOn.toLocalSection] at hb hx

theorem sectionPresheaf_obj_top :
    reflEtale.sectionPresheaf.obj (Opposite.op ⊤) = reflEtale.SectionOn ⊤ := rfl

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSectionsRegression
