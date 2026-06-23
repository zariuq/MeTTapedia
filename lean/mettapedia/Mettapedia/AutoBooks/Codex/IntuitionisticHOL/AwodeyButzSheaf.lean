import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSections

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open CategoryTheory Opposite TopCat TopCat.Presheaf
open TopologicalSpace TopologicalSpace.Opens
open Topology

universe u v

namespace EtaleSpace

variable {X : Type u} [TopologicalSpace X]

namespace SectionOn

variable {E : EtaleSpace X}
variable {ι : Type v}

/-- The open union covered by a family of opens. -/
abbrev unionOpen (U : ι → Opens X) : Opens X :=
  ⨆ i, U i

/-- The subset of the union-open corresponding to one member of the cover. -/
def coverSet (U : ι → Opens X) (i : ι) : Set ↥(unionOpen U) :=
  { x | x.1 ∈ U i }

theorem isOpen_coverSet (U : ι → Opens X) (i : ι) :
    IsOpen (coverSet U i) := by
  change IsOpen ((Subtype.val : ↥(unionOpen U) → X) ⁻¹' (U i : Set X))
  exact (U i).isOpen.preimage continuous_subtype_val

/-- A compatible local section on `U i`, viewed over the corresponding subset of `⋃ᵢ Uᵢ`. -/
def coverMap (U : ι → Opens X) (sf : ∀ i, E.SectionOn (U i)) (i : ι) :
    C(coverSet U i, E.Carrier) where
  toFun := fun x => (sf i).toContinuousMap ⟨x.1.1, x.2⟩
  continuous_toFun :=
    (sf i).toContinuousMap.continuous.comp <|
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x => x.2

/-- A point of `U i` viewed as a point of the union-open. -/
def unionPoint (U : ι → Opens X) (i : ι) (x : U i) : ↥(unionOpen U) :=
  ⟨x.1, mem_iSup.mpr ⟨i, x.2⟩⟩

/-- A point of the union-open lying in `U i`, viewed in the lifted cover set. -/
def coverPoint (U : ι → Opens X) (i : ι) (x : ↥(unionOpen U)) (hxi : x.1 ∈ U i) :
    coverSet U i :=
  ⟨x, by simpa [coverSet] using hxi⟩

theorem cover_mem_nhds (U : ι → Opens X) :
    ∀ x : ↥(unionOpen U), ∃ i, coverSet U i ∈ 𝓝 x := by
  intro x
  rcases mem_iSup.mp x.2 with ⟨i, hxi⟩
  exact ⟨i, (isOpen_coverSet U i).mem_nhds hxi⟩

theorem coverMap_compatible (U : ι → Opens X) (sf : ∀ i, E.SectionOn (U i))
    (hcompat : IsCompatible (sectionPresheaf E) U sf) :
    ∀ (i j) (x : ↥(unionOpen U)) (hxi : x ∈ coverSet U i) (hxj : x ∈ coverSet U j),
      coverMap U sf i ⟨x, hxi⟩ = coverMap U sf j ⟨x, hxj⟩ := by
  intro i j x hxi hxj
  have hxi' : x.1 ∈ U i := by
    simpa [coverSet] using hxi
  have hxj' : x.1 ∈ U j := by
    simpa [coverSet] using hxj
  have hij :=
    congrArg
      (fun t : E.SectionOn (U i ⊓ U j) => t.toContinuousMap ⟨x.1, ⟨hxi', hxj'⟩⟩)
      (hcompat i j)
  dsimp [sectionPresheaf, SectionOn.restrict, coverMap] at hij ⊢
  exact hij

/-- The glued section over the union-open of a compatible family of sections. -/
noncomputable def glue (U : ι → Opens X)
    (sf : ∀ i, E.SectionOn (U i))
    (hcompat : IsCompatible (sectionPresheaf E) U sf) :
    E.SectionOn (unionOpen U) where
  toContinuousMap :=
    ContinuousMap.liftCover
      (coverSet U)
      (coverMap U sf)
      (coverMap_compatible U sf hcompat)
      (cover_mem_nhds U)
  proj_comp := by
    funext x
    rcases mem_iSup.mp x.2 with ⟨i, hxi⟩
    have hglue :
        ContinuousMap.liftCover
            (coverSet U)
            (coverMap U sf)
            (coverMap_compatible U sf hcompat)
            (cover_mem_nhds U) x =
          (sf i).toContinuousMap ⟨x.1, hxi⟩ := by
      simpa [coverMap, coverPoint] using
        (ContinuousMap.liftCover_coe
          (S := coverSet U)
          (φ := coverMap U sf)
          (hφ := coverMap_compatible U sf hcompat)
          (hS := cover_mem_nhds U)
          (x := coverPoint U i x hxi))
    simpa [Function.comp, hglue] using congrFun (sf i).proj_comp ⟨x.1, hxi⟩

theorem glue_isGluing (U : ι → Opens X)
    (sf : ∀ i, E.SectionOn (U i))
    (hcompat : IsCompatible (sectionPresheaf E) U sf) :
    IsGluing (sectionPresheaf E) U sf (glue U sf hcompat) := by
  intro i
  apply SectionOn.ext
  intro x
  have hglue :
      (glue U sf hcompat).toContinuousMap (unionPoint U i x) = (sf i).toContinuousMap x := by
    simpa [glue, coverMap, coverPoint, unionPoint] using
      (ContinuousMap.liftCover_coe
        (S := coverSet U)
        (φ := coverMap U sf)
        (hφ := coverMap_compatible U sf hcompat)
        (hS := cover_mem_nhds U)
        (x := coverPoint U i (unionPoint U i x) x.2))
  dsimp [sectionPresheaf, SectionOn.restrict, unionPoint] at hglue ⊢
  exact hglue

theorem eq_glue_of_isGluing (U : ι → Opens X)
    (sf : ∀ i, E.SectionOn (U i))
    (hcompat : IsCompatible (sectionPresheaf E) U sf)
    (s : E.SectionOn (unionOpen U))
    (hs : IsGluing (sectionPresheaf E) U sf s) :
    s = glue U sf hcompat := by
  apply SectionOn.ext
  intro x
  rcases mem_iSup.mp x.2 with ⟨i, hxi⟩
  have hsx :
      s.toContinuousMap x = (sf i).toContinuousMap ⟨x.1, hxi⟩ := by
    have hsi :=
      congrArg
        (fun t : E.SectionOn (U i) => t.toContinuousMap ⟨x.1, hxi⟩)
        (hs i)
    dsimp [sectionPresheaf, SectionOn.restrict] at hsi
    exact hsi
  have hgx :
      (glue U sf hcompat).toContinuousMap x = (sf i).toContinuousMap ⟨x.1, hxi⟩ := by
    simpa [glue, coverMap, coverPoint] using
      (ContinuousMap.liftCover_coe
        (S := coverSet U)
        (φ := coverMap U sf)
        (hφ := coverMap_compatible U sf hcompat)
        (hS := cover_mem_nhds U)
        (x := coverPoint U i x hxi))
  exact hsx.trans hgx.symm

end SectionOn

theorem sectionPresheaf_isSheafUniqueGluing (E : EtaleSpace X) :
    (sectionPresheaf E).IsSheafUniqueGluing := by
  intro ι U sf hcompat
  refine ⟨SectionOn.glue U sf hcompat, SectionOn.glue_isGluing U sf hcompat, ?_⟩
  intro s hs
  exact SectionOn.eq_glue_of_isGluing U sf hcompat s hs

theorem sectionPresheaf_isSheaf (E : EtaleSpace X) :
    (sectionPresheaf E).IsSheaf :=
  TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types (F := sectionPresheaf E)
    (sectionPresheaf_isSheafUniqueGluing E)

end EtaleSpace

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
