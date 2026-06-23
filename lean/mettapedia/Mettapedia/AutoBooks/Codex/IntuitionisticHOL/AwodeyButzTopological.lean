import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Maps.Basic
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Types

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open TopologicalSpace Topology

universe u v w z

/--
Awodey-Butz's topological carrier notion: an etale space over a base space.

This is the archive-free semantic starting point for the topological/sheaf route:
a space `E` together with a local homeomorphism `E → X`.
-/
structure EtaleSpace (X : Type u) [TopologicalSpace X] where
  Carrier : Type v
  carrierTopologicalSpace : TopologicalSpace Carrier
  proj : Carrier → X
  isLocalHomeomorph_proj : IsLocalHomeomorph proj

attribute [instance] EtaleSpace.carrierTopologicalSpace

namespace EtaleSpace

variable {X : Type u} [TopologicalSpace X]

/-- The fiber of an etale space over a base point. -/
def fiber (E : EtaleSpace X) (x : X) : Type v :=
  { e : E.Carrier // E.proj e = x }

/-- The projection of an etale space is continuous. -/
theorem continuous_proj (E : EtaleSpace X) : Continuous E.proj :=
  E.isLocalHomeomorph_proj.continuous

/-- The projection of an etale space is an open map. -/
theorem isOpenMap_proj (E : EtaleSpace X) : IsOpenMap E.proj :=
  E.isLocalHomeomorph_proj.isOpenMap

/-- The identity map is the simplest etale space over `X`. -/
def refl (X : Type u) [TopologicalSpace X] : EtaleSpace X where
  Carrier := X
  carrierTopologicalSpace := inferInstance
  proj := id
  isLocalHomeomorph_proj := (Homeomorph.refl X).isLocalHomeomorph

/-- Every open subset gives an etale space by inclusion into the base. -/
def ofOpen (U : Set X) (hU : IsOpen U) : EtaleSpace X where
  Carrier := U
  carrierTopologicalSpace := inferInstance
  proj := Subtype.val
  isLocalHomeomorph_proj :=
    Topology.IsOpenEmbedding.isLocalHomeomorph hU.isOpenEmbedding_subtypeVal

/--
A local section of an etale space, expressed in the elementary topological form
used in the paper: an open domain and a continuous map over that domain whose
projection back to the base is the inclusion.
-/
structure LocalSection (E : EtaleSpace X) where
  domain : Set X
  isOpen_domain : IsOpen domain
  toContinuousMap : C(domain, E.Carrier)
  proj_comp : E.proj ∘ toContinuousMap = Subtype.val

namespace LocalSection

variable {E : EtaleSpace X}

/-- The range of a local section inside the total space. -/
def range (s : E.LocalSection) : Set E.Carrier :=
  Set.range s.toContinuousMap

/-- Continuous local sections of an etale projection are open embeddings. -/
  theorem isOpenEmbedding (s : E.LocalSection) : IsOpenEmbedding s.toContinuousMap := by
  have hcomp : IsOpenEmbedding (E.proj ∘ s.toContinuousMap) := by
    simpa [s.proj_comp] using s.isOpen_domain.isOpenEmbedding_subtypeVal
  exact IsLocalHomeomorph.isOpenEmbedding_of_comp
    E.isLocalHomeomorph_proj hcomp s.toContinuousMap.continuous

/-- The range of a local section is open in the total space. -/
theorem isOpen_range (s : E.LocalSection) : IsOpen s.range := by
  simpa [range] using s.isOpenEmbedding.isOpen_range

/-- A point in the range of a local section projects into its domain. -/
theorem proj_mem_domain_of_mem_range (s : E.LocalSection) {x : E.Carrier}
    (hx : x ∈ s.range) : E.proj x ∈ s.domain := by
  rcases hx with ⟨y, rfl⟩
  have hy : E.proj (s.toContinuousMap y) = y.1 := congrFun s.proj_comp y
  exact hy ▸ y.property

/--
A point in the range of a local section is recovered by evaluating the section
at its base projection.
-/
theorem toContinuousMap_proj_of_mem_range (s : E.LocalSection) {x : E.Carrier}
    (hx : x ∈ s.range) :
    s.toContinuousMap ⟨E.proj x, s.proj_mem_domain_of_mem_range hx⟩ = x := by
  rcases hx with ⟨y, rfl⟩
  have hy :
      (⟨E.proj (s.toContinuousMap y), s.proj_mem_domain_of_mem_range ⟨y, rfl⟩⟩ : s.domain) = y := by
    apply Subtype.ext
    exact congrFun s.proj_comp y
  exact congrArg s.toContinuousMap hy

end LocalSection

/-- Every point of an etale space lies in the range of some local section. -/
theorem exists_localSection_through (E : EtaleSpace X) (x : E.Carrier) :
    ∃ s : E.LocalSection, x ∈ s.range := by
  classical
  obtain ⟨e, hx, hEq⟩ := E.isLocalHomeomorph_proj x
  let s : E.LocalSection := {
    domain := e.target
    isOpen_domain := e.open_target
    toContinuousMap :=
      { toFun := fun y => e.toHomeomorphSourceTarget.symm y
        continuous_toFun := continuous_subtype_val.comp e.toHomeomorphSourceTarget.symm.continuous }
    proj_comp := by
      funext y
      have hy :
          (((e.toHomeomorphSourceTarget.symm y : e.source) : E.Carrier) ∈ e.source) :=
        (e.toHomeomorphSourceTarget.symm y).property
      exact (congrFun hEq (((e.toHomeomorphSourceTarget.symm y : e.source) : E.Carrier))).trans
        (by exact e.right_inv y.property) }
  refine ⟨s, ?_⟩
  refine ⟨⟨e x, e.map_source hx⟩, ?_⟩
  exact e.left_inv hx

/-- A chosen local section through a given point. -/
noncomputable def localSectionThrough (E : EtaleSpace X) (x : E.Carrier) : E.LocalSection :=
  Classical.choose (E.exists_localSection_through x)

/-- The chosen local section through a point contains that point in its range. -/
theorem mem_range_localSectionThrough (E : EtaleSpace X) (x : E.Carrier) :
    x ∈ (E.localSectionThrough x).range :=
  Classical.choose_spec (E.exists_localSection_through x)

/--
A global section is just a local section over the whole base space.
Awodey-Butz interpret constant symbols by such sections.
-/
structure GlobalSection (E : EtaleSpace X) where
  toContinuousMap : C(X, E.Carrier)
  proj_comp : E.proj ∘ toContinuousMap = id

namespace GlobalSection

variable {E : EtaleSpace X}

/-- Every global section induces a local section over `univ`. -/
def toLocalSection (s : E.GlobalSection) : E.LocalSection where
  domain := Set.univ
  isOpen_domain := isOpen_univ
  toContinuousMap :=
    { toFun := fun x => s.toContinuousMap x.1
      continuous_toFun := s.toContinuousMap.continuous.comp continuous_subtype_val }
  proj_comp := by
    funext x
    exact congrFun s.proj_comp x.1

@[simp] theorem range_toLocalSection (s : E.GlobalSection) :
    s.toLocalSection.range = Set.range s.toContinuousMap := by
  ext e
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, Set.mem_univ x⟩, rfl⟩

end GlobalSection

/--
Ranges of local sections form a topological basis of the total space.

This is the elementary etale-space fact highlighted in the paper's discussion of
sheaves versus etale spaces.
-/
theorem isTopologicalBasis_ranges (E : EtaleSpace X) :
    IsTopologicalBasis { U : Set E.Carrier | ∃ s : E.LocalSection, s.range = U } := by
  have hEq :
      { U : Set E.Carrier | ∃ s : E.LocalSection, s.range = U } =
        { U : Set E.Carrier |
            ∃ V : Set X, IsOpen V ∧
              ∃ s : C(V, E.Carrier), E.proj ∘ s = (↑) ∧ Set.range s = U } := by
    ext U
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.domain, s.isOpen_domain, s.toContinuousMap, s.proj_comp, rfl⟩
    · rintro ⟨V, hV, s, hs, rfl⟩
      exact ⟨⟨V, hV, s, hs⟩, rfl⟩
  rw [hEq]
  exact E.isLocalHomeomorph_proj.isTopologicalBasis

/-- If the base space is discrete, then every etale space over it is discrete. -/
theorem discreteTopology_of_discrete_base (E : EtaleSpace X) [DiscreteTopology X] :
    DiscreteTopology E.Carrier :=
  E.isLocalHomeomorph_proj.comap_discreteTopology

/--
First paper-faithful typed interface for the topological route.

This only records the semantic carriers and the interpretation of constants as
global sections; product, exponential, and formula semantics are future work.
-/
structure BasicTopologicalInterpretation
    (Base : Type u) (Const : Ty Base → Type v)
    (X : Type w) [TopologicalSpace X] where
  space : Ty Base → EtaleSpace.{w, z} X
  const : {τ : Ty Base} → Const τ → (space τ).GlobalSection

end EtaleSpace

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
