import Mathlib.Topology.Sheaves.Presheaf
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzTopological

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u v

namespace EtaleSpace

variable {X : Type u} [TopologicalSpace X]

/--
A section of an etale space over a fixed open set `U`.

This is the `Opens X`-indexed form of local sections, set up so restriction and
presheaf structure can be stated directly.
-/
structure SectionOn (E : EtaleSpace X) (U : Opens X) where
  toContinuousMap : C(U, E.Carrier)
  proj_comp : E.proj ∘ toContinuousMap = Subtype.val

namespace SectionOn

variable {E : EtaleSpace X} {U V W : Opens X}

/-- A section over an open set gives a local section on the underlying subset. -/
def toLocalSection (s : E.SectionOn U) : E.LocalSection where
  domain := U
  isOpen_domain := U.2
  toContinuousMap := s.toContinuousMap
  proj_comp := s.proj_comp

/-- A local section can be repackaged as a section over its open domain. -/
def ofLocalSection (s : E.LocalSection) : E.SectionOn ⟨s.domain, s.isOpen_domain⟩ where
  toContinuousMap := s.toContinuousMap
  proj_comp := s.proj_comp

@[simp] theorem toLocalSection_ofLocalSection (s : E.LocalSection) :
    (SectionOn.ofLocalSection s).toLocalSection = s := by
  cases s
  rfl

@[simp] theorem ofLocalSection_toLocalSection (s : E.SectionOn U) :
    SectionOn.ofLocalSection s.toLocalSection = s := by
  cases s
  rfl

@[ext] theorem ext (s t : E.SectionOn U)
    (h : ∀ x : U, s.toContinuousMap x = t.toContinuousMap x) : s = t := by
  cases s with
  | mk s hs =>
    cases t with
    | mk t ht =>
      simp only at h
      have hMap : s = t := by
        ext x
        exact h x
      subst hMap
      simp

/-- Restrict a section along an inclusion of open sets. -/
def restrict (i : V ⟶ U) (s : E.SectionOn U) : E.SectionOn V where
  toContinuousMap :=
    { toFun := fun x => s.toContinuousMap ⟨x.1, i.le x.2⟩
      continuous_toFun :=
        s.toContinuousMap.continuous.comp (Opens.isOpenEmbedding_of_le i.le).continuous }
  proj_comp := by
    funext x
    exact congrFun s.proj_comp ⟨x.1, i.le x.2⟩

@[simp] theorem restrict_apply (i : V ⟶ U) (s : E.SectionOn U) (x : V) :
    (s.restrict i).toContinuousMap x = s.toContinuousMap ⟨x.1, i.le x.2⟩ :=
  rfl

@[simp] theorem restrict_id (s : E.SectionOn U) :
    s.restrict (𝟙 U) = s := by
  ext x
  simp [restrict]

@[simp] theorem restrict_comp (f : W ⟶ V) (g : V ⟶ U) (s : E.SectionOn U) :
    (s.restrict g).restrict f = s.restrict (f ≫ g) := by
  ext x
  rfl

@[simp] theorem toLocalSection_restrict (i : V ⟶ U) (s : E.SectionOn U) :
    (s.restrict i).toLocalSection =
      { domain := V
        isOpen_domain := V.2
        toContinuousMap :=
          { toFun := fun x => s.toContinuousMap ⟨x.1, i.le x.2⟩
            continuous_toFun :=
              s.toContinuousMap.continuous.comp (Opens.isOpenEmbedding_of_le i.le).continuous }
        proj_comp := by
          funext x
          exact congrFun s.proj_comp ⟨x.1, i.le x.2⟩ } := by
  rfl

end SectionOn

namespace GlobalSection

variable {E : EtaleSpace X}

/-- A global section is a section over the top open set. -/
def toSectionOnTop (s : E.GlobalSection) : E.SectionOn ⊤ where
  toContinuousMap :=
    { toFun := fun x => s.toContinuousMap x.1
      continuous_toFun := s.toContinuousMap.continuous.comp continuous_subtype_val }
  proj_comp := by
    funext x
    exact congrFun s.proj_comp x.1

/-- A section over the top open set is a global section. -/
def ofSectionOnTop (s : E.SectionOn ⊤) : E.GlobalSection where
  toContinuousMap :=
    { toFun := fun x => s.toContinuousMap ⟨x, trivial⟩
      continuous_toFun := s.toContinuousMap.continuous.comp (continuous_id.subtype_mk fun _ => trivial) }
  proj_comp := by
    funext x
    exact congrFun s.proj_comp ⟨x, trivial⟩

@[simp] theorem ofSectionOnTop_toSectionOnTop (s : E.GlobalSection) :
    (GlobalSection.ofSectionOnTop s.toSectionOnTop) = s := by
  cases s
  rfl

@[simp] theorem toSectionOnTop_ofSectionOnTop (s : E.SectionOn ⊤) :
    (GlobalSection.ofSectionOnTop s).toSectionOnTop = s := by
  ext x
  rfl

/-- Global sections are equivalent to sections over the top open. -/
def sectionOnTopEquiv (E : EtaleSpace X) :
    E.GlobalSection ≃ E.SectionOn ⊤ where
  toFun := GlobalSection.toSectionOnTop
  invFun := GlobalSection.ofSectionOnTop
  left_inv := ofSectionOnTop_toSectionOnTop
  right_inv := toSectionOnTop_ofSectionOnTop

end GlobalSection

/-- The presheaf of sections of an etale space. -/
def sectionPresheaf (E : EtaleSpace X) : (TopCat.of X).Presheaf (Type _) where
  obj U := E.SectionOn U.unop
  map {U V} i :=
    TypeCat.ofHom (fun s : E.SectionOn U.unop => s.restrict i.unop)
  map_id := by
    intro U
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    rfl
  map_comp := by
    intro U V W f g
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    rfl

end EtaleSpace

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
