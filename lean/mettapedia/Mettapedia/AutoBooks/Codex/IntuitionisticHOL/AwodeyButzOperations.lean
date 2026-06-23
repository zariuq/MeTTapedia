import Mathlib.Data.Set.Prod
import Mathlib.Topology.Category.TopCat.Opens
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSections

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Function TopologicalSpace TopologicalSpace.Opens Topology

universe u v w

namespace EtaleSpace

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]

/-- The projection of an etale space packaged as a continuous map. -/
def projMap (E : EtaleSpace X) : C(E.Carrier, X) :=
  ⟨E.proj, E.continuous_proj⟩

/-- The terminal etale space over a base is the identity local homeomorphism. -/
abbrev terminal (X : Type u) [TopologicalSpace X] : EtaleSpace X :=
  EtaleSpace.refl X

/--
Pull back an etale space along a continuous map.

This is the elementary base-change construction used by the Awodey-Butz
semantics before one passes to the corresponding sheaf of sections.
-/
def reindex (f : C(Y, X)) (E : EtaleSpace X) : EtaleSpace Y where
  Carrier := Function.Pullback f E.proj
  carrierTopologicalSpace := inferInstance
  proj := Function.Pullback.fst
  isLocalHomeomorph_proj := by
    classical
    refine IsLocalHomeomorph.mk (f := (Function.Pullback.fst : Function.Pullback f E.proj → Y)) ?_
    intro p
    obtain ⟨e, hp, hproj⟩ := E.isLocalHomeomorph_proj p.snd
    let source : Set (Function.Pullback f E.proj) := { q | q.snd ∈ e.source }
    let target : Set Y := f ⁻¹' e.target
    have hsource : IsOpen source := by
      exact e.open_source.preimage (continuous_snd.comp continuous_subtype_val)
    have htarget : IsOpen target := by
      exact e.open_target.preimage f.continuous
    let homeo : source ≃ₜ target := {
      toFun := fun q =>
        ⟨q.1.fst, by
          have hq : q.1.snd ∈ e.source := q.2
          have hEq : f q.1.fst = e q.1.snd := by
            simpa [Function.Pullback.fst, Function.Pullback.snd, hproj] using q.1.property
          change f q.1.fst ∈ e.target
          rw [hEq]
          exact e.map_source hq⟩
      invFun := fun y =>
        ⟨⟨(y.1, (e.toHomeomorphSourceTarget.symm ⟨f y.1, y.2⟩ : e.source)), by
            simpa [hproj] using (e.right_inv y.2).symm⟩,
          (e.toHomeomorphSourceTarget.symm ⟨f y.1, y.2⟩).2⟩
      left_inv := by
        intro q
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hq : q.1.snd ∈ e.source := q.2
          have hEq : f q.1.fst = e q.1.snd := by
            simpa [Function.Pullback.fst, Function.Pullback.snd, hproj] using q.1.property
          simpa [Function.Pullback.snd, hEq] using e.left_inv hq
      right_inv := by
        intro y
        apply Subtype.ext
        rfl
      continuous_toFun := by
          have hfst : Continuous fun q : Function.Pullback f E.proj => q.fst :=
            continuous_fst.comp continuous_subtype_val
          exact (hfst.comp continuous_subtype_val).subtype_mk fun q => by
            have hq : q.1.snd ∈ e.source := q.2
            have hEq : f q.1.fst = e q.1.snd := by
              simpa [Function.Pullback.fst, Function.Pullback.snd, hproj] using q.1.property
            change f q.1.fst ∈ e.target
            rw [hEq]
            exact e.map_source hq
      continuous_invFun := by
        have htargetMap : Continuous fun y : target => (⟨f y.1, y.2⟩ : e.target) :=
          (f.continuous.comp continuous_subtype_val).subtype_mk fun y => y.2
        have hsourceMap :
            Continuous fun y : target => (e.toHomeomorphSourceTarget.symm ⟨f y.1, y.2⟩ : e.source) :=
          e.toHomeomorphSourceTarget.symm.continuous.comp htargetMap
        have hsecond :
            Continuous fun y : target =>
              ((e.toHomeomorphSourceTarget.symm ⟨f y.1, y.2⟩ : e.source) : E.Carrier) :=
          continuous_subtype_val.comp hsourceMap
        have hpair :
            Continuous fun y : target =>
              (y.1, ((e.toHomeomorphSourceTarget.symm ⟨f y.1, y.2⟩ : e.source) : E.Carrier)) :=
          continuous_subtype_val.prodMk hsecond
        have hpullback :
            Continuous fun y : target =>
              (⟨(y.1, ((e.toHomeomorphSourceTarget.symm ⟨f y.1, y.2⟩ : e.source) : E.Carrier)), by
                simpa [hproj] using (e.right_inv y.2).symm⟩ : Function.Pullback f E.proj) :=
          hpair.subtype_mk fun y => by
            simpa [hproj] using (e.right_inv y.2).symm
        exact hpullback.subtype_mk fun y =>
          (e.toHomeomorphSourceTarget.symm ⟨f y.1, y.2⟩).2 }
    let chart :
        OpenPartialHomeomorph (Function.Pullback f E.proj) Y :=
      OpenPartialHomeomorph.ofContinuousOpenRestrict
        { toFun := Function.Pullback.fst
          invFun := fun y =>
            if hy : y ∈ target then
              ⟨(y, (e.toHomeomorphSourceTarget.symm ⟨f y, hy⟩ : e.source)), by
                simpa [Function.Pullback.fst, Function.Pullback.snd, hproj] using (e.right_inv hy).symm⟩
            else p
          source := source
          target := target
          map_source' := by
            intro q hq
            have hEq : f q.fst = e q.snd := by
              simpa [Function.Pullback.fst, Function.Pullback.snd, hproj] using q.property
            change f q.fst ∈ e.target
            rw [hEq]
            exact e.map_source hq
          map_target' := by
            intro y hy
            simpa [hy, source, Function.Pullback.snd] using e.map_target hy
          left_inv' := by
            intro q hq
            have hqy : q.fst ∈ target := by
              have hEq : f q.fst = e q.snd := by
                simpa [Function.Pullback.fst, Function.Pullback.snd, hproj] using q.property
              change f q.fst ∈ e.target
              rw [hEq]
              exact e.map_source hq
            have hqy' : ((q : Function.Pullback f E.proj) : Y × E.Carrier).1 ∈ target := by
              simpa [Function.Pullback.fst] using hqy
            apply Subtype.ext
            apply Prod.ext
            · simp [Function.Pullback.fst, hqy']
            · have hEq : f q.fst = e q.snd := by
                simpa [Function.Pullback.fst, Function.Pullback.snd, hproj] using q.property
              simpa [Function.Pullback.snd, hqy, hEq] using e.left_inv hq
          right_inv' := by
            intro y hy
            simp [hy, Function.Pullback.fst] }
        (by
          have hfst : Continuous fun q : Function.Pullback f E.proj => q.fst :=
            continuous_fst.comp continuous_subtype_val
          exact hfst.continuousOn)
        (by
          have hSubtype : IsOpenMap (Subtype.val : target → Y) :=
            htarget.isOpenMap_subtype_val
          have hHomeo :
              IsOpenMap fun q : source => ((homeo q : target) : Y) :=
            hSubtype.comp homeo.isOpenMap
          show IsOpenMap (fun q : source => q.1.fst)
          dsimp [homeo, Function.Pullback.fst] at hHomeo
          exact hHomeo)
        hsource
    refine ⟨chart, hp, ?_⟩
    intro q hq
    rfl

/--
Fiber product of etale spaces over a common base.

This is the categorical product in the slice over `X`.
-/
def prod (E F : EtaleSpace X) : EtaleSpace X where
  Carrier := Function.Pullback E.proj F.proj
  carrierTopologicalSpace := inferInstance
  proj := fun p => E.proj p.fst
  isLocalHomeomorph_proj := by
    change IsLocalHomeomorph
      (fun p : (reindex E.projMap F).Carrier => E.proj (Function.Pullback.fst p))
    exact E.isLocalHomeomorph_proj.comp (reindex E.projMap F).isLocalHomeomorph_proj

/-- First projection from the fiber product. -/
def prodFst (E F : EtaleSpace X) : C((prod E F).Carrier, E.Carrier) where
  toFun := Function.Pullback.fst
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- Second projection from the fiber product. -/
def prodSnd (E F : EtaleSpace X) : C((prod E F).Carrier, F.Carrier) where
  toFun := Function.Pullback.snd
  continuous_toFun := continuous_snd.comp continuous_subtype_val

@[simp] theorem prod_proj_fst (E F : EtaleSpace X) (p : (prod E F).Carrier) :
    (prod E F).proj p = E.proj (prodFst E F p) :=
  rfl

@[simp] theorem prod_proj_snd (E F : EtaleSpace X) (p : (prod E F).Carrier) :
    E.proj (prodFst E F p) = F.proj (prodSnd E F p) :=
  p.property

/-- Swap the factors of a fiber product. -/
def prodSwap (E F : EtaleSpace X) : C((prod E F).Carrier, (prod F E).Carrier) where
  toFun := fun p => ⟨(p.val.2, p.val.1), p.property.symm⟩
  continuous_toFun := by
    refine (continuous_snd.comp continuous_subtype_val).prodMk ?_ |>.subtype_mk _
    exact continuous_fst.comp continuous_subtype_val

@[simp] theorem prodSwap_fst (E F : EtaleSpace X) (p : (prod E F).Carrier) :
    (prodSwap E F p).val.1 = p.val.2 :=
  rfl

@[simp] theorem prodSwap_snd (E F : EtaleSpace X) (p : (prod E F).Carrier) :
    (prodSwap E F p).val.2 = p.val.1 :=
  rfl

@[simp] theorem prodSwap_proj (E F : EtaleSpace X) (p : (prod E F).Carrier) :
    (prod F E).proj (prodSwap E F p) = (prod E F).proj p := by
  simp only [prod, prodSwap]
  exact p.property.symm

namespace SectionOn

variable {E F : EtaleSpace X}
variable {U : Opens X}
variable {V : Opens Y}

/-- The unique section of the terminal etale space over an open set. -/
def terminal (U : Opens X) : (EtaleSpace.terminal X).SectionOn U where
  toContinuousMap :=
    { toFun := fun x => x.1
      continuous_toFun := continuous_subtype_val }
  proj_comp := by
    funext x
    rfl

theorem terminal_apply (x : U) :
    (terminal U).toContinuousMap x = x.1 :=
  rfl

/-- Pair sections into a section of the fiber product. -/
def pair (s : E.SectionOn U) (t : F.SectionOn U) : (prod E F).SectionOn U where
  toContinuousMap :=
    { toFun := fun x =>
        ⟨(s.toContinuousMap x, t.toContinuousMap x), by
          have hs := congrFun s.proj_comp x
          have ht := congrFun t.proj_comp x
          exact hs.trans ht.symm⟩
      continuous_toFun :=
        (s.toContinuousMap.continuous.prodMk t.toContinuousMap.continuous).subtype_mk fun x => by
          have hs := congrFun s.proj_comp x
          have ht := congrFun t.proj_comp x
          exact hs.trans ht.symm }
  proj_comp := by
    funext x
    exact congrFun s.proj_comp x

/-- First projection of a section of a fiber product. -/
def fst (s : (prod E F).SectionOn U) : E.SectionOn U where
  toContinuousMap := (prodFst E F).comp s.toContinuousMap
  proj_comp := by
    funext x
    exact congrFun s.proj_comp x

/-- Second projection of a section of a fiber product. -/
def snd (s : (prod E F).SectionOn U) : F.SectionOn U where
  toContinuousMap := (prodSnd E F).comp s.toContinuousMap
  proj_comp := by
    funext x
    exact (prod_proj_snd E F (s.toContinuousMap x)).symm.trans (congrFun s.proj_comp x)

/-- Pull back a section along a continuous base map. -/
def pullback (f : C(Y, X)) {W : Opens X} (s : E.SectionOn W) :
    (reindex f E).SectionOn ((Opens.comap f) W) where
  toContinuousMap :=
    { toFun := fun y =>
        ⟨(y.1, s.toContinuousMap ⟨f y.1, y.2⟩), by
          simpa [Function.comp] using (congrFun s.proj_comp ⟨f y.1, y.2⟩).symm⟩
      continuous_toFun := by
        have hbase : Continuous fun y : (Opens.comap f) W => y.1 :=
          continuous_subtype_val
        have hdom : Continuous fun y : (Opens.comap f) W => (⟨f y.1, y.2⟩ : W) :=
          (f.continuous.comp continuous_subtype_val).subtype_mk fun y => y.2
        have hsec :
            Continuous fun y : (Opens.comap f) W => s.toContinuousMap ⟨f y.1, y.2⟩ :=
          s.toContinuousMap.continuous.comp hdom
        exact (hbase.prodMk hsec).subtype_mk fun y => by
          simpa [Function.comp] using (congrFun s.proj_comp ⟨f y.1, y.2⟩).symm }
  proj_comp := by
    funext y
    rfl

@[simp] theorem fst_pair (s : E.SectionOn U) (t : F.SectionOn U) :
    (pair s t).fst = s := by
  ext x
  rfl

@[simp] theorem snd_pair (s : E.SectionOn U) (t : F.SectionOn U) :
    (pair s t).snd = t := by
  ext x
  simp [snd, pair, prodSnd, Function.Pullback.snd]

@[simp] theorem pair_fst_snd (s : (prod E F).SectionOn U) :
    pair s.fst s.snd = s := by
  ext x
  apply Subtype.ext
  apply Prod.ext <;> simp [pair, fst, snd, prodFst, prodSnd, Function.Pullback.fst,
    Function.Pullback.snd]

end SectionOn

namespace GlobalSection

variable {E F : EtaleSpace X}
variable {Z : Type w} [TopologicalSpace Z]

/-- The unique global section of the terminal etale space. -/
def terminal (X : Type u) [TopologicalSpace X] :
    (EtaleSpace.terminal X).GlobalSection where
  toContinuousMap := ContinuousMap.id X
  proj_comp := by
    funext x
    rfl

/-- Pair global sections into a global section of the fiber product. -/
def pair (s : E.GlobalSection) (t : F.GlobalSection) : (prod E F).GlobalSection :=
  GlobalSection.ofSectionOnTop (SectionOn.pair s.toSectionOnTop t.toSectionOnTop)

/-- First projection of a global section of a fiber product. -/
def fst (s : (prod E F).GlobalSection) : E.GlobalSection :=
  GlobalSection.ofSectionOnTop s.toSectionOnTop.fst

/-- Second projection of a global section of a fiber product. -/
def snd (s : (prod E F).GlobalSection) : F.GlobalSection :=
  GlobalSection.ofSectionOnTop s.toSectionOnTop.snd

/-- Pull back a global section along a continuous base map. -/
def pullback (f : C(Z, X)) (s : E.GlobalSection) : (reindex f E).GlobalSection :=
  GlobalSection.ofSectionOnTop (SectionOn.pullback f s.toSectionOnTop)

@[simp] theorem fst_pair (s : E.GlobalSection) (t : F.GlobalSection) :
    (pair s t).fst = s := by
  apply (GlobalSection.sectionOnTopEquiv (E := E)).injective
  simp [fst, pair]

@[simp] theorem snd_pair (s : E.GlobalSection) (t : F.GlobalSection) :
    (pair s t).snd = t := by
  apply (GlobalSection.sectionOnTopEquiv (E := F)).injective
  simp [snd, pair]

end GlobalSection

end EtaleSpace

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
