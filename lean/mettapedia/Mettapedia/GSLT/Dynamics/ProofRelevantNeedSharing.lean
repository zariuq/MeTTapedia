import Mathlib.Data.Finset.Card
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedProfile

/-!
# Sharing scopes for proof-relevant need

Call-by-need shares demands assigned to the same cell.  Full laziness and
compiled-program reuse ask the same question one level earlier: which dynamic
sites are assigned the same reusable key?

This module keeps that choice outside the cell protocol.  A sharing scheme is
a map from demand sites to keys.  A coarsening maps fine keys to coarse keys
and commutes with allocation.  Coarsening cannot increase the number of
distinct compiled keys in a finite workload.  It is semantically admissible
only when equal coarse keys imply equal declared meanings; this obligation is
not derivable from the corresponding fine scheme.

The theorem concerns the compilation component of cost.  A separating
example records the classical full-laziness boundary: longer retention can
make total cost larger even when compilation count falls.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

universe uSite uFineKey uCoarseKey uObservation uIndex

/-- A language-selected cell or compiled-program identity scheme. -/
structure SharingScheme (Site : Type uSite) where
  Key : Type uFineKey
  decEq : DecidableEq Key
  key : Site -> Key

namespace SharingScheme

variable {Site : Type uSite}

/-- Two sites share precisely when the scheme assigns the same key. -/
def Shares (scheme : SharingScheme Site) (left right : Site) : Prop :=
  scheme.key left = scheme.key right

theorem shares_refl (scheme : SharingScheme Site) (site : Site) :
    scheme.Shares site site :=
  rfl

theorem shares_symm (scheme : SharingScheme Site) {left right : Site}
    (shares : scheme.Shares left right) : scheme.Shares right left :=
  shares.symm

theorem shares_trans (scheme : SharingScheme Site)
    {first second third : Site}
    (firstSecond : scheme.Shares first second)
    (secondThird : scheme.Shares second third) :
    scheme.Shares first third :=
  firstSecond.trans secondThird

/-- A coarsening witnesses that every coarse key is computed uniformly from
the fine key. -/
structure Coarsening
    (fine : SharingScheme.{uSite, uFineKey} Site)
    (coarse : SharingScheme.{uSite, uCoarseKey} Site) where
  mapKey : fine.Key -> coarse.Key
  commutes : ∀ site, mapKey (fine.key site) = coarse.key site

namespace Coarsening

variable {fine : SharingScheme.{uSite, uFineKey} Site}
  {middle : SharingScheme Site}
  {coarse : SharingScheme.{uSite, uCoarseKey} Site}

def id (scheme : SharingScheme Site) : Coarsening scheme scheme where
  mapKey := _root_.id
  commutes := fun _ => rfl

def comp (first : Coarsening fine middle)
    (second : Coarsening middle coarse) : Coarsening fine coarse where
  mapKey := second.mapKey ∘ first.mapKey
  commutes := fun site => by rw [Function.comp_apply, first.commutes,
    second.commutes]

/-- Fine sharing always implies coarse sharing. -/
theorem map_shares (coarsening : Coarsening fine coarse)
    {left right : Site} (shares : fine.Shares left right) :
    coarse.Shares left right := by
  unfold SharingScheme.Shares at shares ⊢
  rw [← coarsening.commutes left, ← coarsening.commutes right, shares]

end Coarsening

/-- The distinct reusable keys demanded by a finite set of sites. -/
def allocatedKeys (scheme : SharingScheme Site) (sites : Finset Site) :
    Finset scheme.Key := by
  letI := scheme.decEq
  exact sites.image scheme.key

theorem allocatedKeys_coarsening
    [DecidableEq Site]
    {fine : SharingScheme.{uSite, uFineKey} Site}
    {coarse : SharingScheme.{uSite, uCoarseKey} Site}
    (coarsening : Coarsening fine coarse) (sites : Finset Site) :
    coarse.allocatedKeys sites =
      @Finset.image fine.Key coarse.Key coarse.decEq coarsening.mapKey
        (fine.allocatedKeys sites) := by
  letI := fine.decEq
  letI := coarse.decEq
  ext coarseKey
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨site, siteMember, keyEquation⟩
    apply Finset.mem_image.2
    refine ⟨fine.key site, Finset.mem_image.2 ⟨site, siteMember, rfl⟩, ?_⟩
    rw [coarsening.commutes]
    exact keyEquation
  · intro member
    rcases Finset.mem_image.1 member with
      ⟨fineKey, fineKeyMember, keyEquation⟩
    rcases Finset.mem_image.1 fineKeyMember with
      ⟨site, siteMember, fineKeyEquation⟩
    apply Finset.mem_image.2
    refine ⟨site, siteMember, ?_⟩
    rw [← keyEquation, ← fineKeyEquation, coarsening.commutes]

/-- Coarser lawful reuse cannot increase the number of distinct cells or
compiled programs required by a finite workload. -/
theorem allocatedKeys_card_mono
    [DecidableEq Site]
    {fine : SharingScheme.{uSite, uFineKey} Site}
    {coarse : SharingScheme.{uSite, uCoarseKey} Site}
    (coarsening : Coarsening fine coarse) (sites : Finset Site) :
    (coarse.allocatedKeys sites).card ≤ (fine.allocatedKeys sites).card := by
  letI := fine.decEq
  letI := coarse.decEq
  rw [allocatedKeys_coarsening coarsening sites]
  exact @Finset.card_image_le fine.Key coarse.Key
    (fine.allocatedKeys sites) coarsening.mapKey coarse.decEq

/-- The compilation-count component induced by a sharing key. -/
def compilationCount (scheme : SharingScheme Site) (sites : Finset Site) : Nat :=
  (scheme.allocatedKeys sites).card

theorem compilationCount_mono
    [DecidableEq Site]
    {fine : SharingScheme.{uSite, uFineKey} Site}
    {coarse : SharingScheme.{uSite, uCoarseKey} Site}
    (coarsening : Coarsening fine coarse) (sites : Finset Site) :
    coarse.compilationCount sites ≤ fine.compilationCount sites :=
  allocatedKeys_card_mono coarsening sites

/-- Reuse is sound for an observation exactly when sites merged by its key
have equal declared meanings. -/
def SoundFor (scheme : SharingScheme Site)
    (meaning : Site -> Observation) : Prop :=
  ∀ ⦃left right⦄, scheme.Shares left right -> meaning left = meaning right

/-- Soundness descends from a coarse scheme to every refinement.  The reverse
is deliberately absent: merging more sites creates new proof obligations. -/
theorem Coarsening.sound_fine_of_sound_coarse
    {fine : SharingScheme.{uSite, uFineKey} Site}
    {coarse : SharingScheme.{uSite, uCoarseKey} Site}
    (coarsening : Coarsening fine coarse)
    {meaning : Site -> Observation} (sound : coarse.SoundFor meaning) :
    fine.SoundFor meaning := by
  intro left right shares
  exact sound (coarsening.map_shares shares)

/-- Revision, dialect, authority, or observation identity can be placed in
the key without changing the underlying sharing scheme. -/
def withIndex (scheme : SharingScheme Site) (Index : Type uIndex)
    [DecidableEq Index] (index : Site -> Index) : SharingScheme Site where
  Key := Index × scheme.Key
  decEq := by letI := scheme.decEq; infer_instance
  key := fun site => (index site, scheme.key site)

theorem withIndex_shares_same_index
    (scheme : SharingScheme Site) (Index : Type uIndex)
    [DecidableEq Index] (index : Site -> Index) {left right : Site}
    (shares : (scheme.withIndex Index index).Shares left right) :
    index left = index right :=
  congrArg Prod.fst shares

/-- A simple resource decomposition keeps compilation, lookup, and retention
visible as separate quantities. -/
structure ResourceBreakdown where
  compilation : Nat
  lookup : Nat
  retention : Nat
deriving DecidableEq, Repr

namespace ResourceBreakdown

def total (resources : ResourceBreakdown) : Nat :=
  resources.compilation + resources.lookup + resources.retention

end ResourceBreakdown

end SharingScheme

/-! ## Positive and negative canaries -/

namespace SharingCanary

open SharingScheme

def perDemand : SharingScheme (Fin 3) where
  Key := Fin 3
  decEq := inferInstance
  key := id

def perProgram : SharingScheme (Fin 3) where
  Key := Unit
  decEq := inferInstance
  key := fun _ => ()

def demandToProgram : perDemand.Coarsening perProgram where
  mapKey := fun _ => ()
  commutes := fun _ => rfl

def allDemands : Finset (Fin 3) := Finset.univ

theorem perDemand_compiles_three :
    perDemand.compilationCount allDemands = 3 := by
  decide

theorem perProgram_compiles_once :
    perProgram.compilationCount allDemands = 1 := by
  decide

theorem reuse_reduces_compilations :
    perProgram.compilationCount allDemands <
      perDemand.compilationCount allDemands := by
  decide

def exactSite : SharingScheme Bool where
  Key := Bool
  decEq := inferInstance
  key := id

def collapseSites : SharingScheme Bool where
  Key := Unit
  decEq := inferInstance
  key := fun _ => ()

def collapse : exactSite.Coarsening collapseSites where
  mapKey := fun _ => ()
  commutes := fun _ => rfl

theorem exactSite_sound_for_identity : exactSite.SoundFor id := by
  intro left right shares
  exact shares

/-- Negative canary: a coarser key may merge observably different demands.
Reuse therefore needs a semantic equality proof, not only a cache key. -/
theorem collapseSites_not_sound_for_identity :
    ¬ collapseSites.SoundFor id := by
  intro sound
  have impossible := sound (left := false) (right := true) rfl
  simp at impossible

def fineResources : SharingScheme.ResourceBreakdown where
  compilation := 3
  lookup := 0
  retention := 0

def coarseResources : SharingScheme.ResourceBreakdown where
  compilation := 1
  lookup := 0
  retention := 10

/-- Negative cost canary: reducing compilation count alone does not prove a
total-cost improvement when the coarser cache retains data longer. -/
theorem fewer_compilations_can_cost_more :
    coarseResources.compilation < fineResources.compilation ∧
      fineResources.total < coarseResources.total := by
  decide

end SharingCanary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed
