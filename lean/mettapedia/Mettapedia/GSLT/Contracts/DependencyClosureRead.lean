import Mettapedia.GSLT.Contracts.ReadWindowCuts
import Mathlib.Data.Finset.Union

/-!
# A closed dependency footprint at a coherent read cut

A finite footprint can grow as reads reveal providers. Closure is tested
on the edges observed at the accepted cut. Earlier edge samples can
participate when their checked read windows still contain that cut.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.DependencyClosureRead

open ReadWindowCuts

universe u v w z

variable {Site : Type u} [DecidableEq Site]

/-- The guard set has set semantics. The observations and the lists of
providers keep their order and multiplicity. -/
def expand (links : Site → List Site) (held : Finset Site) : Finset Site :=
  held ∪ held.biUnion (fun site => (links site).toFinset)

def Closed (links : Site → List Site) (held : Finset Site) : Prop :=
  ∀ site ∈ held, ∀ provider ∈ links site, provider ∈ held

theorem subset_expand (links : Site → List Site) (held : Finset Site) :
    held ⊆ expand links held := Finset.subset_union_left

theorem expand_eq_iff_closed (links : Site → List Site) (held : Finset Site) :
    expand links held = held ↔ Closed links held := by
  constructor
  · intro fixed site member provider linked
    rw [← fixed]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨site, member, List.mem_toFinset.mpr linked⟩)
  · intro closed
    apply Finset.Subset.antisymm _ (subset_expand links held)
    intro provider member
    rcases Finset.mem_union.mp member with included | discovered
    · exact included
    · obtain ⟨site, included, linked⟩ := Finset.mem_biUnion.mp discovered
      exact closed site included provider (List.mem_toFinset.mp linked)

/-- Reflexive transitive reachability allows callers and cyclic
dependency graphs to remain in the same closure. -/
def Reachable (links : Site → List Site) : Site → Site → Prop :=
  Relation.ReflTransGen (fun site provider => provider ∈ links site)

omit [DecidableEq Site] in
theorem Closed.covers {links : Site → List Site} {held : Finset Site}
    (closed : Closed links held) {root site : Site}
    (inside : root ∈ held) (along : Reachable links root site) : site ∈ held := by
  induction along with
  | refl => exact inside
  | tail _ edge reached => exact closed _ reached _ edge

omit [DecidableEq Site] in
/-- Within a finite provider universe, every round which discovers a new
site strictly decreases the number of sites still available to discover.
The edges can change between rounds. -/
theorem strict_growth (carrier : Finset Site) :
    WellFounded (fun (later earlier : {held : Finset Site // held ⊆ carrier}) =>
      earlier.val ⊂ later.val) := by
  apply Subrelation.wf _ (measure (fun held : {held : Finset Site // held ⊆ carrier} =>
    carrier.card - held.val.card)).wf
  intro later earlier growth
  have bigger := Finset.card_lt_card growth
  have within := Finset.card_le_card later.property
  change carrier.card - later.val.card < carrier.card - earlier.val.card
  omega

section StampedRead

variable {Payload : Type v} {Region : Type w} {Stamp : Type z} [PartialOrder Stamp] {steps : Nat}
  {view : Cut steps → Site → Payload} {support : Site → Set Region}
  {stamp : Cut steps → Region → Stamp}

def sampled (view : Cut steps → Site → Payload) (windows : Site → Window (Cut steps)) :
    Site → Payload :=
  fun site => view (windows site).sample site

omit [DecidableEq Site] in
theorem replays_in_footprint (disciplined : Discipline view support stamp)
    (held : Finset Site) (windows : Site → Window (Cut steps)) (cut : Cut steps)
    (same : ∀ site ∈ held,
      Set.EqOn (stamp (windows site).start) (stamp (windows site).finish) (support site))
    (overlap : ∀ site ∈ held, (windows site).Contains cut) :
    ∀ site ∈ held, sampled view windows site = view cut site := by
  intro site member
  exact (disciplined.stable_in_window site (windows site) (same site member) (overlap site member)).symm

/-- A successful closure check covers every actual provider of the root.
Stamps transport the discovered edges to the accepted cut, including
edges examined before a section had to reacquire some of its guards. -/
theorem closes_at_cut (disciplined : Discipline view support stamp) (providers : Payload → List Site)
    (held : Finset Site) (windows : Site → Window (Cut steps)) (cut : Cut steps)
    (same : ∀ site ∈ held,
      Set.EqOn (stamp (windows site).start) (stamp (windows site).finish) (support site))
    (overlap : ∀ site ∈ held, (windows site).Contains cut)
    (fixed : expand (providers ∘ sampled view windows) held = held)
    (root : Site) (inside : root ∈ held) :
    Closed (providers ∘ view cut) held ∧
      ∀ site, Reachable (providers ∘ view cut) root site →
        site ∈ held ∧ sampled view windows site = view cut site := by
  have replay := replays_in_footprint disciplined held windows cut same overlap
  have discovered := (expand_eq_iff_closed _ _).mp fixed
  have closed : Closed (providers ∘ view cut) held := by
    intro site member provider sees
    apply discovered site member provider
    simpa only [Function.comp_apply, replay site member] using sees
  exact ⟨closed, fun site along =>
    let member := closed.covers inside along
    ⟨member, replay site member⟩⟩

end StampedRead

end Mettapedia.GSLT.Contracts.DependencyClosureRead
