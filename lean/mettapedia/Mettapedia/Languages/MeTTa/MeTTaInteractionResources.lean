import Mettapedia.Languages.MeTTa.MeTTaInteraction
import Mettapedia.GSLT.Causality.ResourceInteraction

/-!
# MeTTa site rewriting as interaction on a bag: sites are read, calls consumed

A site of a MeTTa world answers a call it matches. As a resource system, the
configuration holds the pending calls beside the catalogue of sites. A firing
consumes one call, reads one site, and adds the instantiated template as a new
call. The catalogue never changes: every site persists.

A site step from one term to another is exactly one firing from that call
beside the catalogue to the result beside the catalogue. Firings on different
calls are concurrent even when they read the same site, and commute; two
firings on one call are alternatives, and after either the other is disabled.
Rho's communication is the case where the receiver is consumed as well.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {Revision Name Cost : Type} [DecidableEq Revision] [DecidableEq Name] [DecidableEq Cost]

/-- Resources: pending calls and site declarations. -/
inductive SiteRes (Revision Name Cost : Type) where
  | call (term : Pattern)
  | site (declaration : SiteDecl Revision Name Cost)
  deriving DecidableEq

/-- A firing of one declaration: the call it answers and the bindings of its
match. -/
abbrev SiteFiring (model : Model) (revision : Revision) (declaration : SiteDecl Revision Name Cost) :
    Type :=
  {firing : Pattern × Bindings //
    declaration.revision = revision ∧ firing.2 ∈ model.matchAtoms declaration.pattern firing.1}

/-- Site rewriting as a resource system: the call is consumed, the site read. -/
def siteSystem (model : Model) (revision : Revision) : System (SiteRes Revision Name Cost) where
  Site := SiteDecl Revision Name Cost
  Instance := SiteFiring model revision
  consume := fun firing => {SiteRes.call firing.val.1}
  read := fun {declaration} _ => {SiteRes.site declaration}
  produce := fun {declaration} firing =>
    {SiteRes.call (applyBindings firing.val.2 declaration.template)}

/-- The catalogue of a world, as persistent resources. -/
def catalogue (world : World Revision Name Cost) : Multiset (SiteRes Revision Name Cost) :=
  world.sites.map SiteRes.site

/-- A call beside the catalogue. -/
def withCall (world : World Revision Name Cost) (term : Pattern) :
    Multiset (SiteRes Revision Name Cost) :=
  SiteRes.call term ::ₘ catalogue world

omit [DecidableEq Revision] [DecidableEq Name] [DecidableEq Cost] in
private theorem call_not_mem_catalogue (world : World Revision Name Cost) (term : Pattern) :
    SiteRes.call term ∉ catalogue world := by
  unfold catalogue
  simp

private theorem fire_withCall (model : Model) (revision : Revision)
    (world : World Revision Name Cost) {declaration : SiteDecl Revision Name Cost}
    (firing : SiteFiring model revision declaration) :
    (siteSystem model revision).fire (withCall world firing.val.1) firing =
      withCall world (applyBindings firing.val.2 declaration.template) := by
  unfold System.fire withCall
  change SiteRes.call firing.val.1 ::ₘ catalogue world - SiteRes.call firing.val.1 ::ₘ 0 +
      SiteRes.call (applyBindings firing.val.2 declaration.template) ::ₘ 0 = _
  have split : SiteRes.call firing.val.1 ::ₘ catalogue world =
      (SiteRes.call firing.val.1 ::ₘ 0) + catalogue world := by
    rw [Multiset.cons_add, zero_add]
  rw [split, add_tsub_cancel_left, add_comm, Multiset.cons_add, zero_add]

/-- **A site step is exactly one firing from the call beside the catalogue to
the result beside the catalogue.** -/
theorem siteStep_iff_firing (model : Model) (world : World Revision Name Cost)
    (revision : Revision) (source target : Pattern) :
    SiteStep model world revision source target ↔
      (siteSystem model revision).theory.Step (withCall world source) (withCall world target) := by
  constructor
  · rintro ⟨declaration, member, revisionMatches, bindings, bindingsMatch, instantiates⟩
    let firing : SiteFiring model revision declaration :=
      ⟨(source, bindings), revisionMatches, bindingsMatch⟩
    refine ⟨declaration, firing, ?_, ?_⟩
    · change SiteRes.call source ::ₘ 0 + SiteRes.site declaration ::ₘ 0 ≤ withCall world source
      unfold withCall
      rw [Multiset.cons_add, zero_add]
      exact Multiset.cons_le_cons _ (Multiset.singleton_le.mpr
        (Multiset.mem_map_of_mem _ member))
    · rw [fire_withCall model revision world firing, instantiates]
  · rintro ⟨declaration, firing, enabled, fired⟩
    obtain ⟨⟨called, bindings⟩, revisionMatches, bindingsMatch⟩ := firing
    change SiteRes.call called ::ₘ 0 + SiteRes.site declaration ::ₘ 0 ≤ withCall world source
      at enabled
    have calledMember : SiteRes.call called ∈ withCall world source :=
      Multiset.mem_of_le enabled (by simp)
    have siteMember : SiteRes.site declaration ∈ withCall world source :=
      Multiset.mem_of_le enabled (by simp)
    have sameCall : called = source := by
      rcases Multiset.mem_cons.mp calledMember with same | inCatalogue
      · exact SiteRes.call.inj same
      · exact absurd inCatalogue (call_not_mem_catalogue world called)
    subst sameCall
    have member : declaration ∈ world.sites := by
      rcases Multiset.mem_cons.mp siteMember with impossible | inCatalogue
      · cases impossible
      · unfold catalogue at inCatalogue
        obtain ⟨d, dMember, same⟩ := Multiset.mem_map.mp inCatalogue
        cases same
        exact dMember
    refine ⟨declaration, member, revisionMatches, bindings, bindingsMatch, ?_⟩
    have result : withCall world target =
        withCall world (applyBindings bindings declaration.template) :=
      fired.trans (fire_withCall model revision world
        (declaration := declaration) ⟨(called, bindings), revisionMatches, bindingsMatch⟩)
    unfold withCall at result
    exact (SiteRes.call.inj ((Multiset.cons_inj_left (catalogue world)).mp result)).symm

/-- **Sites persist.** Every firing leaves the catalogue in place. -/
theorem catalogue_persists (model : Model) (revision : Revision)
    (world : World Revision Name Cost) {declaration : SiteDecl Revision Name Cost}
    (firing : SiteFiring model revision declaration) (calls : Multiset (SiteRes Revision Name Cost))
    (enabled : (siteSystem model revision).Enables (calls + catalogue world) firing) :
    catalogue world ≤ (siteSystem model revision).fire (calls + catalogue world) firing := by
  unfold System.fire
  have consumed : (siteSystem model revision).consume firing ≤ calls := by
    change SiteRes.call firing.val.1 ::ₘ 0 ≤ calls
    apply Multiset.singleton_le.mpr
    have inBag : SiteRes.call firing.val.1 ∈ calls + catalogue world :=
      Multiset.mem_of_le enabled (by
        change SiteRes.call firing.val.1 ∈ SiteRes.call firing.val.1 ::ₘ 0 + _
        simp)
    rcases Multiset.mem_add.mp inBag with inCalls | inCatalogue
    · exact inCalls
    · exact absurd inCatalogue (call_not_mem_catalogue world _)
  rw [add_comm calls, add_tsub_assoc_of_le consumed]
  exact le_trans (Multiset.le_add_right _ _) (Multiset.le_add_right _ _)

omit [DecidableEq Revision] [DecidableEq Name] [DecidableEq Cost] in
/-- **Two calls answered by one site are concurrent**: they commute. -/
theorem calls_sharing_a_site_concurrent (model : Model) (revision : Revision)
    (world : World Revision Name Cost) {declaration : SiteDecl Revision Name Cost}
    (member : declaration ∈ world.sites) (first second : SiteFiring model revision declaration) :
    (siteSystem model revision).Concurrent
      (SiteRes.call first.val.1 ::ₘ SiteRes.call second.val.1 ::ₘ catalogue world) first second :=
  (siteSystem model revision).concurrent_of_shared_read _ first second
    {SiteRes.site declaration} le_rfl le_rfl (by
      change SiteRes.call first.val.1 ::ₘ 0 + SiteRes.call second.val.1 ::ₘ 0 +
          SiteRes.site declaration ::ₘ 0 ≤ _
      simp only [Multiset.cons_add, zero_add]
      exact Multiset.cons_le_cons _ (Multiset.cons_le_cons _
        (Multiset.singleton_le.mpr (Multiset.mem_map_of_mem _ member))))

/-- **Two firings on one call are alternatives**: when the call is pending once,
they are not concurrent, and after either the other is disabled. -/
theorem firings_on_one_call_conflict (model : Model) (revision : Revision)
    {first second : SiteDecl Revision Name Cost} (M : Multiset (SiteRes Revision Name Cost))
    (firingOne : SiteFiring model revision first) (firingTwo : SiteFiring model revision second)
    (sameCall : firingOne.val.1 = firingTwo.val.1)
    (once : M.count (SiteRes.call firingOne.val.1) ≤ 1)
    (notBack : applyBindings firingOne.val.2 first.template ≠ firingOne.val.1) :
    ¬ (siteSystem model revision).Concurrent M firingOne firingTwo ∧
      ¬ (siteSystem model revision).Enables ((siteSystem model revision).fire M firingOne)
        firingTwo := by
  have inOne : SiteRes.call firingOne.val.1 ∈ (siteSystem model revision).consume firingOne := by
    change _ ∈ SiteRes.call firingOne.val.1 ::ₘ 0
    simp
  have inTwo : SiteRes.call firingOne.val.1 ∈ (siteSystem model revision).consume firingTwo := by
    change _ ∈ SiteRes.call firingTwo.val.1 ::ₘ 0
    simp [sameCall]
  refine ⟨(siteSystem model revision).not_concurrent_of_shared_consumption M firingOne firingTwo
    _ inOne inTwo once, (siteSystem model revision).disabled_after M firingOne firingTwo _ inOne
    inTwo once ?_⟩
  change SiteRes.call firingOne.val.1 ∉ SiteRes.call (applyBindings firingOne.val.2 first.template) ::ₘ 0
  intro same
  rcases Multiset.mem_cons.mp same with same | impossible
  · exact notBack (SiteRes.call.inj same).symm
  · simp at impossible

#print axioms siteStep_iff_firing
#print axioms catalogue_persists
#print axioms calls_sharing_a_site_concurrent
#print axioms firings_on_one_call_conflict

end Mettapedia.Languages.MeTTa.MeTTaInteraction
