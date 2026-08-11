import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.Languages.MeTTa.MeTTaZero

/-!
# Revisioned proof-relevant interaction sites for MeTTa

This module models the semantic boundary exercised by the experimental
`metta-interact` language.  A fixed catalog contains revisioned pattern/
template sites.  Matching a site produces an occurrence-specific event;
erasing the event yields the ordinary rewrite step.  Learned data is a
separate writable fibre and cannot add a site merely by resembling one.

Costs decorate exact site occurrences.  Two events may have equal endpoints
and unequal costs, so endpoint-only cost maps are insufficient.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uRevision uName uCost

/-- One static authority declaration.  Pattern and template are ordinary
MeTTa terms; revision, name, and cost remain independently indexed data. -/
structure SiteDecl (Revision : Type uRevision) (Name : Type uName)
    (Cost : Type uCost) where
  revision : Revision
  name : Name
  pattern : Pattern
  template : Pattern
  cost : Cost
  deriving DecidableEq

/-- The writable learned fibre is deliberately separate from the authority
catalog. -/
structure World (Revision : Type uRevision) (Name : Type uName)
    (Cost : Type uCost) where
  sites : Multiset (SiteDecl Revision Name Cost)
  learned : Multiset Pattern

section General

variable {Revision : Type uRevision} {Name : Type uName} {Cost : Type uCost}

/-- The endpoint relation forgets occurrence identity but is defined
independently as existence of a matching catalog member. -/
def SiteStep (model : Model) (world : World Revision Name Cost)
    (revision : Revision) (source target : Pattern) : Prop :=
  ∃ declaration ∈ world.sites,
    declaration.revision = revision ∧
      ∃ bindings ∈ model.matchAtoms declaration.pattern source,
        applyBindings bindings declaration.template = target

/-- The GSLT at one cited authority revision. -/
def siteGSLT (model : Model) (world : World Revision Name Cost)
    (revision : Revision) : GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SiteStep model world revision
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

section Decidable

variable [DecidableEq Revision] [DecidableEq Name] [DecidableEq Cost]

/-- An exact site occurrence and substitution witnessing one endpoint step. -/
structure SiteEvent (model : Model) (world : World Revision Name Cost)
    (revision : Revision) (declaration : SiteDecl Revision Name Cost)
    (source target : Pattern) where
  revision_matches : declaration.revision = revision
  occurrence : Nat
  occurrence_exists : occurrence < Multiset.count declaration world.sites
  bindings : Bindings
  bindings_match : bindings ∈ model.matchAtoms declaration.pattern source
  instantiates : applyBindings bindings declaration.template = target

/-- Occurrence-aware interaction presentation of the independently defined
site-step relation. -/
def presentation (model : Model) (world : World Revision Name Cost)
    (revision : Revision) :
    InteractionPresentation (siteGSLT model world revision) where
  Site := SiteDecl Revision Name Cost
  Event := SiteEvent model world revision
  sound := by
    intro declaration source target event
    refine ⟨declaration, ?_, event.revision_matches,
      event.bindings, event.bindings_match, event.instantiates⟩
    exact Multiset.count_pos.mp
      (Nat.zero_lt_of_lt event.occurrence_exists)

/-- Every site step has an occurrence-specific event. -/
theorem presentation_complete (model : Model)
    (world : World Revision Name Cost) (revision : Revision) :
    (presentation model world revision).Complete := by
  intro source target step
  obtain ⟨declaration, member, revisionMatches,
    bindings, bindingsMatch, instantiates⟩ := step
  have positive : 0 < Multiset.count declaration world.sites :=
    Multiset.count_pos.mpr member
  exact ⟨⟨declaration,
    { revision_matches := revisionMatches
      occurrence := 0
      occurrence_exists := positive
      bindings := bindings
      bindings_match := bindingsMatch
      instantiates := instantiates }⟩⟩

/-- Declared cost is attached to the selected occurrence evidence. -/
def eventCost (model : Model) (world : World Revision Name Cost)
    (revision : Revision) :
    EventCost (presentation model world revision) Cost where
  cost := fun {site} {_source _target} _ => site.cost

end Decidable

/-- Updating learned data cannot change the authoritative endpoint relation. -/
@[simp] theorem siteStep_with_learned
    (model : Model) (world : World Revision Name Cost)
    (learned : Multiset Pattern) (revision : Revision)
    (source target : Pattern) :
    SiteStep model { world with learned := learned } revision source target ↔
      SiteStep model world revision source target :=
  Iff.rfl

/-- Consequently the GSLT step relation is invariant under arbitrary learning
in the unprivileged fibre. -/
@[simp] theorem siteGSLT_step_with_learned
    (model : Model) (world : World Revision Name Cost)
    (learned : Multiset Pattern) (revision : Revision)
    (source target : Pattern) :
    (siteGSLT model { world with learned := learned } revision).Step
        source target ↔
      (siteGSLT model world revision).Step source target :=
  Iff.rfl

end General

/-! ## Positive and negative canaries -/

namespace Canary

def a : Pattern := .apply "interaction-a" []
def b : Pattern := .apply "interaction-b" []
def c : Pattern := .apply "interaction-c" []

def cheap : SiteDecl Bool String Nat where
  revision := false
  name := "cheap"
  pattern := a
  template := b
  cost := 1

def dear : SiteDecl Bool String Nat where
  revision := false
  name := "dear"
  pattern := a
  template := b
  cost := 2

def authorityWorld : World Bool String Nat where
  sites := {cheap, dear}
  learned := {(.apply "site" [a, c])}

def model : Model := structuralModel

def cheapEvent : SiteEvent model authorityWorld false cheap a b where
  revision_matches := rfl
  occurrence := 0
  occurrence_exists := by
    simp [authorityWorld, cheap, dear]
  bindings := []
  bindings_match := by
    simp [model, structuralModel, cheap, a, matchPattern, matchArgs]
  instantiates := by
    simp [cheap, b, applyBindings]

def dearEvent : SiteEvent model authorityWorld false dear a b where
  revision_matches := rfl
  occurrence := 0
  occurrence_exists := by
    simp [authorityWorld, cheap, dear]
  bindings := []
  bindings_match := by
    simp [model, structuralModel, dear, a, matchPattern, matchArgs]
  instantiates := by
    simp [dear, b, applyBindings]

theorem both_events_erase_to_steps :
    (siteGSLT model authorityWorld false).Step a b ∧
      (siteGSLT model authorityWorld false).Step a b := by
  exact ⟨(presentation model authorityWorld false).sound cheapEvent,
    (presentation model authorityWorld false).sound dearEvent⟩

theorem equal_endpoints_do_not_determine_cost :
    ¬ (eventCost model authorityWorld false).FactorsThroughEndpoints := by
  apply
    (eventCost model authorityWorld false).not_factorsThroughEndpoints_of_parallel_costs
      (first := cheapEvent) (second := dearEvent)
  decide

/-- A learned atom that resembles a site does not authorize the forged edge. -/
theorem learned_site_shape_cannot_mint_step :
    ¬ (siteGSLT model authorityWorld false).Step a c := by
  change ¬ SiteStep model authorityWorld false a c
  simp [SiteStep, authorityWorld, cheap, dear, model, structuralModel,
    a, b, c, matchPattern, matchArgs, applyBindings]

/-- The positive catalog edge remains available. -/
theorem authored_site_authorizes_step :
    (siteGSLT model authorityWorld false).Step a b := by
  exact (presentation model authorityWorld false).sound cheapEvent

end Canary

end Mettapedia.Languages.MeTTa.MeTTaInteraction
