import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.Languages.MeTTa.MeTTaInteraction

/-!
# MeTTa-shaped bind over authenticated interaction events

The proof-relevant interaction presentation supplies semantic authority and
occurrence identity.  This module gives that theory an ordinary MeTTa-facing
elimination form: normalize a subject through authenticated events, match a
pattern against the resulting value, and instantiate a continuation body.

`BangArticle` is the identity continuation and is therefore equivalent to
normalization.  `InspectArticle` exposes the enabled one-step events when
reflection on execution is wanted.  Neither construct introduces another
step relation.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaInteractionBind

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaInteraction
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uRevision uName uCost

variable {Revision : Type uRevision} {Name : Type uName} {Cost : Type uCost}
  [DecidableEq Revision] [DecidableEq Name] [DecidableEq Cost]

/-- One occurrence of matching a normal value against a `let` pattern,
together with the exact instantiated continuation result. -/
structure LetContinuation (model : Model) (pattern body value result : Pattern) where
  bindings : Bindings
  occurrence : Nat
  occurrence_exists :
    occurrence < Multiset.count bindings (model.matchAtoms pattern value)
  instantiates : applyBindings bindings body = result

/-- The semantic article behind ordinary MeTTa `let`: authenticated
normalization followed by one occurrence of pattern binding and
substitution. -/
def LetArticle (model : Model) (world : World Revision Name Cost)
    (revision : Revision) (pattern subject body result : Pattern) : Type _ :=
  Bind (theory := siteGSLT model world revision)
    (presentation model world revision)
    (LetContinuation model pattern body) subject result

/-- The semantic article behind ordinary execution.  It is normalization
with the identity continuation, not a distinct evaluator. -/
abbrev BangArticle (model : Model) (world : World Revision Name Cost)
    (revision : Revision) (subject result : Pattern) : Type _ :=
  Run (theory := siteGSLT model world revision)
    (presentation model world revision) subject result

/-- Optional reflective observation of the occurrence-specific one-step
frontier. -/
abbrev InspectArticle (model : Model) (world : World Revision Name Cost)
    (revision : Revision) (subject : Pattern) : Type _ :=
  Inspect (theory := siteGSLT model world revision)
    (presentation model world revision) subject

/-- Execution contains exactly the same proof-relevant path as
normalization. -/
def bangEquivNormalizes (model : Model) (world : World Revision Name Cost)
    (revision : Revision) (subject result : Pattern) :
    BangArticle model world revision subject result ≃
      EventNormalizes (presentation model world revision) subject result :=
  runEquivNormalizes (theory := siteGSLT model world revision)
    (presentation model world revision) subject result

/-! ## Positive and negative canaries -/

namespace Canary

open Mettapedia.Languages.MeTTa.MeTTaInteraction.Canary

def valuePattern : Pattern := .fvar "value"
def wrappedBody : Pattern := .apply "wrapped" [.fvar "value"]
def wrappedB : Pattern := .apply "wrapped" [b]

theorem b_normal :
    (siteGSLT model authorityWorld false).IsNormalForm b := by
  rintro ⟨target, step⟩
  change SiteStep model authorityWorld false b target at step
  simp [SiteStep, authorityWorld, cheap, dear, model, structuralModel,
    a, b, matchPattern] at step

def cheapNormalization :
    EventNormalizes (presentation model authorityWorld false) a b where
  path := .cons cheapEvent
    (.nil (presentation := presentation model authorityWorld false) b)
  normal := b_normal

def dearNormalization :
    EventNormalizes (presentation model authorityWorld false) a b where
  path := .cons dearEvent
    (.nil (presentation := presentation model authorityWorld false) b)
  normal := b_normal

def wrapB : LetContinuation model valuePattern wrappedBody b wrappedB where
  bindings := [("value", b)]
  occurrence := 0
  occurrence_exists := by
    simp [model, structuralModel, valuePattern, matchPattern]
  instantiates := by
    simp [wrappedBody, wrappedB, applyBindings]

/-- Positive: normal MeTTa-shaped binding follows an authenticated event and
then substitutes the normal value into its continuation. -/
def wrappedArticle :
    LetArticle model authorityWorld false valuePattern a wrappedBody wrappedB :=
  ⟨b, cheapNormalization, wrapB⟩

/-- Positive: two occurrence-distinct events yield two execution articles
with the same endpoint. -/
def cheapBang : BangArticle model authorityWorld false a b :=
  ⟨b, cheapNormalization, ⟨rfl⟩⟩

def dearBang : BangArticle model authorityWorld false a b :=
  ⟨b, dearNormalization, ⟨rfl⟩⟩

def cheapInspect : InspectArticle model authorityWorld false a where
  site := cheap
  target := b
  evidence := cheapEvent

def dearInspect : InspectArticle model authorityWorld false a where
  site := dear
  target := b
  evidence := dearEvent

abbrev siteCostValuation :=
  additiveEventCost (presentation model authorityWorld false)
    (eventCost model authorityWorld false)

abbrev siteNameValuation :=
  chronological fun occurrence :
      Occurrence (presentation model authorityWorld false) =>
    occurrence.2.site.name

abbrev costAndNameValuation :=
  siteCostValuation.prod siteNameValuation

/-- Cost and provenance are independent coordinates over the same exact
normalization path. -/
theorem cheap_normalization_cost_and_provenance :
    Mettapedia.GSLT.Dynamics.InteractionEventValuation.EventPath.grade
      (presentation model authorityWorld false) costAndNameValuation
      cheapNormalization.path = some (1, ["cheap"]) := by
  rfl

theorem dear_normalization_cost_and_provenance :
    Mettapedia.GSLT.Dynamics.InteractionEventValuation.EventPath.grade
      (presentation model authorityWorld false) costAndNameValuation
      dearNormalization.path = some (2, ["dear"]) := by
  rfl

/-- Inspection retains distinctions erased by ordinary result observation. -/
theorem inspection_retains_parallel_costs :
    cheapInspect.target = dearInspect.target ∧
      (eventCost model authorityWorld false).cost cheapInspect.evidence = 1 ∧
      (eventCost model authorityWorld false).cost dearInspect.evidence = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Negative: a fixed continuation body cannot manufacture a differently
shaped result. -/
theorem let_cannot_forge_unwrapped_result :
    LetArticle model authorityWorld false valuePattern a wrappedBody c → False := by
  rintro ⟨value, _normalization, continuation⟩
  have impossible := continuation.instantiates
  simp [wrappedBody, c, applyBindings] at impossible

end Canary

end Mettapedia.Languages.MeTTa.MeTTaInteractionBind
