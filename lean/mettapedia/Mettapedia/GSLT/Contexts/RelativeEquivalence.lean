import Mettapedia.GSLT.Contexts.ContextTheory
import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity

/-!
# One interface: the relative equivalence of a class of contexts

At one interface, the labels from the interface to itself compose and act on
the terms of the interface.  That is the structure of contextual rules on the
theory at that interface, whose admissible classes of contexts each carry a
relative equivalence: the bisimilarity of the system in which a term steps
under a context to whatever the filled context reduces to.

The bisimilarity that a probe sees, for the probe whose observers are all the
labels from one interface to itself, is that relative equivalence for the
class of all contexts.  So probes extend relative equivalences from one
interface to many, and from contexts on one sort to contexts between sorts
and stages.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

universe u

namespace ContextTheory

variable (theory : ContextTheory.{u}) (interface : theory.Interface)

theorem apply_identity_equiv (term : theory.Term interface) :
    (theory.equations interface).r (theory.apply (theory.identity interface) term) term := by
  rw [theory.apply_identity]

theorem apply_compose_equiv (outer inner : theory.Label interface interface)
    (term : theory.Term interface) :
    (theory.equations interface).r (theory.apply (theory.compose outer inner) term)
      (theory.apply outer (theory.apply inner term)) := by
  rw [theory.apply_compose]

/-- The labels from an interface to itself, acting on its terms. -/
def contextualRules : ContextualRules.{u, 0} (theory.gslt interface) where
  Context := theory.Label interface interface
  identity := theory.identity interface
  compose := theory.compose
  plug := theory.apply
  plug_identity := theory.apply_identity_equiv interface
  plug_compose := theory.apply_compose_equiv interface
  plug_resp := fun context _ _ equivalent => theory.apply_resp context equivalent
  Rule := Unit
  fires := fun _ source target => theory.rewrites source target
  fires_resp_left := fun equivalent step => theory.rewrites_resp_left equivalent step
  fires_resp_right := fun step equivalent => theory.rewrites_resp_right step equivalent
  fires_step := fun step => step

/-- No base observation. -/
def noObservations : ContextualRules.Observations.{0} (theory.gslt interface) where
  Atom := Empty
  observes := fun atom _ => atom.elim
  observes_resp := fun atom _ _ _ => atom.elim

/-- The probe whose observers are the labels from one interface to itself. -/
def endoProbe : theory.Probe where
  Index := PUnit
  interface := fun _ => interface
  Observer := fun _ _ => theory.Label interface interface
  label := fun observer => observer

/-- **What the probe of one interface sees is the relative equivalence of the
class of all its contexts.** -/
theorem endoProbe_bisimilar_iff_relEquiv (left right : theory.Term interface) :
    (theory.endoProbe interface).Bisimilar (index := PUnit.unit) left right ↔
      (⊤ : AdmissibleClass (theory.contextualRules interface)).RelEquiv
        (theory.noObservations interface) left right := by
  constructor
  · rintro ⟨relation, ⟨forward, backward⟩, related⟩
    refine ⟨relation PUnit.unit, ⟨?_, ?_, ?_⟩, related⟩
    · intro first second pair label next step
      exact forward pair (target := PUnit.unit) label.1 step
    · intro first second pair label next step
      exact backward pair (target := PUnit.unit) label.1 step
    · intro first second _ atom
      exact atom.1.elim
  · rintro ⟨relation, ⟨forward, backward, -⟩, related⟩
    refine ⟨fun _ => relation, ⟨?_, ?_⟩, related⟩
    · intro source first second pair target observer next step
      exact forward pair
        ⟨observer, AdmissibleClass.top_admissible (rules := theory.contextualRules interface)
          observer⟩ step
    · intro source first second pair target observer next step
      exact backward pair
        ⟨observer, AdmissibleClass.top_admissible (rules := theory.contextualRules interface)
          observer⟩ step

end ContextTheory

end Mettapedia.GSLT
