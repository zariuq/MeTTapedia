import Mettapedia.Languages.TuringMachine.Universal
import Mettapedia.GSLT.LanguageDef.AuthoredComputation
import Mettapedia.Logic.HostingStyles.Universality

/-!
# Two existing universal hosts, as instances

Two results already in the tree have the shape of a universal host.  This
module states each as an instance, with the level at which it holds.

## The universal Turing-machine theory

`Mettapedia.Languages.TuringMachine.universalTheory` is one language
definition that runs every machine.  The existing result
(`intoUniversal`, `bisimilar_withTable_iff`) is stated for theories given by
their terms alone (`Mettapedia.GSLT.GSLT` with its morphisms
`GSLT.Morphism`): from every machine there is a map of terms into the
universal theory that preserves bisimilarity and reflects it.  That is
hosting as the probe of reduction sees it (`HostsEveryUpToBisimilarity`,
`universalTheory_hostsEvery_machine`).  It is not yet a statement about maps
of theories presented through their contexts: the map on contexts and the
three hosting laws of `ContextMap.Hosting` have been proved for the one-sort
presentation of a machine (`Mettapedia.Languages.TuringMachine.hostingMorphism`),
not for the map into the universal theory.

## The checker of an authored calculus

For every authored calculus `K` the specified checker accepts a certificate
for a goal exactly when the goal is derivable (`AuthoredCalculus.accepts_iff`).
At the level of provability this is a hosting and exhausting map
(`authoredCalculus_hostsExhaustively`): acceptance by the checker hosts
derivability and adds nothing.  The statement is about which goals are
accepted, so the level is provability; it does not say that two different
derivations are kept apart by their certificates.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT

universe v

/-! ## Semantics with the same truths -/

section SameTruths

variable {J : Type} {Point : Type v} {first second : Point → J → Prop}

/-- Two semantics that agree at every point have the same theory: the
identity on judgments is a map between them. -/
def sameTruthsMap (same : ∀ point j, first point j ↔ second point j) :
    ContextMap (shallowTheory first) (shallowTheory second) where
  interface := fun j => j
  term := fun valid => ⟨fun point => (same point _).mp (valid.down point)⟩
  context := fun context => ⟨by
    obtain ⟨support, follows⟩ := context.down
    exact ⟨support, fun point assumed => (same point _).mp
      (follows point fun index member => (same point _).mpr (assumed index member))⟩⟩
  term_resp := fun _ => trivial
  equivariant := fun _ _ => trivial

theorem sameTruthsMap_hosting (same : ∀ point j, first point j ↔ second point j) :
    (sameTruthsMap same).Hosting := by
  rw [ContextMap.hosting_iff]
  exact ⟨fun _ => trivial, fun _ _ _ step => step.elim, fun _ _ _ step => step.elim⟩

theorem sameTruthsMap_exhausting (same : ∀ point j, first point j ↔ second point j) :
    (sameTruthsMap same).Exhausting := by
  intro arity assumptions conclusion observer
  refine ⟨⟨?_⟩, fun _ => trivial⟩
  obtain ⟨support, follows⟩ := observer.down
  exact ⟨support, fun point assumed => (same point _).mpr
    (follows point fun index member => (same point _).mp (assumed index member))⟩

end SameTruths

/-! ## The checker of an authored calculus -/

open Mettapedia.GSLT.LanguageDef.Authored in
/-- **Acceptance by the specified checker hosts derivability and adds
nothing**, at the level of provability, for every authored calculus. -/
theorem authoredCalculus_hostsExhaustively (K : AuthoredCalculus) :
    HostsExhaustively (shallowTheory fun (_ : PUnit.{1}) goal => K.Accepts goal)
      (shallowTheory fun (_ : PUnit.{1}) goal => K.Derivable goal) :=
  ⟨sameTruthsMap fun _ goal => (K.accepts_iff goal).symm,
    sameTruthsMap_hosting _, sameTruthsMap_exhausting _⟩

/-! ## The universal Turing-machine theory -/

/-- A theory given by its terms hosts every theory of a class, as the probe
of reduction sees it: each member has a map of terms into it that preserves
bisimilarity and reflects it. -/
def HostsEveryUpToBisimilarity (host : GSLT.{0}) (sources : GSLT.{0} → Prop) : Prop :=
  ∀ source, sources source → ∃ map : GSLT.Morphism source host,
    ∀ first second : source.Term,
      host.Bisimilar (map.toFun first) (map.toFun second) → source.Bisimilar first second

open Mettapedia.Languages.TuringMachine Mettapedia.OSLF.Framework.TypeSynthesis in
/-- **The universal Turing-machine theory hosts every machine**, as the probe
of reduction sees it. -/
theorem universalTheory_hostsEvery_machine :
    HostsEveryUpToBisimilarity (langGSLT universalTheory)
      (fun source => ∃ machine : Machine, source = configurationGSLT machine) := by
  rintro source ⟨machine, rfl⟩
  exact ⟨intoUniversal machine, fun first second bisimilar =>
    (bisimilar_withTable_iff machine first second).mpr bisimilar⟩

#print axioms authoredCalculus_hostsExhaustively
#print axioms universalTheory_hostsEvery_machine

end Mettapedia.Logic.HostingStyles
