import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySupportedEndgame

/-!
# Inhabitation ledger for the rho Cost₁ chain

A conditional theorem over an empty hypothesis type compiles, reports green,
and constrains nothing.  The reference-executor object tower reached exactly
that state before it was noticed: every bundle in it was refuted at one
stroke by projecting the generator-invariance field onto the checked
counterexample.

This file keeps the distinction visible under the build.  Every entry is a
checked witness or a checked refutation; the open obligations of the live
chain appear only as the recorded hypothesis signatures of the assembly
definitions, so a rename or reshaping of an open obligation fails here
rather than silently.

Ledger, as of this file's last update:

* inhabited — `OrderedCIGSLT` (first witness: the rho theory);
* refuted for rho — every reference-executor law bundle
  (`CostReferenceOpenGeneratorInvariant`, `CostReferenceOpenSectionLaws`,
  `CostReferenceOneObjectLaws`);
* proved — the reflective-support crown: `rhoHereditaryReflectiveSupportPreserving`
  is a theorem (local static-node law by path-indexed substitution, whole-tree
  structural theorem, supported-executor context transport);
* open — the single hypothesis of `rhoHereditaryCostOneObjectLaws_ofProvider`:
  the per-colour semantic-cut provider
  (`RhoCanonicalStaticPairSemanticCutProviderInDomain`).  Generator tree
  alignability is reduced to it by
  `rhoCostOpenGeneratorTreeAlignable_of_provider`;
* proved from that same provider — the exact selected-executor compact Cost²
  obstruction.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostInhabitationLedger

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The ordered continued carrier is inhabited: rho is an object. -/
example : Nonempty OrderedCIGSLT := ⟨⟨rhoCIGSLT⟩⟩

/-- The reference-executor object bundle is refuted for rho, so nothing may
be built over it. -/
example : ¬ CIGSLT.CostReferenceOneObjectLaws rhoCIGSLT :=
  CostGeneratorInvariantCounterexample.not_rho_costReferenceOneObjectLaws

/-- The reference-executor section bundle is refuted for rho. -/
example : ¬ CostReferenceOpenSectionLaws rhoCIGSLT :=
  CostGeneratorInvariantCounterexample.not_rho_costReferenceOpenSectionLaws

/-- Signature guard: the live rho Cost₁ object assembly and its exact open
hypotheses.  If either obligation is discharged, replace the corresponding
guard with the witness. -/
example := @rhoHereditaryCostOneObjectLaws_of

/-- Signature guard: the normalizer-indexed rho domain object assembly. -/
example := @rhoHereditaryCostOneDomainObject_of

/-- Historical signature guard: the reduced two-local-law assembly.  The
second input now has a checked global producer in the support crown. -/
example := @rhoHereditaryCostOneObjectLaws_ofStaticLaw

/-- Signature guard: the reduction itself — the supported executor preserves
every caller-relative reflective support once the local static-node law
holds. -/
example := @rhoHereditaryReflectiveSupportPreserving_of

/-- Signature guard: the alignability reduction — generator tree alignability
from the per-colour semantic-cut provider alone. -/
example := @rhoCostOpenGeneratorTreeAlignable_of_provider

/-- Signature guard: the fully reduced assembly over the two node-local
semantic obligations. -/
example := @rhoHereditaryCostOneObjectLaws_ofSemanticLaws

/-- The reflective-support crown is closed: a checked witness, not a guard. -/
example : RhoHereditaryReflectiveSupportPreserving :=
  rhoHereditaryReflectiveSupportPreserving

/-- Signature guard: the final waist — the Cost₁ object from the per-colour
semantic-cut provider alone. -/
example := @rhoHereditaryCostOneObjectLaws_ofProvider

/-- The selected-executor Cost² boundary has the same sole provider input as
the Cost₁ object; no executor agreement hypothesis remains. -/
example :=
  @rhoHereditaryCostOneDomainObject_not_compactCostNormalizationCoherent_ofProvider

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostInhabitationLedger
