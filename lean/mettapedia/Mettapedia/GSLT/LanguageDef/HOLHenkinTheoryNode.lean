import Mettapedia.GSLT.LanguageDef.InstitutionConsequence
import Mettapedia.Logic.HOL.HenkinInstitutionDerivation

/-!
# The property-explicit Henkin simple-type-theory node of the theory graph

This module places one precisely qualified simple type theory in the common
logical atlas.  Its native institution has a fixed alphabet of base types,
varying typed constants, extensional Henkin models, and the extensional
derivation calculus.  The selected theory adds excluded middle, schematic
Hilbert choice, and Dedekind infinity at one named base type.

The node is intentionally logical-only.  A GSLT becomes its operational model
only after equation classes of machine states have been mapped to qualified
Henkin models and the satisfaction square has been proved.  This avoids a
dummy transition system masquerading as semantics for a mathematical theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HOLHenkinTheoryNode

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.Logic
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.HenkinInstitution
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InstitutionConsequence

universe u

/-- Extend a typed constant signature by the parameter constants used by the
classical Henkin construction. -/
def parameterSignature {Base : Type u} (Const : Ty Base → Type u) :
    Signature Base :=
  ⟨WithParams Const⟩

/-- The model-generated consequence structure for fixed-base extensional
Henkin simple type theory. -/
abbrev extensionalHenkinConsequence (Base : Type u) :=
  consequenceProjection (institution Base)

/-- The property-explicit classical extensional STT theory.  The name records
the selected components rather than using an ambiguous bare `HOL`. -/
def classicalExtensionalChoiceInfinityTheory {Base : Type u}
    (Const : Ty Base → Type u) (infiniteBase : Base) :
    PiInstitution.TheoryObject (extensionalHenkinConsequence Base) :=
  PiInstitution.generatedTheory (extensionalHenkinConsequence Base)
    (parameterSignature Const)
    (StandardAxiomProperties.classicalChoiceInfinityTheory infiniteBase)

/-- An extensional Henkin model carrying the independently selected choice
and infinity witnesses qualifies the named theory. -/
structure QualifiedModel {Base : Type u} (Const : Ty Base → Type u)
    (infiniteBase : Base) where
  native : Model (parameterSignature Const)
  properties : native.henkin.ExtensionalChoiceInfinity infiniteBase

/-- Every theorem of the generated theory holds in every qualified model. -/
theorem qualifiedModel_models_theory {Base : Type u}
    {Const : Ty Base → Type u} {infiniteBase : Base}
    (qualified : QualifiedModel Const infiniteBase)
    {formula : ClosedFormula (WithParams Const)}
    (theoremhood : formula ∈
      (classicalExtensionalChoiceInfinityTheory Const infiniteBase).theory.1) :
    qualified.native.henkin.models formula := by
  exact theoremhood
    (CategoryTheory.Discrete.mk qualified.native) <| by
      intro premise membership
      change qualified.native.henkin.models premise
      exact StandardAxiomProperties.models_classicalChoiceInfinityTheory
        qualified.native.henkin infiniteBase qualified.properties
        premise membership

/-- Proofs in the extensional calculus enter the semantic closure selected by
the theory-graph node. -/
theorem provable_mem_classicalExtensionalChoiceInfinityTheory
    {Base : Type u} {Const : Ty Base → Type u} {infiniteBase : Base}
    {formula : ClosedFormula (WithParams Const)}
    (derivation : ClosedTheorySet.Provable
      (StandardAxiomProperties.classicalChoiceInfinityTheory infiniteBase)
      formula) :
    formula ∈
      (classicalExtensionalChoiceInfinityTheory Const infiniteBase).theory.1 :=
  provable_entails derivation

/-- The mathematical theory as a closed theory of its consequence
institution: a node of the theory graph, with no fabricated operational
dynamics.  A GSLT becomes an operational model of it only after a
satisfaction square has been proved. -/
def classicalExtensionalChoiceInfinityNode {Base : Type u}
    (Const : Ty Base → Type u) (infiniteBase : Base) :
    PiInstitution.TheoryObject (extensionalHenkinConsequence Base) :=
  classicalExtensionalChoiceInfinityTheory Const infiniteBase

#print axioms qualifiedModel_models_theory
#print axioms provable_mem_classicalExtensionalChoiceInfinityTheory
#print axioms classicalExtensionalChoiceInfinityNode

end Mettapedia.GSLT.LanguageDef.HOLHenkinTheoryNode
