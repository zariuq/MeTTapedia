import Mettapedia.OSLF.Syntax.EventGraphNullaryPolynomial
import Mettapedia.OSLF.Syntax.PresheafEventGraphTransport

/-!
# Transporting retained rule constructors with their event graphs

The nullary polynomial of an event graph is compatible with context-base
precomposition and with an isomorphism of its state presheaf. Both comparisons
are equivalences on individual firing trees, not merely on the propositions
that their endpoint pairs are related.

This is the graph-generator component of an operational interpretation. A
premise-bearing polynomial additionally needs an action on its recursive
positions and their possibly extended binder contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EventGraphPolynomialTransport

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport

universe u u' v v' w

variable {C : Type u} [Category.{v} C]
variable {B : Type u'} [Category.{v'} B]
variable {V W : C ⥤ Type w}

/-- Base precomposition leaves the actual event fibre unchanged at each
stage, with only its displayed context index changed. -/
def reindexFibreEquiv (H : B ⥤ C) (G : Graph V) (X : B)
    (pair : V.obj (H.obj X) × V.obj (H.obj X)) :
    EndpointFiber (reindex H G) X pair ≃
      EndpointFiber G (H.obj X) pair :=
  Equiv.refl _

/-- The corresponding constructor-tree fibres agree under base change.
The comparison passes through the full event fibre, retaining occurrence
identity rather than its image in an endpoint predicate. -/
def reindexTreeEquiv (H : B ⥤ C) (G : Graph V) (X : B)
    (pair : V.obj (H.obj X) × V.obj (H.obj X)) :
    (rules (reindex H G)).Fix () ⟨X, pair⟩ ≃
      (rules G).Fix () ⟨H.obj X, pair⟩ :=
  (eventFiberEquiv (reindex H G) X pair).symm.trans
    ((reindexFibreEquiv H G X pair).trans
      (eventFiberEquiv G (H.obj X) pair))

/-- The base-change comparison maps the one-node constructor for an event
to the one-node constructor for that same event. -/
theorem reindexTreeEquiv_event (H : B ⥤ C) (G : Graph V) (X : B)
    (pair : V.obj (H.obj X) × V.obj (H.obj X))
    (event : EndpointFiber (reindex H G) X pair) :
    reindexTreeEquiv H G X pair (eventTree (reindex H G) event) =
      eventTree G ((reindexFibreEquiv H G X pair) event) := rfl

/-- Transport along a state-presheaf isomorphism changes both displayed
endpoints but keeps exactly the same event occurrence. -/
def changeVertexFibreEquiv (i : V ≅ W) (G : Graph V)
    (X : C) (pair : V.obj X × V.obj X) :
    EndpointFiber G X pair ≃
      EndpointFiber (changeVertex i G) X
        (i.hom.app X pair.1, i.hom.app X pair.2) where
  toFun event :=
    ⟨event.1,
      congrArg (i.hom.app X) event.2.1,
      congrArg (i.hom.app X) event.2.2⟩
  invFun event :=
    ⟨event.1,
      componentInjective i X event.2.1,
      componentInjective i X event.2.2⟩
  left_inv := by
    intro event
    apply Subtype.ext
    rfl
  right_inv := by
    intro event
    apply Subtype.ext
    rfl

/-- State-isomorphism transport preserves and reflects every individual
nullary operational derivation. -/
def changeVertexTreeEquiv (i : V ≅ W) (G : Graph V)
    (X : C) (pair : V.obj X × V.obj X) :
    (rules G).Fix () ⟨X, pair⟩ ≃
      (rules (changeVertex i G)).Fix ()
        ⟨X, (i.hom.app X pair.1, i.hom.app X pair.2)⟩ :=
  (eventFiberEquiv G X pair).symm.trans
    ((changeVertexFibreEquiv i G X pair).trans
      (eventFiberEquiv (changeVertex i G) X
        (i.hom.app X pair.1, i.hom.app X pair.2)))

/-- The state-isomorphism comparison likewise sends an event constructor
to the constructor for the identical event at transported endpoints. -/
theorem changeVertexTreeEquiv_event (i : V ≅ W) (G : Graph V)
    (X : C) (pair : V.obj X × V.obj X)
    (event : EndpointFiber G X pair) :
    changeVertexTreeEquiv i G X pair (eventTree G event) =
      eventTree (changeVertex i G)
        ((changeVertexFibreEquiv i G X pair) event) := rfl

#print axioms reindexTreeEquiv_event
#print axioms changeVertexFibreEquiv
#print axioms changeVertexTreeEquiv_event

end Mettapedia.OSLF.Binding.EventGraphPolynomialTransport

namespace Mettapedia.OSLF.Binding.EventGraphPolynomialTransport.RhoExample

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents
open Mettapedia.OSLF.Binding.RhoSourceEquationLexClassification
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport.RhoExample

/-- Every source rho firing tree over a raw clone context corresponds to
exactly one tree over the generated finite-limit program object, at the
transported equation-class endpoints. -/
noncomputable def sourceGeneratedTreeEquiv
    (X : (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject
      (termClone sig))ᵒᵖ)
    (pair : states.obj (rawCloneIndex.obj X) ×
      states.obj (rawCloneIndex.obj X)) :
    (rules sourceEvents).Fix () ⟨rawCloneIndex.obj X, pair⟩ ≃
      (rules generatedEventGraph).Fix ()
        ⟨X, (generatedProgramAsOperationalStatesIso.hom.app X pair.1,
          generatedProgramAsOperationalStatesIso.hom.app X pair.2)⟩ :=
  (reindexTreeEquiv rawCloneIndex sourceEvents X pair).symm.trans
    (changeVertexTreeEquiv generatedProgramAsOperationalStatesIso
      (reindex rawCloneIndex sourceEvents) X pair)

/-- The rho comparison sends the tree for a particular authored firing to
the tree for that very firing in the generated program interpretation. -/
theorem sourceGeneratedTreeEquiv_event
    (X : (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject
      (termClone sig))ᵒᵖ)
    (pair : states.obj (rawCloneIndex.obj X) ×
      states.obj (rawCloneIndex.obj X))
    (event : EndpointFiber sourceEvents (rawCloneIndex.obj X) pair) :
    sourceGeneratedTreeEquiv X pair (eventTree sourceEvents event) =
      eventTree generatedEventGraph
        ((changeVertexFibreEquiv generatedProgramAsOperationalStatesIso
          (reindex rawCloneIndex sourceEvents) X pair)
          ((reindexFibreEquiv rawCloneIndex sourceEvents X pair).symm event)) := by
  rfl

/-- This generated interpretation preserves the distinction between any
two source firing trees at the same equation-class endpoints. -/
theorem sourceGeneratedTreeEquiv_injective
    (X : (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject
      (termClone sig))ᵒᵖ)
    (pair : states.obj (rawCloneIndex.obj X) ×
      states.obj (rawCloneIndex.obj X))
    (first second :
      (rules sourceEvents).Fix () ⟨rawCloneIndex.obj X, pair⟩)
    (distinct : first ≠ second) :
    sourceGeneratedTreeEquiv X pair first ≠
      sourceGeneratedTreeEquiv X pair second := by
  intro equal
  exact distinct ((sourceGeneratedTreeEquiv X pair).injective equal)

#print axioms sourceGeneratedTreeEquiv
#print axioms sourceGeneratedTreeEquiv_event
#print axioms sourceGeneratedTreeEquiv_injective

end Mettapedia.OSLF.Binding.EventGraphPolynomialTransport.RhoExample
