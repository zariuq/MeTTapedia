import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPolynomial
import Mettapedia.OSLF.Syntax.IndexedRuleFreeTransport
import Mettapedia.TypeTheory.IndexedPolynomialAdjunction

/-!
# Authored conditional firing trees with existing event generators

The intrinsic rule presentation supplies the constructor shapes, ordered
premise positions and binder-local child judgments. The general free-tree
transport applies to those exact authored data. Existing event evidence is
represented by typed leaves and is not confused with a generated firing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFreeGenerators

open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IndexedRuleFreeTransport
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.FreeBindingClone
open Mettapedia.TypeTheory
open CategoryTheory

universe u v w uCarrier

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- A rule derivation may end at an existing event generator, or at an
authored rule constructor with its exact ordered child derivations. -/
abbrev FreeWithEvents (A : BindingCloneAlgebra.Algebra.{u} S)
    (Seed : Judgment A → Type v) (judgment : Judgment A) : Type _ :=
  (rules R A).Free (fun _ j => Seed j) PUnit.unit judgment

/-- An existing event remains a leaf at its exact contextual judgment. -/
def existingEvent (A : BindingCloneAlgebra.Algebra.{u} S)
    {Seed : Judgment A → Type v} {judgment : Judgment A}
    (seed : Seed judgment) : FreeWithEvents R A Seed judgment :=
  Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A) seed

/-- An interpretation of authored binding syntax and existing events
transports the complete free firing tree through the declared rule map. -/
noncomputable def mapFreeWithEvents
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{u} S}
    {Seed : Judgment A → Type v}
    {TargetSeed : Judgment B → Type w}
    (h : Hom A B)
    (seedMap : ∀ judgment, Seed judgment → TargetSeed (mapJudgment h judgment))
    (judgment : Judgment A) :
    FreeWithEvents R A Seed judgment →
      FreeWithEvents R B TargetSeed (mapJudgment h judgment) :=
  mapFree (presentationMap R h).rules
    (fun _ judgment seed => seedMap judgment seed) PUnit.unit judgment

/-- The authored transport sends an existing event to the corresponding
target event, with no rule constructor inserted or deleted. -/
theorem mapFreeWithEvents_existing
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{u} S}
    {Seed : Judgment A → Type v}
    {TargetSeed : Judgment B → Type w}
    (h : Hom A B)
    (seedMap : ∀ judgment, Seed judgment → TargetSeed (mapJudgment h judgment))
    {judgment : Judgment A} (seed : Seed judgment) :
    mapFreeWithEvents R h seedMap judgment
        (existingEvent R A seed) =
      existingEvent R B (seedMap judgment seed) := by
  exact mapFree_pure (presentationMap R h).rules
    (fun _ judgment seed => seedMap judgment seed) seed

/-- An authored rule action and a meaning for each existing event interpret
every finite constructor tree. The target algebra uses the actual authored
rule polynomial, so its children are still addressed by the rule's ordered
binder-local premise positions. -/
noncomputable def foldWithEvents
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Seed : Judgment A → Type v}
    {Carrier : Judgment A → Type uCarrier}
    (event : ∀ judgment, Seed judgment → Carrier judgment)
    (action : (rules R A).Algebra (fun _ judgment => Carrier judgment))
    (judgment : Judgment A) :
    FreeWithEvents R A Seed judgment → Carrier judgment :=
  IndexedPolynomial.Free.fold (rules R A)
    (fun _ judgment seed => event judgment seed) action PUnit.unit judgment

/-- Existing firing evidence is interpreted by the supplied event map,
without invoking any authored rule action. -/
theorem foldWithEvents_existing
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Seed : Judgment A → Type v}
    {Carrier : Judgment A → Type uCarrier}
    (event : ∀ judgment, Seed judgment → Carrier judgment)
    (action : (rules R A).Algebra (fun _ judgment => Carrier judgment))
    {judgment : Judgment A} (seed : Seed judgment) :
    foldWithEvents R A event action judgment (existingEvent R A seed) =
      event judgment seed := rfl

/-- A lawful interpretation is determined on every authored firing tree
by its action on existing events and on each ordered rule constructor. -/
theorem foldWithEvents_unique
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Seed : Judgment A → Type v}
    {Carrier : Judgment A → Type uCarrier}
    (event : ∀ judgment, Seed judgment → Carrier judgment)
    (action : (rules R A).Algebra (fun _ judgment => Carrier judgment))
    (candidate : ∀ judgment, FreeWithEvents R A Seed judgment →
      Carrier judgment)
    (onEvent : ∀ judgment (seed : Seed judgment),
      candidate judgment (existingEvent R A seed) = event judgment seed)
    (onRule : ∀ judgment (shape : (rules R A).Shape PUnit.unit judgment)
      (children : ∀ position,
        FreeWithEvents R A Seed
          ((rules R A).next shape position)),
      candidate judgment
          (IndexedPolynomial.Free.node (rules R A) shape children) =
        action.act PUnit.unit judgment
          ⟨shape, fun position =>
            candidate ((rules R A).next shape position)
              (children position)⟩)
    (judgment : Judgment A) (tree : FreeWithEvents R A Seed judgment) :
    candidate judgment tree = foldWithEvents R A event action judgment tree := by
  exact IndexedPolynomial.Free.fold_unique (rules R A)
    (fun _ judgment seed => event judgment seed)
    action (fun _ judgment tree => candidate judgment tree)
    (fun _ judgment seed => onEvent judgment seed)
    (fun _ judgment shape children => onRule judgment shape children)
    PUnit.unit judgment tree

/-- For the actual authored conditional-rule polynomial at a fixed binding
model, freely adjoining firing trees is left adjoint to forgetting the rule
action. The unit inserts existing events; the counit folds authored rule
constructors into a target model. -/
noncomputable def freeEventsAdjunction
    (A : BindingCloneAlgebra.Algebra.{0} S) :
    IndexedPolynomial.FreeAdjunction.freeFunctor (rules R A) ⊣
      Endofunctor.Algebra.forget (rules R A).endofunctor :=
  IndexedPolynomial.FreeAdjunction.adjunction (rules R A)

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFreeGenerators
