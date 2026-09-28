import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFiniteContext
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalActedBaseChange

/-!
# Base change for rule-local acted firing trees

A binding-clone interpretation maps the selected local rule valuation and
every premise under its declared binders. An event-variable leaf retains its
original variable position and its contextual substitution arrow.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedBaseChange

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial
  (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedBaseChange
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree
open Mettapedia.OSLF.Binding.IndexedRuleFreeTransport

variable {S : Signature}
variable (R : List (LocalRule S))
variable {A B : BindingCloneAlgebra.Algebra.{0} S}

/-- Change the base of one event-variable use, retaining its original
generator and contextual substitution arrow. -/
noncomputable def pushHole
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    (judgment : Judgment A) (event : Holes A Seed judgment) :
    Holes B TargetSeed (mapJudgment h judgment) := by
  have same : pushState h (ofJudgment A judgment) =
      ofJudgment B (mapJudgment h judgment) := rfl
  exact Eq.mp
    (congrArg (fun st : State B judgment.2.1 =>
      Orbit B TargetSeed st) same)
    (pushOrbit h seedMap event)

/-- Every authored node keeps its selected rule address, and every event
leaf retains its origin and contextual substitution arrow. -/
noncomputable def pushTree
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    (judgment : Judgment A) :
    Tree R A Seed judgment →
      Tree R B TargetSeed (mapJudgment h judgment) :=
  mapFree (presentationMap R h).rules
    (fun _ judgment event => pushHole h seedMap judgment event)
    () judgment

theorem pushTree_pure
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    (judgment : Judgment A) (hole : Holes A Seed judgment) :
    pushTree R h seedMap judgment
        (IndexedPolynomial.Free.pure (rules R A) hole) =
      IndexedPolynomial.Free.pure (rules R B)
        (pushHole h seedMap judgment hole) :=
  mapFree_pure (presentationMap R h).rules
    (fun _ judgment event => pushHole h seedMap judgment event) hole

theorem pushTree_node
    {Seed : (sort : S.Srt) → State A sort → Type}
    {TargetSeed : (sort : S.Srt) → State B sort → Type}
    (h : FreeBindingClone.Hom A B)
    (seedMap : ∀ sort (state : State A sort),
      Seed sort state → TargetSeed sort (pushState h state))
    {judgment : Judgment A}
    (shape : Shape R A judgment)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      Tree R A Seed (childJudgment R A shape.1 position)) :
    pushTree R h seedMap judgment
        (IndexedPolynomial.Free.node (rules R A) shape children) =
      IndexedPolynomial.Free.node (rules R B)
        ((presentationMap R h).rules.onShape () judgment shape)
        (fun position =>
          ((presentationMap R h).rules.onNext () judgment shape
              position).symm ▸
            pushTree R h seedMap _
              (children (((presentationMap R h).rules.onPosition
                () judgment shape) position))) :=
  mapFree_node (presentationMap R h).rules _ shape children

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedBaseChange
