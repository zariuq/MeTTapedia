import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryMeaning
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryPresentation
import Mettapedia.CategoryTheory.InternalCategoryLocalDiagrams
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Retained weighted evidence and rejected endpoint behavior

Evidence retains both Boolean endpoints and its independent natural-number
weight. Composition adds weights and keeps the outer endpoints. Its admitted
endpoint diagrams and complete parser readings are computed independently.
An incorrect unit is equally well formed but cannot satisfy the endpoint
presentation. Equal endpoints do not recover an omitted evidence weight.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation
open Meaning

abbrev Base := Discrete Bool

def vertex : Base := ⟨true⟩

def base : Base ⥤ Type := Discrete.functor (fun object => if object then Bool else PUnit)

abbrev Evidence := Bool × Bool × Nat

def graph : Meaning.Graph (base.obj vertex) where
  edge := Evidence
  source := TypeCat.ofHom (fun evidence => evidence.1)
  target := TypeCat.ofHom (fun evidence => evidence.2.1)

def weighted : Meaning.Operations (base.obj vertex) where
  toGraph := graph
  unit := TypeCat.ofHom (fun state => (state, state, 0))
  composition := TypeCat.ofHom (fun pair =>
    ((graph.first pair).1, (graph.second pair).2.1,
      (graph.first pair).2.2 + (graph.second pair).2.2))

theorem weighted_endpoint_laws : EndpointLaws vertex base weighted where
  unitSource := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext state
    rfl
  unitTarget := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext state
    rfl
  compositionSource := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext pair
    rfl
  compositionTarget := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext pair
    rfl

theorem weighted_realized : Realization (endpointSignature vertex)
    (EquationExtension.extendAssignment (Meaning.assignment vertex base weighted)) :=
  (endpoint_realization_iff vertex base weighted).mpr weighted_endpoint_laws

theorem complete_composition_read : (Meaning.assignment vertex base weighted).evaluateArrow
    (RelativeClosedInternalCategory.composition vertex).code =
      some (⟨graph.composable, Evidence, weighted.composition⟩ : ArrowValue Type) := rfl

def incorrectUnit : Meaning.Operations (base.obj vertex) where
  toGraph := graph
  unit := TypeCat.ofHom (fun state => (!state, state, 0))
  composition := weighted.composition

theorem incorrect_unit_well_formed : Realization (RelativeClosedInternalCategory.signature vertex)
    (Meaning.assignment vertex base incorrectUnit) := Meaning.realization vertex base incorrectUnit

theorem incorrect_unit_rejected : ¬ EndpointLaws vertex base incorrectUnit := by
  intro laws
  have impossible := congrArg (fun arrow : base.obj vertex ⟶ base.obj vertex => arrow true) laws.unitSource
  change false = true at impossible
  cases impossible

theorem incorrect_unit_not_realized : ¬ Realization (endpointSignature vertex)
    (EquationExtension.extendAssignment (Meaning.assignment vertex base incorrectUnit)) := by
  intro admitted
  exact incorrect_unit_rejected ((endpoint_realization_iff vertex base incorrectUnit).mp admitted)

theorem equal_endpoints_distinct_evidence :
    graph.source (false, true, 3) = graph.source (false, true, 7) ∧
      graph.target (false, true, 3) = graph.target (false, true, 7) ∧
      ((false, true, 3) : Evidence) ≠ (false, true, 7) := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have impossible := congrArg (fun evidence : Evidence => evidence.2.2) same
  exact (by decide : (3 : Nat) ≠ 7) impossible

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.Controls
