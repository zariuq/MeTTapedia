import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mettapedia.Logic.HOL.Probabilistic.ModelSpace

/-!
# Concrete Indexed Model Spaces for Probabilistic HOL

This module provides concrete constructors for the abstract indexed-model-space
interface used by semantic `ProbHOL`.

The constructors come in three flavors:

- `ofFamily` for arbitrary measurable index spaces with explicit measurability,
- `ofCountableFamily` for countable index spaces with singleton measurability,
- `ofFiniteFamily` for finite index spaces.

This keeps the infinitary-first semantic layer easy to instantiate while staying
strictly separate from the dynamic belief-process layer motivated by Garrabrant,
Benson-Tilsen, Critch, Soares, and Taylor, *Logical Induction*,
arXiv:1609.03543v5 (2020).
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WorldModel
open Mettapedia.Logic.HOL.Probabilistic.ModelSpace

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Build a probabilistic HOL model space from an arbitrary measurable family of
pointed Henkin models and explicit sentence-event measurability proofs. -/
def ofFamily
    (Idx : Type x) [mIdx : MeasurableSpace Idx]
    (model : Idx → HenkinModel.{u, v, w} Base Const)
    (hmeas : ∀ φ : ClosedFormula Const, MeasurableSet {i | holSatisfies (model i) φ}) :
    ModelSpace Base Const where
  Idx := Idx
  instMeasurableSpace := mIdx
  model := model
  measurable_sentence_event := hmeas

/-- Build a probabilistic HOL model space from a countable index family. Every
sentence event is measurable because every subset of a countable measurable
singleton class is measurable. -/
def ofCountableFamily
    (Idx : Type x) [mIdx : MeasurableSpace Idx] [MeasurableSingletonClass Idx] [Countable Idx]
    (model : Idx → HenkinModel.{u, v, w} Base Const) :
    ModelSpace Base Const where
  Idx := Idx
  instMeasurableSpace := mIdx
  model := model
  measurable_sentence_event := by
    intro φ
    exact Set.Countable.measurableSet (Set.to_countable _)

/-- Build a probabilistic HOL model space from a finite index family. -/
def ofFiniteFamily
    (Idx : Type x) [mIdx : MeasurableSpace Idx] [MeasurableSingletonClass Idx] [Finite Idx]
    (model : Idx → HenkinModel.{u, v, w} Base Const) :
    ModelSpace Base Const where
  Idx := Idx
  instMeasurableSpace := mIdx
  model := model
  measurable_sentence_event := by
    intro φ
    exact Set.Finite.measurableSet (Set.toFinite _)

end Mettapedia.Logic.HOL.Probabilistic
