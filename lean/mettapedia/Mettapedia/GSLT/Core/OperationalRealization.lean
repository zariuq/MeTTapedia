import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Path-valued operational realizations

An ordinary `OperationalTranslation` maps every source step to exactly one
target step.  That is the correct strict notion for language embeddings, but
it is too rigid for compilation: fusion may erase an administrative step,
while lowering may expand one source step into several target steps.

An `OperationalRealization` therefore maps each source step to a finite,
proof-relevant target path.  It is the free-path extension forced by the
existing execution categories.  Complete source paths map compositionally,
strict operational translations embed, and realizations compose.  The direct
term map remains separate from the retained path justification.
-/

namespace Mettapedia.GSLT.IndexedOperational

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite

universe uTerm uSourceTerm uMiddleTerm uTargetTerm

/-- A direct term realization whose source steps are simulated by finite
target paths.  Zero-length target paths express fusion or erasure; paths of
length greater than one express lowering or expansion. -/
structure OperationalRealization
    (source : GSLT.{uSourceTerm}) (target : GSLT.{uTargetTerm}) where
  mapTerm : source.Term → target.Term
  mapEquiv : ∀ {left right}, source.Equiv left right →
    target.Equiv (mapTerm left) (mapTerm right)
  mapStep : ∀ {sourceTerm targetTerm}, source.Step sourceTerm targetTerm →
    ExecutionPath target (mapTerm sourceTerm) (mapTerm targetTerm)

namespace OperationalRealization

/-- Map a complete source execution by expanding each retained source step
to its admitted target path. -/
def mapRoute {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (realization : OperationalRealization source target) :
    {first last : source.Term} → ExecutionPath source first last →
      ExecutionPath target (realization.mapTerm first)
        (realization.mapTerm last)
  | _, _, .refl object => .refl (realization.mapTerm object)
  | _, _, .cons step rest =>
      (realization.mapStep step.down).append (realization.mapRoute rest)

@[simp] theorem mapRoute_refl
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (realization : OperationalRealization source target)
    (object : source.Term) :
    realization.mapRoute (.refl object) = .refl (realization.mapTerm object) :=
  rfl

@[simp] theorem mapRoute_append
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (realization : OperationalRealization source target)
    {first middle last : source.Term}
    (earlier : ExecutionPath source first middle)
    (later : ExecutionPath source middle last) :
    realization.mapRoute (earlier.append later) =
      (realization.mapRoute earlier).append (realization.mapRoute later) := by
  induction earlier with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      change
        (realization.mapStep step.down).append
            (realization.mapRoute (rest.append later)) =
          ((realization.mapStep step.down).append
            (realization.mapRoute rest)).append
              (realization.mapRoute later)
      rw [inductionHypothesis]
      exact (Route.append_assoc _ _ _).symm

/-- Identity realizes every primitive step by its singleton path. -/
def id (system : GSLT.{uTerm}) : OperationalRealization system system where
  mapTerm := _root_.id
  mapEquiv := fun equivalent => equivalent
  mapStep := fun step => .cons ⟨step⟩ (.refl _)

@[simp] theorem mapRoute_id
    {system : GSLT.{uTerm}} {first last : system.Term}
    (route : ExecutionPath system first last) :
    (id system).mapRoute route = route := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      rcases step with ⟨sourceStep⟩
      simp only [mapRoute]
      rw [inductionHypothesis]
      rfl

/-- Path-valued realizations compose in execution order. -/
def comp {first : GSLT.{uSourceTerm}} {middle : GSLT.{uMiddleTerm}}
    {last : GSLT.{uTargetTerm}}
    (earlier : OperationalRealization first middle)
    (later : OperationalRealization middle last) :
    OperationalRealization first last where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  mapStep := fun step => later.mapRoute (earlier.mapStep step)

@[simp] theorem comp_mapTerm
    {first : GSLT.{uSourceTerm}} {middle : GSLT.{uMiddleTerm}}
    {last : GSLT.{uTargetTerm}}
    (earlier : OperationalRealization first middle)
    (later : OperationalRealization middle last) :
    (earlier.comp later).mapTerm = later.mapTerm ∘ earlier.mapTerm :=
  rfl

@[simp] theorem mapRoute_comp
    {first : GSLT.{uSourceTerm}} {middle : GSLT.{uMiddleTerm}}
    {last : GSLT.{uTargetTerm}}
    (earlier : OperationalRealization first middle)
    (later : OperationalRealization middle last)
    {source target : first.Term}
    (route : ExecutionPath first source target) :
    (earlier.comp later).mapRoute route =
      later.mapRoute (earlier.mapRoute route) := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp only [mapRoute]
      change
        (later.mapRoute (earlier.mapStep step.down)).append
            ((earlier.comp later).mapRoute rest) =
          later.mapRoute
            ((earlier.mapStep step.down).append (earlier.mapRoute rest))
      rw [later.mapRoute_append, inductionHypothesis]
      rfl

/-- A strict one-step operational translation is a path-valued realization
using singleton target paths. -/
def ofTranslation {source : GSLT.{uSourceTerm}}
    {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target) :
    OperationalRealization source target where
  mapTerm := translation.mapTerm
  mapEquiv := translation.mapEquiv
  mapStep := fun step => .cons ⟨translation.mapStep step⟩ (.refl _)

@[simp] theorem mapRoute_ofTranslation
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    {first last : source.Term} (route : ExecutionPath source first last) :
    (ofTranslation translation).mapRoute route = translation.mapRoute route := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      rcases step with ⟨sourceStep⟩
      simp only [mapRoute, OperationalTranslation.mapRoute]
      rw [inductionHypothesis]
      rfl

/-! ## Strictness canary: fusion requires path-valued realization -/

namespace FusionCanary

@[reducible] def source : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first last => first = false ∧ last = true
  rewrites_resp_left := by
    rintro first first' last firstEq ⟨sourceEq, targetEq⟩
    subst first'
    exact ⟨last, ⟨sourceEq, targetEq⟩, rfl⟩
  rewrites_resp_right := by
    rintro first last last' ⟨sourceEq, targetEq⟩ lastEq
    subst last'
    exact ⟨sourceEq, targetEq⟩

@[reducible] def target : GSLT := GSLT.discrete Unit

theorem source_step : source.Step false true :=
  ⟨rfl, rfl⟩

/-- Fusion maps both administrative source states to one target state and the
source step to a zero-length target path. -/
def fused : OperationalRealization source target where
  mapTerm := fun _ => ()
  mapEquiv := fun _ => rfl
  mapStep := fun _ => .refl ()

@[simp] theorem fused_source_step_has_zero_target_steps :
    (fused.mapStep source_step).length = 0 :=
  rfl

/-- The same fusion cannot be expressed by the old one-source-step to
one-target-step interface because the target has no primitive steps. -/
theorem no_strict_operational_translation :
    ¬ Nonempty (OperationalTranslation source target) := by
  rintro ⟨translation⟩
  exact translation.mapStep source_step

end FusionCanary

#print axioms mapRoute_append
#print axioms mapRoute_comp
#print axioms mapRoute_ofTranslation
#print axioms FusionCanary.fused_source_step_has_zero_target_steps
#print axioms FusionCanary.no_strict_operational_translation

end OperationalRealization

end Mettapedia.GSLT.IndexedOperational
