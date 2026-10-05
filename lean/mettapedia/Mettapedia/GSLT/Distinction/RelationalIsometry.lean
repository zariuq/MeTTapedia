import Mettapedia.GSLT.Distinction.Isometry
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# Metric transport through a span of related execution states

Functional observation bisimulations already preserve formula values and
logical distance. A relation with labelled forth/back laws factors through
the GSLT of related state pairs and their matched actual transitions. Both
projections are functional observation bisimulations. This retains runtime
phases without selecting a decoder or collapsing them to a single compiler
image. Behavioral distance additionally requires the existing finite-branching
hypotheses; logical transport itself does not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational

universe uS uT uA uL uO uA' uL' uO'

structure ObservationRelation {S : GSLT.{uS}} {T : GSLT.{uT}}
    (Q : GradedSystem.{uS, uA, uL, uO} S) (R : GradedSystem.{uT, uA', uL', uO'} T) where
  related : S.Term → T.Term → Prop
  atom : Q.observations.Atom → R.observations.Atom
  label : Q.dynamics.Label → R.dynamics.Label
  discount_eq : Q.discount = R.discount
  value_map : ∀ observation ⦃source target⦄, related source target →
    R.observations.value (atom observation) target = Q.observations.value observation source
  forth : ∀ action ⦃source target after⦄, related source target → Q.dynamics.act action source after →
    ∃ final, R.dynamics.act (label action) target final ∧ related after final
  back : ∀ action ⦃source target final⦄, related source target →
    R.dynamics.act (label action) target final →
    ∃ after, Q.dynamics.act action source after ∧ related after final

namespace ObservationRelation

variable {S : GSLT.{uS}} {T : GSLT.{uT}}
  {Q : GradedSystem.{uS, uA, uL, uO} S} {R : GradedSystem.{uT, uA', uL', uO'} T}
  (relation : ObservationRelation Q R)

abbrev Pair := {pair : S.Term × T.Term // relation.related pair.1 pair.2}

/-- Edges carry both actual transitions and the common action label. -/
def span : GSLT where
  Term := relation.Pair
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites left right := ∃ label,
    Q.dynamics.act label left.1.1 right.1.1 ∧
      R.dynamics.act (relation.label label) left.1.2 right.1.2
  rewrites_resp_left := by
    rintro left _ right rfl step
    exact ⟨right, step, rfl⟩
  rewrites_resp_right := by
    rintro left right _ step rfl
    exact step

def dynamics : System relation.span where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Q.dynamics.Label
  act label left right := Q.dynamics.act label left.1.1 right.1.1 ∧
    R.dynamics.act (relation.label label) left.1.2 right.1.2
  act_resp_left := by
    rintro label left _ right rfl step
    exact ⟨right, step, rfl⟩
  act_resp_right := by
    rintro label left right _ step rfl
    exact step

def readings : GradedObservations relation.span where
  Atom := Q.observations.Atom
  value observation pair := Q.observations.value observation pair.1.1
  value_nonneg observation pair := Q.observations.value_nonneg observation pair.1.1
  value_le_one observation pair := Q.observations.value_le_one observation pair.1.1
  value_resp := by
    rintro observation left _ rfl
    rfl

def graded : GradedSystem relation.span where
  dynamics := relation.dynamics
  observations := relation.readings
  discount := Q.discount
  discount_nonneg := Q.discount_nonneg
  discount_le_one := Q.discount_le_one

def sourceProjection : ObservationBisimulation relation.graded Q where
  mapTerm pair := pair.1.1
  mapEquiv := by rintro left _ rfl; exact S.equations.iseqv.refl _
  atom := id
  label := id
  discount_eq := rfl
  value_map _ _ := rfl
  mapAct _ _ _ step := step.1
  liftAct label pair after step := by
    obtain ⟨final, targetStep, related⟩ := relation.forth label pair.2 step
    exact ⟨⟨(after, final), related⟩, ⟨step, targetStep⟩, S.equations.iseqv.refl _⟩

def targetProjection : ObservationBisimulation relation.graded R where
  mapTerm pair := pair.1.2
  mapEquiv := by rintro left _ rfl; exact T.equations.iseqv.refl _
  atom := relation.atom
  label := relation.label
  discount_eq := relation.discount_eq
  value_map observation pair := relation.value_map observation pair.2
  mapAct _ _ _ step := step.2
  liftAct label pair final step := by
    obtain ⟨after, sourceStep, related⟩ := relation.back label pair.2 step
    exact ⟨⟨(after, final), related⟩, ⟨sourceStep, step⟩, T.equations.iseqv.refl _⟩

theorem logicalDistance_eq (atoms : Function.Surjective relation.atom)
    (labels : Function.Surjective relation.label)
    {left right : S.Term} {left' right' : T.Term}
    (before : relation.related left left') (after : relation.related right right') :
    R.logicalDistance left' right' = Q.logicalDistance left right := by
  let first : relation.Pair := ⟨(left, left'), before⟩
  let second : relation.Pair := ⟨(right, right'), after⟩
  exact (relation.targetProjection.logicalDistance_map atoms labels first second).trans
    (relation.sourceProjection.logicalDistance_map Function.surjective_id
      Function.surjective_id first second).symm

theorem behaviouralDistance_eq (atoms : Function.Surjective relation.atom)
    (labels : Function.Surjective relation.label)
    (sourceFinite : Q.dynamics.ImageFiniteModulo) (targetFinite : R.dynamics.ImageFiniteModulo)
    {left right : S.Term} {left' right' : T.Term}
    (before : relation.related left left') (after : relation.related right right') :
    R.behaviouralDistance left' right' = Q.behaviouralDistance left right := by
  rw [R.behaviouralDistance_eq_logicalDistance targetFinite,
    Q.behaviouralDistance_eq_logicalDistance sourceFinite]
  exact relation.logicalDistance_eq atoms labels before after

end ObservationRelation

section Closure

variable {S : GSLT.{uS}} {T : GSLT.{uT}} (comparison : OperationalCorrespondence S T)
  (sourceReadings : GradedObservations.{uS, uO} S.closure)
  (targetReadings : GradedObservations.{uT, uO'} T.closure)
  (atom : sourceReadings.Atom → targetReadings.Atom)
  (values : ∀ observation ⦃source target⦄, comparison.related source target →
    targetReadings.value (atom observation) target = sourceReadings.value observation source)
  (discount : ℝ) (nonneg : 0 ≤ discount) (bounded : discount ≤ 1)

/-- Weak finite-reachability transport hides primitive administrative work.
It does not identify reachability blocks with one source firing. -/
def closureObservationRelation :
    ObservationRelation (GradedSystem.stepping S.closure sourceReadings discount nonneg bounded)
      (GradedSystem.stepping T.closure targetReadings discount nonneg bounded) where
  related source target := ∃ source₀ target₀,
    S.Equiv source source₀ ∧ T.Equiv target target₀ ∧ comparison.related source₀ target₀
  atom := atom
  label := id
  discount_eq := rfl
  value_map := by
    rintro observation source target ⟨source₀, target₀, sourceEq, targetEq, related⟩
    exact (targetReadings.value_resp _ targetEq).trans
      ((values observation related).trans (sourceReadings.value_resp _ sourceEq).symm)
  forth := by
    rintro action source target after ⟨source₀, target₀, sourceEq, targetEq, related⟩
      ⟨reached, path, reachedEq⟩
    obtain ⟨endpoint₀, ⟨reached₀, path₀, reached₀Eq⟩, reachedEq₀⟩ :=
      S.closure.rewrites_resp_left sourceEq ⟨reached, path, S.equations.iseqv.refl _⟩
    have equalReached := S.equations.iseqv.trans reachedEq₀ (S.equations.iseqv.symm reached₀Eq)
    obtain ⟨final, targetPath, nextRelated⟩ := comparison.liftMultiStep related path₀
    obtain ⟨final₀, actual, equalFinal⟩ := T.closure.rewrites_resp_left
      (T.equations.iseqv.symm targetEq) ⟨final, targetPath, T.equations.iseqv.refl _⟩
    exact ⟨final₀, actual, reached₀, final,
      S.equations.iseqv.trans (S.equations.iseqv.symm reachedEq) equalReached,
      T.equations.iseqv.symm equalFinal, nextRelated⟩
  back := by
    rintro action source target final ⟨source₀, target₀, sourceEq, targetEq, related⟩
      ⟨reached, path, reachedEq⟩
    obtain ⟨endpoint₀, ⟨reached₀, path₀, reached₀Eq⟩, reachedEq₀⟩ :=
      T.closure.rewrites_resp_left targetEq ⟨reached, path, T.equations.iseqv.refl _⟩
    have equalReached := T.equations.iseqv.trans reachedEq₀ (T.equations.iseqv.symm reached₀Eq)
    obtain ⟨after, sourcePath, nextRelated⟩ :=
      comparison.toOperationalReadback.reflectMultiStep related path₀
    obtain ⟨after₀, actual, equalAfter⟩ := S.closure.rewrites_resp_left
      (S.equations.iseqv.symm sourceEq) ⟨after, sourcePath, S.equations.iseqv.refl _⟩
    exact ⟨after₀, actual, after, reached₀, S.equations.iseqv.symm equalAfter,
      T.equations.iseqv.trans (T.equations.iseqv.symm reachedEq) equalReached, nextRelated⟩

end Closure

end Mettapedia.GSLT.Distinction
