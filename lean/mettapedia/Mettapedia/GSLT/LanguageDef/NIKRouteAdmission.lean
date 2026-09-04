import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.GSLT.LanguageDef.GSLTILRouteEquipment
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# Revision-indexed NIK admission over operational refinements

NIK admission is a metalogical judgment about a proposed realization.  It is
not an object-language theorem, a profitability comparison, or a runtime
checker call.  This module connects the common `AdmissionHom` algebra to the
GSLT-IL route structure:

* an operational object is a GSLT plus the semantic fibre to be preserved;
* a refinement is a path-valued operational realization plus fibre
  preservation;
* represented loose routes provide one source of such direct refinements;
* admitted refinements compose;
* stored admission is activated only when its selected dependencies agree
  with the current revision;
* executing an active admission applies only its retained direct map;
* profitability remains a separate optional receipt.

Exact route representation is sufficient but not necessary for NIK
refinement.  A compiler may validate a direct implementation against a richer
or nondeterministic source semantics by a refinement square even when the
entire raw relation is not itself the companion of a function.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment

universe uTerm uRevision uDependency uValue uCost

/-! ## Semantic operational refinements -/

/-- A GSLT together with the semantic fibre relevant to one admission
judgment. -/
structure OperationalObject where
  theory : GSLT.{uTerm}
  Meaning : theory.Term → Prop

namespace OperationalObject

def toAdmissionObject (object : OperationalObject.{uTerm}) :
    AdmissionObject.{uTerm} where
  Carrier := object.theory.Term
  Meaning := object.Meaning

end OperationalObject

/-- A direct realization that preserves equations, steps, and the selected
semantic fibre.  It carries no checker or emitted certificate. -/
structure Refinement
    (source target : OperationalObject.{uTerm}) where
  realization : OperationalRealization source.theory target.theory
  preservesMeaning : ∀ value, source.Meaning value →
    target.Meaning (realization.mapTerm value)

namespace Refinement

/-- Identity is admitted without changing execution or meaning. -/
def id (object : OperationalObject.{uTerm}) : Refinement object object where
  realization := OperationalRealization.id object.theory
  preservesMeaning := fun _ meaningful => meaningful

/-- Refinements compose in execution order. -/
def comp {first middle last : OperationalObject.{uTerm}}
    (earlier : Refinement first middle) (later : Refinement middle last) :
    Refinement first last where
  realization := OperationalRealization.comp earlier.realization
    later.realization
  preservesMeaning := fun value meaningful =>
    later.preservesMeaning _ (earlier.preservesMeaning value meaningful)

/-- Forget operational structure only after constructing the common NIK
admission arrow. -/
def toAdmissionHom {source target : OperationalObject.{uTerm}}
    (refinement : Refinement source target) :
    AdmissionHom source.toAdmissionObject target.toAdmissionObject where
  run := refinement.realization.mapTerm
  preserves := refinement.preservesMeaning

@[simp] theorem toAdmissionHom_run
    {source target : OperationalObject.{uTerm}}
    (refinement : Refinement source target) (value : source.theory.Term) :
    refinement.toAdmissionHom.run value = refinement.realization.mapTerm value :=
  rfl

@[simp] theorem toAdmissionHom_id (object : OperationalObject.{uTerm}) :
    (id object).toAdmissionHom = AdmissionHom.id object.toAdmissionObject := by
  ext
  rfl

@[simp] theorem toAdmissionHom_comp
    {first middle last : OperationalObject.{uTerm}}
    (earlier : Refinement first middle) (later : Refinement middle last) :
    (comp earlier later).toAdmissionHom =
      AdmissionHom.comp earlier.toAdmissionHom later.toAdmissionHom := by
  ext
  rfl

/-- An exactly represented GSLT-IL route supplies a direct operational
refinement once its selected meaning fibre is also preserved. -/
def ofRepresentedRoute {source target : OperationalObject.{uTerm}}
    (route : RepresentedOperationalRoute source.theory target.theory)
    (preservesMeaning : ∀ value, source.Meaning value →
      target.Meaning (route.representation.map value)) :
    Refinement source target where
  realization := OperationalRealization.ofTranslation
    route.toOperationalTranslation
  preservesMeaning := preservesMeaning

end Refinement

/-! ## Dependency-indexed currentness -/

/-- The exact dependency view used to decide whether stored admission remains
current.  `Dependency` may itself be a subtype selecting only the dependencies
of one artifact. -/
structure DependencySystem where
  Revision : Type uRevision
  Dependency : Type uDependency
  Value : Type uValue
  read : Revision → Dependency → Value

namespace DependencySystem

/-- Two revisions are interchangeable for one artifact exactly when all of
that artifact's selected dependency values agree. -/
def SameDependencies (system : DependencySystem)
    (first second : system.Revision) : Prop :=
  ∀ dependency, system.read first dependency = system.read second dependency

theorem sameDependencies_refl (system : DependencySystem)
    (revision : system.Revision) :
    system.SameDependencies revision revision := by
  intro dependency
  rfl

theorem sameDependencies_symm (system : DependencySystem)
    {first second : system.Revision}
    (same : system.SameDependencies first second) :
    system.SameDependencies second first := by
  intro dependency
  exact (same dependency).symm

theorem sameDependencies_trans (system : DependencySystem)
    {first second third : system.Revision}
    (firstSecond : system.SameDependencies first second)
    (secondThird : system.SameDependencies second third) :
    system.SameDependencies first third := by
  intro dependency
  exact (firstSecond dependency).trans (secondThird dependency)

end DependencySystem

/-- A semantic refinement admitted at one exact dependency revision.  The
stored object contains the retained proof, not a checker invocation. -/
structure AdmittedAt (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (source target : OperationalObject.{uTerm}) where
  refinement : Refinement source target

namespace AdmittedAt

/-- Identity admission at any revision. -/
def id (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (object : OperationalObject.{uTerm}) :
    AdmittedAt dependencies revision object object where
  refinement := Refinement.id object

/-- Admissions at the same dependency revision compose. -/
def comp {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {first middle last : OperationalObject.{uTerm}}
    (earlier : AdmittedAt dependencies revision first middle)
    (later : AdmittedAt dependencies revision middle last) :
    AdmittedAt dependencies revision first last where
  refinement := Refinement.comp earlier.refinement later.refinement

/-- Current activation of stored admission.  Construction requires exact
agreement of the selected dependency view, while the proof is absent from
the execution function below. -/
structure Active {dependencies : DependencySystem}
    {admittedRevision : dependencies.Revision}
    {source target : OperationalObject.{uTerm}}
    (admission : AdmittedAt dependencies admittedRevision source target)
    (currentRevision : dependencies.Revision) : Prop where
  current : dependencies.SameDependencies admittedRevision currentRevision

/-- Activate stored admission after proving exact dependency currentness. -/
def activate {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : OperationalObject.{uTerm}}
    (admission : AdmittedAt dependencies admittedRevision source target)
    (current : dependencies.SameDependencies admittedRevision currentRevision) :
    admission.Active currentRevision :=
  ⟨current⟩

/-- Execute an active admission.  Currentness has already selected the
artifact; the hot operation is only the retained direct function. -/
def Active.run {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : OperationalObject.{uTerm}}
    {admission : AdmittedAt dependencies admittedRevision source target}
    (_active : admission.Active currentRevision) :
    source.theory.Term → target.theory.Term :=
  admission.refinement.realization.mapTerm

@[simp] theorem Active.run_eq_refinement
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : OperationalObject.{uTerm}}
    {admission : AdmittedAt dependencies admittedRevision source target}
    (active : admission.Active currentRevision) :
    active.run = admission.refinement.realization.mapTerm :=
  rfl

/-- An active refinement still supplies the common NIK admission arrow; no
new preservation proof is generated during activation. -/
def Active.toAdmissionHom
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : OperationalObject.{uTerm}}
    {admission : AdmittedAt dependencies admittedRevision source target}
    (_active : admission.Active currentRevision) :
    AdmissionHom source.toAdmissionObject target.toAdmissionObject :=
  admission.refinement.toAdmissionHom

/-- Active execution preserves the admitted semantic fibre.  The proof is a
property of the retained refinement; `run` itself remains only the direct map. -/
theorem Active.preservesMeaning
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    {source target : OperationalObject.{uTerm}}
    {admission : AdmittedAt dependencies admittedRevision source target}
    (active : admission.Active currentRevision)
    (value : source.theory.Term) (meaningful : source.Meaning value) :
    target.Meaning (active.run value) :=
  admission.refinement.preservesMeaning value meaningful

end AdmittedAt

/-! ## Profitability is an orthogonal policy receipt -/

/-- Optional cost comparison for an already admitted semantic refinement.
Its absence cannot invalidate semantic admission, and its presence cannot
construct one. -/
structure ProfitabilityReceipt
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : OperationalObject.{uTerm}}
    (admission : AdmittedAt dependencies revision source target)
    (Cost : Type uCost) [Preorder Cost]
    (sourceCost : source.theory.Term → Cost)
    (targetCost : target.theory.Term → Cost) : Prop where
  improves : ∀ value,
    targetCost (admission.refinement.realization.mapTerm value) ≤
      sourceCost value

/-! ## Positive and negative controls -/

namespace Canary

@[reducible] private def discreteTheory (Carrier : Type) : GSLT where
  Term := Carrier
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ impossible
    exact False.elim impossible
  rewrites_resp_right := by
    intro _ _ _ impossible _
    exact False.elim impossible

@[reducible] def naturalObject : OperationalObject where
  theory := discreteTheory Nat
  Meaning := fun value => value ≠ 0

/-- A nonidentity operational refinement: successor preserves equality, the
empty step relation, and positivity. -/
def successorRefinement : Refinement naturalObject naturalObject where
  realization :=
    { mapTerm := Nat.succ
      mapEquiv := fun equal => congrArg Nat.succ equal
      mapStep := fun impossible => impossible.elim }
  preservesMeaning := fun _ _ => Nat.succ_ne_zero _

def dependencySystem : DependencySystem where
  Revision := Bool × Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision.1

def admittedSuccessor :
    AdmittedAt dependencySystem (false, false) naturalObject naturalObject :=
  ⟨successorRefinement⟩

/-- An irrelevant revision-coordinate change preserves the selected
dependency view and therefore activates the stored refinement. -/
theorem irrelevant_change_current :
    dependencySystem.SameDependencies (false, false) (false, true) := by
  intro dependency
  cases dependency
  rfl

def activeSuccessor : admittedSuccessor.Active (false, true) :=
  admittedSuccessor.activate irrelevant_change_current

/-- Active execution is the admitted direct map, not replay of its proof. -/
theorem active_successor_runs_directly : activeSuccessor.run 1 = 2 :=
  rfl

/-- A policy may certify this admitted realization as profitable. -/
def successorProfitability : ProfitabilityReceipt admittedSuccessor Nat
    (fun _ => 1) (fun _ => 0) := by
  constructor
  intro value
  exact Nat.zero_le _

/-- Semantic admission survives even when a declared cost observation refuses
the realization.  Profitability therefore cannot be part of admission itself. -/
theorem admitted_but_not_profitable_for_growth :
    ¬ Nonempty (ProfitabilityReceipt admittedSuccessor Nat
      (fun _ => 0) (fun value => value)) := by
  rintro ⟨receipt⟩
  have impossible : Nat.succ 0 ≤ 0 := by
    simpa [admittedSuccessor, successorRefinement] using receipt.improves 0
  exact Nat.not_succ_le_zero 0 impossible

/-- Changing a selected dependency prevents reuse of the stored artifact. -/
theorem relevant_change_not_current :
    ¬ dependencySystem.SameDependencies (false, false) (true, false) := by
  intro same
  have changed := same ()
  simp [dependencySystem] at changed

/-- Consequently no current activation can be constructed at the changed
dependency revision. -/
theorem no_activation_after_relevant_change :
    ¬ Nonempty (admittedSuccessor.Active (true, false)) := by
  rintro ⟨active⟩
  exact relevant_change_not_current active.current

@[reducible] def trueObject : OperationalObject where
  theory := discreteTheory Bool
  Meaning := fun value => value = true

/-- Negative semantic control: an arbitrary direct callback does not become
NIK admission when it leaves the selected meaning fibre. -/
theorem no_negation_refinement :
    ¬ ∃ refinement : Refinement trueObject trueObject,
      refinement.realization.mapTerm = Bool.not := by
  rintro ⟨refinement, mapEqual⟩
  have preserved := refinement.preservesMeaning true rfl
  rw [mapEqual] at preserved
  simp at preserved

end Canary

/-! ## Universe-polymorphic controls -/

namespace UniverseCanary

/-- A nontrivial semantic fibre whose operational terms live strictly above
universe zero. -/
def liftedTrueObject : OperationalObject.{1} where
  theory := GSLT.discrete (ULift.{1, 0} Bool)
  Meaning := fun value => value.down = true

/-- Identity refinement is available at the higher universe. -/
def liftedIdentity : Refinement liftedTrueObject liftedTrueObject :=
  Refinement.id liftedTrueObject

theorem lifted_identity_runs_true :
    liftedIdentity.realization.mapTerm (ULift.up true) = ULift.up true :=
  rfl

/-- The higher-universe generalization retains semantic rejection; it is not
merely a vacuous inhabitant. -/
theorem no_lifted_negation_refinement :
    ¬ ∃ refinement : Refinement liftedTrueObject liftedTrueObject,
      refinement.realization.mapTerm =
        (fun value : ULift.{1, 0} Bool => ULift.up (!value.down)) := by
  rintro ⟨refinement, mapEqual⟩
  have preserved := refinement.preservesMeaning (ULift.up true) rfl
  rw [mapEqual] at preserved
  simp [liftedTrueObject] at preserved

end UniverseCanary

#print axioms Refinement.toAdmissionHom_comp
#print axioms DependencySystem.sameDependencies_trans
#print axioms AdmittedAt.Active.run_eq_refinement
#print axioms AdmittedAt.Active.preservesMeaning
#print axioms Canary.active_successor_runs_directly
#print axioms Canary.admitted_but_not_profitable_for_growth
#print axioms Canary.no_activation_after_relevant_change
#print axioms Canary.no_negation_refinement
#print axioms UniverseCanary.lifted_identity_runs_true
#print axioms UniverseCanary.no_lifted_negation_refinement

end Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
