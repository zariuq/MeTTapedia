import Mettapedia.GSLT.Logic.ContextualObservedCoalgebra
import Mettapedia.GSLT.Logic.HennessyMilnerTransport

/-!
# Full transport of declared contextual observations

A natural map whose complete future image is exactly the target coalgebra
constructs an operational cover. The cover lifts every target action from a
mapped state, while preserving each declared atom. Its actual material values
are equal, and all Hennessy--Milner formulas are preserved and reflected.

The statement retains the actual context arrow. No incoming lifting law,
occurrence inverse, or predecessor-modal preservation is inferred from this
outgoing cover.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedCoalgebraTransport

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph
open ContextualObservedCoalgebra HennessyMilner

universe u
variable {D : Type u} [Category.{u} D] {A B : D ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
variable (operation : NaturalHom A B)
variable (square : source.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
variable {Atom : Type u} (sourceAtoms : Atom → State A → Prop) (targetAtoms : Atom → State B → Prop)
variable (atomLaw : ∀ atom state, sourceAtoms atom state ↔ targetAtoms atom (graphMap operation state))
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))

def cover : SystemCover (system source sourceAtoms) (system target targetAtoms) where
  mapTerm := graphMap operation
  mapAtom := id
  mapLabel := id
  mapEquiv same := congrArg (graphMap operation) same
  observes_iff := atomLaw
  mapAct {label first last} step := by
    have bisimulation := coalgebra_map_isLabelledBisimulation source
      (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading operation target square
    obtain ⟨matchingLabel, matching, matched, labelsEqual, statesEqual⟩ :=
      (bisimulation (a := first) rfl).1 label last step
    have labelEqual := (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective labelsEqual
    cases labelEqual
    exact statesEqual ▸ matched
  liftAct {label first last} step := by
    have bisimulation := coalgebra_map_isLabelledBisimulation source
      (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading operation target square
    obtain ⟨matchingLabel, matching, matched, labelsEqual, statesEqual⟩ :=
      (bisimulation (a := first) rfl).2 label last step
    have labelEqual := (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective labelsEqual
    cases labelEqual
    exact ⟨matching, matched, statesEqual.symm⟩

variable (atoms : ArgumentCoding Atom)

include square atomLaw

theorem encoded_graph_bisimulation :
    IsLabelledBisimulation
      (ObservedMaterialization.encodedStep (system source sourceAtoms))
      (ObservedMaterialization.encodedStep (system target targetAtoms))
      (readings source sourceAtoms worlds arrows atoms).taggedReading
      (readings target targetAtoms worlds arrows atoms).taggedReading
      (fun first second => second = first.map (graphMap operation)) := by
  intro first second related
  subst second
  cases first with
  | none =>
      constructor <;> intro label next step <;> cases label <;> cases next <;> exact step.elim
  | some first =>
      constructor
      · intro label next step
        cases label with
        | inl atom =>
            cases next with
            | none => exact ⟨.inl atom, none, (atomLaw atom first).mp step, rfl, rfl⟩
            | some next => exact step.elim
        | inr action =>
            cases next with
            | none => exact step.elim
            | some next =>
                exact ⟨.inr action, some (graphMap operation next),
                  (cover source target operation square sourceAtoms targetAtoms atomLaw worlds arrows).mapAct step,
                  rfl, rfl⟩
      · intro label next step
        cases label with
        | inl atom =>
            cases next with
            | none => exact ⟨.inl atom, none, (atomLaw atom first).mpr step, rfl, rfl⟩
            | some next => exact step.elim
        | inr action =>
            cases next with
            | none => exact step.elim
            | some next =>
                obtain ⟨matching, matched, statesEqual⟩ :=
                  (cover source target operation square sourceAtoms targetAtoms atomLaw worlds arrows).liftAct step
                exact ⟨.inr action, some matching, matched, rfl, congrArg some statesEqual.symm⟩

theorem value_preservation (state : State A) :
    value source sourceAtoms worlds arrows atoms state =
      value target targetAtoms worlds arrows atoms (graphMap operation state) :=
  (readings source sourceAtoms worlds arrows atoms).taggedPresentation.decorate_eq_of_labelledBisimilar
    (readings target targetAtoms worlds arrows atoms).taggedPresentation
    ⟨_, encoded_graph_bisimulation source target operation square sourceAtoms targetAtoms atomLaw worlds arrows atoms,
      rfl⟩

include atomLaw worlds arrows in
theorem formula_preservation_reflection (formula : Formula Atom (Label D)) (state : State A) :
    (system target targetAtoms).sat formula (graphMap operation state) ↔
      (system source sourceAtoms).sat formula state := by
  have transported :=
    (cover source target operation square sourceAtoms targetAtoms atomLaw worlds arrows).sat_map formula state
  change (system target targetAtoms).sat (Formula.map id id formula) (graphMap operation state) ↔
    (system source sourceAtoms).sat formula state at transported
  exact Eq.mp (congrArg (fun mapped : Formula Atom (Label D) =>
    (system target targetAtoms).sat mapped (graphMap operation state) ↔
      (system source sourceAtoms).sat formula state) (Formula.map_id formula)) transported

theorem material_formula_preservation_reflection (formula : Formula Atom (Label D)) (state : State A) :
    (readings target targetAtoms worlds arrows atoms).materialSat formula
        (value target targetAtoms worlds arrows atoms (graphMap operation state)) ↔
      (readings source sourceAtoms worlds arrows atoms).materialSat formula
        (value source sourceAtoms worlds arrows atoms state) :=
  (material_formula_iff target targetAtoms worlds arrows atoms formula _).trans
    ((formula_preservation_reflection source target operation square sourceAtoms targetAtoms atomLaw worlds arrows formula state).trans
      (material_formula_iff source sourceAtoms worlds arrows atoms formula state).symm)

theorem context_value_square {first second : D} (step : first ⟶ second) (argument : A.obj first) :
    value source sourceAtoms worlds arrows atoms ⟨second, A.map step argument⟩ =
      value target targetAtoms worlds arrows atoms ⟨second, B.map step (operation.app first argument)⟩ := by
  have values := value_preservation source target operation square sourceAtoms targetAtoms atomLaw worlds arrows atoms
    ⟨second, A.map step argument⟩
  change _ = value target targetAtoms worlds arrows atoms ⟨second, operation.app second (A.map step argument)⟩ at values
  exact values.trans (congrArg (fun next => value target targetAtoms worlds arrows atoms ⟨second, next⟩)
    (operation.naturality step argument).symm)

end Mettapedia.GSLT.ContextualObservedCoalgebraTransport
