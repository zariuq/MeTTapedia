import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentProgramControls

/-!+# Dependent type information controls a schema's absence query

The existing query asks whether a Ground-typed row can coincide with a
stored row of unknown type. With no deciding type knowledge it is refused;
when the type is constrained to a function type, it is admitted. Schema
opening preserves those actual dependent-step verdicts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.QueryControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedContextual ContextualDependentEta ContextualDependentTwins
open DependentFull
open DependentFull.Controls

abbrev levels : TypedEquality.Normalization.LevelModel Tower.rules Nat := setting.levels

def absenceSchema : Schema levels Nat triple where
  helpers := .nil _
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.absent levels Nat gRow]

def absencePick : Pick absenceSchema := ⟨⟨[], [], []⟩, rfl⟩

theorem compile_absence (knowledge : EquationStore (TotalTerm triple)) :
    absenceSchema.compile (s := queryState knowledge) absencePick = absenceFiring knowledge := rfl

theorem unknown_type_refuses_absence :
    ¬ absenceSchema.Admits (s := queryState []) absencePick := by
  intro admitted
  have actual := (absenceSchema.compile_admits_iff (s := queryState []) absencePick).mpr admitted
  rw [compile_absence] at actual
  exact absence_refused_unknown actual

theorem ground_type_refuses_absence :
    ¬ absenceSchema.Admits (s := queryState [(xUniverse, groundUniverse)]) absencePick := by
  intro admitted
  have actual := (absenceSchema.compile_admits_iff
    (s := queryState [(xUniverse, groundUniverse)]) absencePick).mpr admitted
  rw [compile_absence] at actual
  exact absence_refused_after_ground actual

theorem function_type_admits_absence :
    absenceSchema.Admits (s := queryState [(xUniverse, arrowUniverse)]) absencePick := by
  apply (absenceSchema.compile_admits_iff
    (s := queryState [(xUniverse, arrowUniverse)]) absencePick).mp
  rw [compile_absence]
  exact absence_admitted_after_arrow

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.QueryControls
