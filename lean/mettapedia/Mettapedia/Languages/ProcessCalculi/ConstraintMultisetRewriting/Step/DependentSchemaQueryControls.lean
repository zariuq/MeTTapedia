import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentProgramControls

/-!+# Dependent type information controls a schema's none query

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

def noneSchema : Schema levels Nat triple where
  helpers := .nil _
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.predicate levels Nat .none gRow]

def nonePick : Pick noneSchema := ⟨⟨[], [], []⟩, rfl⟩

theorem compile_none (knowledge : EquationStore (TotalTerm triple)) :
    noneSchema.compile (s := queryState knowledge) nonePick = noneQueryFiring knowledge := rfl

theorem unknown_type_refuses_none :
    ¬ noneSchema.Admits (s := queryState []) nonePick := by
  intro admitted
  have actual := (noneSchema.compile_admits_iff (s := queryState []) nonePick).mpr admitted
  rw [compile_none] at actual
  exact none_refused_unknown actual

theorem ground_type_refuses_none :
    ¬ noneSchema.Admits (s := queryState [(xUniverse, groundUniverse)]) nonePick := by
  intro admitted
  have actual := (noneSchema.compile_admits_iff
    (s := queryState [(xUniverse, groundUniverse)]) nonePick).mpr admitted
  rw [compile_none] at actual
  exact none_refused_after_ground actual

theorem function_type_admits_none :
    noneSchema.Admits (s := queryState [(xUniverse, arrowUniverse)]) nonePick := by
  apply (noneSchema.compile_admits_iff
    (s := queryState [(xUniverse, arrowUniverse)]) nonePick).mp
  rw [compile_none]
  exact none_admitted_after_arrow

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram.QueryControls
