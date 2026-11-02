import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlNormalizedProgress

/-! A finite independent source evaluation admits no infinite sequence of
committed normalized O0 transitions. Search scheduling and service epochs
are handled separately; this theorem does not identify a pause with a step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem normalized_accessible (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {source : OCaml.MachineState} {config : Pattern}
    {rank budget : Nat} {result : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (point : ControlPoint program source config rank) (completed : OCaml.run program budget source = .complete result) :
    Acc (fun target current => Complete.Normalized.NormalizedStep
      (epochPlan prepared table) [] (.base "MlConfig") .canonical current target) config := by
  refine Acc.intro config ?_
  intro target step
  obtain ⟨next, nextRank, work, nextPoint, later, smaller⟩ := normalized_step_progress program prepared table
    built invariant point completed step
  exact normalized_accessible program prepared table built invariant nextPoint later
termination_by (budget, rank)
decreasing_by
  rcases smaller with less | ⟨same, less⟩
  · exact Prod.Lex.left _ _ less
  · subst work
    exact Prod.Lex.right _ less

#print axioms normalized_accessible

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
