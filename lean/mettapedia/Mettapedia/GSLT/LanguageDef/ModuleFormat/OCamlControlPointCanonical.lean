import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPoint
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCanonicalState
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRowTyping

/-! Canonical commitment fixes every source control point, including pending
administrative configurations. Ordered vectors retain their original order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection

private theorem patternId_vector (index : Nat) : VectorFirstOrder (patternId index) :=
  node_vector_all _ _ (vector_list_cons (digits_vector index) vector_list_nil)

theorem ControlPoint.vector {program : OCaml.Program} {source : OCaml.MachineState} {config : Pattern} {rank : Nat}
    (point : ControlPoint program source config rank) : VectorFirstOrder config := by
  cases point with
  | state encoded => exact state?_vector _ _ _ encoded
  | application resolved _ =>
    exact node_vector_all _ _ (vector_list_cons (value_vector _) (vector_list_cons (value_vector _)
      (vector_list_cons (continuation?_vector _ _ _ resolved) vector_list_nil)))
  | matchOne _ resolved =>
    exact node_vector_all _ _ (vector_list_cons (patternId_vector _) (vector_list_cons (value_vector _)
      (vector_list_cons (code_vector _) (vector_list_cons (environment_vector _)
        (vector_list_cons (continuation?_vector _ _ _ resolved) vector_list_nil)))))
  | select listed resolved _ =>
    exact node_vector_all _ _ (vector_list_cons (clauseList?_vector _ _ _ listed) (vector_list_cons (value_vector _)
      (vector_list_cons (environment_vector _) (vector_list_cons (continuation?_vector _ _ _ resolved) vector_list_nil))))
  | clause _ listed resolved _ =>
    exact node_vector_all _ _ (vector_list_cons (patternId_vector _) (vector_list_cons (value_vector _)
      (vector_list_cons (code_vector _) (vector_list_cons (clauseList?_vector _ _ _ listed)
        (vector_list_cons (environment_vector _) (vector_list_cons (continuation?_vector _ _ _ resolved) vector_list_nil))))))
  | build resolved _ =>
    exact node_vector_all _ _ (vector_list_cons (build_vector _) (vector_list_cons (valueList_vector _)
      (vector_list_cons (continuation?_vector _ _ _ resolved) vector_list_nil)))
  | primitive resolved _ =>
    exact node_vector_all _ _ (vector_list_cons (primitive_vector _) (vector_list_cons (valueList_vector _)
      (vector_list_cons (continuation?_vector _ _ _ resolved) vector_list_nil)))
  | answer resolved =>
    exact node_vector_all _ _ (vector_list_cons (primitiveResult_vector _)
      (vector_list_cons (continuation?_vector _ _ _ resolved) vector_list_nil))

theorem control_point_commit (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {source : OCaml.MachineState} {config : Pattern} {rank : Nat}
    (built : prepare program = .ok prepared) (point : ControlPoint program source config rank) :
    Complete.Normalized.commit (epochPlan prepared table) .canonical config = config := by
  simp only [Complete.Normalized.commit, Complete.Normalized.standard,
    epoch_laws_empty program prepared table built, epoch_extrusions_empty program prepared table built,
    CollectionLaws.standardForm_nil]
  exact point.vector.canon_fixed

#print axioms ControlPoint.vector
#print axioms control_point_commit

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
