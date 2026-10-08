import Mettapedia.GSLT.Core.OperationalReadback
import Mettapedia.GSLT.Core.OperationalPathFibration
import Mathlib.CategoryTheory.Yoneda

/-!
# Dependent certificates at supplied operational endpoints

An evidence functor on the existing free execution category states exactly
how a certificate changes along source executions. Readback of an actual
target prefix then transports the supplied certificate along the retained
source path. No reduction-preservation law is inferred from coherence over
a different, purely syntactic context category.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalReadbackEvidence

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite

universe u
variable {source target : GSLT.{u}}

structure Receipt (readback : OperationalReadback source target)
    (evidence : ExecutionObject source ⥤ Type u)
    {origin : source.Term} {current final : target.Term}
    (supplied : evidence.obj origin) (actual : ExecutionPath target current final) where
  after : source.Term
  sourcePath : ExecutionPath source origin after
  endpoint : readback.related after final
  lengthBound : sourcePath.length ≤ actual.length
  certificate : evidence.obj after
  transported : certificate = evidence.map sourcePath supplied

/-- Every supplied target prefix, with its exact endpoint and schedule,
has a source history and an actual transported dependent certificate. -/
theorem reflect (readback : OperationalReadback source target)
    (evidence : ExecutionObject source ⥤ Type u)
    {origin : source.Term} {current final : target.Term}
    (related : readback.related origin current) (supplied : evidence.obj origin)
    (actual : ExecutionPath target current final) :
    Nonempty (Receipt readback evidence supplied actual) := by
  obtain ⟨after, path, endpoint, bound⟩ := readback.reflectPath related actual
  exact ⟨⟨after, path, endpoint, bound, evidence.map path supplied, rfl⟩⟩

/-- Updating a certificate across two source histories agrees with updating
it across their composite; this uses the evidence functor's real action. -/
theorem update_composition (evidence : ExecutionObject source ⥤ Type u)
    {first middle last : source.Term} (before : ExecutionPath source first middle)
    (after : ExecutionPath source middle last) (supplied : evidence.obj first) :
    evidence.map (before.append after) supplied =
      evidence.map after (evidence.map before supplied) :=
  evidence.map_comp_apply before after supplied

/-- A concrete evidence family stores both a complete source history and
the initial witness. Its action appends the supplied path and retains the
witness, so it is not the support predicate of reachability. -/
def historyAndWitness (system : GSLT.{u}) (start : system.Term) (Witness : Type u) :
    ExecutionObject system ⥤ Type u where
  obj finish := ExecutionPath system start finish × Witness
  map suffix := TypeCat.ofHom (fun value => ⟨value.1.append suffix, value.2⟩)
  map_id finish := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext (Route.append_refl value.1) rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Prod.ext (Route.append_assoc value.1 first second).symm rfl

theorem historyAndWitness_update (system : GSLT.{u}) (start : system.Term) (Witness : Type u)
    {first last : system.Term} (initial : ExecutionPath system start first)
    (suffix : ExecutionPath system first last) (supplied : Witness) :
    (historyAndWitness system start Witness).map suffix ⟨initial, supplied⟩ =
      ⟨initial.append suffix, supplied⟩ := rfl

/-- Erasing history loses the distinction between a silent prefix and an
actual loop. The loop is an explicit hypothesis, not an invented transition. -/
theorem loop_history_not_erased (system : GSLT.{u}) (state : system.Term)
    (loop : system.Step state state) (Witness : Type u) (supplied : Witness) :
    ((.refl state : ExecutionPath system state state), supplied) ≠
        ((.cons ⟨loop⟩ (.refl state) : ExecutionPath system state state), supplied) ∧
      ((.refl state : ExecutionPath system state state), supplied).2 =
        ((.cons ⟨loop⟩ (.refl state) : ExecutionPath system state state), supplied).2 := by
  constructor
  · intro same
    have lengths := congrArg (fun value => value.1.length) same
    cases lengths
  · rfl

end Mettapedia.GSLT.IndexedOperational.OperationalReadbackEvidence
