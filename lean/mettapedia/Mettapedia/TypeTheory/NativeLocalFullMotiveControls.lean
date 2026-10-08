import Mettapedia.TypeTheory.NativeLocalTypeControls
import Mettapedia.TypeTheory.NativeLocalSumElimination

/-!
# A native motive depending on both pair components

The motive is named on the complete pair context. Its fibre depends on
the argument and its supplied dependent witness. The independently
constructed branch retains the second witness; full elimination recovers
that entire section after the actual packing map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.NativeLocalFullMotiveControls

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTypeOperations
open NativeLocalParameterControls NativeLocalTypeControls NativeLocalSumElimination
open ContextualSumComprehension

abbrev tuple : Face.{0, 0, 0} World :=
  tupleContext (C := localModel World) domain codomain

def tupleName : tuple ⟶ naturals where
  app _ := TypeCat.ofHom fun receipt => receipt.1.2.val + receipt.2.val
  naturality := by intros; rfl

abbrev tupleMotive : NativeType tuple := ⟨naturals, finiteFibre, tupleName⟩

noncomputable def motive :=
  tupleMotive.reindex (unpack (stableSums World) domain codomain)

theorem motive_on_tuple :
    motive.reindex (pack (stableSums World) domain codomain) = tupleMotive := by
  change (tupleMotive.reindex (unpack (stableSums World) domain codomain)).reindex
    (pack (stableSums World) domain codomain) = tupleMotive
  have comparison : pack (stableSums World) domain codomain ≫
      unpack (stableSums World) domain codomain = 𝟙 tuple :=
    unpack_pack (stableSums World) domain codomain
  rw [← LocalType.reindex_comp]
  exact (congrArg (LocalType.reindex tupleMotive) comparison).trans
    (LocalType.reindex_id tupleMotive)

def branch : tupleMotive.decoded.sections where
  val point := ⟨point.2.2.val, by
    change point.2.2.val < point.2.1.2.val + point.2.2.val + 1
    omega⟩
  property := by
    intro source target arrow
    apply Fin.ext
    change source.2.2.val = target.2.2.val
    exact congrArg (fun receipt => receipt.2.val) arrow.property

noncomputable def pulledBranch :
    (motive.reindex (pack (stableSums World) domain codomain)).decoded.sections :=
  cast (congrArg (fun type : NativeType tuple => (type.decoded.sections : Type))
    motive_on_tuple.symm) branch

noncomputable def eliminated := fullMotiveEquiv domain codomain motive pulledBranch

private theorem cast_section_value {F G : DisplayedFamily.{0, 0, 0, 0} tuple}
    (same : F = G) (value : F.sections) (point : tuple.Elements) :
    HEq ((cast (congrArg (fun family : DisplayedFamily.{0, 0, 0, 0} tuple =>
      (family.sections : Type)) same) value).val point) (value.val point) := by
  cases same
  rfl

theorem actual_elimination_retains_branch :
    HEq ((localModel World).tmSub eliminated
      (pack (stableSums World) domain codomain)) branch :=
  (heq_of_eq (full_motive_beta domain codomain motive pulledBranch)).trans (cast_heq _ _)

theorem actual_elimination_point (point : tuple.Elements) :
    HEq ((substituteTerm (type := motive) eliminated
      (pack (stableSums World) domain codomain)).val point) (branch.val point) := by
  have computation := full_motive_beta domain codomain motive pulledBranch
  change substituteTerm (type := motive) eliminated
    (pack (stableSums World) domain codomain) = pulledBranch at computation
  rw [computation]
  have familyEquality := congrArg LocalType.decoded motive_on_tuple
  change HEq ((cast (congrArg (fun family : DisplayedFamily.{0, 0, 0, 0} tuple =>
    (family.sections : Type)) familyEquality.symm) branch).val point) (branch.val point)
  exact cast_section_value familyEquality.symm branch point

def zeroWitness : tuple.obj world := ⟨trueOne, ⟨0, by decide⟩⟩
def oneWitness : tuple.obj world := ⟨trueOne, ⟨1, by decide⟩⟩

theorem distinct_motive_fibres :
    tupleMotive.decoded.obj ⟨world, zeroWitness⟩ = Fin 2 ∧
      tupleMotive.decoded.obj ⟨world, oneWitness⟩ = Fin 3 := ⟨rfl, rfl⟩

theorem actual_branch_readouts :
    (branch.val ⟨world, zeroWitness⟩).val = 0 ∧
      (branch.val ⟨world, oneWitness⟩).val = 1 := ⟨rfl, rfl⟩

theorem erasing_second_witness_changes_readout :
    (branch.val ⟨world, zeroWitness⟩).val ≠ (branch.val ⟨world, oneWitness⟩).val := by
  decide

end Mettapedia.TypeTheory.NativeLocalFullMotiveControls
