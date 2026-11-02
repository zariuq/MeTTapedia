import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandData
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextControls

/-!
# Finite command data: actual source declaration and certificate controls

The original type declaration retains its exact two outputs and existence
premise. A missing premise remains a refusal for every finite graph. Local
annotation checks reject a malformed instance certificate; unused provider
questions are not confused with the finite observation that is encoded.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open HOLLightFiniteWitnesses HOLLightFiniteCommandWitnesses HOLLightFiniteCommandData
open DefinitionAdapters.ContextControls ProofExecution.Registered.Controls

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

local instance : DecidableEq Const := SyntaxEncoding.constantCodec.decEq
local instance : DecidableEq Ty := SyntaxEncoding.tyCodec.decEq

def typeData : Mettapedia.OSLF.Binding.WireCodec.Data :=
  encode typeCommand (sampleCommand typeCommand HOLLightContextControls.TypeDefinition.output)

theorem actual_type_declaration_exact_outputs :
    (decode typeData).bind (fun command => command.check emptyAxiomPolicy coreContext #[identityExistence]) =
      some HOLLightContextControls.TypeDefinition.output :=
  every_accepted_command_representable emptyAxiomPolicy coreContext #[identityExistence] typeCommand
    HOLLightContextControls.TypeDefinition.command_checked

theorem actual_type_origin_retained : (decode typeData).map Command.origin = some ("define-type", 1) :=
  decoded_origin typeCommand _

theorem actual_selected_existence_retained : (decode typeData).map Command.parents = some [0] :=
  decoded_parents typeCommand _

theorem missing_existence_refused (graph : Graph) :
    (decode (encode typeCommand graph)).bind (fun command => command.check emptyAxiomPolicy coreContext #[]) = none := by
  rw [decode_encode]
  rfl

theorem malformed_instance_certificate_refused :
    constantInstanceB coreContext.signature (witnesses []) Const.equality Ty.bool = false := by
  simp [constantInstanceB, coreContext, baseContext, booleanContext, TheoryContext.addConstant,
    TheoryContext.addTypeOperator, TheoryContext.empty, Signature.addConstant,
    witnesses, HOLLightFiniteSignatureLookup.rowLookup, Ty.equality, TypeSubst.empty,
    TypeSubst.lookup, Ty.bool, Ty.function, Ty.same, TypeOp.same,
    TypeOp.function, TypeOp.bool, Name.global]

theorem finite_graph_does_not_identify_all_provider_questions (keys : Finset Key)
    (outside : Key) (absent : outside ∉ keys) (provider : InstanceWitnesses)
    (nonempty : (provider outside.1 outside.2).entries ≠ []) :
    witnesses (sample keys provider) outside.1 outside.2 ≠ provider outside.1 outside.2 := by
  have noRow : HOLLightFiniteSignatureLookup.rowLookup outside (sample keys provider) = none := by
    cases found : HOLLightFiniteSignatureLookup.rowLookup outside (sample keys provider) with
    | none => rfl
    | some value =>
        have member := HOLLightFiniteSignatureLookup.rowLookup_member found
        obtain ⟨key, inKeys, same⟩ := List.mem_map.mp member
        have equal : key = outside := congrArg Prod.fst same
        subst key
        exact False.elim (absent ((Finset.mem_sort _).mp inKeys))
  intro equal
  have empty : (provider outside.1 outside.2).entries = [] := by
    rw [← equal]
    simp [witnesses, noRow, TypeSubst.empty]
  exact nonempty empty

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandControls
