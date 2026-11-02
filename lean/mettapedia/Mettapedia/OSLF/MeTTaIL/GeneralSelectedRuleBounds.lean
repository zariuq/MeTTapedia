import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! A selected premise-free row's output names are supplied by its input.
This is read from the actual admission flow check and retained elaboration,
not from a second hand-maintained variable inventory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

open Syntax

theorem selected_premiseFree_bound {snapshot : Snapshot} {permissions : Permissions} {row : RulePlan} {ordinal : Nat}
    (position : (compile snapshot permissions).rules[ordinal]? = some row) (premiseFree : row.authored.premises = []) :
    ∀ name ∈ row.authored.right.freeFvarNames, name ∈ row.authored.left.freeFvarNames := by
  obtain ⟨actual, index, _, _, selected⟩ := compiled_rule_origin (List.mem_of_getElem? position)
  obtain ⟨_, authored, _, _, _, checked⟩ := rulePlan_readout selected
  change GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider row.rule row.binding.spec = true at checked
  have noPremises : row.rule.premises = [] := premiseFree
  simp only [GeneralPremise.rulePremisesAdmitted, noPremises, GeneralPremise.premisesFlow,
    Bool.true_and] at checked
  exact GeneralPremise.namesAvailable_sound _ _ checked

#print axioms selected_premiseFree_bound

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
