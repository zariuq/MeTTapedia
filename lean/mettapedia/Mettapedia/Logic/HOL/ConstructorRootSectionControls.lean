import Mettapedia.Logic.HOL.ConstructorRootSection
import Mettapedia.Logic.HOL.IndexedConstructorRootInversionControls

/-!
# Controls for the root-index section

The independent recursive-tree model has two nullary constructors with
different result indices. The section retains the produced root and refuses
the other index under the original constructor-injectivity premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorRootSectionControls
open IndexedConstructorRootInversionControls

def member : ProofSyntax Symbol [] (.app (inventory.rootAt constructor .bot) value) :=
  inventory.rootAt_intro constructor .bot value producedRoot

theorem member_free : member.FunctionExtensionalityFree :=
  inventory.rootAt_intro_free _ _ _ producedRoot producedRoot_free

def recovered : ProofSyntax Symbol [] (inventory.rootIndex constructor value .bot) :=
  inventory.rootAt_elim constructor .bot value member

theorem recovered_free : recovered.FunctionExtensionalityFree :=
  inventory.rootAt_elim_free _ _ _ member member_free

def wrongSection : ClosedFormula Symbol := .app (inventory.rootAt constructor .top) value

def wrongSectionRefused : ProofSyntax Symbol [injectivity] (.not wrongSection) := by
  apply ProofSyntax.notI
  exact .notE (wrongIndexRefused.prepend wrongSection)
    (inventory.rootAt_elim constructor .top value (.hyp 0))

theorem wrongSectionRefused_free : wrongSectionRefused.FunctionExtensionalityFree := by
  unfold wrongSectionRefused
  exact ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr wrongIndexRefused_free,
    inventory.rootAt_elim_free constructor .top value
      (ProofSyntax.hyp (Δ := [wrongSection, injectivity]) 0) True.intro⟩

theorem member_valid : model.models (.app (inventory.rootAt constructor .bot) value) :=
  Soundness.extTheorem_sound member.erase model (model.functionsRespectEqv_of_fullDomains full)

theorem wrongSection_invalid : ¬ model.models wrongSection := by
  have implication := Soundness.extTheorem_sound (ProofSyntax.impI wrongSectionRefused).erase model
    (model.functionsRespectEqv_of_fullDomains full)
  exact (HenkinModel.models_not model).mp ((HenkinModel.models_imp model).mp implication injectivity_valid)

theorem section_is_not_constant :
    model.models (.app (inventory.rootAt constructor .bot) value) ∧ ¬ model.models wrongSection :=
  ⟨member_valid, wrongSection_invalid⟩

#print axioms member_free
#print axioms wrongSectionRefused_free
#print axioms section_is_not_constant
end Mettapedia.Logic.HOL.ConstructorRootSectionControls
