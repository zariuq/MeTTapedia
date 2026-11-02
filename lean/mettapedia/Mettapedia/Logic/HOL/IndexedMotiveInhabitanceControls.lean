import Mettapedia.Logic.HOL.IndexedMotiveInhabitance
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# Retained motive witnesses and empty indexed fibres

The motive depends on its index, point and result. Elimination uses the
opened result witness to prove a separate existential. A false point has
no result although the Boolean result carrier itself is inhabited.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedMotiveInhabitanceControls

open FiniteConstructorEncoding.Controls (Constants model values)

def motive : ClosedTerm Constants (.prop ⇒ .prop ⇒ .prop ⇒ .prop) :=
  .lam (.lam (.lam (.and (.var (.vs (.vs .vz))) (.and (.var (.vs .vz)) (.var .vz)))))

def typed : ProofSyntax Constants [] (.app (.app (.app motive .top) .top) .top) :=
  .impE (.eqPropER (CurriedGuardProgramProofs.beta3
    (.and (.var (.vs (.vs .vz))) (.and (.var (.vs .vz)) (.var .vz))) .top .top .top))
    (.andI .topI (.andI .topI .topI))

theorem typed_free : typed.FunctionExtensionalityFree :=
  ⟨CurriedGuardProgramProofs.beta3_free _ _ _ _, True.intro, True.intro, True.intro⟩

def inhabited := IndexedMotiveInhabitance.introduce motive .top .top .top typed

theorem inhabited_free : inhabited.FunctionExtensionalityFree :=
  IndexedMotiveInhabitance.introduce_free motive .top .top .top typed typed_free

def goal : ClosedFormula Constants := .ex (.var .vz)
def body : Formula Constants [.prop] :=
  .app (weaken (.app (.app motive .top) .top)) (.var .vz)

def continuation : ProofSyntax Constants [body] (weaken goal) := by
  let result : Term Constants [.prop] .prop := .var .vz
  have present : ProofSyntax Constants [body] (.app (.app (.app (weaken motive) .top) .top) result) := .hyp 0
  have components : ProofSyntax Constants [body] (.and .top (.and .top result)) :=
    .impE (.eqPropEL (CurriedGuardProgramProofs.beta3
      (.and (.var (.vs (.vs .vz))) (.and (.var (.vs .vz)) (.var .vz))) .top .top result)) present
  exact .exI result (.andER (.andER components))

theorem continuation_free : continuation.FunctionExtensionalityFree := by
  unfold continuation
  exact ⟨CurriedGuardProgramProofs.beta3_free _ _ _ _, True.intro⟩

def eliminated := IndexedMotiveInhabitance.eliminate motive .top .top goal inhabited continuation

theorem eliminated_free : eliminated.FunctionExtensionalityFree :=
  IndexedMotiveInhabitance.eliminate_free motive .top .top goal inhabited continuation inhabited_free continuation_free

theorem false_point_refused : ¬ Nonempty (ProofSyntax Constants []
    (.app (.app (IndexedMotiveInhabitance.predicate motive) .bot) .top)) := by
  rintro ⟨present⟩
  have impossible := Soundness.extDerivation_sound present.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ absent; nomatch absent) (by intro _ absent; nomatch absent)
  change ∃ result : ULift.{1} Prop, True ∧ (True ∧ False ∧ result.down) at impossible
  obtain ⟨_, _, _, absent, _⟩ := impossible
  exact absent

theorem false_result_refused : ¬ Nonempty (ProofSyntax Constants []
    (.app (.app (.app motive .top) .top) .bot)) := by
  rintro ⟨present⟩
  have impossible := Soundness.extDerivation_sound present.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ absent; nomatch absent) (by intro _ absent; nomatch absent)
  exact impossible.2.2

#print axioms eliminated_free
#print axioms false_point_refused
#print axioms false_result_refused

end Mettapedia.Logic.HOL.IndexedMotiveInhabitanceControls
