import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFieldGuards
import Mettapedia.Logic.HOL.FiniteConstructorFieldEmbeddingControls

/-!
# Actual parsed field-guard controls

The nontrivial recursive-space provider stores both Boolean answers
faithfully. A separate numeric environment supplies arity two and either the
canonical zero shape or a noncanonical shape two. The numeric guard is also
restrictive. The position-one program is left arbitrary: these controls
observe field guards, rather than assigning it an arithmetic interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFieldGuardControls
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open FiniteConstructorEncoding CurriedPredicates
open FiniteConstructorFieldEmbeddingControls
open IndexedVectorTreeStoredFieldGuards

abbrev Context : Ctx Base := [N,N,N]
def emptyToContext : Subst Const [] Context := fun index => nomatch index
def storedInputs := given.substitute emptyToContext
def sourcePredicate : Term Const Context (A ⇒ .prop) := weakenCtx Context onlyTrue

def numbers : Term Const Context (N ⇒ .prop) :=
  .lam (.eq (.var .vz) (weaken (.var (.vs (.vs .vz)))))
def arity : Term Const Context N := .var (.vs .vz)
def shape : Term Const Context N := .var .vz

def numericValues (n q : Nat) : model.Valuation Context
  | _,.vz => ULift.up q
  | _,.vs .vz => ULift.up n
  | _,.vs (.vs .vz) => ULift.up 2
  | _,.vs (.vs (.vs impossible)) => nomatch impossible

def actualBranch (one : ClosedTerm Const N) : Formula Const Context :=
  applyArguments [N,N]
    (compiledConditions storedInputs sourcePredicate numbers (.const .zero) one ⟨1,by decide⟩)
    (arity,shape,PUnit.unit)

theorem branch_meaning (one : ClosedTerm Const N) (n q : Nat) :
    (model.denote (actualBranch one) (numericValues n q)).down ↔ n = 2 ∧ q = 0 := by
  have checked := Soundness.extDerivation_sound (M := model) (ρ := numericValues n q)
    (application_eq (Δ := []) storedInputs sourcePredicate numbers (.const .zero) one
      ⟨1,by decide⟩ (arity,shape,PUnit.unit)).erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) (by intro formula present; cases present)
  change (model.denote (actualBranch one) (numericValues n q)).down ↔
    ((ULift.up n : Number) = ULift.up 2 ∧ (ULift.up q = (ULift.up 0 : Number) ∧ True)) at checked
  simpa only [ULift.up.injEq,and_true] using checked

theorem arity_two_zero_shape_accepted (one : ClosedTerm Const N) :
    (model.denote (actualBranch one) (numericValues 2 0)).down :=
  (branch_meaning one 2 0).mpr ⟨rfl,rfl⟩

theorem arity_two_shape_two_refused (one : ClosedTerm Const N) :
    ¬ (model.denote (actualBranch one) (numericValues 2 2)).down := by
  intro present
  have impossible := (branch_meaning one 2 2).mp present
  exact Nat.noConfusion impossible.2

theorem wrong_numeric_guard_refused (one : ClosedTerm Const N) :
    ¬ (model.denote (actualBranch one) (numericValues 1 0)).down := by
  intro present
  have impossible := (branch_meaning one 1 0).mp present
  have wrong := impossible.1
  omega

def actualSolved (one : ClosedTerm Const N) (answer : Bool) : ClosedFormula Const :=
  applyArguments [E]
    (compiledConditions given onlyTrue (.lam .top) (.const .zero) one ⟨0,by decide⟩)
    (.app given.encode (.const (.answer answer)),PUnit.unit)

theorem solved_meaning (one : ClosedTerm Const N) (answer : Bool) :
    (model.denote (actualSolved one answer) values).down ↔
      (model.denote (given.predicate onlyTrue) values (model.denote encode values (.up answer))).down := by
  exact Soundness.extDerivation_sound (M := model) (ρ := values)
    (application_eq (Δ := []) given onlyTrue (.lam .top) (.const .zero) one
      ⟨0,by decide⟩ (.app given.encode (.const (.answer answer)),PUnit.unit)).erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) (by intro formula present; cases present)

theorem true_answer_accepted (one : ClosedTerm Const N) :
    (model.denote (actualSolved one true) values).down := (solved_meaning one true).mpr accepted_true

theorem false_answer_refused (one : ClosedTerm Const N) :
    ¬ (model.denote (actualSolved one false) values).down := fun present =>
  rejected_false ((solved_meaning one false).mp present)


def actualCount (one : ClosedTerm Const N) : Term Const Context N :=
  .app (HOL.subst (Subst.cons arity Subst.id)
    ((reading (Γ := Context) (E := E) one).count (context := [.length]) "Vector" IndexedPositiveContainer.VectorControl.entry
      (by simp [registry,IndexedPositiveContainer.VectorControl.registry]) .here)) shape

theorem count_uses_arity (one : ClosedTerm Const N) (n q : Nat) :
    model.denote (actualCount one) (numericValues n q) = ULift.up n := rfl

theorem shape_does_not_replace_arity (one : ClosedTerm Const N) :
    model.denote (actualCount one) (numericValues 2 0) = ULift.up 2 ∧
      model.denote (actualCount one) (numericValues 2 2) = ULift.up 2 :=
  ⟨count_uses_arity one 2 0,count_uses_arity one 2 2⟩

#print axioms branch_meaning
#print axioms arity_two_zero_shape_accepted
#print axioms arity_two_shape_two_refused
#print axioms wrong_numeric_guard_refused
#print axioms true_answer_accepted
#print axioms false_answer_refused
#print axioms shape_does_not_replace_arity
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFieldGuardControls
