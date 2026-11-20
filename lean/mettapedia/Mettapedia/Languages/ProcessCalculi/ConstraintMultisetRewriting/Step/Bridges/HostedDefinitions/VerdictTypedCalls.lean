import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalTypedExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.CheckedDeclarations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxLimit

/-!
# Verdict-checked compiled calls in a fresh mixed development

The actual typing certificate proves that a compiled call contains none of
the development's fresh names. Its directed reductions and normal answers
therefore reflect to the existing vector package. This does not qualify the
raw new rows or identify substitution interpretation with reflection of an
arbitrary named constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictTypedCalls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open AlgebraicSchema (SchemaTable)
open TelescopeAbstraction (applyClosed)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg level1)

theorem typed_old {dev : Definitions.Development} (fresh : Definitions.devFresh dev = true)
    {n : Nat} {Γ : Ctx Tower.Head n} {term type : Tower.Tm n} (typed : Typed pkg Γ term type) :
    Definitions.OldTerm dev term := by
  intro entry member
  have missing : pkg.constantType entry.1 = none :=
    Option.isNone_iff_eq_none.mp (List.all_eq_true.mp fresh entry member)
  exact TowerSyntaxLimit.typed_free missing typed

theorem compiled_old {dev : Definitions.Development} (fresh : Definitions.devFresh dev = true)
    {definition : Vectors.Checker.Definition} {base : Nat} {compiled : Tower.Tm base}
    (checked : Definitions.Checked definition base compiled) : Definitions.OldTerm dev compiled :=
  typed_old fresh checked.guarantee.1

theorem compiled_call_typed_old {dev : Definitions.Development} (fresh : Definitions.devFresh dev = true)
    {definition : Vectors.Checker.Definition} {base : Nat} {compiled : Tower.Tm base}
    (checked : Definitions.Checked definition base compiled)
    {arguments : Sub Tower.Head definition.arity base}
    (typedArguments : SubstMor pkg definition.telescope (Definitions.baseCtx definition base) arguments) :
    Typed pkg (Definitions.baseCtx definition base) (applyClosed definition.telescope arguments compiled)
      (subst arguments definition.result) ∧
      Definitions.OldTerm dev (applyClosed definition.telescope arguments compiled) := by
  have typed := Definitions.call_typed checked typedArguments
  exact ⟨typed, typed_old fresh typed⟩

theorem old_root_step {dev : Definitions.Development} (checked : Definitions.devCheck dev = true)
    {rows : SchemaTable Tower.Head} (found : Definitions.devRules dev = some rows)
    {n : Nat} {term result : Tower.Tm n} (old : Definitions.OldTerm dev term)
    (step : (Definitions.devPackage dev rows).computation.step term result) : pkg.computation.step term result := by
  obtain ⟨rows', found', _, heads, _⟩ := Definitions.devCheck_parts checked
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  rcases step with impossible | step
  · exact impossible.elim
  · cases step with
    | instantiate member sigma =>
        rcases List.mem_append.mp member with base | new
        · exact Vectors.vector_sound level1 base sigma
        · obtain ⟨name, head, entry, included, rfl⟩ := heads _ new
          exact (Definitions.not_constFree_of_head sigma head (old entry included)).elim

private theorem old_reduction {dev : Definitions.Development} (checked : Definitions.devCheck dev = true)
    {rows : SchemaTable Tower.Head} (found : Definitions.devRules dev = some rows)
    {n : Nat} {term result : Tower.Tm n}
    (step : StrongNormalization.Reduces (Definitions.devPackage dev rows) term result) :
    Definitions.OldTerm dev term → StrongNormalization.Reduces pkg term result := by
  induction step with
  | betaPi body argument => exact fun _ => .betaPi body argument
  | betaSigmaFst first second => exact fun _ => .betaSigmaFst first second
  | betaSigmaSnd first second => exact fun _ => .betaSigmaSnd first second
  | head impossible => cases impossible
  | root computed => exact fun old => .root (old_root_step checked found old computed)
  | congPiDom _ ih => exact fun old => .congPiDom (ih fun entry member => (old entry member).1)
  | congPiCod _ ih => exact fun old => .congPiCod (ih fun entry member => (old entry member).2)
  | congSigmaDom _ ih => exact fun old => .congSigmaDom (ih fun entry member => (old entry member).1)
  | congSigmaCod _ ih => exact fun old => .congSigmaCod (ih fun entry member => (old entry member).2)
  | congIdTy _ ih => exact fun old => .congIdTy (ih fun entry member => (old entry member).1)
  | congIdLeft _ ih => exact fun old => .congIdLeft (ih fun entry member => (old entry member).2.1)
  | congIdRight _ ih => exact fun old => .congIdRight (ih fun entry member => (old entry member).2.2)
  | congLam _ ih => exact fun old => .congLam (ih fun entry member => old entry member)
  | congAppFun _ ih => exact fun old => .congAppFun (ih fun entry member => (old entry member).1)
  | congAppArg _ ih => exact fun old => .congAppArg (ih fun entry member => (old entry member).2)
  | congPairFst _ ih => exact fun old => .congPairFst (ih fun entry member => (old entry member).1)
  | congPairSnd _ ih => exact fun old => .congPairSnd (ih fun entry member => (old entry member).2)
  | congFst _ ih => exact fun old => .congFst (ih fun entry member => old entry member)
  | congSnd _ ih => exact fun old => .congSnd (ih fun entry member => old entry member)
  | congRefl _ ih => exact fun old => .congRefl (ih fun entry member => old entry member)

theorem old_directed_step {dev : Definitions.Development} (checked : Definitions.devCheck dev = true)
    {rows : SchemaTable Tower.Head} (found : Definitions.devRules dev = some rows)
    {n : Nat} {term result : Tower.Tm n} (old : Definitions.OldTerm dev term)
    (step : StrongNormalization.Reduces (Definitions.devPackage dev rows) term result) :
    StrongNormalization.Reduces pkg term result ∧ Definitions.OldTerm dev result :=
  ⟨old_reduction checked found step old,
    (Definitions.dev_step_old checked found (DirectedAnswers.step_of_reduces step) old).2⟩

theorem old_directed_steps {dev : Definitions.Development} (checked : Definitions.devCheck dev = true)
    {rows : SchemaTable Tower.Head} (found : Definitions.devRules dev = some rows)
    {n : Nat} {term result : Tower.Tm n} (old : Definitions.OldTerm dev term)
    (steps : StrongNormalization.ReducesStar (Definitions.devPackage dev rows) term result) :
    StrongNormalization.ReducesStar pkg term result ∧ Definitions.OldTerm dev result := by
  induction steps with
  | refl => exact ⟨.refl, old⟩
  | tail _ step ih =>
      obtain ⟨base, priorOld⟩ := ih
      obtain ⟨baseStep, resultOld⟩ := old_directed_step checked found priorOld step
      exact ⟨base.tail baseStep, resultOld⟩

theorem old_directedAnswer_iff {dev : Definitions.Development} (checked : Definitions.devCheck dev = true)
    {rows : SchemaTable Tower.Head} (found : Definitions.devRules dev = some rows)
    {n : Nat} {term result : Tower.Tm n} (old : Definitions.OldTerm dev term) :
    DirectedAnswers.DirectedAnswer (Definitions.devPackage dev rows) term result ↔
      DirectedAnswers.DirectedAnswer pkg term result := by
  constructor
  · intro answer
    obtain ⟨steps, _⟩ := old_directed_steps checked found old answer.1
    exact ⟨steps, fun target step => answer.2 target
      (Definitions.stepCore_mono (fun edge => Definitions.pkg_step_dev dev rows edge) step)⟩
  · intro answer
    have steps := Definitions.reducesStar_dev dev rows answer.1
    have resultOld := (old_directed_steps checked found old steps).2
    exact ⟨steps, fun target step => answer.2 target (old_directed_step checked found resultOld step).1⟩

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (N : Hosting.Nodes MSig [] ()) (supply : Nat → MClosed)

include supply in
theorem compiled_public_iff_checked_native (checkedDev : Definitions.devCheck dev = true)
    (fresh : Definitions.devFresh dev = true)
    {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Definitions.Checked definition 0 compiled)
    {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) (result : Tower.Tm 0) :
    NormalTypedExecution.Answer built D N (applyClosed definition.telescope arguments compiled) result ↔
      CheckedCalls.NativeAnswer checked typedArguments result := by
  have old := (compiled_call_typed_old fresh checked typedArguments).2
  exact (NormalTypedExecution.answer_iff built D N supply _ _).trans
    ((old_directedAnswer_iff checkedDev built.native old).trans
      (CheckedCalls.compiled_answer_iff_native checked typedArguments result))

include supply in
theorem compiled_public_answer_typed (checkedDev : Definitions.devCheck dev = true)
    (fresh : Definitions.devFresh dev = true)
    {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Definitions.Checked definition 0 compiled)
    {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) {result : Tower.Tm 0}
    (answered : NormalTypedExecution.Answer built D N (applyClosed definition.telescope arguments compiled) result) :
    Typed pkg .nil result (subst arguments definition.result) ∧
      Typed (Definitions.devPackage dev built.nativeRows) .nil result (subst arguments definition.result) ∧
      Equal (Definitions.devPackage dev built.nativeRows) .nil
        (applyClosed definition.telescope arguments compiled) result (subst arguments definition.result) := by
  have nativeAnswer := (compiled_public_iff_checked_native built D N supply checkedDev fresh checked typedArguments result).mp answered
  have typed := CheckedCalls.native_answer_keeps_type checked typedArguments nativeAnswer
  have initial := compiled_call_typed_old fresh checked typedArguments
  have preservation := NormalTypedExecution.old_answer_typed built D N supply checkedDev fresh initial.2 initial.1 answered
  exact ⟨typed, preservation⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictTypedCalls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictTypedCalls.old_directedAnswer_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.VerdictTypedCalls.compiled_public_answer_typed
