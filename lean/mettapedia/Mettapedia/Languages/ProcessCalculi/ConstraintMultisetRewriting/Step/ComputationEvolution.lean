import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationCompleteness

/-!
# Scoped licenses for extending computation rules

Rule inclusion retains old finite computations. Retaining a completed answer
additionally needs normality to survive: no newly enabled root may occur in
the result, and head equality may not introduce a new step there. A syntactic
constant-support condition derives that root obligation for fresh-name rules.
The new package's qualification remains a separate required certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationEvolution

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open AlgebraicParallel NativeTypesOnTheStep.Computing ConversionCoherence
open ComputationSyntax

variable {Head : Type} {old next : Rules Head}

theorem step_mono (inclusion : RulesSub old next) {n : Nat} {before after : Tm Head n}
    (reduction : StepCore old.computation old.headEq before after) :
    StepCore next.computation next.headEq before after := by
  induction reduction with
  | betaPi body argument => exact .betaPi body argument
  | betaSigmaFst left right => exact .betaSigmaFst left right
  | betaSigmaSnd left right => exact .betaSigmaSnd left right
  | head same => exact .head (inclusion.headEq same)
  | root source => exact .root (inclusion.computation source)
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

theorem steps_mono (inclusion : RulesSub old next) {n : Nat} {before after : Tm Head n}
    (steps : StepStar old before after) : StepStar next before after := by
  induction steps with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (step_mono inclusion last)

def RootAgreementAt {n : Nat} (term : Tm Head n) : Prop :=
  ∀ m (context : Context Head n m) (redex : Tm Head m), context.plug redex = term →
    ∀ target, next.computation.step redex target → old.computation.step redex target

theorem step_reflects_at (presentation : SchemaPresentation next)
    (heads : ∀ {left right}, next.headEq left right → old.headEq left right)
    {n : Nat} {term target : Tm Head n} (roots : RootAgreementAt (old := old) (next := next) term)
    (reduction : StepCore next.computation next.headEq term target) :
    StepCore old.computation old.headEq term target := by
  obtain ⟨event, source, endpoint⟩ := ComputationSyntax.complete presentation reduction
  rcases event with ⟨arity, context, action⟩
  change context.plug action.source = term at source
  change context.plug action.target = target at endpoint
  have root : StepCore old.computation old.headEq action.source action.target := by
    cases action with
    | beta body argument => exact .betaPi body argument
    | first left right => exact .betaSigmaFst left right
    | second left right => exact .betaSigmaSnd left right
    | head left right same => exact .head (heads same)
    | declared left right selected arguments =>
        exact .root (roots _ context _ source _ (presentation.sound selected arguments))
  have whole := context.step root
  rwa [source, endpoint] at whole

theorem normal_preserved (presentation : SchemaPresentation next)
    (heads : ∀ {left right}, next.headEq left right → old.headEq left right)
    {n : Nat} {term : Tm Head n} (roots : RootAgreementAt (old := old) (next := next) term)
    (normal : ConstructorSystem.Normal old term) : ConstructorSystem.Normal next term := by
  intro target reduction
  exact normal (step_reflects_at presentation heads roots reduction)

theorem answer_preserved (inclusion : RulesSub old next) (presentation : SchemaPresentation next)
    (heads : ∀ {left right}, next.headEq left right → old.headEq left right)
    {n : Nat} {term value : Tm Head n} (roots : RootAgreementAt (old := old) (next := next) value)
    (answer : Answer old term value) : Answer next term value :=
  ⟨steps_mono inclusion answer.1, normal_preserved presentation heads roots answer.2⟩

def Uses (name : DeclName) : {n : Nat} → Tm Head n → Prop
  | _, .var _ | _, .head _ => False
  | _, .const other => name = other
  | _, .pi first second | _, .sigma first second => Uses name first ∨ Uses name second
  | _, .id type left right => Uses name type ∨ Uses name left ∨ Uses name right
  | _, .lam body => Uses name body
  | _, .app first second | _, .pair first second => Uses name first ∨ Uses name second
  | _, .fst inner | _, .snd inner | _, .refl inner => Uses name inner

theorem Context.plug_uses {n m : Nat} (context : Context Head n m) (name : DeclName) (term : Tm Head m)
    (uses : Uses name term) : Uses name (context.plug term) := by
  induction context with
  | hole => exact uses
  | piDom _ _ ih | sigmaDom _ _ ih | appFun _ _ ih | pairFst _ _ ih => exact Or.inl (ih term uses)
  | piCod _ _ ih | sigmaCod _ _ ih | appArg _ _ ih | pairSnd _ _ ih => exact Or.inr (ih term uses)
  | idType _ _ _ ih => exact Or.inl (ih term uses)
  | idLeft _ _ _ ih => exact Or.inr (Or.inl (ih term uses))
  | idRight _ _ _ ih => exact Or.inr (Or.inr (ih term uses))
  | lam _ ih | fst _ ih | snd _ ih | refl _ ih => exact ih term uses

theorem fresh_name_license (name : DeclName)
    (newRules : ∀ {m : Nat} {left right : Tm Head m}, next.computation.step left right →
      old.computation.step left right ∨ Uses name left)
    {n : Nat} {term : Tm Head n} (missing : ¬ Uses name term) :
    RootAgreementAt (old := old) (next := next) term := by
  intro m context redex same target reduction
  rcases newRules reduction with oldRule | contains
  · exact oldRule
  · exact False.elim (missing (same ▸ Context.plug_uses context name redex contains))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationEvolution

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationEvolution.answer_preserved
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationEvolution.fresh_name_license
