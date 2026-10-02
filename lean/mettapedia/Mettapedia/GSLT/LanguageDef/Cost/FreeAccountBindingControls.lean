import Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction
import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingEquationBoundary

/-!
# Concrete controls for the relative free binding account construction

The lambda control retains an account at one occurrence of the same bound
variable and separates substitution through a marked environment from an
erased-environment clause.  The rho control retains a send beneath an input
binder and its original equation-class observation.  The marker target used
here distinguishes local occurrences and multiplicity, not account labels.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open FreeBindingTerms
open RawAccountBindingExtension
open RawAccountBindingLaws
open AccountBindingQuotientSubstitution
open FreeAccountBindingModel
open FreeAccountBindingExtension
open AccountBindingAlgebra

namespace Lambda

open LambdaContextualRung LambdaBindingComparison

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

abbrev base : Over source := Over.mk (𝟙 source)

/-- The actual marked lambda clone receives all original lambda syntax. -/
noncomputable def incoming : base ⟶ LambdaBindingComparison.model.observed :=
  Over.homMk (FreeBindingClone.interpretHom LambdaBindingComparison.model.observed.left) (by
    exact (FreeBindingClone.hom_unique source _).trans
      (FreeBindingClone.hom_unique source (𝟙 source)).symm)

def word : SourceAccountSubstitution.Account source Srt.term [Srt.term] :=
  FreeMonoid.of (.var .zero)

/-- The two bound-variable occurrences receive independently supplied raw
values.  Only the first occurrence is accounted. -/
def rawSelfApplication : Raw source Srt.term base [] Srt.term :=
  .operation .lam (.cons
    (.operation .app (.cons (.account word (sourceVariable source Srt.term base .zero))
      (.cons (sourceVariable source Srt.term base .zero) .nil))) .nil)

def accountedSelfApplication : Carrier source Srt.term base [] Srt.term :=
  project source Srt.term base rawSelfApplication

theorem self_application_source :
    observation source Srt.term base accountedSelfApplication = selfApplication := rfl

theorem self_application_extension :
    (extend source Srt.term base LambdaBindingComparison.model incoming).underlying.left.raw.map
      accountedSelfApplication = markedSelfApplication := rfl

/-- The accounted quotient retains this inside-binder occurrence distinction,
as witnessed by a genuine independently specified target clone. -/
theorem self_application_nontrivial :
    accountedSelfApplication ≠ project source Srt.term base (.gen selfApplication) := by
  intro equal
  have mapped := congrArg
    (extend source Srt.term base LambdaBindingComparison.model incoming).underlying.left.raw.map equal
  exact marked_self_application_keeps_occurrence mapped

/-- Genuine local action in the free quotient is nontrivial, as detected by
the independently specified marker model. -/
theorem action_nontrivial : act source Srt.term base word
    (project source Srt.term base (.gen (.var .zero))) ≠
      project source Srt.term base (.gen (.var .zero)) := by
  intro equal
  have mapped := congrArg
    (extend source Srt.term base LambdaBindingComparison.model incoming).underlying.left.raw.map equal
  exact LambdaBindingComparison.action_nontrivial mapped

theorem multiplication_noninjective : ¬ Function.Injective
    (((FreeAccountBindingAdjunction.accountMonad source Srt.term).μ.app base).left.raw.map
      (Γ := [Srt.term]) (s := Srt.term)) :=
  FreeAccountBindingAdjunction.multiplication_not_injective source Srt.term base word
    (project source Srt.term base (.gen (.var .zero))) action_nontrivial

/-- The inside-binder account cannot be supplied merely as one account
outside a pure source generator, even if arbitrary words are allowed there. -/
theorem inside_binder_not_root_action
    (outer : SourceAccountSubstitution.Account source Srt.term [])
    (value : source.substitution.Carrier [] Srt.term) :
    accountedSelfApplication ≠ act source Srt.term base outer
      (project source Srt.term base (.gen value)) := by
  intro equal
  have observed := congrArg (observation source Srt.term base) equal
  have sourceSame : selfApplication = value := observed.trans
    (observation_act source Srt.term base outer (project source Srt.term base (.gen value)))
  subst value
  have mapped := congrArg
    (extend source Srt.term base LambdaBindingComparison.model incoming).underlying.left.raw.map equal
  change markedSelfApplication = (OccurrenceMarker.markAt (S := sig) Srt.term)^[outer.length]
    (embed (M := (OccurrenceMarker.context (S := sig) Srt.term).arities) selfApplication) at mapped
  cases lengthEq : outer.length with
  | zero =>
      rw [lengthEq] at mapped
      exact marked_self_application_keeps_occurrence mapped
  | succ count =>
      rw [lengthEq, Function.iterate_succ_apply'] at mapped
      simp only [OccurrenceMarker.markAt] at mapped
      cases mapped

def markedEnvironment : Environment sig (Raw source Srt.term base) [Srt.term] [Srt.term] :=
  fun _ v => match v with
    | .zero => .account word (sourceVariable source Srt.term base .zero)
    | .succ impossible => nomatch impossible

def retainedVariableSubstitution : Raw source Srt.term base [Srt.term] Srt.term :=
  .substitute markedEnvironment (sourceVariable source Srt.term base .zero)

def erasedVariableSubstitution : Raw source Srt.term base [Srt.term] Srt.term :=
  .gen (source.substitution.substitute
    (fun sort v => observe source Srt.term base (markedEnvironment sort v))
    (source.substitution.injectVar .zero))

/-- Actual substitution returns the marked supplied value, whereas
substituting only its source observation loses that account. -/
theorem full_environment_is_essential :
    project source Srt.term base retainedVariableSubstitution ≠
      project source Srt.term base erasedVariableSubstitution := by
  intro equal
  have mapped := congrArg
    (extend source Srt.term base LambdaBindingComparison.model incoming).underlying.left.raw.map equal
  change OccurrenceMarker.mark (S := sig) Srt.term (Γ := [Srt.term]) (.var .zero) =
    (.var .zero : Term (withMetas sig (OccurrenceMarker.context (S := sig) Srt.term).arities)
      [Srt.term] Srt.term) at mapped
  cases mapped

end Lambda

namespace Rho

open RhoSchema RhoSourceComparison AccountBindingEquationBoundary

noncomputable def base : Over source :=
  Over.mk (FreeBindingClone.interpretHom source)

/-- The incoming arrow is from full raw rho terms; it does not assert an
incoming map from the equation quotient into literal marker syntax. -/
noncomputable def incoming : base ⟶
    (AccountBindingAlgebra.forget source Srt.pr).obj RhoSourceComparison.model :=
  Over.homMk rawMarkerIncoming (by exact FreeBindingClone.hom_unique source _)

/-- One account is local to the send body beneath the actual input binder. -/
noncomputable def rawMarkedInput : Raw source Srt.pr base [] Srt.pr :=
  .operation .inp (.cons (.gen quotedZero)
    (.cons (.account (FreeMonoid.of ((FreeBindingClone.interpretHom source).raw.map sendBody))
      (.gen sendBody)) .nil))

noncomputable def accountedInput : Carrier source Srt.pr base [] Srt.pr :=
  project source Srt.pr base rawMarkedInput

theorem input_source : observation source Srt.pr base accountedInput =
    (Quotient.mk _ RhoSourceComparison.input : TermQ rhoSourceE [] Srt.pr) := by
  change BindingCloneFoldSubstitution.interpret source RhoSourceComparison.input = _
  exact BindingEquationQuotientModel.interpret_eq_mk rhoSourceE RhoSourceComparison.input

theorem input_extension :
    (extend source Srt.pr base RhoSourceComparison.model incoming).underlying.left.raw.map
      accountedInput = markedInput := rfl

theorem input_nontrivial :
    accountedInput ≠ project source Srt.pr base (.gen RhoSourceComparison.input) := by
  intro equal
  have mapped := congrArg
    (extend source Srt.pr base RhoSourceComparison.model incoming).underlying.left.raw.map equal
  change markedInput = embed (M := (OccurrenceMarker.context (S := sig) Srt.pr).arities)
    RhoSourceComparison.input at mapped
  cases mapped

end Rho

#print axioms Lambda.self_application_nontrivial
#print axioms Lambda.full_environment_is_essential
#print axioms Lambda.multiplication_noninjective
#print axioms Lambda.inside_binder_not_root_action
#print axioms Rho.input_source
#print axioms Rho.input_nontrivial

end Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls
