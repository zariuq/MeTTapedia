import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperationalBeta
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasBodies
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredPresentationControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.PublicOutputObservation

/-!
# Whole native operational receipts and binding controls

The supplied two-coordinate function becomes an actual scope and binary COMM
firing, with its argument and return kept distinct. Clone substitution can
identify the two names while retaining the whole event. Unary fetch likewise
retains its supplied function and original authored metadata. Two unused
metavariable supplies distinguish real receipts with identical endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperational.Controls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf
open IntrinsicScopedLocalPolynomial
open NamePassingCategoricalCompiler NamePassingBindingClosedSchemas

attribute [local irreducible] BindingEquationQuotientModel.operation
attribute [local irreducible] NamePassingContinuationOperations.Operations.abstraction
  NamePassingContinuationOperations.Operations.application

abbrev context : Ctx sig := [.nm,.nm]
abbrev world : Base := stage context

def argument : operations.names.obj world := rawPoint (.var .zero : Name context)
def result : operations.names.obj world := rawPoint (.var (.succ .zero) : Name context)

def function : operations.boundBodyObject.obj world :=
  rawSchemaBody (out1 (.var (.succ .zero)) (.var .zero) : Proc (.nm :: .nm :: context))

def firing : events.obj world := betaReaction.app world ((function,argument),result)

def expected : operations.processes.obj world :=
  rawPoint (out1 (.var .zero) (.var (.succ .zero)) : Proc context)

theorem beta_source_is_independent_continuation :
    source.app world firing =
      (betaSource.app world (function,argument)).app world (𝟙 world) result :=
  beta_source_current world (function,argument) result

theorem beta_complete_target : target.app world firing = expected := by
  unfold firing
  rw [beta_target_current]
  apply (programsAtEquiv algebra .pr world).injective
  change programsAtEquiv algebra .pr world
    (((function.app world (𝟙 world)) argument).app world (𝟙 world) result) =
      programsAtEquiv algebra .pr world expected
  have calculated := rawSchemaBody_call
    (out1 (.var (.succ .zero)) (.var .zero) : Proc (.nm :: .nm :: context))
    (.var .zero : Name context) (.var (.succ .zero) : Name context)
  change programsAtEquiv algebra .pr world
    (((function.app world (𝟙 world)) argument).app world (𝟙 world) result) =
      (Quotient.mk _ (out1 (.var .zero) (.var (.succ .zero)) : Proc context) :
        TermQ equations context .pr) at calculated
  exact calculated.trans (rawPoint_readout _).symm

theorem beta_is_actual_runtime :
    StepModulo (Quotient.out (programsAtEquiv algebra .pr world (source.app world firing)))
      (Quotient.out (programsAtEquiv algebra .pr world expected)) := by
  have actual := CategoricalOperational.runtime world firing
  rw [← CategoricalOperational.source_readout, ← CategoricalOperational.target_readout,
    beta_complete_target] at actual
  exact actual

def exchanged : operations.processes.obj world :=
  rawPoint (out1 (.var (.succ .zero)) (.var .zero) : Proc context)

theorem exchanged_bound_coordinates_change_target : expected ≠ exchanged := by
  intro same
  have classes := congrArg (programsAtEquiv algebra .pr world) same
  change programsAtEquiv algebra .pr world (rawPoint
    (out1 (.var .zero) (.var (.succ .zero)) : Proc context)) =
      programsAtEquiv algebra .pr world (rawPoint
        (out1 (.var (.succ .zero)) (.var .zero) : Proc context)) at classes
  rw [rawPoint_readout,rawPoint_readout] at classes
  have equation := (AuthoredEquations.eqClosure_iff_structuralEq _ _).mp (Quotient.exact classes)
  have offered : PublicOutputObservation.HasOutput (.zero : Var context .nm)
      (out1 (.var .zero) (.var (.succ .zero)) : Proc context) :=
    PublicOutputObservation.output_observed _ _
  have received := (PublicOutputObservation.structural_congr .zero equation).mp offered
  have active := (PublicOutputObservation.hasOutput_iff_active _ _).mp received
  cases active

def identify : Sub sig context context
  | _, .zero => .var (.succ .zero)
  | _, .succ .zero => .var (.succ .zero)

theorem identified_whole_firing :
    events.map (rawChange identify) firing =
      betaReaction.app world
        (((operations.boundBodyObject.map (rawChange identify) function,
          operations.names.map (rawChange identify) argument)),
          operations.names.map (rawChange identify) result) :=
  betaReaction_substitution (rawChange identify) ((function,argument),result)

theorem identified_complete_target :
    target.app world (events.map (rawChange identify) firing) =
      rawPoint (out1 (.var (.succ .zero)) (.var (.succ .zero)) : Proc context) := by
  rw [CategoricalOperational.target_substitution,beta_complete_target,
    expected,rawPoint_substitution]
  rfl

def capturedFunction : operations.boundBodyObject.obj world :=
  rawSchemaBody
    (out1 (.var (.succ (.succ .zero))) (.var .zero) : Proc (.nm :: .nm :: context))

def swap : Sub sig context context
  | _, .zero => .var (.succ .zero)
  | _, .succ .zero => .var .zero

/-- The full future function changes its captured ambient coordinate while
the received argument and return remain separate bound positions. -/
theorem captured_future_target :
    target.app world
      (((beta.app world (capturedFunction,result)).app world (rawChange swap)) argument) =
      rawPoint (out1 (.var (.succ .zero)) (.var .zero) : Proc context) := by
  rw [beta_future,beta_target_current]
  apply (programsAtEquiv algebra .pr world).injective
  change programsAtEquiv algebra .pr world
    ((((operations.boundBodyObject.map (rawChange swap) capturedFunction).app world (𝟙 world))
      (operations.names.map (rawChange swap) result)).app world (𝟙 world) argument) = _
  unfold capturedFunction result argument
  rw [rawSchemaBody_substitution,rawPoint_substitution]
  have calculated := rawSchemaBody_call
    (out1 (.var (.succ (.succ (.succ .zero)))) (.var .zero) : Proc (.nm :: .nm :: context))
    (.var .zero : Name context) (.var .zero : Name context)
  change programsAtEquiv algebra .pr world
    (((rawSchemaBody
      (out1 (.var (.succ (.succ (.succ .zero)))) (.var .zero) : Proc (.nm :: .nm :: context))).app
      world (𝟙 world) (rawPoint (.var .zero : Name context))).app world (𝟙 world)
        (rawPoint (.var .zero : Name context))) =
      (Quotient.mk _ (out1 (.var (.succ .zero)) (.var .zero) : Proc context) :
        TermQ equations context .pr) at calculated
  exact calculated.trans (rawPoint_readout _).symm

def stored : operations.termObject.obj world :=
  rawBody (out1 (.var (.succ .zero)) (.var .zero) : Proc (.nm :: context))

def fetchReceipt : events.obj world := fetchFiring.app world ((argument,stored),result)

theorem fetch_complete_target : target.app world fetchReceipt = expected := by
  unfold fetchReceipt
  rw [fetchFiring_target]
  apply (programsAtEquiv algebra .pr world).injective
  have calculated := rawBody_evaluation
    (out1 (.var (.succ .zero)) (.var .zero) : Proc (.nm :: context))
    (.var (.succ .zero) : Name context)
  change programsAtEquiv algebra .pr world (stored.app world (𝟙 world) result) =
    (Quotient.mk _ (out1 (.var .zero) (.var (.succ .zero)) : Proc context) :
      TermQ equations context .pr) at calculated
  exact calculated.trans (rawPoint_readout _).symm

theorem fetch_is_actual_runtime :
    StepModulo (Quotient.out (programsAtEquiv algebra .pr world (source.app world fetchReceipt)))
      (Quotient.out (programsAtEquiv algebra .pr world expected)) := by
  have actual := CategoricalOperational.runtime world fetchReceipt
  rw [← CategoricalOperational.source_readout, ← CategoricalOperational.target_readout,
    fetch_complete_target] at actual
  exact actual

/-- The actual top-layer occurrence includes its entire authored supply. -/
def origin (atWorld : Base) (event : events.obj atWorld) :
    Instance AuthoredOperationalProfile.rules algebra :=
  ((Mettapedia.TypeTheory.IndexedPolynomial.Fix.out
    (IntrinsicScopedLocalPolynomial.rules AuthoredOperationalProfile.rules algebra)
    (CategoricalOperational.atEquiv atWorld event).2).1).1

theorem beta_retains_private_scope_occurrence : (origin world firing).index.val = 4 := rfl

theorem beta_retains_binary_child :
    (origin world (betaChild.app world (((function,argument),result),argument))).index.val = 1 := rfl

theorem fetch_retains_unary_occurrence : (origin world fetchReceipt).index.val = 0 := rfl

def unusedEmpty : algebra.substitution.Carrier (.nm :: .nm :: context) .pr :=
  Quotient.mk _ (nil : Proc (.nm :: .nm :: context))

def unusedOffer : algebra.substitution.Carrier (.nm :: .nm :: context) .pr :=
  Quotient.mk _ (out1 (.var .zero) (.var .zero) : Proc (.nm :: .nm :: context))

theorem unused_supplies_distinct : unusedEmpty ≠ unusedOffer := by
  intro same
  have equation := (AuthoredEquations.eqClosure_iff_structuralEq _ _).mp (Quotient.exact same)
  have indicator := AuthoredPresentationControls.activeOutput_structural equation
  simp only [nil,out1,AuthoredPresentationControls.activeOutput] at indicator
  cases indicator

def alternativeOccurrence (unused : algebra.substitution.Carrier (.nm :: .nm :: context) .pr) :
    Instance AuthoredOperationalProfile.rules algebra where
  index := ⟨0,by decide⟩
  ambient := context
  valuation
    | ⟨0,_⟩ => CategoricalOperations.unaryBody algebra world stored
    | ⟨1,_⟩ => unused
    | ⟨n+2,impossible⟩ => by change n+2 < 2 at impossible; omega
  close
    | _, .zero => programsAtEquiv algebra .nm world argument
    | _, .succ .zero => programsAtEquiv algebra .nm world result

def alternativeReceipt (unused : algebra.substitution.Carrier (.nm :: .nm :: context) .pr) :
    events.obj world :=
  ⟨⟨Srt.pr,
    (conclusionJudgment AuthoredOperationalProfile.rules algebra
      (alternativeOccurrence unused)).2.2,
    Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
      ⟨alternativeOccurrence unused,rfl⟩ (fun position => nomatch position)⟩,rfl⟩

theorem unused_metadata_does_not_change_endpoints :
    source.app world (alternativeReceipt unusedEmpty) =
      source.app world (alternativeReceipt unusedOffer) ∧
    target.app world (alternativeReceipt unusedEmpty) =
      target.app world (alternativeReceipt unusedOffer) := ⟨rfl,rfl⟩

private theorem valuation_heq
    {first second : Instance AuthoredOperationalProfile.rules algebra} (same : first = second) :
    HEq first.valuation second.valuation := by cases same; rfl

theorem unused_metadata_remains_in_complete_receipt :
    alternativeReceipt unusedEmpty ≠ alternativeReceipt unusedOffer := by
  intro same
  have roots := congrArg (origin world) same
  have supplies := valuation_heq roots
  change HEq (alternativeOccurrence unusedEmpty).valuation
    (alternativeOccurrence unusedOffer).valuation at supplies
  have point := congrFun (eq_of_heq supplies) (⟨1,by decide⟩ : Fin 2)
  exact unused_supplies_distinct point

theorem no_endpoint_receipt_decoder :
    ¬ ∃ decode : operations.processes.obj world × operations.processes.obj world → events.obj world,
      ∀ supplied, decode (source.app world supplied,target.app world supplied) = supplied := by
  rintro ⟨decode,correct⟩
  have pairs :
      (source.app world (alternativeReceipt unusedEmpty),
        target.app world (alternativeReceipt unusedEmpty)) =
      (source.app world (alternativeReceipt unusedOffer),
        target.app world (alternativeReceipt unusedOffer)) :=
    Prod.ext unused_metadata_does_not_change_endpoints.1
      unused_metadata_does_not_change_endpoints.2
  exact unused_metadata_remains_in_complete_receipt
    ((correct _).symm.trans ((congrArg decode pairs).trans (correct _)))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperational.Controls
