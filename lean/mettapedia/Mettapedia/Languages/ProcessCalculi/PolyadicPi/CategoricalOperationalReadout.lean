import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalCommunication

/-!
# Whole-function endpoints of the retained COMM arrows

The source is the independently formed output/input parallel process.
The target opens every supplied receiver position in the actual complete
function section. These equalities compare the authored rule interpretation
with categorical evaluation, rather than defining endpoints by evaluation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperational

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra SemanticContextualMetavariables
open BindingEquationalModels (argsEnvironment)
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open IntrinsicScopedLocalPolynomial

private abbrev rules := AuthoredOperationalProfile.rules

attribute [local irreducible] BindingEquationQuotientModel.operation

private theorem weaken_empty (A : BindingCloneAlgebra.Algebra sig)
    {context destination : Ctx sig}
    (environment : Environment sig A.substitution.Carrier context destination) :
    weakenEnvironment A [] environment = environment := by
  funext sort position
  exact A.substitution.substitute_identity (environment sort position)

private theorem unaryIdentity (A : BindingCloneAlgebra.Algebra sig) (context : Ctx sig) :
    joinEnvironment
      (argsEnvironment A (bs := [Srt.nm]) (Γ := Srt.nm :: context)
        (.cons (A.substitution.injectVar (.zero : Var (.nm :: context) .nm)) .nil))
      (weakenEnvironment A [.nm]
        (fun _ position => A.substitution.injectVar position :
          Environment sig A.substitution.Carrier context context)) =
      (fun _ position => A.substitution.injectVar position) := by
  funext sort position
  cases position with
  | zero => rfl
  | succ old => exact A.substitution.substitute_var _ old

private theorem binaryIdentity (A : BindingCloneAlgebra.Algebra sig) (context : Ctx sig) :
    joinEnvironment
      (argsEnvironment A (bs := [Srt.nm, Srt.nm]) (Γ := Srt.nm :: Srt.nm :: context)
        (.cons (A.substitution.injectVar (.zero : Var (.nm :: .nm :: context) .nm))
          (.cons (A.substitution.injectVar (.succ .zero : Var (.nm :: .nm :: context) .nm)) .nil)))
      (weakenEnvironment A [.nm, .nm]
        (fun _ position => A.substitution.injectVar position :
          Environment sig A.substitution.Carrier context context)) =
      (fun _ position => A.substitution.injectVar position) := by
  funext sort position
  cases position with
  | zero => rfl
  | succ position => cases position with
    | zero => rfl
    | succ old => exact A.substitution.substitute_var _ old

private theorem unarySchema_source (A : BindingCloneAlgebra.Algebra sig)
    (context : Ctx sig) (valuation : Valuation (M := metas) A context)
    (close : Environment sig A.substitution.Carrier [Srt.nm, Srt.nm] context) :
    interpretSchema A valuation (fun _ position => A.substitution.injectVar position)
      close comm1.lhs =
      A.operation Op.par
        (.cons (A.operation Op.out1 (.cons (close _ .zero) (.cons (close _ (.succ .zero)) .nil)))
          (.cons (A.operation Op.inp1 (.cons (close _ .zero) (.cons (valuation 0) .nil))) .nil)) := by
  simp only [comm1, unaryContinuation, interpretSchema, interpretArgs,
    BindingSubstitutionAlgebra.Algebra.liftEnvironment,
    SemanticContextualMetavariables.apply]
  rw [weaken_empty]
  change A.operation Op.par (.cons _ (.cons (A.operation Op.inp1 (.cons _ (.cons
    (A.substitution.substitute
      (joinEnvironment
        (argsEnvironment A (bs := [Srt.nm]) (Γ := Srt.nm :: context)
          (.cons (A.substitution.injectVar .zero) .nil))
        (weakenEnvironment A [.nm] (fun _ position => A.substitution.injectVar position)))
      (valuation 0)) .nil))) .nil)) = _
  rw [unaryIdentity, A.substitution.substitute_identity]

private theorem binarySchema_source (A : BindingCloneAlgebra.Algebra sig)
    (context : Ctx sig) (valuation : Valuation (M := metas) A context)
    (close : Environment sig A.substitution.Carrier [Srt.nm, Srt.nm, Srt.nm] context) :
    interpretSchema A valuation (fun _ position => A.substitution.injectVar position)
      close comm2.lhs =
      A.operation Op.par
        (.cons (A.operation Op.out2 (.cons (close _ .zero) (.cons (close _ (.succ .zero))
          (.cons (close _ (.succ (.succ .zero))) .nil))))
          (.cons (A.operation Op.inp2 (.cons (close _ .zero) (.cons (valuation 1) .nil))) .nil)) := by
  simp only [comm2, binaryContinuation, interpretSchema, interpretArgs,
    BindingSubstitutionAlgebra.Algebra.liftEnvironment,
    BindingSubstitutionAlgebra.Algebra.weaken, A.substitution.substitute_var,
    SemanticContextualMetavariables.apply]
  rw [weaken_empty]
  change A.operation Op.par (.cons _ (.cons (A.operation Op.inp2 (.cons _ (.cons
    (A.substitution.substitute
      (joinEnvironment
        (argsEnvironment A (bs := [Srt.nm, Srt.nm]) (Γ := Srt.nm :: Srt.nm :: context)
          (.cons (A.substitution.injectVar .zero)
            (.cons (A.substitution.injectVar (.succ .zero)) .nil)))
        (weakenEnvironment A [.nm, .nm] (fun _ position => A.substitution.injectVar position)))
      (valuation 1)) .nil))) .nil)) = _
  rw [binaryIdentity, A.substitution.substitute_identity]

theorem unary_identity (context : Ctx sig) :
    joinEnvironment
      (argsEnvironment algebra (bs := [Srt.nm]) (Γ := Srt.nm :: context)
        (.cons (algebra.substitution.injectVar (.zero : Var (.nm :: context) .nm)) .nil))
      (weakenEnvironment algebra [.nm]
        (fun _ position => algebra.substitution.injectVar position :
          Environment sig algebra.substitution.Carrier context context)) =
      (fun _ position => algebra.substitution.injectVar position) := by
  funext sort position
  cases position with
  | zero => rfl
  | succ old =>
      exact algebra.substitution.substitute_var _ old

theorem binary_identity (context : Ctx sig) :
    joinEnvironment
      (argsEnvironment algebra (bs := [Srt.nm, Srt.nm]) (Γ := Srt.nm :: Srt.nm :: context)
        (.cons (algebra.substitution.injectVar (.zero : Var (.nm :: .nm :: context) .nm))
          (.cons (algebra.substitution.injectVar (.succ .zero : Var (.nm :: .nm :: context) .nm)) .nil)))
      (weakenEnvironment algebra [.nm, .nm]
        (fun _ position => algebra.substitution.injectVar position :
          Environment sig algebra.substitution.Carrier context context)) =
      (fun _ position => algebra.substitution.injectVar position) := by
  funext sort position
  cases position with
  | zero => rfl
  | succ position => cases position with
    | zero => rfl
    | succ old => exact algebra.substitution.substitute_var _ old

theorem unary_source_body (world : Base) (channel datum : names.obj world)
    (body : unaryBodies.obj world) :
    (conclusionJudgment rules algebra (unaryOccurrence world channel datum body)).2.2.1 =
      algebra.operation Op.par
        (.cons (algebra.operation Op.out1
          (.cons (programsAtEquiv algebra .nm world channel)
            (.cons (programsAtEquiv algebra .nm world datum) .nil)))
          (.cons (algebra.operation Op.inp1
            (.cons (programsAtEquiv algebra .nm world channel)
              (.cons (CategoricalOperations.unaryBody algebra world body) .nil))) .nil)) := by
  exact unarySchema_source algebra world.unop.context
    (unaryOccurrence world channel datum body).valuation
    (unaryOccurrence world channel datum body).close

theorem binary_source_body (world : Base) (channel first second : names.obj world)
    (body : binaryBodies.obj world) :
    (conclusionJudgment rules algebra (binaryOccurrence world channel first second body)).2.2.1 =
      algebra.operation Op.par
        (.cons (algebra.operation Op.out2
          (.cons (programsAtEquiv algebra .nm world channel)
            (.cons (programsAtEquiv algebra .nm world first)
              (.cons (programsAtEquiv algebra .nm world second) .nil))))
          (.cons (algebra.operation Op.inp2
            (.cons (programsAtEquiv algebra .nm world channel)
              (.cons (CategoricalOperations.binaryBody algebra world body) .nil))) .nil)) := by
  exact binarySchema_source algebra world.unop.context
    (binaryOccurrence world channel first second body).valuation
    (binaryOccurrence world channel first second body).close

theorem unaryEvent_source (world : Base) (channel datum : names.obj world)
    (body : unaryBodies.obj world) :
    source.app world (unaryEvent world channel datum body) =
      (CategoricalOperations.parallel algebra).app world
        ((CategoricalOperations.output algebra).app world (channel, datum),
          (CategoricalOperations.input algebra).app world (channel, body)) := by
  apply (programsAtEquiv algebra .pr world).injective
  rw [source_readout]
  change (conclusionJudgment rules algebra (unaryOccurrence world channel datum body)).2.2.1 = _
  rw [unary_source_body, CategoricalOperations.parallel_readout,
    CategoricalOperations.output_readout, CategoricalOperations.input_readout]

theorem binaryEvent_source (world : Base) (channel first second : names.obj world)
    (body : binaryBodies.obj world) :
    source.app world (binaryEvent world channel first second body) =
      (CategoricalOperations.parallel algebra).app world
        ((CategoricalOperations.send algebra).app world (channel, first, second),
          (CategoricalOperations.receive algebra).app world (channel, body)) := by
  apply (programsAtEquiv algebra .pr world).injective
  rw [source_readout]
  change (conclusionJudgment rules algebra (binaryOccurrence world channel first second body)).2.2.1 = _
  rw [binary_source_body, CategoricalOperations.parallel_readout,
    CategoricalOperations.send_readout, CategoricalOperations.receive_readout]

theorem unaryEvent_target (world : Base) (channel datum : names.obj world)
    (body : unaryBodies.obj world) :
    target.app world (unaryEvent world channel datum body) = body.app world (𝟙 world) datum := by
  apply (programsAtEquiv algebra .pr world).injective
  rw [target_readout]
  have evaluated := IntrinsicScopedOperationalPresheafPrograms.function_eval_body
    algebra [.nm] .pr world datum body
  change programsAtEquiv algebra .pr world (body.app world (𝟙 world) datum) =
    algebra.substitution.substitute
      (fromPositions (S := sig) (Srt.nm :: world.unop.context)
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair
          algebra.substitution.toClone datum (𝟙 world.unop)))
      (CategoricalOperations.unaryBody algebra world body) at evaluated
  change algebra.substitution.substitute
    (joinEnvironment (argsEnvironment algebra (bs := [Srt.nm]) (Γ := world.unop.context)
      (.cons (programsAtEquiv algebra .nm world datum) .nil))
      (fun _ position => algebra.substitution.injectVar position))
    (CategoricalOperations.unaryBody algebra world body) = _
  exact (evaluated.trans (congrArg
    (fun environment => algebra.substitution.substitute environment
      (CategoricalOperations.unaryBody algebra world body))
    (IntrinsicScopedOperationalPresheafPrograms.evaluation_environment algebra [Srt.nm] world datum))).symm

theorem binaryEvent_target (world : Base) (channel first second : names.obj world)
    (body : binaryBodies.obj world) :
    target.app world (binaryEvent world channel first second body) =
      body.app world (𝟙 world) (first, second) := by
  apply (programsAtEquiv algebra .pr world).injective
  rw [target_readout]
  let arguments := (CategoricalOperations.binaryContextIso algebra).hom.app world (first, second)
  have evaluated := IntrinsicScopedOperationalPresheafPrograms.function_eval_body
    algebra [.nm, .nm] .pr world arguments ((CategoricalOperations.binaryBodyIso algebra).hom.app world body)
  change programsAtEquiv algebra .pr world
    ((((CategoricalOperations.binaryBodyIso algebra).hom.app world body).app world (𝟙 world)) arguments) =
    algebra.substitution.substitute
      (fromPositions (S := sig) (Srt.nm :: Srt.nm :: world.unop.context)
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair
          algebra.substitution.toClone arguments (𝟙 world.unop)))
      (CategoricalOperations.binaryBody algebra world body) at evaluated
  rw [CategoricalOperations.binaryBodyIso_future] at evaluated
  change algebra.substitution.substitute
    (joinEnvironment
      (argsEnvironment algebra (bs := [Srt.nm, Srt.nm]) (Γ := world.unop.context)
        (.cons (programsAtEquiv algebra .nm world first)
        (.cons (programsAtEquiv algebra .nm world second) .nil)))
      (fun _ position => algebra.substitution.injectVar position))
    (CategoricalOperations.binaryBody algebra world body) = _
  have joined := evaluated.trans (congrArg
    (fun environment => algebra.substitution.substitute environment
      (CategoricalOperations.binaryBody algebra world body))
    (IntrinsicScopedOperationalPresheafPrograms.evaluation_environment algebra
      [Srt.nm, Srt.nm] world arguments))
  have recovered : (CategoricalOperations.binaryContextIso algebra).inv.app world arguments = (first, second) := by
    change (((CategoricalOperations.binaryContextIso algebra).hom ≫
      (CategoricalOperations.binaryContextIso algebra).inv).app world) (first, second) = _
    rw [(CategoricalOperations.binaryContextIso algebra).hom_inv_id]
    rfl
  rw [recovered] at joined
  exact joined.symm

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperational
