import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalGraph
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationsReadout
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleFirings

/-!
# Complete native unary and binary COMM receipts

The supplied input functions are decoded through the actual binder-body
equivalences. Rule occurrences retain their independent declarations,
complete assignments, closing values and empty premise families. Every
clone substitution acts on the retained tree itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperational

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open IntrinsicScopedLocalPolynomial
open IntrinsicScopedConditionalSubstitution (substJudgment)
open IntrinsicScopedOperationalPresheafRuleFirings (sortedEvent_ext)
open IntrinsicScopedOperationalPresheafRuleFunctions
open AuthoredPositionedRulePolynomial (Judgment)

private abbrev rules := AuthoredOperationalProfile.rules

abbrev names : Ambient := CategoricalOperations.names algebra
abbrev unaryBodies : Ambient := CategoricalOperations.unaryBodies algebra
abbrev binaryBodies : Ambient := CategoricalOperations.binaryBodies algebra

def unaryOccurrence (world : Base) (channel datum : names.obj world)
    (body : unaryBodies.obj world) : Instance rules algebra where
  index := ⟨0, by decide⟩
  ambient := world.unop.context
  valuation
    | ⟨0, _⟩ => CategoricalOperations.unaryBody algebra world body
    | ⟨1, _⟩ => algebra.operation Op.nil .nil
    | ⟨n + 2, impossible⟩ => by
        change n + 2 < 2 at impossible
        omega
  close
    | _, .zero => programsAtEquiv algebra .nm world channel
    | _, .succ .zero => programsAtEquiv algebra .nm world datum

def binaryOccurrence (world : Base) (channel first second : names.obj world)
    (body : binaryBodies.obj world) : Instance rules algebra where
  index := ⟨1, by decide⟩
  ambient := world.unop.context
  valuation
    | ⟨0, _⟩ => algebra.operation Op.nil .nil
    | ⟨1, _⟩ => CategoricalOperations.binaryBody algebra world body
    | ⟨n + 2, impossible⟩ => by
        change n + 2 < 2 at impossible
        omega
  close
    | _, .zero => programsAtEquiv algebra .nm world channel
    | _, .succ .zero => programsAtEquiv algebra .nm world first
    | _, .succ (.succ .zero) => programsAtEquiv algebra .nm world second

def unaryEvent (world : Base) (channel datum : names.obj world)
    (body : unaryBodies.obj world) : edges.obj world :=
  ⟨⟨.pr, (conclusionJudgment rules algebra
    (unaryOccurrence world channel datum body)).2.2,
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        ⟨unaryOccurrence world channel datum body, rfl⟩
        (fun position => by change Fin 0 at position; exact position.elim0)⟩, rfl⟩

def binaryEvent (world : Base) (channel first second : names.obj world)
    (body : binaryBodies.obj world) : edges.obj world :=
  ⟨⟨.pr, (conclusionJudgment rules algebra
    (binaryOccurrence world channel first second body)).2.2,
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        ⟨binaryOccurrence world channel first second body, rfl⟩
        (fun position => by change Fin 0 at position; exact position.elim0)⟩, rfl⟩

theorem unaryBody_substitution {world future : Base} (change : world ⟶ future)
    (body : unaryBodies.obj world) :
    CategoricalOperations.unaryBody algebra future (unaryBodies.map change body) =
      algebra.substitution.substitute
        (algebra.substitution.liftEnvironment
          (fromPositions world.unop.context change.unop) [.nm])
        (CategoricalOperations.unaryBody algebra world body) := by
  exact (scopedBodyEquiv_reindex algebra [.nm] .pr change body).trans
    (congrArg (fun environment => algebra.substitution.substitute environment
      (CategoricalOperations.unaryBody algebra world body))
      (fromPositions_extendScope algebra [.nm] change.unop))

theorem binaryBody_substitution {world future : Base} (change : world ⟶ future)
    (body : binaryBodies.obj world) :
    CategoricalOperations.binaryBody algebra future (binaryBodies.map change body) =
      algebra.substitution.substitute
        (algebra.substitution.liftEnvironment
          (fromPositions world.unop.context change.unop) [.nm, .nm])
        (CategoricalOperations.binaryBody algebra world body) := by
  unfold CategoricalOperations.binaryBody
  rw [(CategoricalOperations.binaryBodyIso algebra).hom.naturality_apply change]
  exact (scopedBodyEquiv_reindex algebra [.nm, .nm] .pr change _).trans
    (congrArg (fun environment => algebra.substitution.substitute environment
      (scopedBodyEquiv algebra world.unop [.nm, .nm] .pr
        ((CategoricalOperations.binaryBodyIso algebra).hom.app world body)))
      (fromPositions_extendScope algebra [.nm, .nm] change.unop))

theorem unaryOccurrence_substitution {world future : Base} (change : world ⟶ future)
    (channel datum : names.obj world) (body : unaryBodies.obj world) :
    unaryOccurrence future (names.map change channel) (names.map change datum)
        (unaryBodies.map change body) =
      Instance.subst rules (unaryOccurrence world channel datum body)
        (fromPositions world.unop.context change.unop) := by
  have values : (unaryOccurrence future (names.map change channel) (names.map change datum)
      (unaryBodies.map change body)).valuation =
      (Instance.subst rules (unaryOccurrence world channel datum body)
        (fromPositions world.unop.context change.unop)).valuation := by
    funext index
    rcases index with ⟨index, bound⟩
    have small : index < 2 := bound
    interval_cases index
    · exact unaryBody_substitution change body
    · change algebra.operation Op.nil .nil = algebra.substitution.substitute
        (algebra.substitution.liftEnvironment
          (fromPositions world.unop.context change.unop) [.nm, .nm])
        (algebra.operation Op.nil .nil)
      exact (algebra.operation_substitute
        (algebra.substitution.liftEnvironment
          (fromPositions world.unop.context change.unop) [.nm, .nm]) Op.nil .nil).symm
  have close : (unaryOccurrence future (names.map change channel) (names.map change datum)
      (unaryBodies.map change body)).close =
      (Instance.subst rules (unaryOccurrence world channel datum body)
        (fromPositions world.unop.context change.unop)).close := by
    funext sort position
    cases position with
    | zero => rfl
    | succ position => cases position with
      | zero => rfl
      | succ position => nomatch position
  exact congrArg₂ (fun valuation close =>
    (⟨⟨0, by decide⟩, future.unop.context, valuation, close⟩ : Instance rules algebra)) values close

theorem binaryOccurrence_substitution {world future : Base} (change : world ⟶ future)
    (channel first second : names.obj world) (body : binaryBodies.obj world) :
    binaryOccurrence future (names.map change channel) (names.map change first)
        (names.map change second) (binaryBodies.map change body) =
      Instance.subst rules (binaryOccurrence world channel first second body)
        (fromPositions world.unop.context change.unop) := by
  have values : (binaryOccurrence future (names.map change channel) (names.map change first)
      (names.map change second) (binaryBodies.map change body)).valuation =
      (Instance.subst rules (binaryOccurrence world channel first second body)
        (fromPositions world.unop.context change.unop)).valuation := by
    funext index
    rcases index with ⟨index, bound⟩
    have small : index < 2 := bound
    interval_cases index
    · change algebra.operation Op.nil .nil = algebra.substitution.substitute
        (algebra.substitution.liftEnvironment
          (fromPositions world.unop.context change.unop) [.nm])
        (algebra.operation Op.nil .nil)
      exact (algebra.operation_substitute
        (algebra.substitution.liftEnvironment
          (fromPositions world.unop.context change.unop) [.nm]) Op.nil .nil).symm
    · exact binaryBody_substitution change body
  have close : (binaryOccurrence future (names.map change channel) (names.map change first)
      (names.map change second) (binaryBodies.map change body)).close =
      (Instance.subst rules (binaryOccurrence world channel first second body)
        (fromPositions world.unop.context change.unop)).close := by
    funext sort position
    cases position with
    | zero => rfl
    | succ position => cases position with
      | zero => rfl
      | succ position => cases position with
        | zero => rfl
        | succ position => nomatch position
  exact congrArg₂ (fun valuation close =>
    (⟨⟨1, by decide⟩, future.unop.context, valuation, close⟩ : Instance rules algebra)) values close

theorem unaryEvent_substitution {world future : Base} (change : world ⟶ future)
    (channel datum : names.obj world) (body : unaryBodies.obj world) :
    edges.map change (unaryEvent world channel datum body) =
      unaryEvent future (names.map change channel) (names.map change datum)
        (unaryBodies.map change body) := by
  let first := unaryOccurrence world channel datum body
  let second := unaryOccurrence future (names.map change channel) (names.map change datum)
    (unaryBodies.map change body)
  let sigma := fromPositions world.unop.context change.unop
  have same : Instance.subst rules first sigma = second :=
    (unaryOccurrence_substitution change channel datum body).symm
  have conclusion : substJudgment (conclusionJudgment rules algebra first) sigma =
      conclusionJudgment rules algebra second :=
    (conclusionJudgment_subst rules first sigma).symm.trans
      (congrArg (conclusionJudgment rules algebra) same)
  apply sortedEvent_ext rules model future
  · exact (sortEventJudgment_reindex algebra model.toAction change _).trans conclusion
  · have original := sortEventEvidence_reindex algebra model.toAction change
      (unaryEvent world channel datum body)
    have changed := model.toAction.act_heq
      (value₁ := sortEventEvidence algebra model.toAction world
        (unaryEvent world channel datum body))
      rfl HEq.rfl HEq.rfl conclusion rfl conclusion
    have law := model.act_rules
      (⟨first, rfl⟩ : Shape rules algebra (conclusionJudgment rules algebra first))
      (fun position => by change Fin 0 at position; exact position.elim0)
      sigma (conclusionJudgment rules algebra second) conclusion
    have compared := IntrinsicScopedLocalSubstitutionModel.rulesAct_congr_instance
      algebra model.rules same
      ((conclusionJudgment_subst rules first sigma).trans conclusion) rfl
      (fun position => model.act (childJudgment rules algebra first position)
        (by change Fin 0 at position; exact position.elim0)
        (algebra.substitution.liftEnvironment sigma
          ((rules.get first.index).2.premises.get position).binders)
        (childJudgment rules algebra (Instance.subst rules first sigma) position)
        (childJudgment_subst rules first sigma position).symm)
      (fun position => by change Fin 0 at position; exact position.elim0)
      (by intro position; change Fin 0 at position; exact position.elim0)
    exact original.trans (changed.trans ((heq_of_eq law).trans (heq_of_eq compared)))

theorem binaryEvent_substitution {world future : Base} (change : world ⟶ future)
    (channel firstName secondName : names.obj world) (body : binaryBodies.obj world) :
    edges.map change (binaryEvent world channel firstName secondName body) =
      binaryEvent future (names.map change channel) (names.map change firstName)
        (names.map change secondName) (binaryBodies.map change body) := by
  let first := binaryOccurrence world channel firstName secondName body
  let second := binaryOccurrence future (names.map change channel) (names.map change firstName)
    (names.map change secondName) (binaryBodies.map change body)
  let sigma := fromPositions world.unop.context change.unop
  have same : Instance.subst rules first sigma = second :=
    (binaryOccurrence_substitution change channel firstName secondName body).symm
  have conclusion : substJudgment (conclusionJudgment rules algebra first) sigma =
      conclusionJudgment rules algebra second :=
    (conclusionJudgment_subst rules first sigma).symm.trans
      (congrArg (conclusionJudgment rules algebra) same)
  apply sortedEvent_ext rules model future
  · exact (sortEventJudgment_reindex algebra model.toAction change _).trans conclusion
  · have original := sortEventEvidence_reindex algebra model.toAction change
      (binaryEvent world channel firstName secondName body)
    have changed := model.toAction.act_heq
      (value₁ := sortEventEvidence algebra model.toAction world
        (binaryEvent world channel firstName secondName body))
      rfl HEq.rfl HEq.rfl conclusion rfl conclusion
    have law := model.act_rules
      (⟨first, rfl⟩ : Shape rules algebra (conclusionJudgment rules algebra first))
      (fun position => by change Fin 0 at position; exact position.elim0)
      sigma (conclusionJudgment rules algebra second) conclusion
    have compared := IntrinsicScopedLocalSubstitutionModel.rulesAct_congr_instance
      algebra model.rules same
      ((conclusionJudgment_subst rules first sigma).trans conclusion) rfl
      (fun position => model.act (childJudgment rules algebra first position)
        (by change Fin 0 at position; exact position.elim0)
        (algebra.substitution.liftEnvironment sigma
          ((rules.get first.index).2.premises.get position).binders)
        (childJudgment rules algebra (Instance.subst rules first sigma) position)
        (childJudgment_subst rules first sigma position).symm)
      (fun position => by change Fin 0 at position; exact position.elim0)
      (by intro position; change Fin 0 at position; exact position.elim0)
    exact original.trans (changed.trans ((heq_of_eq law).trans (heq_of_eq compared)))

/-- Native COMM acts on the complete supplied unary input function. -/
def unaryCommunication : names ⊗ (names ⊗ unaryBodies) ⟶ edges where
  app world := TypeCat.ofHom (fun point => unaryEvent world point.1 point.2.1 point.2.2)
  naturality world future change := by
    apply ConcreteCategory.hom_ext
    rintro ⟨channel, datum, body⟩
    exact (unaryEvent_substitution change channel datum body).symm

/-- The two emitted names stay in distinct ordered binary positions. -/
def binaryCommunication : names ⊗ (names ⊗ (names ⊗ binaryBodies)) ⟶ edges where
  app world := TypeCat.ofHom (fun point =>
    binaryEvent world point.1 point.2.1 point.2.2.1 point.2.2.2)
  naturality world future change := by
    apply ConcreteCategory.hom_ext
    rintro ⟨channel, first, second, body⟩
    exact (binaryEvent_substitution change channel first second body).symm

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperational
