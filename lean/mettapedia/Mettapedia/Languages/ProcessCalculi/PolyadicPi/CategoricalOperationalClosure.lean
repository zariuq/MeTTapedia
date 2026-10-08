import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalReadout
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafContextHom

/-!
# Actual private-scope descent on retained native evidence

The bound event is evaluated in the real extended clone context. The
independently authored private-scope rule uses both of its complete endpoint
bodies and retains its individual child firing. Endpoint interpretation is
compared with the native fresh-name constructor.
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
open IntrinsicScopedOperationalPresheafEvents
open IntrinsicScopedLocalPolynomial
open IntrinsicScopedConditionalSubstitution (substJudgment heq_transport castEnv castEnv_heq)
open IntrinsicScopedOperationalPresheafRuleFirings (sortedEvent_ext)
open IntrinsicScopedOperationalPresheafRuleFunctions
open IntrinsicScopedOperationalPresheafContextHom
open AuthoredPositionedRulePolynomial (Judgment)

private abbrev rules := AuthoredOperationalProfile.rules
private abbrev onlyChild : Fin 1 := ⟨0, by decide⟩

attribute [local irreducible] BindingEquationQuotientModel.operation

abbrev extended (world : Base) : Base := (binderExtension algebra [Srt.nm]).obj world

def scopeOccurrence (world : Base) (child : edges.obj (extended world)) :
    Instance rules algebra where
  index := ⟨4, by decide⟩
  ambient := world.unop.context
  valuation
    | ⟨0, _⟩ => (atEquiv (extended world) child).1.1
    | ⟨1, _⟩ => (atEquiv (extended world) child).1.2
    | ⟨n + 2, impossible⟩ => by change n + 2 < 2 at impossible; omega
  close := fun _ position => nomatch position

theorem scope_child (world : Base) (child : edges.obj (extended world))
    (position : Fin (rules.get (scopeOccurrence world child).index).2.premises.length) :
    childJudgment rules algebra (scopeOccurrence world child) position =
      (⟨Srt.nm :: world.unop.context, .pr, (atEquiv (extended world) child).1⟩ : Judgment algebra) := by
  have zero : position = ⟨0, by change 0 < 1; decide⟩ := Fin.eq_zero position
  subst position
  change (⟨Srt.nm :: world.unop.context, .pr,
    algebra.substitution.substitute
      (joinEnvironment
        (argsEnvironment algebra (bs := [Srt.nm]) (Γ := Srt.nm :: world.unop.context)
          (.cons (algebra.substitution.injectVar .zero) .nil))
        (weakenEnvironment algebra [Srt.nm] (fun _ position => algebra.substitution.injectVar position)))
      (atEquiv (extended world) child).1.1,
    algebra.substitution.substitute
      (joinEnvironment
        (argsEnvironment algebra (bs := [Srt.nm]) (Γ := Srt.nm :: world.unop.context)
          (.cons (algebra.substitution.injectVar .zero) .nil))
        (weakenEnvironment algebra [Srt.nm] (fun _ position => algebra.substitution.injectVar position)))
      (atEquiv (extended world) child).1.2⟩ : Judgment algebra) = _
  rw [unary_identity, algebra.substitution.substitute_identity,
    algebra.substitution.substitute_identity]
  rfl

theorem scope_conclusion (world : Base) (child : edges.obj (extended world)) :
    conclusionJudgment rules algebra (scopeOccurrence world child) =
      (⟨world.unop.context, .pr,
        algebra.operation Op.nu (.cons (atEquiv (extended world) child).1.1 .nil),
        algebra.operation Op.nu (.cons (atEquiv (extended world) child).1.2 .nil)⟩ : Judgment algebra) := by
  change (⟨world.unop.context, .pr,
    algebra.operation Op.nu (.cons
      (algebra.substitution.substitute
        (joinEnvironment
          (argsEnvironment algebra (bs := [Srt.nm]) (Γ := Srt.nm :: world.unop.context)
            (.cons (algebra.substitution.injectVar .zero) .nil))
          (weakenEnvironment algebra [Srt.nm] (fun _ position => algebra.substitution.injectVar position)))
        (atEquiv (extended world) child).1.1) .nil),
    algebra.operation Op.nu (.cons
      (algebra.substitution.substitute
        (joinEnvironment
          (argsEnvironment algebra (bs := [Srt.nm]) (Γ := Srt.nm :: world.unop.context)
            (.cons (algebra.substitution.injectVar .zero) .nil))
          (weakenEnvironment algebra [Srt.nm] (fun _ position => algebra.substitution.injectVar position)))
        (atEquiv (extended world) child).1.2) .nil)⟩ : Judgment algebra) = _
  rw [unary_identity, algebra.substitution.substitute_identity,
    algebra.substitution.substitute_identity]

def scopeChildEvidence (world : Base) (child : edges.obj (extended world))
    (position : Fin (rules.get (scopeOccurrence world child).index).2.premises.length) :
    Tree rules algebra (childJudgment rules algebra (scopeOccurrence world child) position) :=
  (scope_child world child position).symm ▸ (atEquiv (extended world) child).2

/-- Private descent contains the actual supplied child, not just its support. -/
def scopeEvent (world : Base) (child : edges.obj (extended world)) : edges.obj world :=
  (atEquiv world).symm
    ⟨(algebra.operation Op.nu (.cons (atEquiv (extended world) child).1.1 .nil),
      algebra.operation Op.nu (.cons (atEquiv (extended world) child).1.2 .nil)),
      Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        ⟨scopeOccurrence world child, scope_conclusion world child⟩
        (scopeChildEvidence world child)⟩

theorem scopeEvent_source (world : Base) (child : edges.obj (extended world)) :
    programsAtEquiv algebra .pr world (source.app world (scopeEvent world child)) =
      algebra.operation Op.nu (.cons (atEquiv (extended world) child).1.1 .nil) := rfl

theorem scopeEvent_target (world : Base) (child : edges.obj (extended world)) :
    programsAtEquiv algebra .pr world (target.app world (scopeEvent world child)) =
      algebra.operation Op.nu (.cons (atEquiv (extended world) child).1.2 .nil) := rfl

theorem judgment_readout (world : Base) (event : edges.obj world) :
    sortEventJudgment algebra model.toAction world event =
      (⟨world.unop.context, Srt.pr, (atEquiv world event).1⟩ : Judgment algebra) := by
  rcases event with ⟨⟨sort, pair, tree⟩, same⟩
  cases same
  rfl

theorem pair_substitution {world future : Base} (change : world ⟶ future)
    (event : edges.obj world) :
    (atEquiv future (edges.map change event)).1 =
      (algebra.substitution.substitute (fromPositions world.unop.context change.unop)
        (atEquiv world event).1.1,
       algebra.substitution.substitute (fromPositions world.unop.context change.unop)
        (atEquiv world event).1.2) := by
  rcases event with ⟨⟨sort, pair, tree⟩, same⟩
  cases same
  rfl

theorem evidence_readout (world : Base) (event : edges.obj world) :
    HEq (sortEventEvidence algebra model.toAction world event) (atEquiv world event).2 := by
  rcases event with ⟨⟨sort, pair, tree⟩, same⟩
  cases same
  exact HEq.rfl

theorem child_congr {first second : Instance rules algebra} (same : first = second)
    (firstPosition : Fin (rules.get first.index).2.premises.length)
    (secondPosition : Fin (rules.get second.index).2.premises.length)
    (positions : HEq firstPosition secondPosition) :
    childJudgment rules algebra first firstPosition =
      childJudgment rules algebra second secondPosition := by
  cases same
  cases positions
  rfl

theorem scopeOccurrence_substitution {world future : Base} (change : world ⟶ future)
    (child : edges.obj (extended world)) :
    scopeOccurrence future (edges.map ((binderExtension algebra [Srt.nm]).map change) child) =
      Instance.subst rules (scopeOccurrence world child)
        (fromPositions world.unop.context change.unop) := by
  have pair := pair_substitution ((binderExtension algebra [Srt.nm]).map change) child
  have environment := fromPositions_extendScope algebra [Srt.nm] change.unop
  have values : (scopeOccurrence future
      (edges.map ((binderExtension algebra [Srt.nm]).map change) child)).valuation =
      (Instance.subst rules (scopeOccurrence world child)
        (fromPositions world.unop.context change.unop)).valuation := by
    funext index
    rcases index with ⟨index, bound⟩
    have small : index < 2 := bound
    interval_cases index
    · exact (congrArg Prod.fst pair).trans (congrArg
        (fun environment => algebra.substitution.substitute environment
          (atEquiv (extended world) child).1.1) environment)
    · exact (congrArg Prod.snd pair).trans (congrArg
        (fun environment => algebra.substitution.substitute environment
          (atEquiv (extended world) child).1.2) environment)
  have closing : (scopeOccurrence future
      (edges.map ((binderExtension algebra [Srt.nm]).map change) child)).close =
      (Instance.subst rules (scopeOccurrence world child)
        (fromPositions world.unop.context change.unop)).close := by
    funext sort position
    nomatch position
  exact congrArg₂ (fun valuation close =>
    (⟨⟨4, by decide⟩, future.unop.context, valuation, close⟩ : Instance rules algebra)) values closing

theorem scopeChildEvidence_substitution {world future : Base} (change : world ⟶ future)
    (child : edges.obj (extended world))
    (position : Fin (rules.get (scopeOccurrence world child).index).2.premises.length) :
    HEq
      (model.act (childJudgment rules algebra (scopeOccurrence world child) position)
        (scopeChildEvidence world child position)
        (algebra.substitution.liftEnvironment (fromPositions world.unop.context change.unop)
          ((rules.get (scopeOccurrence world child).index).2.premises.get position).binders)
        (childJudgment rules algebra
          (Instance.subst rules (scopeOccurrence world child)
            (fromPositions world.unop.context change.unop)) position)
        (childJudgment_subst rules (scopeOccurrence world child)
          (fromPositions world.unop.context change.unop) position).symm)
      (scopeChildEvidence future
        (edges.map ((binderExtension algebra [Srt.nm]).map change) child) position) := by
  have zero : position = ⟨0, by change 0 < 1; decide⟩ := Fin.eq_zero position
  subst position
  let changedChild := edges.map ((binderExtension algebra [Srt.nm]).map change) child
  have sameInstance := scopeOccurrence_substitution change child
  have oldIndex : childJudgment rules algebra (scopeOccurrence world child) onlyChild =
      sortEventJudgment algebra model.toAction (extended world) child :=
    (scope_child world child onlyChild).trans (judgment_readout (extended world) child).symm
  have newIndex : childJudgment rules algebra
      (Instance.subst rules (scopeOccurrence world child)
        (fromPositions world.unop.context change.unop)) onlyChild =
      sortEventJudgment algebra model.toAction (extended future) changedChild := by
    exact (child_congr sameInstance.symm onlyChild onlyChild HEq.rfl).trans
      ((scope_child future changedChild onlyChild).trans (judgment_readout (extended future) changedChild).symm)
  have oldValue : HEq (scopeChildEvidence world child onlyChild)
      (sortEventEvidence algebra model.toAction (extended world) child) :=
    (heq_transport (scope_child world child onlyChild).symm (atEquiv (extended world) child).2).trans
      (evidence_readout (extended world) child).symm
  have newValue : HEq
      (sortEventEvidence algebra model.toAction (extended future) changedChild)
      (scopeChildEvidence future changedChild onlyChild) :=
    (evidence_readout (extended future) changedChild).trans
      (heq_transport (scope_child future changedChild onlyChild).symm
        (atEquiv (extended future) changedChild).2).symm
  have changed := model.toAction.act_heq oldIndex oldValue
    (heq_of_eq (fromPositions_extendScope algebra [Srt.nm] change.unop).symm) newIndex
    (childJudgment_subst rules (scopeOccurrence world child)
      (fromPositions world.unop.context change.unop) onlyChild).symm
    (sortEventJudgment_reindex algebra model.toAction
      ((binderExtension algebra [Srt.nm]).map change) child).symm
  have fixed := model.toAction.act_heq
    (value₁ := sortEventEvidence algebra model.toAction (extended world) child)
    rfl HEq.rfl HEq.rfl
    (sortEventJudgment_reindex algebra model.toAction
      ((binderExtension algebra [Srt.nm]).map change) child).symm rfl
    (sortEventJudgment_reindex algebra model.toAction
      ((binderExtension algebra [Srt.nm]).map change) child).symm
  exact changed.trans (fixed.symm.trans ((sortEventEvidence_reindex algebra model.toAction
    ((binderExtension algebra [Srt.nm]).map change) child).symm.trans newValue))

def scopeResult (world : Base) (child : edges.obj (extended world)) : Judgment algebra :=
  ⟨world.unop.context, Srt.pr,
    algebra.operation Op.nu (.cons (atEquiv (extended world) child).1.1 .nil),
    algebra.operation Op.nu (.cons (atEquiv (extended world) child).1.2 .nil)⟩

theorem scopeEvent_judgment (world : Base) (child : edges.obj (extended world)) :
    sortEventJudgment algebra model.toAction world (scopeEvent world child) =
      scopeResult world child := rfl

theorem scopeResult_substitution {world future : Base} (change : world ⟶ future)
    (child : edges.obj (extended world)) :
    substJudgment (scopeResult world child) (fromPositions world.unop.context change.unop) =
      scopeResult future (edges.map ((binderExtension algebra [Srt.nm]).map change) child) := by
  have pair := pair_substitution ((binderExtension algebra [Srt.nm]).map change) child
  have environment := fromPositions_extendScope algebra [Srt.nm] change.unop
  have first := (congrArg Prod.fst pair).trans (congrArg
    (fun environment => algebra.substitution.substitute environment
      (atEquiv (extended world) child).1.1) environment)
  have second := (congrArg Prod.snd pair).trans (congrArg
    (fun environment => algebra.substitution.substitute environment
      (atEquiv (extended world) child).1.2) environment)
  apply congrArg (fun pair => (⟨future.unop.context,Srt.pr,pair⟩ : Judgment algebra))
  apply Prod.ext
  · exact (algebra.operation_substitute
      (fromPositions world.unop.context change.unop) Op.nu
      (.cons (atEquiv (extended world) child).1.1 .nil)).trans
        (congrArg (fun body => algebra.operation Op.nu (.cons body .nil)) first.symm)
  · exact (algebra.operation_substitute
      (fromPositions world.unop.context change.unop) Op.nu
      (.cons (atEquiv (extended world) child).1.2 .nil)).trans
        (congrArg (fun body => algebra.operation Op.nu (.cons body .nil)) second.symm)

theorem scopeEvent_substitution {world future : Base} (change : world ⟶ future)
    (child : edges.obj (extended world)) :
    edges.map change (scopeEvent world child) =
      scopeEvent future (edges.map ((binderExtension algebra [Srt.nm]).map change) child) := by
  let changedChild := edges.map ((binderExtension algebra [Srt.nm]).map change) child
  let first := scopeOccurrence world child
  let second := scopeOccurrence future changedChild
  let sigma := fromPositions world.unop.context change.unop
  have same : Instance.subst rules first sigma = second :=
    (scopeOccurrence_substitution change child).symm
  have conclusion := scopeResult_substitution change child
  have original := sortEventEvidence_reindex algebra model.toAction change (scopeEvent world child)
  apply sortedEvent_ext rules model future
  · exact (sortEventJudgment_reindex algebra model.toAction change _).trans conclusion
  · have fixed := model.toAction.act_heq
      (value₁ := sortEventEvidence algebra model.toAction world (scopeEvent world child))
      rfl HEq.rfl HEq.rfl conclusion rfl conclusion
    have law := model.act_rules
      (⟨first,scope_conclusion world child⟩ : Shape rules algebra (scopeResult world child))
      (scopeChildEvidence world child) sigma (scopeResult future changedChild) conclusion
    let transported := castEnv (scope_conclusion world child) sigma
    have environment : transported = sigma :=
      eq_of_heq (castEnv_heq (scope_conclusion world child) sigma)
    have sameTransported : Instance.subst rules first transported = second :=
      (congrArg (Instance.subst rules first) environment).trans same
    have sameConclusion : conclusionJudgment rules algebra (Instance.subst rules first transported) =
        scopeResult future changedChild :=
      (congrArg (fun occurrence => conclusionJudgment rules algebra occurrence) sameTransported).trans
        (scope_conclusion future changedChild)
    have compared := IntrinsicScopedLocalSubstitutionModel.rulesAct_congr_instance
      algebra model.rules sameTransported sameConclusion (scope_conclusion future changedChild)
      (fun position => model.act (childJudgment rules algebra first position)
        (scopeChildEvidence world child position)
        (algebra.substitution.liftEnvironment transported
          ((rules.get first.index).2.premises.get position).binders)
        (childJudgment rules algebra (Instance.subst rules first transported) position)
        (childJudgment_subst rules first transported position).symm)
      (scopeChildEvidence future changedChild)
      (by
        intro position otherPosition samePosition
        cases samePosition
        have targets := child_congr (congrArg (Instance.subst rules first) environment)
          position position HEq.rfl
        have childChange := model.toAction.act_heq
          (value₁ := scopeChildEvidence world child position)
          rfl HEq.rfl
          (heq_of_eq (congrArg (fun environment => algebra.substitution.liftEnvironment environment
            ((rules.get first.index).2.premises.get position).binders) environment)) targets
          (childJudgment_subst rules first transported position).symm
          (childJudgment_subst rules first sigma position).symm
        exact childChange.trans (scopeChildEvidence_substitution change child position))
    exact original.trans (fixed.trans ((heq_of_eq law).trans (heq_of_eq compared)))

/-- The whole private-scope operation acts on complete bound evidence functions. -/
def privateDescent : (names.functorHom edges) ⟶ edges where
  app world := TypeCat.ofHom (fun child => scopeEvent world
    (contextHomAtEquiv algebra [Srt.nm] edges world child))
  naturality world future change := by
    apply ConcreteCategory.hom_ext
    intro child
    change scopeEvent future (contextHomAtEquiv algebra [Srt.nm] edges future
      ((names.functorHom edges).map change child)) = _
    exact (congrArg (scopeEvent future)
      (contextHomAtEquiv_reindex algebra [Srt.nm] edges change child)).trans
      (scopeEvent_substitution change _).symm

theorem context_program_readout (world : Base) (body : unaryBodies.obj world) :
    programsAtEquiv algebra Srt.pr (extended world)
      (contextHomAtEquiv algebra [Srt.nm] processes world body) =
        CategoricalOperations.unaryBody algebra world body := by
  rw [contextHomAtEquiv_apply, CategoricalOperations.unaryBody, scopedBodyEquiv_apply]
  rfl

theorem privateDescent_source : privateDescent ≫ source =
    (ihom names).map source ≫ CategoricalOperations.fresh algebra := by
  ext world child
  apply (programsAtEquiv algebra Srt.pr world).injective
  change programsAtEquiv algebra Srt.pr world
    (source.app world (scopeEvent world (contextHomAtEquiv algebra [Srt.nm] edges world child))) =
    programsAtEquiv algebra Srt.pr world
      ((CategoricalOperations.fresh algebra).app world (((ihom names).map source).app world child))
  rw [scopeEvent_source, CategoricalOperations.fresh_readout]
  have mapped := contextHomAtEquiv_map algebra [Srt.nm] source world child
  have read := (context_program_readout world (((ihom names).map source).app world child)).symm.trans
    ((congrArg (programsAtEquiv algebra Srt.pr (extended world)) mapped).trans
      (source_readout (extended world) (contextHomAtEquiv algebra [Srt.nm] edges world child)))
  exact congrArg (fun body => algebra.operation Op.nu (.cons body .nil)) read.symm

theorem privateDescent_target : privateDescent ≫ target =
    (ihom names).map target ≫ CategoricalOperations.fresh algebra := by
  ext world child
  apply (programsAtEquiv algebra Srt.pr world).injective
  change programsAtEquiv algebra Srt.pr world
    (target.app world (scopeEvent world (contextHomAtEquiv algebra [Srt.nm] edges world child))) =
    programsAtEquiv algebra Srt.pr world
      ((CategoricalOperations.fresh algebra).app world (((ihom names).map target).app world child))
  rw [scopeEvent_target, CategoricalOperations.fresh_readout]
  have mapped := contextHomAtEquiv_map algebra [Srt.nm] target world child
  have read := (context_program_readout world (((ihom names).map target).app world child)).symm.trans
    ((congrArg (programsAtEquiv algebra Srt.pr (extended world)) mapped).trans
      (target_readout (extended world) (contextHomAtEquiv algebra [Srt.nm] edges world child)))
  exact congrArg (fun body => algebra.operation Op.nu (.cons body .nil)) read.symm

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperational
