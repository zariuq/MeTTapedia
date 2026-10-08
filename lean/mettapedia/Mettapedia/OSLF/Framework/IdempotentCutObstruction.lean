import Mettapedia.OSLF.Syntax.IdempotentCutEquations
import Mettapedia.GSLT.Logic.RelativePushoutFunctor
import Mettapedia.GSLT.Logic.RedexRelativeCongruence

/-!
# An actual idempotent Cut equation family without redex RPOs

The independently generated term and fresh-hole context quotients have two
distinct closed classes. Their actual based normalization is full and faithful.
Two genuine reductions of an absorbing bound have no common refining candidate:
one requires a zero left mediator, the other a zero right mediator. Thus the
bound has no relative pushout, even for a binary Cut-headed rule. This failure
is not inferred from noncancellation alone or from an empty rule family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CommutativeCut.Idempotent.Obstruction

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundMonoidAction
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

instance regularAction : MulAction (Multiplicative (Class Unit)) (Class Unit) where
  smul supplied value := supplied.toAdd + value
  one_smul value := zero_add value
  mul_smul _ _ _ := add_assoc _ _ _

def erasureHom : ContextClass Unit →* Multiplicative (Class Unit) where
  toFun supplied := Multiplicative.ofAdd (erasureQ supplied)
  map_one' := rfl
  map_mul' first second := congrArg Multiplicative.ofAdd (erasureQ_mul first second)

def normalization : Category Unit ⥤ Object (Multiplicative (Class Unit)) (Class Unit) :=
  Mettapedia.CategoryTheory.GroundMonoidAction.map erasureHom id action_readout

instance normalization_faithful : normalization.Faithful :=
  map_faithful erasureHom id action_readout
    (fun _ _ same => erasureEquiv.injective (congrArg Multiplicative.toAdd same))
    Function.injective_id

instance normalization_full : normalization.Full := by
  apply map_full
  · intro supplied
    obtain ⟨preimage, same⟩ := erasureEquiv.surjective supplied.toAdd
    exact ⟨preimage, congrArg Multiplicative.ofAdd same⟩
  · exact Function.surjective_id

theorem normalization_objects : Function.Surjective normalization.obj :=
  map_objects_surjective erasureHom id action_readout

abbrev Carrier := Category Unit

def token : Class Unit := classOf (.atom ())

def tokenContext : ContextClass Unit := fromTerm token

def closed (value : Class Unit) : (.origin : Carrier) ⟶ .interface := valueArrow value

def context (value : ContextClass Unit) : (.interface : Carrier) ⟶ .interface := contextArrow value

theorem erasure_tokenContext : erasureQ tokenContext = token := erasureEquiv.apply_symm_apply token

theorem tokenContext_smul : tokenContext • token = token := by
  rw [action_readout, erasure_tokenContext, add_self]

theorem tokenContext_mul : tokenContext * tokenContext = tokenContext := by
  apply erasureEquiv.injective
  change erasureQ (tokenContext * tokenContext) = erasureQ tokenContext
  rw [erasureQ_mul, erasure_tokenContext, add_self]

def contextPresence (value : ContextClass Unit) : Bool := presenceQ (erasureQ value)

theorem contextPresence_one : contextPresence 1 = false := rfl

theorem contextPresence_mul (first second : ContextClass Unit) :
    contextPresence (first * second) = (contextPresence first || contextPresence second) := by
  unfold contextPresence
  rw [erasureQ_mul, presenceQ_add]

theorem contextPresence_token : contextPresence tokenContext = true := by
  unfold contextPresence
  rw [erasure_tokenContext]
  rfl

def leftCandidate : Candidate (closed token) (closed token) (context tokenContext) (context tokenContext) where
  apex := .interface
  inl := context 1
  inr := context tokenContext
  down := context tokenContext
  comm := by
    exact congrArg closed ((one_smul (ContextClass Unit) token).trans tokenContext_smul.symm)
  fac_left := congrArg Arrow.context (mul_one tokenContext)
  fac_right := congrArg Arrow.context tokenContext_mul

def rightCandidate : Candidate (closed token) (closed token) (context tokenContext) (context tokenContext) where
  apex := .interface
  inl := context tokenContext
  inr := context 1
  down := context tokenContext
  comm := by
    exact congrArg closed (tokenContext_smul.trans (one_smul (ContextClass Unit) token).symm)
  fac_left := congrArg Arrow.context tokenContext_mul
  fac_right := congrArg Arrow.context (mul_one tokenContext)

theorem no_common_refiner
    (candidate : Candidate (closed token) (closed token) (context tokenContext) (context tokenContext)) :
    ¬ ((∃ first, Candidate.Mediates candidate leftCandidate first) ∧
      ∃ second, Candidate.Mediates candidate rightCandidate second) := by
  rcases candidate with ⟨apex, left, right, down, comm, leftFac, rightFac⟩
  cases apex with
  | origin => cases left
  | interface =>
    cases left with
    | context left =>
      cases right with
      | context right =>
        rintro ⟨⟨first, firstLaws⟩, ⟨second, secondLaws⟩⟩
        cases first with
        | context first =>
          cases second with
          | context second =>
            have leftA : first * left = 1 := Arrow.context.inj firstLaws.1
            have rightA : first * right = tokenContext := Arrow.context.inj firstLaws.2.1
            have rightB : second * right = 1 := Arrow.context.inj secondLaws.2.1
            have firstPresence := congrArg contextPresence leftA
            have secondPresence := congrArg contextPresence rightA
            have thirdPresence := congrArg contextPresence rightB
            rw [contextPresence_mul, contextPresence_one] at firstPresence thirdPresence
            rw [contextPresence_mul, contextPresence_token] at secondPresence
            have firstFalse : contextPresence first = false := by
              cases same : contextPresence first
              · rfl
              · rw [same, Bool.true_or] at firstPresence
                cases firstPresence
            have rightFalse : contextPresence right = false := by
              cases same : contextPresence right
              · rfl
              · rw [same, Bool.or_true] at thirdPresence
                cases thirdPresence
            rw [firstFalse, rightFalse, Bool.false_or] at secondPresence
            cases secondPresence

theorem no_relativePushout_for_absorbing_bound :
    ¬ ∃ candidate : Candidate (closed token) (closed token) (context tokenContext) (context tokenContext),
      IsRelativePushout candidate := by
  rintro ⟨candidate, universal⟩
  exact no_common_refiner candidate ⟨(universal leftCandidate).exists, (universal rightCandidate).exists⟩

theorem redex_rpo_condition_fails : ¬ HasRelativePushouts (closed token) (closed token) := by
  intro allBounds
  exact no_relativePushout_for_absorbing_bound
    (allBounds .interface (context tokenContext) (context tokenContext) rfl)

def obstructingRule : ReactionRule (.origin : Carrier) where
  codomain := .interface
  redex := closed (classOf (.cut (.atom ()) (.atom ())))
  reactum := closed (classOf .zero)

theorem actual_binary_redex_lacks_rpos : ¬ HasRelativePushouts (closed token) obstructingRule.redex := by
  have same : obstructingRule.redex = closed token := congrArg closed (Quotient.sound (Equates.idem (.atom ())))
  rw [same]
  exact redex_rpo_condition_fails

theorem idempotence_is_not_total_collapse : (0 : Class Unit) ≠ token := by
  intro same
  have impossible := congrArg presenceQ same
  cases impossible

theorem actual_equation_erases_duplicates :
    classOf (.cut (.atom ()) (.atom ())) = token := Quotient.sound (Equates.idem (.atom ()))

end Mettapedia.OSLF.CommutativeCut.Idempotent.Obstruction
