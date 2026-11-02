import Mettapedia.OSLF.Syntax.PartialRenaming

/-!
# Pulling compatible binding terms back to their common variable interface

A variable pullback records pairs of positions whose ambient images agree.
Its projections, recovery and uniqueness laws lift through every declared
binder prefix. The existing binding-term constructors preserve this
pullback: two terms with equal ambient images come from a common term.

These are structural scope laws. They do not identify value conversion with
syntax equality or assume that arbitrary higher-order unification is decidable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

variable {S : Signature} {L R Γ : Ctx S}

structure ScopePullback (left : Ren S L Γ) (right : Ren S R Γ) where
  context : Ctx S
  toLeft : Ren S context L
  toRight : Ren S context R
  commutes : ∀ sort (position : Var context sort),
    left sort (toLeft sort position) = right sort (toRight sort position)
  recover : ∀ sort (first : Var L sort) (second : Var R sort),
    left sort first = right sort second → Var context sort
  recover_left : ∀ sort (first : Var L sort) (second : Var R sort)
    (same : left sort first = right sort second), toLeft sort (recover sort first second same) = first
  recover_right : ∀ sort (first : Var L sort) (second : Var R sort)
    (same : left sort first = right sort second), toRight sort (recover sort first second same) = second
  recover_pair : ∀ sort (position : Var context sort),
    recover sort (toLeft sort position) (toRight sort position) (commutes sort position) = position

namespace ScopePullback

variable {left : Ren S L Γ} {right : Ren S R Γ} (pullback : ScopePullback left right)

def liftRecover : (binders : Ctx S) → ∀ sort
    (first : Var (binders ++ L) sort) (second : Var (binders ++ R) sort),
    liftRen left binders sort first = liftRen right binders sort second →
      Var (binders ++ pullback.context) sort
  | [], sort, first, second, same => pullback.recover sort first second same
  | _ :: _, _, .zero, .zero, _ => .zero
  | _ :: _, _, .zero, .succ _, same => nomatch same
  | _ :: _, _, .succ _, .zero, same => nomatch same
  | _ :: binders, sort, .succ first, .succ second, same =>
      .succ (liftRecover binders sort first second (Var.succ.inj same))

theorem liftRecover_left : ∀ (binders : Ctx S) sort
    (first : Var (binders ++ L) sort) (second : Var (binders ++ R) sort)
    (same : liftRen left binders sort first = liftRen right binders sort second),
    liftRen pullback.toLeft binders sort (pullback.liftRecover binders sort first second same) = first
  | [], sort, first, second, same => pullback.recover_left sort first second same
  | _ :: _, _, .zero, .zero, _ => rfl
  | _ :: _, _, .zero, .succ _, same => nomatch same
  | _ :: _, _, .succ _, .zero, same => nomatch same
  | _ :: binders, sort, .succ first, .succ second, same =>
      congrArg Var.succ (liftRecover_left binders sort first second (Var.succ.inj same))

theorem liftRecover_right : ∀ (binders : Ctx S) sort
    (first : Var (binders ++ L) sort) (second : Var (binders ++ R) sort)
    (same : liftRen left binders sort first = liftRen right binders sort second),
    liftRen pullback.toRight binders sort (pullback.liftRecover binders sort first second same) = second
  | [], sort, first, second, same => pullback.recover_right sort first second same
  | _ :: _, _, .zero, .zero, _ => rfl
  | _ :: _, _, .zero, .succ _, same => nomatch same
  | _ :: _, _, .succ _, .zero, same => nomatch same
  | _ :: binders, sort, .succ first, .succ second, same =>
      congrArg Var.succ (liftRecover_right binders sort first second (Var.succ.inj same))

theorem lift_commutes : ∀ (binders : Ctx S) sort (position : Var (binders ++ pullback.context) sort),
    liftRen left binders sort (liftRen pullback.toLeft binders sort position) =
      liftRen right binders sort (liftRen pullback.toRight binders sort position)
  | [], sort, position => pullback.commutes sort position
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ position => congrArg Var.succ (lift_commutes binders sort position)

theorem liftRecover_pair : ∀ (binders : Ctx S) sort (position : Var (binders ++ pullback.context) sort),
    pullback.liftRecover binders sort
      (liftRen pullback.toLeft binders sort position)
      (liftRen pullback.toRight binders sort position)
      (pullback.lift_commutes binders sort position) = position
  | [], sort, position => pullback.recover_pair sort position
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ position => congrArg Var.succ (liftRecover_pair binders sort position)

/-- Bound variables in the new prefix are common to both sides, while
outer variables retain exactly their previous pullback interface. -/
def liftS (binders : Ctx S) : ScopePullback (liftRen left binders) (liftRen right binders) where
  context := binders ++ pullback.context
  toLeft := liftRen pullback.toLeft binders
  toRight := liftRen pullback.toRight binders
  commutes := pullback.lift_commutes binders
  recover := pullback.liftRecover binders
  recover_left := pullback.liftRecover_left binders
  recover_right := pullback.liftRecover_right binders
  recover_pair := pullback.liftRecover_pair binders

mutual

/-- Compatibility in the ambient context is sufficient to reconstruct a
common term, including each operator's full binding argument interface. -/
theorem factor_terms : ∀ {L R Γ : Ctx S} {left : Ren S L Γ} {right : Ren S R Γ}
    (pullback : ScopePullback left right) {sort : S.Srt}
    (first : Term S L sort) (second : Term S R sort),
    rename left first = rename right second →
      ∃ common : Term S pullback.context sort,
        rename pullback.toLeft common = first ∧ rename pullback.toRight common = second
  | _, _, _, _, _, pullback, sort, .var first, .var second, same => by
      let compatible := Term.var.inj same
      exact ⟨.var (pullback.recover sort first second compatible),
        congrArg Term.var (pullback.recover_left sort first second compatible),
        congrArg Term.var (pullback.recover_right sort first second compatible)⟩
  | _, _, _, _, _, _, _, .var _, .op _ _, same => by cases same
  | _, _, _, _, _, _, _, .op _ _, .var _, same => by cases same
  | _, _, _, _, _, pullback, _, .op operator arguments, .op other others, same => by
      have operators := (Term.op.inj same).1
      subst other
      obtain ⟨common, firstCommon, secondCommon⟩ :=
        factor_arguments pullback arguments others (eq_of_heq (Term.op.inj same).2)
      exact ⟨.op operator common, congrArg (Term.op operator) firstCommon,
        congrArg (Term.op operator) secondCommon⟩

theorem factor_arguments : ∀ {L R Γ : Ctx S} {left : Ren S L Γ} {right : Ren S R Γ}
    (pullback : ScopePullback left right) {arities : List (List S.Srt × S.Srt)}
    (first : Args S arities L) (second : Args S arities R),
    renameArgs left first = renameArgs right second →
      ∃ common : Args S arities pullback.context,
        renameArgs pullback.toLeft common = first ∧ renameArgs pullback.toRight common = second
  | _, _, _, _, _, _, _, .nil, .nil, _ => ⟨.nil, rfl, rfl⟩
  | _, _, _, _, _, pullback, _, .cons (bs := binders) first rest, .cons second remaining, same => by
      have arguments := Args.cons.inj same
      obtain ⟨commonHead, firstHead, secondHead⟩ :=
        (pullback.liftS binders).factor_terms first second arguments.1
      obtain ⟨commonTail, firstTail, secondTail⟩ := factor_arguments pullback rest remaining arguments.2
      exact ⟨.cons commonHead commonTail,
        congrArg₂ Args.cons firstHead firstTail, congrArg₂ Args.cons secondHead secondTail⟩

end

theorem jointly_injective_variables {sort : S.Srt} {first second : Var pullback.context sort}
    (firstProjection : pullback.toLeft sort first = pullback.toLeft sort second)
    (secondProjection : pullback.toRight sort first = pullback.toRight sort second) : first = second := by
  let compatible (position : Var pullback.context sort) :
      { pair : Var L sort × Var R sort // left sort pair.1 = right sort pair.2 } :=
    ⟨(pullback.toLeft sort position, pullback.toRight sort position), pullback.commutes sort position⟩
  have same : compatible first = compatible second :=
    Subtype.ext (Prod.ext firstProjection secondProjection)
  have recovered := congrArg (fun pair => pullback.recover sort pair.1.1 pair.1.2 pair.2) same
  simpa only [compatible, pullback.recover_pair] using recovered

mutual

theorem jointly_injective_terms : ∀ {L R Γ : Ctx S} {left : Ren S L Γ} {right : Ren S R Γ}
    (pullback : ScopePullback left right) {sort : S.Srt}
    (first second : Term S pullback.context sort),
    rename pullback.toLeft first = rename pullback.toLeft second →
      rename pullback.toRight first = rename pullback.toRight second → first = second
  | _, _, _, _, _, pullback, _, .var first, .var second, sameLeft, sameRight =>
      congrArg Term.var (pullback.jointly_injective_variables (Term.var.inj sameLeft) (Term.var.inj sameRight))
  | _, _, _, _, _, _, _, .var _, .op _ _, same, _ => by cases same
  | _, _, _, _, _, _, _, .op _ _, .var _, same, _ => by cases same
  | _, _, _, _, _, pullback, _, .op operator arguments, .op other others, sameLeft, sameRight => by
      have operators := (Term.op.inj sameLeft).1
      subst other
      exact congrArg (Term.op operator) (jointly_injective_arguments pullback arguments others
        (eq_of_heq (Term.op.inj sameLeft).2) (eq_of_heq (Term.op.inj sameRight).2))
termination_by _ _ _ _ _ _ _ first _ _ _ => 2 * termSize first
decreasing_by all_goals simp only [termSize]; omega

theorem jointly_injective_arguments : ∀ {L R Γ : Ctx S} {left : Ren S L Γ} {right : Ren S R Γ}
    (pullback : ScopePullback left right) {arities : List (List S.Srt × S.Srt)}
    (first second : Args S arities pullback.context),
    renameArgs pullback.toLeft first = renameArgs pullback.toLeft second →
      renameArgs pullback.toRight first = renameArgs pullback.toRight second → first = second
  | _, _, _, _, _, _, _, .nil, .nil, _, _ => rfl
  | _, _, _, _, _, pullback, _, .cons (bs := binders) first rest, .cons second remaining, sameLeft, sameRight => by
      have firstArgs := Args.cons.inj sameLeft
      have secondArgs := Args.cons.inj sameRight
      exact congrArg₂ Args.cons
        ((pullback.liftS binders).jointly_injective_terms first second firstArgs.1 secondArgs.1)
        (jointly_injective_arguments pullback rest remaining firstArgs.2 secondArgs.2)
termination_by _ _ _ _ _ _ _ first _ _ _ => 2 * argsSize first + 1
decreasing_by all_goals dsimp only [argsSize, liftS]; have := termSize_pos first; omega

end

/-- The variable-interface pullback has the full unique-factorization
property on binding terms, rather than only existence of a common image. -/
theorem factor_terms_unique {sort : S.Srt} (first : Term S L sort) (second : Term S R sort)
    (same : rename left first = rename right second) :
    ∃! common : Term S pullback.context sort,
      rename pullback.toLeft common = first ∧ rename pullback.toRight common = second := by
  obtain ⟨common, firstCommon, secondCommon⟩ := pullback.factor_terms first second same
  refine ⟨common, ⟨firstCommon, secondCommon⟩, ?_⟩
  rintro other ⟨firstOther, secondOther⟩
  exact pullback.jointly_injective_terms other common (firstOther.trans firstCommon.symm)
    (secondOther.trans secondCommon.symm)

end ScopePullback
end Mettapedia.OSLF.Binding
