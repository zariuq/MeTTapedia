import Mettapedia.GSLT.Logic.ObserverBubble
import Mettapedia.Logic.Diagonal.Combinatory

/-!
# Reflective bubbles: the diagonal against internal carve-outs

A *reflective bubble* is a bubble whose terms run on terms, point-surjectively
onto the polynomial maps, up to the bubble's own equality: a bubble together
with a reflexive structure on its terms whose equivalence is the bubble's
equality judgment (`ReflectiveBubble.equiv_iff`).  Its codes denote the
bubble's own procedures.

**The diagonal theorem.**  Once two terms are unequal in the bubble:

* no term decides the bubble's full equality
  (`ReflectiveBubble.no_internal_total_decision`);
* every fragment decision realised by a term (`InternallyRealizes`) excludes
  an explicit diagonal term from its fragment
  (`ReflectiveBubble.diagonal_not_mem_fragment`), so its fragment is proper
  (`ReflectiveBubble.fragment_ne_univ`), and its verdict on the diagonal is
  `outsideFragment` (`ReflectiveBubble.diagonal_verdict_outside`);
* a sound partial decider realised by a term is undetermined at its own
  diagonal (`ReflectiveBubble.sound_undetermined`).

The theorem concerns *internal* deciders.  A decision given by an arbitrary
function of the metalanguage is not covered; the instance module exhibits a
total classical decision of β-conversion that no term realises.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Reflection

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.ObserverBubble
open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.Logic.Diagonal

universe uS uContext uRule uAtom uBudget uJudgment uEvidence uObstruction uBoundary uReceipt

-- The fields live in the universes of the underlying bubble.
set_option linter.checkUnivs false in
/-- **A reflective bubble**: a bubble whose terms form a reflexive structure
whose equivalence is exactly the bubble's equality judgment. -/
structure ReflectiveBubble (S : GSLT.{uS}) (rules : ContextualRules.{uContext, uRule} S)
    (Budget : Type uBudget) [Preorder Budget] where
  bubble : Bubble.{uS, uContext, uRule, uAtom, uBudget, uJudgment, uEvidence, uObstruction,
    uBoundary, uReceipt} S rules Budget
  reflexive : Reflexive S.Term
  equiv_iff : ∀ left right,
    reflexive.Equiv left right ↔ bubble.authority.Holds (bubble.equality left right)

namespace ReflectiveBubble

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
variable {Budget : Type uBudget} [Preorder Budget]
variable (reflective : ReflectiveBubble.{uS, uContext, uRule, uAtom, uBudget, uJudgment,
  uEvidence, uObstruction, uBoundary, uReceipt} S rules Budget)

/-- The bubble's full equality judgment. -/
def Equal (left right : S.Term) : Prop :=
  reflective.bubble.authority.Holds (reflective.bubble.equality left right)

/-- The full equality is the bubble's observer equivalence. -/
theorem equal_iff_relEquiv (left right : S.Term) :
    reflective.Equal left right ↔
      reflective.bubble.observers.RelEquiv reflective.bubble.observations left right :=
  reflective.bubble.equality_holds left right

/-- **No term decides the bubble's full equality**, once two terms are
unequal. -/
theorem no_internal_total_decision {first second : S.Term}
    (distinct : ¬ reflective.Equal first second) (decider : S.Term) :
    ¬ reflective.reflexive.DecidesEquiv decider :=
  Reflexive.no_equality_decider
    (fun related => distinct ((reflective.equiv_iff first second).mp related)) decider

/-- A term realises a fragment decision of the full equality when, on the
fragment, its answer is truth where the decision says `true` and falsity where
it says `false`. -/
def InternallyRealizes (decision : FragmentDecision reflective.Equal) (decider : S.Term) :
    Prop :=
  ∀ left right (leftIn : decision.Fragment left) (rightIn : decision.Fragment right),
    (decision.answer left right leftIn rightIn = true →
      reflective.reflexive.Equiv
        (reflective.reflexive.apply (reflective.reflexive.apply decider left) right)
        reflective.reflexive.truth) ∧
    (decision.answer left right leftIn rightIn = false →
      reflective.reflexive.Equiv
        (reflective.reflexive.apply (reflective.reflexive.apply decider left) right)
        reflective.reflexive.falsity)

/-- The explicit diagonal of a binary decider against a pair of terms: the
fixed point of "if equal to `yes` then `no` else `yes`". -/
def diagonalTerm (decider yes no : S.Term) : S.Term :=
  reflective.reflexive.decisionDiagonal (Reflexive.equivDecider decider yes) yes no

/-- **Internal carve-outs are proper.**  A fragment decision realised by a term
excludes the diagonal of that term against any fragment term `yes` and any
term `no` the bubble does not equate with it. -/
theorem diagonal_not_mem_fragment (decision : FragmentDecision reflective.Equal)
    {decider : S.Term} (realizes : reflective.InternallyRealizes decision decider)
    {yes no : S.Term} (yesIn : decision.Fragment yes) (distinct : ¬ reflective.Equal yes no) :
    ¬ decision.Fragment (reflective.diagonalTerm decider yes no) := by
  have invariant : ∀ {first second : S.Term}, reflective.reflexive.Equiv first second →
      (reflective.reflexive.Equiv first yes ↔ reflective.reflexive.Equiv second yes) :=
    fun related => ⟨fun held => reflective.reflexive.trans (reflective.reflexive.symm related) held,
      fun held => reflective.reflexive.trans related held⟩
  refine Reflexive.diagonal_not_mem_fragment (A := reflective.reflexive)
    (P := fun value => reflective.reflexive.Equiv value yes) invariant
    (reflective.reflexive.refl yes)
    (fun related => distinct ((reflective.equiv_iff yes no).mp
      (reflective.reflexive.symm related)))
    (Fragment := decision.Fragment) ?_
  intro value valueIn
  have exact := decision.answer_exact value yes valueIn yesIn
  cases answered : decision.answer value yes valueIn yesIn with
  | true =>
      exact Or.inl ⟨(realizes value yes valueIn yesIn).1 answered,
        (reflective.equiv_iff value yes).mpr (exact.mp answered)⟩
  | false =>
      refine Or.inr ⟨(realizes value yes valueIn yesIn).2 answered, fun related => ?_⟩
      have holds := exact.mpr ((reflective.equiv_iff value yes).mp related)
      rw [answered] at holds
      exact Bool.false_ne_true holds

/-- The fragment of an internally realised decision is not everything. -/
theorem fragment_ne_univ (decision : FragmentDecision reflective.Equal)
    {decider : S.Term} (realizes : reflective.InternallyRealizes decision decider)
    {yes no : S.Term} (yesIn : decision.Fragment yes) (distinct : ¬ reflective.Equal yes no) :
    ∃ term, ¬ decision.Fragment term :=
  ⟨_, reflective.diagonal_not_mem_fragment decision realizes yesIn distinct⟩

/-- **The diagonal stays undetermined**: the verdict of an internally realised
fragment decision on the diagonal is `outsideFragment`. -/
theorem diagonal_verdict_outside (decision : FragmentDecision reflective.Equal)
    {decider : S.Term} (realizes : reflective.InternallyRealizes decision decider)
    {yes no : S.Term} (yesIn : decision.Fragment yes) (distinct : ¬ reflective.Equal yes no) :
    decision.verdict (reflective.diagonalTerm decider yes no) yes = .outsideFragment () :=
  decision.verdict_outside fun inside =>
    reflective.diagonal_not_mem_fragment decision realizes yesIn distinct inside.1

/-- **Sound internal verdicts are partial.**  A term that soundly (not
necessarily totally) decides equality with `yes` answers neither truth nor
falsity at its diagonal. -/
theorem sound_undetermined {decider yes no : S.Term} (distinct : ¬ reflective.Equal yes no)
    (sound : reflective.reflexive.SoundlyDecides
      (fun value => reflective.reflexive.Equiv value yes)
      (Reflexive.equivDecider decider yes)) :
    ¬ reflective.reflexive.Equiv
        ((Reflexive.equivDecider decider yes).eval reflective.reflexive.apply
          (reflective.diagonalTerm decider yes no)) reflective.reflexive.truth ∧
      ¬ reflective.reflexive.Equiv
        ((Reflexive.equivDecider decider yes).eval reflective.reflexive.apply
          (reflective.diagonalTerm decider yes no)) reflective.reflexive.falsity :=
  Reflexive.sound_undetermined (A := reflective.reflexive)
    (fun related => ⟨fun held =>
        reflective.reflexive.trans (reflective.reflexive.symm related) held,
      fun held => reflective.reflexive.trans related held⟩)
    (reflective.reflexive.refl yes)
    (fun related => distinct ((reflective.equiv_iff yes no).mp
      (reflective.reflexive.symm related)))
    sound

end ReflectiveBubble

end Mettapedia.GSLT.Reflection
