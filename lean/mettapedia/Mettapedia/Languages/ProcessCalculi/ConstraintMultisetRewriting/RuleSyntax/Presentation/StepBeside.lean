import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Direct

/-!
# A firing of a part is a firing of the whole, on `RuleSyntax.step`

`Spatial.succ_beside` proves this law on the instance-set step (`ProgramAdequacy.program`). Here it is proved on
`RuleSyntax.step` itself at the one frame over ground rows (`groundStep`): two states side by side
(`unionState`: the knowledge of both, the present rows of both, each row with its own label) have the bag of
both (`stateBag_union`); and for a program of the positive fragment, every admitted firing of a state with trivial
knowledge is matched by an admitted firing of the state beside another one, with disjoint identities and trivial
knowledge, whose result's bag is the first result's bag beside the other's (`admitted_beside`), when identities are
infinitely many. The proof reads the firing on bags (`Direct.bag_of_admitted`) and fires again on the larger bag
(`Direct.admitted_of_bag`).

Existence: `beside_holds`, the token state of `Direct`'s examples beside a row `7`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.StepBeside

open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground)
open OneFrame (frames ext)

universe uO

variable {O : Type uO} [DecidableEq O] {rules : List (Rule Rows)}

/-- **Two states side by side**: the knowledge of both, the present rows of both, each with its own label. -/
def unionState (s t : State Rows O) : State Rows O :=
  ⟨PUnit.unit, s.knowledge ++ t.knowledge, s.present ∪ t.present,
    fun o => if o ∈ s.present then s.label o else t.label o⟩

/-- **The bag of two states side by side is the bag of both.** -/
theorem stateBag_union {s t : State Rows O} (apart : Disjoint s.present t.present) :
    stateBag (unionState s t) = stateBag s + stateBag t := by
  show (s.present ∪ t.present).val.map (fun o => if o ∈ s.present then s.label o else t.label o) = _
  rw [val_union_of_disjoint apart, Multiset.map_add]
  congr 1
  · exact Multiset.map_congr rfl fun o member => if_pos (Finset.mem_val.mp member)
  · exact Multiset.map_congr rfl fun o member =>
      if_neg fun inS => Finset.disjoint_left.mp apart inS (Finset.mem_val.mp member)

theorem trivial_union {s t : State Rows O} (knowledgeS : Trivial s.knowledge) (knowledgeT : Trivial t.knowledge) :
    Trivial (unionState s t).knowledge := by
  intro e member
  rcases List.mem_append.mp member with inS | inT
  · exact knowledgeS e inS
  · exact knowledgeT e inT

/-- **A firing of a part is a firing of the whole, on `RuleSyntax.step`**: for a program of the positive
fragment, an admitted firing of a state with trivial knowledge gives an admitted firing of the state beside
another one with disjoint identities and trivial knowledge, whose result's bag is the first result's bag beside
the other's. -/
theorem admitted_beside [Infinite O] (positive : ∀ r ∈ rules, Positive r) {s t : State Rows O}
    (apart : Disjoint s.present t.present) (knowledgeS : Trivial s.knowledge) (knowledgeT : Trivial t.knowledge)
    (g : Firing O (ext ground) {r | r ∈ rules} s.frame) (admitted : (groundStep O rules).Admits (s := s) g) :
    ∃ (g' : Firing O (ext ground) {r | r ∈ rules} (unionState s t).frame)
      (admitted' : (groundStep O rules).Admits (s := unionState s t) g'),
      stateBag ((groundStep O rules).result g' admitted') =
        stateBag ((groundStep O rules).result g admitted) + stateBag t := by
  obtain ⟨member, holds, rest, before, after, -⟩ := bag_of_admitted g admitted
  have split : ((consumes g.rule : List Expr) : Multiset Expr) + (rest + stateBag t) = stateBag (unionState s t) := by
    rw [stateBag_union apart, ← add_assoc, before]
  obtain ⟨g', admitted', bag⟩ :=
    admitted_of_bag member (positive g.rule member) holds (trivial_union knowledgeS knowledgeT) split
  exact ⟨g', admitted', by rw [bag, after, add_assoc]⟩

/-- A row `7` at identity `1`. -/
def sevenState : State Rows ℕ := ⟨PUnit.unit, [], {1}, fun _ => .sym 7⟩

/-- **Existence**: the token state of `Direct`'s examples fires beside a row `7`. -/
theorem beside_holds :
    ∃ (g : Firing ℕ (ext ground) {r | r ∈ Examples.demo} (unionState Examples.tokenState sevenState).frame),
      (groundStep ℕ Examples.demo).Admits (s := unionState Examples.tokenState sevenState) g := by
  obtain ⟨-, g, admitted, -⟩ := Examples.direct_holds (relEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
  obtain ⟨g', admitted', -⟩ := admitted_beside Examples.demo_positive (s := Examples.tokenState)
    (t := sevenState) (by simp [Examples.tokenState, sevenState]) (fun _ member => absurd member List.not_mem_nil)
    (fun _ member => absurd member List.not_mem_nil) g admitted
  exact ⟨g', admitted'⟩

#print axioms stateBag_union
#print axioms admitted_beside
#print axioms beside_holds

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.StepBeside
