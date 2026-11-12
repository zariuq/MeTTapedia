import Mettapedia.TypeTheory.KnowledgeSolvedForm

/-!
# A frame does not solve its equations

The conversion of a frame is the congruence closure of what the frame was told. A congruence
closure has no injectivity of constructors: from `succ n ≐ succ 0` it does not derive `n ≐ 0`.

* `Controls.successors_do_not_decompose`: the frame that was told `succ n ≐ succ 0`, with no
  declared step, does not convert `Vec n` with `Vec 0`.
* `Controls.solved_form_converts`: the frame that was told the solved equation `n ≐ 0` does.

In the standard model the two pieces of knowledge say the same. So what a match or a unification
tells a frame has to be the solved equations. Injectivity and the conflict of constructors are
steps of the solver that produces them; they are not part of the frame's conversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeUnsolved

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls

/-- The knowledge `succ n ≐ succ 0` at the frame with the one variable `n`. -/
def knowsSuccessors : EquationStore AExpr := [(succE (bvar 0), succE zeroE)]

/-- Whether a term is a constant. -/
def isConst : AExpr → Bool
  | .const _ _ => true
  | _ => false

/-- Every application of a constant read as one fixed term. -/
def blurConstants : AExpr → AExpr
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (blurConstants A) (blurConstants B)
  | .lam A b => .lam (blurConstants A) (blurConstants b)
  | .app f a => if isConst f then .top else .app (blurConstants f) (blurConstants a)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (blurConstants p) (blurConstants q)
  | .or p q => .or (blurConstants p) (blurConstants q)
  | .imp p q => .imp (blurConstants p) (blurConstants q)
  | .not p => .not (blurConstants p)
  | .eq a b => .eq (blurConstants a) (blurConstants b)
  | .all A b => .all (blurConstants A) (blurConstants b)
  | .ex A b => .ex (blurConstants A) (blurConstants b)

theorem shiftN_succE (t : AExpr) : ∀ depth : Nat, shiftN depth (succE t) = succE (shiftN depth t)
  | 0 => rfl
  | depth + 1 => by
      show shiftAt 0 (shiftN depth (succE t)) = succE (shiftAt 0 (shiftN depth t))
      rw [shiftN_succE t depth]
      rfl

/-- Neither side of a step by the knowledge is a constant. -/
theorem step_not_const {depth : Nat} {e e' : AExpr}
    (step : RewriteUnder
      (fun depth left right => False ∨ assumedAt knowsSuccessors depth left right) depth e e') :
    isConst e = false ∧ isConst e' = false := by
  cases step with
  | root rule =>
      rcases rule with impossible | ⟨equation, member, atLeft, atRight⟩
      · exact impossible.elim
      · obtain rfl := List.mem_singleton.mp member
        rw [atLeft, atRight, shiftN_succE, shiftN_succE]
        exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

/-- A step by the knowledge keeps the reading with the applications of constants blurred. -/
theorem blurConstants_step {depth : Nat} {e e' : AExpr}
    (step : RewriteUnder
      (fun depth left right => False ∨ assumedAt knowsSuccessors depth left right) depth e e') :
    blurConstants e = blurConstants e' := by
  induction step with
  | @root depth left right rule =>
      rcases rule with impossible | ⟨equation, member, atLeft, atRight⟩
      · exact impossible.elim
      · obtain rfl := List.mem_singleton.mp member
        rw [atLeft, atRight, shiftN_succE, shiftN_succE]
        rfl
  | piDomain _ ih => simp only [blurConstants, ih]
  | piBody _ ih => simp only [blurConstants, ih]
  | lamDomain _ ih => simp only [blurConstants, ih]
  | lamBody _ ih => simp only [blurConstants, ih]
  | appFunction inner ih =>
      have apart := step_not_const inner
      simp only [blurConstants, apart.1, apart.2, ih, Bool.false_eq_true, ↓reduceIte]
  | appArgument _ ih => simp only [blurConstants, ih]
  | andLeft _ ih => simp only [blurConstants, ih]
  | andRight _ ih => simp only [blurConstants, ih]
  | orLeft _ ih => simp only [blurConstants, ih]
  | orRight _ ih => simp only [blurConstants, ih]
  | impLeft _ ih => simp only [blurConstants, ih]
  | impRight _ ih => simp only [blurConstants, ih]
  | notBody _ ih => simp only [blurConstants, ih]
  | eqLeft _ ih => simp only [blurConstants, ih]
  | eqRight _ ih => simp only [blurConstants, ih]
  | allDomain _ ih => simp only [blurConstants, ih]
  | allBody _ ih => simp only [blurConstants, ih]
  | exDomain _ ih => simp only [blurConstants, ih]
  | exBody _ ih => simp only [blurConstants, ih]

theorem blurConstants_conv {e e' : AExpr}
    (converted : ConvertibleKnowing (fun _ _ => False) knowsSuccessors e e') :
    blurConstants e = blurConstants e' := by
  induction converted with
  | rel _ _ step => exact blurConstants_step step
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **The frame does not solve its equations**: told `succ n ≐ succ 0`, with no declared step, it
does not convert `Vec n` with `Vec 0`. -/
theorem successors_do_not_decompose :
    ¬ ConvertibleKnowing (fun _ _ => False) knowsSuccessors (vec (bvar 0)) (vec zeroE) := by
  intro converted
  have same := blurConstants_conv converted
  simp [blurConstants, isConst, vec, zeroE] at same

/-- **Told the solved equation, it does**: the frame that knows `n ≐ 0` converts `Vec n` with
`Vec 0`. -/
theorem solved_form_converts :
    ConvertibleKnowing (fun _ _ => False) knowsZero (vec (bvar 0)) (vec zeroE) :=
  Relation.EqvGen.rel _ _
    (RewriteUnder.appArgument
      (RewriteUnder.root (Or.inr ⟨(bvar 0, zeroE), List.mem_singleton_self _, rfl, rfl⟩)))

end Controls

/-! ## Axiom audit -/

#print axioms Controls.blurConstants_conv
#print axioms Controls.successors_do_not_decompose
#print axioms Controls.solved_form_converts

end Mettapedia.TypeTheory.KnowledgeUnsolved
