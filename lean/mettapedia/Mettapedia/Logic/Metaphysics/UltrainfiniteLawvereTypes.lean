import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalTypeControl
import Mettapedia.Logic.Metaphysics.UltrainfiniteLawvere

/-!
# Why rational types keep the occurs check: every type is a One

`RationalTypeControl.omega_typable` types `Ω` at the rational type `T = T → T`, and
`omega_no_normal_form` shows that `Ω` never stops reducing. This module reads the same cyclic
types through Lawvere's theorem.

**Curry types.** Every rational type `b` has a rational type `C` with `C = C → b`
(`curryType`, `rarrow_curryType`): the solution of `X = X → Y` (`curryVar`, `rarrow_curryVar`)
with `b` substituted for `Y`. `T = T → T` is `loop .arrow` (`loop_arrow_fixed`).

**Every arrow model is trivial** (`ArrowModel.unique_carrier`). An arrow model interprets each
rational type as a type and the arrow as the function type, up to equivalence. At a Curry type
`C = C → b` the carrier of `C` is equivalent to the functions from it into the carrier of `b`, so
by Lawvere's theorem the carrier of `b` is inhabited and has at most one element. So in every arrow
model every rational type, `T = T → T` included, has exactly one element: as propositions, every
type is inhabited. Control: arrow models exist (`ArrowModel.punit`).

**Over finite types the arrow is not degenerate** (`FiniteArrowModel.bool`): the interpretation that
sends constants and variables to `Bool` and the arrow to the function type respects the arrow, and
its base types have two elements. The finite types have no Curry types, because the occurs check
refutes `C = C → b` (`selfApplication_untypable` is the case of `λx. x x`).

So data may be rational, while the types that read it keep the occurs check: a self-containing type
logic inhabits every type and collapses every model in types. The collapse decides equality
classically (`subsingleton_of_surjective`); inhabitation (`nonempty_of_surjective`) does not.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Controls
open Raw (node bot)

universe u

/-! ## Curry types -/

/-- The graph of `X = X → Y`: node `false` is the arrow, with children `false` and `true`; node
`true` is the variable `Y`. -/
def curryGraph : Raw.Graph ctlSig Bool where
  label k := if k then .var (1 : ℕ) else .fn Sym.arrow
  edge k i := if k then true else if i = 0 then false else true

/-- **The rational type `X = X → Y`.** -/
def curryVar : RTree ctlSig :=
  ⟨curryGraph.unfold false, curryGraph.wf_unfold false, curryGraph.rational_unfold false⟩

theorem curryGraph_unfold_true : curryGraph.unfold true = Raw.leaf (1 : ℕ) := by
  rw [curryGraph.unfold_eq true]
  exact Raw.node_congr fun i inside => absurd inside (Nat.not_lt_zero i)

theorem rarrow_curryVar : rarrow curryVar (RTree.leaf (1 : ℕ)) = curryVar := by
  refine RTree.ext ?_
  show node (.fn Sym.arrow) (fun i => if i = 0 then curryGraph.unfold false else Raw.leaf (1 : ℕ)) =
    curryGraph.unfold false
  conv_rhs => rw [curryGraph.unfold_eq false]
  refine Raw.node_congr fun i inside => ?_
  rcases i with _ | _ | i
  · rfl
  · exact curryGraph_unfold_true.symm
  · have : i + 1 + 1 < 2 := inside
    omega

/-- Substitution commutes with the arrow. -/
theorem subst_rarrow (θ : RSubst ctlSig) (a c : RTree ctlSig) :
    RTree.subst θ (rarrow a c) = rarrow (RTree.subst θ a) (RTree.subst θ c) := by
  refine RTree.ext ?_
  show Raw.subst (fun v => (θ v).1) (node (Head.fn (σ := ctlSig) Sym.arrow) fun i => if i = 0 then a.1 else c.1) =
    node (Head.fn (σ := ctlSig) Sym.arrow) fun i => if i = 0 then (RTree.subst θ a).1 else (RTree.subst θ c).1
  rw [Raw.subst_node _ (fun v same => by cases same)]
  congr 1
  funext i
  split_ifs <;> rfl

/-- **The Curry type of `b`**: `C = C → b`. -/
def curryType (b : RTree ctlSig) : RTree ctlSig :=
  RTree.subst (fun _ => b) curryVar

theorem rarrow_curryType (b : RTree ctlSig) : rarrow (curryType b) b = curryType b := by
  have carried := congrArg (RTree.subst fun _ => b) rarrow_curryVar
  rw [subst_rarrow, RTree.subst_leaf] at carried
  exact carried

/-! ## Arrow models -/

/-- **An arrow model** of the rational types: a type for each rational type, with the arrow read as
the function type up to equivalence. -/
structure ArrowModel where
  carrier : RTree ctlSig → Sort u
  arrow : ∀ a b, carrier (rarrow a b) ≃ (carrier a → carrier b)

namespace ArrowModel

variable (M : ArrowModel.{u})

/-- At a Curry type the carrier is equivalent to its functions into the carrier of `b`. -/
def curryEquiv (b : RTree ctlSig) : M.carrier (curryType b) ≃ (M.carrier (curryType b) → M.carrier b) :=
  (Equiv.cast (congrArg M.carrier (rarrow_curryType b))).symm.trans (M.arrow (curryType b) b)

/-- **In an arrow model every rational type is inhabited.** -/
theorem nonempty_carrier (b : RTree ctlSig) : Nonempty (M.carrier b) :=
  nonempty_of_surjective (M.curryEquiv b) (M.curryEquiv b).surjective

/-- **In an arrow model every rational type has exactly one element.** -/
theorem unique_carrier (b : RTree ctlSig) : Nonempty (Unique (M.carrier b)) :=
  let ⟨x⟩ := M.nonempty_carrier b
  ⟨{ default := x
     uniq := fun y => (subsingleton_of_surjective (M.curryEquiv b) (M.curryEquiv b).surjective).elim y x }⟩

/-- In particular the self-containing type `T = T → T`, at which `Ω` is typed, is a One. -/
theorem unique_loop_arrow : Nonempty (Unique (M.carrier (loop .arrow))) :=
  M.unique_carrier _

/-- Control: arrow models exist. -/
def punit : ArrowModel.{u} where
  carrier _ := PUnit
  arrow _ _ := punitEquivArrow

end ArrowModel

/-! ## Finite types -/

/-- **An arrow model of the finite types.** -/
structure FiniteArrowModel where
  carrier : Term ctlSig → Sort u
  arrow : ∀ a b, carrier (arrowT a b) ≃ (carrier a → carrier b)

/-- Constants and variables as `Bool`, the arrow as the function type. -/
def boolCarrier : Term ctlSig → Type
  | .var _ => Bool
  | .const _ => Bool
  | .app .f ts => boolCarrier (ts ⟨0, by decide⟩)
  | .app .g ts => boolCarrier (ts ⟨0, by decide⟩)
  | .app .arrow ts => boolCarrier (ts ⟨0, by decide⟩) → boolCarrier (ts ⟨1, by decide⟩)

/-- **Over finite types the arrow is not degenerate**: an arrow model whose base types have two
elements. -/
def FiniteArrowModel.bool : FiniteArrowModel.{1} where
  carrier := boolCarrier
  arrow _ _ := Equiv.refl _

theorem FiniteArrowModel.bool_nontrivial :
    ∃ a b : FiniteArrowModel.bool.carrier (.const true), a ≠ b :=
  ⟨true, false, Bool.noConfusion⟩

/-- **The contrast**: the finite types have an arrow model with a two-element type; in every arrow
model of the rational types every type has one element. -/
theorem occurs_check_keeps_models :
    (∃ M : FiniteArrowModel.{1}, ∃ a b : M.carrier (.const true), a ≠ b) ∧
      ∀ (M : ArrowModel.{u}) (b : RTree ctlSig), Nonempty (Unique (M.carrier b)) :=
  ⟨⟨_, FiniteArrowModel.bool_nontrivial⟩, fun M b => M.unique_carrier b⟩

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms curryGraph_unfold_true
#print axioms rarrow_curryVar
#print axioms subst_rarrow
#print axioms rarrow_curryType
#print axioms ArrowModel.nonempty_carrier
#print axioms ArrowModel.unique_carrier
#print axioms ArrowModel.unique_loop_arrow
#print axioms ArrowModel.punit
#print axioms FiniteArrowModel.bool
#print axioms FiniteArrowModel.bool_nontrivial
#print axioms occurs_check_keeps_models

end Mettapedia.Logic.Metaphysics.Ultrainfinite
