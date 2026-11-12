import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperScheduleDomain

/-!
# Local exchanges generate every two-source schedule order

Each side retains the complete source event sequence. Adjacent events from
opposite sides generate the equivalence of interleavings. Normalization moves
them to the selected left-then-right order without identifying source events.
Native admission and interpretation of these exchanges are separate results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
variable {S : Signature} {O : Type} [DecidableEq O]

abbrev rightOnly (l : State S O) : {r : State S O} → (second : helperStep.Run r) →
    Schedule (left := l) (right := r) (.nil l) second
  | r, .nil _ => .done l r
  | _, .cons g allowed rest => .right g allowed (rightOnly l rest)

abbrev leftFirst : ∀ {left right : State S O} (first : helperStep.Run left) (second : helperStep.Run right),
    Schedule (left := left) (right := right) first second
  | l, _, .nil _, other => rightOnly l other
  | _, _, .cons f allowed rest, other => .left f allowed (leftFirst rest other)

inductive Swap : {left right : State S O} → {first : helperStep.Run left} → {second : helperStep.Run right} →
    Schedule first second → Schedule first second → Prop
  | here {left right : State S O} (f : Firing left) (af : helperStep.Admits f)
      (g : Firing right) (ag : helperStep.Admits g)
      {restL : helperStep.Run f.after} {restR : helperStep.Run g.after}
      (tail : Schedule (left := f.after) (right := g.after) restL restR) :
      Swap (.left f af (.right g ag tail)) (.right g ag (.left f af tail))
  | left {l r : State S O} (f : Firing l) (af : helperStep.Admits f)
      {rest : helperStep.Run f.after} {other : helperStep.Run r}
      {a b : Schedule (left := f.after) (right := r) rest other}
      (swapped : Swap a b) : Swap (.left f af a) (.left f af b)
  | right {l r : State S O} (g : Firing r) (ag : helperStep.Admits g)
      {other : helperStep.Run l} {rest : helperStep.Run g.after}
      {a b : Schedule (left := l) (right := g.after) other rest}
      (swapped : Swap a b) : Swap (.right g ag a) (.right g ag b)

abbrev Equivalent {left right : State S O} (first : helperStep.Run left) (second : helperStep.Run right) :=
  Relation.EqvGen (Swap (first := first) (second := second))

theorem Equivalent.left {left right : State S O} (f : Firing left) (af : helperStep.Admits f)
    {rest : helperStep.Run f.after} {other : helperStep.Run right} {a b : Schedule rest other}
    (related : Equivalent rest other a b) : Equivalent (.cons f af rest) other (.left f af a) (.left f af b) := by
  induction related with
  | rel _ _ swapped => exact .rel _ _ (.left f af swapped)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem Equivalent.right {left right : State S O} (g : Firing right) (ag : helperStep.Admits g)
    {other : helperStep.Run left} {rest : helperStep.Run g.after} {a b : Schedule other rest}
    (related : Equivalent other rest a b) : Equivalent other (.cons g ag rest) (.right g ag a) (.right g ag b) := by
  induction related with
  | rel _ _ swapped => exact .rel _ _ (.right g ag swapped)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem bubbleRight : ∀ {left right : State S O} (first : helperStep.Run left)
    (g : Firing right) (ag : helperStep.Admits g) (rest : helperStep.Run g.after),
    Equivalent first (.cons g ag rest) (.right g ag (leftFirst first rest)) (leftFirst first (.cons g ag rest))
  | _, _, .nil _, _, _, _ => .refl _
  | _, _, .cons f af tail, g, ag, rest =>
      .trans _ _ _ (.symm _ _ (.rel _ _ (.here f af g ag (leftFirst tail rest))))
        ((bubbleRight tail g ag rest).left f af)

theorem normalizes : ∀ {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (schedule : Schedule first second), Equivalent first second schedule (leftFirst first second)
  | _, _, _, _, .done _ _ => .refl _
  | _, _, _, _, .left f af tail => (normalizes tail).left f af
  | _, _, first, _, .right g ag tail =>
      .trans _ _ _ ((normalizes tail).right g ag) (bubbleRight first g ag _)

theorem all_orders_equivalent {left right : State S O} {first : helperStep.Run left} {second : helperStep.Run right}
    (one two : Schedule first second) : Equivalent first second one two :=
  .trans _ _ _ (normalizes one) (.symm _ _ (normalizes two))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Schedule
