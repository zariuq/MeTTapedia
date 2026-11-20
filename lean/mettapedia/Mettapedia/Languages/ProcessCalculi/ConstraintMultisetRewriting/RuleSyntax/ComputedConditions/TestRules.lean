import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.MachineRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Evaluation

/-!
# Two more rules of the machine of transform rules, with their helpers as tables

**A test.** The rule of the machine's library for a returned value that is a partial application:

```
(pm:rule! (ret pm:k-rest)
  (, (take (pm:state (pm:ret $v) (pm:k (pm:k-rest $id $rest) $k) $d $r))
     (let True (pm:is-partial $v)))
  (pm:state (pm:rev pm:nil (pm:items $v $rest) (pm:mk-apply)) $k $d $r))
```

Its condition's value pattern is the constant `True`. Transcribed as `retPartial` (symbols as in
`MachineRule`, and `pm:k` `120`, `pm:k-rest` `121`, `pm:mk-apply` `122`, `pm:is-partial` `123`, `True` `124`,
`False` `125`, `partial` `126`). `retPartial_table_admitted`: with the row
`pm:is-partial (partial g ()) True` stored, the table read fires, obtained from the point reading through
`tableFiring_admits_iff`. `retPartial_refuses_false`: at a point whose value is `False` the rule at the point
is admitted at no state.

**Control: a test of whether the values still hold a variable is not a table read.** The rule

```
(pm:rule! (ctl pm:rev)
  (, (take (pm:state (pm:rev pm:nil $acc (pm:mk-prim $f)) $k $d $r))
     (let open (pm:open-items $acc))
     (let $values (pm:list-of $acc)))
  (pm:state (pm:effect (pm:host $f $values)) $k $d $r))
```

tests the value `open` of `pm:open-items`, which the library defines to answer `open` only when one of the
values holds a variable. Transcribed as `primOpen` (`pm:mk-prim` `130`, `pm:effect` `131`, `pm:host` `132`,
`pm:open-items` `133`, `open` `134`, `closed` `135`, `pm:list-of` `136`). `primOpen_never_fires`,
`primOpen_table_never_fires`: for every interpretation that answers `closed` at every ground argument of
`pm:open-items`, neither the rule at points of the graph nor the table read over rows of the graph is
admitted, at any state, with any choices. A function of ground arguments cannot answer `open`, so this
condition is no condition of the five kinds read as tables; what it asks of the store is stated in
`OpenValues`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.TestRules

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Presentation.Schematic (Tm SRule SState GroundLabels X E rowSig toTerm toTerm_injective applyTerm_toTerm inst
  lift)
open KernelStep (k v)
open MachineRule (state rev ret)

/-! ## A test -/

/-- `(pm:k (pm:k-rest ID REST) K)`. -/
def kRest (id rest continuation : Tm) : Tm := spine (k 120) [spine (k 121) [id, rest], continuation]

/-- **The rule**, with its condition `True := pm:is-partial(0)`. Unknowns: `0` the value, `1` the
identifier, `2` the rest, `3` the continuation, `4` the depth, `5` the alternatives. -/
def retPartial : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[state (ret (v 0)) (kRest (v 1) (v 2) (v 3)) (v 4) (v 5)], [], [], [],
    [state (rev (spine (k 107) [v 0, v 2]) (k 122)) (v 3) (v 4) (v 5)]⟩, []⟩
  conditions := [⟨k 124, 123, [v 0]⟩]

/-- `(partial g ())`. -/
def partialG : Expr := groundSpine (.sym 126) [.sym 110, .sym 102]

/-- The rows: the state that returns `(partial g ())` to a rest, and the row of `pm:is-partial`'s table. -/
def rowsAt : ℕ → Expr
  | 0 => groundSpine (.sym 100) [groundSpine (.sym 104) [partialG],
      groundSpine (.sym 120) [groundSpine (.sym 121) [.sym 7, .sym 102], .sym 106], .sym 108, .sym 102]
  | _ => groundRow 123 [partialG] (.sym 124)

/-- The machine state, with the table row stored. -/
def machine : SState ℕ := ⟨PUnit.unit, [], Finset.range 2, fun o => toTerm (rowsAt o)⟩

theorem machine_ground : GroundLabels machine rowsAt := fun _ _ => rfl

/-- The match. -/
def θ : ℕ → Expr
  | 0 => partialG
  | 1 => .sym 7
  | 2 => .sym 102
  | 3 => .sym 106
  | 4 => .sym 108
  | _ => .sym 102

/-- The point `pm:is-partial((partial g ())) = True`. -/
def points : List EvalPoint := [([partialG], .sym 124)]

/-- The choices: the state taken, the table row `1`, the made identity `2`. -/
def choice : Choice ℕ (Subst rowSig) := ⟨Subst.id rowSig, [0], [], [1], [2], []⟩

/-- The rule at the point fires. -/
theorem retPartial_point_admitted :
    (step X ℕ E {retPartial.at rows (retPartial.pointRows points)}).Admits (s := machine)
      (pointFiring (A := Presentation.Schematic.A) retPartial (retPartial.pointRows points) (Set.mem_singleton _)
        choice) := by
  refine (admits_iff _).mpr ⟨identity_fresh machine_ground rfl _ rfl, ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨PUnit.unit, lift θ, models_lift machine_ground (fun _ inside => absurd inside List.not_mem_nil) _ rfl θ
      ?_ ?_ ?_⟩, fun c inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pointFiring, choice, machine, Selection.commit]
  · intro x inside
    simp only [pointFiring, choice, RuleWithCondition.at_take, retPartial, List.zip_cons_cons, List.zip_nil_left,
      List.mem_singleton] at inside
    subst inside
    exact ⟨by simp [machine], rfl⟩
  · intro x inside
    exact absurd inside List.not_mem_nil
  · intro pair inside
    simp only [pointFiring, RuleWithCondition.at_tell, retPartial, RuleWithCondition.calls,
      RuleWithCondition.pointRows, points, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
      List.append_nil, List.mem_singleton] at inside
    subst inside
    show inst θ (callRow rows ⟨k 124, 123, [v 0]⟩) = inst θ (toTerm (groundRow 123 [partialG] (.sym 124)))
    rw [Presentation.Schematic.inst_toTerm]
    rfl

/-- **The table read fires**, from the point reading through `tableFiring_admits_iff`. -/
theorem retPartial_table_admitted :
    (step X ℕ E {retPartial.tableRule rows}).Admits (s := machine)
      (tableFiring (A := Presentation.Schematic.A) retPartial (Set.mem_singleton _) choice) :=
  (tableFiring_admits_iff machine retPartial (Set.mem_singleton _) (retPartial.pointRows points)
    (Set.mem_singleton _) choice rfl rfl (fun g inside => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp inside
      exact fixed_toTerm _)).mpr
    ⟨retPartial_point_admitted, fun o inside => by
      rw [show choice.tables = [1] from rfl, List.mem_singleton] at inside
      subst inside
      exact ⟨by simp [machine], by simp [choice]⟩⟩

/-- **At a point whose value is `False` the rule is admitted at no state.** -/
theorem retPartial_refuses_false {O : Type} [DecidableEq O] (s : SState O) (argument : Expr)
    {Q : Program (OneFrame.Terms Tm)}
    (mP : retPartial.at rows (retPartial.pointRows [([argument], .sym 125)]) ∈ Q) (c : Choice O (Subst rowSig)) :
    ¬ (step X O E Q).Admits (s := s)
      (pointFiring (A := Presentation.Schematic.A) retPartial (retPartial.pointRows [([argument], .sym 125)])
        mP c) := by
  intro admitted
  obtain ⟨-, -, -, ⟨_, σ, solved⟩, -⟩ := (admits_iff _).mp admitted
  have calls := ((models_point_iff s retPartial [([argument], .sym 125)] mP c σ).mp solved).2.2
  have call := calls (callRow rows ⟨k 124, 123, [v 0]⟩, pointRow ⟨k 124, 123, [v 0]⟩ ([argument], .sym 125))
    List.mem_cons_self
  have value := ((callRow_point_iff c σ (d := ⟨k 124, 123, [v 0]⟩) (pt := ([argument], .sym 125)) rfl).mp call).2
  exact absurd (toTerm_injective (show toTerm (.sym 124) = toTerm (.sym 125) from value)) (by decide)

/-! ## Control: a test of `open` -/

/-- **The rule**, with its conditions `open := pm:open-items(0)` and `5 := pm:list-of(0)`. Unknowns: `0` the
collected values, `1` the operation, `2` the continuation, `3` the depth, `4` the alternatives, `5` the
list of values. -/
def primOpen : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[state (rev (v 0) (spine (k 130) [v 1])) (v 2) (v 3) (v 4)], [], [], [],
    [state (spine (k 131) [spine (k 132) [v 1, v 5]]) (v 2) (v 3) (v 4)]⟩, []⟩
  conditions := [⟨k 134, 133, [v 0]⟩, ⟨v 5, 136, [v 0]⟩]

section Never

variable {O : Type} [DecidableEq O] (I : Interpretation ℕ Expr)
  (closedOnly : ∀ args value, I 133 args = some value → value = .sym 135)
  (s : SState O) (first second : EvalPoint) (answers : I 133 first.1 = some first.2)
  (oneArgument : first.1.length = 1) (c : Choice O (Subst rowSig))

include closedOnly answers oneArgument in
/-- **The rule at points of the graph is admitted at no state**, when `pm:open-items` answers `closed` at
every ground argument. -/
theorem primOpen_never_fires {Q : Program (OneFrame.Terms Tm)}
    (mP : primOpen.at rows (primOpen.pointRows [first, second]) ∈ Q) :
    ¬ (step X O E Q).Admits (s := s)
      (pointFiring (A := Presentation.Schematic.A) primOpen (primOpen.pointRows [first, second]) mP c) := by
  intro admitted
  obtain ⟨-, -, -, ⟨_, σ, solved⟩, -⟩ := (admits_iff _).mp admitted
  have calls := ((models_point_iff s primOpen [first, second] mP c σ).mp solved).2.2
  have call := calls (callRow rows ⟨k 134, 133, [v 0]⟩, pointRow ⟨k 134, 133, [v 0]⟩ first) List.mem_cons_self
  have value := ((callRow_point_iff c σ (d := ⟨k 134, 133, [v 0]⟩) (pt := first) oneArgument).mp call).2
  rw [closedOnly _ _ answers] at value
  exact absurd (toTerm_injective (show toTerm (.sym 134) = toTerm (.sym 135) from value)) (by decide)

include closedOnly answers oneArgument in
/-- **The table read over rows of the graph is admitted at no state**, through `tableFiring_admits_iff`. -/
theorem primOpen_table_never_fires {P : Program (OneFrame.Terms Tm)} (mT : primOpen.tableRule rows ∈ P)
    (labels : c.tables.map s.label = primOpen.pointRows [first, second]) :
    ¬ (step X O E P).Admits (s := s) (tableFiring (A := Presentation.Schematic.A) primOpen mT c) := fun admitted =>
  primOpen_never_fires I closedOnly s first second answers oneArgument c (Set.mem_singleton _)
    ((tableFiring_admits_iff s primOpen mT (primOpen.pointRows [first, second]) (Set.mem_singleton _) c labels rfl
      (fun g inside => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp inside
        exact fixed_toTerm _)).mp admitted).1

end Never

#print axioms retPartial_point_admitted
#print axioms retPartial_table_admitted
#print axioms retPartial_refuses_false
#print axioms primOpen_never_fires
#print axioms primOpen_table_never_fires

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.TestRules
