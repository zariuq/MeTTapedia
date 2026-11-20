import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelStep

/-!
# A rule of the machine of transform rules, with its helper as a table

The rule of the machine's library for the end of a data constructor's arguments:

```
(pm:rule! (ctl pm:rev)
  (, (take (pm:state (pm:rev pm:nil $acc (pm:mk-data $f)) $k $d $r))
     (let $v (pm:expression $f $acc)))
  (pm:state (pm:ret $v) $k $d $r))
```

Its helper `pm:expression` is a function of its arguments (the library defines it by one equation from
`pm:list-of` and `cons-atom`, reading nothing of the store). Transcribed over rows with unknowns, with a
symbol for each name of the library (`pm:state` `100`, `pm:rev` `101`, `pm:nil` `102`, `pm:mk-data`
`103`, `pm:ret` `104`, `pm:expression` `105`, `pm:halt` `106`, `pm:items` `107`, the depth `z` `108`),
the rule is `dataEnd`, with the condition `5 := pm:expression(1, 0)`.

* `dataEnd_restricted`, `dataEndTable_fragment`: its value is bound by the condition and the rest by the
  take, so its table read is in the presentation's fragment.
* `dataEnd_fires`: at the machine state that has collected the item `7` for the constructor `g`, beside
  the row of `pm:expression`'s table `pm:expression g (pm:items 7 pm:nil) (g 7)`, `RuleSyntax.step` admits
  the table read, and its result reads as the state that returns `(g 7)`, beside the table row.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.MachineRule

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SRule SState GroundLabels TrivialKnowledge ReadsAs schematicStep E toTerm inst
  Bound written RangeRestrictedPositive equationsOf mem_vars_var not_mem_vars_const admitted_of_match)
open KernelStep (k v)

/-- `(pm:state CONTROL K D R)`. -/
def state (control continuation depth alternatives : Tm) : Tm :=
  spine (k 100) [control, continuation, depth, alternatives]

/-- `(pm:rev pm:nil ACC MAKER)`. -/
def rev (acc maker : Tm) : Tm := spine (k 101) [k 102, acc, maker]

/-- `(pm:mk-data F)`. -/
def mkData (f : Tm) : Tm := spine (k 103) [f]

/-- `(pm:ret V)`. -/
def ret (value : Tm) : Tm := spine (k 104) [value]

/-- **The rule**, with its computed condition `5 := pm:expression(1, 0)`. Unknowns: `0` the collected
items, `1` the constructor, `2` the continuation, `3` the depth, `4` the alternatives, `5` the value. -/
def dataEnd : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[state (rev (v 0) (mkData (v 1))) (v 2) (v 3) (v 4)], [], [], [],
    [state (ret (v 5)) (v 2) (v 3) (v 4)]⟩, []⟩
  conditions := [⟨v 5, 105, [v 1, v 0]⟩]

/-- Its table read. -/
abbrev dataEndTable : SRule := dataEnd.tableRule rows

/-- The program of the table read. -/
abbrev dataEndProgram : List SRule := [dataEndTable]

/-- The unknowns of a spine at a symbol are those of its arguments. -/
theorem vars_spine_symbol {x n : ℕ} {ts : List Tm} (inside : x ∈ (spine (k n) ts).freeVars) :
    ∃ t ∈ ts, x ∈ t.freeVars := by
  rcases (mem_vars_spine _ _).mp inside with inHead | found
  · exact absurd inHead not_mem_vars_const
  · exact found

/-- The take pattern mentions the unknowns `0` to `4`. -/
theorem take_mentions {x : ℕ} (small : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) :
    x ∈ (state (rev (v 0) (mkData (v 1))) (v 2) (v 3) (v 4)).freeVars := by
  have var : x ∈ (v x).freeVars := mem_vars_var.mpr rfl
  rcases small with rfl | rfl | rfl | rfl | rfl
  · exact (mem_vars_spine _ _).mpr (.inr ⟨_, List.mem_cons_self, (mem_vars_spine _ _).mpr
      (.inr ⟨v 0, by simp, var⟩)⟩)
  · exact (mem_vars_spine _ _).mpr (.inr ⟨_, List.mem_cons_self, (mem_vars_spine _ _).mpr
      (.inr ⟨mkData (v 1), by simp, (mem_vars_spine _ _).mpr (.inr ⟨v 1, by simp, var⟩)⟩)⟩)
  · exact (mem_vars_spine _ _).mpr (.inr ⟨v 2, by simp, var⟩)
  · exact (mem_vars_spine _ _).mpr (.inr ⟨v 3, by simp, var⟩)
  · exact (mem_vars_spine _ _).mpr (.inr ⟨v 4, by simp, var⟩)

theorem dataEnd_restricted : dataEnd.RangeRestrictedWith := by
  intro t member x inT
  have made : t = state (ret (v 5)) (v 2) (v 3) (v 4) := by simpa [written, dataEnd, checkTerms] using member
  subst made
  obtain ⟨u, inArgs, inU⟩ := vars_spine_symbol inT
  have takeBound : ∀ y, (y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4) → dataEnd.Binds y := fun y small =>
    .inl ⟨_, List.mem_append_left _ (List.mem_singleton_self _), take_mentions small⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inArgs
  rcases inArgs with rfl | rfl | rfl | rfl
  · obtain ⟨w, inW, inX⟩ := vars_spine_symbol inU
    rw [List.mem_singleton.mp inW] at inX
    rw [mem_vars_var.mp inX]
    exact .inr ⟨⟨v 5, 105, [v 1, v 0]⟩, List.mem_singleton_self _, mem_vars_var.mpr rfl⟩
  · exact takeBound x (by rw [mem_vars_var.mp inU]; simp)
  · exact takeBound x (by rw [mem_vars_var.mp inU]; simp)
  · exact takeBound x (by rw [mem_vars_var.mp inU]; simp)

theorem dataEndTable_fragment : RangeRestrictedPositive dataEndTable :=
  dataEnd.fragment_tableRule rfl rfl dataEnd_restricted

theorem dataEndProgram_fragment : ∀ r ∈ dataEndProgram, RangeRestrictedPositive r := by
  intro r member
  rw [List.mem_singleton.mp member]
  exact dataEndTable_fragment

/-! ## A machine state -/

/-- `(pm:items 7 pm:nil)`: the collected item `7`. -/
def itemsSeven : Expr := groundSpine (.sym 107) [.sym 7, .sym 102]

/-- The constructor `g`. -/
abbrev g : Expr := .sym 110

/-- `(g 7)`. -/
def gSeven : Expr := .app g (.sym 7)

/-- The ground state `(pm:state CONTROL pm:halt z pm:nil)`. -/
def stateE (control : Expr) : Expr := groundSpine (.sym 100) [control, .sym 106, .sym 108, .sym 102]

/-- The rows: the state that has collected `7` for `g`, and the row of `pm:expression`'s table. -/
def rowsAt : ℕ → Expr
  | 0 => stateE (groundSpine (.sym 101) [.sym 102, itemsSeven, groundSpine (.sym 103) [g]])
  | _ => groundRow 105 [g, itemsSeven] gSeven

/-- The machine state, with the table row stored. -/
def machine : SState ℕ := ⟨PUnit.unit, [], Finset.range 2, fun o => toTerm (rowsAt o)⟩

/-- The match. -/
def θ : ℕ → Expr
  | 0 => itemsSeven
  | 1 => g
  | 2 => .sym 106
  | 3 => .sym 108
  | 4 => .sym 102
  | _ => gSeven

/-- **The table read fires at the machine state** and its result reads as the state that returns `(g 7)`,
beside the table row. -/
theorem dataEnd_fires :
    ∃ (f : Firing ℕ E {r | r ∈ dataEndProgram} machine.frame)
      (admitted : (schematicStep ℕ dataEndProgram).Admits (s := machine) f),
      f.rule = dataEndTable ∧
        ReadsAs ((schematicStep ℕ dataEndProgram).result f admitted)
          ((([stateE (groundSpine (.sym 104) [gSeven])] : List Expr) : Multiset Expr) + ([rowsAt 1] : List Expr)) := by
  have split : ((dataEndTable.body.take.map (inst θ) : List Expr) : Multiset Expr) +
      (([rowsAt 1] : List Expr) : Multiset Expr) = machine.present.val.map rowsAt := rfl
  have reads : ∀ q ∈ dataEndTable.body.read, inst θ q ∈ (([rowsAt 1] : List Expr) : Multiset Expr) := by
    intro q member
    simp only [dataEndTable, RuleWithCondition.tableRule_read, dataEnd, RuleWithCondition.calls, List.map_cons,
      List.map_nil, List.nil_append, List.mem_singleton] at member
    subst member
    rw [Multiset.mem_coe]
    decide
  have equations : ∀ eq ∈ equationsOf dataEndTable, inst θ eq.1 = inst θ eq.2 := by
    intro eq member
    simp [equationsOf, dataEndTable, dataEnd, RuleWithCondition.tableRule] at member
  exact admitted_of_match (fun _ _ => rfl) (fun _ inside => absurd inside List.not_mem_nil)
    (List.mem_singleton_self _) dataEndTable_fragment split reads equations

#print axioms dataEnd_restricted
#print axioms dataEndTable_fragment
#print axioms dataEnd_fires

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.MachineRule
