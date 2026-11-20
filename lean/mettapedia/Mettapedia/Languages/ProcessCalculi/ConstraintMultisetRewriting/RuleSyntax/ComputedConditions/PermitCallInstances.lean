import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.PermitCalls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.CallInstances

/-!
# Rules that answer, and the call that asks once at instances

**Rules that answer.**

* `defined_answers`: the equation of a function defined by one equation with distinct parameters
  (`Calls.Defined`) answers its interpretation.
* `Equation`: a function defined by one equation with PATTERN parameters, `f(π₁, …, πₙ) = body`. It has a
  value exactly at the instances of its parameters (`Equation.interp_match`, `Equation.interp_none`); its
  equation as a rule (`Equation.rule`) answers its interpretation (`Equation.answers`) and is in the fragment
  (`Equation.rule_fragment`).

**A function with a value everywhere** (`CallInstances.wrap`, `CallInstances.boxItem`): from the bag `item 7`
beside its permit, the call reaches by internal firings and one resume a bag related to the atomic result
`out (box 7)` (`boxItem_permit_called`); its internal firings stop (`boxItem_internal_stops`); and the call and
the atomic evaluation correspond on states of `RuleSyntax.step` (`boxItem_step`).

**A function with no value at some arguments** (`predEq`: `pred(s x) = x`; the rule `unPred`: take `item x`,
let `r := pred(x)`, make `out r`): at `item 0` the atomic evaluation is refused (`pred_refused`); the request
fires and leaves the pending row `ask pred 0` (`pred_request_fires`); and that row is in every bag of every
run of the call from there (`pred_waits`). At `item (s 5)` the function has the value `5` (`pred_defined`).

**Control: arguments that the trigger does not determine** (`twoCells`, `request_loses_cover`): the rule takes
`tok`, reads `cell x` and asks `f(x)`, so the argument comes from a read row. At the bag `tok, cell 1, cell 2`
with the permit of `tok`, a request at `cell 1` leaves a bag that is not related to the atomic bag: the row
`tok` is no longer covered at the argument `2`, where the atomic evaluation may still fire.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.PermitCalls

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SRule inst inst_congr agree_of_inst_eq equationsOf RangeRestrictedPositive
  written mem_vars_var not_mem_vars_const)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Rewrites)
open CallInstances (k askSym wrap wrapCall boxItem item out box spineHead_inst_spine boxItem_evaluates)

/-! ## Rules that answer -/

/-- **The equation of a function defined by one equation answers its interpretation.** -/
theorem defined_answers (askSym : ℕ) (d : Defined) : Answers askSym d.interp d.name [equationRule askSym d] where
  sound := by
    intro C C' fires
    obtain ⟨r, member, θ, rest, rfl, -, -, rfl⟩ := fires
    obtain rfl := List.mem_singleton.mp member
    refine ⟨d.params.map θ, inst θ d.body, rest, ?_, ?_, ?_⟩
    · rw [d.interp_eq (List.length_map _), ← d.inst_body θ]
    · simp only [equationRule, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_askRow, List.map_map]
      rfl
    · simp only [equationRule, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_row, List.map_map]
      rfl
  complete := by
    intro args v rest value
    have lengths : args.length = d.params.length := by
      by_contra wrong
      simp [Defined.interp, wrong] at value
    rw [d.interp_eq lengths] at value
    obtain rfl := Option.some.inj value
    have paramsMap := map_bindParams d.params args d.distinct lengths.symm
    refine ⟨equationRule askSym d, List.mem_singleton_self _, bindParams d.params args, rest, ?_,
      fun x inside => absurd inside List.not_mem_nil, fun e inside => ?_, ?_⟩
    · simp only [equationRule, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_askRow, List.map_map]
      show {groundAsk askSym d.name (d.params.map (bindParams d.params args))} + rest = _
      rw [paramsMap]
    · simp [equationsOf, equationRule] at inside
    · simp only [equationRule, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_row, List.map_map]
      show _ = ({groundRow d.name (d.params.map (bindParams d.params args)) _} : Multiset Expr) + _
      rw [paramsMap]

/-- **A function defined by one equation with pattern parameters**: `name(π₁, …, πₙ) = body`, the body's
unknowns among the parameters'. -/
structure Equation where
  name : ℕ
  params : List Tm
  body : Tm
  closed : ∀ x ∈ body.freeVars, ∃ π ∈ params, x ∈ π.freeVars

namespace Equation

variable (q : Equation)

open Classical in
/-- **Its interpretation**: at an instance of the parameters, the body at that instance; elsewhere no value. -/
noncomputable def interp (g : ℕ) (args : List Expr) : Option Expr :=
  if h : g = q.name ∧ ∃ θ : ℕ → Expr, q.params.map (inst θ) = args then some (inst (Classical.choose h.2) q.body)
  else none

/-- **At an instance of the parameters the value is the body at that instance.** -/
theorem interp_match (θ : ℕ → Expr) : q.interp q.name (q.params.map (inst θ)) = some (inst θ q.body) := by
  unfold interp
  split
  · rename_i h
    congr 1
    refine inst_congr q.body fun x inBody => ?_
    obtain ⟨π, inParams, inπ⟩ := q.closed x inBody
    exact agree_of_inst_eq π (List.map_inj_left.mp (Classical.choose_spec h.2) π inParams) x inπ
  · rename_i h
    exact absurd ⟨rfl, θ, rfl⟩ h

/-- **Where the arguments are no instance of the parameters there is no value.** -/
theorem interp_none {args : List Expr} (noMatch : ∀ θ : ℕ → Expr, q.params.map (inst θ) ≠ args) :
    q.interp q.name args = none := by
  unfold interp
  split
  · rename_i h
    obtain ⟨θ, same⟩ := h.2
    exact absurd same (noMatch θ)
  · rfl

/-- **A value is the body at a match of the parameters.** -/
theorem interp_some {g : ℕ} {args : List Expr} {v : Expr} (value : q.interp g args = some v) :
    g = q.name ∧ ∃ θ : ℕ → Expr, q.params.map (inst θ) = args ∧ v = inst θ q.body := by
  unfold interp at value
  split at value
  · rename_i h
    exact ⟨h.1, Classical.choose h.2, Classical.choose_spec h.2, (Option.some.inj value).symm⟩
  · exact absurd value (by simp)

/-- **The equation as a rule**: take a pending row at the parameters, make the row of the table at the
body. -/
def rule (askSym : ℕ) : SRule :=
  ⟨PUnit.unit, ⟨[askRow askSym q.name q.params], [], [], [], [rows.row q.name q.params q.body]⟩, []⟩

/-- **The equation answers its interpretation.** -/
theorem answers (askSym : ℕ) : Answers askSym q.interp q.name [q.rule askSym] where
  sound := by
    intro C C' fires
    obtain ⟨r, member, θ, rest, rfl, -, -, rfl⟩ := fires
    obtain rfl := List.mem_singleton.mp member
    refine ⟨q.params.map (inst θ), inst θ q.body, rest, q.interp_match θ, ?_, ?_⟩
    · simp only [rule, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_askRow]
    · simp only [rule, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_row]
  complete := by
    intro args v rest value
    obtain ⟨-, θ, rfl, rfl⟩ := q.interp_some value
    refine ⟨q.rule askSym, List.mem_singleton_self _, θ, rest, ?_,
      fun x inside => absurd inside List.not_mem_nil, fun e inside => ?_, ?_⟩
    · simp only [rule, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_askRow]
    · simp [equationsOf, rule] at inside
    · simp only [rule, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_row]

/-- **The equation's rule is in the fragment.** -/
theorem rule_fragment (askSym : ℕ) : RangeRestrictedPositive (q.rule askSym) := by
  refine ⟨rfl, rfl, fun t member x inT => ?_⟩
  have isRow : t = rows.row q.name q.params q.body := by
    simpa [written, rule] using member
  subst isRow
  have inParams : ∃ π ∈ q.params, x ∈ π.freeVars := by
    rcases (mem_vars_callRow ⟨q.body, q.name, q.params⟩).mp inT with inArguments | inBody
    · exact inArguments
    · exact q.closed x inBody
  exact ⟨askRow askSym q.name q.params, List.mem_singleton_self _,
    (mem_vars_askRow askSym q.name _).mpr inParams⟩

end Equation

/-! ## A function with a value everywhere -/

/-- The symbol of permit rows. -/
abbrev permitSym : ℕ := 23

/-- A row headed by a symbol other than the call's three is none of the call's own. -/
theorem not_hidden_of_head {e : Expr} {n f : ℕ} (head : spineHead e = .sym n) (notPermit : permitSym ≠ n)
    (notAsk : askSym ≠ n) (notTable : f ≠ n) : ¬ Hidden askSym permitSym f e := by
  rintro (permit | pending | table)
  · exact notPermit (headed_inj permit head)
  · exact notAsk (headed_inj pending head)
  · exact notTable (headed_inj table head)

theorem wrap_apart : Apart askSym permitSym wrapCall.name := ⟨by decide, by decide, by decide⟩

theorem boxItem_unseen : ∀ θ : ℕ → Expr,
    ∀ q ∈ boxItem.rule.body.take ++ boxItem.rule.body.read ++ boxItem.rule.body.produce,
      ¬ Hidden askSym permitSym wrapCall.name (inst θ q) := by
  intro θ q inside
  simp only [boxItem, List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
    or_false] at inside
  rcases inside with rfl | rfl
  · exact not_hidden_of_head (spineHead_inst_spine θ 40 _) (by decide) (by decide) (by decide)
  · exact not_hidden_of_head (spineHead_inst_spine θ 41 _) (by decide) (by decide) (by decide)

/-- The trigger `item x` holds the argument's unknown. -/
theorem item_bound : ∀ t ∈ wrapCall.arguments, ∀ x ∈ t.freeVars, x ∈ (spine (k 40) [.var 0]).freeVars := by
  intro t inArguments x inT
  rw [List.mem_singleton.mp inArguments] at inT
  exact (mem_vars_spine _ _).mpr (.inr ⟨.var 0, List.mem_singleton_self _, inT⟩)

theorem item_clean (n f : ℕ) (notTable : f ≠ 40) : ∀ e ∈ ({item n} : Multiset Expr), ¬ Hidden askSym permitSym f e := by
  intro e inside
  rw [Multiset.mem_singleton.mp inside]
  exact not_hidden_of_head (spineHead_groundSpine _ _) (by decide) (by decide) notTable

/-- **The call that asks once reaches a bag related to the atomic result**: from `item 7` beside its permit,
internal firings and then the resume. -/
theorem boxItem_permit_called :
    ∃ C₁ C', Relation.ReflTransGen
        (Internal askSym permitSym boxItem wrapCall (spine (k 40) [.var 0]) [equationRule askSym wrap])
        ({item 7} + ({item 7} : Multiset Expr).map (groundPermit permitSym)) C₁ ∧
      Rewrites [permitResume permitSym boxItem] C₁ C' ∧
      PermitRelated askSym permitSym wrap.interp wrapCall (spine (k 40) [.var 0]) {out (box (.sym 7))} C' :=
  related_atomic wrap_apart rfl (List.mem_singleton_self _) item_bound boxItem_unseen
    (defined_answers askSym wrap) (related_start (item_clean 7 _ (by decide))) boxItem_evaluates

/-- **Its internal firings stop.** -/
theorem boxItem_internal_stops :
    WellFounded (fun C' C : Multiset Expr =>
      Internal askSym permitSym boxItem wrapCall (spine (k 40) [.var 0]) [equationRule askSym wrap] C C') :=
  internal_terminates wrap_apart (defined_answers askSym wrap)

theorem boxItem_restricted : boxItem.RangeRestrictedWith := by
  intro t member x inT
  have isOut : t = spine (k 41) [.var 1] := by simpa [written, boxItem] using member
  subst isOut
  rcases (mem_vars_spine _ _).mp inT with inHead | ⟨u, inArgs, inU⟩
  · exact absurd inHead not_mem_vars_const
  · rw [List.mem_singleton.mp inArgs] at inU
    exact .inr ⟨wrapCall, List.mem_singleton_self _, inU⟩

/-- **The call and the atomic evaluation on states of `RuleSyntax.step`**, at the instance. -/
def boxItem_step : OperationalCorrespondence (evaluation wrap.interp {boxItem})
    (Machines.stepSystem ℕ (permitProgram askSym permitSym boxItem wrapCall (spine (k 40) [.var 0])
      [equationRule askSym wrap])) :=
  permitStepCorrespondence ℕ wrap_apart rfl (List.mem_singleton_self _) item_bound boxItem_unseen
    (defined_answers askSym wrap) rfl rfl boxItem_restricted (fun r inside => by
      rw [List.mem_singleton.mp inside]
      exact equationRule_fragment askSym wrap)

/-! ## A function with no value at some arguments -/

/-- **`pred(s x) = x`**: no value at an argument that is no successor. -/
def predEq : Equation where
  name := 24
  params := [spine (k 31) [.var 0]]
  body := .var 0
  closed := fun _ inside =>
    ⟨_, List.mem_singleton_self _, (mem_vars_spine _ _).mpr (.inr ⟨.var 0, List.mem_singleton_self _, inside⟩)⟩

/-- Its call `r := pred(x)`. -/
def predCall : Condition ℕ Tm := ⟨.var 1, 24, [.var 0]⟩

/-- **The rule**: take `item x`, let `r := pred(x)`, make `out r`. -/
def unPred : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[spine (k 40) [.var 0]], [], [], [], [spine (k 41) [.var 1]]⟩, []⟩
  conditions := [predCall]

theorem pred_apart : Apart askSym permitSym predCall.name := ⟨by decide, by decide, by decide⟩

theorem unPred_unseen : ∀ θ : ℕ → Expr,
    ∀ q ∈ unPred.rule.body.take ++ unPred.rule.body.read ++ unPred.rule.body.produce,
      ¬ Hidden askSym permitSym predCall.name (inst θ q) := by
  intro θ q inside
  simp only [unPred, List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
    or_false] at inside
  rcases inside with rfl | rfl
  · exact not_hidden_of_head (spineHead_inst_spine θ 40 _) (by decide) (by decide) (by decide)
  · exact not_hidden_of_head (spineHead_inst_spine θ 41 _) (by decide) (by decide) (by decide)

/-- **No value at `0`.** -/
theorem pred_undefined : predEq.interp predCall.name [.sym 0] = none :=
  predEq.interp_none fun θ same => by
    have first : inst θ (spine (k 31) [.var 0]) = .sym 0 := (List.cons.inj same).1
    rw [inst_spine] at first
    exact absurd (show Expr.app (.sym 31) (θ 0) = .sym 0 from first) (fun clash => Expr.noConfusion clash)

/-- **The value `5` at `s 5`.** -/
theorem pred_defined : predEq.interp predCall.name [groundSpine (.sym 31) [.sym 5]] = some (.sym 5) :=
  predEq.interp_match fun _ => .sym 5

/-- **The atomic evaluation is refused at `item 0`.** -/
theorem pred_refused (A' : Multiset Expr) : ¬ EvalStep predEq.interp unPred {item 0} A' := by
  rintro ⟨θ, rest, sum, -, -, conditions, -⟩
  have value := conditions predCall (List.mem_singleton_self _)
  have taken : inst θ (spine (k 40) [.var 0]) ∈ ({item 0} : Multiset Expr) := by
    rw [← sum]
    exact Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_map_of_mem (List.mem_singleton_self _))))
  have isItem : inst θ (spine (k 40) [.var 0]) = item 0 := Multiset.mem_singleton.mp taken
  rw [inst_spine] at isItem
  have zero : θ 0 = .sym 0 := (List.cons.inj (groundSpine_sym_inj isItem).2).1
  have arguments : predCall.arguments.map (inst θ) = [.sym 0] := by
    show [θ 0] = [.sym 0]
    rw [zero]
  rw [arguments] at value
  exact absurd (pred_undefined.symm.trans value) (by simp)

/-- **The request fires at `item 0` with its permit** and leaves the pending row `ask pred 0`. -/
theorem pred_request_fires :
    Rewrites [permitRequest askSym permitSym unPred predCall (spine (k 40) [.var 0])]
      ({item 0} + ({item 0} : Multiset Expr).map (groundPermit permitSym))
      ({groundAsk askSym 24 [.sym 0]} + {item 0}) := by
  refine ⟨_, List.mem_singleton_self _, fun _ => .sym 0, {item 0}, ?_, fun q inside => ?_,
    fun e inside => by simp [equationsOf, permitRequest] at inside, ?_⟩
  · simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.map_singleton]
    rw [inst_permitRow, inst_spine, add_comm]
    rfl
  · have isItem : q = spine (k 40) [.var 0] := by simpa [permitRequest, unPred] using inside
    rw [isItem, inst_spine]
    exact Multiset.mem_singleton_self _
  · simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [inst_askRow]
    rfl

/-- **The call waits, and the bag says so**: the pending row `ask pred 0` is in every bag of every run of the
call from the bag after the request. -/
theorem pred_waits {C' : Multiset Expr}
    (run : Relation.ReflTransGen
      (Rewrites (permitProgram askSym permitSym unPred predCall (spine (k 40) [.var 0]) [predEq.rule askSym]))
      ({groundAsk askSym 24 [.sym 0]} + {item 0}) C') :
    groundAsk askSym 24 [.sym 0] ∈ C' :=
  undefined_waits_run (c := predCall) pred_apart unPred_unseen (predEq.answers askSym) pred_undefined run
    (Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _)))

/-! ## Control: arguments that the trigger does not determine -/

/-- **The rule**: take `tok`, read `cell x`, let `r := f(x)` (`f` the symbol `25`), make `out r`. The
argument's unknown is bound by the read, not by the trigger `tok`. -/
def twoCells : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[k 42], [spine (k 44) [.var 0]], [], [], [spine (k 41) [.var 1]]⟩, []⟩
  conditions := [⟨.var 1, 25, [.var 0]⟩]

/-- The rows `tok` and `cell n`. -/
def tokRow : Expr := .sym 42
def cellRow (n : ℕ) : Expr := groundSpine (.sym 44) [.sym n]

/-- The atomic bag: `tok`, `cell 1`, `cell 2`. -/
def cells : Multiset Expr := {tokRow} + ({cellRow 1} + {cellRow 2})

/-- **A request at `cell 1` leaves a bag that is not related to the atomic bag**, for every interpretation:
the bag before it is related (`related_start`), the request fires, and after it the row `tok` is not covered
at the argument `2`. -/
theorem request_loses_cover (I : Interpretation ℕ Expr) :
    PermitRelated askSym permitSym I ⟨.var 1, 25, [.var 0]⟩ (k 42) cells
        (cells + {groundPermit permitSym tokRow}) ∧
      Rewrites [permitRequest askSym permitSym twoCells ⟨.var 1, 25, [.var 0]⟩ (k 42)]
        (cells + {groundPermit permitSym tokRow}) ({groundAsk askSym 25 [.sym 1]} + cells) ∧
      ¬ PermitRelated askSym permitSym I ⟨.var 1, 25, [.var 0]⟩ (k 42) cells
        ({groundAsk askSym 25 [.sym 1]} + cells) := by
  have clean : ∀ e ∈ cells, ¬ Hidden askSym permitSym 25 e := by
    intro e inside
    rcases Multiset.mem_add.mp inside with isTok | isCell
    · rw [Multiset.mem_singleton.mp isTok]
      exact not_hidden_of_head (n := 42) rfl (by decide) (by decide) (by decide)
    · rcases Multiset.mem_add.mp isCell with first | second
      · rw [Multiset.mem_singleton.mp first]
        exact not_hidden_of_head (spineHead_groundSpine _ _) (by decide) (by decide) (by decide)
      · rw [Multiset.mem_singleton.mp second]
        exact not_hidden_of_head (spineHead_groundSpine _ _) (by decide) (by decide) (by decide)
  refine ⟨⟨{groundPermit permitSym tokRow}, 0, 0, by simp, clean, fun e inside => ?_,
      fun _ inside => absurd inside (Multiset.notMem_zero _), fun _ inside => absurd inside (Multiset.notMem_zero _),
      fun _ _ => .inl (Multiset.mem_singleton_self _)⟩, ?_, ?_⟩
  · rw [Multiset.mem_singleton.mp inside]
    exact headed_permit permitSym _
  · refine ⟨_, List.mem_singleton_self _, fun x => if x = 0 then .sym 1 else .sym 0, cells, ?_,
      fun q inside => ?_, fun e inside => by simp [equationsOf, permitRequest] at inside, ?_⟩
    · simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_permitRow, add_comm]
      rfl
    · have patterns : q = k 42 ∨ q = spine (k 44) [.var 0] := by simpa [permitRequest, twoCells] using inside
      rcases patterns with rfl | rfl
      · exact Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))
      · rw [inst_spine]
        exact Multiset.mem_add.mpr (.inr (Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))))
    · simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_askRow]
      rfl
  · rintro ⟨permits, pending, answers, split⟩
    have others : permits + pending + answers = {groundAsk askSym 25 [.sym 1]} := by
      have whole : cells + (permits + pending + answers) = cells + {groundAsk askSym 25 [.sym 1]} := by
        rw [add_comm cells {groundAsk askSym 25 [.sym 1]}, split.sum]
        abel
      exact add_left_cancel whole
    have only : ∀ e ∈ permits + pending + answers, e = groundAsk askSym 25 [.sym 1] := by
      intro e inside
      rw [others] at inside
      exact Multiset.mem_singleton.mp inside
    have isAsk : Headed askSym (groundAsk askSym 25 [.sym 1]) := headed_ask _ _ _
    rcases split.covered (fun _ => .sym 2) (Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))) with
      permit | pendingRow | ⟨w, answer⟩
    · have same := only _ (Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl permit))))
      exact absurd (headed_inj (same ▸ isAsk) (headed_permit permitSym _)) (by decide)
    · have same := only _ (Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr pendingRow))))
      exact absurd (groundAsk_inj same) (by decide)
    · have same := only _ (Multiset.mem_add.mpr (.inr answer))
      exact absurd (headed_inj (same ▸ isAsk) (headed_row _ _ _)) (by decide)

#print axioms defined_answers
#print axioms Equation.interp_match
#print axioms Equation.interp_none
#print axioms Equation.answers
#print axioms Equation.rule_fragment
#print axioms boxItem_permit_called
#print axioms boxItem_internal_stops
#print axioms boxItem_step
#print axioms pred_undefined
#print axioms pred_defined
#print axioms pred_refused
#print axioms pred_request_fires
#print axioms pred_waits
#print axioms request_loses_cover

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.PermitCalls
