import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Calls

/-!
# A defined helper called through the pending row, and the two controls of the call

**The helper** (`wrap`): `wrap(x) = box x`, one equation. **The rule** (`boxItem`): take `item x`, let
`r := wrap(x)`, make `out r`.

* `boxItem_evaluates`: at the bag `item 7`, the atomic evaluation makes `out (box 7)`.
* `boxItem_called`: from the same bag, the call (request, equation, resume) reaches a bag related to the
  atomic result, by `related_atomic`; `boxItem_called_rows`: it holds `out (box 7)`.

**Control: a neighbour that reads the pending row** (`watch`, `watch_sees_pending`,
`watch_never_at_clean`): after the request, `watch` fires (it reads `ask wrap 7` and makes `seen`); at a
clean bag, where every atomic bag is, it never fires. With `watch` in the program the atomic system and
the call are told apart, so the privacy of the pending row is needed.

**Control: a request that consumes the rule's rows, on a test** (`isOne`, `checkTok`, `consumingRequest`,
`consumingCall`, `test_refused_atomically`, `consuming_request_fires`, `consuming_loses_tok`,
`call_keeps_tok`): the helper `isOne(x) = no` and the rule `take tok x, let yes := isOne(x), make done` (a
test). The atomic evaluation refuses at `tok 7` and keeps the row. A request that takes the rule's take
patterns fires and takes `tok 7`, and along every run of that call from there no bag holds `tok 7` again
(no rule of it makes a `tok` row); the request of `Calls`, which reads the rule's rows, fires and keeps it.

**Control: the request of `Calls` fires again and again** (`request_refires`, `request_unbounded`,
`test_call_unbounded`): it reads the rule's rows and takes nothing, so once it fires it fires again from its
own result with one more pending row, without bound. At the test above, where the atomic evaluation refuses
every result, the call still has internal runs of every length: the atomic bag is stuck and the related bag
of the call is not. `Related` is kept along these runs (`related_request`); what it does not say is that the
internal firings stop.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.CallInstances

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SRule inst equationsOf mem_vars_var not_mem_vars_const)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Rewrites)

/-- A symbol. -/
abbrev k (n : ℕ) : Tm := .const (.sym n)

/-- The symbol of pending rows. -/
abbrev askSym : ℕ := 20

/-- **The helper** `wrap(x) = box x`. -/
def wrap : Defined where
  name := 21
  params := [0]
  body := spine (k 30) [.var 0]
  distinct := List.nodup_singleton 0
  closed := by
    intro x inside
    rcases (mem_vars_spine _ _).mp inside with inHead | ⟨t, member, inT⟩
    · exact absurd inHead not_mem_vars_const
    · rw [List.mem_singleton.mp member] at inT
      rw [mem_vars_var.mp inT]
      exact List.mem_singleton_self 0

/-- Its call `r := wrap(x)`. -/
def wrapCall : Condition ℕ Tm := ⟨.var 1, 21, [.var 0]⟩

/-- **The rule**: take `item x`, let `r := wrap(x)`, make `out r`. -/
def boxItem : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[spine (k 40) [.var 0]], [], [], [], [spine (k 41) [.var 1]]⟩, []⟩
  conditions := [wrapCall]

/-- The rows of the instance. -/
def item (n : ℕ) : Expr := groundSpine (.sym 40) [.sym n]
def out (e : Expr) : Expr := groundSpine (.sym 41) [e]
def box (e : Expr) : Expr := groundSpine (.sym 30) [e]

theorem spineHead_inst_spine (θ : ℕ → Expr) (n : ℕ) (ts : List Tm) :
    spineHead (inst θ (spine (k n) ts)) = .sym n := by
  rw [inst_spine, spineHead_groundSpine]
  rfl

/-- A row starting with a symbol other than `20` and `21` is neither pending nor a table row of `wrap`. -/
theorem not_private_of_head {e : Expr} {n : ℕ} (head : spineHead e = .sym n) (notAsk : n ≠ askSym)
    (notTable : n ≠ 21) : ¬ Private askSym 21 e := by
  rintro (⟨args, rfl⟩ | ⟨args, v, rfl⟩)
  · rw [groundAsk, spineHead_groundSpine] at head
    exact notAsk (Expr.sym.inj head).symm
  · rw [groundRow, spineHead_groundSpine] at head
    exact notTable (Expr.sym.inj head).symm

theorem boxItem_unseen : SeesNoPending askSym wrap.name boxItem := by
  intro θ q inside
  simp only [boxItem, List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
    or_false] at inside
  rcases inside with rfl | rfl
  · exact not_private_of_head (spineHead_inst_spine θ 40 _) (by decide) (by decide)
  · exact not_private_of_head (spineHead_inst_spine θ 41 _) (by decide) (by decide)

theorem item_clean (n : ℕ) : Clean askSym wrap.name {item n} := by
  intro e inside
  rw [Multiset.mem_singleton.mp inside]
  exact not_private_of_head (spineHead_groundSpine _ _) (by decide) (by decide)

/-- **The atomic evaluation makes `out (box 7)`.** -/
theorem boxItem_evaluates : EvalStep wrap.interp boxItem {item 7} {out (box (.sym 7))} := by
  refine ⟨fun x => if x = 0 then .sym 7 else box (.sym 7), 0, rfl, fun q inside => absurd inside List.not_mem_nil,
    fun e inside => by simp [equationsOf, boxItem] at inside, fun c inside => ?_, rfl⟩
  rw [List.mem_singleton.mp inside]
  rfl

/-- **The call reaches a bag related to the atomic result**: a request, the equation and the resume. -/
theorem boxItem_called :
    ∃ C₁ C₂ C', Rewrites [request askSym boxItem wrapCall] {item 7} C₁ ∧
      Rewrites [equationRule askSym wrap] C₁ C₂ ∧ Rewrites [boxItem.tableRule rows] C₂ C' ∧
      Related askSym wrap {out (box (.sym 7))} C' :=
  related_atomic rfl rfl rfl boxItem_unseen (related_refl wrap (item_clean 7)) boxItem_evaluates

/-- **The call's last bag holds `out (box 7)`**, as the atomic result does. -/
theorem boxItem_called_rows :
    ∃ C₁ C₂ C', Rewrites [request askSym boxItem wrapCall] {item 7} C₁ ∧
      Rewrites [equationRule askSym wrap] C₁ C₂ ∧ Rewrites [boxItem.tableRule rows] C₂ C' ∧
      out (box (.sym 7)) ∈ C' := by
  obtain ⟨C₁, C₂, C', request', equation', resume', related⟩ := boxItem_called
  refine ⟨C₁, C₂, C', request', equation', resume', ?_⟩
  have count := related_rows related (e := out (box (.sym 7)))
    (not_private_of_head (spineHead_groundSpine _ _) (by decide) (by decide))
  rw [← Multiset.count_pos, count]
  simp

/-! ## Control: a neighbour that reads the pending row -/

/-- **The neighbour**: read a pending row of `wrap`, make `seen`. -/
def watch : SRule := ⟨PUnit.unit, ⟨[], [askRow askSym 21 [.var 0]], [], [], [k 50]⟩, []⟩

/-- **It fires after a request.** -/
theorem watch_sees_pending :
    Rewrites [watch] ({groundAsk askSym 21 [.sym 7]} + {item 7})
      ({.sym 50} + ({groundAsk askSym 21 [.sym 7]} + {item 7})) := by
  refine ⟨watch, List.mem_singleton_self _, fun _ => .sym 7, {groundAsk askSym 21 [.sym 7]} + {item 7},
    by simp [watch], fun q inside => ?_, fun e inside => by simp [equationsOf, watch] at inside, rfl⟩
  rw [List.mem_singleton.mp inside, inst_askRow]
  exact Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))

/-- **It never fires at a clean bag.** -/
theorem watch_never_at_clean {B B' : Multiset Expr} (clean : Clean askSym 21 B) : ¬ Rewrites [watch] B B' := by
  rintro ⟨r, member, θ, rest, split, reads, -, -⟩
  obtain rfl := List.mem_singleton.mp member
  have inRest := reads _ (List.mem_singleton_self _)
  have inB : inst θ (askRow askSym 21 [.var 0]) ∈ B := by
    rw [← split]
    exact Multiset.mem_add.mpr (.inr inRest)
  exact clean _ inB (.inl ⟨_, inst_askRow askSym θ 21 [.var 0]⟩)

/-! ## Control: a request that consumes, on a test -/

/-- **The helper** `isOne(x) = no`. -/
def isOne : Defined where
  name := 22
  params := [0]
  body := k 60
  distinct := List.nodup_singleton 0
  closed := fun _ inside => absurd inside not_mem_vars_const

/-- **A test**: take `tok x`, let `yes := isOne(x)`, make `done`. -/
def checkTok : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[spine (k 42) [.var 0]], [], [], [], [k 43]⟩, []⟩
  conditions := [⟨k 61, 22, [.var 0]⟩]

/-- The row `tok 7`. -/
def tok (n : ℕ) : Expr := groundSpine (.sym 42) [.sym n]

/-- **A request that consumes** the rule's take patterns (the hosting translation's form, for a rule). -/
def consumingRequest (ρ : RuleWithCondition ℕ Tm) (c : Condition ℕ Tm) : SRule :=
  ⟨PUnit.unit, ⟨ρ.rule.body.take, ρ.rule.body.read, [], [], [askRow askSym c.name c.arguments]⟩, []⟩

/-- **The atomic evaluation refuses the test at `tok 7`**, so it keeps the row. -/
theorem test_refused_atomically (A' : Multiset Expr) : ¬ EvalStep isOne.interp checkTok {tok 7} A' := by
  rintro ⟨θ, rest, -, -, -, conditions, -⟩
  have value := conditions _ (List.mem_singleton_self _)
  simp only [Defined.interp, isOne, List.length_map, List.length_singleton, and_self, if_true] at value
  exact absurd (Option.some.inj value) (by simp [inst])

/-- **The consuming request fires at `tok 7`** and takes the row. -/
theorem consuming_request_fires :
    Rewrites [consumingRequest checkTok ⟨k 61, 22, [.var 0]⟩] {tok 7} {groundAsk askSym 22 [.sym 7]} := by
  refine ⟨_, List.mem_singleton_self _, fun _ => .sym 7, 0, ?_, fun q inside => absurd inside List.not_mem_nil,
    fun e inside => by simp [equationsOf, consumingRequest, checkTok] at inside, ?_⟩
  · simp only [consumingRequest, checkTok, List.map_cons, List.map_nil, Multiset.coe_singleton, add_zero]
    rw [inst_spine]
    rfl
  · simp only [consumingRequest, List.map_cons, List.map_nil, Multiset.coe_singleton, add_zero]
    rw [inst_askRow]
    rfl

/-- **The call whose request consumes**, for the test: the consuming request, the equation and the resume. -/
def consumingCall : List SRule :=
  [consumingRequest checkTok ⟨k 61, 22, [.var 0]⟩, equationRule askSym isOne, checkTok.tableRule rows]

/-- No rule of the consuming call makes a `tok` row. -/
theorem consumingCall_makes_no_tok {B B' : Multiset Expr} (fires : Rewrites consumingCall B B')
    (none : ∀ e ∈ B, spineHead e ≠ .sym 42) : ∀ e ∈ B', spineHead e ≠ .sym 42 := by
  obtain ⟨r, member, θ, rest, split, -, -, rfl⟩ := fires
  intro e inside
  rcases Multiset.mem_add.mp inside with made | old
  · obtain ⟨m, inProduce, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp made)
    simp only [consumingCall, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · obtain rfl : m = askRow askSym 22 [.var 0] := by simpa [consumingRequest] using inProduce
      rw [inst_askRow, groundAsk, spineHead_groundSpine]
      exact fun same => absurd (Expr.sym.inj same) (by decide)
    · obtain rfl : m = rows.row 22 [.var 0] (k 60) := by simpa [equationRule, isOne] using inProduce
      rw [inst_row, groundRow, spineHead_groundSpine]
      exact fun same => absurd (Expr.sym.inj same) (by decide)
    · rw [RuleWithCondition.tableRule_produce] at inProduce
      obtain rfl : m = k 43 := by simpa [checkTok] using inProduce
      have head : spineHead (inst θ (k 43)) = .sym 43 := spineHead_inst_spine θ 43 []
      rw [head]
      exact fun same => absurd (Expr.sym.inj same) (by decide)
  · exact none e (by rw [← split]; exact Multiset.mem_add.mpr (.inr old))

/-- **The row is lost for good**: along every run of the consuming call from the bag after its request, no bag
holds `tok 7`. -/
theorem consuming_loses_tok {B : Multiset Expr}
    (run : Relation.ReflTransGen (Rewrites consumingCall) {groundAsk askSym 22 [.sym 7]} B) : tok 7 ∉ B := by
  have none : ∀ e ∈ B, spineHead e ≠ .sym 42 := by
    induction run with
    | refl =>
        intro e inside
        rw [Multiset.mem_singleton.mp inside, groundAsk, spineHead_groundSpine]
        exact fun same => absurd (Expr.sym.inj same) (by decide)
    | tail _ last ih => exact consumingCall_makes_no_tok last ih
  intro inside
  exact none _ inside (by rw [tok, spineHead_groundSpine]; rfl)

/-- **The request of `Calls` fires at `tok 7` and keeps the row.** -/
theorem call_keeps_tok :
    Rewrites [request askSym checkTok ⟨k 61, 22, [.var 0]⟩] {tok 7}
      ({groundAsk askSym 22 [.sym 7]} + {tok 7}) ∧ tok 7 ∈ ({groundAsk askSym 22 [.sym 7]} + {tok 7} : Multiset Expr) := by
  refine ⟨⟨_, List.mem_singleton_self _, fun _ => .sym 7, {tok 7}, by simp [request], fun q inside => ?_,
    fun e inside => by simp [equationsOf, request] at inside, ?_⟩, Multiset.mem_add.mpr (.inr
      (Multiset.mem_singleton_self _))⟩
  · simp only [request, checkTok, List.append_nil, List.mem_singleton] at inside
    rw [inside, inst_spine]
    exact Multiset.mem_singleton_self _
  · simp only [request, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [inst_askRow]
    rfl

/-! ## Control: the request of `Calls` fires again and again -/

section Refires

variable {ask : ℕ} {ρ : RuleWithCondition ℕ Tm} {c : Condition ℕ Tm}

/-- **The request fires again from its own result**, adding one more row. -/
theorem request_refires {B B' : Multiset Expr} (fires : Rewrites [request ask ρ c] B B') :
    ∃ B'', Rewrites [request ask ρ c] B' B'' ∧ B''.card = B'.card + 1 := by
  obtain ⟨r, member, θ, rest, -, reads, equations, rfl⟩ := fires
  obtain rfl := List.mem_singleton.mp member
  refine ⟨((request ask ρ c).body.produce.map (inst θ) : Multiset Expr) +
      (((request ask ρ c).body.produce.map (inst θ) : Multiset Expr) + rest),
    ⟨request ask ρ c, List.mem_singleton_self _, θ,
      ((request ask ρ c).body.produce.map (inst θ) : Multiset Expr) + rest, ?_,
      fun q inside => Multiset.mem_add.mpr (.inr (reads q inside)), equations, rfl⟩, ?_⟩
  · simp [request]
  · rw [Multiset.card_add]
    simp [request]
    omega

/-- **Internal runs of every length**: after one request, for every `n` there is a run of requests that
reaches a bag with `n + 1` more rows. -/
theorem request_unbounded {B B' : Multiset Expr} (fires : Rewrites [request ask ρ c] B B') (n : ℕ) :
    ∃ Bn Bn', Relation.ReflTransGen (Rewrites [request ask ρ c]) B' Bn ∧ Rewrites [request ask ρ c] Bn Bn' ∧
      Bn'.card = B'.card + (n + 1) := by
  induction n with
  | zero =>
      obtain ⟨B'', again, card⟩ := request_refires fires
      exact ⟨B', B'', .refl, again, card⟩
  | succ n ih =>
      obtain ⟨Bn, Bn', run, last, card⟩ := ih
      obtain ⟨B'', again, card'⟩ := request_refires last
      exact ⟨Bn', B'', run.tail last, again, by rw [card', card]; omega⟩

end Refires

/-- **At the test, the atomic evaluation refuses and the call runs without bound.** -/
theorem test_call_unbounded :
    (∀ A', ¬ EvalStep isOne.interp checkTok {tok 7} A') ∧
      ∀ n : ℕ, ∃ Bn Bn',
        Relation.ReflTransGen (Rewrites [request askSym checkTok ⟨k 61, 22, [.var 0]⟩])
          ({groundAsk askSym 22 [.sym 7]} + {tok 7}) Bn ∧
        Rewrites [request askSym checkTok ⟨k 61, 22, [.var 0]⟩] Bn Bn' ∧ Bn'.card = 2 + (n + 1) := by
  refine ⟨test_refused_atomically, fun n => ?_⟩
  obtain ⟨Bn, Bn', run, last, card⟩ := request_unbounded call_keeps_tok.1 n
  refine ⟨Bn, Bn', run, last, ?_⟩
  rw [card]
  rfl

#print axioms request_refires
#print axioms request_unbounded
#print axioms test_call_unbounded
#print axioms boxItem_evaluates
#print axioms boxItem_called
#print axioms boxItem_called_rows
#print axioms watch_sees_pending
#print axioms watch_never_at_clean
#print axioms test_refused_atomically
#print axioms consuming_request_fires
#print axioms consuming_loses_tok
#print axioms call_keeps_tok

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.CallInstances
