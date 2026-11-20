import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Calls

/-!
# The call that asks once: a permit made with the rule's rows

The request of `Calls` takes nothing and so fires again without bound. Here the request **takes a permit**:
a row `permit e` that is made together with the row `e`, by whoever makes `e`. The rule has one condition
`r := f(t̄)` and a **trigger**, one of its take patterns `p`, whose unknowns include those of the arguments. The
call's program (`permitProgram`) is

* **the request** (`permitRequest`): take `permit p`, read the rule's take and read patterns, make the pending
  row `ask f t̄`. The rule's own rows are read, so a condition that is a test keeps them;
* **rules that answer** (`Answers`): any rules of which each firing takes one pending row `ask f ā` with
  `I f ā = some v` and makes the row `f ā v`, and which can fire on every such pending row. The function is
  given by an interpretation `I`, with no value at some arguments if it has none there;
* **the resume** (`permitResume`): the rule's table read, which also makes a permit for each row it makes.

## The correspondence with the atomic evaluation

A bag of the call **is related** to a bag of the atomic system (`PermitRelated`) when it is that bag beside
permits, pending rows and rows of the graph, the atomic bag holds none of these (by their head symbols), and
every row of the atomic bag that the trigger matches is **covered**: its permit is there, or the pending row
at its arguments, or the answer at its arguments.

* `related_permitRequest`, `related_answer`: an internal firing keeps the relation;
* `related_permitResume`: a resume is an atomic evaluation, and the relation continues;
* `related_atomic`: an atomic evaluation is at most one request and one answer, then a resume;
* `related_start`: a bag with none of the call's rows, beside a permit for each of its rows, is related to
  itself;
* `permitCorrespondence`: an `OperationalCorrespondence` between the atomic evaluation on bags and rewriting
  by the call's program. The request and the answers are silent; the resume is the observed firing.
  `permitStepCorrespondence` composes it with `Machines.correspondence`, so the same holds for the firings of
  `RuleSyntax.step` at states that read as bags, along runs.

## What the general notion does not say, and is proved beside it

* **The internal firings stop** (`internal_decreases`, `internal_terminates`): twice the permits plus the
  pending rows is a number that every request and every answer lowers. So the call has no internal run
  without end, as the atomic system has none.
* **Where the function has no value the call waits, and the bag says so** (`undefined_waits`,
  `undefined_waits_run`): a pending row at arguments with `I f ā = none` is taken by no firing of the call's
  program, so it stays in every bag of every run. Where it has a value the pending row can be answered
  (`Answers.complete`).

Hypotheses and their reasons: the trigger's unknowns include the arguments' (`bound`: a permit is for one
row, so the question must be a function of that row); the rule's rows are never rows of the call's own
(`unseen`); the three head symbols are apart (`Apart`). Instances and controls are in `PermitCallInstances`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.PermitCalls

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SRule inst inst_congr agree_of_inst_eq equationsOf RangeRestrictedPositive
  RangeRestricted Bound written isGuard mem_vars_var not_mem_vars_const)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Rewrites rewrites_of_mem)

/-! ## Rows by their head symbol -/

/-- **A row headed by a symbol.** -/
def Headed (n : ℕ) (e : Expr) : Prop := spineHead e = .sym n

instance (n : ℕ) : DecidablePred (Headed n) := fun e => inferInstanceAs (Decidable (spineHead e = .sym n))

theorem headed_groundSpine (n : ℕ) (xs : List Expr) : Headed n (groundSpine (.sym n) xs) := by
  rw [Headed, spineHead_groundSpine]
  rfl

theorem headed_inj {n m : ℕ} {e : Expr} (first : Headed n e) (second : Headed m e) : n = m :=
  Expr.sym.inj (first.symm.trans second)

theorem headed_row (f : ℕ) (args : List Expr) (v : Expr) : Headed f (groundRow f args v) :=
  headed_groundSpine f _

theorem headed_ask (askSym f : ℕ) (args : List Expr) : Headed askSym (groundAsk askSym f args) :=
  headed_groundSpine askSym _

theorem groundAsk_inj {askSym f : ℕ} {xs ys : List Expr} (same : groundAsk askSym f xs = groundAsk askSym f ys) :
    xs = ys :=
  (List.cons.inj (groundSpine_sym_inj same).2).2

/-- **Splitting rows of one kind off**: rows that are not hidden, beside a rest, are a bag beside hidden rows
only when the bag holds them. -/
theorem split_apart {hidden : Expr → Prop} {X R A H : Multiset Expr} (sum : X + R = A + H)
    (apartX : ∀ x ∈ X, ¬ hidden x) (hiddenH : ∀ h ∈ H, hidden h) : ∃ rest, A = X + rest ∧ R = rest + H := by
  have le : X ≤ A := by
    rw [Multiset.le_iff_count]
    intro x
    by_cases inX : x ∈ X
    · have notH : Multiset.count x H = 0 := Multiset.count_eq_zero.mpr fun inH => apartX x inX (hiddenH x inH)
      have := congrArg (Multiset.count x) sum
      rw [Multiset.count_add, Multiset.count_add, notH, add_zero] at this
      omega
    · rw [Multiset.count_eq_zero.mpr inX]
      exact Nat.zero_le _
  refine ⟨A - X, (add_tsub_cancel_of_le le).symm, ?_⟩
  have : R = A + H - X := by rw [← sum, add_tsub_cancel_left]
  rw [this, tsub_add_eq_add_tsub le]

/-! ## The call's program -/

section Program

variable (askSym permitSym : ℕ)

/-- **A permit row** for a row pattern. -/
def permitRow (t : Tm) : Tm := spine (.const (.sym permitSym)) [t]

/-- A ground permit row. -/
def groundPermit (e : Expr) : Expr := groundSpine (.sym permitSym) [e]

theorem inst_permitRow (θ : ℕ → Expr) (t : Tm) :
    inst θ (permitRow permitSym t) = groundPermit permitSym (inst θ t) := by
  rw [permitRow, inst_spine]
  rfl

theorem headed_permit (e : Expr) : Headed permitSym (groundPermit permitSym e) := headed_groundSpine permitSym _

theorem groundPermit_inj {a b : Expr} (same : groundPermit permitSym a = groundPermit permitSym b) : a = b :=
  (List.cons.inj (groundSpine_sym_inj same).2).1

/-- The unknowns of a permit row are those of its row. -/
theorem mem_vars_permitRow {x : ℕ} (t : Tm) : x ∈ (permitRow permitSym t).freeVars ↔ x ∈ t.freeVars := by
  rw [permitRow, mem_vars_spine]
  constructor
  · rintro (inHead | ⟨u, member, inU⟩)
    · exact absurd inHead not_mem_vars_const
    · rw [List.mem_singleton.mp member] at inU
      exact inU
  · intro inside
    exact .inr ⟨t, List.mem_singleton_self _, inside⟩

/-- **The request that takes a permit**: take the permit of the trigger's row, read the rule's take and read
patterns, make the pending row of the condition. -/
def permitRequest (ρ : RuleWithCondition ℕ Tm) (c : Condition ℕ Tm) (p : Tm) : SRule :=
  ⟨PUnit.unit, ⟨[permitRow permitSym p], ρ.rule.body.take ++ ρ.rule.body.read, [], [],
    [askRow askSym c.name c.arguments]⟩, []⟩

/-- **The resume that makes permits**: the rule's table read, with a permit made beside each made row. -/
def permitResume (ρ : RuleWithCondition ℕ Tm) : SRule where
  locals := ρ.rule.locals
  body := { ρ.rule.body with
    read := ρ.rule.body.read ++ ρ.calls rows
    produce := ρ.rule.body.produce ++ ρ.rule.body.produce.map (permitRow permitSym) }
  collect := ρ.rule.collect

/-- **The program of the call**: the request, the rules that answer, the resume. -/
def permitProgram (ρ : RuleWithCondition ℕ Tm) (c : Condition ℕ Tm) (p : Tm) (answerers : List SRule) :
    List SRule :=
  permitRequest askSym permitSym ρ c p :: (answerers ++ [permitResume permitSym ρ])

/-- **Rules that answer the pending rows of `f` by an interpretation**: each firing takes one pending row at
arguments where the interpretation has a value and makes the row of the graph there, and every such pending
row can be answered. -/
structure Answers (I : Interpretation ℕ Expr) (f : ℕ) (answerers : List SRule) : Prop where
  sound : ∀ {C C' : Multiset Expr}, Rewrites answerers C C' →
    ∃ (args : List Expr) (v : Expr) (rest : Multiset Expr), I f args = some v ∧
      C = {groundAsk askSym f args} + rest ∧ C' = {groundRow f args v} + rest
  complete : ∀ {args : List Expr} {v : Expr} (rest : Multiset Expr), I f args = some v →
    Rewrites answerers ({groundAsk askSym f args} + rest) ({groundRow f args v} + rest)

/-- **A row of the call's own**: a permit, a pending row or a row of the function's table, by its head. -/
def Hidden (f : ℕ) (e : Expr) : Prop := Headed permitSym e ∨ Headed askSym e ∨ Headed f e

/-- **The three head symbols are apart.** -/
structure Apart (f : ℕ) : Prop where
  permit_ask : permitSym ≠ askSym
  permit_table : permitSym ≠ f
  ask_table : askSym ≠ f

/-- **A bag of the call, split**: the atomic bag beside permits, pending rows and rows of the graph, with
every row the trigger matches covered. -/
structure Split (I : Interpretation ℕ Expr) (c : Condition ℕ Tm) (p : Tm)
    (A C permits pending answers : Multiset Expr) : Prop where
  sum : C = A + permits + pending + answers
  clean : ∀ e ∈ A, ¬ Hidden askSym permitSym c.name e
  permitRows : ∀ e ∈ permits, Headed permitSym e
  pendingRows : ∀ e ∈ pending, Headed askSym e
  answerRows : ∀ e ∈ answers, ∃ (args : List Expr) (v : Expr), I c.name args = some v ∧ e = groundRow c.name args v
  covered : ∀ θ : ℕ → Expr, inst θ p ∈ A →
    groundPermit permitSym (inst θ p) ∈ permits ∨
      groundAsk askSym c.name (c.arguments.map (inst θ)) ∈ pending ∨
      ∃ v, groundRow c.name (c.arguments.map (inst θ)) v ∈ answers

/-- **Related bags.** -/
def PermitRelated (I : Interpretation ℕ Expr) (c : Condition ℕ Tm) (p : Tm) (A C : Multiset Expr) : Prop :=
  ∃ permits pending answers : Multiset Expr, Split askSym permitSym I c p A C permits pending answers

/-- **An internal firing of the call**: a request or an answer. -/
def Internal (ρ : RuleWithCondition ℕ Tm) (c : Condition ℕ Tm) (p : Tm) (answerers : List SRule)
    (C C' : Multiset Expr) : Prop :=
  Rewrites [permitRequest askSym permitSym ρ c p] C C' ∨ Rewrites answerers C C'

/-- **The weight of a bag**: twice its permits and once its pending rows, by head. -/
def weight (C : Multiset Expr) : ℕ :=
  2 * Multiset.countP (Headed permitSym) C + Multiset.countP (Headed askSym) C

end Program

section Relation

variable {askSym permitSym : ℕ} {I : Interpretation ℕ Expr} {ρ : RuleWithCondition ℕ Tm} {c : Condition ℕ Tm}
  {p : Tm} {answerers : List SRule}

/-- A member of a split bag with the head of the permits is a permit of the split. -/
theorem Split.mem_permits {A C permits pending answers : Multiset Expr}
    (split : Split askSym permitSym I c p A C permits pending answers) (apart : Apart askSym permitSym c.name)
    {e : Expr} (inC : e ∈ C) (head : Headed permitSym e) : e ∈ permits := by
  rw [split.sum] at inC
  rcases Multiset.mem_add.mp inC with inAPP | inAnswers
  · rcases Multiset.mem_add.mp inAPP with inAP | inPending
    · rcases Multiset.mem_add.mp inAP with inA | inPermits
      · exact absurd (.inl head) (split.clean e inA)
      · exact inPermits
    · exact absurd (headed_inj head (split.pendingRows e inPending)) apart.permit_ask
  · obtain ⟨args, v, -, rfl⟩ := split.answerRows e inAnswers
    exact absurd (headed_inj head (headed_row _ _ _)) apart.permit_table

/-- A member of a split bag with the head of the pending rows is a pending row of the split. -/
theorem Split.mem_pending {A C permits pending answers : Multiset Expr}
    (split : Split askSym permitSym I c p A C permits pending answers) (apart : Apart askSym permitSym c.name)
    {e : Expr} (inC : e ∈ C) (head : Headed askSym e) : e ∈ pending := by
  rw [split.sum] at inC
  rcases Multiset.mem_add.mp inC with inAPP | inAnswers
  · rcases Multiset.mem_add.mp inAPP with inAP | inPending
    · rcases Multiset.mem_add.mp inAP with inA | inPermits
      · exact absurd (.inr (.inl head)) (split.clean e inA)
      · exact absurd (headed_inj (split.permitRows e inPermits) head) apart.permit_ask
    · exact inPending
  · obtain ⟨args, v, -, rfl⟩ := split.answerRows e inAnswers
    exact absurd (headed_inj head (headed_row _ _ _)) apart.ask_table

/-- A member of a split bag with the head of the function's table is an answer of the split. -/
theorem Split.mem_answers {A C permits pending answers : Multiset Expr}
    (split : Split askSym permitSym I c p A C permits pending answers) (apart : Apart askSym permitSym c.name)
    {e : Expr} (inC : e ∈ C) (head : Headed c.name e) : e ∈ answers := by
  rw [split.sum] at inC
  rcases Multiset.mem_add.mp inC with inAPP | inAnswers
  · rcases Multiset.mem_add.mp inAPP with inAP | inPending
    · rcases Multiset.mem_add.mp inAP with inA | inPermits
      · exact absurd (.inr (.inr head)) (split.clean e inA)
      · exact absurd (headed_inj (split.permitRows e inPermits) head) apart.permit_table
    · exact absurd (headed_inj (split.pendingRows e inPending) head) apart.ask_table
  · exact inAnswers

/-- **A bag with none of the call's rows, beside a permit for each of its rows, is related to itself.** -/
theorem related_start {A : Multiset Expr} (clean : ∀ e ∈ A, ¬ Hidden askSym permitSym c.name e) :
    PermitRelated askSym permitSym I c p A (A + A.map (groundPermit permitSym)) :=
  ⟨A.map (groundPermit permitSym), 0, 0, by simp, clean, fun e inside => by
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp inside
      exact headed_permit permitSym x,
    fun _ inside => absurd inside (Multiset.notMem_zero _), fun _ inside => absurd inside (Multiset.notMem_zero _),
    fun _ inA => .inl (Multiset.mem_map_of_mem _ inA)⟩

/-- **A request keeps the relation**: it turns the permit of a row into the pending row at its arguments. -/
theorem related_permitRequest (apart : Apart askSym permitSym c.name)
    (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, x ∈ p.freeVars) {A C C' : Multiset Expr}
    (related : PermitRelated askSym permitSym I c p A C)
    (fires : Rewrites [permitRequest askSym permitSym ρ c p] C C') :
    PermitRelated askSym permitSym I c p A C' := by
  obtain ⟨permits, pending, answers, split⟩ := related
  obtain ⟨r, member, θ, rest, sum, -, -, rfl⟩ := fires
  obtain rfl := List.mem_singleton.mp member
  have takeEq : ((permitRequest askSym permitSym ρ c p).body.take.map (inst θ) : Multiset Expr) =
      {groundPermit permitSym (inst θ p)} := by
    simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [inst_permitRow]
  rw [takeEq] at sum
  have inPermits : groundPermit permitSym (inst θ p) ∈ permits :=
    split.mem_permits apart (by rw [← sum]; exact Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _)))
      (headed_permit permitSym _)
  obtain ⟨permits', rfl⟩ := Multiset.exists_cons_of_mem inPermits
  have restEq : rest = A + permits' + pending + answers := by
    have whole : {groundPermit permitSym (inst θ p)} + rest =
        {groundPermit permitSym (inst θ p)} + (A + permits' + pending + answers) := by
      rw [sum, split.sum, ← Multiset.singleton_add]
      abel
    exact add_left_cancel whole
  refine ⟨permits', groundAsk askSym c.name (c.arguments.map (inst θ)) ::ₘ pending, answers, ?_, split.clean,
    fun e inside => split.permitRows e (Multiset.mem_cons_of_mem inside), fun e inside => ?_, split.answerRows,
    fun θ' inA => ?_⟩
  · simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [inst_askRow, restEq, ← Multiset.singleton_add]
    abel
  · rcases Multiset.mem_cons.mp inside with rfl | old
    · exact headed_ask _ _ _
    · exact split.pendingRows e old
  · rcases split.covered θ' inA with permit | pendingRow | answer
    · rcases Multiset.mem_cons.mp permit with same | kept
      · have agree := agree_of_inst_eq p (groundPermit_inj permitSym same)
        have sameArgs : c.arguments.map (inst θ') = c.arguments.map (inst θ) :=
          List.map_congr_left fun t inT => inst_congr t fun x inX => agree x (bound t inT x inX)
        rw [sameArgs]
        exact .inr (.inl (Multiset.mem_cons_self _ _))
      · exact .inl kept
    · exact .inr (.inl (Multiset.mem_cons_of_mem pendingRow))
    · exact .inr (.inr answer)

/-- **An answer keeps the relation**: it turns a pending row into the row of the graph at its arguments. -/
theorem related_answer (apart : Apart askSym permitSym c.name) (answering : Answers askSym I c.name answerers)
    {A C C' : Multiset Expr} (related : PermitRelated askSym permitSym I c p A C)
    (fires : Rewrites answerers C C') : PermitRelated askSym permitSym I c p A C' := by
  obtain ⟨permits, pending, answers, split⟩ := related
  obtain ⟨args, v, rest, value, rfl, rfl⟩ := answering.sound fires
  have inPending : groundAsk askSym c.name args ∈ pending :=
    split.mem_pending apart (Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))) (headed_ask _ _ _)
  obtain ⟨pending', rfl⟩ := Multiset.exists_cons_of_mem inPending
  have restEq : rest = A + permits + pending' + answers := by
    have whole : {groundAsk askSym c.name args} + rest =
        {groundAsk askSym c.name args} + (A + permits + pending' + answers) := by
      rw [split.sum, ← Multiset.singleton_add]
      abel
    exact add_left_cancel whole
  refine ⟨permits, pending', groundRow c.name args v ::ₘ answers, ?_, split.clean, split.permitRows,
    fun e inside => split.pendingRows e (Multiset.mem_cons_of_mem inside), fun e inside => ?_, fun θ' inA => ?_⟩
  · rw [restEq, ← Multiset.singleton_add]
    abel
  · rcases Multiset.mem_cons.mp inside with rfl | old
    · exact ⟨args, v, value, rfl⟩
    · exact split.answerRows e old
  · rcases split.covered θ' inA with permit | pendingRow | ⟨w, answer⟩
    · exact .inl permit
    · rcases Multiset.mem_cons.mp pendingRow with same | kept
      · rw [groundAsk_inj same]
        exact .inr (.inr ⟨v, Multiset.mem_cons_self _ _⟩)
      · exact .inr (.inl kept)
    · exact .inr (.inr ⟨w, Multiset.mem_cons_of_mem answer⟩)

/-- **The bag after a resume is related to the bag after the evaluation**, at the same match. -/
theorem resume_related
    (unseen : ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
      ¬ Hidden askSym permitSym c.name (inst θ q))
    {A C permits pending answers : Multiset Expr}
    (split : Split askSym permitSym I c p A C permits pending answers) (θ : ℕ → Expr) {rest' : Multiset Expr}
    (sumA : (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest' = A) :
    PermitRelated askSym permitSym I c p ((ρ.rule.body.produce.map (inst θ) : Multiset Expr) + rest')
      (((permitResume permitSym ρ).body.produce.map (inst θ) : Multiset Expr) +
        (rest' + (permits + pending + answers))) := by
  have permitsMade : (ρ.rule.body.produce.map (permitRow permitSym)).map (inst θ) =
      (ρ.rule.body.produce.map (inst θ)).map (groundPermit permitSym) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun m _ => inst_permitRow permitSym θ m
  have made : ((permitResume permitSym ρ).body.produce.map (inst θ) : Multiset Expr) =
      (ρ.rule.body.produce.map (inst θ) : Multiset Expr) +
        ((ρ.rule.body.produce.map (inst θ)).map (groundPermit permitSym) : Multiset Expr) := by
    show (((ρ.rule.body.produce ++ ρ.rule.body.produce.map (permitRow permitSym)).map (inst θ) : List Expr) :
      Multiset Expr) = _
    rw [List.map_append, permitsMade, Multiset.coe_add]
  refine ⟨((ρ.rule.body.produce.map (inst θ)).map (groundPermit permitSym) : Multiset Expr) + permits, pending,
    answers, ?_, fun e inside => ?_, fun e inside => ?_, split.pendingRows, split.answerRows,
    fun θ' inA' => ?_⟩
  · rw [made]
    abel
  · rcases Multiset.mem_add.mp inside with new | old
    · obtain ⟨m, inProduce, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp new)
      exact unseen θ m (List.mem_append_right _ inProduce)
    · exact split.clean e (by rw [← sumA]; exact Multiset.mem_add.mpr (.inr old))
  · rcases Multiset.mem_add.mp inside with new | old
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp new)
      exact headed_permit permitSym x
    · exact split.permitRows e old
  · rcases Multiset.mem_add.mp inA' with new | old
    · exact .inl (Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr
        (List.mem_map_of_mem (Multiset.mem_coe.mp new)))))
    · rcases split.covered θ' (by rw [← sumA]; exact Multiset.mem_add.mpr (.inr old)) with
        permit | pendingRow | answer
      · exact .inl (Multiset.mem_add.mpr (.inr permit))
      · exact .inr (.inl pendingRow)
      · exact .inr (.inr answer)

/-- **A resume is an atomic evaluation**, and the relation continues. -/
theorem related_permitResume (apart : Apart askSym permitSym c.name) (only : ρ.conditions = [c])
    (unseen : ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
      ¬ Hidden askSym permitSym c.name (inst θ q))
    {A C C' : Multiset Expr} (related : PermitRelated askSym permitSym I c p A C)
    (fires : Rewrites [permitResume permitSym ρ] C C') :
    ∃ A', EvalStep I ρ A A' ∧ PermitRelated askSym permitSym I c p A' C' := by
  obtain ⟨permits, pending, answers, split⟩ := related
  obtain ⟨r, member, θ, rest, sum, reads, equations, rfl⟩ := fires
  obtain rfl := List.mem_singleton.mp member
  have sum' : (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest = A + (permits + pending + answers) := by
    rw [show (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest = C from sum, split.sum]
    abel
  have hiddenRows : ∀ e ∈ permits + pending + answers, Hidden askSym permitSym c.name e := by
    intro e inside
    rcases Multiset.mem_add.mp inside with inPP | inAnswers
    · rcases Multiset.mem_add.mp inPP with inPermits | inPending
      · exact .inl (split.permitRows e inPermits)
      · exact .inr (.inl (split.pendingRows e inPending))
    · obtain ⟨args, v, -, rfl⟩ := split.answerRows e inAnswers
      exact .inr (.inr (headed_row _ _ _))
  have takesPublic : ∀ x ∈ (ρ.rule.body.take.map (inst θ) : Multiset Expr),
      ¬ Hidden askSym permitSym c.name x := by
    intro x inside
    obtain ⟨q, inTake, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp inside)
    exact unseen θ q (List.mem_append_left _ (List.mem_append_left _ inTake))
  obtain ⟨rest', aEq, restEq⟩ := split_apart sum' takesPublic hiddenRows
  have readsIn : ∀ q ∈ ρ.rule.body.read, inst θ q ∈ rest' := by
    intro q inside
    have inRest := reads q (List.mem_append_left _ inside)
    rw [restEq] at inRest
    rcases Multiset.mem_add.mp inRest with inRest' | inHidden
    · exact inRest'
    · exact absurd (hiddenRows _ inHidden)
        (unseen θ q (List.mem_append_left _ (List.mem_append_right _ inside)))
  have callIn := reads (callRow rows c) (List.mem_append_right _ (by simp [RuleWithCondition.calls, only]))
  rw [restEq, show inst θ (callRow rows c) = groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) from
    inst_row θ c.name c.arguments c.value] at callIn
  have inAnswers : groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) ∈ answers := by
    rcases Multiset.mem_add.mp callIn with inRest' | inHidden
    · exact absurd (.inr (.inr (headed_row _ _ _)))
        (split.clean _ (by rw [aEq]; exact Multiset.mem_add.mpr (.inr inRest')))
    · rcases Multiset.mem_add.mp inHidden with inPP | inAnswers
      · rcases Multiset.mem_add.mp inPP with inPermits | inPending
        · exact absurd (headed_inj (split.permitRows _ inPermits) (headed_row _ _ _)) apart.permit_table
        · exact absurd (headed_inj (split.pendingRows _ inPending) (headed_row _ _ _)) apart.ask_table
      · exact inAnswers
  obtain ⟨args, v, value, same⟩ := split.answerRows _ inAnswers
  obtain ⟨-, rfl, rfl⟩ := groundRow_inj same
  refine ⟨(ρ.rule.body.produce.map (inst θ) : Multiset Expr) + rest',
    ⟨θ, rest', aEq.symm, readsIn, equations, fun c' inside => ?_, rfl⟩, ?_⟩
  · rw [only, List.mem_singleton] at inside
    subst inside
    exact value
  · rw [restEq]
    exact resume_related unseen split θ aEq.symm

/-- **A pending row at arguments with a value is answered**, and the relation continues. -/
theorem answer_step (apart : Apart askSym permitSym c.name) (answering : Answers askSym I c.name answerers)
    {A C : Multiset Expr} (related : PermitRelated askSym permitSym I c p A C) {args : List Expr} {v : Expr}
    (inC : groundAsk askSym c.name args ∈ C) (value : I c.name args = some v) :
    ∃ C₁, Rewrites answerers C C₁ ∧ PermitRelated askSym permitSym I c p A C₁ ∧
      groundRow c.name args v ∈ C₁ := by
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem inC
  have fires : Rewrites answerers (groundAsk askSym c.name args ::ₘ rest) ({groundRow c.name args v} + rest) := by
    rw [← Multiset.singleton_add]
    exact answering.complete rest value
  exact ⟨_, fires, related_answer apart answering related fires,
    Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))⟩

/-- **A row with its permit is asked about**, and the relation continues. -/
theorem request_step (apart : Apart askSym permitSym c.name)
    (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, x ∈ p.freeVars)
    (unseen : ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
      ¬ Hidden askSym permitSym c.name (inst θ q))
    {A C : Multiset Expr} (related : PermitRelated askSym permitSym I c p A C) (θ : ℕ → Expr)
    (inC : groundPermit permitSym (inst θ p) ∈ C)
    (readable : ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read, inst θ q ∈ A) :
    ∃ C₀, Rewrites [permitRequest askSym permitSym ρ c p] C C₀ ∧ PermitRelated askSym permitSym I c p A C₀ ∧
      groundAsk askSym c.name (c.arguments.map (inst θ)) ∈ C₀ := by
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem inC
  have fires : Rewrites [permitRequest askSym permitSym ρ c p] (groundPermit permitSym (inst θ p) ::ₘ rest)
      ({groundAsk askSym c.name (c.arguments.map (inst θ))} + rest) := by
    refine ⟨_, List.mem_singleton_self _, θ, rest, ?_, fun q inside => ?_, fun e inside => ?_, ?_⟩
    · simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_permitRow, Multiset.singleton_add]
    · obtain ⟨permits, pending, answers, split⟩ := related
      have inWhole : inst θ q ∈ groundPermit permitSym (inst θ p) ::ₘ rest := by
        rw [split.sum]
        exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr
          (.inl (readable q inside))))))
      rcases Multiset.mem_cons.mp inWhole with same | inRest
      · have head : Headed permitSym (inst θ q) := by
          rw [same]
          exact headed_permit permitSym _
        exact absurd (.inl head) (unseen θ q (List.mem_append_left _ inside))
      · exact inRest
    · simp [equationsOf, permitRequest] at inside
    · simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_askRow]
  exact ⟨_, fires, related_permitRequest apart bound related fires,
    Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))⟩

/-- **An atomic evaluation is at most one request and one answer, then a resume.** -/
theorem related_atomic (apart : Apart askSym permitSym c.name) (only : ρ.conditions = [c])
    (trigger : p ∈ ρ.rule.body.take) (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, x ∈ p.freeVars)
    (unseen : ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
      ¬ Hidden askSym permitSym c.name (inst θ q))
    (answering : Answers askSym I c.name answerers) {A A' C : Multiset Expr}
    (related : PermitRelated askSym permitSym I c p A C) (evaluates : EvalStep I ρ A A') :
    ∃ C₁ C', Relation.ReflTransGen (Internal askSym permitSym ρ c p answerers) C C₁ ∧
      Rewrites [permitResume permitSym ρ] C₁ C' ∧ PermitRelated askSym permitSym I c p A' C' := by
  obtain ⟨θ, rest₀, sumA, reads, equations, conditions, rfl⟩ := evaluates
  have value := conditions c (by rw [only]; exact List.mem_singleton_self _)
  have inA : inst θ p ∈ A := by
    rw [← sumA]
    exact Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_map_of_mem trigger)))
  have readable : ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read, inst θ q ∈ A := by
    intro q inside
    rw [← sumA]
    rcases List.mem_append.mp inside with inTake | inRead
    · exact Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_map_of_mem inTake)))
    · exact Multiset.mem_add.mpr (.inr (reads q inRead))
  have reach : ∃ C₁, Relation.ReflTransGen (Internal askSym permitSym ρ c p answerers) C C₁ ∧
      PermitRelated askSym permitSym I c p A C₁ ∧
      groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) ∈ C₁ := by
    obtain ⟨permits, pending, answers, split⟩ := related
    rcases split.covered θ inA with permit | pendingRow | ⟨w, answer⟩
    · obtain ⟨C₀, requested, related₀, asked⟩ := request_step (ρ := ρ) apart bound unseen
        ⟨permits, pending, answers, split⟩ θ (by
          rw [split.sum]
          exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr permit))))))
        readable
      obtain ⟨C₁, answered, related₁, row⟩ := answer_step apart answering related₀ asked value
      exact ⟨C₁, (Relation.ReflTransGen.single (.inl requested)).tail (.inr answered), related₁, row⟩
    · obtain ⟨C₁, answered, related₁, row⟩ := answer_step apart answering ⟨permits, pending, answers, split⟩
        (by
          rw [split.sum]
          exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inr pendingRow)))) value
      exact ⟨C₁, .single (.inr answered), related₁, row⟩
    · obtain ⟨args, v, value', same⟩ := split.answerRows _ answer
      obtain ⟨-, rfl, rfl⟩ := groundRow_inj same
      obtain rfl : w = inst θ c.value := Option.some.inj (value'.symm.trans value)
      exact ⟨C, .refl, ⟨permits, pending, answers, split⟩, by
        rw [split.sum]
        exact Multiset.mem_add.mpr (.inr answer)⟩
  obtain ⟨C₁, run, ⟨permits, pending, answers, split⟩, row⟩ := reach
  have inAnswers := split.mem_answers apart row (headed_row _ _ _)
  refine ⟨C₁, _, run, ⟨permitResume permitSym ρ, List.mem_singleton_self _, θ,
    rest₀ + (permits + pending + answers), ?_, fun q inside => ?_, equations, rfl⟩,
    resume_related unseen split θ sumA⟩
  · show (ρ.rule.body.take.map (inst θ) : Multiset Expr) + (rest₀ + (permits + pending + answers)) = C₁
    rw [split.sum, ← sumA]
    abel
  · rcases List.mem_append.mp (show q ∈ ρ.rule.body.read ++ ρ.conditions.map (callRow rows) from inside) with
      inRead | inCalls
    · exact Multiset.mem_add.mpr (.inl (reads q inRead))
    · rw [only] at inCalls
      obtain rfl := List.mem_singleton.mp inCalls
      rw [show inst θ (callRow rows c) = groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) from
        inst_row θ c.name c.arguments c.value]
      exact Multiset.mem_add.mpr (.inr (Multiset.mem_add.mpr (.inr inAnswers)))

/-! ## The internal firings stop -/

/-- **Every internal firing lowers the weight.** -/
theorem internal_decreases (apart : Apart askSym permitSym c.name) (answering : Answers askSym I c.name answerers)
    {C C' : Multiset Expr} (moved : Internal askSym permitSym ρ c p answerers C C') :
    weight askSym permitSym C' < weight askSym permitSym C := by
  rcases moved with requested | answered
  · obtain ⟨r, member, θ, rest, rfl, -, -, rfl⟩ := requested
    obtain rfl := List.mem_singleton.mp member
    have takeEq : ((permitRequest askSym permitSym ρ c p).body.take.map (inst θ) : Multiset Expr) =
        groundPermit permitSym (inst θ p) ::ₘ 0 := by
      simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_permitRow]
      rfl
    have madeEq : ((permitRequest askSym permitSym ρ c p).body.produce.map (inst θ) : Multiset Expr) =
        groundAsk askSym c.name (c.arguments.map (inst θ)) ::ₘ 0 := by
      simp only [permitRequest, List.map_cons, List.map_nil, Multiset.coe_singleton]
      rw [inst_askRow]
      rfl
    have isPermit : Headed permitSym (groundPermit permitSym (inst θ p)) := headed_permit permitSym _
    have notAsk : ¬ Headed askSym (groundPermit permitSym (inst θ p)) :=
      fun head => apart.permit_ask (headed_inj isPermit head)
    have isAsk : Headed askSym (groundAsk askSym c.name (c.arguments.map (inst θ))) := headed_ask _ _ _
    have notPermit : ¬ Headed permitSym (groundAsk askSym c.name (c.arguments.map (inst θ))) :=
      fun head => apart.permit_ask (headed_inj head isAsk)
    rw [takeEq, madeEq]
    simp only [weight, Multiset.countP_add, Multiset.countP_cons, Multiset.countP_zero, if_pos isPermit,
      if_neg notAsk, if_pos isAsk, if_neg notPermit]
    omega
  · obtain ⟨args, v, rest, -, rfl, rfl⟩ := answering.sound answered
    have isAsk : Headed askSym (groundAsk askSym c.name args) := headed_ask _ _ _
    have notPermit : ¬ Headed permitSym (groundAsk askSym c.name args) :=
      fun head => apart.permit_ask (headed_inj head isAsk)
    have isRow : Headed c.name (groundRow c.name args v) := headed_row _ _ _
    have rowNotPermit : ¬ Headed permitSym (groundRow c.name args v) :=
      fun head => apart.permit_table (headed_inj head isRow)
    have rowNotAsk : ¬ Headed askSym (groundRow c.name args v) :=
      fun head => apart.ask_table (headed_inj head isRow)
    rw [← Multiset.cons_zero (groundAsk askSym c.name args), ← Multiset.cons_zero (groundRow c.name args v)]
    simp only [weight, Multiset.countP_add, Multiset.countP_cons, Multiset.countP_zero, if_pos isAsk,
      if_neg notPermit, if_neg rowNotPermit, if_neg rowNotAsk]
    omega

/-- **The internal firings stop**: no run of requests and answers goes on for ever. -/
theorem internal_terminates (apart : Apart askSym permitSym c.name)
    (answering : Answers askSym I c.name answerers) :
    WellFounded (fun C' C : Multiset Expr => Internal askSym permitSym ρ c p answerers C C') :=
  Subrelation.wf (fun {_ _} moved => internal_decreases apart answering moved)
    (InvImage.wf (weight askSym permitSym) Nat.lt_wfRel.wf)

/-! ## Where the function has no value, the call waits -/

/-- **A pending row at arguments with no value is taken by no firing of the call's program.** -/
theorem undefined_waits (apart : Apart askSym permitSym c.name)
    (unseen : ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
      ¬ Hidden askSym permitSym c.name (inst θ q))
    (answering : Answers askSym I c.name answerers) {args : List Expr} (undefined : I c.name args = none)
    {C C' : Multiset Expr} (fires : Rewrites (permitProgram askSym permitSym ρ c p answerers) C C')
    (waiting : groundAsk askSym c.name args ∈ C) : groundAsk askSym c.name args ∈ C' := by
  have isAsk : Headed askSym (groundAsk askSym c.name args) := headed_ask _ _ _
  obtain ⟨r, member, θ, rest, sum, reads, equations, made⟩ := fires
  rcases List.mem_cons.mp member with rfl | later
  · -- the request takes a permit
    rw [made]
    rw [← sum] at waiting
    rcases Multiset.mem_add.mp waiting with taken | kept
    · have isPermit : groundAsk askSym c.name args = groundPermit permitSym (inst θ p) := by
        simpa [permitRequest, inst_permitRow] using taken
      exact absurd (headed_inj (isPermit ▸ headed_permit permitSym (inst θ p)) isAsk) apart.permit_ask
    · exact Multiset.mem_add.mpr (.inr kept)
  · rcases List.mem_append.mp later with inAnswerers | isResume
    · -- an answer takes a pending row at arguments with a value
      obtain ⟨args', v, rest', value, rfl, rfl⟩ :=
        answering.sound ⟨r, inAnswerers, θ, rest, sum, reads, equations, made⟩
      rcases Multiset.mem_add.mp waiting with taken | kept
      · have sameArgs := groundAsk_inj (Multiset.mem_singleton.mp taken)
        rw [sameArgs, value] at undefined
        exact absurd undefined (by simp)
      · exact Multiset.mem_add.mpr (.inr kept)
    · -- the resume takes the rule's rows
      obtain rfl := List.mem_singleton.mp isResume
      rw [made]
      rw [← sum] at waiting
      rcases Multiset.mem_add.mp waiting with taken | kept
      · obtain ⟨q, inTake, same⟩ := List.mem_map.mp (Multiset.mem_coe.mp taken)
        have hidden : Hidden askSym permitSym c.name (inst θ q) := by
          rw [same]
          exact .inr (.inl isAsk)
        exact absurd hidden (unseen θ q (List.mem_append_left _ (List.mem_append_left _ inTake)))
      · exact Multiset.mem_add.mpr (.inr kept)

/-- **It stays in every bag of every run of the call.** -/
theorem undefined_waits_run (apart : Apart askSym permitSym c.name)
    (unseen : ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
      ¬ Hidden askSym permitSym c.name (inst θ q))
    (answering : Answers askSym I c.name answerers) {args : List Expr} (undefined : I c.name args = none)
    {C C' : Multiset Expr}
    (run : Relation.ReflTransGen (Rewrites (permitProgram askSym permitSym ρ c p answerers)) C C')
    (waiting : groundAsk askSym c.name args ∈ C) : groundAsk askSym c.name args ∈ C' := by
  induction run with
  | refl => exact waiting
  | tail _ last ih => exact undefined_waits apart unseen answering undefined last ih

/-! ## The general notion -/

/-- An internal firing is a firing of the call's program. -/
theorem internal_step {C C' : Multiset Expr} (moved : Internal askSym permitSym ρ c p answerers C C') :
    Rewrites (permitProgram askSym permitSym ρ c p answerers) C C' := by
  rcases moved with requested | answered
  · exact rewrites_of_mem (List.mem_cons_self) requested
  · obtain ⟨r, inAnswerers, witness⟩ := answered
    exact ⟨r, List.mem_cons_of_mem _ (List.mem_append_left _ inAnswerers), witness⟩

theorem internal_run {C C' : Multiset Expr}
    (run : Relation.ReflTransGen (Internal askSym permitSym ρ c p answerers) C C') :
    Relation.ReflTransGen (Rewrites (permitProgram askSym permitSym ρ c p answerers)) C C' := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (internal_step last)

/-- **The call and the atomic evaluation, as an operational correspondence**: the atomic evaluation of the
rule on bags, and rewriting by the call's program, related by `PermitRelated`. A request and an answer are
silent, a resume is one evaluation, and an evaluation is a run of the call that ends with a resume. -/
def permitCorrespondence (apart : Apart askSym permitSym c.name) (only : ρ.conditions = [c])
    (trigger : p ∈ ρ.rule.body.take) (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, x ∈ p.freeVars)
    (unseen : ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
      ¬ Hidden askSym permitSym c.name (inst θ q))
    (answering : Answers askSym I c.name answerers) :
    OperationalCorrespondence (evaluation I {ρ})
      (Machines.rewriting (permitProgram askSym permitSym ρ c p answerers)) where
  related A C := PermitRelated askSym permitSym I c p A C
  readStep := by
    intro A C C' related fires
    obtain ⟨r, member, witness⟩ := fires
    rcases List.mem_cons.mp member with rfl | later
    · exact .inl (related_permitRequest apart bound related ⟨_, List.mem_singleton_self _, witness⟩)
    · rcases List.mem_append.mp later with inAnswerers | isResume
      · exact .inl (related_answer apart answering related ⟨r, inAnswerers, witness⟩)
      · obtain rfl := List.mem_singleton.mp isResume
        obtain ⟨A', evaluates, related'⟩ :=
          related_permitResume apart only unseen related ⟨_, List.mem_singleton_self _, witness⟩
        exact .inr ⟨A', ⟨ρ, Set.mem_singleton ρ, evaluates⟩, related'⟩
  forward := by
    intro A A' C related evaluates
    obtain ⟨ρ', isRule, single⟩ := evaluates
    obtain rfl := Set.mem_singleton_iff.mp isRule
    obtain ⟨C₁, C', run, resumed, related'⟩ :=
      related_atomic apart only trigger bound unseen answering related single
    refine ⟨C', (executionPath_nonempty_iff_multiStep
      (Machines.rewriting (permitProgram askSym permitSym ρ' c p answerers)) _ _).mpr
      ((Meredith.multiStep_iff_reflTransGen
        (Machines.rewriting (permitProgram askSym permitSym ρ' c p answerers)) C C').mpr ?_), related'⟩
    exact (internal_run run).tail (rewrites_of_mem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))) resumed)

end Relation

/-! ## The call's firings are firings of the step -/

section Fragment

variable {askSym permitSym : ℕ} {I : Interpretation ℕ Expr} {ρ : RuleWithCondition ℕ Tm} {c : Condition ℕ Tm}
  {p : Tm} {answerers : List SRule}

/-- The request is in the fragment when the trigger's unknowns include the arguments'. -/
theorem permitRequest_fragment (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, x ∈ p.freeVars) :
    RangeRestrictedPositive (permitRequest askSym permitSym ρ c p) := by
  refine ⟨rfl, rfl, fun t member x inT => ?_⟩
  have isAsk : t = askRow askSym c.name c.arguments := by
    simpa [written, permitRequest] using member
  subst isAsk
  obtain ⟨u, inArguments, inU⟩ := (mem_vars_askRow askSym c.name c.arguments).mp inT
  exact ⟨permitRow permitSym p, List.mem_append_left _ (List.mem_singleton_self _),
    (mem_vars_permitRow permitSym p).mpr (bound u inArguments x inU)⟩

/-- The resume is in the fragment when the rule's table read is. -/
theorem permitResume_fragment (noCollect : ρ.rule.collect = []) (guards : ρ.rule.body.checks.all isGuard = true)
    (restricted : ρ.RangeRestrictedWith) : RangeRestrictedPositive (permitResume permitSym ρ) := by
  refine ⟨noCollect, guards, fun t member x inT => ?_⟩
  have tableBound : ∀ u ∈ written (ρ.tableRule rows), ∀ y ∈ u.freeVars, Bound (ρ.tableRule rows) y :=
    ρ.rangeRestricted_tableRule restricted
  have cases : t ∈ written (ρ.tableRule rows) ∨ ∃ m ∈ ρ.rule.body.produce, t = permitRow permitSym m := by
    have unfolded : t ∈ ρ.rule.body.tell.map Prod.fst ++ ρ.rule.body.tell.map Prod.snd ++
        ρ.rule.body.checks.flatMap checkTerms ++
        (ρ.rule.body.produce ++ ρ.rule.body.produce.map (permitRow permitSym)) := member
    rcases List.mem_append.mp unfolded with early | made
    · exact .inl (List.mem_append_left _ early)
    · rcases List.mem_append.mp made with plain | permit
      · exact .inl (List.mem_append_right _ plain)
      · obtain ⟨m, inProduce, rfl⟩ := List.mem_map.mp permit
        exact .inr ⟨m, inProduce, rfl⟩
  rcases cases with plain | ⟨m, inProduce, rfl⟩
  · exact tableBound t plain x inT
  · exact tableBound m (List.mem_append_right _ inProduce) x ((mem_vars_permitRow permitSym m).mp inT)

/-- **The rules of the call are in the fragment.** -/
theorem permitProgram_fragment (noCollect : ρ.rule.collect = []) (guards : ρ.rule.body.checks.all isGuard = true)
    (restricted : ρ.RangeRestrictedWith) (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, x ∈ p.freeVars)
    (answerFragment : ∀ r ∈ answerers, RangeRestrictedPositive r) :
    ∀ r ∈ permitProgram askSym permitSym ρ c p answerers, RangeRestrictedPositive r := by
  intro r member
  rcases List.mem_cons.mp member with rfl | later
  · exact permitRequest_fragment bound
  · rcases List.mem_append.mp later with inAnswerers | isResume
    · exact answerFragment r inAnswerers
    · rw [List.mem_singleton.mp isResume]
      exact permitResume_fragment noCollect guards restricted

/-- **The call and the atomic evaluation, on states of `RuleSyntax.step`**: the atomic evaluation of the rule
on bags, and the step of the call's program, related by reading a state as a bag related to the atomic bag. -/
def permitStepCorrespondence (O : Type) [DecidableEq O] [Infinite O] (apart : Apart askSym permitSym c.name)
    (only : ρ.conditions = [c]) (trigger : p ∈ ρ.rule.body.take)
    (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, x ∈ p.freeVars)
    (unseen : ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
      ¬ Hidden askSym permitSym c.name (inst θ q))
    (answering : Answers askSym I c.name answerers) (noCollect : ρ.rule.collect = [])
    (guards : ρ.rule.body.checks.all isGuard = true) (restricted : ρ.RangeRestrictedWith)
    (answerFragment : ∀ r ∈ answerers, RangeRestrictedPositive r) :
    OperationalCorrespondence (evaluation I {ρ})
      (Machines.stepSystem O (permitProgram askSym permitSym ρ c p answerers)) :=
  (permitCorrespondence apart only trigger bound unseen answering).comp
    (Machines.correspondence (permitProgram_fragment noCollect guards restricted bound answerFragment))

end Fragment

#print axioms split_apart
#print axioms related_start
#print axioms related_permitRequest
#print axioms related_answer
#print axioms related_permitResume
#print axioms related_atomic
#print axioms internal_decreases
#print axioms internal_terminates
#print axioms undefined_waits
#print axioms undefined_waits_run
#print axioms permitCorrespondence
#print axioms permitProgram_fragment
#print axioms permitStepCorrespondence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.PermitCalls
