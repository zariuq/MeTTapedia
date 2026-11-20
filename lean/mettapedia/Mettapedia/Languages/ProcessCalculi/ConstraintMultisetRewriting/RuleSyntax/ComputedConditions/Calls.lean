import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Runs

/-!
# A function defined by a rule of the program: the call through a pending row

A function **defined by one equation** (`Defined`: `f(x₁, …, xₙ) = body`, distinct parameters, the body's
unknowns among them) is total on argument lists of its length and has no choice; its interpretation is
`Defined.interp`. A rule with one condition `r := f(t̄)` is evaluated by it atomically (`EvalStep`), or
through **the call**, three rules of the program (`callProgram`):

* **the request** (`request`): read the rule's take and read patterns, make the pending row
  `ask f t̄` (it consumes nothing);
* **the function's equation as a rule** (`equationRule`): take `ask f x̄`, make the row of `f`'s table
  `f x̄ body`;
* **the resume**: the rule's table read (`RuleWithCondition.tableRule`), which takes and reads what the
  rule does and reads the answer row.

Firings are read on bags of ground rows, by matching (`Machines.Rewrites`). The three rules are in the
fragment of `Machines.Rewriting` when the rule has no collect pattern, only equation checks, every written
unknown bound, and the condition's arguments bound by its take and read patterns (`callProgram_fragment`).
Then, at every state that reads as a bag and so along runs of every length, a firing of the call's program
admitted by `RuleSyntax.step` is one rewrite of the bag and a rewrite is one admitted firing
(`callCorrespondence`, an instance of `Machines.correspondence`).

## The weak bisimulation

A bag of the call **is related** to a bag of the atomic system (`Related`) when it is that bag beside
pending rows and answer rows of the function's graph, and the atomic bag has none (`Clean`). With the
request and the equation internal and the resume visible:

* `related_request`, `related_equation`: an internal firing keeps the relation;
* `related_resume`: a resume is an atomic evaluation, and the relation continues;
* `related_atomic`: an atomic evaluation is a request, an equation and a resume;
* `related_rows`: related bags hold the same rows other than pending and answer rows;
* `related_refl`: every clean bag is related to itself.

Hypotheses: the rule's take, read and made patterns never have a pending or table row as an instance
(`SeesNoPending`), the pending rows have their own symbol, and the condition's arguments are as many as
the parameters. **Control** (`watch_sees_pending`, `watch_never_at_clean`): a neighbour that reads the
pending row fires after a request and never at a clean bag, so with it in the program the relation fails.

## What this relation does not see

The request takes nothing, so wherever it fires it fires again: from one bag the call has runs of internal
firings of every length (`CallInstances.request_refires`, `CallInstances.request_unbounded`), also for a
test that the atomic evaluation refuses (`CallInstances.test_call_unbounded`). The relation above is weak:
it relates the atomic system, which has no internal firing, to a program with internal runs without bound.
A function with no value at some arguments is not modelled here (`Defined` has a value at every argument
list of its length). The call that asks once, with a function given by any interpretation, is in
`PermitCalls`.

The request does not consume the rule's rows: a firing that intervenes between request and resume meets
the rule's rows as they are, and the resume checks everything again, atomically. **Control for a request
that consumes them** (`consumingRequest`, `test_refused_atomically`, `consuming_request_fires`): for a
condition that is a test (`no := isOne(x)` with the answer `yes`), the atomic evaluation refuses and keeps
the row, while a request that takes the row fires and loses it.

## The hosting theorem's `let`

The hosting translation's `bindStartRule` and `bindValueRule` are the consuming form for one
alternative: the request takes the alternative's row and keeps the continuation in its own stack
(`push(P, D, FS)`), the resume tells `P ≐ T`. Their one-firing correspondences are
`Hosting.simulation_letStart`, `Hosting.simulation_letBind`, `Hosting.reflection_bindStart` and
`Hosting.reflection_bindValue`, under the hygiene `Hosting.FramePrivate`. There the source semantics is
sequential (a failed bind fails the alternative), so consuming at the request is right; for a rule of a
program whose rows a neighbour shares, the request here does not consume.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SRule inst inst_congr equationsOf RangeRestrictedPositive Bound written isGuard
  mem_vars_var not_mem_vars_const)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Rewrites)

/-! ## A function defined by one equation -/

/-- **A function defined by one equation**: `name(params) = body`, distinct parameters, the body's unknowns
among them. -/
structure Defined where
  name : ℕ
  params : List ℕ
  body : Tm
  distinct : params.Nodup
  closed : ∀ x ∈ body.freeVars, x ∈ params

/-- The parameters bound to arguments. -/
def bindParams : List ℕ → List Expr → ℕ → Expr
  | p :: ps, a :: as, x => if x = p then a else bindParams ps as x
  | _, _, _ => .sym 0

theorem bindParams_map (θ : ℕ → Expr) : ∀ (params : List ℕ) {x : ℕ}, x ∈ params →
    bindParams params (params.map θ) x = θ x
  | [], _, inside => absurd inside List.not_mem_nil
  | p :: ps, x, inside => by
      by_cases same : x = p
      · subst same
        simp [bindParams]
      · simp only [List.map_cons, bindParams, if_neg same]
        exact bindParams_map θ ps ((List.mem_cons.mp inside).resolve_left same)

theorem map_bindParams : ∀ (params : List ℕ) (args : List Expr), params.Nodup → params.length = args.length →
    params.map (bindParams params args) = args
  | [], [], _, _ => rfl
  | [], _ :: _, _, lengths => by simp at lengths
  | _ :: _, [], _, lengths => by simp at lengths
  | p :: ps, a :: as, nodup, lengths => by
      have fresh : p ∉ ps := (List.nodup_cons.mp nodup).1
      have tail : ps.map (bindParams (p :: ps) (a :: as)) = ps.map (bindParams ps as) :=
        List.map_congr_left fun x inside => by
          have different : x ≠ p := fun same => fresh (same ▸ inside)
          simp only [bindParams, if_neg different]
      rw [List.map_cons, tail, map_bindParams ps as (List.nodup_cons.mp nodup).2 (Nat.succ.inj lengths)]
      simp [bindParams]

namespace Defined

variable (d : Defined)

/-- **The interpretation of a defined function**: on argument lists of its length, the body at them. -/
def interp : Interpretation ℕ Expr :=
  fun g args => if g = d.name ∧ args.length = d.params.length then some (inst (bindParams d.params args) d.body)
    else none

theorem interp_eq {args : List Expr} (lengths : args.length = d.params.length) :
    d.interp d.name args = some (inst (bindParams d.params args) d.body) := by
  simp [interp, lengths]

/-- **The body at the parameters' values.** -/
theorem inst_body (θ : ℕ → Expr) : inst θ d.body = inst (bindParams d.params (d.params.map θ)) d.body :=
  inst_congr d.body fun x inside => (bindParams_map θ d.params (d.closed x inside)).symm

end Defined

/-! ## The call

The atomic evaluation on bags is `EvalStep` of `Runs`. -/

section Call

variable (askSym : ℕ)

/-- **A pending row** `ask f t̄`, with its own symbol. -/
def askRow (f : ℕ) (args : List Tm) : Tm := spine (.const (.sym askSym)) (.const (.sym f) :: args)

/-- A ground pending row. -/
def groundAsk (f : ℕ) (args : List Expr) : Expr := groundSpine (.sym askSym) (.sym f :: args)

theorem inst_askRow (θ : ℕ → Expr) (f : ℕ) (args : List Tm) :
    inst θ (askRow askSym f args) = groundAsk askSym f (args.map (inst θ)) := by
  rw [askRow, inst_spine]
  rfl

/-- The unknowns of a pending row are those of its arguments. -/
theorem mem_vars_askRow {x : ℕ} (f : ℕ) (args : List Tm) :
    x ∈ (askRow askSym f args).freeVars ↔ ∃ t ∈ args, x ∈ t.freeVars := by
  rw [askRow, mem_vars_spine]
  constructor
  · rintro (inHead | ⟨t, member, inT⟩)
    · exact absurd inHead not_mem_vars_const
    · rcases List.mem_cons.mp member with rfl | inArgs
      · exact absurd inT not_mem_vars_const
      · exact ⟨t, inArgs, inT⟩
  · rintro ⟨t, member, inT⟩
    exact .inr ⟨t, List.mem_cons_of_mem _ member, inT⟩

/-- **The request**: read the rule's take and read patterns, make the pending row of its condition. -/
def request (ρ : RuleWithCondition ℕ Tm) (c : Condition ℕ Tm) : SRule :=
  ⟨PUnit.unit, ⟨[], ρ.rule.body.take ++ ρ.rule.body.read, [], [], [askRow askSym c.name c.arguments]⟩, []⟩

/-- **The function's equation as a rule**: take a pending row of the function, make the row of its table at
the body. -/
def equationRule (d : Defined) : SRule :=
  ⟨PUnit.unit, ⟨[askRow askSym d.name (d.params.map .var)], [], [], [],
    [rows.row d.name (d.params.map .var) d.body]⟩, []⟩

/-- **The program of the call**: the request, the equation, and the table read, which resumes. -/
def callProgram (ρ : RuleWithCondition ℕ Tm) (c : Condition ℕ Tm) (d : Defined) : List SRule :=
  [request askSym ρ c, equationRule askSym d, ρ.tableRule rows]

/-- **The request is in the fragment** when the condition's arguments use only unknowns bound by the rule's
take and read patterns. -/
theorem request_fragment {ρ : RuleWithCondition ℕ Tm} {c : Condition ℕ Tm}
    (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, Bound ρ.rule x) :
    RangeRestrictedPositive (request askSym ρ c) := by
  refine ⟨rfl, rfl, fun t member x inT => ?_⟩
  have isAsk : t = askRow askSym c.name c.arguments := by
    simpa [written, request] using member
  subst isAsk
  obtain ⟨u, inArguments, inU⟩ := (mem_vars_askRow askSym c.name c.arguments).mp inT
  obtain ⟨q, inPatterns, inQ⟩ := bound u inArguments x inU
  refine ⟨q, ?_, inQ⟩
  show q ∈ [] ++ (ρ.rule.body.take ++ ρ.rule.body.read)
  exact inPatterns

/-- **The function's equation is in the fragment.** -/
theorem equationRule_fragment (d : Defined) : RangeRestrictedPositive (equationRule askSym d) := by
  refine ⟨rfl, rfl, fun t member x inT => ?_⟩
  have isRow : t = rows.row d.name (d.params.map .var) d.body := by
    simpa [written, equationRule] using member
  subst isRow
  have inParams : x ∈ d.params := by
    rcases (mem_vars_callRow ⟨d.body, d.name, d.params.map .var⟩).mp inT with ⟨u, inArguments, inU⟩ | inBody
    · obtain ⟨y, inY, rfl⟩ := List.mem_map.mp inArguments
      rw [mem_vars_var.mp inU]
      exact inY
    · exact d.closed x inBody
  exact ⟨askRow askSym d.name (d.params.map .var), List.mem_singleton_self _,
    (mem_vars_askRow askSym d.name _).mpr ⟨.var x, List.mem_map_of_mem inParams, mem_vars_var.mpr rfl⟩⟩

/-- **The rules of the call are in the fragment**, for a rule with no collect pattern, only equation checks,
every written unknown bound, and the condition's arguments bound by its take and read patterns. -/
theorem callProgram_fragment {ρ : RuleWithCondition ℕ Tm} {c : Condition ℕ Tm} (d : Defined)
    (noCollect : ρ.rule.collect = []) (guards : ρ.rule.body.checks.all isGuard = true)
    (restricted : ρ.RangeRestrictedWith) (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, Bound ρ.rule x) :
    ∀ r ∈ callProgram askSym ρ c d, RangeRestrictedPositive r := by
  intro r member
  simp only [callProgram, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact request_fragment askSym bound
  · exact equationRule_fragment askSym d
  · exact ρ.fragment_tableRule noCollect guards restricted

/-- **The call's firings are firings of `RuleSyntax.step`, along runs**: at every state that reads as a bag,
an admitted firing of the call's program is one rewrite of the bag, and a rewrite is one admitted firing, with
the result read as the rewritten bag. The instance of `Machines.correspondence` at the call's program. -/
def callCorrespondence (O : Type) [DecidableEq O] [Infinite O] {ρ : RuleWithCondition ℕ Tm}
    {c : Condition ℕ Tm} (d : Defined) (noCollect : ρ.rule.collect = [])
    (guards : ρ.rule.body.checks.all isGuard = true) (restricted : ρ.RangeRestrictedWith)
    (bound : ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, Bound ρ.rule x) :
    OperationalCorrespondence (Machines.rewriting (callProgram askSym ρ c d))
      (Machines.stepSystem O (callProgram askSym ρ c d)) :=
  Machines.correspondence (callProgram_fragment askSym d noCollect guards restricted bound)

/-- A pending row of the function `f`. -/
def IsAsk (f : ℕ) (e : Expr) : Prop := ∃ args, e = groundAsk askSym f args

/-- A row of the table of `f`. -/
def IsTable (f : ℕ) (e : Expr) : Prop := ∃ args v, e = groundRow f args v

/-- A pending row or a table row of `f`. -/
def Private (f : ℕ) (e : Expr) : Prop := IsAsk askSym f e ∨ IsTable f e

/-- **A clean bag**: no pending row and no table row of `f`. -/
def Clean (f : ℕ) (A : Multiset Expr) : Prop := ∀ e ∈ A, ¬ Private askSym f e

/-- **The rule sees no pending row**: no instance of its take, read or made patterns is a pending or a table
row of `f`. -/
def SeesNoPending (f : ℕ) (ρ : RuleWithCondition ℕ Tm) : Prop :=
  ∀ θ : ℕ → Expr, ∀ q ∈ ρ.rule.body.take ++ ρ.rule.body.read ++ ρ.rule.body.produce,
    ¬ Private askSym f (inst θ q)

/-- **Related bags**: the call's bag is the atomic bag beside pending rows and answer rows of the graph. -/
def Related (d : Defined) (A C : Multiset Expr) : Prop :=
  Clean askSym d.name A ∧ ∃ pending answers : Multiset Expr, C = A + pending + answers ∧
    (∀ e ∈ pending, IsAsk askSym d.name e) ∧
    ∀ e ∈ answers, ∃ args : List Expr, args.length = d.params.length ∧
      e = groundRow d.name args (inst (bindParams d.params args) d.body)

theorem ask_not_table {f : ℕ} (apart : f ≠ askSym) {e : Expr} (ask : IsAsk askSym f e) : ¬ IsTable f e := by
  rintro ⟨args', v, rfl⟩
  obtain ⟨args, same⟩ := ask
  have heads := congrArg spineHead same
  rw [groundRow, groundAsk, spineHead_groundSpine, spineHead_groundSpine] at heads
  exact apart (Expr.sym.inj heads)

/-- **Splitting a clean part off**: rows that are not private, beside a rest, are a clean bag beside private
rows only when the clean bag holds them. -/
theorem split_clean {f : ℕ} {X R A P : Multiset Expr} (sum : X + R = A + P)
    (clean : ∀ x ∈ X, ¬ Private askSym f x) (priv : ∀ p ∈ P, Private askSym f p) :
    ∃ rest, A = X + rest ∧ R = rest + P := by
  have le : X ≤ A := by
    rw [Multiset.le_iff_count]
    intro x
    by_cases inX : x ∈ X
    · have notP : Multiset.count x P = 0 := Multiset.count_eq_zero.mpr fun inP => clean x inX (priv x inP)
      have := congrArg (Multiset.count x) sum
      rw [Multiset.count_add, Multiset.count_add, notP, add_zero] at this
      omega
    · rw [Multiset.count_eq_zero.mpr inX]
      exact Nat.zero_le _
  refine ⟨A - X, (add_tsub_cancel_of_le le).symm, ?_⟩
  have : R = A + P - X := by rw [← sum, add_tsub_cancel_left]
  rw [this, tsub_add_eq_add_tsub le]

variable {askSym}

/-- **Every clean bag is related to itself.** -/
theorem related_refl (d : Defined) {A : Multiset Expr} (clean : Clean askSym d.name A) : Related askSym d A A :=
  ⟨clean, 0, 0, by simp, fun _ inside => absurd inside (Multiset.notMem_zero _),
    fun _ inside => absurd inside (Multiset.notMem_zero _)⟩

/-- **Related bags hold the same rows other than pending and answer rows.** -/
theorem related_rows {d : Defined} {A C : Multiset Expr} (related : Related askSym d A C) {e : Expr}
    (outside : ¬ Private askSym d.name e) : Multiset.count e C = Multiset.count e A := by
  obtain ⟨-, pending, answers, rfl, asks, rows'⟩ := related
  have notPending : Multiset.count e pending = 0 :=
    Multiset.count_eq_zero.mpr fun inside => outside (.inl (asks e inside))
  have notAnswer : Multiset.count e answers = 0 := Multiset.count_eq_zero.mpr fun inside => by
    obtain ⟨args, -, same⟩ := rows' e inside
    exact outside (.inr ⟨args, _, same⟩)
  rw [Multiset.count_add, Multiset.count_add, notPending, notAnswer, add_zero, add_zero]

variable {ρ : RuleWithCondition ℕ Tm} {c : Condition ℕ Tm} {d : Defined}

/-- **A request keeps the relation**: it adds a pending row. -/
theorem related_request (isName : c.name = d.name) {A C C' : Multiset Expr} (related : Related askSym d A C)
    (fires : Rewrites [request askSym ρ c] C C') : Related askSym d A C' := by
  obtain ⟨clean, pending, answers, rfl, asks, answerRows⟩ := related
  obtain ⟨r, member, θ, rest, split, -, -, rfl⟩ := fires
  obtain rfl := List.mem_singleton.mp member
  have restEq : rest = A + pending + answers := by simpa [request] using split
  refine ⟨clean, {inst θ (askRow askSym c.name c.arguments)} + pending, answers, ?_, fun e inside => ?_,
    answerRows⟩
  · rw [restEq]
    simp only [request, List.map_cons, List.map_nil, Multiset.coe_singleton]
    abel
  · rcases Multiset.mem_add.mp inside with new | old
    · rw [Multiset.mem_singleton.mp new]
      exact ⟨_, by rw [inst_askRow, isName]⟩
    · exact asks e old

/-- **An equation keeps the relation**: it turns a pending row into an answer row of the graph. -/
theorem related_equation (apart : d.name ≠ askSym) {A C C' : Multiset Expr} (related : Related askSym d A C)
    (fires : Rewrites [equationRule askSym d] C C') : Related askSym d A C' := by
  obtain ⟨clean, pending, answers, rfl, asks, answerRows⟩ := related
  obtain ⟨r, member, θ, rest, split, -, -, rfl⟩ := fires
  obtain rfl := List.mem_singleton.mp member
  set ask := groundAsk askSym d.name (d.params.map θ) with askIs
  have takeEq : ((equationRule askSym d).body.take.map (inst θ) : Multiset Expr) = {ask} := by
    simp only [equationRule, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [inst_askRow, List.map_map]
    rfl
  rw [takeEq] at split
  have inC : ask ∈ A + pending + answers := by
    rw [← split]
    exact Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))
  have isAsk : IsAsk askSym d.name ask := ⟨_, rfl⟩
  have inPending : ask ∈ pending := by
    rcases Multiset.mem_add.mp inC with inAP | inAnswers
    · rcases Multiset.mem_add.mp inAP with inA | inP
      · exact absurd (.inl isAsk) (clean ask inA)
      · exact inP
    · obtain ⟨args, -, same⟩ := answerRows ask inAnswers
      exact absurd ⟨args, _, same⟩ (ask_not_table askSym apart isAsk)
  obtain ⟨pending', rfl⟩ := Multiset.exists_cons_of_mem inPending
  have restEq : rest = A + pending' + answers := by
    rw [← Multiset.singleton_add] at split
    have : {ask} + rest = {ask} + (A + pending' + answers) := by rw [split]; abel
    exact add_left_cancel this
  refine ⟨clean, pending', {inst θ (rows.row d.name (d.params.map .var) d.body)} + answers, ?_,
    fun e inside => asks e (Multiset.mem_cons_of_mem inside), fun e inside => ?_⟩
  · simp only [equationRule, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [restEq]
    abel
  · rcases Multiset.mem_add.mp inside with new | old
    · rw [Multiset.mem_singleton.mp new]
      refine ⟨d.params.map θ, List.length_map _, ?_⟩
      rw [inst_row, List.map_map, d.inst_body θ]
      rfl
    · exact answerRows e old

/-- **A resume is an atomic evaluation**, and the relation continues. -/
theorem related_resume (only : ρ.conditions = [c]) (isName : c.name = d.name)
    (lengths : c.arguments.length = d.params.length) (apart : d.name ≠ askSym)
    (unseen : SeesNoPending askSym d.name ρ) {A C C' : Multiset Expr} (related : Related askSym d A C)
    (fires : Rewrites [ρ.tableRule rows] C C') :
    ∃ A', EvalStep d.interp ρ A A' ∧ Related askSym d A' C' := by
  obtain ⟨clean, pending, answers, rfl, asks, answerRows⟩ := related
  obtain ⟨r, member, θ, rest, split, reads, equations, rfl⟩ := fires
  obtain rfl := List.mem_singleton.mp member
  have privateRows : ∀ p ∈ pending + answers, Private askSym d.name p := by
    intro p inside
    rcases Multiset.mem_add.mp inside with inP | inAnswers
    · exact .inl (asks p inP)
    · obtain ⟨args, -, same⟩ := answerRows p inAnswers
      exact .inr ⟨args, _, same⟩
  have takesPublic : ∀ x ∈ (ρ.rule.body.take.map (inst θ) : Multiset Expr), ¬ Private askSym d.name x := by
    intro x inside
    obtain ⟨q, inTake, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp inside)
    exact unseen θ q (List.mem_append_left _ (List.mem_append_left _ inTake))
  rw [add_assoc] at split
  obtain ⟨rest', aEq, restEq⟩ := split_clean askSym split takesPublic privateRows
  have restClean : Clean askSym d.name rest' := fun e inside => clean e (by
    rw [aEq]
    exact Multiset.mem_add.mpr (.inr inside))
  have readsIn : ∀ q ∈ ρ.rule.body.read, inst θ q ∈ rest' := by
    intro q inside
    have inRest := reads q (List.mem_append_left _ inside)
    rw [restEq] at inRest
    rcases Multiset.mem_add.mp inRest with inRest' | inPrivate
    · exact inRest'
    · exact absurd (privateRows _ inPrivate)
        (unseen θ q (List.mem_append_left _ (List.mem_append_right _ inside)))
  have callIn := reads (callRow rows c) (List.mem_append_right _ (by simp [RuleWithCondition.calls, only]))
  rw [restEq, show inst θ (callRow rows c) = groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) from
    inst_row θ c.name c.arguments c.value] at callIn
  have callTable : IsTable d.name (groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value)) :=
    ⟨_, _, by rw [isName]⟩
  have answered : ∃ args : List Expr, args.length = d.params.length ∧
      groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) =
        groundRow d.name args (inst (bindParams d.params args) d.body) := by
    rcases Multiset.mem_add.mp callIn with inRest' | inPrivate
    · exact absurd (.inr callTable) (restClean _ inRest')
    · rcases Multiset.mem_add.mp inPrivate with inP | inAnswers
      · exact absurd callTable (ask_not_table askSym apart (asks _ inP))
      · exact answerRows _ inAnswers
  obtain ⟨args, argsLength, same⟩ := answered
  rw [isName] at same
  obtain ⟨-, both⟩ := groundSpine_inj (by simp [argsLength, lengths]) same
  obtain ⟨argsEq, valueEq⟩ := List.append_inj both (by simp [argsLength, lengths])
  have valueEq' : inst θ c.value = inst (bindParams d.params args) d.body := (List.cons.inj valueEq).1
  refine ⟨(ρ.rule.body.produce.map (inst θ) : Multiset Expr) + rest', ⟨θ, rest', aEq.symm, readsIn,
    equations, fun c' inside => ?_, rfl⟩, ⟨fun e inside => ?_, pending, answers, ?_, asks, answerRows⟩⟩
  · rw [only, List.mem_singleton] at inside
    subst inside
    rw [isName, argsEq, d.interp_eq argsLength, valueEq']
  · rcases Multiset.mem_add.mp inside with made | old
    · obtain ⟨q, inProduce, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp made)
      exact unseen θ q (List.mem_append_right _ inProduce)
    · exact restClean e old
  · show (ρ.tableRule rows).body.produce.map (inst θ) + rest = _
    rw [restEq]
    simp only [RuleWithCondition.tableRule_produce]
    abel

/-- **An atomic evaluation is a request, an equation and a resume.** -/
theorem related_atomic (only : ρ.conditions = [c]) (isName : c.name = d.name)
    (lengths : c.arguments.length = d.params.length) (unseen : SeesNoPending askSym d.name ρ)
    {A A' C : Multiset Expr} (related : Related askSym d A C) (evaluates : EvalStep d.interp ρ A A') :
    ∃ C₁ C₂ C', Rewrites [request askSym ρ c] C C₁ ∧ Rewrites [equationRule askSym d] C₁ C₂ ∧
      Rewrites [ρ.tableRule rows] C₂ C' ∧ Related askSym d A' C' := by
  obtain ⟨clean, pending, answers, rfl, asks, answerRows⟩ := related
  obtain ⟨θ, rest, rfl, reads, equations, conditions, rfl⟩ := evaluates
  have value := conditions c (by rw [only]; exact List.mem_singleton_self _)
  rw [isName, d.interp_eq (by rw [List.length_map, lengths])] at value
  have valueEq : inst θ c.value = inst (bindParams d.params (c.arguments.map (inst θ))) d.body :=
    (Option.some.inj value).symm
  have argsLength : (c.arguments.map (inst θ)).length = d.params.length := by rw [List.length_map, lengths]
  have paramsMap := map_bindParams d.params (c.arguments.map (inst θ)) d.distinct argsLength.symm
  refine ⟨{groundAsk askSym d.name (c.arguments.map (inst θ))} +
      ((ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest + pending + answers),
    {groundRow d.name (c.arguments.map (inst θ)) (inst (bindParams d.params (c.arguments.map (inst θ))) d.body)} +
      ((ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest + pending + answers), _,
    ⟨_, List.mem_singleton_self _, θ, (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest + pending + answers,
      by simp [request], fun q inside => ?_, fun e inside => ?_, ?_⟩,
    ⟨_, List.mem_singleton_self _, bindParams d.params (c.arguments.map (inst θ)),
      (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest + pending + answers, ?_, fun q inside => ?_,
      fun e inside => ?_, ?_⟩,
    ⟨_, List.mem_singleton_self _, θ, rest + pending + ({groundRow d.name (c.arguments.map (inst θ))
      (inst (bindParams d.params (c.arguments.map (inst θ))) d.body)} + answers), ?_, fun q inside => ?_,
      fun e inside => ?_, rfl⟩, ?_⟩
  · -- the request reads the rule's rows
    have inA : ∀ x ∈ (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest,
        x ∈ (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest + pending + answers :=
      fun x inside => Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl inside)))
    rcases List.mem_append.mp inside with inTake | inRead
    · exact inA _ (Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_map_of_mem inTake))))
    · exact inA _ (Multiset.mem_add.mpr (.inr (reads q inRead)))
  · simp [equationsOf, request] at inside
  · simp only [request, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [inst_askRow, isName]
  · -- the equation takes the pending row
    simp only [equationRule, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [inst_askRow, List.map_map]
    show {groundAsk askSym d.name (d.params.map (bindParams d.params (c.arguments.map (inst θ))))} + _ = _
    rw [paramsMap]
  · simp [equationRule] at inside
  · simp [equationsOf, equationRule] at inside
  · simp only [equationRule, List.map_cons, List.map_nil, Multiset.coe_singleton]
    rw [inst_row, List.map_map]
    show _ = ({groundRow d.name (d.params.map (bindParams d.params (c.arguments.map (inst θ)))) _} :
      Multiset Expr) + _
    rw [paramsMap]
  · -- the resume takes the rule's rows beside the answer
    show ((ρ.tableRule rows).body.take.map (inst θ) : Multiset Expr) + _ = _
    simp only [RuleWithCondition.tableRule_take]
    abel
  · -- the resume reads the rule's rows and the answer
    simp only [RuleWithCondition.tableRule_read, RuleWithCondition.calls, only, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton] at inside
    rcases inside with inRead | rfl
    · exact Multiset.mem_add.mpr (.inl (Multiset.mem_add.mpr (.inl (reads q inRead))))
    · rw [show inst θ (callRow rows c) = groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) from
        inst_row θ c.name c.arguments c.value, isName, valueEq]
      exact Multiset.mem_add.mpr (.inr (Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))))
  · exact equations e (by simpa [equationsOf] using inside)
  · refine ⟨fun e inside => ?_, pending, {groundRow d.name (c.arguments.map (inst θ))
      (inst (bindParams d.params (c.arguments.map (inst θ))) d.body)} + answers, ?_, asks, fun e inside => ?_⟩
    · rcases Multiset.mem_add.mp inside with made | old
      · obtain ⟨q, inProduce, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp made)
        exact unseen θ q (List.mem_append_right _ inProduce)
      · exact clean e (Multiset.mem_add.mpr (.inr old))
    · show ((ρ.tableRule rows).body.produce.map (inst θ) : Multiset Expr) + _ = _
      simp only [RuleWithCondition.tableRule_produce]
      abel
    · rcases Multiset.mem_add.mp inside with new | old
      · rw [Multiset.mem_singleton.mp new]
        exact ⟨c.arguments.map (inst θ), argsLength, rfl⟩
      · exact answerRows e old

end Call

#print axioms callProgram_fragment
#print axioms callCorrespondence
#print axioms map_bindParams
#print axioms split_clean
#print axioms related_refl
#print axioms related_rows
#print axioms related_request
#print axioms related_equation
#print axioms related_resume
#print axioms related_atomic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
