import Mettapedia.Languages.Dataflow.Core

/-!
# Operational semantics and adequacy for the dataflow language

The data-driven half of the language, and its agreement with the
demand-driven denotation of `Core`.

* `Denotes spec p c v` — the mathematical denotation: cell `c` evaluates to
  `v` under *some* dependency-depth budget.  Because `denoteCell` descends
  through operands and the budget is finite, a cell on a dependency cycle
  denotes nothing; acyclicity is therefore not a separate predicate but a
  consequence of denoting at all.
* `Step` — Kahn-style firing of any *ready* pending instruction, in any
  order.

The results are: firing strictly decreases the pending count, the
reachability invariant is preserved, independent firings commute, a
well-formed program never deadlocks, and every terminal state assigns the
returned cell exactly its denotation — under every schedule.
-/

namespace Mettapedia.Languages.Dataflow

variable {Op Value : Type}

/-! ## Fuel monotonicity

`denoteCell` and `denoteOperands` are mutually recursive, so their shared
facts are proved as one bundled statement indexed by fuel: the cell claim at
`fuel + 1` consumes the operand claim at `fuel`, and the operand claim at
`fuel` consumes the cell claim at the *same* `fuel`, which the bundle makes
available. -/

private theorem denote_mono_bundle (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) : ∀ fuel : Nat,
    (∀ (c : CellId) (v : Value), denoteCell spec p fuel c = some v →
        denoteCell spec p (fuel + 1) c = some v) ∧
    (∀ (cs : List CellId) (vs : List Value),
        denoteOperands spec p fuel cs = some vs →
        denoteOperands spec p (fuel + 1) cs = some vs) := by
  have operandPart : ∀ (fuel : Nat),
      (∀ (c : CellId) (v : Value), denoteCell spec p fuel c = some v →
        denoteCell spec p (fuel + 1) c = some v) →
      ∀ (cs : List CellId) (vs : List Value),
        denoteOperands spec p fuel cs = some vs →
        denoteOperands spec p (fuel + 1) cs = some vs := by
    intro fuel cellPart cs
    induction cs with
    | nil =>
        intro vs evaluated
        rw [denoteOperands_nil] at evaluated ⊢
        exact evaluated
    | cons c cs inductionHypothesis =>
        intro vs evaluated
        cases headValue : denoteCell spec p fuel c with
        | none => simp [denoteOperands_cons, headValue] at evaluated
        | some v =>
            cases tailValues : denoteOperands spec p fuel cs with
            | none =>
                simp [denoteOperands_cons, headValue, tailValues] at evaluated
            | some tail =>
                simp only [denoteOperands_cons, headValue, tailValues]
                  at evaluated
                simp only [denoteOperands_cons, cellPart c v headValue,
                  inductionHypothesis tail tailValues]
                exact evaluated
  intro fuel
  induction fuel with
  | zero =>
      have cellPart : ∀ (c : CellId) (v : Value),
          denoteCell spec p 0 c = some v →
          denoteCell spec p 1 c = some v := by
        intro c v evaluated
        rw [denoteCell_zero] at evaluated
        rw [denoteCell_succ, evaluated]
      exact ⟨cellPart, operandPart 0 cellPart⟩
  | succ fuel inductionHypothesis =>
      have cellPart : ∀ (c : CellId) (v : Value),
          denoteCell spec p (fuel + 1) c = some v →
          denoteCell spec p (fuel + 2) c = some v := by
        intro c v evaluated
        cases isInput : p.inputValue? c with
        | some inputValue =>
            simp only [denoteCell_succ, isInput] at evaluated ⊢
            exact evaluated
        | none =>
            cases writer : p.writerOf? c with
            | none => simp [denoteCell_succ, isInput, writer] at evaluated
            | some instruction =>
                cases instruction with
                | const d constValue =>
                    simp only [denoteCell_succ, isInput, writer] at evaluated ⊢
                    exact evaluated
                | apply d op operands =>
                    by_cases arity : operands.length = spec.arity op
                    · cases operandValues :
                          denoteOperands spec p fuel operands with
                      | none =>
                          simp [denoteCell_succ, isInput, writer, arity,
                            operandValues] at evaluated
                      | some values =>
                          simp only [denoteCell_succ, isInput, writer,
                            if_pos arity, operandValues] at evaluated
                          simp only [denoteCell_succ, isInput, writer,
                            if_pos arity,
                            inductionHypothesis.2 operands values operandValues]
                          exact evaluated
                    · simp [denoteCell_succ, isInput, writer, arity]
                        at evaluated
      exact ⟨cellPart, operandPart (fuel + 1) cellPart⟩

theorem denoteCell_mono {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {fuel : Nat} {c : CellId} {v : Value}
    (evaluated : denoteCell spec p fuel c = some v) :
    denoteCell spec p (fuel + 1) c = some v :=
  (denote_mono_bundle spec p fuel).1 c v evaluated

theorem denoteOperands_mono {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {fuel : Nat} {cs : List CellId} {vs : List Value}
    (evaluated : denoteOperands spec p fuel cs = some vs) :
    denoteOperands spec p (fuel + 1) cs = some vs :=
  (denote_mono_bundle spec p fuel).2 cs vs evaluated

theorem denoteCell_mono_le {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {fuel fuel' : Nat} (le : fuel ≤ fuel')
    {c : CellId} {v : Value} (evaluated : denoteCell spec p fuel c = some v) :
    denoteCell spec p fuel' c = some v := by
  induction le with
  | refl => exact evaluated
  | step _ inductionHypothesis => exact denoteCell_mono inductionHypothesis

theorem denoteOperands_mono_le {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {fuel fuel' : Nat} (le : fuel ≤ fuel')
    {cs : List CellId} {vs : List Value}
    (evaluated : denoteOperands spec p fuel cs = some vs) :
    denoteOperands spec p fuel' cs = some vs := by
  induction le with
  | refl => exact evaluated
  | step _ inductionHypothesis => exact denoteOperands_mono inductionHypothesis

/-! ## The mathematical denotation -/

/-- Cell `c` denotes value `v`: demand-driven evaluation succeeds at some
finite dependency depth.  A cell on a dependency cycle denotes nothing. -/
def Denotes (spec : PureOperatorSpec Op Value) (p : Program Op Value)
    (c : CellId) (v : Value) : Prop :=
  ∃ fuel, denoteCell spec p fuel c = some v

/-- Pointwise denotation of an operand vector. -/
def DenotesList (spec : PureOperatorSpec Op Value) (p : Program Op Value)
    (cs : List CellId) (vs : List Value) : Prop :=
  ∃ fuel, denoteOperands spec p fuel cs = some vs

/-- The denotation is a partial function: no cell denotes two values. -/
theorem Denotes.functional {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {c : CellId} {v w : Value}
    (first : Denotes spec p c v) (second : Denotes spec p c w) : v = w := by
  obtain ⟨fuelFirst, evaluatedFirst⟩ := first
  obtain ⟨fuelSecond, evaluatedSecond⟩ := second
  have atFirst := denoteCell_mono_le (Nat.le_max_left fuelFirst fuelSecond)
    evaluatedFirst
  have atSecond := denoteCell_mono_le (Nat.le_max_right fuelFirst fuelSecond)
    evaluatedSecond
  rw [atFirst] at atSecond
  exact Option.some.inj atSecond

/-! ### Introduction and inversion

These make `Denotes` usable as if it were the inductive definition, while
keeping determinism free. -/

theorem Denotes.input {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {c : CellId} {v : Value}
    (isInput : p.inputValue? c = some v) : Denotes spec p c v :=
  ⟨0, by rw [denoteCell_zero]; exact isInput⟩

theorem Denotes.const {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {c : CellId} {v : Value}
    (notInput : p.inputValue? c = none)
    (writer : p.writerOf? c = some (.const c v)) : Denotes spec p c v :=
  ⟨1, by simp [denoteCell_succ, notInput, writer]⟩

theorem Denotes.apply {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {c : CellId} {op : Op} {operands : List CellId}
    {values : List Value} (notInput : p.inputValue? c = none)
    (writer : p.writerOf? c = some (.apply c op operands))
    (arity : operands.length = spec.arity op)
    (children : DenotesList spec p operands values) :
    Denotes spec p c (spec.apply op values) := by
  obtain ⟨fuel, evaluated⟩ := children
  exact ⟨fuel + 1, by
    simp only [denoteCell_succ, notInput, writer, if_pos arity, evaluated]⟩

@[simp] theorem DenotesList.nil {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} : DenotesList spec p [] [] :=
  ⟨0, denoteOperands_nil spec p 0⟩

theorem DenotesList.cons {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {c : CellId} {v : Value} {cs : List CellId}
    {vs : List Value} (head : Denotes spec p c v)
    (tail : DenotesList spec p cs vs) :
    DenotesList spec p (c :: cs) (v :: vs) := by
  obtain ⟨headFuel, headEvaluated⟩ := head
  obtain ⟨tailFuel, tailEvaluated⟩ := tail
  refine ⟨max headFuel tailFuel, ?_⟩
  rw [denoteOperands,
    denoteCell_mono_le (Nat.le_max_left headFuel tailFuel) headEvaluated,
    denoteOperands_mono_le (Nat.le_max_right headFuel tailFuel) tailEvaluated]

/-- Every operand of a denoting vector denotes. -/
theorem DenotesList.mem_denotes {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} :
    ∀ {cs : List CellId} {vs : List Value}, DenotesList spec p cs vs →
      ∀ c ∈ cs, ∃ v, Denotes spec p c v := by
  intro cs
  induction cs with
  | nil => intro vs _ d member; cases member
  | cons c cs inductionHypothesis =>
      rintro vs ⟨fuel, evaluated⟩ d member
      simp only [denoteOperands] at evaluated
      cases headValue : denoteCell spec p fuel c with
      | none => rw [headValue] at evaluated; cases evaluated
      | some v =>
          rw [headValue] at evaluated
          cases tailValues : denoteOperands spec p fuel cs with
          | none => rw [tailValues] at evaluated; cases evaluated
          | some tail =>
              rw [tailValues] at evaluated
              rcases List.mem_cons.mp member with rfl | tailMember
              · exact ⟨v, fuel, headValue⟩
              · exact inductionHypothesis ⟨fuel, tailValues⟩ d tailMember

/-- Denotation of an operand vector from pointwise denotations. -/
theorem DenotesList.of_forall {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} :
    ∀ {cs : List CellId} (choice : ∀ c ∈ cs, Value),
      (∀ (c : CellId) (member : c ∈ cs), Denotes spec p c (choice c member)) →
      ∃ vs, DenotesList spec p cs vs := by
  intro cs
  induction cs with
  | nil => intro _ _; exact ⟨[], DenotesList.nil⟩
  | cons c cs inductionHypothesis =>
      intro choice denotes
      obtain ⟨vs, tail⟩ := inductionHypothesis
        (fun d member => choice d (List.mem_cons_of_mem _ member))
        (fun d member => denotes d (List.mem_cons_of_mem _ member))
      exact ⟨choice c (List.mem_cons_self ..) :: vs,
        DenotesList.cons (denotes c (List.mem_cons_self ..)) tail⟩

end Mettapedia.Languages.Dataflow
