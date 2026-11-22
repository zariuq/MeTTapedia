import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Monotone
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PositiveTell

/-!
# A necessary condition for switching, on the step of rule instances: an absence or count check, or a shared unknown

Over first-order terms, with occurrences labelled by their rows, on the step whose programs are sets of
rule instances (`stepCalculus`, over `AnnotatedRuns`). A rule instance carries its variables fixed:
the step has no fresh openings, so a firing's information mentions the instance's own variables as
they stand.

* **Coincidence** (`applyTerm_congr`): two substitutions that agree on the variables of a term send it
  to the same term. So two solvable knowledges that mention no common variable are solvable together
  (`models_of_apart`).
* **Monotonicity for runs that share no unknown with the neighbour** (`succeeds_union_of_apart`): for a
  program whose rules have only equality checks and `any` queries and every success predicate on rows, if `C` reaches
  success by firings whose information mentions no variable that the knowledge of a composable `D`
  mentions (`ApartStep`), then `C` beside `D` reaches success. It is `Monotone.succeeds_union_of_joint`
  with the joint solutions given by coincidence. This is the content of the line below.
* **The line, a necessary condition** (`switched_off_has_guard_or_shared`,
  `switchable_has_guard_or_shared`): when a composable neighbour switches reachable success off, some
  rule of the program has an absence or a count check, or every run that reaches success alone has a
  firing whose information mentions a variable the neighbour's knowledge mentions. A firing's predicate
  queries never block reachability on this step (`Monotone.dropQueries_valid`), so they are no third
  source. What it counts as a shared variable includes a rule instance's own variable: a neighbour
  that constrains only that variable, which the system mentions nowhere, switches the program off and
  falls on the shared side (`captor_switches`, `captor_on_shared_side`). It is not a characterization:
  a neighbour that shares the system's unknown and agrees with the tell leaves success reachable
  (`friend_shares_and_succeeds`). Where the system's own knowledge already mentions a variable of the
  neighbour's, no step is apart (`no_apartStep_of_shared`, `apart_run_trivial`), and the second
  disjunct says only that the system does not show success yet.

On the step of a program with fresh openings (`RuleSyntax.step`), capture cannot happen; the line is
stated there in `FreshOpenings`.

Controls, one for each source of switching: an absence check (`source_switchable`) and a count check
(`Monotone.counted_switchable`), both over ground terms, where no unknown exists; and a tell on a
shared unknown, with no check (`PositiveTell.tellSource_switchable`), where the only run to success has a
firing whose information mentions the neighbour's unknown (`tell_shares_with_neighbour`). Positive
control: beside a neighbour whose knowledge constrains another unknown, the same request succeeds,
by the theorem (`tell_beside_other`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.SharedUnknown

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
  (unionOf)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

section General

variable {sig : LPSignature}

/-- A variable occurs in a term. -/
inductive Occurs (v : sig.vars) : Term sig → Prop
  | var : Occurs v (.var v)
  | app {f : sig.functionSymbols} {ts : Fin (sig.functionArity f) → Term sig}
      (i : Fin (sig.functionArity f)) : Occurs v (ts i) → Occurs v (.app f ts)

/-- **Coincidence**: two substitutions that agree on the variables of a term send it to the same
term. -/
theorem applyTerm_congr {σ τ : Subst sig} (t : Term sig) (agree : ∀ v, Occurs v t → σ v = τ v) :
    σ.applyTerm t = τ.applyTerm t := by
  induction t with
  | var v => exact agree v .var
  | const c => rfl
  | app f ts ih =>
      simp only [Subst.applyTerm]
      congr 1
      funext i
      exact ih i fun v occurs => agree v (.app i occurs)

/-- A knowledge mentions a variable: it occurs in a side of one of its equations. -/
def Mentions (E : EquationStore (Term sig)) (v : sig.vars) : Prop :=
  ∃ e ∈ E, Occurs v e.1 ∨ Occurs v e.2

/-- **Two solvable knowledges that mention no common variable are solvable together.** -/
theorem models_of_apart {E K : EquationStore (Term sig)} {σ τ : Subst sig}
    (solvedE : (FirstOrder.action sig).Models σ E) (solvedK : (FirstOrder.action sig).Models τ K)
    (apart : ∀ v, Mentions E v → ¬ Mentions K v) :
    ∃ ρ, (FirstOrder.action sig).Models ρ E ∧ (FirstOrder.action sig).Models ρ K := by
  classical
  let ρ : Subst sig := fun v => if Mentions E v then σ v else τ v
  refine ⟨ρ, fun e member => ?_, fun e member => ?_⟩
  · have left : ρ.applyTerm e.1 = σ.applyTerm e.1 :=
      applyTerm_congr e.1 fun v occurs => if_pos ⟨e, member, Or.inl occurs⟩
    have right : ρ.applyTerm e.2 = σ.applyTerm e.2 :=
      applyTerm_congr e.2 fun v occurs => if_pos ⟨e, member, Or.inr occurs⟩
    show ρ.applyTerm e.1 = ρ.applyTerm e.2
    rw [left, right]
    exact solvedE e member
  · have outside : ∀ v, Mentions K v → ρ v = τ v := fun v mentioned =>
      if_neg fun inE => apart v inE mentioned
    have left : ρ.applyTerm e.1 = τ.applyTerm e.1 :=
      applyTerm_congr e.1 fun v occurs => outside v ⟨e, member, Or.inl occurs⟩
    have right : ρ.applyTerm e.2 = τ.applyTerm e.2 :=
      applyTerm_congr e.2 fun v occurs => outside v ⟨e, member, Or.inr occurs⟩
    show ρ.applyTerm e.1 = ρ.applyTerm e.2
    rw [left, right]
    exact solvedK e member

variable [DecidableEq (Term sig)]

/-- **A step whose information shares no unknown with the knowledge `K`**: a firing of the program,
admitted, whose information mentions no variable that `K` mentions. -/
def ApartStep (P : RuleInstance (Term sig) → Prop) (K : EquationStore (Term sig))
    (C C' : Configuration (Term sig) (Term sig × ℕ)) : Prop :=
  ∃ f : AnnotatedRuns.Firing (Term sig) (Subst sig) (Term sig × ℕ), P f.rule ∧
    f.Valid (FirstOrder.action sig) Prod.fst C ∧ f.result Prod.fst C = C' ∧
    ∀ v, Mentions (f.selection.problem Prod.fst f.rule C) v → ¬ Mentions K v

variable {P : RuleInstance (Term sig) → Prop} {row : Term sig → Prop}

/-- A step sharing no unknown with a solvable knowledge is solvable together with it. -/
theorem joint_of_apart {K : EquationStore (Term sig)} (solvable : (FirstOrder.action sig).Consistent K)
    {C C' : Configuration (Term sig) (Term sig × ℕ)} (step : ApartStep P K C C') :
    Monotone.JointStep (FirstOrder.action sig) P K C C' := by
  obtain ⟨f, inProgram, admitted, rfl, apart⟩ := step
  obtain ⟨σ, solvedC⟩ := admitted.firing.consistent
  obtain ⟨τ, solvedK⟩ := solvable
  obtain ⟨ρ, solvedC', solvedK'⟩ := models_of_apart solvedC solvedK apart
  exact ⟨f, inProgram, admitted, rfl, ρ, solvedC', solvedK'⟩

theorem joint_run_of_apart {K : EquationStore (Term sig)} (solvable : (FirstOrder.action sig).Consistent K)
    {C C' : Configuration (Term sig) (Term sig × ℕ)} (run : Relation.ReflTransGen (ApartStep P K) C C') :
    Relation.ReflTransGen (Monotone.JointStep (FirstOrder.action sig) P K) C C' := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (joint_of_apart solvable step)

/-- **Monotonicity for runs that share no unknown with the neighbour.** -/
theorem succeeds_union_of_apart (monotone : ∀ r, P r → Monotone.MonotoneChecks r)
    {C D C' : Configuration (Term sig) (Term sig × ℕ)} (composable : Composable (FirstOrder.action sig) C D)
    (run : Relation.ReflTransGen (ApartStep P D.equations) C C')
    (shows : Shows (Prod.fst : Term sig × ℕ → Term sig) row C') :
    (stepCalculus (FirstOrder.action sig) (Prod.fst : Term sig × ℕ → Term sig) P row).Succeeds
      (unionOf C D) := by
  have solvable : (FirstOrder.action sig).Consistent D.equations := by
    obtain ⟨σ, solved⟩ := composable.2
    exact ⟨σ, fun e member => solved e (List.mem_append_right _ member)⟩
  exact Monotone.succeeds_union_of_joint monotone composable rfl (joint_run_of_apart solvable run) shows

omit [DecidableEq (Term sig)] in
/-- Every check is an equality, an `any` query, an absence or a count: a rule has monotone checks, or
an absence or a count check. -/
theorem monotoneChecks_or_guard (r : RuleInstance (Term sig)) :
    Monotone.MonotoneChecks r ∨ ∃ c ∈ r.checks, (∃ p, c = Check.predicate .none p) ∨ ∃ p n, c = Check.count p n := by
  by_cases guard : ∃ c ∈ r.checks, (∃ p, c = Check.predicate .none p) ∨ ∃ p n, c = Check.count p n
  · exact Or.inr guard
  · refine Or.inl fun c member => ?_
    cases c with
    | equal l r' => exact Or.inl ⟨l, r', rfl⟩
    | predicate quantifier p =>
        cases quantifier with
        | any => exact Or.inr ⟨p, rfl⟩
        | none => exact absurd ⟨_, member, Or.inl ⟨p, rfl⟩⟩ guard
    | count p n => exact absurd ⟨_, member, Or.inr ⟨p, n, rfl⟩⟩ guard

/-- **The necessary condition, for one pair.** When `D`, composable with `C`, switches reachable success
off, some rule of the program has an absence or a count check, or no run that reaches success from
`C` consists of firings sharing no unknown with `D`'s knowledge. A shared unknown here may be a rule
instance's own variable (`captor_on_shared_side`); the converse fails (`friend_shares_and_succeeds`). -/
theorem switched_off_has_guard_or_shared {C D : Configuration (Term sig) (Term sig × ℕ)}
    (composable : Composable (FirstOrder.action sig) C D)
    (blocked : ¬ (stepCalculus (FirstOrder.action sig) (Prod.fst : Term sig × ℕ → Term sig) P row).Succeeds
      (unionOf C D)) :
    (∃ r, P r ∧ ∃ c ∈ r.checks, (∃ p, c = Check.predicate .none p) ∨ ∃ p n, c = Check.count p n) ∨
      ∀ C', Relation.ReflTransGen (ApartStep P D.equations) C C' →
        ¬ Shows (Prod.fst : Term sig × ℕ → Term sig) row C' := by
  by_cases guard : ∃ r, P r ∧ ∃ c ∈ r.checks, (∃ p, c = Check.predicate .none p) ∨ ∃ p n, c = Check.count p n
  · exact Or.inl guard
  · refine Or.inr fun C' run shows => blocked (succeeds_union_of_apart (fun r inProgram => ?_)
      composable run shows)
    rcases monotoneChecks_or_guard r with monotone | hasGuard
    · exact monotone
    · exact absurd ⟨r, inProgram, hasGuard⟩ guard

/-- **The necessary condition**: a switchable program has a rule with an absence or a count check, or a
switching pair every run to success of whose first part has a firing sharing an unknown with the
knowledge of the second (an unknown that may be a rule instance's own variable). -/
theorem switchable_has_guard_or_shared
    (switchable : (stepCalculus (FirstOrder.action sig) (Prod.fst : Term sig × ℕ → Term sig) P row).Switchable) :
    (∃ r, P r ∧ ∃ c ∈ r.checks, (∃ p, c = Check.predicate .none p) ∨ ∃ p n, c = Check.count p n) ∨
      ∃ C D, Composable (FirstOrder.action sig) C D ∧
        (stepCalculus (FirstOrder.action sig) (Prod.fst : Term sig × ℕ → Term sig) P row).Succeeds C ∧
        ∀ C', Relation.ReflTransGen (ApartStep P D.equations) C C' →
          ¬ Shows (Prod.fst : Term sig × ℕ → Term sig) row C' := by
  obtain ⟨C, D, composable, succeeds, blocked⟩ := switchable
  rcases switched_off_has_guard_or_shared composable blocked with guard | shared
  · exact Or.inl guard
  · exact Or.inr ⟨C, D, composable, succeeds, shared⟩

end General

/-! ## Controls for the shared unknown -/

section Controls

open PositiveTell (atoms x y c tellRule tellRule_checks tellSource request neighbour)

/-- **The tell's only run to success shares the neighbour's unknown**: its information mentions `x`,
which the neighbour's knowledge mentions. -/
theorem tell_shares_with_neighbour :
    Mentions (PositiveTell.fireAt.selection.problem Prod.fst PositiveTell.fireAt.rule request) 0 ∧
      Mentions neighbour.equations 0 :=
  ⟨⟨(y, x), by rw [PositiveTell.fireAt_problem]; exact List.mem_cons_self .., Or.inr .var⟩,
    ⟨(x, c 6), List.mem_singleton_self _, Or.inl .var⟩⟩

/-- The store with no rows whose knowledge says `z = 6`, for an unknown `z` the request does not
mention. -/
def otherNeighbour : Configuration (Term atoms) PositiveTell.Occ := ⟨[(.var 2, c 6)], ∅⟩

/-- The request and the other neighbour are composable. -/
theorem request_other_composable : tellSource.composable request otherNeighbour := by
  refine ⟨Finset.disjoint_empty_right _, fun _ => c 6, fun e inside => ?_⟩
  simp only [request, otherNeighbour, List.nil_append, List.mem_singleton] at inside
  subst inside
  rfl

/-- `x` and `y` are not `z`. -/
theorem fireAt_apart :
    ∀ v, Mentions (PositiveTell.fireAt.selection.problem Prod.fst PositiveTell.fireAt.rule request) v →
      ¬ Mentions otherNeighbour.equations v := by
  rintro v ⟨e, inside, occurs⟩ ⟨e', inside', occurs'⟩
  rw [PositiveTell.fireAt_problem] at inside
  simp only [otherNeighbour, List.mem_singleton] at inside'
  subst inside'
  have isTwo : v = 2 := by
    rcases occurs' with occurs' | occurs'
    · cases occurs'
      rfl
    · cases occurs'
  subst isTwo
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl <;> rcases occurs with occurs | occurs <;> cases occurs

/-- **Positive control, by the theorem**: beside a neighbour whose knowledge constrains another
unknown, the request succeeds. -/
theorem tell_beside_other : tellSource.Succeeds (unionOf request otherNeighbour) :=
  succeeds_union_of_apart (fun r isTell c member => by
      rw [isTell, tellRule_checks] at member
      exact absurd member List.not_mem_nil)
    request_other_composable
    (.single ⟨PositiveTell.fireAt, rfl, PositiveTell.fireAt_admitted, rfl, fireAt_apart⟩)
    ⟨(c 9, 0), by
      change (c 9, 0) ∈ fire request.present (PositiveTell.fireAt.selection.commit (T := Term atoms))
      rw [mem_fire]
      exact Or.inr (by simp [PositiveTell.fireAt, Selection.commit]), rfl⟩

end Controls

/-! ## What the line counts as sharing, and why it is only necessary -/

section Sharing

open PositiveTell (atoms A Occ x y c tellRule tellRule_checks tellSource request request_succeeds)

/-- **The captor**: no rows, and the knowledge `y = 7`, on the rule instance's own variable. -/
def captor : Configuration (Term atoms) Occ := ⟨[(y, c 7)], ∅⟩

theorem request_captor_composable : tellSource.composable request captor := by
  refine ⟨Finset.disjoint_empty_right _, fun _ => c 7, fun e inside => ?_⟩
  simp only [request, captor, List.nil_append, List.mem_singleton] at inside
  subst inside
  rfl

/-- The captor's knowledge mentions only `y`. -/
theorem captor_mentions_only_y : ∀ v, Mentions captor.equations v → v = 1 := by
  rintro v ⟨e, inside, occurs⟩
  simp only [captor, List.mem_singleton] at inside
  subst inside
  rcases occurs with occurs | occurs
  · cases occurs
    rfl
  · cases occurs

/-- The request mentions `y` nowhere: no knowledge, and its one row is `x`. -/
theorem request_does_not_mention_y :
    request.equations = [] ∧ ∀ o ∈ request.present, ¬ Occurs (1 : ℕ) o.1 := by
  refine ⟨rfl, fun o inside occurs => ?_⟩
  simp only [request, Finset.mem_singleton] at inside
  subst inside
  change Occurs (1 : ℕ) (Term.var 0 : Term atoms) at occurs
  cases occurs

/-- **Beside the captor no firing of the program is admitted**: the tell `y = 5` meets `y = 7`. -/
theorem nothing_admitted_beside_captor (f : AnnotatedRuns.Firing (Term atoms) (Subst atoms) Occ)
    (inProgram : PositiveTell.program f.rule) : ¬ f.Valid A Prod.fst (unionOf request captor) := by
  intro valid
  have rule : f.rule = tellRule := inProgram
  obtain ⟨firing, -⟩ := valid
  obtain ⟨σ, solved⟩ := firing.consistent
  have known : (y, c 7) ∈ f.selection.problem Prod.fst f.rule (unionOf request captor) := by
    simp [Selection.problem, unionOf, request, captor]
  have told : (y, c 5) ∈ f.selection.problem Prod.fst f.rule (unionOf request captor) := by
    simp [Selection.problem, rule, tellRule]
  have seven : σ 1 = c 7 := solved _ known
  have five : σ 1 = c 5 := solved _ told
  have same : (c 5 : Term atoms) = c 7 := five.symm.trans seven
  exact absurd (Term.const.inj same) (by decide)

theorem beside_captor_blocked : ¬ tellSource.Succeeds (unionOf request captor) := by
  rintro ⟨C', run, shows⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨f, inProgram, admitted, -⟩, -⟩
  · obtain ⟨o, present, isNine⟩ := shows
    have isX : o = (x, 0) := by
      simpa [unionOf, request, captor] using present
    subst isX
    have wrong : (x : Term atoms) = c 9 := isNine
    exact absurd wrong (by simp [x, c])
  · exact nothing_admitted_beside_captor f inProgram admitted

/-- **The captor switches the program off, sharing no unknown with the request**: its knowledge
constrains only the rule instance's own variable `y`, which the request mentions nowhere. -/
theorem captor_switches : tellSource.Switchable :=
  ⟨request, captor, request_captor_composable, request_succeeds, beside_captor_blocked⟩

/-- **The line puts the captor on its shared side, through the rule instance's own variable**: no run
of the request whose firings share no variable with the captor's knowledge shows success. -/
theorem captor_on_shared_side :
    ∀ C', Relation.ReflTransGen (ApartStep PositiveTell.program captor.equations) request C' →
      ¬ Shows (Prod.fst : Occ → Term atoms) (· = c 9) C' := by
  rcases switched_off_has_guard_or_shared (P := PositiveTell.program) (row := (· = c 9))
      request_captor_composable beside_captor_blocked with ⟨r, inProgram, check, member, -⟩ | shared
  · have isTell : r = tellRule := inProgram
    rw [isTell, tellRule_checks] at member
    exact absurd member List.not_mem_nil
  · exact shared

/-- **A neighbour that shares the request's unknown and agrees with the tell**: no rows, `x = 5`. -/
def friend : Configuration (Term atoms) Occ := ⟨[(x, c 5)], ∅⟩

theorem friend_problem :
    PositiveTell.fireAt.selection.problem Prod.fst PositiveTell.fireAt.rule (unionOf request friend) =
      [(x, c 5), (y, x), (y, c 5)] := rfl

theorem fireAt_beside_friend : PositiveTell.fireAt.Valid A Prod.fst (unionOf request friend) := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [PositiveTell.fireAt, request, friend, unionOf, Selection.commit, x, c]
  · refine ⟨fun _ => c 5, fun e inside => ?_⟩
    rw [friend_problem] at inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> rfl
  · intro check inside
    simp [PositiveTell.fireAt, tellRule] at inside
  · intro query inside
    simp [PositiveTell.fireAt] at inside

/-- **The line is necessary, not sufficient**: beside the friend the request succeeds, although its
only firing's information mentions `x`, which the friend's knowledge mentions and constrains. -/
theorem friend_shares_and_succeeds :
    tellSource.composable request friend ∧ tellSource.Succeeds (unionOf request friend) ∧
      Mentions (PositiveTell.fireAt.selection.problem Prod.fst PositiveTell.fireAt.rule request) 0 ∧
      Mentions friend.equations 0 := by
  refine ⟨⟨Finset.disjoint_empty_right _, fun _ => c 5, fun e inside => ?_⟩, ?_,
    ⟨(y, x), by rw [PositiveTell.fireAt_problem]; exact List.mem_cons_self .., Or.inr .var⟩,
    ⟨(x, c 5), List.mem_singleton_self _, Or.inl .var⟩⟩
  · simp only [request, friend, List.nil_append, List.mem_singleton] at inside
    subst inside
    rfl
  · refine ⟨_, .single ⟨PositiveTell.fireAt, rfl, fireAt_beside_friend, rfl⟩, (c 9, 0), ?_, rfl⟩
    change (c 9, 0) ∈ fire (unionOf request friend).present
      (PositiveTell.fireAt.selection.commit (T := Term atoms))
    rw [mem_fire]
    exact Or.inr (by simp [PositiveTell.fireAt, Selection.commit])

end Sharing

/-- **Where the system's knowledge shares a variable with the neighbour's, no step is apart**: a
firing's information contains the knowledge it fires at. So the second disjunct of the line then says
only that the system does not show success yet. -/
theorem no_apartStep_of_shared {sig : LPSignature} [DecidableEq (Term sig)]
    {P : RuleInstance (Term sig) → Prop} {K : EquationStore (Term sig)}
    {C C' : Configuration (Term sig) (Term sig × ℕ)} {v : sig.vars}
    (inC : Mentions C.equations v) (inK : Mentions K v) : ¬ ApartStep P K C C' := by
  rintro ⟨f, -, -, -, apart⟩
  obtain ⟨e, member, occurs⟩ := inC
  exact apart v ⟨e, by simp [Selection.problem, member], occurs⟩ inK

/-- **Then every apart run is empty.** -/
theorem apart_run_trivial {sig : LPSignature} [DecidableEq (Term sig)]
    {P : RuleInstance (Term sig) → Prop} {K : EquationStore (Term sig)}
    {C C' : Configuration (Term sig) (Term sig × ℕ)} {v : sig.vars}
    (inC : Mentions C.equations v) (inK : Mentions K v)
    (run : Relation.ReflTransGen (ApartStep P K) C C') : C' = C := by
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, step, -⟩
  · rfl
  · exact absurd step (no_apartStep_of_shared inC inK)

#print axioms captor_switches
#print axioms captor_on_shared_side
#print axioms captor_mentions_only_y
#print axioms request_does_not_mention_y
#print axioms friend_shares_and_succeeds
#print axioms no_apartStep_of_shared
#print axioms apart_run_trivial
#print axioms applyTerm_congr
#print axioms models_of_apart
#print axioms joint_of_apart
#print axioms succeeds_union_of_apart
#print axioms switched_off_has_guard_or_shared
#print axioms switchable_has_guard_or_shared
#print axioms tell_shares_with_neighbour
#print axioms tell_beside_other

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.SharedUnknown
