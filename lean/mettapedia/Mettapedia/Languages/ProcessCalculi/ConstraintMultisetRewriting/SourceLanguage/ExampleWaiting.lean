import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExamplesWellFormed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Observation

/-!
# Waiting and failing are told apart; a well-formed program whose `run` waits

**Failing against waiting.** The query `fail` ends with no alternative. The well-formed query
`(add-atom $s a)`, here `add $S a (ret 1)` over the empty program, cannot move at its start: its store
determines no address for `$S` (`undetermined`), and its store changes only by its own moves, so it waits
forever. Both bags of answers are empty (`fail_answers`, `waiting_answers`); the observations differ:
the waiting alternative shows `address $S` (`fail_and_waiting_differ`). Real HE and the engine's HE lane
answer this query with an error value; here nothing fails, the none query is shown with its type.

**A well-formed program whose `run` waits** (the control for the pattern clause of `WellFormed`):

```
(= (app (lam x. $F x) $a) (let $r (g ($F $a)) (run $r)))
(= (g 1) one)
!(app $G 1)
```

The program and the query are well formed (`program_wellFormed`, `query_wellFormed`): `($F $a)` applies
an unknown that a pattern of the left-hand side names. Unification is two-way, so the query's unknown
`$G` meets `(lam x. $F x)` and leaves `$F` undetermined; the inner call then puts `$F 1 = 1` in the
store, which `λy. y` and `λy. 1` both solve, and which has no most general solution (`no_principal`).
The run ends (`final_quiescent`) with no answer, and the observation shows the waiting `run`
(`deadlock_observed`). Well-formedness is a syntactic check; it does not ensure principal stores.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleWaiting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit Observation
open ExamplesWellFormed (lam holeAtBound holeAt)

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

def supply : ℕ → MClosed := fun _ => csym "fresh"

/-! ## Failing against waiting -/

/-- The empty program. -/
def emptyProgram : Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

/-- The query's own unknown `$S`, standing where a space is wanted. -/
def S : MData := mvar [3] 0

def addQuery : Comp mkeys [] () MTy := .add S (sym "a") (.ret (num 1))

theorem addQuery_wellFormed : QueryWellFormed emptyProgram [3] addQuery := by decide

/-- **The empty store determines no address for `$S`.** -/
theorem undetermined (h : MClosed) : ¬ Determines ([] : List (Constraint mkeys [] ())) S h := by
  intro determined
  have atP := determined.2 noNames (closeNames [(([], [3], 0), csym "p")] (csym "a")) (fun _ member => by
    cases member)
  have atQ := determined.2 noNames (closeNames [(([], [3], 0), csym "q")] (csym "a")) (fun _ member => by
    cases member)
  have p : Rigid.includeTerm noNames (csym "p") = Rigid.includeTerm noNames h := atP
  have q : Rigid.includeTerm noNames (csym "q") = Rigid.includeTerm noNames h := atQ
  have same := Rigid.include_injective noNames _ _ (p.trans q.symm)
  exact absurd same (by decide)

def waitStart : Config mkeys [] () MTy := Config.initial (fun _ => 0) addQuery

def waitBranch : Branch mkeys [] () MTy := ⟨[], .eval addQuery, [], []⟩

theorem waitBranch_reason : reason (D := D) waitBranch = some (.address S) := by
  have no : ¬ ∃ h, Determines ([] : List (Constraint mkeys [] ())) S h :=
    fun ⟨h, determined⟩ => undetermined h determined
  simp [reason, waitBranch, addQuery, no]

theorem waitStart_quiescent : Config.Quiescent (D := D) emptyProgram supply waitStart := by
  intro b member _ w' bs moved
  have only : b = waitBranch := Multiset.mem_singleton.mp member
  subst only
  exact stuck_of_reason waitBranch_reason w' bs moved

theorem waiting_answers : Config.answers (D := D) waitStart = 0 := by
  classical
  show Config.answers (D := D) (⟨⟨0, 0, fun _ => 0⟩, waitBranch ::ₘ 0⟩ : Config mkeys [] () MTy) = 0
  simp only [Config.answers]
  rw [Multiset.filter_cons_of_neg _ (fun hold => by obtain ⟨⟨_, t, focus⟩, _⟩ := hold; cases focus)]
  simp

theorem waiting_observed : observe (D := D) waitStart = ⟨0, 0, {.address S}⟩ := by
  classical
  have liveStart : live (D := D) waitStart = waitBranch ::ₘ 0 := by
    show Multiset.filter _ (waitBranch ::ₘ 0) = _
    rw [Multiset.filter_cons_of_pos (p := fun b : Branch mkeys [] () MTy => Solvable b.store)
      (a := waitBranch) _ live_nil]
    rfl
  simp only [observe, liveStart, waiting_answers]
  refine congrArg₂ (Shown.mk 0) ?_ ?_
  · rfl
  · rw [Multiset.filterMap_cons_some _ _ _ waitBranch_reason, Multiset.filterMap_zero]
    rfl

def failFinal : Config mkeys [] () MTy := ⟨⟨0, 0, fun _ => 0⟩, 0⟩

theorem fail_runs : Runs D emptyProgram supply (Config.initial (fun _ => 0) .fail) failFinal :=
  Relation.ReflTransGen.single (step_one live_nil (.fail _ _ _ _))

theorem fail_quiescent : Config.Quiescent (D := D) emptyProgram supply failFinal :=
  fun b member => absurd member (Multiset.notMem_zero b)

theorem fail_answers : Config.answers (D := D) failFinal = 0 := answers_zero

theorem fail_observed : observe (D := D) failFinal = ⟨0, 0, 0⟩ := by
  classical
  simp [observe, live, failFinal, Config.answers]

/-- **Failing and waiting are told apart**: two well-formed queries over the empty program, each with a
quiescent configuration it reaches and an empty bag of answers; the observations differ. -/
theorem fail_and_waiting_differ :
    Runs D emptyProgram supply (Config.initial (fun _ => 0) .fail) failFinal ∧
      Config.Quiescent (D := D) emptyProgram supply failFinal ∧
      Runs D emptyProgram supply waitStart waitStart ∧ Config.Quiescent (D := D) emptyProgram supply waitStart ∧
      Config.answers (D := D) failFinal = Config.answers (D := D) waitStart ∧
      observe (D := D) failFinal ≠ observe (D := D) waitStart := by
  refine ⟨fail_runs, fail_quiescent, .refl, waitStart_quiescent, by rw [fail_answers, waiting_answers], ?_⟩
  rw [fail_observed, waiting_observed]
  intro same
  have := congrArg (fun o : Shown MSig mkeys [] () MTy => Multiset.card o.waiting) same
  simp at this

/-! ## A well-formed program whose `run` waits -/

/-- `(app (lam x. $F x) $a)` at site `[100]`. -/
def lhs1 : MData := tuple [sym "app", lam (holeAtBound [100] 0), mvar [100] 1]

/-- `(g ($F $a))`. -/
def gText : MData := tuple [sym "g", holeAt [100] 0 (mvar [100] 1)]

/-- `(let $r (g ($F $a)) (run $r))`, the arrow at site `[101]`. -/
def rhs1 : Comp mkeys [] () MTy := .let_ [101] (mvar [101] 0) (.apply gText) (.run (mvar [101] 0))

def E1 : Equation mkeys [] () MTy := ⟨[100], lhs1, rhs1⟩

def lhs2 : MData := tuple [sym "g", num 1]

def E2 : Equation mkeys [] () MTy := ⟨[102], lhs2, .ret (sym "one")⟩

def program : Program mkeys [] () MTy := ⟨[E1, E2], fun t => .ret t⟩

/-- `(app $G 1)`, with `$G` the query's own unknown at site `[3]`. -/
def call : MData := tuple [sym "app", mvar [3] 0, num 1]

def query : Comp mkeys [] () MTy := .apply call

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) query

theorem program_wellFormed : WellFormed program := by decide

theorem query_wellFormed : QueryWellFormed program [3] query := by decide

def K1 : List (Constraint mkeys [] ()) := [] ++ [(instantiate (copyAt mkeys 0) lhs1, call)]

def gCall0 : MData := instantiate (copyAt mkeys 0) gText

def r0 : MData := instantiate (copyAt mkeys 0) (mvar [101] 0)

def K2 : List (Constraint mkeys [] ()) := K1 ++ [(instantiate (copyAt mkeys 1) lhs2, gCall0)]

def one1 : MData := instantiate (copyAt mkeys 1) (sym "one")

def r2 : MData := instantiate (openAt mkeys [101] 2) r0

def K3 : List (Constraint mkeys [] ()) := K2 ++ [(r2, one1)]

/-- The constant `1` at the context of a one-parameter unknown. -/
def oneAt {X : Type} {target : X → MetaArity MSig} : Term (signature MSig target) [()] () :=
  .op (.inl (.num 1)) .nil

/-- First solution: `$F ↦ λy. y`, `$a ↦ 1`, `$G ↦ lam x. x`, `$r ↦ one`. -/
def σ1 : Assignment (fam mkeys) noNames := fun x =>
  match x with
  | ⟨[0], ⟨[100], 0, ([()], ())⟩⟩ => .var .zero
  | ⟨[0], ⟨[100], 1, ([], ())⟩⟩ => Rigid.includeTerm noNames (cnum 1)
  | ⟨[], ⟨[3], 0, ([], ())⟩⟩ => lamAt (.var .zero)
  | ⟨[2, 0], ⟨[101], 0, ([], ())⟩⟩ => Rigid.includeTerm noNames (csym "one")
  | ⟨_, ⟨_, _, (_, _)⟩⟩ =>
      Rigid.includeTerm noNames (rename (Γ := []) (fun _ impossible => nomatch impossible) (csym "a"))

/-- Second solution: `$F ↦ λy. 1`, `$a ↦ 1`, `$G ↦ lam x. 1`, `$r ↦ one`. -/
def σ2 : Assignment (fam mkeys) noNames := fun x =>
  match x with
  | ⟨[0], ⟨[100], 0, ([()], ())⟩⟩ => oneAt
  | ⟨[0], ⟨[100], 1, ([], ())⟩⟩ => Rigid.includeTerm noNames (cnum 1)
  | ⟨[], ⟨[3], 0, ([], ())⟩⟩ => lamAt oneAt
  | ⟨[2, 0], ⟨[101], 0, ([], ())⟩⟩ => Rigid.includeTerm noNames (csym "one")
  | ⟨_, ⟨_, _, (_, _)⟩⟩ =>
      Rigid.includeTerm noNames (rename (Γ := []) (fun _ impossible => nomatch impossible) (csym "a"))

theorem σ1_solves : Models σ1 K3 := by
  intro e member
  simp only [K3, K2, K1, List.nil_append, List.cons_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem σ2_solves : Models σ2 K3 := by
  intro e member
  simp only [K3, K2, K1, List.nil_append, List.cons_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem K3_live : Solvable K3 := ⟨Empty, noNames, σ1, σ1_solves⟩
theorem K2_live : Solvable K2 := solvable_of_append K3_live
theorem K1_live : Solvable K1 := solvable_of_append K2_live

/-- **No principal solution**: `$F 1 = 1` is solved by `λy. y` and by `λy. 1`. A principal `θ` would
send `$F` to a term both solutions fix: not the bound variable (the second moves it), not a constant
head (the first moves it), and not an unknown's application (then `θ` would not solve `$F 1 = 1`,
whose right side is rigid). -/
theorem no_principal : ¬ ∃ θ, Principal K3 θ := by
  rintro ⟨θ, solves, general⟩
  have tell : instantiate θ (instantiate (copyAt mkeys 1) lhs2) = instantiate θ gCall0 :=
    solves (instantiate (copyAt mkeys 1) lhs2, gCall0) (by simp [K3, K2])
  have pair : tupleAt [symAt "g", instantiate θ (num 1)] =
      tupleAt [symAt "g", instantiate θ (hoD [0] [100] 0 (foD [0] [100] 1))] := tell
  have inner := (tuple2_inj pair).2
  rw [instantiate_hoD] at inner
  have g1 := general noNames σ1 σ1_solves (ho [0] [100] 0)
  have g2 := general noNames σ2 σ2_solves (ho [0] [100] 0)
  obtain ⟨T, hT⟩ : ∃ T : Term (signature MSig (fam mkeys)) [()] (), θ (ho [0] [100] 0) = T := ⟨_, rfl⟩
  rw [hT] at inner g1 g2
  cases T with
  | var v =>
      cases v with
      | zero => cases g2
      | succ w => cases w
  | op o args =>
      rcases o with o | ⟨x⟩
      · cases g1
      · cases inner

def b1 : Branch mkeys [] () MTy := callBranch D 0 [] call [] [] E1
def b2 : Branch mkeys [] () MTy := callBranch D 0 [] call [] [] E2
def frame0 : Frame mkeys [] () MTy := .bindTo [101] r0 (.run r0)
def b1' : Branch mkeys [] () MTy := ⟨K1, .eval (.apply gCall0), [frame0], []⟩
def d1 : Branch mkeys [] () MTy := callBranch D 1 K1 gCall0 [frame0] [] E1
def b3 : Branch mkeys [] () MTy := callBranch D 1 K1 gCall0 [frame0] [] E2
def b3' : Branch mkeys [] () MTy := ⟨K2, .value one1, [frame0], []⟩
def bStuck : Branch mkeys [] () MTy := ⟨K3, .eval (.run r2), [], []⟩

def C1 : Config mkeys [] () MTy := ⟨⟨1, 0, fun _ => 0⟩, b1 ::ₘ b2 ::ₘ 0⟩
def C2 : Config mkeys [] () MTy := ⟨⟨1, 0, fun _ => 0⟩, b1' ::ₘ b2 ::ₘ 0⟩
def C3 : Config mkeys [] () MTy := ⟨⟨2, 0, fun _ => 0⟩, d1 ::ₘ b3 ::ₘ b2 ::ₘ 0⟩
def C4 : Config mkeys [] () MTy := ⟨⟨2, 0, fun _ => 0⟩, d1 ::ₘ b3' ::ₘ b2 ::ₘ 0⟩
def final : Config mkeys [] () MTy := ⟨⟨3, 0, fun _ => 0⟩, d1 ::ₘ bStuck ::ₘ b2 ::ₘ 0⟩

theorem b2_dead : ¬ Solvable b2.store :=
  dead_of_length (ts := [sym "g", num 1]) (ts' := [sym "app", mvar [3] 0, num 1])
    (List.mem_singleton_self _) (by decide)

theorem d1_dead : ¬ Solvable d1.store :=
  dead_of_length (ts := [sym "app", instantiate (copyAt mkeys 1) (lam (holeAtBound [100] 0)),
      instantiate (copyAt mkeys 1) (mvar [100] 1)])
    (ts' := [sym "g", instantiate (copyAt mkeys 0) (holeAt [100] 0 (mvar [100] 1))])
    (List.mem_append_right _ (List.mem_singleton_self _)) (by decide)

theorem runs : Runs D program supply start final := by
  refine Relation.ReflTransGen.tail (b := C4) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := b3') (rest := d1 ::ₘ b2 ::ₘ 0)
      (bs := bStuck ::ₘ 0) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.cons_add, zero_add, Multiset.cons_swap]) K2_live
      (Move.letBind (D := D) (P := program) (supply := supply) ⟨2, 0, fun _ => 0⟩ K2 one1 [101] r0
        (.run r0) [] []))
  refine Relation.ReflTransGen.tail (b := C3) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := b3) (rest := d1 ::ₘ b2 ::ₘ 0)
      (bs := b3' ::ₘ 0) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.cons_add, zero_add, Multiset.cons_swap]) K2_live
      (Move.ret (D := D) (P := program) (supply := supply) ⟨2, 0, fun _ => 0⟩ K2 one1 [frame0] []))
  refine Relation.ReflTransGen.tail (b := C2) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := b1') (rest := b2 ::ₘ 0) rfl rfl K1_live
      (Move.apply (D := D) (P := program) (supply := supply) ⟨1, 0, fun _ => 0⟩ K1 gCall0 [frame0] []
        ⟨E2, List.mem_cons_of_mem _ (List.mem_singleton_self _), K2_live⟩))
  refine Relation.ReflTransGen.tail (b := C1) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := b1) (rest := b2 ::ₘ 0) (bs := b1' ::ₘ 0) rfl
      (by rw [Multiset.cons_add, zero_add]) K1_live
      (Move.letStart (D := D) (P := program) (supply := supply) ⟨1, 0, fun _ => 0⟩ K1 [101] r0
        (.apply gCall0) (.run r0) [] []))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := ⟨[], .eval query, [], []⟩) (rest := 0) rfl rfl
      live_nil (Move.apply (D := D) (P := program) (supply := supply) ⟨0, 0, fun _ => 0⟩ [] call [] []
        ⟨E1, List.mem_cons_self, K1_live⟩))

theorem bStuck_reason : reason (D := D) bStuck = some (.noPrincipal r2) := by
  simp [reason, bStuck, no_principal]

theorem final_quiescent : Config.Quiescent (D := D) program supply final := by
  intro b member live w' bs moved
  have member' : b ∈ d1 ::ₘ bStuck ::ₘ b2 ::ₘ 0 := member
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member'
  rcases member' with rfl | rfl | rfl
  · exact d1_dead live
  · exact stuck_of_reason bStuck_reason w' bs moved
  · exact b2_dead live

theorem final_answers : Config.answers (D := D) final = 0 := by
  classical
  show Config.answers (D := D) (⟨⟨3, 0, fun _ => 0⟩, d1 ::ₘ bStuck ::ₘ b2 ::ₘ 0⟩ : Config mkeys [] () MTy) = 0
  rw [answers_cons_dead (D := D) d1_dead]
  simp only [Config.answers]
  rw [Multiset.filter_cons_of_neg _ (fun hold => by obtain ⟨⟨_, t, focus⟩, _⟩ := hold; cases focus)]
  rw [Multiset.filter_cons_of_neg _ (fun hold => b2_dead hold.2)]
  simp

theorem final_live : live (D := D) final = bStuck ::ₘ 0 := by
  classical
  show Multiset.filter _ (d1 ::ₘ bStuck ::ₘ b2 ::ₘ 0) = _
  rw [Multiset.filter_cons_of_neg (p := fun b : Branch mkeys [] () MTy => Solvable b.store) (a := d1) _ d1_dead,
    Multiset.filter_cons_of_pos (p := fun b : Branch mkeys [] () MTy => Solvable b.store) (a := bStuck) _ K3_live,
    Multiset.filter_cons_of_neg (p := fun b : Branch mkeys [] () MTy => Solvable b.store) (a := b2) _ b2_dead]
  rfl

/-- **The deadlock is observed**: a well-formed program and query, a run to a quiescent configuration
with no answer, whose observation shows the `run` waiting for a principal solution. -/
theorem deadlock_observed :
    WellFormed program ∧ QueryWellFormed program [3] query ∧ Runs D program supply start final ∧
      Config.Quiescent (D := D) program supply final ∧ Config.answers (D := D) final = 0 ∧
      observe (D := D) final = ⟨0, 0, {.noPrincipal r2}⟩ := by
  refine ⟨program_wellFormed, query_wellFormed, runs, final_quiescent, final_answers, ?_⟩
  classical
  simp only [observe, final_live, final_answers]
  refine congrArg₂ (Shown.mk 0) ?_ ?_
  · rfl
  · rw [Multiset.filterMap_cons_some _ _ _ bStuck_reason, Multiset.filterMap_zero]
    rfl

#print axioms fail_and_waiting_differ
#print axioms no_principal
#print axioms deadlock_observed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleWaiting
