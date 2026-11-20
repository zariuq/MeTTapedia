import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingFirstOrder

/-!
# Controls for hiding

* **The bisimulation has instances that fire** (`hidden_reaches_success`): the request with the extra
  knowledge `x₉ = 3`, which no row mentions, hides to the request with `x₉` kept only as a name
  (`hiddenRequest_related`), and both reach success under the positive program.
* **Dropping every equation that mentions a hidden unknown is unsound**
  (`naive_drop_not_seen_alike`): over a signature with one unary function symbol `f`, the store
  `x = f(h)` with `h` hidden is not seen alike, from the row `x`, by the empty store: the empty store
  lets `x` be a constant, which `x = f(h)` excludes. The projection must keep `h` as an existential
  witness, as `hideStore` does.
* **The hidden store is genuinely weaker** (`hiding_forgets`): from `x = 5, h = x` with `h` hidden, the
  hidden store has a solution with `h = 7`, which the original refuses. Knowledge, after hiding, does
  not only grow.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingControls

open Mettapedia.Logic.LP
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Examples (Tm X E x c shift everywhere)
open CompositionControls (tellRule tellRule_terms tellProgram tellAt result_succeeds freeVars_var
  freeVars_const)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## An instance that fires -/

/-- The unknown `x₉`. -/
def nine : Term atoms := .var 9

/-- The request with the knowledge `x₉ = 3`, which no row mentions. -/
def knowingRequest : State Tm ℕ := ⟨PUnit.unit, [(nine, c 3)], {0}, fun _ => x⟩

theorem knowingRequest_mentions {t : Term atoms} (mentioned : knowingRequest.Mentions t) :
    t = nine ∨ t = c 3 ∨ t = x := by
  rcases mentioned with first | second | ⟨o, -, rfl⟩
  · simp only [knowingRequest, List.map_cons, List.map_nil, List.mem_singleton] at first
    exact Or.inl first
  · simp only [knowingRequest, List.map_cons, List.map_nil, List.mem_singleton] at second
    exact Or.inr (Or.inl second)
  · exact Or.inr (Or.inr rfl)

theorem tellAt_admitted_knowing : (step X ℕ E tellProgram).Admits (s := knowingRequest) tellAt := by
  refine (admits_iff tellAt).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 1 then h 0 else g v, fun t mentioned => ?_, fun t member => ?_⟩
    · rcases knowingRequest_mentions mentioned with rfl | rfl | rfl <;> rfl
    · rcases tellRule_terms member with rfl | rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tellAt, knowingRequest, Selection.commit]
  · refine ⟨PUnit.unit, fun v => if v = 9 then c 3 else c 5, fun e member => ?_⟩
    have known : tellAt.information X knowingRequest =
        [(nine, c 3), ((Term.var 1 : Term atoms), x), ((Term.var 1 : Term atoms), c 5)] := rfl
    rw [known] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro check member
    simp [tellAt, tellRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [tellAt, tellRule, Firing.collectOpened] at member

theorem knowing_result_succeeds : Succeeds (· = c 9) (tellAt.result X knowingRequest) :=
  ⟨1, by simp [Firing.result, tellAt, knowingRequest, fire, Selection.commit], rfl⟩

theorem knowingRequest_succeeds :
    ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep) knowingRequest t ∧
      Succeeds (· = c 9) t :=
  ⟨_, .single ⟨tellAt, tellAt_admitted_knowing, rfl⟩, knowing_result_succeeds⟩

theorem knowing_solvable : ∃ θ, unifyTotal knowingRequest.knowledge = some θ :=
  unifyTotal_complete ⟨fun _ => c 3, fun e member => by
    simp only [knowingRequest, List.mem_singleton] at member
    subst member
    rfl⟩

/-- **The request and its hiding of `x₉` are related by the bisimulation.** -/
theorem hiddenRequest_related :
    ∃ θ, HiddenFO knowingRequest (withKnowledge knowingRequest (hideStore θ {9} knowingRequest.knowledge)) := by
  obtain ⟨θ, accepted⟩ := knowing_solvable
  refine ⟨θ, hiddenFO_hide accepted ?_⟩
  rintro v ⟨t, ⟨o, -, rfl⟩, inside⟩
  have zero := freeVars_var 0 inside
  subst zero
  decide

/-- **Both reach success**: the hidden state by the bisimulation. -/
theorem hidden_reaches_success :
    ∃ θ, ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep)
      (withKnowledge knowingRequest (hideStore θ {9} knowingRequest.knowledge)) t ∧ Succeeds (· = c 9) t := by
  obtain ⟨θ, related⟩ := hiddenRequest_related
  exact ⟨θ, (reaches_iff_of_hiddenFO related).mp knowingRequest_succeeds⟩

/-! ## Dropping the equations of a hidden unknown is unsound -/

/-- A signature with one unary function symbol. -/
abbrev unary : LPSignature where
  constants := ℕ
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Unit
  functionArity := fun _ => 1

/-- The term `f(t)`. -/
def fOf (t : Term unary) : Term unary := .app () fun _ => t

/-- **Dropping every equation that mentions a hidden unknown is unsound**: `x = f(h)` with `h`
hidden is not seen alike from the row `x` by the empty store. -/
theorem naive_drop_not_seen_alike :
    ¬ SeenAlike (FirstOrder.action unary) [((Term.var 0 : Term unary), fOf (Term.var 1))] []
      (· = (Term.var 0 : Term unary)) := by
  rintro ⟨-, back⟩
  obtain ⟨σ, solved, near⟩ := back (fun _ => (Term.const 0 : Term unary)) (fun e member => by cases member)
  have bound : σ 0 = fOf (σ 1) := solved _ List.mem_cons_self
  have agrees : σ 0 = (Term.const 0 : Term unary) := near (Term.var 0) rfl
  rw [bound] at agrees
  cases agrees

/-! ## The hidden store is genuinely weaker -/

/-- `x = 5, h = x`, with `h` the unknown `x₁`. -/
def chain : EquationStore (Term atoms) := [(x, c 5), (Term.var 1, x)]

theorem chain_vars {v : ℕ} (inside : v ∈ eqVars chain) : v = 0 ∨ v = 1 := by
  obtain ⟨e, member, occurs⟩ := (mem_eqVars (σ := atoms) (equations := chain)).mp inside
  simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rcases occurs with occurs | occurs
    · exact Or.inl (freeVars_var 0 occurs)
    · exact (freeVars_const 5 occurs).elim
  · rcases occurs with occurs | occurs
    · exact Or.inr (freeVars_var 1 occurs)
    · exact Or.inl (freeVars_var 0 occurs)

/-- `h` to `7`, everything else to `5`. -/
def freed : Subst atoms := fun v => if v = 1 then c 7 else c 5

/-- **The hidden store has a solution the original refuses.** -/
theorem hiding_forgets :
    ∃ θ, unifyTotal chain = some θ ∧ ∃ σ : Subst atoms,
      action.Models σ (hideStore θ {1} chain) ∧ ¬ action.Models σ chain := by
  obtain ⟨θ, accepted⟩ : ∃ θ, unifyTotal chain = some θ :=
    unifyTotal_complete ⟨fun _ => c 5, fun e member => by
      simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl⟩
  have unified : Unifies θ chain := unifyTotal_sound chain θ accepted
  have atZero : θ 0 = c 5 := unified (x, c 5) List.mem_cons_self
  refine ⟨θ, accepted, freed, fun e member => ?_, fun solved => ?_⟩
  · rcases (mem_hideStore (sig := atoms) (θ := θ) (H := {1}) (K := chain)).mp member with
      ⟨v, inK, outH, rfl⟩ | ⟨v, -, -, rfl⟩
    · have zero : v = 0 := by
        rcases chain_vars inK with zero | one
        · exact zero
        · subst one
          exact absurd (Finset.mem_singleton_self 1) outH
      subst zero
      show Subst.applyTerm freed (Term.var 0 : Term atoms) = Subst.applyTerm freed (θ 0)
      rw [atZero]
      rfl
    · rfl
  · have linked : Subst.applyTerm freed (Term.var 1 : Term atoms) = Subst.applyTerm freed x :=
      solved ((Term.var 1 : Term atoms), x) (List.mem_cons_of_mem _ List.mem_cons_self)
    have seven : Subst.applyTerm freed (Term.var 1 : Term atoms) = c 7 := rfl
    have five : Subst.applyTerm freed x = c 5 := rfl
    rw [seven, five] at linked
    exact absurd (Term.const.inj linked) (by decide)

#print axioms hiddenRequest_related
#print axioms hidden_reaches_success
#print axioms naive_drop_not_seen_alike
#print axioms hiding_forgets

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingControls
