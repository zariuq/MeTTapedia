import Mettapedia.GSLT.LanguageDef.BindingDecisionExactness

/-!
# Adequacy of the binding-decision language for the compiled evaluator

The reference machine of the binding-decision language reaches a terminal
result from a decision exactly when the compiled decision evaluator lists
that result.  Through the exactness theorem this transfers to the language
itself: the language's own multi-step reduction from an encoded decision to
an encoded result is membership in the evaluator's output, and hence, by the
existing compiler theorem, in the canonical syntactic matcher's output.  The
language definition is therefore not a description of the compiled decision
trees beside their evaluator; it *is* their evaluator, and the Lean
evaluator is now a proved reference for it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Reachability in the reference machine -/

/-- One machine step as a relation. -/
def MachineStep (source target : MachineState) : Prop :=
  machineStep? source = some target

/-- Finitely many machine steps. -/
def Reaches : MachineState → MachineState → Prop :=
  Relation.ReflTransGen MachineStep

theorem machineStep?_done (bindings : Bindings) : machineStep? (.done bindings) = none := rfl

/-- Steps are deterministic, so a run that ends in a result passes through
the unique successor of every non-terminal state on its way. -/
theorem reaches_of_step {source next : MachineState} {final : Bindings}
    (step : machineStep? source = some next) (run : Reaches source (.done final)) :
    Reaches next (.done final) := by
  rcases Relation.ReflTransGen.cases_head run with equal | ⟨next', step', rest⟩
  · subst equal
    simp [machineStep?_done] at step
  · have : next = next' := by
      change machineStep? source = some next' at step'
      exact Option.some.inj (step.symm.trans step')
    subst this
    exact rest

theorem reaches_iff_of_step {source next : MachineState} {final : Bindings}
    (step : machineStep? source = some next) :
    Reaches source (.done final) ↔ Reaches next (.done final) :=
  ⟨reaches_of_step step, fun rest => Relation.ReflTransGen.head step rest⟩

/-- A stuck state reaches no result. -/
theorem not_reaches_of_stuck {source : MachineState} {final : Bindings}
    (stuck : machineStep? source = none) (notDone : ∀ bindings, source ≠ .done bindings) :
    ¬ Reaches source (.done final) := by
  intro run
  rcases Relation.ReflTransGen.cases_head run with equal | ⟨next, step, _⟩
  · exact notDone final equal
  · change machineStep? source = some next at step
    rw [stuck] at step
    simp at step

/-- A finished return with an empty continuation is the result. -/
theorem reaches_ret_nil_iff (bindings : Bindings) (subject : Pattern) (final : Bindings) :
    Reaches (.ret bindings subject []) (.done final) ↔ final = bindings := by
  constructor
  · intro run
    have run' := reaches_of_step (next := .done bindings) rfl run
    rcases Relation.ReflTransGen.cases_head run' with equal | ⟨_, step, _⟩
    · exact (MachineState.done.inj equal).symm
    · change machineStep? (.done bindings) = some _ at step
      simp [machineStep?_done] at step
  · rintro rfl
    exact Relation.ReflTransGen.single rfl

/-! ## The compiled evaluator, reorganized by the machine's tests -/

theorem eval_checkBound_eq (path : AccessPath) (expected : Nat) (subject : Pattern) :
    Decision.eval (.checkBound path expected) subject =
      match path.project? subject with
      | some focused => if isBoundAt focused expected then [[]] else []
      | none => [] := by
  simp only [Decision.eval]
  cases path.project? subject with
  | none => rfl
  | some focused =>
      cases focused <;> simp [isBoundAt]

theorem eval_checkConstructor_eq (path : AccessPath) (expected : String) (arity : Nat)
    (children : Decision) (subject : Pattern) :
    Decision.eval (.checkConstructor path expected arity children) subject =
      match path.project? subject with
      | some focused =>
          if isConstructorOf focused expected arity then children.eval subject else []
      | none => [] := by
  simp only [Decision.eval]
  cases path.project? subject with
  | none => rfl
  | some focused =>
      cases focused <;> simp [isConstructorOf]

theorem mem_eval_join_iff (head tail : Decision) (subject : Pattern) (bindings : Bindings) :
    bindings ∈ Decision.eval (.join head tail) subject ↔
      ∃ headBindings ∈ head.eval subject, ∃ tailBindings ∈ tail.eval subject,
        mergeBindings headBindings tailBindings = some bindings := by
  simp only [Decision.eval, List.mem_flatMap, List.mem_filterMap]

/-! ## Continuation semantics of the machine -/

/-- Running a decision under a continuation reaches a result exactly when
the evaluator lists some bindings for the decision and returning those
bindings under the continuation reaches the result. -/
theorem reaches_run_iff (decision : Decision) :
    ∀ (subject : Pattern) (kont : List Frame) (final : Bindings),
      Reaches (.run decision subject kont) (.done final) ↔
        ∃ bindings ∈ decision.eval subject, Reaches (.ret bindings subject kont) (.done final) := by
  induction decision with
  | succeed =>
      intro subject kont final
      rw [reaches_iff_of_step (next := .ret [] subject kont) rfl]
      simp [Decision.eval]
  | capture path name =>
      intro subject kont final
      cases projection : path.project? subject with
      | none =>
          have stuck : machineStep? (.run (.capture path name) subject kont) = none := by
            simp [machineStep?, projection]
          simp [not_reaches_of_stuck stuck (fun _ => MachineState.noConfusion), Decision.eval,
            projection]
      | some focused =>
          have step : machineStep? (.run (.capture path name) subject kont) =
              some (.ret [(name, focused)] subject kont) := by
            simp [machineStep?, projection]
          rw [reaches_iff_of_step step]
          simp [Decision.eval, projection]
  | checkBound path expected =>
      intro subject kont final
      rw [eval_checkBound_eq]
      cases projection : path.project? subject with
      | none =>
          have stuck : machineStep? (.run (.checkBound path expected) subject kont) = none := by
            simp [machineStep?, projection]
          simp [not_reaches_of_stuck stuck (fun _ => MachineState.noConfusion)]
      | some focused =>
          cases bound : isBoundAt focused expected with
          | false =>
              have stuck :
                  machineStep? (.run (.checkBound path expected) subject kont) = none := by
                simp [machineStep?, projection, bound]
              simp [not_reaches_of_stuck stuck (fun _ => MachineState.noConfusion), bound]
          | true =>
              have step : machineStep? (.run (.checkBound path expected) subject kont) =
                  some (.ret [] subject kont) := by
                simp [machineStep?, projection, bound]
              rw [reaches_iff_of_step step]
              simp [bound]
  | checkConstructor path expected arity children inductionHypothesis =>
      intro subject kont final
      rw [eval_checkConstructor_eq]
      cases projection : path.project? subject with
      | none =>
          have stuck : machineStep?
              (.run (.checkConstructor path expected arity children) subject kont) = none := by
            simp [machineStep?, projection]
          simp [not_reaches_of_stuck stuck (fun _ => MachineState.noConfusion)]
      | some focused =>
          cases constructorTest : isConstructorOf focused expected arity with
          | false =>
              have stuck : machineStep?
                  (.run (.checkConstructor path expected arity children) subject kont) =
                    none := by
                simp [machineStep?, projection, constructorTest]
              simp [not_reaches_of_stuck stuck (fun _ => MachineState.noConfusion),
                constructorTest]
          | true =>
              have step : machineStep?
                  (.run (.checkConstructor path expected arity children) subject kont) =
                    some (.run children subject kont) := by
                simp [machineStep?, projection, constructorTest]
              rw [reaches_iff_of_step step]
              simpa [constructorTest] using inductionHypothesis subject kont final
  | join head tail headHypothesis tailHypothesis =>
      intro subject kont final
      rw [reaches_iff_of_step (next := .run head subject (.joinRight tail :: kont)) rfl,
        headHypothesis]
      constructor
      · rintro ⟨headBindings, headMember, run⟩
        rw [reaches_iff_of_step (next := .run tail subject (.joinMerge headBindings :: kont)) rfl,
          tailHypothesis] at run
        obtain ⟨tailBindings, tailMember, run⟩ := run
        cases merge : mergeBindings headBindings tailBindings with
        | none =>
            have stuck : machineStep?
                (.ret tailBindings subject (.joinMerge headBindings :: kont)) = none := by
              simp [machineStep?, merge]
            exact (not_reaches_of_stuck stuck (fun _ => MachineState.noConfusion) run).elim
        | some merged =>
            have step : machineStep?
                (.ret tailBindings subject (.joinMerge headBindings :: kont)) =
                  some (.ret merged subject kont) := by
              simp [machineStep?, merge]
            rw [reaches_iff_of_step step] at run
            exact ⟨merged, (mem_eval_join_iff head tail subject merged).mpr
              ⟨headBindings, headMember, tailBindings, tailMember, merge⟩, run⟩
      · rintro ⟨merged, mergedMember, run⟩
        obtain ⟨headBindings, headMember, tailBindings, tailMember, merge⟩ :=
          (mem_eval_join_iff head tail subject merged).mp mergedMember
        refine ⟨headBindings, headMember, ?_⟩
        rw [reaches_iff_of_step (next := .run tail subject (.joinMerge headBindings :: kont)) rfl,
          tailHypothesis]
        refine ⟨tailBindings, tailMember, ?_⟩
        have step : machineStep? (.ret tailBindings subject (.joinMerge headBindings :: kont)) =
            some (.ret merged subject kont) := by
          simp [machineStep?, merge]
        rw [reaches_iff_of_step step]
        exact run

/-- The machine computes exactly the evaluator. -/
theorem reaches_iff_mem_eval (decision : Decision) (subject : Pattern) (final : Bindings) :
    Reaches (.run decision subject []) (.done final) ↔ final ∈ decision.eval subject := by
  rw [reaches_run_iff]
  constructor
  · rintro ⟨bindings, member, run⟩
    rw [reaches_ret_nil_iff] at run
    subst run
    exact member
  · intro member
    exact ⟨final, member, (reaches_ret_nil_iff final subject final).mpr rfl⟩

/-! ## Transfer to the language -/

/-- Finitely many language steps. -/
def LanguageReaches : Pattern → Pattern → Prop :=
  Relation.ReflTransGen ir.semantics.Step

theorem languageReaches_of_reaches {source target : MachineState}
    (run : Reaches source target) :
    LanguageReaches (encodeState source) (encodeState target) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step rest => exact Relation.ReflTransGen.tail rest (step_of_machineStep step)

/-- Every language run from an encoded state is the encoding of a machine
run. -/
theorem reaches_of_languageReaches {source : MachineState} {target : Pattern}
    (run : LanguageReaches (encodeState source) target) :
    ∃ final : MachineState, target = encodeState final ∧ Reaches source final := by
  induction run with
  | refl => exact ⟨source, rfl, Relation.ReflTransGen.refl⟩
  | tail _ step inductionHypothesis =>
      obtain ⟨middle, rfl, run⟩ := inductionHypothesis
      obtain ⟨next, machineStep, rfl⟩ := machineStep_of_step step
      exact ⟨next, rfl, Relation.ReflTransGen.tail run machineStep⟩

/-- The language reaches an encoded result from an encoded decision exactly
when the compiled evaluator lists that result. -/
theorem languageReaches_iff_mem_eval (decision : Decision) (subject : Pattern)
    (final : Bindings) :
    LanguageReaches (encodeState (.run decision subject [])) (encodeState (.done final)) ↔
      final ∈ decision.eval subject := by
  constructor
  · intro run
    obtain ⟨state, equal, machineRun⟩ := reaches_of_languageReaches run
    have := encodeState_injective equal
    subst this
    exact (reaches_iff_mem_eval decision subject final).mp machineRun
  · intro member
    exact languageReaches_of_reaches ((reaches_iff_mem_eval decision subject final).mpr member)

/-- Through the compiler theorem: the language executing a compiled pattern
plan is the canonical syntactic matcher. -/
theorem languageReaches_compile_iff_mem_matchPattern (plan : FirstOrder.PatternPlan)
    (subject : Pattern) (final : Bindings) :
    LanguageReaches (encodeState (.run (compile plan) subject [])) (encodeState (.done final)) ↔
      final ∈ matchPattern plan.erase subject := by
  rw [languageReaches_iff_mem_eval, eval_compile_eq_matchPattern]

#print axioms reaches_iff_mem_eval
#print axioms languageReaches_iff_mem_eval
#print axioms languageReaches_compile_iff_mem_matchPattern

end Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
