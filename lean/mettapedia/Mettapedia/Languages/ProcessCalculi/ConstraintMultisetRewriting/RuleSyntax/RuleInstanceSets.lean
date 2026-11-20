import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy

/-!
# Programs given as sets of rule instances

The tree's first-order step under a rule set (`LogicOverTheStep.ProgramAdequacy.program`) admits a
firing when its rule instance belongs to a fixed set of rule instances. No instance is opened: a rule
instance used twice uses the same unknowns twice.

* **For ground programs it is the step of the program** (`instanceSet_eq`): when every substitution
  fixes the terms of every rule and no rule has collect patterns, its transition relation is that of
  the first-order step restricted to the program (`firstOrderOn`), hence, through `embed`, that of the
  label-keeping step of the program (`firstOrder_eq`).
* **With unknowns it is not** (`Controls.instanceSet_captures`, `Controls.opened_keeps_caller_free`):
  the rule "tell `x = 5`" used as an instance binds a caller's row labelled by the same unknown `x`
  to `5`; opened freshly, as the step of the program does, it leaves the caller's `x` free (a solution
  of the result sends it to `7`). The instance-set form shares a rule's unknowns with the caller, which
  the fresh opening of rule variables at each use excludes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open LogicOverTheStep.ProgramAdequacy (program program_succ_iff)

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- The bodies of the rules of a program, as rule instances. -/
def bodies (P : Program (Terms T)) : Set (RuleInstance T) := {i | ∃ r ∈ P, r.body = i}

/-- A rule is ground when every substitution fixes its terms. -/
def Ground (r : Rule (Terms T)) : Prop := ∀ t ∈ r.terms, ∀ σ : S, A.apply σ t = t

/-- A map that fixes every term of a rule fixes its body. -/
theorem map_fixed (r : Rule (Terms T)) (f : T → T) (fixes : ∀ t ∈ r.terms, f t = t) :
    r.body.map f = r.body := by
  obtain ⟨locals, ⟨take, read, tell, checks, produce⟩, collect⟩ := r
  simp only [Rule.terms] at fixes
  simp only [RuleInstance.map, RuleInstance.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · conv_rhs => rw [← List.map_id take]
    exact List.map_congr_left fun t member => fixes t (by simp [member])
  · conv_rhs => rw [← List.map_id read]
    exact List.map_congr_left fun t member => fixes t (by simp [member])
  · conv_rhs => rw [← List.map_id tell]
    refine List.map_congr_left fun pair member => ?_
    have first : f pair.1 = pair.1 :=
      fixes pair.1 (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        (List.mem_map_of_mem member))))))
    have second : f pair.2 = pair.2 :=
      fixes pair.2 (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr
        (List.mem_map_of_mem member)))))
    rw [first, second]
    rfl
  · conv_rhs => rw [← List.map_id checks]
    refine List.map_congr_left fun c member => ?_
    have inside : ∀ t ∈ checkTerms c, f t = t := fun t term => fixes t (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨c, member, term⟩))))
    cases c with
    | equal left right =>
        simp only [Check.map, id, inside left (by simp [checkTerms]), inside right (by simp [checkTerms])]
    | predicate quantifier pattern => simp only [Check.map, id, inside pattern (by simp [checkTerms])]
    | count pattern number => simp only [Check.map, id, inside pattern (by simp [checkTerms])]
  · conv_rhs => rw [← List.map_id produce]
    exact List.map_congr_left fun t member => fixes t (by simp [member])

variable {A} {O : Type uO} [DecidableEq O] {label : O → T} {P : Program (Terms T)}

omit [DecidableEq O] in
theorem opened_ground (g : Firing O (ext A) P PUnit.unit) (ground : Ground A g.rule) :
    g.opened (frames A) = g.rule.body :=
  map_fixed g.rule (A.apply g.opening) fun t member => ground t member g.opening

/-- **For ground programs without collect patterns, the instance-set form is the step of the
program.** -/
theorem instanceSet_eq (ground : ∀ r ∈ P, Ground A r) (noCollect : ∀ r ∈ P, r.collect = [])
    (C C' : Configuration T O) :
    Succ (program A label (bodies P)) C C' ↔ Succ (firstOrderOn A label P) C C' := by
  constructor
  · intro reached
    obtain ⟨rule, sel, ⟨r, member, rfl⟩, valid, result⟩ := (program_succ_iff A label _ C C').mp reached
    let g : Firing O (ext A) P PUnit.unit := ⟨r, member, PUnit.unit, A.identity, sel, []⟩
    have opened : g.opened (frames A) = r.body := opened_ground g (ground r member)
    have image : toFirstOrder A P g = ⟨r.body, [], sel⟩ := by
      unfold toFirstOrder
      rw [opened]
      simp [g]
    refine ⟨toFirstOrder A P g, ⟨?_, g, ?_, by simp [g, noCollect r member], rfl⟩, ?_⟩
    · show (toFirstOrder A P g).Valid A label C
      rw [image]
      exact PredicateQueryAdmission.regionValid_nil_iff.mpr valid
    · exact Examples.fresh_of_ground A _ g fun t inside σ => ground r member t inside σ
    · show (toFirstOrder A P g).result label C = C'
      rw [image]
      exact result
  · rintro ⟨f, ⟨admitted, g, fresh, collect, rfl⟩, result⟩
    have opened := opened_ground g (ground g.rule g.member)
    refine (program_succ_iff A label _ C C').mpr ⟨g.rule.body, g.selection, ⟨g.rule, g.member, rfl⟩,
      ?_, ?_⟩
    · have valid := admitted.firing
      change g.selection.Valid A label (g.opened (frames A)) C at valid
      rw [opened] at valid
      exact valid
    · change g.selection.result label (g.opened (frames A)) C = C' at result
      rw [opened] at result
      exact result

/-! ## Controls: with unknowns, instance sets share them with the caller -/

namespace Controls

open Mettapedia.Logic.LP
open Examples (x c everywhere)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- Tell `x = 5`. -/
def tellFive : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[], [], [(x, c 5)], [], []⟩, []⟩

/-- The program of that one rule. -/
def tellProgram : Program (Terms (Term atoms)) := {tellFive}

/-- A caller's request row `0`, labelled by its unknown `x`, which nothing binds. -/
def request : Configuration (Term atoms) ℕ := ⟨[], {0}⟩

/-- Every identity is labelled by the caller's unknown. -/
def callerLabel : ℕ → Term atoms := fun _ => x

/-- **The instance-set form binds the caller's unknown**: firing the rule instance tells `x = 5` about
the caller's own `x`. -/
theorem instanceSet_captures :
    ∃ C', Succ (program action callerLabel (bodies tellProgram)) request C' ∧
      ∀ σ : Subst atoms, action.Models σ C'.equations → σ 0 = c 5 := by
  refine ⟨⟨[(x, c 5)], {0}⟩, (program_succ_iff action callerLabel _ request _).mpr
    ⟨tellFive.body, ⟨[], [], []⟩, ⟨tellFive, rfl, rfl⟩, ?_, ?_⟩, ?_⟩
  · refine ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [request, Selection.commit]
    · refine ⟨everywhere 5, fun e member => ?_⟩
      have known : (⟨[], [], []⟩ : Selection ℕ).problem callerLabel tellFive.body request =
          [(x, c 5)] := rfl
      rw [known, List.mem_singleton] at member
      subst member
      rfl
    · intro check member
      cases member
  · simp [Selection.result, Selection.problem, Selection.equations, request, tellFive, fire,
      Selection.commit]
  · intro σ solved
    exact solved (x, c 5) List.mem_cons_self

/-- **Opened freshly, the same rule leaves the caller's unknown free**: every result of the step of
the program has a solution that sends the caller's `x` to `7`. -/
theorem opened_keeps_caller_free (C' : Configuration (Term atoms) ℕ)
    (reached : Succ (firstOrderOn action callerLabel tellProgram) request C') :
    ∃ σ : Subst atoms, action.Models σ C'.equations ∧ σ 0 = c 7 := by
  obtain ⟨f, ⟨-, ⟨r, member, ext, ι, sel, seen⟩, fresh, -, rfl⟩, rfl⟩ := reached
  obtain rfl : r = tellFive := member
  obtain ⟨u, state, rule⟩ := fresh PUnit.unit (everywhere 7) (everywhere 5)
  have seven : u 0 = c 7 := state x (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩))
  have five : Subst.applyTerm u (ι 0) = c 5 := rule x (by simp [tellFive, Rule.terms])
  refine ⟨u, ?_, seven⟩
  intro e inside
  change e ∈ [(ι 0, c 5)] at inside
  rw [List.mem_singleton] at inside
  subst inside
  exact five

end Controls

#print axioms map_fixed
#print axioms instanceSet_eq
#print axioms Controls.instanceSet_captures
#print axioms Controls.opened_keeps_caller_free

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame
