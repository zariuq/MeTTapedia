import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ModalComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.HeatingBisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulFirstOrder

/-!
# OSLF in the fibre over one solution, and OSLF of the step

A hosted calculus reads a store at one solution of its knowledge, as rho reads it at the identity
(`HeatingBisimulation.RuleStep`: the step restricted to a rule set, keeping the solution a model).
Configurations modelled by the solution are the fibre of the knowledge over it; the step at the
solution is the step restricted to that fibre (`modelledStep`). The inclusion of the fibre is a map
of transition systems into the step at every solution (`PlainStep`).

* `zig_val`: the inclusion always carries steps, so possibility at the solution implies possibility
  of the step: the lax square.
* `zag_iff_quiet`: it lifts steps exactly when the rule set is **quiet** at the solution: every
  firing from a modelled configuration keeps the solution a model (`Quiet`).
* `diamond_at_solution_iff_quiet`: possibility pulls back from the step to the fibre, for every
  predicate, exactly for quiet rule sets.
* `ground_quiet`, `ground_diamond_eq`: over ground terms every rule set is quiet at the one
  solution, so there OSLF at the solution is OSLF of the step.
* **Control** (`TellControl.not_quiet`, `TellControl.tell_diamond_fails`): over first-order terms
  with variables, the rule that tells `X = 1` fires at the empty store, and not at the identity
  solution, which the told equation excludes. Knowledge that refines the solution away is exactly
  what the fibre cannot see.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.SolutionFibres

open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps FragmentsOfTheStep.HeatingBisimulation
open ModalComparison

universe uT uS uO

section Generic

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T) (σ : S)

/-- **The step restricted to a rule set**, at every solution. -/
def PlainStep (R : RuleSet T) (C C' : Configuration T O) : Prop :=
  ∃ rule, R rule ∧ ConstraintMultisetRewriting.Step A label rule C C'

/-- **Quiet at a solution**: every firing of the rule set from a configuration the solution models
keeps it a model. -/
def Quiet (R : RuleSet T) : Prop :=
  ∀ C C' : Configuration T O, A.Models σ C.equations → PlainStep A label R C C' →
    A.Models σ C'.equations

variable {A label σ}

/-- **The fibre's inclusion carries steps.** -/
theorem zig_val (R : RuleSet T) :
    Zig (modelledStep A label σ R) (PlainStep A label R) (fun C : Modelled A σ (O := O) => C.1) := by
  rintro C D ⟨rule, member, step, _⟩
  exact ⟨rule, member, step⟩

/-- **The fibre's inclusion lifts steps exactly for quiet rule sets.** -/
theorem zag_iff_quiet (R : RuleSet T) :
    Zag (modelledStep A label σ R) (PlainStep A label R) (fun C : Modelled A σ (O := O) => C.1) ↔
      Quiet A label σ R := by
  constructor
  · intro zag C C' modelled step
    have lift : ∀ {D : Modelled A σ (O := O)} {C'' : Configuration T O},
        PlainStep A label R D.1 C'' → ∃ D', modelledStep A label σ R D D' ∧ D'.1 = C'' := zag
    obtain ⟨D, ⟨_, _, _, solved⟩, rfl⟩ := lift (D := ⟨C, modelled⟩) step
    exact solved
  · intro quiet C C' step
    obtain ⟨rule, member, fires⟩ := step
    have kept := quiet C.1 C' C.2 ⟨rule, member, fires⟩
    exact ⟨⟨C', kept⟩, ⟨rule, member, fires, kept⟩, rfl⟩

/-- **Possibility pulls back from the step to the fibre over a solution exactly for quiet rule
sets.** -/
theorem diamond_at_solution_iff_quiet (R : RuleSet T) :
    Quiet A label σ R ↔ ∀ φ : Configuration T O → Prop,
      pb (fun C : Modelled A σ (O := O) => C.1) (derivedDiamond (span (PlainStep A label R)) φ) =
        derivedDiamond (span (modelledStep A label σ R))
          (pb (fun C : Modelled A σ (O := O) => C.1) φ) :=
  Iff.trans ⟨fun quiet => ⟨zig_val R, (zag_iff_quiet R).mpr quiet⟩,
    fun bisimulation => (zag_iff_quiet R).mp bisimulation.zag⟩ functionalBisimulation_iff_pb_diamond

end Generic

section Ground

open NamesOnTheStep NamesOnTheStep.IssuingControls

/-- **Over ground terms every rule set is quiet at the one solution.** -/
theorem ground_quiet (R : RuleSet Expr) : Quiet ground (Prod.fst : Occ → Expr) () R := by
  rintro C C' _ ⟨rule, _, selection, valid, rfl⟩
  obtain ⟨u, solved⟩ := valid.consistent
  exact solved

/-- **Over ground terms OSLF at the solution is OSLF of the step.** -/
theorem ground_diamond_eq (R : RuleSet Expr) (φ : Configuration Expr Occ → Prop) :
    pb (fun C : Modelled ground () (O := Occ) => C.1)
        (derivedDiamond (span (PlainStep ground (Prod.fst : Occ → Expr) R)) φ) =
      derivedDiamond (span (modelledStep ground (Prod.fst : Occ → Expr) () R))
        (pb (fun C : Modelled ground () (O := Occ) => C.1) φ) :=
  (diamond_at_solution_iff_quiet R).mp (ground_quiet R) φ

end Ground

/-! ## Control: a told equation refines the solution away -/

namespace TellControl

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label)
open AnnotatedRuns.RoundControls (tellOne empty)

/-- The rule set holding the rule that tells `X = 1`. -/
def tellsXOne : RuleSet (Term signature) := (· = tellOne.rule)

/-- The empty store, modelled by the identity substitution. -/
def emptyAtIdentity : Modelled A (Subst.id signature) (O := ℕ) :=
  ⟨empty, fun _ member => absurd member List.not_mem_nil⟩

/-- The rule fires at the empty store. -/
theorem tell_plain : PlainStep A label tellsXOne empty (tellOne.result label empty) :=
  ⟨tellOne.rule, rfl, tellOne.selection, AnnotatedRuns.LawfulControls.tellOne_valid.firing, rfl⟩

/-- **The rule set is not quiet at the identity.** -/
theorem not_quiet : ¬ Quiet A label (Subst.id signature) tellsXOne := by
  intro quiet
  have modelled := quiet empty _ emptyAtIdentity.2 tell_plain
  have bad := modelled (.var 0, .const 1) (by
    simp [AnnotatedRuns.Firing.result, Selection.result, Selection.problem, Selection.equations,
      tellOne, empty])
  cases bad

/-- **Possibility of the step does not pull back to the fibre over the identity.** -/
theorem tell_diamond_fails :
    pb (fun C : Modelled A (Subst.id signature) (O := ℕ) => C.1)
        (derivedDiamond (span (PlainStep A label tellsXOne)) (fun _ => True)) emptyAtIdentity ∧
      ¬ derivedDiamond (span (modelledStep A label (Subst.id signature) tellsXOne)) (fun _ => True)
        emptyAtIdentity := by
  refine ⟨(diamond_iff _ _ _).mpr ⟨_, tell_plain, trivial⟩, fun possible => ?_⟩
  obtain ⟨D, ⟨rule, member, ⟨selection, _, same⟩, solved⟩, _⟩ := (diamond_iff _ _ _).mp possible
  have isTell : rule = tellOne.rule := member
  subst isTell
  have bad := solved (.var 0, .const 1) (by
    rw [same]
    simp [Selection.result, Selection.problem, Selection.equations, tellOne, empty, emptyAtIdentity])
  cases bad

end TellControl

#print axioms zig_val
#print axioms zag_iff_quiet
#print axioms diamond_at_solution_iff_quiet
#print axioms ground_quiet
#print axioms ground_diamond_eq
#print axioms TellControl.not_quiet
#print axioms TellControl.tell_diamond_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.SolutionFibres
