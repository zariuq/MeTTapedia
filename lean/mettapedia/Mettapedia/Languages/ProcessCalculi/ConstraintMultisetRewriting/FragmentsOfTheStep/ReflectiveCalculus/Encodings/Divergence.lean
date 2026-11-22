import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.FirstHalf

/-!
# Divergence both ways, with a process that diverges

Divergence reflection (`encode_divergenceReflecting`) is a statement about every process whose
translation diverges. This module shows that such processes exist, and that divergence is preserved
as well as reflected.

* **A process that diverges** (`omega_diverges`): the self-reproducing process
  `D | @0!(D)` with `D = @0(y).(@0!(*y) | *y)` communicates to itself modulo the equations
  (`omega_steps`: the communication rule makes `(@0!(D) | D)`, structurally congruent to it). Every
  name in it is a closed quote, so it lies in the sealed carrier.
* **Divergence is preserved** (`divergence_preserved`): from a state that represents a process with an
  infinite run, the step has an infinite run (each source reduction is matched by a nonempty run, and
  nonempty runs chain into an infinite one, `infinite_of_transGen`).
* **The hypothesis of divergence reflection is met** (`encode_omega_diverges`): the translation of the
  self-reproducing process diverges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction (input output)
open ByInstantiation (sig G Closed read)

/-! ## Infinite runs from nonempty runs -/

/-- **Nonempty runs chain into an infinite run.** -/
theorem infinite_of_transGen {α : Type*} {r : α → α → Prop} {f : ℕ → α}
    (steps : ∀ n, Relation.TransGen r (f n) (f (n + 1))) :
    ∃ g : ℕ → α, g 0 = f 0 ∧ ∀ n, r (g n) (g (n + 1)) := by
  classical
  let A : α → Prop := fun x => ∃ n, Relation.ReflTransGen r x (f n)
  have next : ∀ x, A x → ∃ y, r x y ∧ A y := by
    rintro x ⟨n, run⟩
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨y, step, rest⟩
    · obtain ⟨y, step, rest⟩ := Relation.TransGen.head'_iff.mp (steps n)
      exact ⟨y, step, n + 1, rest⟩
    · exact ⟨y, step, n, rest⟩
  let sequence : ℕ → {x // A x} := fun k =>
    Nat.rec (motive := fun _ => {x // A x}) ⟨f 0, 0, .refl⟩
      (fun _ x => ⟨Classical.choose (next x.1 x.2), (Classical.choose_spec (next x.1 x.2)).2⟩) k
  exact ⟨fun k => (sequence k).1, rfl, fun k => (Classical.choose_spec (next (sequence k).1 (sequence k).2)).1⟩

/-- **Divergence is preserved**: an infinite run of the source from a represented process gives an
infinite run of the step. -/
theorem divergence_preserved {s : ByInstantiation.State} {P : RhoProcess}
    (represented : ByInstantiation.Represents s P)
    (diverges : ∃ g : ℕ → RhoProcess, g 0 = P ∧ ∀ n, rhoLanguageDefGSLT.Step (g n) (g (n + 1))) :
    ∃ f : ℕ → ByInstantiation.State, f 0 = s ∧ ∀ n, Moves (f n) (f (n + 1)) := by
  classical
  obtain ⟨g, start, steps⟩ := diverges
  have next : ∀ k (t : ByInstantiation.State), ByInstantiation.Represents t (g k) →
      ∃ t', ByInstantiation.Represents t' (g (k + 1)) ∧ Relation.TransGen Moves t t' := by
    intro k t onT
    obtain ⟨t₁, t₂, admin, comm, onT₂⟩ :=
      ByInstantiation.reflective_calculus_by_instantiation.2.2.2.2.1 onT (steps k)
    exact ⟨t₂, onT₂, Relation.TransGen.tail'_iff.mpr ⟨t₁, runs_of_administrative admin,
      communicates_moves comm⟩⟩
  have initial : ByInstantiation.Represents s (g 0) := by
    rw [start]
    exact represented
  let states : (k : ℕ) → {t : ByInstantiation.State // ByInstantiation.Represents t (g k)} := fun k =>
    Nat.rec (motive := fun k => {t : ByInstantiation.State // ByInstantiation.Represents t (g k)})
      ⟨s, initial⟩
      (fun k x => ⟨Classical.choose (next k x.1 x.2), (Classical.choose_spec (next k x.1 x.2)).1⟩) k
  obtain ⟨f, first, run⟩ := infinite_of_transGen (f := fun k => (states k).1)
    (fun k => (Classical.choose_spec (next k (states k).1 (states k).2)).2)
  exact ⟨f, first, run⟩

/-! ## A process that diverges -/

/-- The channel `@0`. -/
def omegaChannel : Pattern := .apply "NQuote" [.apply "PZero" []]

/-- The continuation `@0!(*y) | *y`. -/
def omegaBody : Pattern :=
  .collection .hashBag [output omegaChannel (.apply "PDrop" [.bvar 0]), .apply "PDrop" [.bvar 0]] none

/-- `D = @0(y).(@0!(*y) | *y)`. -/
def omegaCode : Pattern := input omegaChannel omegaBody

/-- `@0!(D)`. -/
def omegaOutput : Pattern := output omegaChannel omegaCode

theorem omegaBody_typed : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
    [rhoReflectivePresentation.nameSort] omegaBody :=
  .parallel (.cons (.output (.quote .unit) (.drop (.bvar rfl))) (.cons (.drop (.bvar rfl)) .nil))

theorem omegaCode_typed : ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] omegaCode :=
  .input (.quote .unit) omegaBody_typed

/-- **The calculus's substitution regenerates the process**: `D` receiving its own code makes
`@0!(D) | D`. -/
theorem omega_substitution :
    semanticCommSubst omegaBody omegaCode = .collection .hashBag [omegaOutput, omegaCode] none := by
  decide

/-- **The self-reproducing process** `D | @0!(D)`. -/
def omega : RhoProcess :=
  ⟨.collection .hashBag [omegaCode, omegaOutput] none, (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.parallel (.cons omegaCode_typed (.cons (.output (.quote .unit) omegaCode_typed) .nil)), by decide⟩⟩

/-- Its contractum, as the communication rule writes it: `(@0!(D) | D)`, one component. -/
def omegaNext : RhoProcess :=
  ⟨.collection .hashBag [.collection .hashBag [omegaOutput, omegaCode] none] none,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel (.cons (.parallel (.cons (.output (.quote .unit) omegaCode_typed)
        (.cons omegaCode_typed .nil))) .nil), by decide⟩⟩

/-- The communication rule takes `D | @0!(D)` to its contractum. -/
theorem omega_reduces : rhoRewriteSystem.Reduces omega omegaNext := by
  have step := DerivedContextualStep.RhoStep.comm (free := FreeSortContext.empty) (bound := [])
    omegaChannel omegaBody omegaCode [] omegaBody_typed omegaCode_typed
  rw [omega_substitution] at step
  exact step

/-- **The self-reproducing process communicates to itself**, modulo the equations. -/
theorem omega_steps : rhoLanguageDefGSLT.Step omega omega := by
  refine ⟨omega, omegaNext, rfl, omega_reduces, ?_⟩
  apply (rhoProcessEquations_iff_structuralCongruence _ _).mpr
  exact StructuralCongruence.trans _ _ _ (StructuralCongruence.par_singleton _)
    (StructuralCongruence.par_comm _ _)

/-- **The self-reproducing process diverges.** -/
theorem omega_diverges (ω : G [] .nm) : (rhoCalculus ω).Diverges omega :=
  ⟨fun _ => omega, rfl, fun _ => omega_steps⟩

/-- **The hypothesis of divergence reflection is met**: the translation of the self-reproducing
process diverges. -/
theorem encode_omega_diverges (ω : G [] .nm) : (stepCalculus ω).Diverges (encode omega) :=
  divergence_preserved (encode_represents omega) ⟨fun _ => omega, rfl, fun _ => omega_steps⟩

#print axioms infinite_of_transGen
#print axioms divergence_preserved
#print axioms omega_substitution
#print axioms omega_reduces
#print axioms omega_steps
#print axioms omega_diverges
#print axioms encode_omega_diverges

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
