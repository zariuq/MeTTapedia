import Mettapedia.Logic.LP.RigidUnification
import Mettapedia.Logic.LP.IndependentOutputUnification

/-!
# Sequential constraints under retained variable permissions

The second stage receives both the first stage's substitution and the original
protection environment. This is the sequential form of one joint solve. Fresh
independent matching attempts do not satisfy this contract.
-/

namespace Mettapedia.Logic.LP.RigidUnification

universe u v
variable {σ : LPSignature.{u, u, v, u}}

theorem Fixes.comp {rigid : σ.vars → Prop} {first second : Subst σ}
    (hf : Fixes rigid first) (hs : Fixes rigid second) :
    Fixes rigid (first ∘ₛ second) := by
  intro name held
  simp only [Subst.comp, hs name held, Subst.applyTerm_var, hf name held]

def sequential (rigid : σ.vars → Prop) [DecidablePred rigid] [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (first second : List (Term σ × Term σ)) : Option (Subst σ) :=
  (solve rigid first).bind fun initial =>
    (solve rigid (initial.applyEqs second)).map fun final => final ∘ₛ initial

theorem sequential_sound (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (first second : List (Term σ × Term σ)) (answer : Subst σ)
    (accepted : sequential rigid first second = some answer) :
    Fixes rigid answer ∧ Unifies answer (first ++ second) := by
  unfold sequential at accepted
  cases left : solve rigid first with
  | none => simp [left] at accepted
  | some initial =>
    cases right : solve rigid (initial.applyEqs second) with
    | none => simp [left, right] at accepted
    | some final =>
      simp only [left, right, Option.bind_some, Option.map_some,
        Option.some.injEq] at accepted
      subst answer
      obtain ⟨initialFixed, initialSolves⟩ := solve_sound rigid first initial left
      obtain ⟨finalFixed, finalSolves⟩ := solve_sound rigid _ final right
      refine ⟨finalFixed.comp initialFixed, ?_⟩
      intro pair member
      rcases List.mem_append.mp member with inFirst | inSecond
      · exact IndependentOutputUnification.unifies_refinement first initial final
          initialSolves pair inFirst
      · exact (IndependentOutputUnification.unifies_applyEqs initial final second).mp
          finalSolves pair inSecond

theorem sequential_complete (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (first second : List (Term σ × Term σ)) (candidate : Subst σ)
    (fixed : Fixes rigid candidate) (solves : Unifies candidate (first ++ second)) :
    ∃ answer, sequential rigid first second = some answer := by
  have firstSolves : Unifies candidate first :=
    fun pair member => solves pair (List.mem_append_left second member)
  obtain ⟨initial, left⟩ := solve_complete rigid first ⟨candidate, fixed, firstSolves⟩
  obtain ⟨middle, middleFixed, factors⟩ :=
    solve_mgu rigid first initial candidate left fixed firstSolves
  have remaining : Unifies middle (initial.applyEqs second) := by
    apply (IndependentOutputUnification.unifies_applyEqs initial middle second).mpr
    rw [← factors]
    exact fun pair member => solves pair (List.mem_append_right first member)
  obtain ⟨final, right⟩ := solve_complete rigid _ ⟨middle, middleFixed, remaining⟩
  exact ⟨final ∘ₛ initial, by simp [sequential, left, right]⟩

theorem sequential_mgu (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (first second : List (Term σ × Term σ)) (answer candidate : Subst σ)
    (accepted : sequential rigid first second = some answer)
    (fixed : Fixes rigid candidate) (solves : Unifies candidate (first ++ second)) :
    ∃ factor, Fixes rigid factor ∧ candidate = factor ∘ₛ answer := by
  unfold sequential at accepted
  cases left : solve rigid first with
  | none => simp [left] at accepted
  | some initial =>
    cases right : solve rigid (initial.applyEqs second) with
    | none => simp [left, right] at accepted
    | some final =>
      simp only [left, right, Option.bind_some, Option.map_some,
        Option.some.injEq] at accepted
      subst answer
      obtain ⟨middle, middleFixed, factors⟩ := solve_mgu rigid first initial candidate
        left fixed (fun pair member => solves pair (List.mem_append_left second member))
      have remaining : Unifies middle (initial.applyEqs second) := by
        apply (IndependentOutputUnification.unifies_applyEqs initial middle second).mpr
        rw [← factors]
        exact fun pair member => solves pair (List.mem_append_right first member)
      obtain ⟨later, laterFixed, restFactors⟩ :=
        solve_mgu rigid _ final middle right middleFixed remaining
      exact ⟨later, laterFixed, by rw [factors, restFactors, Subst.comp_assoc]⟩

/-- All permitted refinements of an answer projected onto caller observations. -/
def refinements (rigid : σ.vars → Prop) (answer : Subst σ)
    (observations : List (Term σ)) : Set (List (Term σ)) :=
  { values | ∃ later : Subst σ, Fixes rigid later ∧
      values = observations.map (later ∘ₛ answer).applyTerm }

/-- Independent specification using every permitted solution. -/
def solutions (rigid : σ.vars → Prop) (equations : List (Term σ × Term σ))
    (observations : List (Term σ)) : Set (List (Term σ)) :=
  { values | ∃ candidate : Subst σ, Fixes rigid candidate ∧ Unifies candidate equations ∧
      values = observations.map candidate.applyTerm }

theorem mgu_refinements_exact (rigid : σ.vars → Prop)
    (equations : List (Term σ × Term σ)) (answer : Subst σ)
    (fixed : Fixes rigid answer) (sound : Unifies answer equations)
    (general : ∀ candidate, Fixes rigid candidate → Unifies candidate equations →
      ∃ factor, Fixes rigid factor ∧ candidate = factor ∘ₛ answer)
    (observations : List (Term σ)) :
    refinements rigid answer observations = solutions rigid equations observations := by
  ext values
  constructor
  · rintro ⟨later, laterFixed, rfl⟩
    exact ⟨later ∘ₛ answer, laterFixed.comp fixed,
      IndependentOutputUnification.unifies_refinement equations answer later sound, rfl⟩
  · rintro ⟨candidate, candidateFixed, solves, rfl⟩
    obtain ⟨later, laterFixed, factors⟩ := general candidate candidateFixed solves
    exact ⟨later, laterFixed, by rw [factors]⟩

/-- Chosen variable orientations may differ; every observable permitted
    refinement agrees between sequential and joint constraint solving. -/
theorem sequential_joint_observations (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (first second : List (Term σ × Term σ)) (sequentialAnswer jointAnswer : Subst σ)
    (hs : sequential rigid first second = some sequentialAnswer)
    (hj : solve rigid (first ++ second) = some jointAnswer)
    (observations : List (Term σ)) :
    refinements rigid sequentialAnswer observations =
      refinements rigid jointAnswer observations := by
  obtain ⟨sf, ss⟩ := sequential_sound rigid first second sequentialAnswer hs
  obtain ⟨jf, js⟩ := solve_sound rigid (first ++ second) jointAnswer hj
  rw [mgu_refinements_exact rigid (first ++ second) sequentialAnswer sf ss
      (fun c cf cs => sequential_mgu rigid first second sequentialAnswer c hs cf cs),
    mgu_refinements_exact rigid (first ++ second) jointAnswer jf js
      (fun c cf cs => solve_mgu rigid (first ++ second) jointAnswer c hj cf cs)]

theorem sequential_joint_success (rigid : σ.vars → Prop) [DecidablePred rigid]
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (first second : List (Term σ × Term σ)) :
    (∃ answer, sequential rigid first second = some answer) ↔
      ∃ answer, solve rigid (first ++ second) = some answer := by
  constructor
  · rintro ⟨answer, accepted⟩
    exact solve_complete rigid _ ⟨answer, sequential_sound rigid first second answer accepted⟩
  · rintro ⟨answer, accepted⟩
    obtain ⟨fixed, solves⟩ := solve_sound rigid _ answer accepted
    exact sequential_complete rigid first second answer fixed solves

end Mettapedia.Logic.LP.RigidUnification
