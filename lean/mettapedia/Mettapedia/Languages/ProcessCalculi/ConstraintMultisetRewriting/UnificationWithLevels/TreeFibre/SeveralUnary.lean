import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralGroups

/-!
# One parameter inside several: the unary fragments are decided by the solver with several parameters

* `FitFlex.toK`, `compatK_of_compat`: a unary view and a unary compatibility are the ones with one parameter.
* **The unary fragment of meet groups lies inside** (`inMeetFragmentK_of_meet`), hence so does the fragment of fitting
  groups (`inMeetFragmentK_of_fit`). A declaration of several parameters that occurs in no equation of a unary
  store is put in a group of its own.
* So the solver with several parameters decides every store of the unary fragments (`meetGroupK_decides_unary`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A unary view is a view with one parameter.** -/
def FitFlex.toK {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) : FlexK e where
  ps := [v.p]
  q := v.q
  left := v.left
  right := v.right
  psl := [v.pl]
  cl := v.cl
  psr := [v.pr]
  cr := v.cr
  annotation_left := v.annotation_left
  annotation_right := v.annotation_right
  side_left := v.side_left
  side_right := v.side_right
  declared_left := v.declared_left
  declared_right := v.declared_right
  universes := fun _ member => (List.mem_singleton.mp member) ▸ v.universe_p
  universes_left := fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pl
  universes_right := fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pr
  universe_q := v.universe_q
  universe_cl := v.universe_cl
  universe_cr := v.universe_cr
  domain_left := .cons v.domain_left .nil
  domain_right := .cons v.domain_right .nil
  codomain_left := v.codomain_left
  codomain_right := v.codomain_right

/-- **A unary compatibility is a compatibility with one parameter.** -/
theorem compatK_of_compat {R : Rules Head} {p c p' c' : Head} (h : Compat R p c p' c') :
    CompatK R [p] c [p'] c' := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩
  · exact .inl ⟨.cons a .nil, b⟩
  · exact .inr (.inl ⟨.cons a .nil, b⟩)
  · exact .inr (.inr (.inl ⟨.cons a .nil, b, fun _ member => (List.mem_singleton.mp member) ▸ d⟩))
  · exact .inr (.inr (.inr ⟨.cons a .nil, b, fun _ member => (List.mem_singleton.mp member) ▸ d⟩))

variable [DecidableEq Head]

/-- Whether a declaration is a unary universe family, read off its code. -/
def isUnary {n : Nat} (Γ : Ctx Head n) (i : Fin n) : Bool :=
  match readFam (Ctx.lookup Γ i) with
  | some ([_], _) => true
  | _ => false

theorem isUnary_of {n : Nat} {Γ : Ctx Head n} {i : Fin n} {p c : Head} (declared : Ctx.lookup Γ i = famCode [p] c) :
    isUnary Γ i = true := by
  unfold isUnary
  rw [declared, readFam_famCode]

theorem unary_shape {n : Nat} {Γ : Ctx Head n} {i : Fin n} {ps : List Head} {c : Head}
    (declared : Ctx.lookup Γ i = famCode ps c) (unary : isUnary Γ i = true) : ∃ p, ps = [p] := by
  unfold isUnary at unary
  rw [declared, readFam_famCode] at unary
  match ps, unary with
  | [p], _ => exact ⟨p, rfl⟩

/-- The grouping that keeps every declaration that is not unary apart. -/
def apartGroup {n : Nat} (Γ : Ctx Head n) (group : Fin n → Nat) (i : Fin n) : Nat :=
  if isUnary Γ i = true then 2 * group i else 2 * i.val + 1

/-- **The unary fragment of meet groups lies inside the fragment with several parameters.** -/
theorem inMeetFragmentK_of_meet {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragment problem) : InMeetFragmentK problem := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  have unaryOf : ∀ e ∈ problem, ∀ v : FitFlex e, isUnary Θ.raw v.left = true ∧ isUnary Θ.raw v.right = true :=
    fun _ _ v => ⟨isUnary_of v.declared_left, isUnary_of v.declared_right⟩
  refine ⟨inside.families, fun e member => ?_, ⟨apartGroup Θ.raw group, fun e member u => ?_, ?_⟩⟩
  · obtain ⟨v⟩ := inside.shapes e member
    exact ⟨v.toK⟩
  · obtain ⟨v⟩ := inside.shapes e member
    obtain ⟨hl, hr⟩ := FlexK.unique u v.toK
    obtain ⟨ul, ur⟩ := unaryOf e member v
    unfold apartGroup
    rw [hl, hr]
    change (if isUnary Θ.raw v.left = true then 2 * group v.left else 2 * v.left.val + 1) =
      (if isUnary Θ.raw v.right = true then 2 * group v.right else 2 * v.right.val + 1)
    rw [if_pos ul, if_pos ur, grouped e member v]
  · intro i j ne same psi ci psj cj di dj
    unfold apartGroup at same
    by_cases ui : isUnary Θ.raw i = true <;> by_cases uj : isUnary Θ.raw j = true
    · rw [if_pos ui, if_pos uj] at same
      obtain ⟨pi, rfl⟩ := unary_shape di ui
      obtain ⟨pj, rfl⟩ := unary_shape dj uj
      exact compatK_of_compat (comparable i j ne (by omega) pi ci pj cj di dj)
    · rw [if_pos ui, if_neg uj] at same
      omega
    · rw [if_neg ui, if_pos uj] at same
      omega
    · rw [if_neg ui, if_neg uj] at same
      exact absurd (Fin.ext (by omega)) ne

/-- **The fragment of fitting groups lies inside the fragment with several parameters.** -/
theorem inMeetFragmentK_of_fit {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InFitFragment problem) : InMeetFragmentK problem :=
  inMeetFragmentK_of_meet (inMeetFragment_of_fit inside)

variable [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **One solver for all**: the solver with several parameters decides every store of the unary fragment of meet
groups, at some budget and every larger one, with a principal answer. -/
theorem meetGroupK_decides_unary {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragment original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (meetGroupSolverK facts roots heads algebra rigid complete) original larger =
          run (meetGroupSolverK facts roots heads algebra rigid complete) original fuel ∧
        ((∃ state finished, run (meetGroupSolverK facts roots heads algebra rigid complete) original larger =
              .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent, run (meetGroupSolverK facts roots heads algebra rigid complete) original larger =
            .refuted absent)) :=
  meetGroupK_decided facts roots heads algebra rigid complete (inMeetFragmentK_of_meet inside)

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
