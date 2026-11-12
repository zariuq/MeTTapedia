import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentNarrowing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhases

/-!
# One equation with a dependent code, decided as data

`dep_settles` decides `[X ≐ t]`, `t` a dependent code, by cases. This module computes the case:
* it reads the equation (`readFlexDep`): both annotations the same universe, the left side an unknown declared at a
  universe `u`, the right side a dependent code below `u` (`depCodeB`, `depCode_of_B`);
* it checks that the unknowns of `t` are declared at universes and that no declaration mentions `X` or an unknown of
  `t`;
* `t` is `X`: deleted; `X` occurs in `t`: no solution; a head of `t` typed by a universe not below `u` (read with the
  head typings of a choice of heads, `misfitHead`): no solution; every head typed below `u` (`headsFitB`): the misfit
  unknowns are narrowed and `X := t`.

It returns the finished update or the refutation as data (`depDecide`), so it is a base decision for the phases: stores
whose equations with dependent codes are solved one after another along the telescope, together with what the other
solvers decide, are decided in phases.

The checks are complete: the code check decides dependent codes (`depCodeB_iff`), the reader reads every flex–rigid
equation with a dependent code (`readFlexDep_complete`), and the decision returns an outcome on the whole class of
`dep_settles` whose heads the choice of heads types (`depDecide_complete`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

section Codes

variable {S : Setting Head L} [DecidableRel S.R.cumulative]

/-- A domain that binds a used variable must be a universe below `u`. -/
def depBound (u : Head) {n : Nat} : Tm Head n → Bool
  | .head w => decide (S.R.cumulative w u)
  | _ => false

theorem depBound_spec {u : Head} {n : Nat} {A : Tm Head n} (h : depBound (S := S) u A = true) :
    ∃ w, A = .head w ∧ S.R.cumulative w u := by
  cases A with
  | head w => exact ⟨w, rfl, of_decide_eq_true h⟩
  | _ => simp [depBound] at h

/-- **Whether a code is a dependent code below `u`**, decided. -/
def depCodeB (u : Head) : {n : Nat} → Tm Head n → Bool
  | _, .var _ => true
  | _, .head _ => true
  | _, .pi A B => depCodeB u A && depCodeB u B && (!decide (0 ∈ B.support) || depBound (S := S) u A)
  | _, _ => false

theorem depCode_of_B {u : Head} : ∀ {n : Nat} {t : Tm Head n}, depCodeB (S := S) u t = true → DepCode S.R u t
  | _, .var Y, _ => .var Y
  | _, .head h, _ => .head h
  | _, .pi A B, h => by
      simp only [depCodeB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not] at h
      obtain ⟨⟨hA, hB⟩, bound⟩ := h
      refine .pi (depCode_of_B hA) (depCode_of_B hB) fun used => ?_
      rcases bound with unused | fits
      · exact absurd used unused
      · exact depBound_spec fits
  | _, .const _, h => by simp [depCodeB] at h
  | _, .sigma _ _, h => by simp [depCodeB] at h
  | _, .id _ _ _, h => by simp [depCodeB] at h
  | _, .lam _, h => by simp [depCodeB] at h
  | _, .app _ _, h => by simp [depCodeB] at h
  | _, .pair _ _, h => by simp [depCodeB] at h
  | _, .fst _, h => by simp [depCodeB] at h
  | _, .snd _, h => by simp [depCodeB] at h
  | _, .refl _, h => by simp [depCodeB] at h

/-- **The check is complete**: every dependent code below `u` passes it. -/
theorem depCodeB_of {u : Head} {n : Nat} {t : Tm Head n} (code : DepCode S.R u t) : depCodeB (S := S) u t = true := by
  induction code with
  | var Y => rfl
  | head h => rfl
  | @pi n A B _ _ bound ihA ihB =>
      simp only [depCodeB, ihA, ihB, Bool.true_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not]
      by_cases used : (0 : Fin (n + 1)) ∈ B.support
      · obtain ⟨w, rfl, below⟩ := bound used
        exact .inr (decide_eq_true below)
      · exact .inl used

/-- **Whether a code is a dependent code below `u` is decided.** -/
theorem depCodeB_iff {u : Head} {n : Nat} {t : Tm Head n} : depCodeB (S := S) u t = true ↔ DepCode S.R u t :=
  ⟨depCode_of_B, depCodeB_of⟩

end Codes

section Reader

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

/-- **Read a flex–rigid equation with a dependent code.** -/
def readFlexDep {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (FlexDep (S := S) e) :=
  match hl : e.1.1.code, hr : e.2.1.code, hs : e.1.2.code with
  | .head v, .head v', .var X =>
      if hv : v' = v then
        match hd : Ctx.lookup Θ.raw X with
        | .head u =>
            if hu : S.R.isUniverse u ∧ S.R.isUniverse v ∧ depCodeB (S := S) u e.2.2.code = true then
              some ⟨v, X, u, hl, hv ▸ hr, hs, hd, hu.1, hu.2.1, depCode_of_B hu.2.2⟩
            else none
        | _ => none
      else none
  | _, _, _ => none

/-- **The reader is complete**: it reads every flex–rigid equation with a dependent code. -/
theorem readFlexDep_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep (S := S) e) :
    (readFlexDep (S := S) e).isSome = true := by
  unfold readFlexDep
  split
  · rename_i a b X hl hr hs
    have ha : a = v.v := by
      have := hl.symm.trans v.annotation_left
      exact Tm.head.inj this
    have hb : b = v.v := by
      have := hr.symm.trans v.annotation_right
      exact Tm.head.inj this
    have hX : X = v.X := by
      have := hs.symm.trans v.side_left
      exact Tm.var.inj this
    subst ha hb hX
    rw [dif_pos rfl]
    split
    · rename_i u hd
      have hu : u = v.u := by
        have := hd.symm.trans v.declared
        exact Tm.head.inj this
      subst hu
      rw [dif_pos ⟨v.universe_u, v.universe_v, depCodeB_of v.code⟩]
      rfl
    · rename_i notHead
      exact absurd v.declared (notHead v.u)
  · rename_i notFlex
    exact absurd v.side_left (notFlex v.v v.v v.X v.annotation_left v.annotation_right)

end Reader

section Heads

variable {S : Setting Head L} [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- Whether every head is typed, by the choice of heads, by a universe below `u`. -/
def headsFitB (u : Head) (hs : List Head) : Bool :=
  hs.all fun h => match choices.typing h with
    | some k => decide (S.R.cumulative k.val u)
    | none => false

theorem headsFit_of_B {u : Head} {hs : List Head} (fit : headsFitB choices u hs = true) :
    ∀ h ∈ hs, ∃ k, S.R.headTyping h k ∧ S.R.cumulative k u := by
  intro h member
  have one := List.all_eq_true.mp fit h member
  revert one
  cases typed : choices.typing h with
  | none => simp
  | some k => exact fun below => ⟨k.val, k.property, of_decide_eq_true below⟩

/-- A head typed, by the choice of heads, by a universe not below `u`. -/
def misfitHead (u : Head) (hs : List Head) : Option Head :=
  hs.find? fun h => match choices.typing h with
    | some k => !decide (S.R.cumulative k.val u)
    | none => false

include headTypingUnique in
theorem misfitHead_spec {u h₀ : Head} {hs : List Head} (found : misfitHead choices u hs = some h₀) :
    h₀ ∈ hs ∧ ∀ k, S.R.headTyping h₀ k → ¬ S.R.cumulative k u := by
  refine ⟨List.mem_of_find?_eq_some found, fun k typing below => ?_⟩
  have holds := List.find?_some found
  revert holds
  cases typed : choices.typing h₀ with
  | none => simp
  | some k' =>
      intro notBelow
      have same : k'.val = k := headTypingUnique k'.property typing
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at notBelow
      exact notBelow (same ▸ below)

/-- When every head is typed by the choice and none is a misfit, every head fits. -/
theorem headsFitB_of_none {u : Head} {hs : List Head} (typed : ∀ h ∈ hs, (choices.typing h).isSome = true)
    (noMisfit : misfitHead choices u hs = none) : headsFitB choices u hs = true := by
  unfold misfitHead at noMisfit
  unfold headsFitB
  rw [List.all_eq_true]
  intro h member
  have notMisfit := List.find?_eq_none.mp noMisfit h member
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (typed h member)
  rw [hk] at notMisfit ⊢
  simpa using notMisfit

end Heads

section Decide

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

/-- **One equation with a dependent code, decided as data**: deleted, refuted by the occurs check or a misfit head, or
solved by narrowing; nothing when the equation is not read or a condition fails. -/
def depDecide {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (Decided [e]) :=
  match readFlexDep (S := S) e with
  | none => none
  | some v =>
      if occurring : atUniversesB (S := S) Θ.raw e.2.2.code = true then
        if apart : ∀ i, ∀ j ∈ (Ctx.lookup Θ.raw i).support, j ≠ v.X ∧ j ∉ e.2.2.code.support then
          if same : e.2.2.code = .var v.X then
            some (.solved (deleteCodes e (v.annotation_left.trans v.annotation_right.symm)
              (v.side_left.trans same.symm) []) rfl)
          else if occurs : v.X ∈ e.2.2.code.support then
            some (.refuted (dep_occurs_refutes facts roots heads algebra rigid complete v occurs same []))
          else
            match found : misfitHead choices v.u (codHeads e.2.2.code) with
            | some _ =>
                some (.refuted (dep_misfitHead_refutes facts roots heads algebra rigid complete v
                  (misfitHead_spec choices headTypingUnique found).1
                  (misfitHead_spec choices headTypingUnique found).2 []))
            | none =>
                if fit : headsFitB choices v.u (codHeads e.2.2.code) = true then
                  some (.solved (depNarrowSolveUpdate glb spec facts roots heads algebra rigid complete
                    headTypingUnique declared v
                    { absent := occurs
                      heads := headsFit_of_B choices fit
                      occurring := atUniverses_of_B occurring
                      apart := apart
                      meets := fun i misfit w hw => by
                        obtain ⟨w', hw', uw'⟩ := atUniverses_of_B occurring i (codMisfit_mem misfit)
                        rw [hw] at hw'
                        cases hw'
                        exact total v.universe_u uw' } []) rfl)
                else none
        else none
      else none

/-- **The decision is complete on the class of `dep_settles`**: for a flex–rigid equation with a dependent code whose
unknowns are declared at universes, with no declaration mentioning `X` or an unknown of `t`, and whose heads the choice
of heads types, it returns a finished update or a refutation. -/
theorem depDecide_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep (S := S) e)
    (occurring : AtUniverses (S := S) Θ.raw e.2.2.code)
    (apart : ∀ i, ∀ j ∈ (Ctx.lookup Θ.raw i).support, j ≠ v.X ∧ j ∉ e.2.2.code.support)
    (typed : ∀ h ∈ codHeads e.2.2.code, (choices.typing h).isSome = true) :
    (depDecide choices facts roots heads algebra rigid complete glb spec headTypingUnique declared total e).isSome =
      true := by
  obtain ⟨v', read⟩ := Option.isSome_iff_exists.mp (readFlexDep_complete v)
  have sameX : v'.X = v.X := Tm.var.inj (v'.side_left.symm.trans v.side_left)
  have apart' : ∀ i, ∀ j ∈ (Ctx.lookup Θ.raw i).support, j ≠ v'.X ∧ j ∉ e.2.2.code.support := by
    rw [sameX]
    exact apart
  unfold depDecide
  rw [read]
  dsimp only
  rw [dif_pos (atUniversesB_of occurring), dif_pos apart']
  by_cases same : e.2.2.code = .var v'.X
  · rw [dif_pos same]
    rfl
  rw [dif_neg same]
  by_cases occurs : v'.X ∈ e.2.2.code.support
  · rw [dif_pos occurs]
    rfl
  rw [dif_neg occurs]
  split
  · rfl
  · rename_i noMisfit
    rw [dif_pos (headsFitB_of_none choices typed noMisfit)]
    rfl

/-- **The base decision of one-equation stores with a dependent code.** -/
def depBase {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Decided problem) :=
  match problem with
  | [e] => depDecide choices facts roots heads algebra rigid complete glb spec headTypingUnique declared total e
  | _ => none

end Decide

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
