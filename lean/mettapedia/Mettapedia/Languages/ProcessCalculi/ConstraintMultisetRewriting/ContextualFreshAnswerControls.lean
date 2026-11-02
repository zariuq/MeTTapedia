import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshAnswer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalChecks

/-!
# A fresh contextual answer fires an ordinary occurrence step

The selected pair unifies through its common parameter, a surviving frame
occurrence keeps its contextual declaration, and a fresh output has its own
occurrence identity. The retained principal interface includes that frame.
A guard on the unrelated frame value is not justified by solving the pair.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshAnswer.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopePullback.Controls
  (base leftMap rightMap pullback)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair.Controls (others)

abbrev context : Ctx base := [(), (), ()]
abbrev old := oldDeclarations [(), ()] [(), ()] () others
abbrev active := activeDeclarations [(), ()] [(), ()] [()] () others
abbrev A := ContextualFamilies.action active context ()
abbrev σ := answer pullback () others

def leftCall : Term (signature base active) context () :=
  instantiate (includeOld (L := [(), ()]) (R := [(), ()]) [()] () others)
    (originalLeft (left := leftMap) () others)

def rightCall : Term (signature base active) context () :=
  instantiate (includeOld (L := [(), ()]) (R := [(), ()]) [()] () others)
    (originalRight (right := rightMap) () others)

def oldFrame : Term (signature base old) context () :=
  .op (.inr (.mk (.inr 9))) (.cons (.var .zero) (.cons (.var (.succ (.succ .zero))) .nil))

def frame : Term (signature base active) context () :=
  .op (.inr (.mk (.inr (.inr 9)))) (.cons (.var .zero) (.cons (.var (.succ (.succ .zero))) .nil))

def output : Term (signature base active) context () :=
  .op (.inl .pair) (.cons leftCall (.cons rightCall .nil))

def label : Nat → Term (signature base active) context ()
  | 0 => rightCall
  | 1 => frame
  | _ => output

def initial : Configuration (Term (signature base active) context ()) Nat := ⟨[], {0, 1}⟩
def selected : Selection Nat := ⟨[0], [], [2]⟩
def rule : RuleInstance (Term (signature base active) context ()) :=
  ⟨[leftCall], [], [], [.equal leftCall rightCall], [output]⟩

theorem answer_solves_the_selected_equation :
    A.Models σ (selected.problem label rule initial) := by
  change A.Models σ [(leftCall, rightCall)]
  exact ContextualFreshAnswer.sound pullback () others

theorem ordinary_step_is_valid : selected.Valid A label rule initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨σ, answer_solves_the_selected_equation⟩, ?_⟩
  intro check member candidate solved
  change check ∈ [.equal leftCall rightCall] at member
  have same := List.mem_singleton.mp member
  subst check
  exact solved (leftCall, rightCall) (by
    change (leftCall, rightCall) ∈ [(leftCall, rightCall)]
    simp)

theorem an_ordinary_two_sided_step_fires :
    Step A label rule initial (selected.result label rule initial) :=
  ⟨selected, ordinary_step_is_valid, rfl⟩

theorem surviving_frame_is_present : 1 ∈ (selected.result label rule initial).present := by decide

theorem unrelated_contextual_frame_is_not_bound : instantiate σ frame = frame := rfl

theorem helper_is_fresh_for_the_inputs_and_frame :
    (Sum.inr (Sum.inl ()) : Bool ⊕ (Unit ⊕ Nat)) ∉ support (S := base) (source := active) leftCall ∧
      (Sum.inr (Sum.inl ()) : Bool ⊕ (Unit ⊕ Nat)) ∉ support (S := base) (source := active) rightCall ∧
        (Sum.inr (Sum.inl ()) : Bool ⊕ (Unit ⊕ Nat)) ∉ support (S := base) (source := active) frame := by
  change (Sum.inr (Sum.inl ()) : Bool ⊕ (Unit ⊕ Nat)) ∉ [Sum.inl false] ∧
    (Sum.inr (Sum.inl ()) : Bool ⊕ (Unit ⊕ Nat)) ∉ [Sum.inl true] ∧
      (Sum.inr (Sum.inl ()) : Bool ⊕ (Unit ⊕ Nat)) ∉ [Sum.inr (Sum.inr 9)]
  simp

theorem executable_support_check_accepts_the_old_frame :
    checkSupport (S := base) (source := active)
      [Sum.inl false, Sum.inl true, Sum.inr (Sum.inr 9)] frame = true := rfl

theorem principal_interface_retains_the_surviving_frame :
    A.PrincipalOn (selected.problem label rule initial) σ [leftCall, rightCall, frame] :=
  principal_on pullback () others
    [originalLeft (left := leftMap) () others, originalRight (right := rightMap) () others, oldFrame]

def constant : Term (signature base active) context () := .op (.inl .constant) .nil

def unjustifiedRule : RuleInstance (Term (signature base active) context ()) :=
  { rule with checks := [.equal frame constant] }

/-- Solving the selected pair cannot assert that an unrelated contextual
value is a constant. The explicit answer itself refutes that guard. -/
theorem a_frame_guard_cannot_be_invented : ¬ selected.Valid A label unjustifiedRule initial := by
  intro valid
  have compatible : A.Models σ (selected.problem label unjustifiedRule initial) :=
    answer_solves_the_selected_equation
  have invented := valid.checks (.equal frame constant) (by
    change Check.equal frame constant ∈ [Check.equal frame constant]
    simp) σ compatible
  change instantiate σ frame = instantiate σ constant at invented
  change Term.op (S := signature base active) (.inr (.mk (.inr (.inr 9))))
      (.cons (.var .zero) (.cons (.var (.succ (.succ .zero))) .nil)) =
    Term.op (S := signature base active) (.inl .constant) .nil at invented
  have heads := (Term.op.inj invented).1
  cases heads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshAnswer.Controls
