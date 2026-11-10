import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionObserver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionFinite

/-!
# MeTTaDinC machine operations as transform firings

A table operation consumes the current state occurrence and produces its
successor at a fresh occurrence identity. The clock is administrative; public
queries read the machine state. Admission and the labelled transitions agree
in both directions with the successor table. No choice of successor is made
by the compilation.

This is a semantic lowering of elaborated tables. It is not a parser for the
MeTTaDinC surface language or an implementation in the C kernel.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite
open Interface
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uS uA uV
variable {S : Type uS} {A : Type uA} {V : Type uV}

/-- Closed machine data: substitution does not change an already specified value. -/
def closedFrames (S : Type uS) : Frames (fun _ : Unit => S) (fun _ _ : Unit => Unit) where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act _ t := t
  id _ := ()
  comp _ _ := ()
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro a b σ s t same; exact same

namespace Machine
variable (M : Machine S A V)

def selection (s : Nat × S) : Selection Nat := ⟨[s.1], [], [s.1 + 1]⟩

theorem enabled (s : Nat × S) :
    Enabled (fun _ : Nat => ()) {s.1} ((selection s).commit (T := Unit)) := by
  constructor <;> simp [selection, Selection.commit]

/-- The actual transform instance of the table machine. -/
def step : Interface.Step.Standard (closedFrames S) Nat (Nat × S) (fun _ => A × S) where
  frame _ := ()
  knowledge _ := []
  present s := {s.1}
  selection {s} _ := selection s
  target _ := ()
  extension _ := ()
  information _ := []
  transported _ _ member := False.elim (List.not_mem_nil member)
  Shapes {s} f := f.2 ∈ M.next s.2 f.1
  Holds _ b σ := (closedFrames S).Models (a := ()) (b := b) σ []
  Admits {s} f := f.2 ∈ M.next s.2 f.1
  admits_iff {s} f := ⟨fun h => ⟨h, enabled s, ⟨(), (), Frames.models_nil _⟩,
    fun b σ _ => Frames.models_nil (X := closedFrames S) (a := ()) (b := b) σ⟩,
    fun h => h.1⟩
  preparedResult {s} f _ := (s.1 + 1, f.2)
  present_preparedResult _ _ := by simp [selection, Selection.commit, fire]
  preparedSettle _ _ := ()
  knowledge_preparedResult _ _ := rfl

def offers (label : A) (_ : Nat × S) (f : A × S) : Prop := f.1 = label

theorem admits_iff (s : Nat × S) (f : A × S) :
    M.step.toStep.Admits (s := s) f ↔ f.2 ∈ M.next s.2 f.1 := Iff.rfl

/-- Preservation and reflection: a labelled firing is exactly one table successor. -/
theorem moves_iff (s t : Nat × S) (label : A) :
    Race.Generic.Moves M.step.toStep offers s label t ↔
      t.1 = s.1 + 1 ∧ t.2 ∈ M.next s.2 label := by
  constructor
  · rintro ⟨⟨a, target⟩, admitted, offered, rfl⟩
    change a = label at offered
    subst a
    exact ⟨rfl, admitted⟩
  · rintro ⟨clock, member⟩
    exact ⟨(label, t.2), member, rfl, Prod.ext clock rfl⟩

theorem no_extra_successor (s : Nat × S) (label : A) (t : Nat × S)
    (move : Race.Generic.Moves M.step.toStep offers s label t) : t.2 ∈ M.next s.2 label :=
  (M.moves_iff s t label).mp move |>.2

theorem every_successor_fires (s : Nat × S) (label : A) (t : S) (member : t ∈ M.next s.2 label) :
    Race.Generic.Moves M.step.toStep offers s label (s.1 + 1, t) :=
  (M.moves_iff _ _ _).mpr ⟨rfl, member⟩

def ExactEncoding {Q : Type*} (encode : S → Q) : Prop :=
  (∀ s t, encode s = encode t → M.read s = M.read t) ∧
    ∀ s t, encode s = encode t → ∀ a s', s' ∈ M.next s a →
      ∃ t' ∈ M.next t a, encode s' = encode t'

/-- The finite-machine obligation is precisely the generic transform-observer obligation. -/
theorem exactEncoding_iff_transform {Q : Type*} (encode : S → Q) :
    M.ExactEncoding encode ↔
      DistinctionObserver.Stable M.step.toStep offers (fun s => encode s.2) ∧
      DistinctionObserver.Reads (fun s : Nat × S => encode s.2) (fun s => M.read s.2) := by
  rw [DistinctionObserver.stable_iff_matching]
  constructor
  · rintro ⟨reads, matchMoves⟩
    refine ⟨?_, fun s t equal => reads s.2 t.2 equal⟩
    intro s t equal label s' move
    obtain ⟨t', member, same⟩ := matchMoves s.2 t.2 equal label s'.2 (M.no_extra_successor _ _ _ move)
    exact ⟨(t.1 + 1, t'), M.every_successor_fires t label t' member, same⟩
  · rintro ⟨matchMoves, reads⟩
    refine ⟨fun s t equal => reads (0, s) (0, t) equal, ?_⟩
    intro s t equal label s' member
    obtain ⟨t', move, same⟩ := matchMoves (0, s) (0, t) equal label (1, s')
      (M.every_successor_fires (0, s) label s' member)
    exact ⟨t'.2, M.no_extra_successor _ _ _ move, same⟩

section Check
variable [DecidableEq S] [Fintype S] [Fintype A] [DecidableEq V]

theorem checkEncoding_exact {Q : Type*} [DecidableEq Q] (encode : S → Q) :
    M.checkEncoding encode = true ↔ M.ExactEncoding encode := by
  rw [checkEncoding, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun s t eqn => (h s t eqn).1, ?_⟩
    intro s t eqn a s' member
    obtain ⟨t', member', related⟩ := (h s t eqn).2 a |>.1 s' member
    exact ⟨t', member', (Finset.mem_filter.mp related).2⟩
  · rintro ⟨reads, matchMoves⟩ s t eqn
    refine ⟨reads s t eqn, fun a => ⟨?_, ?_⟩⟩
    · intro s' member
      obtain ⟨t', member', same⟩ := matchMoves s t eqn a s' member
      exact ⟨t', member', Finset.mem_filter.mpr ⟨Finset.mem_univ _, same⟩⟩
    · intro t' member
      obtain ⟨s', member', same⟩ := matchMoves t s eqn.symm a t' member
      exact ⟨s', member', Finset.mem_image.mpr
        ⟨(s', t'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, same.symm⟩, rfl⟩⟩

/-- A checked encoding preserves every modal experiment on the compiled transform program. -/
theorem checked_preserves_modal {Q : Type*} [DecidableEq Q] (encode : S → Q)
    (checked : M.checkEncoding encode = true) {s t : Nat × S} (same : encode s.2 = encode t.2)
    (formula : Mettapedia.GSLT.HennessyMilner.Formula V A) :
    (DistinctionObserver.observed M.step.toStep offers (fun s => M.read s.2)).sat formula s ↔
      (DistinctionObserver.observed M.step.toStep offers (fun s => M.read s.2)).sat formula t :=
  DistinctionObserver.exact_preserves_modal M.step.toStep offers _ _
    ((M.exactEncoding_iff_transform encode).mp ((M.checkEncoding_exact encode).mp checked)) same formula

end Check
end Machine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite
