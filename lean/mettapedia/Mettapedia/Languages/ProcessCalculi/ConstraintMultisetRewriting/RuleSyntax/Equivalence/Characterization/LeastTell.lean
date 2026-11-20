import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Labels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Absorption

/-!
# A positive program with no least enabling tell

The statement that fails for the none-guarded spawn (`no_least_enabling_tell`: no enabling tell
context is entailed by every enabling one) fails in the same form for a positive program with two
rules, at the same row.

The program: "read a row, check that it is `5`, make `7`" and "read a row, check that it is `6`,
make `7`". At one row labelled by the free unknown `x`:

* the tell `x = 5` enables it, and so does the tell `x = 6` (`enablesEither_five`,
  `enablesEither_six`);
* every enabling tell entails `x = 5` or entails `x = 6` (`entails_of_enablesEither`);
* hence no enabling tell is entailed by every enabling one (`no_least_enabling_tell_positive`).

Both rules are positive (`either_positive`): their checks are equations and they have no collect query. The
obstruction here is the choice between two firings, not none queries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.LeastTell

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves rowX)

/-- Read a row, check that it is `6`, make `7`. -/
def readSix : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [], [.equal x (c 6)], [c 7]⟩, []⟩

/-- The tell context `L` enables the read guarded by `6`, at the row `x`. -/
def EnablesSix (L : EquationStore (Term atoms)) : Prop := Moves ⟨{readSix}, tellState rowX L⟩

theorem enablesSix_six : EnablesSix [(x, c 6)] := by
  let s := tellState rowX [(x, c 6)]
  let f : Firing ℕ E ({readSix} : Program Tm) s.frame :=
    ⟨readSix, Set.mem_singleton _, PUnit.unit, fun v => .var (8 + v), ⟨[], [0], [1]⟩, []⟩
  have info : f.information X s = [(x, c 6), (.var 8, x)] := rfl
  have admitted : f.Admits X s := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
      ?_, ?_, fun q inside => absurd inside List.not_mem_nil⟩
    · refine fresh_shift f (N := 8) (fun t mentioned => ?_) fun v => rfl
      rcases mentioned with inside | inside | ⟨o, -, rfl⟩
      · have isX : t = x := by simpa [s, tellState, rowX] using inside
        subst isX
        decide
      · have isSix : t = c 6 := by simpa [s, tellState, rowX] using inside
        subst isSix
        decide
      · show size x ≤ 8
        decide
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, s, Selection.commit, tellState, rowX]
      · simp [f, Selection.commit]
      · simp [f, s, Selection.commit, tellState, rowX]
      · intro q inside
        simp [f, Selection.commit] at inside
    · rw [info]
      refine ⟨PUnit.unit, fun _ => c 6, fun e inside => ?_⟩
      rcases List.mem_cons.mp inside with same | inside
      · subst same
        rfl
      · rw [List.mem_singleton] at inside
        subst inside
        rfl
    · intro check inside b τ solved
      rw [info] at solved
      have isEqual : check = .equal (.var 8) (c 6) := List.mem_singleton.mp inside
      subst isEqual
      have six : Subst.applyTerm τ x = Subst.applyTerm τ (c 6) := solved (x, c 6) (by simp)
      have read : Subst.applyTerm τ (.var 8) = Subst.applyTerm τ x := solved (.var 8, x) (by simp)
      show Subst.applyTerm τ (.var 8) = Subst.applyTerm τ (c 6)
      rw [read, six]
  exact ⟨_, reduces_of_admits f admitted⟩

/-- Every tell context that enables the read guarded by `6` entails `x = 6`. -/
theorem models_six_of_enablesSix {L : EquationStore (Term atoms)} (enables : EnablesSix L)
    (σ : Subst atoms) (solves : X.Models (a := PUnit.unit) (b := PUnit.unit) σ L) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) σ [(x, c 6)] := by
  obtain ⟨T, -, ⟨rule, member, ext, ι, ⟨taken, read, made⟩, seen⟩, admitted, -⟩ := enables
  have isRule : rule = readSix := member
  subst isRule
  obtain ⟨fresh, ⟨-, -, -, readLength, -, -⟩, -, -, checks, -⟩ := (admits_iff _).mp admitted
  obtain ⟨o, rest, rfl⟩ : ∃ o rest, read = o :: rest := by
    cases read with
    | nil => exact absurd readLength (by simp [readSix])
    | cons o rest => exact ⟨o, rest, rfl⟩
  obtain ⟨u, onState, onRule⟩ := fresh PUnit.unit σ (fun _ => Subst.applyTerm σ x)
  have onState' : ∀ t, (tellState rowX L).Mentions t →
      Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) t) = Subst.applyTerm σ t := onState
  have uX : Subst.applyTerm u x = Subst.applyTerm σ x := by
    have mentioned := onState' x (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩))
    rwa [Subst.applyTerm_id] at mentioned
  have uRead : Subst.applyTerm u (Subst.applyTerm ι x) = Subst.applyTerm σ x :=
    onRule x (by simp [readSix, Rule.terms])
  have uSolves : ∀ e ∈ (⟨readSix, member, ext, ι, ⟨taken, o :: rest, made⟩, seen⟩ :
      Firing ℕ E ({readSix} : Program Tm) (tellState rowX L).frame).information X (tellState rowX L),
      Subst.applyTerm u e.1 = Subst.applyTerm u e.2 := by
    intro e inside
    have unfolded : e ∈ X.applyStore (a := PUnit.unit) (b := PUnit.unit) (E.weaken ext)
        (tellState rowX L).knowledge ++ [] ++
        [(Subst.applyTerm ι x, Subst.applyTerm (Subst.id atoms) x)] ++ [] := inside
    simp only [List.append_nil, List.mem_append, List.mem_singleton] at unfolded
    rcases unfolded with known | matched
    · obtain ⟨e', member', rfl⟩ := List.mem_map.mp known
      have inL : e' ∈ L := by simpa [tellState, rowX] using member'
      show Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) e'.1) =
        Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) e'.2)
      rw [onState' e'.1 (Or.inl (List.mem_map.mpr ⟨e', member', rfl⟩)),
        onState' e'.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨e', member', rfl⟩)))]
      exact solves e' inL
    · subst matched
      show Subst.applyTerm u (Subst.applyTerm ι x) =
        Subst.applyTerm u (Subst.applyTerm (Subst.id atoms) x)
      rw [uRead, Subst.applyTerm_id, uX]
  have guard : Subst.applyTerm u (Subst.applyTerm ι x) = Subst.applyTerm u (c 6) :=
    checks (.equal (Subst.applyTerm ι x) (c 6)) (List.mem_singleton_self _) PUnit.unit u uSolves
  intro e inside
  obtain rfl := List.mem_singleton.mp inside
  show Subst.applyTerm σ x = Subst.applyTerm σ (c 6)
  rw [← uRead]
  exact guard

/-! ## The program of the two guarded reads -/

/-- The two guarded reads. -/
def either : Program Tm := {readFive, readSix}

/-- **The program is positive**: its checks are equations and it has no collect query. -/
theorem either_positive : PositiveProgram either := by
  rintro r (isFive | isSix)
  · rw [isFive]
    exact ⟨fun check inside => ⟨x, c 5, List.mem_singleton.mp inside⟩, rfl⟩
  · have same : r = readSix := isSix
    rw [same]
    exact ⟨fun check inside => ⟨x, c 6, List.mem_singleton.mp inside⟩, rfl⟩

/-- The tell context `L` enables the program at the row `x`. -/
def EnablesEither (L : EquationStore (Term atoms)) : Prop := Moves ⟨either, tellState rowX L⟩

/-- A larger program moves where a smaller one does. -/
theorem moves_of_subset {P P' : Program Tm} (sub : P ⊆ P') {s : State Tm ℕ} (moves : Moves ⟨P, s⟩) :
    Moves ⟨P', s⟩ := by
  obtain ⟨T, -, f, admitted, -⟩ := moves
  exact ⟨_, reduces_of_admits (reprogram f (sub f.member)) admitted⟩

theorem enablesEither_five : EnablesEither [(x, c 5)] :=
  moves_of_subset (fun _ isFive => Or.inl isFive) enablesRead_five

theorem enablesEither_six : EnablesEither [(x, c 6)] :=
  moves_of_subset (fun _ isSix => Or.inr isSix) enablesSix_six

/-- **Every enabling tell entails `x = 5` or entails `x = 6`.** -/
theorem entails_of_enablesEither {L : EquationStore (Term atoms)} (enables : EnablesEither L) :
    (∀ σ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ L →
        X.Models (a := PUnit.unit) (b := PUnit.unit) σ [(x, c 5)]) ∨
      ∀ σ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ L →
        X.Models (a := PUnit.unit) (b := PUnit.unit) σ [(x, c 6)] := by
  obtain ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩ := enables
  by_cases isFive : rule = readFive
  · subst isFive
    left
    intro σ solves
    exact models_five_of_enablesRead
      ⟨_, reduces_of_admits (⟨readFive, Set.mem_singleton _, ext, ι, selection, seen⟩ :
        Firing ℕ E ({readFive} : Program Tm) (tellState rowX L).frame) admitted⟩ σ solves
  · have isSix : rule = readSix := by
      rcases member with same | same
      · exact absurd same isFive
      · exact same
    subst isSix
    right
    intro σ solves
    exact models_six_of_enablesSix
      ⟨_, reduces_of_admits (⟨readSix, Set.mem_singleton _, ext, ι, selection, seen⟩ :
        Firing ℕ E ({readSix} : Program Tm) (tellState rowX L).frame) admitted⟩ σ solves

/-- **No least enabling tell for a positive program**: no enabling tell context is entailed by every
enabling one. -/
theorem no_least_enabling_tell_positive :
    PositiveProgram either ∧
      ¬ ∃ L₀ : EquationStore (Term atoms), EnablesEither L₀ ∧ ∀ L, EnablesEither L →
        ∀ σ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ L →
          X.Models (a := PUnit.unit) (b := PUnit.unit) σ L₀ := by
  refine ⟨either_positive, ?_⟩
  rintro ⟨L₀, enables, least⟩
  have atFive : X.Models (a := PUnit.unit) (b := PUnit.unit) (pinX 5) L₀ :=
    least [(x, c 5)] enablesEither_five (pinX 5) (fun e inside => by
      obtain rfl := List.mem_singleton.mp inside
      rfl)
  have atSix : X.Models (a := PUnit.unit) (b := PUnit.unit) (pinX 6) L₀ :=
    least [(x, c 6)] enablesEither_six (pinX 6) (fun e inside => by
      obtain rfl := List.mem_singleton.mp inside
      rfl)
  rcases entails_of_enablesEither enables with five | six
  · have bad : Subst.applyTerm (pinX 6) x = Subst.applyTerm (pinX 6) (c 5) :=
      five (pinX 6) atSix (x, c 5) (List.mem_singleton_self _)
    have values : (c 6 : Term atoms) = c 5 := bad
    exact absurd (Term.const.inj values) (by decide)
  · have bad : Subst.applyTerm (pinX 5) x = Subst.applyTerm (pinX 5) (c 6) :=
      six (pinX 5) atFive (x, c 6) (List.mem_singleton_self _)
    have values : (c 5 : Term atoms) = c 6 := bad
    exact absurd (Term.const.inj values) (by decide)

#print axioms enablesSix_six
#print axioms models_six_of_enablesSix
#print axioms either_positive
#print axioms entails_of_enablesEither
#print axioms no_least_enabling_tell_positive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.LeastTell
