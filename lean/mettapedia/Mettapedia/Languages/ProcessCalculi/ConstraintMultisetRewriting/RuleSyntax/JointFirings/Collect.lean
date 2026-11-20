import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Exec

/-!
# Completeness and the collect query

`Bag.Complete` asks, at the entry state, that the key of every admitted firing of the rules be the key of
a member: a statement over every selection of present rows and every opening. A collect pattern of a firing
(`Firing.Holds`) is read at every solution of the firing's own information and sees the present rows the
solution equates with the pattern.

## One ground pattern: completeness is what the collect query sees (`Ground`)

The rule `copy` reads a token `1` and makes a `2`. At a state of tokens, the collect query of the pattern `1` sees
every token at every solution (`collect_sees_all`), and a bag of matches of `copy` is complete exactly when
it has a match for each row the collect query sees (`complete_iff`).

## A pattern with an unknown: the collect query of a member does not see the other matches (`Unbound`)

The rule `readAny` reads any row `x`, makes a `2`, and has the collect pattern `x`. At a state with a row
labelled `1` and a row labelled `3`, the member that reads the first row and claims that its collect query sees
exactly that row is admitted (`first_admitted`): at every solution of its information, `x` is the label of
the row it read. The bag of that member alone is admitted (`alone_admitted`) and is not complete: the match
on the other row is admitted too (`second_admitted`, `alone_not_complete`). So the collect query of a member's own
pattern holds on a bag that misses a match: what completeness asks is not a collect query of a member.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Collect

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open Examples (Tm X E c x)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

namespace Ground

open EveryControls (copy copies tokensAt copy_ground)
open MatchAll (copy_shape)

/-- **The collect query of the pattern `1` sees every token**, at every solution. -/
theorem collect_sees_all (W : Finset ℕ) (σ : Subst atoms) (row : ℕ → Term atoms)
    (tokens : ∀ o, row o = c 1) :
    matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ row W (c 1) = W := by
  ext o
  rw [mem_matchesAt]
  constructor
  · exact fun inside => inside.1
  · intro inside
    refine ⟨inside, ?_⟩
    show Subst.applyTerm σ (c 1) = Subst.applyTerm σ (row o)
    rw [tokens o]

/-- Read the token at `o`, make the identity `n`. -/
def readAt (o n : ℕ) : Firing ℕ E copies PUnit.unit :=
  ⟨copy, rfl, PUnit.unit, Subst.id atoms, ⟨[], [o], [n]⟩, []⟩

theorem readAt_admitted {W : Finset ℕ} {o n : ℕ} (present : o ∈ W) (fresh : n ∉ W) :
    (readAt o n).Admits X (tokensAt W) := by
  refine ⟨⟨Examples.fresh_of_ground action (tokensAt W) _ copy_ground, List.nodup_nil,
      List.nodup_singleton n, rfl, rfl, rfl, rfl⟩,
    ⟨fun y member => ?_, fun y member => ?_, Finset.disjoint_left.mpr fun _ taken _ => ?_,
      Finset.disjoint_left.mpr fun y made inside => ?_, fun q member => by
        simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
    fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩⟩
  · exact absurd (List.mem_toFinset.mp member) List.not_mem_nil
  · rw [List.mem_singleton.mp (List.mem_toFinset.mp member)]
    exact present
  · exact absurd (List.mem_toFinset.mp taken) List.not_mem_nil
  · rw [List.mem_singleton.mp (List.mem_toFinset.mp made)] at inside
    exact fresh inside
  · have listed : e ∈ [(c 1, c 1)] := member
    rw [List.mem_singleton.mp listed]

/-- **One ground pattern: a bag of matches is complete exactly when it has a match for every row the
collect query of the pattern sees.** -/
theorem complete_iff (W : Finset ℕ) (f : Bag ℕ E copies PUnit.unit) :
    f.Complete X (tokensAt W) copies ↔
      ∀ o ∈ matchesAt X (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms) (fun _ => c 1) W (c 1),
        (copy, ([] : List ℕ), [o]) ∈ f.members.map Member.key := by
  rw [collect_sees_all W _ _ fun _ => rfl]
  constructor
  · intro complete o present
    obtain ⟨n, fresh⟩ := Infinite.exists_notMem_finset W
    exact complete (readAt o n) rfl (readAt_admitted present fresh)
  · intro every g _ admitted
    obtain ⟨o, n, present, rule, selection⟩ := copy_shape g admitted
    have key : firingKey g = (copy, [], [o]) := by
      unfold firingKey
      rw [rule, selection]
    rw [key]
    exact every o present

end Ground

namespace Unbound

/-- Read any row `x`, make a `2`; the collect pattern `x`. -/
def readAny : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [], [], [c 2]⟩, [x]⟩

/-- **The program.** -/
def program : Program Tm := {readAny}

/-- The label of each row: `1` at `0`, `3` elsewhere. -/
def kind : ℕ → ℕ
  | 0 => 1
  | _ => 3

/-- **Two rows, labelled `1` and `3`.** -/
def mixed : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, fun o => c (kind o)⟩

/-- The opening that renames the unknown `n` to `n + 1`. -/
def shift : Subst atoms := fun n => Term.var (n + 1)

/-- Read the row at `o`, make `n`, and claim that the collect query sees exactly that row. -/
def readOne (o n : ℕ) : OneMember action ℕ program := ⟨readAny, rfl, shift, ⟨[], [o], [n]⟩, [{o}]⟩

theorem readOne_information (o n : ℕ) :
    (readOne o n).firing.information X mixed = [(.var 1, c (kind o))] := rfl

theorem readOne_fresh (o n : ℕ) : (readOne o n).firing.Fresh X mixed := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t (member | member | ⟨o', -, rfl⟩)
    · exact absurd member List.not_mem_nil
    · exact absurd member List.not_mem_nil
    · rfl
  · intro t member
    have listed : t ∈ [x, c 2, x] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> rfl

/-- **The collect query of the match on a row sees that row**: at every solution, `x` is the row's label. -/
theorem readOne_admitted {o n : ℕ} (present : o ∈ mixed.present) (fresh : n ∉ mixed.present) :
    (readOne o n).firing.Admits X mixed := by
  refine ⟨⟨readOne_fresh o n, List.nodup_nil, List.nodup_singleton n, rfl, rfl, rfl, rfl⟩,
    ⟨fun y member => ?_, fun y member => ?_, Finset.disjoint_left.mpr fun _ taken _ => ?_,
      Finset.disjoint_left.mpr fun y made inside => ?_, fun q member => by
        simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, fun _ => c (kind o), fun e member => ?_⟩, fun b σ solved => ⟨fun _ member => ?_,
      fun q member => ?_⟩⟩
  · exact absurd (List.mem_toFinset.mp member) List.not_mem_nil
  · rw [List.mem_singleton.mp (List.mem_toFinset.mp member)]
    exact present
  · exact absurd (List.mem_toFinset.mp taken) List.not_mem_nil
  · rw [List.mem_singleton.mp (List.mem_toFinset.mp made)] at inside
    exact fresh inside
  · rw [readOne_information, List.mem_singleton] at member
    rw [member]
    rfl
  · exact absurd member List.not_mem_nil
  · have bound : σ 1 = c (kind o) := by
      rw [readOne_information] at solved
      exact solved (.var 1, c (kind o)) List.mem_cons_self
    have listed : q ∈ [((Term.var 1 : Term atoms), ({o} : Finset ℕ))] := member
    rw [List.mem_singleton.mp listed]
    ext y
    rw [mem_matchesAt, Finset.mem_singleton]
    show (y ∈ ({0, 1} : Finset ℕ) ∧ σ 1 = Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (c (kind y))))
      ↔ y = o
    rw [bound]
    have inside : o = 0 ∨ o = 1 := by simpa [mixed] using present
    constructor
    · rintro ⟨inY, same⟩
      have yCases : y = 0 ∨ y = 1 := by simpa using inY
      have kinds : kind o = kind y := Term.const.inj same
      rcases inside with rfl | rfl <;> rcases yCases with rfl | rfl <;> simp_all [kind]
    · rintro rfl
      exact ⟨present, rfl⟩

/-- **The match on the first row is admitted, its collect query seeing exactly that row.** -/
theorem first_admitted : (readOne 0 10).firing.Admits X mixed := readOne_admitted (by decide) (by decide)

/-- **The match on the second row is admitted too.** -/
theorem second_admitted : (readOne 1 11).firing.Admits X mixed := readOne_admitted (by decide) (by decide)

/-- The bag of the first match alone. -/
def alone : Bag ℕ E program PUnit.unit := bagOf action [readOne 0 10]

/-- **It is admitted**, its member's collect query holding. -/
theorem alone_admitted : Bag.AdmitsOwn X mixed alone :=
  (Bag.admitsOwn_single X mixed (readOne 0 10)).mpr first_admitted

/-- **It is not complete**: the match on the second row is admitted and missing. -/
theorem alone_not_complete : ¬ alone.Complete X mixed program := by
  intro complete
  have listed := complete (readOne 1 11).firing rfl second_admitted
  have same : firingKey (readOne 1 11).firing = (readOne 0 10).key := List.mem_singleton.mp listed
  have reads := congrArg (fun k : Rule Tm × List ℕ × List ℕ => k.2.2) same
  exact absurd reads (by decide)

end Unbound

#print axioms Ground.collect_sees_all
#print axioms Ground.readAt_admitted
#print axioms Ground.complete_iff
#print axioms Unbound.readOne_admitted
#print axioms Unbound.first_admitted
#print axioms Unbound.second_admitted
#print axioms Unbound.alone_admitted
#print axioms Unbound.alone_not_complete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Collect
