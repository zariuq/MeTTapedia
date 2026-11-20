import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Confinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Algebra

/-!
# Where worlds interact: the joint information of a used premise, and publications against checks

Controls on first-order atoms (`RuleSyntax.Examples`), continuing `Worlds.Controls`.

## A firing that uses a shared premise uses the joint information

* `joint_not_pairwise`: a reader whose own row `x` it knows to be `6` fires the closed row that carries
  `x = 5` (admitted: the two knowledges, kept apart by the opening, are solvable together). A rule
  that reads the reader's row and the copy against one unknown is then **refused**, although the
  reader's knowledge with the match, the row's knowledge with the match, and the two knowledges
  without the match are each solvable. The firing is decided by the information of all it uses, at one
  solution: not by what was solvable when the row arrived, and not pair by pair.

* `importCapturing_refused`, `importOntoARow_refused`: the controls for the two hypotheses of
  `snapshot_importable`: an opening that is not fresh (the row's unknown opened as the reader's own)
  and a copy made at a present identity. `copy_label`: an instance of `import_label`.
* `dead_publisher_confined`, `distribute_instance`: instances of `snapshot_dead_never_fires`,
  `dead_world_is_no_neighbour_mayBarb` and `merge_distributes`.

## A publication gives a firing that was not there

* `publication_enables`: a world publishes its row; a second world then fires the published row; before
  the publication no firing of the second world has that rule. The worlds of a bag do interact, through
  the space.

## A located row that a check reads

* `shared_row_blocks`: in the candidate with a store at each location
  (`Hosting.Alternatives.Located.LState`), a location's none check of `9` passes while the row `9`
  is at another location, and is refused once that row is shared. With located rows that checks read,
  a check and the sharing of a row do not commute; with closed rows they always do
  (`fire_publish_commute`).
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
  (Tm X E x c demo shift everywhere boundRequest noNineFiring noNine_fresh)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (System Pattern MayBarb)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located (LState)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Worlds
  (snapshot)
open Mettapedia.Logic.LP

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Controls

open Interface (Frames)

/-! ## The joint information of a used premise -/

/-- Read two rows against one unknown. -/
def twice : Rule Tm := ⟨PUnit.unit, ⟨[], [x, x], [], [], []⟩, []⟩

/-- The rules of the reader: `twice`, and the space that holds the closed row. -/
abbrev jointProgram : Program Tm := {twice} ∪ {fiveRow}

/-- A reader with its own row `x`, which it knows to be `6`. -/
def sixReader : State Tm ℕ := ⟨PUnit.unit, [(x, c 6)], {0}, fun _ => x⟩

/-- The reader fires the closed row, its unknown opened as `x₁`, and makes the copy at identity `1`. -/
def importSix : Firing ℕ E jointProgram PUnit.unit :=
  ⟨fiveRow, Set.mem_union_right _ (Set.mem_singleton _), PUnit.unit, shift, ⟨[], [], [1]⟩, []⟩

theorem importSix_fresh : importSix.Fresh X sixReader := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t (member | member | ⟨o, -, rfl⟩)
    · change t ∈ [x] at member
      rw [List.mem_singleton] at member
      subst member
      rfl
    · change t ∈ [c 6] at member
      rw [List.mem_singleton] at member
      subst member
      rfl
    · rfl
  · intro t member
    change t ∈ [x, c 5, x] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

/-- **The closed row is fired**: the reader's knowledge `x = 6` and the row's knowledge `x = 5` are
about unknowns the opening keeps apart. -/
theorem importSix_admitted : importSix.Admits X sixReader :=
  (snapshot_importable (X := X) (E := E) (P := jointProgram) (terminalFrame := PUnit.unit)
    (fun _ => ⟨Subst.id atoms⟩) boundRequest sixReader x
    (Set.mem_union_right _ (Set.mem_singleton _)) PUnit.unit shift 1 importSix_fresh
    (fun inside => absurd (Finset.mem_singleton.mp inside) (by decide))).mpr
    ⟨⟨PUnit.unit, everywhere 6, fun e member => by
        change e ∈ [(x, c 6)] at member
        rw [List.mem_singleton] at member
        subst member
        rfl⟩,
      ⟨PUnit.unit, everywhere 5, fun e member => by
        change e ∈ [(x, c 5)] at member
        rw [List.mem_singleton] at member
        subst member
        rfl⟩⟩

/-- Read the reader's row and the copy against one unknown, opened as `x₂`. -/
def twiceFiring : Firing ℕ E jointProgram PUnit.unit :=
  ⟨twice, Set.mem_union_left _ (Set.mem_singleton _), PUnit.unit, fun v => Term.var (v + 2),
    ⟨[], [0, 1], []⟩, []⟩

/-- The information of that firing: the reader's knowledge, the row's knowledge, and the match. -/
def jointInformation : EquationStore (Term atoms) :=
  [(x, c 6), (Term.var 1, c 5), (Term.var 2, x), (Term.var 2, Term.var 1)]

theorem twice_information :
    twiceFiring.information X (importSix.result X sixReader) = jointInformation := rfl

/-- The reader's knowledge with the match is solvable. -/
theorem reader_with_match :
    X.Solvable (a := PUnit.unit)
      [(x, c 6), ((Term.var 2 : Term atoms), x), ((Term.var 2 : Term atoms), Term.var 1)] := by
  refine ⟨PUnit.unit, everywhere 6, fun e member => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- The row's knowledge with the match is solvable. -/
theorem row_with_match :
    X.Solvable (a := PUnit.unit)
      [((Term.var 1 : Term atoms), c 5), ((Term.var 2 : Term atoms), x),
        ((Term.var 2 : Term atoms), Term.var 1)] := by
  refine ⟨PUnit.unit, everywhere 5, fun e member => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- The two knowledges without the match are solvable. -/
theorem knowledges_without_match :
    X.Solvable (a := PUnit.unit) [(x, c 6), ((Term.var 1 : Term atoms), c 5)] := by
  refine ⟨PUnit.unit, fun v => if v = 1 then c 5 else c 6, fun e member => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- **The joint information is refused.** -/
theorem twice_refused : ¬ twiceFiring.Admits X (importSix.result X sixReader) := by
  rintro ⟨-, -, ⟨_, σ, solved⟩, -⟩
  rw [twice_information] at solved
  have six : σ 0 = c 6 := solved (x, c 6) List.mem_cons_self
  have five : σ 1 = c 5 := solved (Term.var 1, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)
  have own : σ 2 = σ 0 :=
    solved (Term.var 2, x) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have copy : σ 2 = σ 1 := solved (Term.var 2, Term.var 1)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have same : (c 6 : Term atoms) = c 5 := six.symm.trans (own.symm.trans (copy.trans five))
  exact absurd (Term.const.inj same) (by decide)

/-- **A firing that uses a shared premise uses the joint information.** The closed row is fired; the
reader's knowledge with the match, the row's knowledge with the match, and the two knowledges without
the match are each solvable; the firing that uses the row with the reader's own is refused. -/
theorem joint_not_pairwise :
    importSix.Admits X sixReader ∧
      X.Solvable (a := PUnit.unit)
        [(x, c 6), ((Term.var 2 : Term atoms), x), ((Term.var 2 : Term atoms), Term.var 1)] ∧
      X.Solvable (a := PUnit.unit)
        [((Term.var 1 : Term atoms), c 5), ((Term.var 2 : Term atoms), x),
          ((Term.var 2 : Term atoms), Term.var 1)] ∧
      X.Solvable (a := PUnit.unit) [(x, c 6), ((Term.var 1 : Term atoms), c 5)] ∧
      ¬ twiceFiring.Admits X (importSix.result X sixReader) :=
  ⟨importSix_admitted, reader_with_match, row_with_match, knowledges_without_match, twice_refused⟩

/-! ## Controls for the two hypotheses of `snapshot_importable` -/

/-- The reader fires the closed row with the row's unknown opened as the reader's own `x`. -/
def importCapturing : Firing ℕ E jointProgram PUnit.unit :=
  ⟨fiveRow, Set.mem_union_right _ (Set.mem_singleton _), PUnit.unit, Subst.id atoms,
    ⟨[], [], [1]⟩, []⟩

/-- **Control for freshness**: with the row's unknown opened as the reader's own, the two knowledges
are about one unknown, and the firing is refused although each knowledge is solvable. -/
theorem importCapturing_refused : ¬ importCapturing.Admits X sixReader := by
  rintro ⟨-, -, ⟨_, σ, solved⟩, -⟩
  have known : X.Models (a := PUnit.unit) (b := PUnit.unit) σ [(x, c 6), (x, c 5)] := solved
  have six : σ 0 = c 6 := known (x, c 6) List.mem_cons_self
  have five : σ 0 = c 5 := known (x, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact absurd (Term.const.inj (six.symm.trans five)) (by decide)

/-- The reader fires the closed row and makes the copy at an identity that is present. -/
def importOntoARow : Firing ℕ E jointProgram PUnit.unit :=
  ⟨fiveRow, Set.mem_union_right _ (Set.mem_singleton _), PUnit.unit, shift, ⟨[], [], [0]⟩, []⟩

/-- **Control for the new identity**: a copy made at a present identity is refused. -/
theorem importOntoARow_refused : ¬ importOntoARow.Admits X sixReader := by
  rintro ⟨-, enabled, -, -⟩
  exact Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr List.mem_cons_self)
    (Finset.mem_singleton_self 0)

/-- **The copy is the atom, renamed by the opening**: an instance of `import_label`. -/
theorem copy_label : (importFiring.result X emptyReader).label 0 = (Term.var 1 : Term atoms) :=
  import_label (X := X) (E := E) (P := readerProgram) boundRequest emptyReader x
    (Set.mem_union_right _ (Set.mem_singleton _)) PUnit.unit shift 0 [] import_admitted

/-! ## A world whose knowledge has no solution -/

/-- A world that knows `1 = 2`, with one row. -/
def deadPublisher : State Tm ℕ := ⟨PUnit.unit, [(c 1, c 2)], {0}, fun _ => c 7⟩

theorem deadPublisher_dead : ¬ X.Solvable deadPublisher.knowledge := by
  rintro ⟨_, σ, solved⟩
  have same : (c 1 : Term atoms) = c 2 := solved (c 1, c 2) List.mem_cons_self
  exact absurd (Term.const.inj same) (by decide)

/-- **A row published from that world is fired by no world, and beside any bag the world is no
neighbour**: instances of `snapshot_dead_never_fires` and `dead_world_is_no_neighbour_mayBarb`. -/
theorem dead_publisher_confined (p : Pattern Tm) (ws : Multiset (System Tm ℕ)) (R : Program Tm) :
    (∀ (P : Program Tm) (t : State Tm ℕ) (f : Firing ℕ E P t.frame),
        f.rule = snapshot deadPublisher (c 7) → ¬ f.Admits X t) ∧
      ((bagParallel X besideJoining (events X ℕ E) (MayBarb X p)).Succeeds
          ⟨(⟨demo, deadPublisher⟩ : System Tm ℕ) ::ₘ ws, R⟩ ↔
        (bagParallel X besideJoining (events X ℕ E) (MayBarb X p)).Succeeds ⟨ws, R⟩) :=
  ⟨fun _ _ f isRow => snapshot_dead_never_fires (c 7) deadPublisher_dead f isRow,
    dead_world_is_no_neighbour_mayBarb p deadPublisher_dead ws R⟩

/-- **A world merged with each of two**: an instance of `merge_distributes`, with the world that
holds the row `9` and two copies of the world that knows `x = 5`. -/
theorem distribute_instance :
    Relation.ReflTransGen (Move X besideJoining (events X ℕ E))
      ⟨(⟨demo, boundRequest⟩ : System Tm ℕ) ::ₘ (⟨demo, boundRequest⟩ : System Tm ℕ) ::ₘ
        (⟨∅, nineHolder⟩ : System Tm ℕ) ::ₘ 0, ∅⟩
      ⟨(⟨demo ∪ ∅, Scope.beside boundRequest nineHolder⟩ : System Tm ℕ) ::ₘ
        (⟨demo ∪ ∅, Scope.beside boundRequest nineHolder⟩ : System Tm ℕ) ::ₘ 0, ∅⟩ :=
  merge_distributes 0 ∅ ⟨demo, boundRequest⟩ ⟨demo, boundRequest⟩ ⟨∅, nineHolder⟩
    none_reads_its_own_world.2.1 none_reads_its_own_world.2.1

/-! ## A publication gives a firing that was not there -/

/-- The closed row is no rule of `demo`. -/
theorem fiveRow_not_demo : fiveRow ∉ demo ∪ (∅ : Program Tm) := by
  intro member
  rcases (Set.mem_union _ _ _).mp member with inDemo | inEmpty
  · rcases inDemo with same | same | same | same | same <;>
      exact absurd (congrArg (fun r : Rule Tm => (r.body.read.length, r.body.tell.length)) same)
        (by decide)
  · exact absurd inEmpty (Set.notMem_empty _)

/-- **A publication gives a firing that was not there.** The world that knows `x = 5` publishes its
row; the reader then fires the published row; before the publication no firing of the reader has that
rule. -/
theorem publication_enables :
    Move X besideJoining (events X ℕ E)
        ⟨(⟨demo, emptyReader⟩ : System Tm ℕ) ::ₘ (⟨∅, boundRequest⟩ : System Tm ℕ) ::ₘ 0, ∅⟩
        ⟨(⟨demo, emptyReader⟩ : System Tm ℕ) ::ₘ
          (⟨∅, withoutRow boundRequest 0⟩ : System Tm ℕ) ::ₘ 0, insert fiveRow ∅⟩ ∧
      Move X besideJoining (events X ℕ E)
        ⟨(⟨demo, emptyReader⟩ : System Tm ℕ) ::ₘ
          (⟨∅, withoutRow boundRequest 0⟩ : System Tm ℕ) ::ₘ 0, insert fiveRow ∅⟩
        ⟨(⟨demo, importFiring.result X emptyReader⟩ : System Tm ℕ) ::ₘ
          (⟨∅, withoutRow boundRequest 0⟩ : System Tm ℕ) ::ₘ 0, insert fiveRow ∅⟩ ∧
      ∀ f : Firing ℕ E (demo ∪ (∅ : Program Tm)) PUnit.unit, f.rule ≠ fiveRow :=
  ⟨Move.cast (Move.publish (family := events X ℕ E) ((⟨demo, emptyReader⟩ : System Tm ℕ) ::ₘ 0) ∅ ⟨∅, boundRequest⟩ 0
      (Finset.mem_singleton_self 0)) (swap_worlds _ _ _ _) (swap_worlds _ _ _ _),
    Move.fire (family := events X ℕ E) ((⟨∅, withoutRow boundRequest 0⟩ : System Tm ℕ) ::ₘ 0) (insert fiveRow ∅)
      ⟨demo, emptyReader⟩
      ⟨widen (Set.union_subset_union_right _ fun _ same => Set.mem_insert_iff.mpr (Or.inl same))
        importFiring, import_admitted⟩,
    fun f => not_before_publication fiveRow_not_demo f⟩

/-! ## A located row that a check reads -/

/-- The row `x` at the first location, which knows `x = 5`, and the row `9` at the given place. -/
def nineAt (home : Option Bool) : LState Tm ℕ Bool where
  frame := PUnit.unit
  stores _ := [(x, c 5)]
  live := {true, false}
  present := {0, 1}
  label o := if o = 0 then x else c 9
  place o := if o = 0 then some true else home

/-- While the row `9` is at the other location, the first location sees only its own row. -/
theorem private_row_unseen {o : ℕ} (seen : o ∈ ((nineAt (some false)).view true).present) : o = 0 := by
  obtain ⟨inside, visible⟩ := Finset.mem_filter.mp seen
  rcases Finset.mem_insert.mp inside with zero | one
  · exact zero
  · have isOne : o = 1 := Finset.mem_singleton.mp one
    subst isOne
    rcases visible with atFirst | shared
    · exact absurd (Option.some.inj atFirst) (by decide)
    · exact absurd shared (by decide)

/-- **While the row `9` is at another location, the none check passes.** -/
theorem private_row_passes :
    (step X ℕ E demo).Admits (s := (nineAt (some false)).view true) noNineFiring := by
  show noNineFiring.Admits X ((nineAt (some false)).view true)
  refine ⟨⟨noNine_fresh _, List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [noNineFiring, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 5, fun e inside => ?_⟩
    change e ∈ [(x, c 5)] at inside
    rw [List.mem_singleton] at inside
    subst inside
    rfl
  · intro b σ solved
    have known : X.Models (a := PUnit.unit) (b := b) σ [(x, c 5)] := solved
    have bound : σ 0 = c 5 := known (x, c 5) List.mem_cons_self
    refine ⟨fun check inside => ?_, fun q inside => absurd inside List.not_mem_nil⟩
    have isNone : check = Check.predicate .none (c 9) := List.mem_singleton.mp inside
    subst isNone
    intro o present equated
    have isOwn : o = 0 := private_row_unseen present
    subst isOwn
    have nine : (c 9 : Term atoms) = σ 0 := equated
    rw [bound] at nine
    exact absurd (Term.const.inj nine) (by decide)

/-- **Once the row `9` is shared, the none check is refused.** -/
theorem shared_row_refuses :
    ¬ (step X ℕ E demo).Admits (s := (nineAt none).view true) noNineFiring := by
  intro admitted
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff noNineFiring).mp admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (everywhere 5)
      (noNineFiring.information X ((nineAt none).view true)) := by
    intro e inside
    change e ∈ [(x, c 5)] at inside
    rw [List.mem_singleton] at inside
    subst inside
    rfl
  have holds := checks (.predicate .none (c 9)) (List.mem_singleton_self _) PUnit.unit _ solved
  exact holds 1 (Finset.mem_filter.mpr
    ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self 1), Or.inr rfl⟩) rfl

/-- **A located row that a check reads**: the none check of `9` passes while the row `9` is at
another location, and is refused once it is shared. -/
theorem shared_row_blocks :
    (step X ℕ E demo).Admits (s := (nineAt (some false)).view true) noNineFiring ∧
      ¬ (step X ℕ E demo).Admits (s := (nineAt none).view true) noNineFiring :=
  ⟨private_row_passes, shared_row_refuses⟩

#print axioms importSix_admitted
#print axioms twice_information
#print axioms twice_refused
#print axioms joint_not_pairwise
#print axioms importCapturing_refused
#print axioms importOntoARow_refused
#print axioms copy_label
#print axioms dead_publisher_confined
#print axioms distribute_instance
#print axioms fiveRow_not_demo
#print axioms publication_enables
#print axioms private_row_passes
#print axioms shared_row_refuses
#print axioms shared_row_blocks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Controls
