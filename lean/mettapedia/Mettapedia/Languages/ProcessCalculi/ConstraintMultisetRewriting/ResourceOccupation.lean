import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-!
# Resource occupation operators on physical occurrence identities

Every identity has one presence bit. A partial operator reads, removes or
introduces occurrences; failure is `none`. The operators below compute
independently of `Enabled`, then their successful results are proved to
coincide with the existing occurrence commit and `fire` operation.

Local freshness remains separate: taking and remaking one identity has the
same final-state operator as a read, while the source step forbids that
identity reuse. Equality of operators consequently forgets intermediate
history and does not establish equality of resource-aware processes.

The pointwise product laws preserve exact physical identities. No passage
to label classes, answer-count measure, Weyl algebra or probability model is
assumed. Reversal is a property of successful finite partial maps; it supplies
neither native rollback nor an inverse for a failed operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupation

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

variable {O : Type*} [DecidableEq O]

/-- A partial operator on finite occurrence worlds; `none` is failure. -/
abbrev Op (O : Type*) := Finset O → Option (Finset O)

/-- Sequential composition: first `f`, then `g`. -/
def andThen (f g : Op O) : Op O := fun W => (f W).bind g

/-- The zero operator. -/
def zero : Op O := fun _ => none

/-- The identity operator. -/
def one : Op O := some

omit [DecidableEq O] in
theorem andThen_assoc (first second third : Op O) :
    andThen (andThen first second) third = andThen first (andThen second third) := by
  funext world
  simp only [andThen, Option.bind_assoc]
  rfl

omit [DecidableEq O] in
@[simp] theorem one_andThen (operation : Op O) : andThen one operation = operation := by
  funext world
  rfl

omit [DecidableEq O] in
@[simp] theorem andThen_one (operation : Op O) : andThen operation one = operation := by
  funext world
  simp [andThen, one]

omit [DecidableEq O] in
@[simp] theorem zero_andThen (operation : Op O) : andThen zero operation = zero := by
  funext world
  rfl

omit [DecidableEq O] in
@[simp] theorem andThen_zero (operation : Op O) : andThen operation zero = zero := by
  funext world
  change (operation world).bind (fun _ => none) = none
  cases operation world <;> rfl

/-- Take: defined exactly when the identity is present. -/
def annihilate (o : O) : Op O := fun W => if o ∈ W then some (W.erase o) else none

/-- Read: defined exactly when the identity is present; keeps it. -/
def point (o : O) : Op O := fun W => if o ∈ W then some W else none

/-- Produce: defined exactly when the identity is absent. -/
def create (o : O) : Op O := fun W => if o ∈ W then none else some (insert o W)

/-- The complementary projector `1 − N`: the identity is absent. -/
def vacant (o : O) : Op O := fun W => if o ∈ W then none else some W

/-! ## Per-mode relations -/

section Relations

variable (o : O)

theorem annihilate_twice : andThen (annihilate o) (annihilate o) = zero := by
  funext W
  by_cases h : o ∈ W <;> simp [andThen, annihilate, zero, h]

theorem create_twice : andThen (create o) (create o) = zero := by
  funext W
  by_cases h : o ∈ W <;> simp [andThen, create, zero, h]

theorem point_twice : andThen (point o) (point o) = point o := by
  funext W
  by_cases h : o ∈ W <;> simp [andThen, point, h]

/-- `N∂ = 0`: a row that was taken cannot then be read. -/
theorem annihilate_then_point : andThen (annihilate o) (point o) = zero := by
  funext W
  by_cases h : o ∈ W <;> simp [andThen, annihilate, point, zero, h]

/-- `xN = 0`: a row that is read cannot be made. -/
theorem point_then_create : andThen (point o) (create o) = zero := by
  funext W
  by_cases h : o ∈ W <;> simp [andThen, point, create, zero, h]

/-- `∂N = ∂`: reading and then taking one row is taking it (E1 runs in this order). -/
theorem point_then_annihilate : andThen (point o) (annihilate o) = annihilate o := by
  funext W
  by_cases h : o ∈ W <;> simp [andThen, point, annihilate, h]

/-- `Nx = x`: a row just made can be read. -/
theorem create_then_point : andThen (create o) (point o) = create o := by
  funext W
  by_cases h : o ∈ W <;> simp [andThen, point, create, h]

/-- `x∂ = N`: taking a row and making the same identity again is reading it. This is the one
per-mode combination the algebra does not kill; the source forbids it by freshness. -/
theorem annihilate_then_create : andThen (annihilate o) (create o) = point o := by
  funext W
  by_cases h : o ∈ W
  · simp [andThen, annihilate, create, point, h, Finset.insert_erase h]
  · simp [andThen, annihilate, point, h]

/-- `∂x = 1 − N`. -/
theorem create_then_annihilate : andThen (create o) (annihilate o) = vacant o := by
  funext W
  by_cases h : o ∈ W
  · simp [andThen, create, vacant, h]
  · simp [andThen, create, annihilate, vacant, h, Finset.erase_insert h]

end Relations

/-! ## Operators on distinct modes commute -/

/-- A single-mode operator: it tests and changes only the membership of `o`. -/
def SingleMode (o : O) (f : Op O) : Prop :=
  ∃ (present absent : Option Bool),
    ∀ W, f W = (if o ∈ W then present else absent).map
      (fun keep => if keep then insert o W else W.erase o)

theorem annihilate_single (o : O) : SingleMode o (annihilate o) :=
  ⟨some false, none, fun W => by by_cases h : o ∈ W <;> simp [annihilate, h]⟩

theorem point_single (o : O) : SingleMode o (point o) :=
  ⟨some true, none, fun W => by
    by_cases h : o ∈ W
    · simp [point, h, Finset.insert_eq_of_mem h]
    · simp [point, h]⟩

theorem create_single (o : O) : SingleMode o (create o) :=
  ⟨none, some true, fun W => by by_cases h : o ∈ W <;> simp [create, h]⟩

theorem vacant_single (o : O) : SingleMode o (vacant o) :=
  ⟨none, some false, fun W => by
    by_cases h : o ∈ W
    · simp [vacant, h]
    · simp [vacant, h]⟩

/-- The basis change of one mode. -/
def stepMode (o : O) (W : Finset O) (keep : Bool) : Finset O :=
  if keep then insert o W else W.erase o

private theorem mem_stepMode {o p : O} (ne : o ≠ p) (W : Finset O) (keep : Bool) :
    p ∈ stepMode o W keep ↔ p ∈ W := by
  cases keep <;> simp [stepMode, Finset.mem_insert, Finset.mem_erase, Ne.symm ne]

private theorem stepMode_comm {o p : O} (ne : o ≠ p) (W : Finset O) (k l : Bool) :
    stepMode p (stepMode o W k) l = stepMode o (stepMode p W l) k := by
  cases k <;> cases l <;>
    simp [stepMode, Finset.insert_comm, Finset.erase_right_comm, Finset.erase_insert_of_ne ne,
      Finset.erase_insert_of_ne (Ne.symm ne)]

/-- Single-mode operators on distinct modes commute. -/
theorem singleMode_comm {o p : O} (ne : o ≠ p) {f g : Op O}
    (hf : SingleMode o f) (hg : SingleMode p g) : andThen f g = andThen g f := by
  obtain ⟨fp, fa, hf⟩ := hf
  obtain ⟨gp, ga, hg⟩ := hg
  have hf' : ∀ W, f W = (if o ∈ W then fp else fa).map (stepMode o W) := hf
  have hg' : ∀ W, g W = (if p ∈ W then gp else ga).map (stepMode p W) := hg
  funext W
  simp only [andThen]
  rw [hf' W, hg' W]
  rcases c1 : (if o ∈ W then fp else fa) with _ | k <;>
    rcases c2 : (if p ∈ W then gp else ga) with _ | l
  · rfl
  · simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some]
    rw [hf']
    have same : (if o ∈ stepMode p W l then fp else fa) = (if o ∈ W then fp else fa) := by
      simp only [mem_stepMode (Ne.symm ne)]
    rw [same, c1]
    rfl
  · simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some]
    rw [hg']
    have same : (if p ∈ stepMode o W k then gp else ga) = (if p ∈ W then gp else ga) := by
      simp only [mem_stepMode ne]
    rw [same, c2]
    rfl
  · simp only [Option.map_some, Option.bind_some]
    rw [hf', hg']
    have sameO : (if o ∈ stepMode p W l then fp else fa) = (if o ∈ W then fp else fa) := by
      simp only [mem_stepMode (Ne.symm ne)]
    have sameP : (if p ∈ stepMode o W k then gp else ga) = (if p ∈ W then gp else ga) := by
      simp only [mem_stepMode ne]
    rw [sameO, sameP, c1, c2]
    simp only [Option.map_some, stepMode_comm ne]

/-! ## Lists of single-mode operators -/

/-- Run one single-mode operator per listed identity, left to right. -/
def runList (f : O → Op O) : List O → Op O
  | [] => one
  | o :: rest => andThen (f o) (runList f rest)

omit [DecidableEq O] in
@[simp] theorem runList_nil (f : O → Op O) (W : Finset O) : runList f [] W = some W := rfl

omit [DecidableEq O] in
@[simp] theorem runList_cons (f : O → Op O) (o : O) (rest : List O) (W : Finset O) :
    runList f (o :: rest) W = (f o W).bind (runList f rest) := rfl

theorem runList_annihilate (l : List O) (W W' : Finset O) :
    runList annihilate l W = some W' ↔ l.Nodup ∧ (∀ o ∈ l, o ∈ W) ∧ W' = W \ l.toFinset := by
  induction l generalizing W with
  | nil => simp [eq_comm]
  | cons o rest ih =>
    rw [runList_cons]
    by_cases h : o ∈ W
    · rw [show annihilate o W = some (W.erase o) from if_pos h, Option.bind_some, ih]
      constructor
      · rintro ⟨nodup, mem, rfl⟩
        have notIn : o ∉ rest := fun inRest => (Finset.mem_erase.mp (mem o inRest)).1 rfl
        refine ⟨List.nodup_cons.mpr ⟨notIn, nodup⟩, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h
          · exact (Finset.mem_erase.mp (mem x hx)).2
        · ext x
          simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.toFinset_cons,
            Finset.mem_insert]
          tauto
      · rintro ⟨nodup, mem, rfl⟩
        obtain ⟨notIn, nodupRest⟩ := List.nodup_cons.mp nodup
        refine ⟨nodupRest, fun x hx => Finset.mem_erase.mpr
          ⟨fun eq => notIn (eq ▸ hx), mem x (List.mem_cons_of_mem _ hx)⟩, ?_⟩
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.toFinset_cons,
          Finset.mem_insert]
        tauto
    · rw [show annihilate o W = none from if_neg h, Option.bind_none]
      constructor
      · intro hnone
        exact absurd hnone (by simp)
      · rintro ⟨-, mem, -⟩
        exact absurd (mem o (by simp)) h

theorem runList_point (l : List O) (W W' : Finset O) :
    runList point l W = some W' ↔ (∀ o ∈ l, o ∈ W) ∧ W' = W := by
  induction l generalizing W with
  | nil => simp [eq_comm]
  | cons o rest ih =>
    by_cases h : o ∈ W
    · simp [runList_cons, point, h, ih]
    · simp [runList_cons, point, h]

theorem runList_create (l : List O) (W W' : Finset O) :
    runList create l W = some W' ↔ l.Nodup ∧ (∀ o ∈ l, o ∉ W) ∧ W' = W ∪ l.toFinset := by
  induction l generalizing W with
  | nil => simp [eq_comm]
  | cons o rest ih =>
    rw [runList_cons]
    by_cases h : o ∈ W
    · rw [show create o W = none from if_pos h, Option.bind_none]
      constructor
      · intro hnone
        exact absurd hnone (by simp)
      · rintro ⟨-, mem, -⟩
        exact absurd h (mem o (by simp))
    · rw [show create o W = some (insert o W) from if_neg h, Option.bind_some, ih]
      constructor
      · rintro ⟨nodup, mem, rfl⟩
        have notIn : o ∉ rest := fun inRest => mem o inRest (Finset.mem_insert_self o W)
        refine ⟨List.nodup_cons.mpr ⟨notIn, nodup⟩, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h
          · exact fun hw => mem x hx (Finset.mem_insert_of_mem hw)
        · ext x
          simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.toFinset_cons]
          tauto
      · rintro ⟨nodup, mem, rfl⟩
        obtain ⟨notIn, nodupRest⟩ := List.nodup_cons.mp nodup
        refine ⟨nodupRest, fun x hx hins => ?_, ?_⟩
        · rcases Finset.mem_insert.mp hins with rfl | hw
          · exact notIn hx
          · exact mem x (List.mem_cons_of_mem _ hx) hw
        · ext x
          simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.toFinset_cons]
          tauto

/-! ## The normal-ordered commit -/

/-- The atomic commit as a normal-ordered word: all takes, then all reads, then all makes. -/
def commit (taken read made : List O) : Op O :=
  andThen (andThen (runList annihilate taken) (runList point read)) (runList create made)

/-- The normal-ordered commit succeeds exactly at the listed resource
conditions. Its makes are fresh for `W \ taken`, and its value removes the
takes then adds the makes. Source freshness is a separate theorem below. -/
theorem commit_eq_some_iff (taken read made : List O) (W W' : Finset O) :
    commit taken read made W = some W' ↔
      taken.Nodup ∧ (∀ o ∈ taken, o ∈ W) ∧ (∀ o ∈ read, o ∈ W ∧ o ∉ taken) ∧
        made.Nodup ∧ (∀ o ∈ made, o ∉ W ∨ o ∈ taken) ∧
        W' = (W \ taken.toFinset) ∪ made.toFinset := by
  simp only [commit, andThen]
  constructor
  · intro h
    obtain ⟨V, hV, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨U, hU, hMade⟩ := Option.bind_eq_some_iff.mp hV
    obtain ⟨nodupT, memT, rfl⟩ := (runList_annihilate taken W U).mp hU
    obtain ⟨memR, rfl⟩ := (runList_point read _ V).mp hMade
    obtain ⟨nodupM, memM, rfl⟩ := (runList_create made _ W').mp hRest
    refine ⟨nodupT, memT, fun o ho => ?_, nodupM, fun o ho => ?_, rfl⟩
    · have := memR o ho
      simp only [Finset.mem_sdiff, List.mem_toFinset] at this
      exact this
    · have := memM o ho
      simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not] at this
      by_cases hw : o ∈ W
      · exact Or.inr (this hw)
      · exact Or.inl hw
  · rintro ⟨nodupT, memT, memR, nodupM, memM, rfl⟩
    have hU := (runList_annihilate taken W (W \ taken.toFinset)).mpr ⟨nodupT, memT, rfl⟩
    have hV := (runList_point read (W \ taken.toFinset) (W \ taken.toFinset)).mpr
      ⟨fun o ho => by simpa [Finset.mem_sdiff] using memR o ho, rfl⟩
    have hW := (runList_create made (W \ taken.toFinset) _).mpr
      ⟨nodupM, fun o ho => by
        simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
        intro hw
        rcases memM o ho with h | h
        · exact absurd hw h
        · exact h, rfl⟩
    rw [hU, Option.bind_some, hV, Option.bind_some, hW]

/-! ## Comparison with the source `Enabled` and `fire` -/

section Incumbent

variable {R : Type*}

theorem selection_fire (s : Selection O) (W : Finset O) :
    fire W (s.commit (T := R)) = (W \ s.taken.toFinset) ∪ s.made.toFinset := rfl

/-- The source occurrence discipline of a selection (distinct takes, distinct makes and
`Enabled`) is exactly: the normal-ordered operator is nonzero, and no identity is both taken and
made. -/
theorem enabled_iff_nonzero_and_fresh (label : O → R) (s : Selection O) (W : Finset O) :
    (s.taken.Nodup ∧ s.made.Nodup ∧ Enabled label W s.commit) ↔
      (∃ W', commit s.taken s.read s.made W = some W') ∧ Disjoint s.made.toFinset s.taken.toFinset := by
  constructor
  · rintro ⟨nodupT, nodupM, enabled⟩
    have takenSub : ∀ o ∈ s.taken, o ∈ W := fun o ho =>
      enabled.taken_subset (by simpa [Selection.commit] using ho)
    have keptSub : ∀ o ∈ s.read, o ∈ W := fun o ho =>
      enabled.kept_subset (by simpa [Selection.commit] using ho)
    have apart : ∀ o ∈ s.read, o ∉ s.taken := fun o ho hot =>
      Finset.disjoint_left.mp enabled.apart (by simpa [Selection.commit] using hot)
        (by simpa [Selection.commit] using ho)
    have fresh : ∀ o ∈ s.made, o ∉ W := fun o ho hw =>
      Finset.disjoint_left.mp enabled.fresh (by simpa [Selection.commit] using ho) hw
    refine ⟨⟨_, (commit_eq_some_iff _ _ _ W _).mpr
      ⟨nodupT, takenSub, fun o ho => ⟨keptSub o ho, apart o ho⟩, nodupM,
        fun o ho => Or.inl (fresh o ho), rfl⟩⟩, ?_⟩
    refine Finset.disjoint_left.mpr fun o hm ht => ?_
    exact fresh o (by simpa using hm) (takenSub o (by simpa using ht))
  · rintro ⟨⟨W', h⟩, apartMT⟩
    obtain ⟨nodupT, memT, memR, nodupM, memM, -⟩ := (commit_eq_some_iff _ _ _ W W').mp h
    refine ⟨nodupT, nodupM, ?_⟩
    refine
      { taken_subset := fun o ho => memT o (by simpa [Selection.commit] using ho)
        kept_subset := fun o ho => (memR o (by simpa [Selection.commit] using ho)).1
        apart := Finset.disjoint_left.mpr fun o ht hk =>
          (memR o (by simpa [Selection.commit] using hk)).2 (by simpa [Selection.commit] using ht)
        fresh := Finset.disjoint_left.mpr fun o hm hw => ?_
        queries_hold := by simp [Selection.commit] }
    have hm' : o ∈ s.made := by simpa [Selection.commit] using hm
    rcases memM o hm' with h | h
    · exact h hw
    · exact Finset.disjoint_left.mp apartMT (by simpa using hm') (by simpa using h)

/-- When the commit is enabled in the source sense, the operator computes `fire`. -/
theorem commit_eq_fire (label : O → R) (s : Selection O) (W : Finset O)
    (nodupT : s.taken.Nodup) (nodupM : s.made.Nodup) (enabled : Enabled label W s.commit) :
    commit s.taken s.read s.made W = some (fire W (s.commit (T := R))) := by
  obtain ⟨⟨W', h⟩, _⟩ := (enabled_iff_nonzero_and_fresh label s W).mp ⟨nodupT, nodupM, enabled⟩
  obtain ⟨-, -, -, -, -, rfl⟩ := (commit_eq_some_iff _ _ _ W W').mp h
  rw [selection_fire]
  exact h


/-- **The candidate step factors into a resource part and an information part.** A selection
is valid exactly when (shape) its port counts and made labels fit the rule, (resource) its
normal-ordered occupation operator is nonzero and no identity is both taken and made, and
(information) its joint equations are consistent and entail every check. The resulting world is
the operator's value. -/
theorem valid_iff_resource_information {T S : Type*} (A : SubstitutionAction T S)
    (s : Selection O) (label : O → T) (rule : RuleInstance T) (before : Configuration T O) :
    s.Valid A label rule before ↔
      (rule.take.length = s.taken.length ∧ rule.read.length = s.read.length ∧
          s.made.map label = rule.produce) ∧
        ((∃ W', commit s.taken s.read s.made before.present = some W') ∧
          Disjoint s.made.toFinset s.taken.toFinset) ∧
        (A.Consistent (s.problem label rule before) ∧
          ∀ check ∈ rule.checks, A.Entails (s.problem label rule before)
            (fun σ => check.Holds A σ label before.present)) := by
  constructor
  · intro v
    exact ⟨⟨v.take_length, v.read_length, v.outputs⟩,
      (enabled_iff_nonzero_and_fresh label s before.present).mp
        ⟨v.take_distinct, v.output_distinct, v.occurrences⟩,
      ⟨v.consistent, v.checks⟩⟩
  · rintro ⟨⟨takeLength, readLength, outputs⟩, resource, ⟨consistent, checks⟩⟩
    obtain ⟨nodupT, nodupM, enabled⟩ :=
      (enabled_iff_nonzero_and_fresh label s before.present).mpr resource
    exact ⟨nodupT, nodupM, takeLength, readLength, outputs, enabled, consistent, checks⟩

/-- The world after a valid step is the value of the occupation operator. -/
theorem valid_result_world {T S : Type*} (A : SubstitutionAction T S)
    (s : Selection O) (label : O → T) (rule : RuleInstance T) (before : Configuration T O)
    (v : s.Valid A label rule before) :
    commit s.taken s.read s.made before.present = some (s.result label rule before).present :=
  commit_eq_fire label s before.present v.take_distinct v.output_distinct v.occurrences
end Incumbent

/-! ## Successful partial-map reversal -/

private theorem commit_reverse_of (taken read made : List O) (W W' : Finset O)
    (h : commit taken read made W = some W') : commit made read taken W' = some W := by
  obtain ⟨nodupT, memT, memR, nodupM, memM, rfl⟩ := (commit_eq_some_iff _ _ _ W W').mp h
  refine (commit_eq_some_iff _ _ _ _ _).mpr ⟨nodupM, fun o ho => ?_, fun o ho => ?_, nodupT,
    fun o ho => ?_, ?_⟩
  · simp [ho]
  · obtain ⟨inW, notT⟩ := memR o ho
    refine ⟨by simp [inW, notT], fun hm => ?_⟩
    rcases memM o hm with h | h
    · exact h inW
    · exact notT h
  · by_cases hm : o ∈ made
    · exact Or.inr hm
    · exact Or.inl (by simp [hm, ho])
  · ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset]
    constructor
    · intro hx
      by_cases ht : x ∈ taken
      · exact Or.inr ht
      · refine Or.inl ⟨Or.inl ⟨hx, ht⟩, fun hm => ?_⟩
        rcases memM x hm with h | h
        · exact h hx
        · exact ht h
    · rintro (⟨⟨hx, -⟩ | hm, notM⟩ | ht)
      · exact hx
      · exact absurd hm notM
      · exact memT x ht

/-- The successful relation is inverted by exchanging takes and makes. Failure does not provide a predecessor. -/
theorem commit_reverse_iff (taken read made : List O) (W W' : Finset O) :
    commit taken read made W = some W' ↔ commit made read taken W' = some W :=
  ⟨commit_reverse_of taken read made W W', commit_reverse_of made read taken W' W⟩

/-! ## Controls -/

section Controls

/-- Two read ports on one row (`[7, 7]`) are accepted and keep the row. -/
example : commit ([] : List ℕ) [7, 7] [] {7} = some {7} := by decide

/-- Two take ports on one row are refused. -/
example : commit ([7, 7] : List ℕ) [] [] {7} = none := by decide

/-- A take and a read of one row are refused (the identification condition). -/
example : commit ([7] : List ℕ) [7] [] {7} = none := by decide

/-- A read cannot make the row it reads. -/
example : commit ([] : List ℕ) [7] [7] {7} = none := by decide

/-- Taking 7 and making 7 again is the read of 7 (`x∂ = N`). -/
theorem republish_same_identity_is_read :
    commit ([7] : List ℕ) [] [7] = commit [] [7] [] := by
  funext W
  by_cases h : (7 : ℕ) ∈ W
  · simp [commit, andThen, runList, one, annihilate, point, create, h, Finset.insert_erase h]
  · simp [commit, andThen, runList, one, annihilate, point, h]

/-- The same identity republished is nonzero, yet not enabled in the source sense. -/
theorem republish_same_identity_not_enabled (label : ℕ → Unit) :
    commit ([7] : List ℕ) [] [7] {7} = some {7} ∧
      ¬ Enabled label ({7} : Finset ℕ) (Selection.commit ⟨[7], [], [7]⟩) := by
  refine ⟨by decide, fun enabled => ?_⟩
  have made7 : (7 : ℕ) ∈ (Selection.commit (T := Unit) ⟨[7], [], [7]⟩).made := by
    simp [Selection.commit]
  exact Finset.disjoint_left.mp enabled.fresh made7 (by simp)

/-- E1: read before take runs; take before read does not. -/
example : andThen (commit ([] : List ℕ) [1] []) (commit [1] [] []) {1} = some ∅ := by decide
example : andThen (commit ([1] : List ℕ) [] []) (commit [] [1] []) {1} = none := by decide

/-- E4: with a reused identity only take-then-make runs. -/
example : andThen (commit ([1] : List ℕ) [] []) (commit [] [] [1]) {1} = some {1} := by decide
example : andThen (commit ([] : List ℕ) [] [1]) (commit [1] [] []) {1} = none := by decide

/-- Concurrent readers of one row commute. -/
example : andThen (point (1 : ℕ)) (point 1) = point 1 := point_twice 1

end Controls


/-! ## Guards as projectors -/

section Guards

/-- The absence guard of a region: the projector onto worlds with no row of the region. -/
def absentOn (region : Finset O) : Op O := fun W => if Disjoint region W then some W else none

/-- A run of `vacant` projectors is defined exactly where every listed row is absent. -/
theorem runList_vacant (l : List O) (W W' : Finset O) :
    runList vacant l W = some W' ↔ (∀ o ∈ l, o ∉ W) ∧ W' = W := by
  induction l generalizing W with
  | nil => simp [eq_comm]
  | cons o rest ih =>
    by_cases h : o ∈ W
    · simp [runList_cons, vacant, h]
    · simp [runList_cons, vacant, h, ih]

/-- **Absence is a product of single-mode projectors** `∏ (1 − N_o)`, in any listing. -/
theorem absentOn_eq_product (l : List O) : absentOn l.toFinset = runList vacant l := by
  funext W
  by_cases h : Disjoint l.toFinset W
  · have all : ∀ o ∈ l, o ∉ W := fun o ho => Finset.disjoint_left.mp h (by simpa using ho)
    rw [show absentOn l.toFinset W = some W from if_pos h]
    exact ((runList_vacant l W W).mpr ⟨all, rfl⟩).symm
  · rw [show absentOn l.toFinset W = none from if_neg h]
    symm
    rcases hrun : runList vacant l W with _ | W'
    · rfl
    · obtain ⟨all, -⟩ := (runList_vacant l W W').mp hrun
      exact absurd (Finset.disjoint_left.mpr fun o ho => all o (by simpa using ho)) h

/-- **Locality.** An absence guard commutes with every commit that neither takes nor makes a
row of its region; this is the operator form of the region frame law. -/
theorem absentOn_comm_commit (region : Finset O) (taken read made : List O)
    (apartT : ∀ o ∈ taken, o ∉ region) (apartM : ∀ o ∈ made, o ∉ region) :
    andThen (absentOn region) (commit taken read made) =
      andThen (commit taken read made) (absentOn region) := by
  funext W
  simp only [andThen]
  have frame : ∀ W', commit taken read made W = some W' → (Disjoint region W' ↔ Disjoint region W) := by
    intro W' h
    obtain ⟨-, -, -, -, -, rfl⟩ := (commit_eq_some_iff _ _ _ W W').mp h
    simp only [Finset.disjoint_left, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, not_or,
      not_and, not_not]
    constructor
    · intro hd o hr hw
      exact apartT o ((hd hr).1 hw) hr
    · intro hd o hr
      exact ⟨fun hw => absurd hw (hd hr), fun hm => apartM o hm hr⟩
  by_cases hd : Disjoint region W
  · rw [show absentOn region W = some W from if_pos hd, Option.bind_some]
    rcases hc : commit taken read made W with _ | W'
    · rfl
    · simp only [Option.bind_some, absentOn, (frame W' hc).mpr hd, if_true]
  · rw [show absentOn region W = none from if_neg hd, Option.bind_none]
    rcases hc : commit taken read made W with _ | W'
    · rfl
    · simp only [Option.bind_some, absentOn]
      rw [if_neg (fun h => hd ((frame W' hc).mp h))]

/-- E5 (producer `P` of row 1, taker `C` of row 1, absence guard `G` of row 1, from the empty
world): `G;P;C` and `P;C;G` run, `P;G;C` does not, and `G` commutes with neither `P` nor `C`. -/
theorem e5_words :
    andThen (andThen (absentOn ({1} : Finset ℕ)) (commit [] [] [1])) (commit [1] [] []) ∅ = some ∅ ∧
    andThen (andThen (commit ([] : List ℕ) [] [1]) (commit [1] [] [])) (absentOn {1}) ∅ = some ∅ ∧
    andThen (andThen (commit ([] : List ℕ) [] [1]) (absentOn {1})) (commit [1] [] []) ∅ = none ∧
    andThen (absentOn ({1} : Finset ℕ)) (commit [] [] [1]) ∅ ≠
      andThen (commit ([] : List ℕ) [] [1]) (absentOn {1}) ∅ ∧
    andThen (absentOn ({1} : Finset ℕ)) (commit [1] [] []) {1} ≠
      andThen (commit ([1] : List ℕ) [] []) (absentOn {1}) {1} := by
  decide

end Guards

/-! ## Pointwise decomposition into one-bit operators -/

section Modes

/-- Take, read and make on one occupation bit. -/
def bitTake : Bool → Option Bool
  | true => some false
  | false => none

def bitRead : Bool → Option Bool
  | true => some true
  | false => none

def bitMake : Bool → Option Bool
  | false => some true
  | true => none

/-- `n` copies of a bit operator in sequence. -/
def bitIter (f : Bool → Option Bool) : ℕ → Bool → Option Bool
  | 0, b => some b
  | n + 1, b => (f b).bind (bitIter f n)

@[simp] theorem bitIter_zero (f : Bool → Option Bool) (b : Bool) : bitIter f 0 b = some b := rfl

@[simp] theorem bitIter_take_one (b : Bool) : bitIter bitTake 1 b = bitTake b := by
  cases b <;> rfl

@[simp] theorem bitIter_take_two (n : ℕ) (b : Bool) : bitIter bitTake (n + 2) b = none := by
  cases b <;> simp [bitIter, bitTake]

@[simp] theorem bitIter_read_succ (n : ℕ) (b : Bool) : bitIter bitRead (n + 1) b = bitRead b := by
  induction n generalizing b with
  | zero => cases b <;> rfl
  | succ n ih => cases b <;> simp_all [bitIter, bitRead]

@[simp] theorem bitIter_make_one (b : Bool) : bitIter bitMake 1 b = bitMake b := by
  cases b <;> rfl

@[simp] theorem bitIter_make_two (n : ℕ) (b : Bool) : bitIter bitMake (n + 2) b = none := by
  cases b <;> simp [bitIter, bitMake]

/-- The action on one mode that `ct` takes, `cr` reads and `cm` makes of it have. -/
def modeBits (ct cr cm : ℕ) (b : Bool) : Option Bool :=
  ((bitIter bitTake ct b).bind (bitIter bitRead cr)).bind (bitIter bitMake cm)

/-- The one-mode law, in full. -/
theorem modeBits_eq_some (ct cr cm : ℕ) (b b' : Bool) :
    modeBits ct cr cm b = some b' ↔
      ct ≤ 1 ∧ cm ≤ 1 ∧ (0 < ct → b = true) ∧ (0 < cr → b = true ∧ ct = 0) ∧
        (0 < cm → b = false ∨ 0 < ct) ∧ b' = ((b && decide (ct = 0)) || decide (0 < cm)) := by
  rcases ct with _ | _ | ct <;> rcases cr with _ | cr <;> rcases cm with _ | _ | cm <;>
    cases b <;> cases b' <;> simp [modeBits, bitTake, bitRead, bitMake]

/-- The action of a commit on the mode of `o`. -/
def modeAction (taken read made : List O) (o : O) : Bool → Option Bool :=
  modeBits (taken.count o) (read.count o) (made.count o)

/-- **The commit factors over modes**: it is defined exactly when every identity's own
one-bit action is defined, and then each bit moves as that action says. -/
theorem commit_eq_some_iff_modes (taken read made : List O) (W W' : Finset O) :
    commit taken read made W = some W' ↔
      ∀ o, modeAction taken read made o (decide (o ∈ W)) = some (decide (o ∈ W')) := by
  rw [commit_eq_some_iff]
  simp only [modeAction, modeBits_eq_some]
  constructor
  · rintro ⟨nodupT, memT, memR, nodupM, memM, rfl⟩ o
    refine ⟨List.nodup_iff_count_le_one.mp nodupT o, List.nodup_iff_count_le_one.mp nodupM o,
      fun h => decide_eq_true (memT o (List.count_pos_iff.mp h)), fun h => ?_, fun h => ?_, ?_⟩
    · obtain ⟨inW, notT⟩ := memR o (List.count_pos_iff.mp h)
      exact ⟨decide_eq_true inW, List.count_eq_zero.mpr notT⟩
    · rcases memM o (List.count_pos_iff.mp h) with notW | inT
      · exact Or.inl (decide_eq_false notW)
      · exact Or.inr (List.count_pos_iff.mpr inT)
    · by_cases inT : o ∈ taken <;> by_cases inM : o ∈ made <;> by_cases inW : o ∈ W <;>
        simp [inT, inM, inW, List.count_eq_zero, List.count_pos_iff]
  · intro h
    have nodupT : taken.Nodup := List.nodup_iff_count_le_one.mpr fun o => (h o).1
    have nodupM : made.Nodup := List.nodup_iff_count_le_one.mpr fun o => (h o).2.1
    refine ⟨nodupT, fun o ho => ?_, fun o ho => ?_, nodupM, fun o ho => ?_, ?_⟩
    · exact of_decide_eq_true ((h o).2.2.1 (List.count_pos_iff.mpr ho))
    · obtain ⟨inW, zero⟩ := (h o).2.2.2.1 (List.count_pos_iff.mpr ho)
      exact ⟨of_decide_eq_true inW, List.count_eq_zero.mp zero⟩
    · rcases (h o).2.2.2.2.1 (List.count_pos_iff.mpr ho) with notW | inT
      · exact Or.inl (of_decide_eq_false notW)
      · exact Or.inr (List.count_pos_iff.mp inT)
    · ext o
      have bit := (h o).2.2.2.2.2
      by_cases inT : o ∈ taken <;> by_cases inM : o ∈ made <;> by_cases inW : o ∈ W <;>
        by_cases inW' : o ∈ W' <;>
        simp_all [List.count_eq_zero, List.count_pos_iff]

/-- A run of commits, given as `(taken, read, made)` triples. -/
def runs : List (List O × List O × List O) → Op O
  | [] => one
  | (t, r, m) :: rest => andThen (commit t r m) (runs rest)

/-- The run of one mode. -/
def modeRun : List (List O × List O × List O) → O → Bool → Option Bool
  | [], _, b => some b
  | (t, r, m) :: rest, o, b => (modeAction t r m o b).bind (modeRun rest o)

/-- The value a defined one-mode action gives: kept unless taken, set if made. -/
theorem modeAction_value {t r m : List O} {o : O} {b b' : Bool}
    (h : modeAction t r m o b = some b') :
    b' = ((b && decide (t.count o = 0)) || decide (0 < m.count o)) :=
  ((modeBits_eq_some _ _ _ b b').mp h).2.2.2.2.2

/-- **A run is decided occurrence by occurrence.** A sequence of commits is defined from `W`
and ends in `W'` exactly when, for every identity, its own one-bit word is defined from its
initial occupation and ends in its final occupation. -/
theorem runs_eq_some_iff_modes (cs : List (List O × List O × List O)) (W W' : Finset O) :
    runs cs W = some W' ↔ ∀ o, modeRun cs o (decide (o ∈ W)) = some (decide (o ∈ W')) := by
  induction cs generalizing W with
  | nil =>
    simp only [runs, one, modeRun, Option.some.injEq]
    constructor
    · rintro rfl o
      rfl
    · intro h
      ext o
      have := h o
      by_cases a : o ∈ W <;> by_cases b : o ∈ W' <;> simp_all
  | cons c rest ih =>
    obtain ⟨t, r, m⟩ := c
    simp only [runs, modeRun, andThen]
    constructor
    · intro h o
      obtain ⟨W₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      rw [(commit_eq_some_iff_modes t r m W W₁).mp h₁ o, Option.bind_some]
      exact (ih W₁).mp h₂ o
    · intro h
      let W₁ : Finset O := (W \ t.toFinset) ∪ m.toFinset
      have step : ∀ o, modeAction t r m o (decide (o ∈ W)) = some (decide (o ∈ W₁)) := by
        intro o
        obtain ⟨b₁, h₁, -⟩ := Option.bind_eq_some_iff.mp (h o)
        rw [h₁, modeAction_value h₁]
        by_cases inT : o ∈ t <;> by_cases inM : o ∈ m <;> by_cases inW : o ∈ W <;>
          simp [W₁, inT, inM, inW, List.count_eq_zero, List.count_pos_iff]
      have rest' : ∀ o, modeRun rest o (decide (o ∈ W₁)) = some (decide (o ∈ W')) := by
        intro o
        have := h o
        rw [step o, Option.bind_some] at this
        exact this
      rw [(commit_eq_some_iff_modes t r m W W₁).mpr step, Option.bind_some]
      exact (ih W₁).mpr rest'

/-- Two runs with the same one-mode words are the same operator. -/
theorem runs_eq_of_modes {cs ds : List (List O × List O × List O)}
    (h : ∀ o, modeRun cs o = modeRun ds o) : runs cs = runs ds := by
  funext W
  rcases hc : runs cs W with _ | W'
  · rcases hd : runs ds W with _ | W''
    · rfl
    · have := (runs_eq_some_iff_modes ds W W'').mp hd
      simp only [← h] at this
      rw [(runs_eq_some_iff_modes cs W W'').mpr this] at hc
      exact absurd hc (by simp)
  · have := (runs_eq_some_iff_modes cs W W').mp hc
    simp only [h] at this
    exact ((runs_eq_some_iff_modes ds W W').mpr this).symm

/-- The swap law: two commits that share no identity except as reads commute. -/
theorem commits_comm_of_shared_reads_only (c d : List O × List O × List O)
    (apart : ∀ o, (c.1.count o = 0 ∧ c.2.1.count o = 0 ∧ c.2.2.count o = 0) ∨
      (d.1.count o = 0 ∧ d.2.1.count o = 0 ∧ d.2.2.count o = 0) ∨
      (c.1.count o = 0 ∧ c.2.2.count o = 0 ∧ d.1.count o = 0 ∧ d.2.2.count o = 0)) :
    runs [c, d] = runs [d, c] := by
  apply runs_eq_of_modes
  intro o
  funext b
  obtain ⟨ct, cr, cm⟩ := c
  obtain ⟨dt, dr, dm⟩ := d
  simp only [modeRun, modeAction, modeBits] at apart ⊢
  rcases apart o with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]
  · rw [h1, h2, h3, h4]
    rcases (cr.count o) with _ | k <;> rcases (dr.count o) with _ | l <;> cases b <;>
      simp [bitRead]

end Modes
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupation
