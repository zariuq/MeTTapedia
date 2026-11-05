import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsCollapse
import Mathlib.Data.Set.Finite.List

/-!
# MM2 `exec` as one firing computed from a complete snapshot

The reference is MORK's documented execution rule on ground stored atoms. The
space is a set. The exec atom is removed before it is interpreted. One step
enumerates every row of its sources against that snapshot. The kernel writes
every `+` instance, then subtracts every `-` instance; a removal of an absent
instance does nothing, and an instance removed or added by several rows is
removed or added once. The MORK binary and both CeTTa `mm2` lanes agree on
the nine probes recorded with this file.

* `Result`: the reference step, as a characterization of the next space.
* `exec_firing_adequacy`: given the snapshot's instance lists, one ordinary
  ground firing (take the exec occurrence and the present removal targets,
  produce the new add instances) is valid and leaves exactly the reference
  space, again represented without duplicate labels.
* `exec_is_one_firing`: when every template variable occurs in a source, the
  instance sets are finite, so with an occurrence supply those lists exist and
  the step is always one firing.
* `Probe`: the reference reproduces the MORK outputs of probes p1, p2, p3 and
  p5, and the firing realizes p5.
* `Probe.row_protocol_refuses_overlap`: firing p5 one row at a time fails. The
  second row's removal of `(c)` has no occurrence left to take.
* `Probe.row_protocol_duplicates`: firing p1 one row at a time leaves two
  occurrences of `(b)`; a set space has one.

The completeness of the row list is not certified by the firing:
`MeTTaOperationsCollapse.validity_never_certifies_completeness` applies to it.
The snapshot and the firing must be one atomic observation-and-commit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsExec

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)

/-! ## The reference step -/

/-- An exec atom with its comma sources and its `+` and `-` sinks. -/
structure Exec where
  self : Atom
  sources : List Atom
  adds : List Atom
  removes : List Atom

/-- A row: one substitution matching every source against the snapshot,
from which the exec atom has already been removed. -/
def Row (space : Finset Atom) (exec : Exec) (σ : Subst) : Prop :=
  ∀ p ∈ exec.sources, subst σ p ∈ space.erase exec.self

def AddInst (space : Finset Atom) (exec : Exec) (a : Atom) : Prop :=
  ∃ σ, Row space exec σ ∧ ∃ t ∈ exec.adds, subst σ t = a

def RemoveInst (space : Finset Atom) (exec : Exec) (a : Atom) : Prop :=
  ∃ σ, Row space exec σ ∧ ∃ t ∈ exec.removes, subst σ t = a

/-- The kernel's step: consume the exec atom, write every row's additions,
then subtract every row's removals. -/
def Result (space : Finset Atom) (exec : Exec) (result : Finset Atom) : Prop :=
  ∀ a, a ∈ result ↔ ((a ∈ space ∧ a ≠ exec.self) ∨ AddInst space exec a) ∧ ¬ RemoveInst space exec a

theorem result_unique {space : Finset Atom} {exec : Exec} {first second : Finset Atom}
    (one : Result space exec first) (two : Result space exec second) : first = second := by
  ext a
  rw [one a, two a]

/-! ## One ground firing -/

variable {O : Type*} [DecidableEq O]

omit [DecidableEq O] in
theorem equations_self (label : O → Atom) (selected : List O) :
    Selection.equations label (selected.map label) selected = selected.map fun o => (label o, label o) := by
  induction selected with
  | nil => rfl
  | cons o rest ih =>
    simp only [Selection.equations, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

/-- The ground rule instance of one exec step. -/
def stepRule (label : O → Atom) (taken : List O) (added : List Atom) : RuleInstance Atom :=
  ⟨taken.map label, [], [], [], added⟩

def stepSelection (taken made : List O) : Selection O := ⟨taken, [], made⟩

/-- **Adequacy of MM2 `exec`.** With the snapshot's removal targets and new
add instances listed, one ordinary firing realizes the reference step on a
duplicate-free representation, and the result is duplicate-free again. -/
theorem exec_firing_adequacy {label : O → Atom} {before : Configuration Atom O}
    {space : Finset Atom} {exec : Exec}
    (represents : before.present.image label = space) (injective : Set.InjOn label before.present)
    {selfOcc : O} (selfPresent : selfOcc ∈ before.present) (selfLabel : label selfOcc = exec.self)
    {removed : List O} (removedNodup : removed.Nodup)
    (removedSpec : ∀ o, o ∈ removed ↔ o ∈ before.present ∧ o ≠ selfOcc ∧ RemoveInst space exec (label o))
    {added : List Atom} {made : List O} (madeNodup : made.Nodup)
    (madeFresh : ∀ m ∈ made, m ∉ before.present) (madeLabels : made.map label = added)
    (addedNodup : added.Nodup)
    (addedSpec : ∀ a, a ∈ added ↔
      AddInst space exec a ∧ ¬ RemoveInst space exec a ∧ a ∉ space.erase exec.self)
    (base : atomAction.Consistent before.equations) :
    (stepSelection (selfOcc :: removed) made).Valid atomAction label
        (stepRule label (selfOcc :: removed) added) before ∧
      Result space exec (((stepSelection (selfOcc :: removed) made).result label
        (stepRule label (selfOcc :: removed) added) before).present.image label) ∧
      Set.InjOn label ((stepSelection (selfOcc :: removed) made).result label
        (stepRule label (selfOcc :: removed) added) before).present := by
  classical
  have selfNotRemoved : selfOcc ∉ removed := fun member => ((removedSpec selfOcc).mp member).2.1 rfl
  have takenPresent : ∀ o ∈ selfOcc :: removed, o ∈ before.present := by
    intro o member
    rcases List.mem_cons.mp member with rfl | member
    · exact selfPresent
    · exact ((removedSpec o).mp member).1
  have valid : (stepSelection (selfOcc :: removed) made).Valid atomAction label
      (stepRule label (selfOcc :: removed) added) before := by
    refine ⟨List.nodup_cons.mpr ⟨selfNotRemoved, removedNodup⟩, madeNodup, by simp [stepRule, stepSelection],
      rfl, madeLabels, ?_, ?_, ?_⟩
    · refine ⟨?_, by simp [Selection.commit, stepSelection], by simp [Selection.commit, stepSelection], ?_, ?_⟩
      · intro o member
        exact takenPresent o (by simpa [Selection.commit, stepSelection] using member)
      · rw [Finset.disjoint_left]
        intro m member
        exact madeFresh m (by simpa [Selection.commit, stepSelection] using member)
      · intro query member
        simp [Selection.commit] at member
    · obtain ⟨σ, solved⟩ := base
      refine ⟨σ, ?_⟩
      intro e member
      have noReads : Selection.equations label ([] : List Atom) ([] : List O) = [] := rfl
      simp only [Selection.problem, stepRule, stepSelection, equations_self, noReads, List.append_nil,
        List.mem_append, List.mem_map] at member
      rcases member with old | ⟨o, _, rfl⟩
      · exact solved e old
      · rfl
    · intro check member
      simp [stepRule] at member
  refine ⟨valid, ?_, ?_⟩
  · intro a
    simp only [Selection.result, fire, Selection.commit, stepSelection, Finset.mem_image,
      Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset]
    constructor
    · rintro ⟨o, ((present | made') ), rfl⟩
      · obtain ⟨present, notTaken⟩ := present
        have notSelf : o ≠ selfOcc := fun same => notTaken (same ▸ List.mem_cons_self)
        have notRemoved : o ∉ removed := fun member => notTaken (List.mem_cons_of_mem _ member)
        refine ⟨.inl ⟨represents ▸ Finset.mem_image_of_mem label present, ?_⟩, ?_⟩
        · intro same
          exact notSelf (injective present selfPresent (same.trans selfLabel.symm))
        · intro removes
          exact notRemoved ((removedSpec o).mpr ⟨present, notSelf, removes⟩)
      · have inAdded : label o ∈ added := madeLabels ▸ List.mem_map_of_mem made'
        obtain ⟨adds, notRemoves, _⟩ := (addedSpec (label o)).mp inAdded
        exact ⟨.inr adds, notRemoves⟩
    · rintro ⟨kept | adds, notRemoves⟩
      · obtain ⟨inSpace, notSelf⟩ := kept
        rw [← represents, Finset.mem_image] at inSpace
        obtain ⟨o, present, rfl⟩ := inSpace
        refine ⟨o, .inl ⟨present, ?_⟩, rfl⟩
        intro taken
        rcases List.mem_cons.mp taken with rfl | removedMember
        · exact notSelf selfLabel
        · exact notRemoves ((removedSpec o).mp removedMember).2.2
      · by_cases old : a ∈ space.erase exec.self
        · obtain ⟨notSelf, inSpace⟩ := Finset.mem_erase.mp old
          rw [← represents, Finset.mem_image] at inSpace
          obtain ⟨o, present, rfl⟩ := inSpace
          refine ⟨o, .inl ⟨present, ?_⟩, rfl⟩
          intro taken
          rcases List.mem_cons.mp taken with rfl | removedMember
          · exact notSelf selfLabel
          · exact notRemoves ((removedSpec o).mp removedMember).2.2
        · have inAdded : a ∈ added := (addedSpec a).mpr ⟨adds, notRemoves, old⟩
          rw [← madeLabels] at inAdded
          obtain ⟨m, madeMember, rfl⟩ := List.mem_map.mp inAdded
          exact ⟨m, .inr madeMember, rfl⟩
  · intro first firstMember second secondMember same
    simp only [Selection.result, fire, Selection.commit, stepSelection, Finset.coe_union,
      Finset.coe_sdiff, Set.mem_union, Set.mem_sdiff, Finset.mem_coe, List.mem_toFinset] at firstMember secondMember
    have oldLabel : ∀ o, o ∈ before.present → o ∉ selfOcc :: removed → label o ∈ space.erase exec.self := by
      intro o present notTaken
      refine Finset.mem_erase.mpr ⟨?_, represents ▸ Finset.mem_image_of_mem label present⟩
      intro same
      exact notTaken (List.mem_cons.mpr (.inl (injective present selfPresent (same.trans selfLabel.symm))))
    have madeLabel : ∀ m ∈ made, label m ∉ space.erase exec.self := by
      intro m member
      have inAdded : label m ∈ added := madeLabels ▸ List.mem_map_of_mem member
      exact ((addedSpec (label m)).mp inAdded).2.2
    rcases firstMember with ⟨firstPresent, firstKept⟩ | firstMade <;>
      rcases secondMember with ⟨secondPresent, secondKept⟩ | secondMade
    · exact injective firstPresent secondPresent same
    · exact absurd (same ▸ oldLabel first firstPresent firstKept) (madeLabel second secondMade)
    · exact absurd (same.symm ▸ oldLabel second secondPresent secondKept) (madeLabel first firstMade)
    · exact List.inj_on_of_nodup_map (madeLabels ▸ addedNodup) firstMade secondMade same

/-! ## The snapshot lists exist -/

/-- Every variable of the templates occurs in a source. -/
def Covered (exec : Exec) : Prop :=
  ∀ t ∈ exec.adds ++ exec.removes, ∀ v ∈ vars t, ∃ p ∈ exec.sources, v ∈ vars p

/-- A substitution realizing a tuple of source values, when one exists. -/
noncomputable def chosen (exec : Exec) (values : List Atom) : Subst := by
  classical
  exact if h : ∃ σ : Subst, exec.sources.map (subst σ) = values then Classical.choose h else empty

theorem chosen_spec {exec : Exec} {values : List Atom}
    (h : ∃ σ : Subst, exec.sources.map (subst σ) = values) :
    exec.sources.map (subst (chosen exec values)) = values := by
  classical
  unfold chosen
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- A covered template's instance depends only on the row's source values. -/
theorem instance_of_row {exec : Exec} (covered : Covered exec) {t : Atom}
    (template : t ∈ exec.adds ++ exec.removes) (σ : Subst) :
    subst σ t = subst (chosen exec (exec.sources.map (subst σ))) t := by
  have spec := chosen_spec (exec := exec) ⟨σ, rfl⟩
  apply (subst_eq_iff_on_vars _ _ t).mpr
  intro v member
  obtain ⟨p, source, inside⟩ := covered t template v member
  have same : subst σ p = subst (chosen exec (exec.sources.map (subst σ))) p := by
    exact ((List.map_inj_left.mp spec) p source).symm
  exact (subst_eq_iff_on_vars _ _ p).mp same v inside

/-- The tuples of source values that rows can produce. -/
theorem rows_values_finite (space : Finset Atom) (exec : Exec) :
    {values : List Atom | values.length = exec.sources.length ∧ ∀ value ∈ values, value ∈ space.erase exec.self}.Finite := by
  classical
  have base := List.finite_length_eq (space.erase exec.self) exec.sources.length
  refine (base.image (List.map Subtype.val)).subset ?_
  intro values ⟨length, inside⟩
  refine ⟨values.attach.map fun entry => ⟨entry.1, inside entry.1 entry.2⟩, by simp [length], ?_⟩
  simp [List.map_map, Function.comp_def]

/-- The instances of a covered template list over all rows form a finite set. -/
theorem instances_finite (space : Finset Atom) (exec : Exec) (covered : Covered exec)
    (templates : List Atom) (within : ∀ t ∈ templates, t ∈ exec.adds ++ exec.removes) :
    {a | ∃ σ, Row space exec σ ∧ ∃ t ∈ templates, subst σ t = a}.Finite := by
  classical
  refine ((rows_values_finite space exec).prod (templates.finite_toSet)).image
    (fun pair => subst (chosen exec pair.1) pair.2) |>.subset ?_
  rintro a ⟨σ, row, t, member, rfl⟩
  refine ⟨(exec.sources.map (subst σ), t), ⟨⟨by simp, ?_⟩, member⟩, ?_⟩
  · intro value inside
    obtain ⟨p, source, rfl⟩ := List.mem_map.mp inside
    exact row p source
  · exact (instance_of_row covered (within t member) σ).symm

theorem addInst_finite (space : Finset Atom) (exec : Exec) (covered : Covered exec) :
    {a | AddInst space exec a}.Finite :=
  instances_finite space exec covered exec.adds (fun _ member => List.mem_append_left _ member)

/-- Fresh occurrences with any listed labels, given an occurrence supply. -/
theorem fresh_occurrences {label : O → Atom}
    (supply : ∀ (avoid : Finset O) (a : Atom), ∃ m, m ∉ avoid ∧ label m = a) :
    ∀ (atoms : List Atom) (avoid : Finset O),
      ∃ made : List O, made.Nodup ∧ (∀ m ∈ made, m ∉ avoid) ∧ made.map label = atoms
  | [], _ => ⟨[], List.nodup_nil, by simp, rfl⟩
  | a :: rest, avoid => by
    classical
    obtain ⟨made, nodup, fresh, labels⟩ := fresh_occurrences supply rest avoid
    obtain ⟨m, notIn, labelled⟩ := supply (avoid ∪ made.toFinset) a
    refine ⟨m :: made, ?_, ?_, by simp [labelled, labels]⟩
    · refine List.nodup_cons.mpr ⟨fun member => notIn ?_, nodup⟩
      simp [member]
    · intro o member
      rcases List.mem_cons.mp member with rfl | member
      · exact fun inside => notIn (Finset.mem_union_left _ inside)
      · exact fresh o member

/-- **MM2 `exec` is one firing.** For a covered exec over a duplicate-free
ground representation with an occurrence supply, the snapshot lists exist and
the one ground firing they determine realizes the reference step. -/
theorem exec_is_one_firing {label : O → Atom} {before : Configuration Atom O}
    {space : Finset Atom} {exec : Exec} (covered : Covered exec)
    (represents : before.present.image label = space) (injective : Set.InjOn label before.present)
    {selfOcc : O} (selfPresent : selfOcc ∈ before.present) (selfLabel : label selfOcc = exec.self)
    (supply : ∀ (avoid : Finset O) (a : Atom), ∃ m, m ∉ avoid ∧ label m = a)
    (base : atomAction.Consistent before.equations) :
    ∃ removed : List O, ∃ added : List Atom, ∃ made : List O,
      (stepSelection (selfOcc :: removed) made).Valid atomAction label
          (stepRule label (selfOcc :: removed) added) before ∧
        Result space exec (((stepSelection (selfOcc :: removed) made).result label
          (stepRule label (selfOcc :: removed) added) before).present.image label) := by
  classical
  let removedSet := before.present.filter fun o => o ≠ selfOcc ∧ RemoveInst space exec (label o)
  let addedSet := (addInst_finite space exec covered).toFinset.filter fun a =>
    ¬ RemoveInst space exec a ∧ a ∉ space.erase exec.self
  obtain ⟨made, madeNodup, madeFresh, madeLabels⟩ :=
    fresh_occurrences supply addedSet.toList before.present
  refine ⟨removedSet.toList, addedSet.toList, made, ?_⟩
  obtain ⟨valid, reference, _⟩ := exec_firing_adequacy (removed := removedSet.toList)
    (added := addedSet.toList) (made := made) represents injective selfPresent selfLabel
    (Finset.nodup_toList _) (by intro o; simp [removedSet]) madeNodup madeFresh madeLabels
    (Finset.nodup_toList _) (by intro a; simp [addedSet]) base
  exact ⟨valid, reference⟩

/-! ## The probes -/

namespace Probe

def one : Atom := .symbol "1"
def two : Atom := .symbol "2"
def x : Atom := .var "x"
def pair (head : String) (value : Atom) : Atom := Insertion.wrap head value
def unit (head : String) : Atom := .expression [.symbol head]

theorem pair_inj {head : String} {first second : Atom} (same : pair head first = pair head second) :
    first = second := by
  simpa [pair, Insertion.wrap] using same

theorem pair_ne_pair {first second : String} (different : first ≠ second) (a b : Atom) :
    pair first a ≠ pair second b := by
  simp [pair, Insertion.wrap, different]

theorem pair_ne_unit (head other : String) (value : Atom) : pair head value ≠ unit other := by
  simp [pair, unit, Insertion.wrap]

theorem pair_ne_symbol (head other : String) (value : Atom) : pair head value ≠ .symbol other := by
  simp [pair, Insertion.wrap]

theorem subst_pair (σ : Subst) (head : String) (value : Atom) :
    subst σ (pair head value) = pair head (subst σ value) := Insertion.subst_wrap σ head value

theorem subst_ground_unit (σ : Subst) (head : String) : subst σ (unit head) = unit head := rfl

theorem subst_one (σ : Subst) : subst σ one = one := rfl

theorem subst_two (σ : Subst) : subst σ two = two := rfl

theorem single_x (value : Atom) : subst (Insertion.single "x" value) x = value := by
  simp [x]


/-- Rows of one source `(h $x)` whose instances in the snapshot are `(h 1)` and `(h 2)`. -/
theorem row_values {space : Finset Atom} {exec : Exec} {head : String}
    (sources : exec.sources = [pair head x])
    (members : ∀ v, pair head v ∈ space.erase exec.self ↔ v = one ∨ v = two) (σ : Subst) :
    Row space exec σ ↔ subst σ x = one ∨ subst σ x = two := by
  unfold Row
  rw [sources]
  simp only [List.mem_singleton, forall_eq, subst_pair]
  exact members (subst σ x)

/-! ### p5: overlapping removals -/

def c : Atom := unit "c"
def self5 : Atom := .symbol "exec-p5"
def space5 : Finset Atom := {pair "a" one, pair "a" two, c, self5}
def exec5 : Exec := ⟨self5, [pair "a" x], [pair "r" x], [c]⟩

theorem members5 (v : Atom) : pair "a" v ∈ space5.erase exec5.self ↔ v = one ∨ v = two := by
  simp only [exec5, space5, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, same | same | same | same⟩
    · exact .inl (pair_inj same)
    · exact .inr (pair_inj same)
    · exact absurd same (pair_ne_unit "a" "c" v)
    · exact absurd same (pair_ne_symbol "a" "exec-p5" v)
  · rintro (rfl | rfl)
    · exact ⟨pair_ne_symbol _ _ _, .inl rfl⟩
    · exact ⟨pair_ne_symbol _ _ _, .inr (.inl rfl)⟩

theorem add5 (a : Atom) : AddInst space5 exec5 a ↔ a = pair "r" one ∨ a = pair "r" two := by
  constructor
  · rintro ⟨σ, row, t, member, rfl⟩
    simp only [exec5, List.mem_singleton] at member
    subst member
    rw [subst_pair]
    rcases (row_values rfl members5 σ).mp row with value | value <;> rw [value]
    · exact .inl rfl
    · exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Insertion.single "x" one, (row_values rfl members5 _).mpr (.inl (single_x one)),
        pair "r" x, by simp [exec5], by rw [subst_pair, single_x]⟩
    · exact ⟨Insertion.single "x" two, (row_values rfl members5 _).mpr (.inr (single_x two)),
        pair "r" x, by simp [exec5], by rw [subst_pair, single_x]⟩

theorem remove5 (a : Atom) : RemoveInst space5 exec5 a ↔ a = c := by
  constructor
  · rintro ⟨σ, _, t, member, rfl⟩
    simp only [exec5, List.mem_singleton] at member
    subst member
    rfl
  · rintro rfl
    exact ⟨Insertion.single "x" one, (row_values rfl members5 _).mpr (.inl (single_x one)), c,
      by simp [exec5], rfl⟩

def result5 : Finset Atom := {pair "a" one, pair "a" two, pair "r" one, pair "r" two}

/-- MORK, the CeTTa draft and main CeTTa print `(a 1) (a 2) (r 1) (r 2)` for p5. -/
theorem result5_reference : Result space5 exec5 result5 := by
  intro a
  rw [add5, remove5]
  simp only [result5, space5, exec5, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl) <;> decide
  · rintro ⟨(⟨rfl | rfl | rfl | rfl, notSelf⟩ | rfl | rfl), notC⟩
    all_goals first
      | decide
      | exact absurd rfl notC
      | exact absurd rfl notSelf

def label5 (n : Nat) : Atom :=
  if n = 0 then pair "a" one else if n = 1 then pair "a" two else if n = 2 then c
  else if n = 3 then self5 else if n = 4 then pair "r" one else pair "r" two

def before5 : Configuration Atom Nat := ⟨[], {0, 1, 2, 3}⟩

theorem represents5 : before5.present.image label5 = space5 := by decide

theorem injective5 : Set.InjOn label5 before5.present := by
  intro first firstMember second secondMember same
  simp only [before5, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at firstMember secondMember
  rcases firstMember with rfl | rfl | rfl | rfl <;> rcases secondMember with rfl | rfl | rfl | rfl <;>
    first | rfl | exact absurd same (by decide)

theorem removed5 (o : Nat) :
    o ∈ [2] ↔ o ∈ before5.present ∧ o ≠ 3 ∧ RemoveInst space5 exec5 (label5 o) := by
  rw [remove5]
  constructor
  · intro member
    simp only [List.mem_singleton] at member
    subst member
    decide
  · rintro ⟨present, notSelf, labelled⟩
    simp only [before5, Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl | rfl
    · exact absurd labelled (by decide)
    · exact absurd labelled (by decide)
    · simp
    · exact absurd rfl notSelf

theorem added5 (a : Atom) : a ∈ [pair "r" one, pair "r" two] ↔
    AddInst space5 exec5 a ∧ ¬ RemoveInst space5 exec5 a ∧ a ∉ space5.erase exec5.self := by
  rw [add5, remove5]
  constructor
  · intro member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · rintro ⟨adds, _, _⟩
    rcases adds with rfl | rfl <;> simp

/-- **p5 as one firing.** Take the exec occurrence and `(c)`, produce `(r 1)`
and `(r 2)`: the result is the reference space and MORK's output. -/
theorem p5_one_firing :
    (stepSelection [3, 2] [4, 5]).Valid atomAction label5
        (stepRule label5 [3, 2] [pair "r" one, pair "r" two]) before5 ∧
      ((stepSelection [3, 2] [4, 5]).result label5
        (stepRule label5 [3, 2] [pair "r" one, pair "r" two]) before5).present.image label5 = result5 := by
  obtain ⟨valid, reference, _⟩ := exec_firing_adequacy (label := label5) (before := before5)
    (exec := exec5) represents5 injective5 (selfOcc := 3) (by decide) rfl (removed := [2]) (by decide)
    removed5 (made := [4, 5]) (by decide) (by decide) rfl (by decide) added5
    ⟨empty, by intro e member; simp [before5] at member⟩
  exact ⟨valid, result_unique reference result5_reference⟩

/-- Row `x = k` alone: read `(a k)`, take `(c)`, produce `(r k)`. -/
def rowRule5 (k : Atom) : RuleInstance Atom := ⟨[c], [pair "a" k], [], [], [pair "r" k]⟩

def firstRow : Selection Nat := ⟨[2], [0], [4]⟩

def afterRow1 : Configuration Atom Nat := firstRow.result label5 (rowRule5 one) before5

theorem row1_valid : firstRow.Valid atomAction label5 (rowRule5 one) before5 := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨empty, ?_⟩, ?_⟩
  · intro e member
    simp only [Selection.problem, Selection.equations, rowRule5, firstRow, before5, List.nil_append,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [rowRule5] at member

theorem afterRow1_present : afterRow1.present = {0, 1, 3, 4} := by decide

theorem ground5 (n : Nat) : vars (label5 n) = [] := by
  unfold label5
  split_ifs <;> rfl

/-- **Separation.** After the first row takes `(c)`, no occurrence carries
`(c)`: no selection fires the second row. MM2 removes `(c)` once and keeps
both rows. -/
theorem row_protocol_refuses_overlap (selection : Selection Nat) :
    ¬ selection.Valid atomAction label5 (rowRule5 two) afterRow1 := by
  intro valid
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp valid.take_length.symm
  have present : o ∈ afterRow1.present :=
    valid.occurrences.taken_subset (by simp [Selection.commit, taken])
  obtain ⟨σ, solved⟩ := valid.consistent
  have equation := solved (c, label5 o) (by simp [Selection.problem, Selection.equations, rowRule5, taken])
  change subst σ c = subst σ (label5 o) at equation
  rw [subst_of_vars_eq_nil σ c rfl, subst_of_vars_eq_nil σ (label5 o) (ground5 o)] at equation
  rw [afterRow1_present] at present
  simp only [Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl | rfl <;> exact absurd equation (by decide)

/-! ### p1: one addition reached by two rows -/

def b : Atom := unit "b"
def self1 : Atom := .symbol "exec-p1"
def space1 : Finset Atom := {pair "a" one, pair "a" two, self1}
def exec1 : Exec := ⟨self1, [pair "a" x], [b], []⟩
def result1 : Finset Atom := {pair "a" one, pair "a" two, b}

theorem members1 (v : Atom) : pair "a" v ∈ space1.erase exec1.self ↔ v = one ∨ v = two := by
  simp only [exec1, space1, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, same | same | same⟩
    · exact .inl (pair_inj same)
    · exact .inr (pair_inj same)
    · exact absurd same (pair_ne_symbol "a" "exec-p1" v)
  · rintro (rfl | rfl)
    · exact ⟨pair_ne_symbol _ _ _, .inl rfl⟩
    · exact ⟨pair_ne_symbol _ _ _, .inr (.inl rfl)⟩

/-- MORK, the CeTTa draft and main CeTTa print `(a 1) (a 2) (b)` for p1. -/
theorem result1_reference : Result space1 exec1 result1 := by
  have adds : ∀ a, AddInst space1 exec1 a ↔ a = b := by
    intro a
    constructor
    · rintro ⟨σ, _, t, member, rfl⟩
      simp only [exec1, List.mem_singleton] at member
      subst member
      rfl
    · rintro rfl
      exact ⟨Insertion.single "x" one, (row_values rfl members1 _).mpr (.inl (single_x one)), b,
        by simp [exec1], rfl⟩
  have removes : ∀ a, ¬ RemoveInst space1 exec1 a := by
    rintro a ⟨σ, _, t, member, _⟩
    simp [exec1] at member
  intro a
  rw [adds]
  have notRemove := removes a
  simp only [notRemove, not_false_eq_true, and_true]
  simp only [result1, space1, exec1, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl) <;> decide
  · rintro (⟨rfl | rfl | rfl, notSelf⟩ | rfl)
    all_goals first
      | decide
      | exact absurd rfl notSelf

def label1 (n : Nat) : Atom :=
  if n = 0 then pair "a" one else if n = 1 then pair "a" two else if n = 2 then self1 else b

def before1 : Configuration Atom Nat := ⟨[], {0, 1, 2}⟩

/-- Row `x = k` alone: read `(a k)` and produce `(b)`. -/
def rowRule1 (k : Atom) : RuleInstance Atom := ⟨[], [pair "a" k], [], [], [b]⟩

def rowOne : Selection Nat := ⟨[], [0], [3]⟩
def rowTwo : Selection Nat := ⟨[], [1], [4]⟩
def afterOne : Configuration Atom Nat := rowOne.result label1 (rowRule1 one) before1
def afterTwo : Configuration Atom Nat := rowTwo.result label1 (rowRule1 two) afterOne

theorem rowOne_valid : rowOne.Valid atomAction label1 (rowRule1 one) before1 := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨empty, ?_⟩, ?_⟩
  · intro e member
    simp only [Selection.problem, Selection.equations, rowRule1, rowOne, before1, List.nil_append,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    rfl
  · intro check member
    simp [rowRule1] at member

theorem rowTwo_valid : rowTwo.Valid atomAction label1 (rowRule1 two) afterOne := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨empty, ?_⟩, ?_⟩
  · intro e member
    simp [afterOne, Selection.result, Selection.problem, Selection.equations, rowRule1, rowOne,
      rowTwo, before1] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [rowRule1] at member

/-- **Separation.** Firing p1 one row at a time leaves two occurrences
labelled `(b)`: the result does not represent a set space. -/
theorem row_protocol_duplicates :
    rowOne.Valid atomAction label1 (rowRule1 one) before1 ∧
      rowTwo.Valid atomAction label1 (rowRule1 two) afterOne ∧
      (3 : Nat) ∈ afterTwo.present ∧ (4 : Nat) ∈ afterTwo.present ∧ label1 3 = label1 4 ∧
      ¬ Set.InjOn label1 afterTwo.present := by
  have three : (3 : Nat) ∈ afterTwo.present := by decide
  have four : (4 : Nat) ∈ afterTwo.present := by decide
  refine ⟨rowOne_valid, rowTwo_valid, three, four, rfl, ?_⟩
  intro injective
  have same : (3 : Nat) = 4 := injective (Finset.mem_coe.mpr three) (Finset.mem_coe.mpr four) rfl
  omega

/-! ### p2 and p3: kernel order and snapshot rows -/

def xs : Atom := unit "x"
def self2 : Atom := .symbol "exec-p2"
def space2 : Finset Atom := {xs, self2}
def exec2 : Exec := ⟨self2, [xs], [xs], [xs]⟩

/-- `(O (- (x)) (+ (x)))` leaves `(x)` absent, as MORK and both CeTTa lanes do;
the reverse sink order does too (probe p8). -/
theorem result2_reference : Result space2 exec2 ∅ := by
  have row : ∀ σ, Row space2 exec2 σ := by
    intro σ p member
    simp only [exec2, List.mem_singleton] at member
    subst member
    rw [show subst σ xs = xs from subst_ground_unit σ "x"]
    decide
  have removes : ∀ a, RemoveInst space2 exec2 a ↔ a = xs := by
    intro a
    constructor
    · rintro ⟨σ, _, t, member, rfl⟩
      simp only [exec2, List.mem_singleton] at member
      subst member
      exact subst_ground_unit σ "x"
    · rintro rfl
      exact ⟨empty, row empty, xs, by simp [exec2], subst_ground_unit empty "x"⟩
  intro a
  rw [removes]
  simp only [Finset.notMem_empty, false_iff, not_and, not_not]
  intro kept
  rcases kept with ⟨member, notSelf⟩ | ⟨σ, _, t, inAdds, rfl⟩
  · simp only [space2, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · rfl
    · exact absurd rfl notSelf
  · simp only [exec2, List.mem_singleton] at inAdds
    subst inAdds
    exact subst_ground_unit σ "x"

def self3 : Atom := .symbol "exec-p3"
def space3 : Finset Atom := {pair "a" one, pair "a" two, self3}
def exec3 : Exec := ⟨self3, [pair "a" x, pair "a" one], [pair "seen" x], [pair "a" one]⟩
def result3 : Finset Atom := {pair "a" two, pair "seen" one, pair "seen" two}

theorem members3 (v : Atom) : pair "a" v ∈ space3.erase self3 ↔ v = one ∨ v = two := by
  simp only [space3, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, same | same | same⟩
    · exact .inl (pair_inj same)
    · exact .inr (pair_inj same)
    · exact absurd same (pair_ne_symbol "a" "exec-p3" v)
  · rintro (rfl | rfl)
    · exact ⟨pair_ne_symbol _ _ _, .inl rfl⟩
    · exact ⟨pair_ne_symbol _ _ _, .inr (.inl rfl)⟩

theorem row3 (σ : Subst) : Row space3 exec3 σ ↔ subst σ x = one ∨ subst σ x = two := by
  unfold Row
  simp only [exec3, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, subst_pair, subst_one, members3]
  simp

/-- MORK, the CeTTa draft and main CeTTa print `(a 2) (seen 1) (seen 2)` for p3:
both rows read `(a 1)` although the step removes it. -/
theorem result3_reference : Result space3 exec3 result3 := by
  have adds : ∀ a, AddInst space3 exec3 a ↔ a = pair "seen" one ∨ a = pair "seen" two := by
    intro a
    constructor
    · rintro ⟨σ, row, t, member, rfl⟩
      simp only [exec3, List.mem_singleton] at member
      subst member
      rw [subst_pair]
      rcases (row3 σ).mp row with value | value <;> rw [value]
      · exact .inl rfl
      · exact .inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Insertion.single "x" one, (row3 _).mpr (.inl (single_x one)), pair "seen" x,
          by simp [exec3], by rw [subst_pair, single_x]⟩
      · exact ⟨Insertion.single "x" two, (row3 _).mpr (.inr (single_x two)), pair "seen" x,
          by simp [exec3], by rw [subst_pair, single_x]⟩
  have removes : ∀ a, RemoveInst space3 exec3 a ↔ a = pair "a" one := by
    intro a
    constructor
    · rintro ⟨σ, _, t, member, rfl⟩
      simp only [exec3, List.mem_singleton] at member
      subst member
      rw [subst_pair, subst_one]
    · rintro rfl
      exact ⟨Insertion.single "x" one, (row3 _).mpr (.inl (single_x one)), pair "a" one,
        by simp [exec3], by rw [subst_pair, subst_one]⟩
  intro a
  rw [adds, removes]
  simp only [result3, space3, exec3, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl) <;> decide
  · rintro ⟨(⟨rfl | rfl | rfl, notSelf⟩ | rfl | rfl), notRemoved⟩
    all_goals first
      | decide
      | exact absurd rfl notRemoved
      | exact absurd rfl notSelf

end Probe

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsExec
