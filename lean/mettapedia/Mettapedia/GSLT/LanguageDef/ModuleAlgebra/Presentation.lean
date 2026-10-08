import Mettapedia.GSLT.Core.Composition
import Mathlib.Data.Finset.Image

/-!
# Origin-sensitive declaration fragments

The term/projection fragment of MeTTaIL's `pres.rs` identifies declarations by
origin, checks agreement along shared paths, and rejects independently introduced
declarations with one label. This module gives its extensional algebra. Ordered
builders, source spans, completed cores, and the other upstream entry kinds have
separate contracts; this is not a decoder for the complete Rust presentation.

Source: F1R3FLY-io/mettail-rust, commit
`8c1bb3b0ef3890406e375c2c5387dc9a3cdf0439`, `mettail-elab/src/pres.rs`.
-/

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra

universe u v w

/-- The origin is independent of the exposed label and its specification. -/
structure Entry (Origin : Type u) (Label : Type v) (Body : Type w) where
  origin : Origin
  label : Label
  body : Body
  deriving DecidableEq

variable {Origin : Type u} {Label : Type v} {Body : Type w}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

abbrev Fragment := Finset (Entry Origin Label Body)

/-- Shared origins must agree; one exposed label cannot denote two origins. -/
def Valid (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) : Prop :=
  ∀ first ∈ entries, ∀ second ∈ entries,
    (first.origin = second.origin ∨ first.label = second.label) → first = second

instance (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Decidable (Valid entries) := by unfold Valid; infer_instance

/-- A finite, conflict-free fragment. This admits shared ancestors. -/
abbrev Presentation (Origin : Type u) (Label : Type v) (Body : Type w)
    [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] :=
  {entries : Finset (Entry Origin Label Body) // Valid entries}

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
@[simp] theorem valid_empty : Valid (∅ : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) := by simp [Valid]

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem Valid.mono {entries smaller : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)} (valid : Valid entries) (subset : smaller ⊆ entries) :
    Valid smaller := by
  intro first firstMem second secondMem overlap
  exact valid first (subset firstMem) second (subset secondMem) overlap

def empty : Presentation Origin Label Body := ⟨∅, valid_empty⟩

/-- A checked union, rather than name-based or content-based deduplication. -/
def check (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Option (Presentation Origin Label Body) :=
  if h : Valid entries then some ⟨entries, h⟩ else none

def join (first second : Presentation Origin Label Body) :
    Option (Presentation Origin Label Body) := check (first.val ∪ second.val)

@[simp] theorem check_val (p : Presentation Origin Label Body) : check p.val = some p := by
  simp [check, p.property]

theorem check_eq_some_iff {entries : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)} {p : Presentation Origin Label Body} :
    check entries = some p ↔ entries = p.val := by
  by_cases h : Valid entries
  · simp only [check, dif_pos h, Option.some.injEq]
    exact Subtype.ext_iff
  · simp only [check, dif_neg h, reduceCtorEq, false_iff]
    intro equal
    exact h (equal ▸ p.property)

@[simp] theorem check_eq_none_iff (entries : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) : check entries = none ↔ ¬ Valid entries := by
  simp [check]

theorem join_eq_some_iff {p q r : Presentation Origin Label Body} :
    join p q = some r ↔ p.val ∪ q.val = r.val := check_eq_some_iff

/-- Cross-fragment overlap is checked independently of each side's validity. -/
def Compatible (first second : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) : Prop :=
  ∀ a ∈ first, ∀ b ∈ second,
    (a.origin = b.origin ∨ a.label = b.label) → a = b

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem Compatible.symm {first second : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)} (compatible : Compatible first second) :
    Compatible second first := by
  intro a ha b hb overlap
  exact (compatible b hb a ha (overlap.imp Eq.symm Eq.symm)).symm

theorem valid_union_iff {first second : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)} :
    Valid (first ∪ second) ↔ Valid first ∧ Valid second ∧ Compatible first second := by
  constructor
  · intro valid
    exact ⟨valid.mono Finset.subset_union_left, valid.mono Finset.subset_union_right,
      fun a ha b hb overlap => valid a (Finset.mem_union_left _ ha)
        b (Finset.mem_union_right _ hb) overlap⟩
  · rintro ⟨firstValid, secondValid, cross⟩ a ha b hb overlap
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact firstValid a ha b hb overlap
    · exact cross a ha b hb overlap
    · apply (cross b hb a ha ?_).symm
      exact overlap.imp Eq.symm Eq.symm
    · exact secondValid a ha b hb overlap

/-- Checking early and checking the entire union agree, including failure. -/
theorem check_union (first second : Fragment (Origin := Origin)
    (Label := Label) (Body := Body)) :
    check (first ∪ second) =
      (check first).bind fun p => (check second).bind fun q => join p q := by
  by_cases hf : Valid first
  · by_cases hs : Valid second
    · simp [check, hf, hs, join]
    · have h : ¬ Valid (first ∪ second) :=
        fun h => hs (h.mono Finset.subset_union_right)
      simp [check, hs, h]
  · have h : ¬ Valid (first ∪ second) :=
      fun h => hf (h.mono Finset.subset_union_left)
    simp [check, hf, h]

theorem join_comm (p q : Presentation Origin Label Body) : join p q = join q p := by
  simp only [join, Finset.union_comm]

theorem join_eq_none_iff (p q : Presentation Origin Label Body) :
    join p q = none ↔ ¬ Compatible p.val q.val := by
  simp [join, valid_union_iff, p.property, q.property]

/-- Every failed join exposes either a disagreeing shared origin or a label
collision between distinct entries. -/
theorem join_failure_witness (p q : Presentation Origin Label Body) :
    join p q = none ↔ ∃ a ∈ p.val, ∃ b ∈ q.val,
      (a.origin = b.origin ∨ a.label = b.label) ∧ a ≠ b := by
  rw [join_eq_none_iff]
  simp only [Compatible]
  push Not
  rfl

@[simp] theorem join_self (p : Presentation Origin Label Body) : join p p = some p := by
  simp [join]

/-- Upstream meet selects the left representatives of shared origins. -/
def meet (p q : Presentation Origin Label Body) : Presentation Origin Label Body :=
  ⟨p.val.filter (fun a => ∃ b ∈ q.val, a.origin = b.origin),
    p.property.mono (Finset.filter_subset _ _)⟩

/-- Difference removes shared origins even if their exposed declarations differ. -/
def diff (p q : Presentation Origin Label Body) : Presentation Origin Label Body :=
  ⟨p.val.filter (fun a => ¬ ∃ b ∈ q.val, a.origin = b.origin),
    p.property.mono (Finset.filter_subset _ _)⟩

theorem meet_val_of_compatible (p q : Presentation Origin Label Body)
    (compatible : Compatible p.val q.val) : (meet p q).val = p.val ∩ q.val := by
  ext a
  simp only [meet, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨ha, b, hb, origin⟩
    exact ⟨ha, (compatible a ha b hb (Or.inl origin)) ▸ hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha, a, hb, rfl⟩

theorem meet_comm_of_compatible (p q : Presentation Origin Label Body)
    (compatible : Compatible p.val q.val) : meet p q = meet q p := by
  apply Subtype.ext
  rw [meet_val_of_compatible p q compatible, meet_val_of_compatible q p compatible.symm,
    Finset.inter_comm]

theorem meet_diff_partition (p q : Presentation Origin Label Body) :
    (meet p q).val ∪ (diff p q).val = p.val := by
  ext a
  simp only [meet, diff, Finset.mem_union, Finset.mem_filter]
  by_cases h : ∃ b ∈ q.val, a.origin = b.origin <;> simp [h]

theorem join_meet_diff (p q : Presentation Origin Label Body) :
    join (meet p q) (diff p q) = some p := join_eq_some_iff.mpr (meet_diff_partition p q)

def origins (entries : Fragment (Origin := Origin) (Label := Label) (Body := Body)) :
    Finset Origin := entries.image Entry.origin

/-- Replacement changes a declaration in place, retaining its origin. -/
def replaceEntry (origin : Origin) (label : Label) (body : Body)
    (entry : Entry Origin Label Body) : Entry Origin Label Body :=
  if entry.origin = origin then ⟨entry.origin, label, body⟩ else entry

def replace (p : Presentation Origin Label Body) (origin : Origin) (label : Label)
    (body : Body) : Option (Presentation Origin Label Body) :=
  check (p.val.image (replaceEntry origin label body))

omit [DecidableEq Label] [DecidableEq Body] in
@[simp] theorem replaceEntry_origin (origin : Origin) (label : Label) (body : Body)
    (entry : Entry Origin Label Body) :
    (replaceEntry origin label body entry).origin = entry.origin := by
  simp [replaceEntry]; split <;> rfl

theorem origins_replace (p q : Presentation Origin Label Body) (origin : Origin)
    (label : Label) (body : Body) (success : replace p origin label body = some q) :
    origins q.val = origins p.val := by
  have value := check_eq_some_iff.mp success
  rw [← value]
  simp only [origins, Finset.image_image, Function.comp_def, replaceEntry_origin]

/-- Fresh application stamps newly introduced declarations, leaving imported
ancestors to be supplied separately to `join`. -/
def stamp {Instance : Type*} (instanceId : Instance) (entry : Entry Origin Label Body) :
    Entry (Instance × Origin) Label Body := ⟨(instanceId, entry.origin), entry.label, entry.body⟩

def stampPresentation {Instance : Type*} [DecidableEq Instance] (instanceId : Instance)
    (p : Presentation Origin Label Body) : Presentation (Instance × Origin) Label Body :=
  ⟨p.val.image (stamp instanceId), by
    intro a ha b hb overlap
    obtain ⟨originalA, memberA, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨originalB, memberB, rfl⟩ := Finset.mem_image.mp hb
    have equal : originalA = originalB := p.property _ memberA _ memberB
      (overlap.imp (congrArg Prod.snd) id)
    rw [equal]⟩

omit [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body] in
theorem stamps_disjoint {Instance : Type*} [DecidableEq Instance]
    (first second : Instance) (different : first ≠ second)
    (a b : Entry Origin Label Body) :
    (stamp first a).origin ≠ (stamp second b).origin := by
  intro equal
  exact different (congrArg Prod.fst equal)

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra
