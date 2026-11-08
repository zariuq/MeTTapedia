import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsSeparationFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents

/-!
# Concurrent separation logic over runs

## The parallel rule through the partial tensor

`Shuffle r₁ r₂ w`: the word `w` interleaves `r₁` and `r₂`.

* **Every interleaving of separated runs is one contextual trace with the tensor run**
  (`shuffle_roundEquiv`), so it runs and ends where the tensor does (`shuffle_executable`).
* **The parallel rule** (`parallel_rule`): `{P₁} r₁ {Q₁}` and `{P₂} r₂ {Q₂}` give
  `{P₁ ∗ P₂} w {Q₁ ∗ Q₂}` for every interleaving `w`. The side conditions are stated on the
  preconditions and the words, before execution: disjoint spaces, mutual blindness, and a consistent
  joint store. The last is the one global condition: each run's specification holds alone while
  their joint store has no solution (R26's `tensor_undefined_by_equations`).

These results go through R26's tensor and R22's contextual trace equivalence, and hold for guards
and solution-dependent queries.

## Footprints and independence

A footprint (`Footprint`) is a set of written and a set of read occurrences; two footprints are
compatible when neither writes what the other reads or writes (`Footprint.Compatible`). This is the
read–write permission algebra: reads are shared (`Footprint.reads_duplicable`), writes are exclusive
(`Footprint.writes_exclusive`), and compatibility is symmetric (`Footprint.compatible_comm`).

The footprint of a firing at a solution (`footprintOf`) writes what it takes and makes, and reads
what it reads together with every occurrence in a region its predicate queries observe.

* **R27's independence is compatibility of footprints** (`bernstein_iff_parts`): two firings have
  compatible footprints at every solution (`Bernstein`) exactly when none of R27's three relations
  (flow, read before take, inhibition) holds in either direction and neither conflict (a take or an
  identity made twice) holds. For static firings this gives R22's static independence
  (`staticIndependent_of_bernstein`, through R27's `staticIndependent_of_parts`; R27's
  configuration correspondence is stated for static firings only).
* **It is not disjointness in the algebra of configurations**: disjoint footprints are compatible
  (`bernstein_of_disjoint`), and two readers of one occurrence are compatible with overlapping
  footprints (`SeparationControls.shared_read_compatible`).
* **Rounds** (`round_pair_of_bernstein`, `bernstein_of_round_pair`): two static firings admitted at
  one configuration, with a consistent joint problem, form a round exactly when their footprints are
  compatible. R26's tensor asks for disjoint spaces, the exclusive case; rounds allow shared reads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire mem_fire)
open GuardFreeProcessOrders (SameUpTo)
open AnnotatedRunUnfolding (Flow ReadBeforeTake InhibitsAt)
open AnnotatedRunEvents (TakeConflict MadeConflict Inhibits)

universe uT uS uO

namespace SeparationRuns

/-! ## Interleavings -/

/-- `w` interleaves `u` and `v`. -/
inductive Shuffle {α : Type*} : List α → List α → List α → Prop
  | nil : Shuffle [] [] []
  | left (a : α) {u v w : List α} : Shuffle u v w → Shuffle (a :: u) v (a :: w)
  | right (b : α) {u v w : List α} : Shuffle u v w → Shuffle u (b :: v) (b :: w)

theorem shuffle_nil_left {α : Type*} : ∀ v : List α, Shuffle [] v v
  | [] => .nil
  | b :: v => .right b (shuffle_nil_left v)

/-- The tensor run is an interleaving. -/
theorem shuffle_append {α : Type*} : ∀ u v : List α, Shuffle u v (u ++ v)
  | [], v => shuffle_nil_left v
  | a :: u, v => .left a (shuffle_append u v)

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Parallel

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Every interleaving of separated runs is one contextual trace with the tensor run.** -/
theorem shuffle_roundEquiv {r₁ r₂ w : List (Firing T S O)} (shuffle : Shuffle r₁ r₂ w) :
    ∀ {C₁ C₂ : Configuration T O}, Separated A label C₁ r₁ C₂ r₂ →
      RoundEquiv A label (tensor C₁ C₂) w (r₁ ++ r₂) := by
  induction shuffle with
  | nil => exact fun _ => .refl _
  | left a _ ih =>
      intro C₁ C₂ separated
      have same := tensor_result_left A label (C₁ := C₁) (C₂ := C₂)
        (separated.head_left_apart A label)
      exact RoundEquiv.cons A label (RoundEquiv.congr A label (sameUpTo_symm A same)
        (ih separated.tail_left))
  | right b _ ih =>
      intro C₁ C₂ separated
      have same := tensor_result_right A label (C₁ := C₁) (C₂ := C₂)
        (separated.head_right_apart A label)
      exact .trans _ _ _ (RoundEquiv.cons A label (RoundEquiv.congr A label (sameUpTo_symm A same)
        (ih separated.tail_right))) (.symm _ _ (bubble_right A label C₁ _ C₂ b _ separated))

/-- **Every interleaving of separated runs runs, and ends where the tensor does.** -/
theorem shuffle_executable {C₁ C₂ : Configuration T O} {r₁ r₂ w : List (Firing T S O)}
    (separated : Separated A label C₁ r₁ C₂ r₂) (shuffle : Shuffle r₁ r₂ w) :
    Executable A label (tensor C₁ C₂) w ∧
      SameUpTo A (follow label (tensor C₁ C₂) w) (tensor (follow label C₁ r₁) (follow label C₂ r₂)) := by
  obtain ⟨runs, ends⟩ := tensor_executable A label C₁ r₁ C₂ r₂ separated
  have back := RoundEquiv.executable A label (shuffle_roundEquiv A label shuffle separated)
  exact ⟨back.1.mpr runs, (back.2 (back.1.mpr runs)).trans A ends⟩

/-- **The parallel rule of concurrent separation logic**, for every interleaving. -/
theorem parallel_rule {P₁ Q₁ P₂ Q₂ : Assertion T O} {r₁ r₂ : List (Firing T S O)}
    (left : Triple A label P₁ r₁ Q₁) (right : Triple A label P₂ r₂ Q₂)
    (apart : ∀ C₁ C₂, P₁ C₁ → P₂ C₂ → Separable A C₁ C₂ → Disjoint (space C₁ r₁) (space C₂ r₂))
    (blind : ∀ C₁ C₂, P₁ C₁ → P₂ C₂ → Separable A C₁ C₂ →
      (∀ f ∈ r₁, BlindTo A label (space C₂ r₂) f) ∧ (∀ g ∈ r₂, BlindTo A label (space C₁ r₁) g))
    (joint : ∀ C₁ C₂, P₁ C₁ → P₂ C₂ → Separable A C₁ C₂ →
      A.Consistent (jointStore label C₁ r₁ C₂ r₂))
    {w : List (Firing T S O)} (shuffle : Shuffle r₁ r₂ w) :
    Triple A label (star A P₁ P₂) w (star A Q₁ Q₂) := by
  rintro C ⟨C₁, C₂, sep, same, h₁, h₂⟩
  obtain ⟨runs₁, q₁⟩ := left C₁ h₁
  obtain ⟨runs₂, q₂⟩ := right C₂ h₂
  have separated : Separated A label C₁ r₁ C₂ r₂ :=
    ⟨runs₁, runs₂, apart C₁ C₂ h₁ h₂ sep, (blind C₁ C₂ h₁ h₂ sep).1, (blind C₁ C₂ h₁ h₂ sep).2,
      joint C₁ C₂ h₁ h₂ sep⟩
  obtain ⟨runs, ends⟩ := shuffle_executable A label separated shuffle
  exact ⟨(executable_congr A label w same).mp runs, follow label C₁ r₁, follow label C₂ r₂,
    Separated.ends_separable A label separated,
    (sameUpTo_symm A ends).trans A (follow_congr A label w same), q₁, q₂⟩

end Parallel

/-! ## Footprints in the read–write algebra -/

/-- A footprint: what is written and what is read. -/
structure Footprint (O : Type uO) where
  writes : Set O
  reads : Set O

namespace Footprint

variable {O' : Type uO}

/-- **Compatible footprints**: neither writes what the other reads or writes. -/
def Compatible (x y : Footprint O') : Prop :=
  Disjoint x.writes (y.writes ∪ y.reads) ∧ Disjoint y.writes x.reads

/-- The join of footprints. -/
def join (x y : Footprint O') : Footprint O' := ⟨x.writes ∪ y.writes, x.reads ∪ y.reads⟩

theorem compatible_comm {x y : Footprint O'} : Compatible x y ↔ Compatible y x := by
  unfold Compatible
  rw [Set.disjoint_union_right, Set.disjoint_union_right]
  constructor
  · rintro ⟨⟨a, b⟩, c⟩
    exact ⟨⟨a.symm, c⟩, b⟩
  · rintro ⟨⟨a, b⟩, c⟩
    exact ⟨⟨a.symm, c⟩, b⟩

/-- **Reads are shared.** -/
theorem reads_duplicable (R : Set O') : Compatible ⟨∅, R⟩ ⟨∅, R⟩ ∧ join ⟨∅, R⟩ ⟨∅, R⟩ = ⟨∅, R⟩ :=
  ⟨⟨Set.empty_disjoint _, Set.empty_disjoint _⟩, by simp [join]⟩

/-- **Writes are exclusive.** -/
theorem writes_exclusive {W R R' : Set O'} (compatible : Compatible ⟨W, R⟩ ⟨W, R'⟩) : W = ∅ := by
  have first : Disjoint W (W ∪ R') := compatible.1
  have self : Disjoint W W := Set.disjoint_of_subset_right Set.subset_union_left first
  rw [disjoint_self] at self
  simpa using self

end Footprint

section Footprints

variable (label : O → T)

omit [DecidableEq O] in
/-- A firing writes an occurrence when it takes or makes it. -/
def Writes (f : Firing T S O) (o : O) : Prop := o ∈ f.selection.taken ∨ o ∈ f.selection.made

omit [DecidableEq O] in
/-- A firing reads an occurrence at a solution when it reads it, or when the occurrence lies in a
region one of its predicate queries observes. -/
def ReadsAt (σ : S) (f : Firing T S O) (o : O) : Prop :=
  o ∈ f.selection.read ∨ ∃ query ∈ f.queries, query.region σ (label o) = true

omit [DecidableEq O] in
/-- **The footprint of a firing at a solution.** -/
def footprintOf (σ : S) (f : Firing T S O) : Footprint O :=
  ⟨{o | Writes f o}, {o | ReadsAt label σ f o}⟩

omit [DecidableEq O] in
/-- **Bernstein's conditions**: compatible footprints at every solution. -/
def Bernstein (f g : Firing T S O) : Prop :=
  ∀ σ : S, (footprintOf label σ f).Compatible (footprintOf label σ g)

omit [DecidableEq O] in
theorem bernstein_iff_pointwise {f g : Firing T S O} :
    Bernstein label f g ↔ ∀ (σ : S) (o : O),
      (Writes f o → ¬ Writes g o ∧ ¬ ReadsAt label σ g o) ∧ (Writes g o → ¬ ReadsAt label σ f o) := by
  unfold Bernstein Footprint.Compatible
  constructor
  · intro compatible σ o
    obtain ⟨first, second⟩ := compatible σ
    refine ⟨fun written => ?_, fun written read => Set.disjoint_left.mp second written read⟩
    have outside := Set.disjoint_left.mp first written
    exact ⟨fun other => outside (Or.inl other), fun other => outside (Or.inr other)⟩
  · intro pointwise σ
    refine ⟨Set.disjoint_left.mpr fun o written other => ?_,
      Set.disjoint_left.mpr fun o written read => (pointwise σ o).2 written read⟩
    rcases other with other | other
    · exact ((pointwise σ o).1 written).1 other
    · exact ((pointwise σ o).1 written).2 other

omit [DecidableEq O] in
/-- **R27's independence is compatibility of footprints.** -/
theorem bernstein_iff_parts (σ₀ : S) {f g : Firing T S O} :
    Bernstein label f g ↔
      ¬ Flow f g ∧ ¬ Flow g f ∧ ¬ ReadBeforeTake f g ∧ ¬ ReadBeforeTake g f ∧
        ¬ Inhibits label f g ∧ ¬ Inhibits label g f ∧ ¬ TakeConflict f g ∧ ¬ MadeConflict f g := by
  rw [bernstein_iff_pointwise]
  constructor
  · intro pointwise
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨o, made, taken | read⟩
      · exact ((pointwise (σ₀) o).1 (Or.inr made)).1 (Or.inl taken)
      · exact ((pointwise (σ₀) o).1 (Or.inr made)).2 (Or.inl read)
    · rintro ⟨o, made, taken | read⟩
      · exact ((pointwise (σ₀) o).1 (Or.inl taken)).1 (Or.inr made)
      · exact (pointwise (σ₀) o).2 (Or.inr made) (Or.inl read)
    · rintro ⟨o, read, taken⟩
      exact (pointwise (σ₀) o).2 (Or.inl taken) (Or.inl read)
    · rintro ⟨o, read, taken⟩
      exact ((pointwise (σ₀) o).1 (Or.inl taken)).2 (Or.inl read)
    · rintro ⟨σ, query, member, o, written, inside⟩
      exact ((pointwise σ o).1 written).2 (Or.inr ⟨query, member, inside⟩)
    · rintro ⟨σ, query, member, o, written, inside⟩
      exact (pointwise σ o).2 written (Or.inr ⟨query, member, inside⟩)
    · rintro ⟨o, taken, taken'⟩
      exact ((pointwise (σ₀) o).1 (Or.inl taken)).1 (Or.inl taken')
    · rintro ⟨o, made, made'⟩
      exact ((pointwise (σ₀) o).1 (Or.inr made)).1 (Or.inr made')
  · rintro ⟨flow, flow', read, read', inhibits, inhibits', take, makes⟩ σ o
    refine ⟨fun written => ⟨fun other => ?_, fun other => ?_⟩, fun written other => ?_⟩
    · rcases written with taken | made <;> rcases other with taken' | made'
      · exact take ⟨o, taken, taken'⟩
      · exact flow' ⟨o, made', Or.inl taken⟩
      · exact flow ⟨o, made, Or.inl taken'⟩
      · exact makes ⟨o, made, made'⟩
    · rcases other with readG | ⟨query, member, inside⟩
      · rcases written with taken | made
        · exact read' ⟨o, readG, taken⟩
        · exact flow ⟨o, made, Or.inr readG⟩
      · exact inhibits ⟨σ, query, member, o, written, inside⟩
    · rcases other with readF | ⟨query, member, inside⟩
      · rcases written with taken | made
        · exact read ⟨o, readF, taken⟩
        · exact flow' ⟨o, made, Or.inr readF⟩
      · exact inhibits' ⟨σ, query, member, o, written, inside⟩

omit [DecidableEq O] in
/-- **Disjoint footprints are compatible.** -/
theorem bernstein_of_disjoint {f g : Firing T S O}
    (apart : ∀ (σ : S) (o : O), (Writes f o ∨ ReadsAt label σ f o) →
      ¬ (Writes g o ∨ ReadsAt label σ g o)) :
    Bernstein label f g := by
  rw [bernstein_iff_pointwise]
  intro σ o
  refine ⟨fun written => ⟨fun other => apart σ o (Or.inl written) (Or.inl other),
    fun other => apart σ o (Or.inl written) (Or.inr other)⟩,
    fun written other => apart σ o (Or.inr other) (Or.inl written)⟩

/-- **For static firings, compatible footprints give R22's static independence.** -/
theorem staticIndependent_of_bernstein (σ₀ : S) {f g : Firing T S O} (sf : f.Static) (sg : g.Static)
    (bernstein : Bernstein label f g) : StaticIndependent label f g := by
  obtain ⟨flow, flow', read, read', inhibits, inhibits', take, makes⟩ :=
    (bernstein_iff_parts label σ₀).mp bernstein
  exact AnnotatedRunEvents.staticIndependent_of_parts label sf sg flow flow' read read' inhibits
    inhibits' take makes

end Footprints

/-! ## Rounds -/

section Rounds

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Compatible footprints make a round.** Two static firings admitted at one configuration, with a
consistent joint problem and compatible footprints, form a round there. -/
theorem round_pair_of_bernstein {f g : Firing T S O} {C : Configuration T O} (sf : f.Static)
    (sg : g.Static) (fValid : f.Valid A label C) (gValid : g.Valid A label C)
    (joint : A.Consistent (jointProblem label C [f, g])) (bernstein : Bernstein label f g) :
    Round A label C [f, g] := by
  have pointwise := (bernstein_iff_pointwise label).mp bernstein
  have σ₀ : S := A.identity
  refine ⟨fun x member => ?_, joint, List.pairwise_pair.mpr ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rcases List.mem_pair.mp member with rfl | rfl
    · exact fValid
    · exact gValid
  · rintro (taken | made)
    · obtain ⟨o, inF, inG⟩ := Finset.not_disjoint_iff.mp taken
      exact ((pointwise σ₀ o).1 (Or.inl (by simpa [Selection.commit] using inF))).1
        (Or.inl (by simpa [Selection.commit] using inG))
    · obtain ⟨o, inF, inG⟩ := Finset.not_disjoint_iff.mp made
      exact ((pointwise σ₀ o).1 (Or.inr (by simpa [Selection.commit] using inF))).1
        (Or.inr (by simpa [Selection.commit] using inG))
  · rintro (kept | ⟨query, member, -⟩)
    · obtain ⟨o, inF, inG⟩ := Finset.not_disjoint_iff.mp kept
      exact ((pointwise σ₀ o).1 (Or.inl (by simpa [Selection.commit] using inF))).2
        (Or.inl (by simpa [Selection.commit] using inG))
    · simp [Selection.commit] at member
  · rintro (kept | ⟨query, member, -⟩)
    · obtain ⟨o, inG, inF⟩ := Finset.not_disjoint_iff.mp kept
      exact (pointwise σ₀ o).2 (Or.inl (by simpa [Selection.commit] using inG))
        (Or.inl (by simpa [Selection.commit] using inF))
    · simp [Selection.commit] at member
  · intro check member
    rw [sf.checks] at member
    cases member
  · intro check member
    rw [sg.checks] at member
    cases member
  · intro query member σ _ o written
    cases inside : query.region σ (label o) with
    | false => rfl
    | true =>
        exact ((pointwise σ o).2 (by simpa [Writes] using written)
          (Or.inr ⟨query, member, inside⟩)).elim
  · intro query member σ _ o written
    cases inside : query.region σ (label o) with
    | false => rfl
    | true =>
        exact (((pointwise σ o).1 (by simpa [Writes] using written)).2
          (Or.inr ⟨query, member, inside⟩)).elim

/-- **A round of static firings has compatible footprints.** -/
theorem bernstein_of_round_pair {f g : Firing T S O} {C : Configuration T O} (sf : f.Static)
    (sg : g.Static) (isRound : Round A label C [f, g]) : Bernstein label f g := by
  have fValid := isRound.valid f (List.mem_cons_self)
  have gValid := isRound.valid g (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨⟨noClash, spoilsFG, spoilsGF⟩, -, -, fQueries, gQueries⟩ :=
    List.pairwise_pair.mp isRound.compatible
  obtain ⟨σ₀, solved₀⟩ := isRound.joint
  have cut : A.Models σ₀ (pairCut label C f g) := by
    simpa [jointProblem, pairCut, List.flatMap_cons, List.append_assoc] using solved₀
  have presentF : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ C.present :=
    fun o used => used_present A label fValid used
  have presentG : ∀ o, o ∈ g.selection.taken ∨ o ∈ g.selection.read → o ∈ C.present :=
    fun o used => used_present A label gValid used
  have freshF : ∀ o ∈ f.selection.made, o ∉ C.present := fun o made present =>
    Finset.disjoint_left.mp fValid.firing.occurrences.fresh (by simpa [Selection.commit] using made)
      present
  have freshG : ∀ o ∈ g.selection.made, o ∉ C.present := fun o made present =>
    Finset.disjoint_left.mp gValid.firing.occurrences.fresh (by simpa [Selection.commit] using made)
      present
  rw [bernstein_iff_pointwise]
  intro σ o
  refine ⟨fun written => ⟨fun other => ?_, fun other => ?_⟩, fun written other => ?_⟩
  · rcases written with taken | made <;> rcases other with taken' | made'
    · exact noClash (Or.inl (Finset.not_disjoint_iff.mpr
        ⟨o, by simpa [Selection.commit] using taken, by simpa [Selection.commit] using taken'⟩))
    · exact freshG o made' (presentF o (Or.inl taken))
    · exact freshF o made (presentG o (Or.inl taken'))
    · exact noClash (Or.inr (Finset.not_disjoint_iff.mpr
        ⟨o, by simpa [Selection.commit] using made, by simpa [Selection.commit] using made'⟩))
  · rcases other with readG | ⟨query, member, inside⟩
    · rcases written with taken | made
      · exact spoilsFG (Or.inl (Finset.not_disjoint_iff.mpr
          ⟨o, by simpa [Selection.commit] using taken, by simpa [Selection.commit] using readG⟩))
      · exact freshF o made (presentG o (Or.inr readG))
    · have outside := gQueries query member σ₀ cut o (List.mem_append.mpr written)
      rw [sg.queries query member σ σ₀, outside] at inside
      cases inside
  · rcases other with readF | ⟨query, member, inside⟩
    · rcases written with taken | made
      · exact spoilsGF (Or.inl (Finset.not_disjoint_iff.mpr
          ⟨o, by simpa [Selection.commit] using taken, by simpa [Selection.commit] using readF⟩))
      · exact freshG o made (presentF o (Or.inr readF))
    · have outside := fQueries query member σ₀ cut o (List.mem_append.mpr written)
      rw [sf.queries query member σ σ₀, outside] at inside
      cases inside

end Rounds

end SeparationRuns

open SeparationRuns

#print axioms shuffle_nil_left
#print axioms shuffle_append
#print axioms shuffle_roundEquiv
#print axioms shuffle_executable
#print axioms parallel_rule
#print axioms Footprint.compatible_comm
#print axioms Footprint.reads_duplicable
#print axioms Footprint.writes_exclusive
#print axioms bernstein_iff_pointwise
#print axioms bernstein_iff_parts
#print axioms bernstein_of_disjoint
#print axioms staticIndependent_of_bernstein
#print axioms round_pair_of_bernstein
#print axioms bernstein_of_round_pair

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
