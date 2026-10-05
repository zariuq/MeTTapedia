import Mettapedia.GSLT.Distinction.HistoryContextTwoSided
import Mathlib.Data.List.Sections
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.ProdSigma

/-!
# Coverage profiles of the history model

The capacity-bounded history grammar has a stabilization certificate
(`HistoryCappedStage.bounded_stabilizes`).  That certificate is one profile of
coverage, not coverage of the whole grammar.  This module proves the two facts
that keep the other profiles visible; `HistoryContextHostProfile` applies them
to the history grammar and sets the three profiles side by side.

* **Pigeonhole: infinite faithful systems never stabilize**
  (`not_stabilizes_of_injective`).  For a presented system over the integer
  scale whose equations are equality, the depth-`n` signature of a term (its
  readings, and for each label the listed signatures of its successors at depth
  `n - 1`) ranges over one finite list (`signature_mem`), and equal signatures
  are `n`-step approximants (`approx_of_signature_eq`).  A stabilization
  certificate together with a faithful observer would make the signature
  injective, which an infinite family of different terms rules out.  This is
  the companion of `HistoryCappedStage.finite_stabilizes`.
* **The infinite growing control** (`pending_not_fresh`, `fresh_not_transport`,
  `fresh_values_infinite`).  In the contextual model a state with a pending
  entry is never observed like a fresh state: beside the entry's enabling frame
  it moves, and the fresh state does not.  So with the exact profile a
  configuration placed fresh at a later world has a material value that no
  transport of an earlier state has, and at every world infinitely many fresh
  values are pairwise different.

**Choice.**  Every declaration of this module is free of `Classical.choice`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryCoverageProfiles

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver
open Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver
open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.GradedTwoSidedObservation
open Mettapedia.Cybernetics.DistinctionCalculus.History

/-! ## Pigeonhole: infinite faithful systems never stabilize -/

section Pigeonhole

universe uS uAtom uLabel uObs

variable {S : GSLT.{uS}} {unit : ℤ} {positive : 0 < unit}
variable (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S (Scale.integers unit positive)) (W : Q.Vocabulary)

/-- The signatures of depth `n`: readings, and for each label a list of
signatures of depth `n - 1`. -/
def Signature : ℕ → Type
  | 0 => List ℤ
  | depth + 1 => List ℤ × List (List (Signature depth))

/-- Signatures have decidable equality. -/
def signatureDecidableEq : (depth : ℕ) → DecidableEq (Signature depth)
  | 0 => inferInstanceAs (DecidableEq (List ℤ))
  | depth + 1 => by
      letI := signatureDecidableEq depth
      exact inferInstanceAs (DecidableEq (List ℤ × List (List (Signature depth))))

instance (depth : ℕ) : DecidableEq (Signature depth) := signatureDecidableEq depth

/-- Every reading vector of the vocabulary on the integer scale. -/
def valueVectors : List (List ℤ) :=
  List.sections (W.observations.map fun _ => (List.range (unit.toNat + 1)).map Int.ofNat)

/-- **Every possible signature**, as one finite list. -/
def allSignatures : (depth : ℕ) → List (Signature depth)
  | 0 => valueVectors Q W
  | depth + 1 => valueVectors Q W ×ˢ List.sections (W.labels.map fun _ => (allSignatures depth).sublists)

/-- The readings of a term along the vocabulary. -/
def readingVector (term : S.Term) : List ℤ := W.observations.map fun observation => Q.value observation term

/-- **The depth-`n` signature of a term.** -/
def signature : (depth : ℕ) → S.Term → Signature depth
  | 0, term => readingVector Q W term
  | depth + 1, term => (readingVector Q W term, W.labels.map fun label =>
      (allSignatures Q W depth).filter fun candidate =>
        decide (candidate ∈ (Q.successors label term).map (signature depth)))

theorem value_mem_grid (observation : Q.Obs) (term : S.Term) :
    Q.value observation term ∈ (List.range (unit.toNat + 1)).map Int.ofNat := by
  have nonneg := Q.value_nonneg observation term
  have bounded := Q.value_le_one observation term
  change Q.value observation term ≤ unit at bounded
  refine List.mem_map.mpr ⟨(Q.value observation term).toNat, List.mem_range.mpr ?_, ?_⟩
  · have := Int.toNat_of_nonneg nonneg
    omega
  · exact Int.toNat_of_nonneg nonneg

theorem readingVector_mem (term : S.Term) : readingVector Q W term ∈ valueVectors Q W := by
  unfold readingVector valueVectors
  rw [List.mem_sections, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun observation _ => value_mem_grid Q observation term

/-- **Every signature is listed.** -/
theorem signature_mem : ∀ (depth : ℕ) (term : S.Term), signature Q W depth term ∈ allSignatures Q W depth
  | 0, term => readingVector_mem Q W term
  | depth + 1, term => by
      show (readingVector Q W term, _) ∈ valueVectors Q W ×ˢ _
      refine List.mem_product.mpr ⟨readingVector_mem Q W term, ?_⟩
      rw [List.mem_sections, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun label _ => List.mem_sublists.mpr (List.filter_sublist)

theorem readingVector_eq {left right : S.Term} (same : readingVector Q W left = readingVector Q W right)
    (observation : Q.Obs) : Q.value observation left = Q.value observation right :=
  List.map_inj_left.mp same observation (W.observations_complete observation)

theorem successor_signature_mem {depth : ℕ} {left right : S.Term}
    (same : signature Q W (depth + 1) left = signature Q W (depth + 1) right) (label : Q.dynamics.Label)
    {successor : S.Term} (member : successor ∈ Q.successors label left) :
    ∃ matching ∈ Q.successors label right, signature Q W depth matching = signature Q W depth successor := by
  have labels : (allSignatures Q W depth).filter (fun candidate =>
        decide (candidate ∈ (Q.successors label left).map (signature Q W depth))) =
      (allSignatures Q W depth).filter (fun candidate =>
        decide (candidate ∈ (Q.successors label right).map (signature Q W depth))) :=
    List.map_inj_left.mp (congrArg Prod.snd same) label (W.labels_complete label)
  have listed : signature Q W depth successor ∈ (allSignatures Q W depth).filter fun candidate =>
      decide (candidate ∈ (Q.successors label left).map (signature Q W depth)) :=
    List.mem_filter.mpr ⟨signature_mem Q W depth successor,
      decide_eq_true (List.mem_map_of_mem member)⟩
  rw [labels] at listed
  exact List.mem_map.mp (of_decide_eq_true (List.mem_filter.mp listed).2)

/-- **Equal signatures are approximants**, when the equations are equality. -/
theorem approx_of_signature_eq (equality : ∀ left right, S.Equiv left right → left = right) :
    ∀ (depth : ℕ) {left right : S.Term}, signature Q W depth left = signature Q W depth right →
      Q.Approx depth left right
  | 0, _, _, same => readingVector_eq Q W same
  | depth + 1, left, right, same => by
      refine ⟨readingVector_eq Q W (congrArg Prod.fst same), ?_, ?_⟩
      · intro label left' action
        obtain ⟨representative, member, close⟩ := Q.successors_cover action
        obtain ⟨matching, matchingMember, signatures⟩ := successor_signature_mem Q W same label member
        refine ⟨matching, Q.successors_act matchingMember, ?_⟩
        rw [equality _ _ close]
        exact approx_of_signature_eq equality depth signatures.symm
      · intro label right' action
        obtain ⟨representative, member, close⟩ := Q.successors_cover action
        obtain ⟨matching, matchingMember, signatures⟩ := successor_signature_mem Q W same.symm label member
        refine ⟨matching, Q.successors_act matchingMember, ?_⟩
        rw [equality _ _ close]
        exact approx_of_signature_eq equality depth signatures

/-- The signatures of the first `count` terms of a family. -/
def familySignatures (depth : ℕ) (family : ℕ → S.Term) : ℕ → List (Signature depth)
  | 0 => []
  | count + 1 => signature Q W depth (family count) :: familySignatures depth family count

theorem mem_familySignatures (depth : ℕ) (family : ℕ → S.Term) {candidate : Signature depth} :
    ∀ {count : ℕ}, candidate ∈ familySignatures Q W depth family count →
      ∃ index < count, signature Q W depth (family index) = candidate
  | 0, member => absurd member List.not_mem_nil
  | count + 1, member => by
      rcases List.mem_cons.mp member with same | member
      · exact ⟨count, Nat.lt_succ_self count, same.symm⟩
      · obtain ⟨index, below, same⟩ := mem_familySignatures depth family member
        exact ⟨index, Nat.lt_succ_of_lt below, same⟩

theorem familySignatures_nodup (depth : ℕ) (family : ℕ → S.Term)
    (injective : ∀ first second, signature Q W depth (family first) = signature Q W depth (family second) →
      first = second) :
    ∀ count, (familySignatures Q W depth family count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      refine List.nodup_cons.mpr ⟨fun member => ?_, familySignatures_nodup depth family injective count⟩
      obtain ⟨index, below, same⟩ := mem_familySignatures Q W depth family member
      have := injective index count same
      omega

theorem familySignatures_length (depth : ℕ) (family : ℕ → S.Term) :
    ∀ count, (familySignatures Q W depth family count).length = count
  | 0 => rfl
  | count + 1 => by
      change (familySignatures Q W depth family count).length + 1 = count + 1
      rw [familySignatures_length depth family count]

/-- **Pigeonhole.**  A presented system over the integer scale, with equality as
its equations, a faithful observer and an infinite family of different terms,
has no stabilization certificate at any depth. -/
theorem not_stabilizes_of_injective (equality : ∀ left right, S.Equiv left right → left = right)
    (faithful : ∀ left right, Q.GradedBisimilar left right → left = right) (family : ℕ → S.Term)
    (injective : Function.Injective family) (stage : ℕ) : ¬ Q.Stabilizes W stage := by
  intro stable
  have separated : ∀ first second, signature Q W stage (family first) = signature Q W stage (family second) →
      first = second := by
    intro first second same
    apply injective
    apply faithful
    exact ((Q.gradedBisimilar_iff_of_stabilizes W (Scale.integers_positive unit positive) stable _ _).2).mpr
      (Q.depthBound_eq_zero_of_approx W (approx_of_signature_eq Q W equality stage same))
  have nodup := familySignatures_nodup Q W stage family separated ((allSignatures Q W stage).length + 1)
  have contained : familySignatures Q W stage family ((allSignatures Q W stage).length + 1) ⊆
      allSignatures Q W stage := by
    intro candidate member
    obtain ⟨index, _, rfl⟩ := mem_familySignatures Q W stage family member
    exact signature_mem Q W stage (family index)
  have bounded := (nodup.subperm contained).length_le
  rw [familySignatures_length] at bounded
  omega

end Pigeonhole

/-! ## The infinite growing control -/

section Growing

open Mettapedia.GSLT.Distinction.HistoryContextCategory
open Mettapedia.GSLT.Distinction.HistoryContextTwoSided
open Mettapedia.GSLT.Distinction.HistoryIndependence (consumed read produced)
open Mettapedia.GSLT.Distinction.HistoryObserverControls (relabel)
open Mettapedia.TypeTheory.MaterialSets.Hypersets

variable {V : Type} {G : Grammar V}

/-- A frame that enables an entry beside every configuration: what a forward
entry consumes and reads, or what a backward entry produces and reads. -/
def enablingFrame (G : Grammar V) : Entry V → List V
  | (.forward, .evolve x) => [x]
  | (.forward, .fork x) => [x]
  | (.forward, .merge x y) => [x, y]
  | (.forward, .erase x) => [x]
  | (.backward, .evolve x) => [G.evolve x]
  | (.backward, .fork x) => [x, x]
  | (.backward, .merge x y) => [G.merge x y]
  | (.backward, .erase _) => []

/-- **Every entry moves beside its enabling frame.** -/
theorem moves_enabled (entry : Entry V) (live : Multiset V) :
    ∃ result, Moves G entry (live + (enablingFrame G entry : Multiset V)) result := by
  obtain ⟨direction, event⟩ := entry
  cases direction with
  | forward =>
      refine ⟨produced G event + read event + live, live, ?_, rfl⟩
      rw [Multiset.add_comm]
      cases event <;> rfl
  | backward =>
      refine ⟨consumed event + read event + live, live, rfl, ?_⟩
      rw [Multiset.add_comm]
      cases event <;> rfl

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)
  (R : NodeReadings K V)

/-- **A state with a pending entry is never observed like a fresh one**: placed
beside the entry's enabling frame it moves, and the fresh state does not. -/
theorem pending_not_fresh (profile : Profile G) (admitsSelf : ∀ entry, profile.admits entry entry)
    (point : World G) (state : Placed point) {entry : Entry V} {rest : List (Entry V)}
    (pending : state.script = entry :: rest) (live : Multiset V) :
    ¬ ObservedBisimilar profile K R point state (fresh point live) := by
  rintro ⟨relation, bisimulation, related⟩
  obtain ⟨result, moves⟩ := moves_enabled (G := G) entry state.live
  let framed := inContext point (Context.ofFrame G (enablingFrame G entry))
  have entryEq : (Context.ofFrame G (enablingFrame G entry)).entry entry = entry := by
    obtain ⟨direction, event⟩ := entry
    change (direction, relabel (fun x => x) event) = (direction, event)
    rw [relabel_id]
  have scriptEq : (transport framed state).script = entry ::
      (Context.ofFrame G (enablingFrame G entry)).script rest := by
    rw [transport_script, pending]
    change (Context.ofFrame G (enablingFrame G entry)).entry entry ::
      (Context.ofFrame G (enablingFrame G entry)).script rest ++ [] = _
    rw [entryEq, List.append_nil]
  have lengths := (transport framed state).length_eq
  rw [scriptEq, List.length_cons] at lengths
  have emitted : Emits profile state framed
      ⟨result, state.origin + 1, (Context.ofFrame G (enablingFrame G entry)).script rest, by
        rw [transport_origin] at lengths
        omega⟩ := by
    refine ⟨entry, entry, _, scriptEq, admitsSelf entry, ?_, rfl, rfl⟩
    change Moves G entry ((Context.ofFrame G (enablingFrame G entry)).apply state.live) result
    rw [Context.apply_ofFrame]
    exact moves
  obtain ⟨matching, available, _⟩ := bisimulation.underlying.forth related ⟨point, framed⟩ emitted
  obtain ⟨_, _, _, freshScript, _⟩ := available
  change (Context.ofFrame G (enablingFrame G entry)).script [] ++ [] = _ :: _ at freshScript
  cases freshScript

/-- **The growing control**: with the exact profile, a configuration placed
fresh at the next world has a material value that no transport of an earlier
state has. -/
theorem fresh_not_transport (nodes : ArgumentCoding V) (L : Listing V) (values : ArgumentCoding W)
    (point : World G) (entry : Entry V) (earlier : Placed point) (live : Multiset V) :
    value (exact G) K R nodes L values ⟨next point, transport (entryArrow point entry) earlier⟩ ≠
      value (exact G) K R nodes L values ⟨next point, fresh (next point) live⟩ := by
  intro same
  have related := (value_eq_iff (exact G) K R nodes L values (next point) _ _).mp same
  have pending : ∃ written rest, (transport (entryArrow point entry) earlier).script = written :: rest := by
    rw [transport_script]
    cases earlier.script with
    | nil => exact ⟨entry, [], rfl⟩
    | cons written rest => exact ⟨(Context.one G).entry written, _, rfl⟩
  obtain ⟨written, rest, scriptEq⟩ := pending
  exact pending_not_fresh K R (exact G) (fun _ => rfl) (next point) _ scriptEq live related

/-- **At every world infinitely many fresh values are different.** -/
theorem fresh_values_infinite (nodes : ArgumentCoding V) (L : Listing V) (values : ArgumentCoding W)
    (point : World G) (x : V) :
    Function.Injective fun count : ℕ =>
      freshValue (exact G) K R nodes L values point (Multiset.replicate count x) := by
  intro first second same
  have equal := exact_freshValue_injective K R nodes L values point same
  have sizes := congrArg Multiset.card equal
  rw [Multiset.card_replicate, Multiset.card_replicate] at sizes
  exact sizes

end Growing


end Mettapedia.GSLT.Distinction.HistoryCoverageProfiles
