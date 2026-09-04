import Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

/-!
# Stable-identity indexes for ordered occurrence contraction

An ordered occurrence has two independent coordinates: a stable identity and
its current position in the ordered family.  Stable contraction changes the
second coordinate while retaining the first.  An index whose leaves store
stable identities can therefore remain physically unchanged; its observable
answer is obtained by projecting the stored identities through the current
live family.

The exactness theorem below requires occurrence identities to be unique.
Without that premise, removing one of two equal-identity occurrences cannot be
reconstructed from an identity-keyed index.  Payload equality is harmless:
duplicate payloads remain independently addressable when their identities are
different.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.StableOccurrenceIdentityIndex

open StableOccurrenceContraction

universe uId uRow

/-- One authored occurrence with a stable identity independent of its current
ordered coordinate. -/
structure Occurrence (Id : Type uId) (Row : Type uRow) where
  id : Id
  payload : Row
deriving DecidableEq, Repr

/-- The stable identities in current authored order. -/
def identities {Id : Type uId} {Row : Type uRow}
    (occurrences : List (Occurrence Id Row)) : List Id :=
  occurrences.map Occurrence.id

/-- A payload-index leaf family.  It records stable occurrence identities in
authored order and deliberately contains no dense occurrence coordinate. -/
def index {Id : Type uId} {Row : Type uRow}
    (accept : Row → Bool) : List (Occurrence Id Row) → List Id
  | [] => []
  | occurrence :: occurrences =>
      if accept occurrence.payload then
        occurrence.id :: index accept occurrences
      else
        index accept occurrences

/-- The live identity family after stable contraction. -/
def liveIdentities {Id : Type uId} {Row : Type uRow}
    : List Bool → List (Occurrence Id Row) → List Id
  | true :: mask, occurrence :: occurrences =>
      occurrence.id :: liveIdentities mask occurrences
  | false :: mask, _ :: occurrences =>
      liveIdentities mask occurrences
  | _, _ => []

/-- Observe an unchanged stable-identity index through the current live
identity family. -/
def project {Id : Type uId} [DecidableEq Id]
    (live : List Id) : List Id → List Id
  | [] => []
  | identity :: stored =>
      if identity ∈ live then
        identity :: project live stored
      else
        project live stored

/-- The canonical finite coordinate card for a live identity family.  Absence
is represented explicitly instead of by `List.idxOf`'s out-of-range sentinel. -/
def coordinateCard {Id : Type uId} [DecidableEq Id]
    (live : List Id) (identity : Id) : Option Nat :=
  if identity ∈ live then some (live.idxOf identity) else none

/-- Project unchanged stable-identity leaves directly to their current dense
coordinates. -/
def projectCoordinates {Id : Type uId} [DecidableEq Id]
    (live : List Id) : List Id → List Nat
  | [] => []
  | identity :: stored =>
      match coordinateCard live identity with
      | some coordinate => coordinate :: projectCoordinates live stored
      | none => projectCoordinates live stored

/-- An independent dense-coordinate index over the current occurrence family.
It does not mention stable identities or a projection card. -/
def denseIndex {Id : Type uId} {Row : Type uRow}
    (accept : Row → Bool) : List (Occurrence Id Row) → List Nat
  | [] => []
  | occurrence :: occurrences =>
      let tail := (denseIndex accept occurrences).map Nat.succ
      if accept occurrence.payload then 0 :: tail else tail

@[simp] theorem project_no_live
    {Id : Type uId} [DecidableEq Id] (stored : List Id) :
    project [] stored = [] := by
  induction stored with
  | nil => rfl
  | cons identity stored inductionHypothesis =>
      simp [project, inductionHypothesis]

/-- The direct live-identity observer agrees with mapping stable identities
over the independently defined ordered contraction. -/
theorem liveIdentities_exact
    {Id : Type uId} {Row : Type uRow}
    (mask : List Bool) (occurrences : List (Occurrence Id Row)) :
    liveIdentities mask occurrences = identities (contract mask occurrences) := by
  induction mask generalizing occurrences with
  | nil => simp [liveIdentities, identities, contract]
  | cons keep mask inductionHypothesis =>
      cases occurrences with
      | nil => simp [liveIdentities, identities, contract]
      | cons occurrence occurrences =>
          cases keep <;>
            simp [liveIdentities, identities, contract,
              inductionHypothesis occurrences]

/-- Every live identity came from the source occurrence family. -/
theorem mem_liveIdentities_source
    {Id : Type uId} {Row : Type uRow}
    (mask : List Bool) (occurrences : List (Occurrence Id Row))
    {identity : Id}
    (member : identity ∈ liveIdentities mask occurrences) :
    identity ∈ identities occurrences := by
  induction mask generalizing occurrences with
  | nil => simp [liveIdentities] at member
  | cons keep mask inductionHypothesis =>
      cases occurrences with
      | nil => simp [liveIdentities] at member
      | cons occurrence occurrences =>
          cases keep with
          | false =>
              simp only [liveIdentities] at member
              simp only [identities, List.map_cons, List.mem_cons]
              exact Or.inr (inductionHypothesis occurrences member)
          | true =>
              simp only [liveIdentities, identities, List.map_cons,
                List.mem_cons] at member ⊢
              exact member.elim Or.inl fun tailMember =>
                Or.inr (inductionHypothesis occurrences tailMember)

/-- Every identity named by a payload index belongs to its source occurrence
family. -/
theorem mem_index_source
    {Id : Type uId} {Row : Type uRow}
    (accept : Row → Bool) (occurrences : List (Occurrence Id Row))
    {identity : Id} (member : identity ∈ index accept occurrences) :
    identity ∈ identities occurrences := by
  induction occurrences with
  | nil => simp [index] at member
  | cons occurrence occurrences inductionHypothesis =>
      by_cases accepted : accept occurrence.payload
      · simp only [index, accepted, if_true, identities, List.map_cons,
          List.mem_cons] at member ⊢
        exact member.elim Or.inl fun tailMember =>
          Or.inr (inductionHypothesis tailMember)
      · simp only [index, accepted] at member
        simp only [identities, List.map_cons, List.mem_cons]
        exact Or.inr (inductionHypothesis member)

/-- The executable coordinate-card projection is exactly the abstract live
identity projection followed by lookup of each retained identity's current
coordinate. -/
theorem projectCoordinates_eq_map_project
    {Id : Type uId} [DecidableEq Id]
    (live stored : List Id) :
    projectCoordinates live stored =
      (project live stored).map (fun identity => live.idxOf identity) := by
  induction stored with
  | nil => rfl
  | cons identity stored inductionHypothesis =>
      by_cases member : identity ∈ live <;>
        simp [projectCoordinates, coordinateCard, project, member,
          inductionHypothesis]

/-- Mapping a unique stable-identity index through its current identity list
recovers the independently defined dense-coordinate index. -/
theorem index_coordinates_exact
    {Id : Type uId} {Row : Type uRow} [DecidableEq Id]
    (accept : Row → Bool) (occurrences : List (Occurrence Id Row))
    (unique : (identities occurrences).Nodup) :
    (index accept occurrences).map
        (fun identity => (identities occurrences).idxOf identity) =
      denseIndex accept occurrences := by
  induction occurrences with
  | nil => simp [index, identities, denseIndex]
  | cons occurrence occurrences inductionHypothesis =>
      have uniqueParts := List.nodup_cons.mp unique
      have headNotSource : occurrence.id ∉ identities occurrences :=
        uniqueParts.1
      have tailUnique : (identities occurrences).Nodup := uniqueParts.2
      have tailExact := inductionHypothesis tailUnique
      have shiftedTail :
          (index accept occurrences).map
              (fun identity =>
                (occurrence.id :: identities occurrences).idxOf identity) =
            (denseIndex accept occurrences).map Nat.succ := by
        rw [← tailExact, List.map_map]
        apply List.map_congr_left
        intro identity member
        have identityInSource :=
          mem_index_source accept occurrences member
        have different : identity ≠ occurrence.id := by
          intro equal
          apply headNotSource
          simpa [equal] using identityInSource
        simpa [Nat.succ_eq_add_one] using
          (List.idxOf_cons_ne (identities occurrences)
            (Ne.symm different))
      by_cases accepted : accept occurrence.payload
      · have consShifted := congrArg (List.cons 0) shiftedTail
        simpa [index, identities, denseIndex, accepted] using consShifted
      · simpa [index, identities, denseIndex, accepted] using shiftedTail

/-- Adding a live identity which cannot occur in the stored index does not
change that index's live projection. -/
theorem project_cons_fresh
    {Id : Type uId} [DecidableEq Id]
    (identity : Id) (live stored : List Id)
    (fresh : identity ∉ stored) :
    project (identity :: live) stored = project live stored := by
  induction stored with
  | nil => rfl
  | cons storedIdentity stored inductionHypothesis =>
      have different : storedIdentity ≠ identity := by
        intro equal
        apply fresh
        simp [equal]
      have tailFresh : identity ∉ stored := by
        intro member
        exact fresh (by simp [member])
      simp [project, different, inductionHypothesis tailFresh]

/-- Stable-identity indexing commutes with ordered contraction.  The stored
index on the left is the source index itself; only the live-identity
projection changes.  The right side is an independent recomputation from the
contracted occurrence family. -/
theorem project_index_exact
    {Id : Type uId} {Row : Type uRow} [DecidableEq Id]
    (accept : Row → Bool) (mask : List Bool)
    (occurrences : List (Occurrence Id Row))
    (unique : (identities occurrences).Nodup) :
    project (liveIdentities mask occurrences) (index accept occurrences) =
      index accept (contract mask occurrences) := by
  induction mask generalizing occurrences with
  | nil => simp [liveIdentities, index, contract]
  | cons keep mask inductionHypothesis =>
      cases occurrences with
      | nil => simp [liveIdentities, index, contract]
      | cons occurrence occurrences =>
          have uniqueParts := List.nodup_cons.mp unique
          have headNotSource : occurrence.id ∉ identities occurrences :=
            uniqueParts.1
          have tailUnique : (identities occurrences).Nodup := uniqueParts.2
          have headNotLive :
              occurrence.id ∉ liveIdentities mask occurrences := by
            intro member
            exact headNotSource
              (mem_liveIdentities_source mask occurrences member)
          have tailExact :=
            inductionHypothesis occurrences tailUnique
          have headNotTailIndex :
              occurrence.id ∉ index accept occurrences := by
            intro member
            exact headNotSource
              (mem_index_source accept occurrences member)
          have projectWithHead := project_cons_fresh occurrence.id
            (liveIdentities mask occurrences) (index accept occurrences)
            headNotTailIndex
          cases keep with
          | false =>
              by_cases accepted : accept occurrence.payload <;>
                simp [project, liveIdentities, index, contract,
                  accepted, headNotLive, tailExact]
          | true =>
              by_cases accepted : accept occurrence.payload <;>
                simp [project, liveIdentities, index, contract,
                  accepted, headNotLive, tailExact, projectWithHead]

/-- Stable contraction preserves uniqueness of occurrence identities. -/
theorem identities_contract_nodup
    {Id : Type uId} {Row : Type uRow}
    (mask : List Bool) (occurrences : List (Occurrence Id Row))
    (unique : (identities occurrences).Nodup) :
    (identities (contract mask occurrences)).Nodup := by
  induction mask generalizing occurrences with
  | nil => simp [contract, identities]
  | cons keep mask inductionHypothesis =>
      cases occurrences with
      | nil => simp [contract, identities]
      | cons occurrence occurrences =>
          have uniqueParts := List.nodup_cons.mp unique
          have tailUnique : (identities occurrences).Nodup := uniqueParts.2
          cases keep with
          | false =>
              simpa [contract] using
                inductionHypothesis occurrences tailUnique
          | true =>
              have tailNodup :=
                inductionHypothesis occurrences tailUnique
              have headNotTarget :
                  occurrence.id ∉ identities (contract mask occurrences) := by
                intro member
                have liveMember :
                    occurrence.id ∈ liveIdentities mask occurrences := by
                  rw [liveIdentities_exact]
                  exact member
                exact uniqueParts.1
                  (mem_liveIdentities_source mask occurrences liveMember)
              exact List.nodup_cons.mpr ⟨headNotTarget, tailNodup⟩

/-- The coordinate-card realization commutes all the way to an independently
defined dense-coordinate index over the contracted occurrence family. -/
theorem projectCoordinates_index_exact
    {Id : Type uId} {Row : Type uRow} [DecidableEq Id]
    (accept : Row → Bool) (mask : List Bool)
    (occurrences : List (Occurrence Id Row))
    (unique : (identities occurrences).Nodup) :
    projectCoordinates (liveIdentities mask occurrences)
        (index accept occurrences) =
      denseIndex accept (contract mask occurrences) := by
  rw [projectCoordinates_eq_map_project]
  rw [project_index_exact accept mask occurrences unique]
  rw [liveIdentities_exact]
  exact index_coordinates_exact accept (contract mask occurrences)
    (identities_contract_nodup mask occurrences unique)

/-- A stable-identity leaf family needs zero leaf rewrites under contraction:
the source index is reused verbatim, and `project_index_exact` proves that its
live observation equals independent target reindexing. -/
theorem unchanged_index_realizes_contraction
    {Id : Type uId} {Row : Type uRow} [DecidableEq Id]
    (accept : Row → Bool) (mask : List Bool)
    (occurrences : List (Occurrence Id Row))
    (unique : (identities occurrences).Nodup) :
    let stored := index accept occurrences
    project (liveIdentities mask occurrences) stored =
      index accept (contract mask occurrences) := by
  exact project_index_exact accept mask occurrences unique

/-! ## Positive and negative controls -/

/-- Equal payloads remain independently removable through distinct stable
occurrence identities. -/
example :
    project
        (liveIdentities [false, true, true]
          [⟨10, "same"⟩, ⟨11, "same"⟩, ⟨12, "tail"⟩])
        (index (fun _ => true)
          [⟨10, "same"⟩, ⟨11, "same"⟩, ⟨12, "tail"⟩]) =
      [11, 12] := by
  decide

/-- Identity projection preserves the target's authored relative order. -/
example :
    project
        (liveIdentities [true, false, true]
          [⟨10, "left"⟩, ⟨11, "middle"⟩, ⟨12, "right"⟩])
        (index (fun _ => true)
          [⟨10, "left"⟩, ⟨11, "middle"⟩, ⟨12, "right"⟩]) =
      [10, 12] := by
  decide

/-- Reusing payload identity is insufficient: after removing only the first
equal occurrence, membership projection cannot distinguish the removed
occurrence from the retained one. -/
example :
    project
        (liveIdentities [false, true]
          [⟨7, "first"⟩, ⟨7, "second"⟩])
        (index (fun _ => true)
          [⟨7, "first"⟩, ⟨7, "second"⟩]) ≠
      index (fun _ => true)
        (contract [false, true]
          [⟨7, "first"⟩, ⟨7, "second"⟩]) := by
  decide

#print axioms mem_liveIdentities_source
#print axioms project_index_exact
#print axioms projectCoordinates_index_exact
#print axioms unchanged_index_realizes_contraction

end Mettapedia.GSLT.Dynamics.StableOccurrenceIdentityIndex
