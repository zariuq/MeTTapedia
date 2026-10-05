import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-!
# Data provenance through matching and merge

If one matched atom belongs to a variable-free, subatom-closed data class,
every resulting value assignment belongs to that class. Merging preserves the
same invariant, including equality-class reconciliation and arbitrary fold
order. The relations here are the executable-independent HE specification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Spec.Match.DataPreservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Merge

def AssignmentsIn (allowed : Atom → Prop) (bindings : Bindings) : Prop :=
  ∀ name value, (name, value) ∈ bindings.assignments → allowed value

theorem AssignmentsIn.empty (allowed : Atom → Prop) :
    AssignmentsIn allowed Bindings.empty := by
  intro name value member
  simp [Bindings.empty] at member

theorem AssignmentsIn.assign {allowed : Atom → Prop} {bindings : Bindings}
    (stored : AssignmentsIn allowed bindings) {name : String} {value : Atom}
    (data : allowed value) : AssignmentsIn allowed (bindings.assign name value) := by
  intro key atom member
  by_cases bound : bindings.isBound name = true
  · simp only [Bindings.assign, bound, ↓reduceIte] at member
    obtain ⟨⟨oldKey, oldValue⟩, oldMember, same⟩ := List.mem_map.mp member
    dsimp only at same
    by_cases equal : (oldKey == name) = true
    · simp only [equal, ↓reduceIte] at same
      have equalValue : value = atom := by simpa using congrArg Prod.snd same
      exact equalValue ▸ data
    · have equalValue : oldValue = atom := by
        simpa [equal] using congrArg Prod.snd same
      exact equalValue ▸ stored _ _ oldMember
  · simp only [Bindings.assign, bound] at member
    rcases List.mem_append.mp member with old | fresh
    · exact stored _ _ old
    · have equalValue : atom = value := congrArg Prod.snd (List.mem_singleton.mp fresh)
      exact equalValue.symm ▸ data

theorem AssignmentsIn.addEquality {allowed : Atom → Prop} {bindings : Bindings}
    (stored : AssignmentsIn allowed bindings) (left right : String) :
    AssignmentsIn allowed (bindings.addEquality left right) := stored

theorem AssignmentsIn.lookup {allowed : Atom → Prop} {bindings : Bindings}
    (stored : AssignmentsIn allowed bindings) {name : String} {value : Atom}
    (found : bindings.lookup name = some value) : allowed value := by
  obtain ⟨entries, equalities⟩ := bindings
  induction entries with
  | nil => simp [Bindings.lookup, List.lookup] at found
  | cons entry rest ih =>
      obtain ⟨key, atom⟩ := entry
      simp only [Bindings.lookup, List.lookup] at found
      split at found
      · cases found
        exact stored key value (by simp)
      · exact ih (fun k a member => stored k a (by simp [member])) found

theorem AssignmentsIn.classValues {allowed : Atom → Prop} {bindings : Bindings}
    (stored : AssignmentsIn allowed bindings) {name : String} {value : Atom}
    (member : value ∈ bindings.classValues name) : allowed value := by
  obtain ⟨key, _, found⟩ := List.mem_filterMap.mp member
  exact stored.lookup found

/-- Matching against data stores only data, including during reconciliation. -/
theorem match_preserves {allowed : Atom → Prop}
    (noVariables : ∀ name, ¬allowed (.var name))
    (subatoms : ∀ items, allowed (.expression items) → ∀ atom ∈ items, allowed atom)
    {left right : Atom} {out : Bindings}
    (derivation : MatchRel equalityGroundedSemantic left right out)
    (data : allowed left ∨ allowed right) : AssignmentsIn allowed out := by
  apply MatchRel.rec
    (motive_1 := fun left right out _ =>
      (allowed left ∨ allowed right) → AssignmentsIn allowed out)
    (motive_2 := fun left right seed out _ =>
      AssignmentsIn allowed seed →
      ((∀ atom ∈ left, allowed atom) ∨ (∀ atom ∈ right, allowed atom)) →
        AssignmentsIn allowed out)
    (motive_3 := fun seed _ value out _ =>
      AssignmentsIn allowed seed → allowed value → AssignmentsIn allowed out)
    (motive_4 := fun seed _ _ out _ =>
      AssignmentsIn allowed seed → AssignmentsIn allowed out)
    (motive_5 := fun seed constraints out _ =>
      AssignmentsIn allowed seed →
      (∀ name value, Constraint.value name value ∈ constraints → allowed value) →
        AssignmentsIn allowed out)
    (motive_6 := fun left right out _ =>
      AssignmentsIn allowed left → AssignmentsIn allowed right → AssignmentsIn allowed out)
    (t := derivation)
  next => intro symbol admissible data; exact .empty allowed
  next =>
    intro left right admissible data
    exact (data.elim (noVariables left) (noVariables right)).elim
  next =>
    intro name value nonvar admissible data
    exact (AssignmentsIn.empty allowed).assign (data.resolve_left (noVariables name))
  next =>
    intro value name nonvar admissible data
    exact (AssignmentsIn.empty allowed).assign (data.resolve_right (noVariables name))
  next =>
    intro left right out items admissible ih data
    exact ih (.empty allowed) (data.imp (subatoms left) (subatoms right))
  next =>
    intro grounded right out nonvar custom matched admissible data
    rcases matched with ⟨_, rfl⟩
    exact .empty allowed
  next =>
    intro left grounded out nonvar priority custom matched admissible data
    rcases matched with ⟨_, rfl⟩
    exact .empty allowed
  next => intro left right noLeft noRight admissible data; exact .empty allowed
  next => intro seed stored data; exact stored
  next =>
    intro left right lefts rights seed matched next out head merge tail ihHead ihMerge ihTail
      stored data
    have headData : allowed left ∨ allowed right :=
      data.imp (fun h => h _ (by simp)) (fun h => h _ (by simp))
    have tailData : (∀ atom ∈ lefts, allowed atom) ∨ (∀ atom ∈ rights, allowed atom) :=
      data.imp (fun h atom member => h atom (by simp [member]))
        (fun h atom member => h atom (by simp [member]))
    exact ihTail (ihMerge stored (ihHead headData)) tailData
  next => intro seed name value absent stored data; exact stored.assign data
  next => intro seed name value first rest values agree same stored data; exact stored
  next =>
    intro seed name value first rest matched out values agree different head merge ihHead ihMerge
      stored data
    exact ihMerge stored (ihHead (.inr data))
  next =>
    intro seed name value first rest matched out values disagree listed merge ihList ihMerge
      stored data
    have firstData : allowed first :=
      stored.classValues ((List.Perm.mem_iff values).mp (by simp))
    have replicated : ∀ atom ∈ List.replicate (rest.length + 1) first, allowed atom := by
      intro atom member
      simpa [(List.mem_replicate.mp member).2] using firstData
    exact ihMerge stored (ihList (.empty allowed) (.inl replicated))
  next => intro seed left right values same agree stored; exact stored.addEquality left right
  next =>
    intro seed left right first rest matched out values disagree listed merge ihList ihMerge stored
    have joined := stored.addEquality left right
    have firstData : allowed first :=
      joined.classValues ((List.Perm.mem_iff values).mp (by simp))
    have replicated : ∀ atom ∈ List.replicate rest.length first, allowed atom := by
      intro atom member
      simpa [(List.mem_replicate.mp member).2] using firstData
    exact ihMerge joined (ihList (.empty allowed) (.inl replicated))
  next => intro seed stored data; exact stored
  next =>
    intro seed next out name value rest added tail ihAdd ihTail stored data
    exact ihTail (ihAdd stored (data name value (by simp)))
      (fun key atom member => data key atom (by simp [member]))
  next =>
    intro seed next out left right rest added tail ihAdd ihTail stored data
    exact ihTail (ihAdd stored) (fun key atom member => data key atom (by simp [member]))
  next =>
    intro left right out order perm fold ihFold leftData rightData
    exact ihFold leftData (fun name value member => rightData name value
      (SolutionTheory.value_mem_constraints_iff.mp ((List.Perm.mem_iff perm).mp member)))
  all_goals assumption

/-- Equality aliases and permutation of merge constraints preserve data values. -/
theorem merge_preserves {allowed : Atom → Prop}
    (noVariables : ∀ name, ¬allowed (.var name))
    (subatoms : ∀ items, allowed (.expression items) → ∀ atom ∈ items, allowed atom)
    {left right out : Bindings}
    (derivation : MergeRel equalityGroundedSemantic left right out)
    (leftData : AssignmentsIn allowed left) (rightData : AssignmentsIn allowed right) :
    AssignmentsIn allowed out := by
  apply MergeRel.rec
    (motive_1 := fun left right out _ =>
      (allowed left ∨ allowed right) → AssignmentsIn allowed out)
    (motive_2 := fun left right seed out _ =>
      AssignmentsIn allowed seed →
      ((∀ atom ∈ left, allowed atom) ∨ (∀ atom ∈ right, allowed atom)) →
        AssignmentsIn allowed out)
    (motive_3 := fun seed _ value out _ =>
      AssignmentsIn allowed seed → allowed value → AssignmentsIn allowed out)
    (motive_4 := fun seed _ _ out _ =>
      AssignmentsIn allowed seed → AssignmentsIn allowed out)
    (motive_5 := fun seed constraints out _ =>
      AssignmentsIn allowed seed →
      (∀ name value, Constraint.value name value ∈ constraints → allowed value) →
        AssignmentsIn allowed out)
    (motive_6 := fun left right out _ =>
      AssignmentsIn allowed left → AssignmentsIn allowed right → AssignmentsIn allowed out)
    (t := derivation)
  next => intro symbol admissible data; exact .empty allowed
  next =>
    intro left right admissible data
    exact (data.elim (noVariables left) (noVariables right)).elim
  next =>
    intro name value nonvar admissible data
    exact (AssignmentsIn.empty allowed).assign (data.resolve_left (noVariables name))
  next =>
    intro value name nonvar admissible data
    exact (AssignmentsIn.empty allowed).assign (data.resolve_right (noVariables name))
  next =>
    intro left right out items admissible ih data
    exact ih (.empty allowed) (data.imp (subatoms left) (subatoms right))
  next =>
    intro grounded right out nonvar custom matched admissible data
    rcases matched with ⟨_, rfl⟩
    exact .empty allowed
  next =>
    intro left grounded out nonvar priority custom matched admissible data
    rcases matched with ⟨_, rfl⟩
    exact .empty allowed
  next => intro left right noLeft noRight admissible data; exact .empty allowed
  next => intro seed stored data; exact stored
  next =>
    intro left right lefts rights seed matched next out head merge tail ihHead ihMerge ihTail
      stored data
    have headData : allowed left ∨ allowed right :=
      data.imp (fun h => h _ (by simp)) (fun h => h _ (by simp))
    have tailData : (∀ atom ∈ lefts, allowed atom) ∨ (∀ atom ∈ rights, allowed atom) :=
      data.imp (fun h atom member => h atom (by simp [member]))
        (fun h atom member => h atom (by simp [member]))
    exact ihTail (ihMerge stored (ihHead headData)) tailData
  next => intro seed name value absent stored data; exact stored.assign data
  next => intro seed name value first rest values agree same stored data; exact stored
  next =>
    intro seed name value first rest matched out values agree different head merge ihHead ihMerge
      stored data
    exact ihMerge stored (ihHead (.inr data))
  next =>
    intro seed name value first rest matched out values disagree listed merge ihList ihMerge
      stored data
    have firstData : allowed first :=
      stored.classValues ((List.Perm.mem_iff values).mp (by simp))
    have replicated : ∀ atom ∈ List.replicate (rest.length + 1) first, allowed atom := by
      intro atom member
      simpa [(List.mem_replicate.mp member).2] using firstData
    exact ihMerge stored (ihList (.empty allowed) (.inl replicated))
  next => intro seed left right values same agree stored; exact stored.addEquality left right
  next =>
    intro seed left right first rest matched out values disagree listed merge ihList ihMerge stored
    have joined := stored.addEquality left right
    have firstData : allowed first :=
      joined.classValues ((List.Perm.mem_iff values).mp (by simp))
    have replicated : ∀ atom ∈ List.replicate rest.length first, allowed atom := by
      intro atom member
      simpa [(List.mem_replicate.mp member).2] using firstData
    exact ihMerge joined (ihList (.empty allowed) (.inl replicated))
  next => intro seed stored data; exact stored
  next =>
    intro seed next out name value rest added tail ihAdd ihTail stored data
    exact ihTail (ihAdd stored (data name value (by simp)))
      (fun key atom member => data key atom (by simp [member]))
  next =>
    intro seed next out left right rest added tail ihAdd ihTail stored data
    exact ihTail (ihAdd stored) (fun key atom member => data key atom (by simp [member]))
  next =>
    intro left right out order perm fold ihFold leftData rightData
    exact ihFold leftData (fun name value member => rightData name value
      (SolutionTheory.value_mem_constraints_iff.mp ((List.Perm.mem_iff perm).mp member)))
  all_goals assumption

end Mettapedia.Languages.MeTTa.HE.Spec.Match.DataPreservation
