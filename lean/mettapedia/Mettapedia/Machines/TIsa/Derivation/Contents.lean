import Mettapedia.Machines.TIsa.Derivation.StepAdequacy

/-!
# What a step does to the values of the store

The values of a store, counted (`Store.values`), are what a multiset store observes. A step of the
step theory removes the values of its taken occurrences and adds its made values
(`groundStep_values`): the values after, plus the taken values, are the values before, plus the
made values. For rules whose take patterns and produced terms are values themselves, these are the
rule's own (`groundStep_ground_values`), so counting invariants of a program follow from its rules.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe u s v w

variable {T : Type u} {S : Type s} {V : Type v} {B : Type w}

/-- **The values of a store**, counted. -/
def Store.values (st : Store V) : Multiset V := (st.occurrences.map Prod.snd : Multiset V)

theorem Store.values_eq_of_same {first second : Store V} (same : Store.SameOccurrences first second) :
    first.values = second.values := by
  obtain ⟨firstDistinct, secondDistinct, ids, values⟩ := same
  have perm : first.occurrences.Perm second.occurrences := by
    apply (List.perm_ext_iff_of_nodup (List.Nodup.of_map Prod.fst firstDistinct)
      (List.Nodup.of_map Prod.fst secondDistinct)).mpr
    rintro ⟨o, a⟩
    constructor
    · intro inside
      have member : o ∈ first.ids := Store.mem_ids.mpr ⟨a, inside⟩
      have value := (Store.valueOf_eq_some firstDistinct).mpr inside
      rw [values o member] at value
      exact (Store.valueOf_eq_some secondDistinct).mp value
    · intro inside
      have member : o ∈ first.ids := by
        apply List.mem_toFinset.mp
        rw [ids]
        exact List.mem_toFinset.mpr (Store.mem_ids.mpr ⟨a, inside⟩)
      have value := (Store.valueOf_eq_some secondDistinct).mpr inside
      rw [← values o member] at value
      exact (Store.valueOf_eq_some firstDistinct).mp value
  exact Multiset.coe_eq_coe.mpr (perm.map Prod.snd)

/-- Publication with chosen identities removes the taken occurrences and adds the made values. -/
theorem values_publishWith (st : Store V) (m : Match V B) (ids : List ℕ)
    (lengths : ids.length = m.made.length) :
    (publishWith st m ids).values +
        ((st.occurrences.filter fun x => m.taken.contains x.1).map Prod.snd : Multiset V) =
      st.values + (m.made : Multiset V) := by
  have split := (List.filter_append_perm (fun x : ℕ × V => m.taken.contains x.1) st.occurrences).map Prod.snd
  have whole : st.values = ((st.occurrences.filter fun x => m.taken.contains x.1).map Prod.snd : Multiset V) +
      ((st.occurrences.filter fun x => !(m.taken.contains x.1)).map Prod.snd : Multiset V) := by
    rw [Store.values, Multiset.coe_add, ← List.map_append]
    exact (Multiset.coe_eq_coe.mpr split).symm
  have published : (publishWith st m ids).values =
      ((st.occurrences.filter fun x => !(m.taken.contains x.1)).map Prod.snd : Multiset V) +
        (m.made : Multiset V) := by
    simp only [Store.values, publishWith, List.map_append, List.map_snd_zip (le_of_eq lengths.symm),
      Multiset.coe_add]
  rw [published, whole]
  abel

/-- The taken occurrences of a word accepted for the takes are the word itself. -/
theorem taken_perm {st : Store V} (distinct : st.Distinct) (xs : List (ℕ × V))
    (inside : ∀ x ∈ xs, x ∈ st.occurrences) (nodup : (xs.map Prod.fst).Nodup) :
    (st.occurrences.filter fun x => (xs.map Prod.fst).contains x.1).Perm xs := by
  apply (List.perm_ext_iff_of_nodup ((List.Nodup.of_map Prod.fst distinct).filter _)
    (List.Nodup.of_map Prod.fst nodup)).mpr
  intro x
  simp only [List.mem_filter, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨present, y, member, same⟩
    have equal : y = x := List.inj_on_of_nodup_map distinct (inside y member) present same
    rw [← equal]
    exact member
  · intro member
    exact ⟨inside x member, x, member, rfl⟩

variable [DecidableEq V] [Inhabited T] {A : SubstitutionAction T S} {M : Matcher T V B}
  (Sem : Semantics A M)

/-- **A step removes the values of its taken occurrences and adds its made values.** -/
theorem Semantics.groundStep_values (P : List (Rule T)) {st st' : Store V} (distinct : st.Distinct)
    (ranged : ∀ r ∈ P, RangeRestricted M r) (stepped : Sem.GroundStep P st st') :
    ∃ f ∈ firings M P st, ∃ xs : List (ℕ × V), xs.map Prod.fst = f.2.taken ∧
      (∀ x ∈ xs, x ∈ st.occurrences) ∧
      (∃ m₁, attemptAll M .take f.1.body.take (Match.start M) xs = some m₁) ∧
      st'.values + (xs.map Prod.snd : Multiset V) = st.values + (f.2.made : Multiset V) := by
  obtain ⟨⟨r, m⟩, found, ids, _, _, lengths, same⟩ :=
    (Sem.groundStep_iff P st st' distinct ranged).mp stepped
  obtain ⟨_, solved⟩ := (mem_firings P st r m).mp found
  obtain ⟨xs, ys, m₁, m₂, xsIn, _, takes, reads, dets⟩ := (mem_solve_goals st r m).mp solved
  obtain ⟨takenEq, _, _, _, nodup, _⟩ := attemptAll_take r.body.take _ m₁ xs takes
  obtain ⟨_, takenEq₂, _, _, _⟩ := attemptAll_read r.body.read m₁ m₂ ys reads
  obtain ⟨_, takenEq₃, _⟩ := applyAll_fields st (determinates r) m₂ m dets
  have taken : m.taken = xs.map Prod.fst := by
    rw [takenEq₃, takenEq₂, takenEq]
    simp [Match.start]
  have takenNodup : (xs.map Prod.fst).Nodup := by
    rw [← taken, takenEq₃, takenEq₂]
    exact nodup (by simp [Match.start])
  refine ⟨(r, m), found, xs, taken.symm, xsIn, ⟨m₁, takes⟩, ?_⟩
  rw [← Store.values_eq_of_same same]
  have law := values_publishWith st m ids lengths
  rw [taken] at law
  rw [← law, Multiset.coe_eq_coe.mpr ((taken_perm distinct xs xsIn takenNodup).map Prod.snd)]

omit [DecidableEq V] [Inhabited T] in
theorem Semantics.ground_words (σ : S) :
    ∀ (ws : List V) (xs : List (ℕ × V)),
      List.Forall₂ (fun p x => A.E (A.apply σ p) (Sem.embed x.2)) (ws.map Sem.embed) xs →
      xs.map Prod.snd = ws
  | [], [], _ => rfl
  | [], _ :: _, related => by simp at related
  | _ :: _, [], related => by simp at related
  | w :: ws, x :: xs, related => by
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp related
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨((Sem.value_iff (Sem.fixed σ w)).mp head).symm, Semantics.ground_words σ ws xs tail⟩

omit [DecidableEq V] [Inhabited T] in
/-- The values an accepted word of ground take patterns matches are the patterns' own. -/
theorem Semantics.ground_takes (patterns : List V) (m₀ m : Match V B) (xs : List (ℕ × V))
    (accepted : attemptAll M .take (patterns.map Sem.embed) m₀ xs = some m)
    (inhabited : ∃ σ, Sem.Denotes m₀.bindings σ) : xs.map Prod.snd = patterns := by
  obtain ⟨σ, denoted⟩ := Sem.attemptAll_inhabited .take _ _ _ xs accepted inhabited
  exact Sem.ground_words σ patterns xs ((Sem.attemptAll_denotes .take _ _ _ xs accepted σ).mp denoted).2

omit [DecidableEq V] [Inhabited T] in
theorem Semantics.ground_values {θ : B} {σ : S} (denoted : Sem.Denotes θ σ) :
    ∀ (us ws : List V), List.Forall₂ (fun t w => M.instantiate θ t = some w) (us.map Sem.embed) ws →
      ws = us
  | [], [], _ => rfl
  | [], _ :: _, related => by simp at related
  | _ :: _, [], related => by simp at related
  | u :: us, w :: ws, related => by
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp related
      have valued := Sem.instantiate_sound θ _ w σ head denoted
      have same : u = w := (Sem.value_iff (Sem.fixed σ u)).mp valued
      rw [same, Semantics.ground_values denoted us ws tail]

omit [Inhabited T] in
/-- The made values of a firing of a rule whose produced terms are values are those values. -/
theorem Semantics.made_ground (P : List (Rule T)) (st : Store V) (r : Rule T) (m : Match V B)
    (found : (r, m) ∈ firings M P st) (us : List V) (ground : r.body.produce = us.map Sem.embed) :
    m.made = us := by
  obtain ⟨_, solved⟩ := (mem_firings P st r m).mp found
  obtain ⟨xs, ys, m₁, m₂, _, _, takes, reads, dets⟩ := (mem_solve_goals st r m).mp solved
  obtain ⟨_, _, _, madeEq₁, _, _⟩ := attemptAll_take r.body.take _ m₁ xs takes
  obtain ⟨_, _, _, madeEq₂, _⟩ := attemptAll_read r.body.read m₁ m₂ ys reads
  obtain ⟨_, _, cs, ws, _, wsRel, rfl⟩ := (applyAll_determinates_iff st r m₂ m).mp dets
  obtain ⟨σ, denoted⟩ := Sem.attemptAll_inhabited .read _ _ _ ys reads
    (Sem.attemptAll_inhabited .take _ _ _ xs takes ⟨A.identity, Sem.denotes_empty _⟩)
  rw [ground] at wsRel
  change m₂.made ++ ws = us
  rw [madeEq₂, madeEq₁, Sem.ground_values denoted us ws wsRel]
  rfl

/-- **For rules whose take patterns and produced terms are values, a step removes the rule's take
values and adds its produced values.** -/
theorem Semantics.groundStep_ground_values (P : List (Rule T)) (takeValues madeValues : Rule T → List V)
    (ground : ∀ r ∈ P, r.body.take = (takeValues r).map Sem.embed ∧
      r.body.produce = (madeValues r).map Sem.embed)
    {st st' : Store V} (distinct : st.Distinct) (ranged : ∀ r ∈ P, RangeRestricted M r)
    (stepped : Sem.GroundStep P st st') :
    ∃ r ∈ P, st'.values + (takeValues r : Multiset V) = st.values + (madeValues r : Multiset V) := by
  obtain ⟨⟨r, m⟩, found, xs, _, _, ⟨m₁, takes⟩, law⟩ := Sem.groundStep_values P distinct ranged stepped
  have member := ((mem_firings P st r m).mp found).1
  obtain ⟨takeGround, madeGround⟩ := ground r member
  rw [takeGround] at takes
  have taken := Sem.ground_takes (takeValues r) _ m₁ xs takes ⟨A.identity, Sem.denotes_empty _⟩
  rw [taken, Sem.made_ground P st r m found (madeValues r) madeGround] at law
  exact ⟨r, member, law⟩

/-- **A firing the evaluator finds is a step of the step theory**, published with identities past
every present one; no bound on the store's fresh identity is needed. -/
theorem Semantics.exists_groundStep (P : List (Rule T)) {st : Store V} (distinct : st.Distinct)
    {f : Rule T × Match V B} (found : f ∈ firings M P st) : ∃ st', Sem.GroundStep P st st' := by
  let bound := st.ids.sum + 1
  let ids := (List.range f.2.made.length).map (bound + ·)
  have nodup : ids.Nodup := (List.nodup_range).map (fun _ _ same => Nat.add_left_cancel same)
  have fresh : ∀ o ∈ ids, o ∉ st.ids := by
    intro o member present
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    have := List.le_sum_of_mem present
    omega
  obtain ⟨_, admitted, reads⟩ :=
    Sem.admits_stepFiring P st distinct f.1 f.2 found ids nodup fresh (by simp [ids])
  exact ⟨_, _, admitted, reads⟩

end Mettapedia.Machines.TIsa.Derivation
