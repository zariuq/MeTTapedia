import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Observation

/-!
# Observer records: what an observer knows, and the renamings it cannot see

An observer never sees the raw value of an identity, only the structure of what it recorded: which
identities it saw together, in which relations. This module makes that structure the record.

* **Records** (`Record`): the relations among identities that an observer recorded and can test, in
  the order it recorded them, each a finite set of tuples. A held reference is the singleton relation
  `{[o]}` (`Record.reference`), a sighted set is the unary relation of its members
  (`Record.sighting`), and an ordered tuple is the singleton relation of the tuple (`Record.tuple`).
  Every other finite relation the observer can test is an entry too.
* **Renaming** (`Record.rename`) acts on every relation in place. It is an action of the bijections of
  identities (`rename_refl`, `rename_trans`, `rename_symm_rename`), compatible with appending
  (`rename_append`).
* **Isomorphisms and automorphisms**: a renaming carries one record to another when it carries every
  relation to the relation recorded in the same place. These form a groupoid
  (`Record.rename_eq_symm`, `Record.rename_eq_trans`). The renamings that carry a record to itself
  form its **automorphism group** (`Record.automorphisms`): the stabilizer of the record, in the sense
  of Fraenkel–Mostowski permutation models, not the pointwise fixer of the identities it mentions.
* **Fixing pointwise is sufficient, not necessary.** A renaming that fixes every identity the record
  mentions (`Record.support`) is an automorphism (`rename_eq_self_of_fixes`). The exchange of the two
  members of a sighted set is an automorphism that fixes neither (`RecordControls.sighting_swap`).
* **The pointwise case** (`Record.references`, `Record.ofClient`): a record whose every entry is a held
  reference. Its automorphisms are exactly the renamings that fix every identity it mentions
  (`references_rename_eq_iff`). A client context of the client layer (`Client`) is such a record
  (`ofClient_rename_eq_iff`), and its escaped identities are the identities the record mentions
  (`support_ofClient`).
* **Sightings of predicate queries** (`querySightings`, `runSightings`): each query records its
  sighted set as one unary relation. Renaming a query renames its relation (`querySightings_rename`),
  and flattened, a run's sightings are the client layer's (`support_runSightings`).

## Controls (`RecordControls`)

* The exchange of `5` and `6` is an automorphism of the record that sighted `{5, 6}`
  (`sighting_swap`). It is not one once the record also holds `5` (`reference_blocks`), sighted the
  ordered pair `(5, 6)` (`pair_blocks`), or sighted `{5}` alone (`singleton_blocks`).
* A renaming that carries the sighted set `{5, 6}` onto `{5, 7}` is not an automorphism
  (`onto_other_refused`).
* Relations are finer than sets: the rotation `5 ↦ 6 ↦ 7 ↦ 5` is an automorphism of the cyclic
  relation on `5, 6, 7`, and the exchange of `5` and `6` is not, although both carry the set
  `{5, 6, 7}` to itself (`cycle_rotation`, `cycle_not_swap`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns

universe uT uS uO

/-! ## Records -/

/-- **An observer's record**: the relations among identities it recorded and can test, in the order
it recorded them. Each relation is a finite set of tuples of identities. -/
abbrev Record (O : Type uO) := List (Finset (List O))

namespace Record

variable {O : Type uO}

/-- A held reference: the singleton relation `{[o]}`. -/
def reference (o : O) : Finset (List O) := {[o]}

/-- The tuple of one identity. -/
def single : O ↪ List O := ⟨fun o => [o], fun _ _ same => List.singleton_inj.mp same⟩

/-- A sighted set: the unary relation of its members. -/
def sighting (s : Finset O) : Finset (List O) := s.map single

/-- An ordered tuple: the singleton relation of the tuple. -/
def tuple (l : List O) : Finset (List O) := {l}

/-- A renaming acts on tuples. -/
def tupleEmbedding (π : O ≃ O) : List O ↪ List O := ⟨List.map π, List.map_injective_iff.mpr π.injective⟩

/-- Rename one recorded relation. -/
def renameEntry (π : O ≃ O) (e : Finset (List O)) : Finset (List O) := e.map (tupleEmbedding π)

/-- **Rename a record**: every relation, in place. -/
def rename (π : O ≃ O) (r : Record O) : Record O := r.map (renameEntry π)

theorem renameEntry_refl (e : Finset (List O)) : renameEntry (Equiv.refl O) e = e := by
  ext l
  simp [renameEntry, tupleEmbedding]

theorem renameEntry_trans (π ρ : O ≃ O) (e : Finset (List O)) :
    renameEntry (π.trans ρ) e = renameEntry ρ (renameEntry π e) := by
  ext l
  simp [renameEntry, tupleEmbedding, List.map_map, Function.comp_def]

theorem rename_refl (r : Record O) : rename (Equiv.refl O) r = r :=
  list_map_eq_self fun e _ => renameEntry_refl e

theorem rename_trans (π ρ : O ≃ O) (r : Record O) :
    rename (π.trans ρ) r = rename ρ (rename π r) := by
  simp only [rename, List.map_map]
  exact List.map_congr_left fun e _ => renameEntry_trans π ρ e

theorem rename_symm_rename (π : O ≃ O) (r : Record O) : rename π.symm (rename π r) = r := by
  rw [← rename_trans, Equiv.self_trans_symm, rename_refl]

theorem rename_rename_symm (π : O ≃ O) (r : Record O) : rename π (rename π.symm r) = r := by
  rw [← rename_trans, Equiv.symm_trans_self, rename_refl]

theorem rename_append (π : O ≃ O) (r s : Record O) : rename π (r ++ s) = rename π r ++ rename π s :=
  List.map_append

theorem rename_nil (π : O ≃ O) : rename π ([] : Record O) = [] := rfl

theorem length_rename (π : O ≃ O) (r : Record O) : (rename π r).length = r.length :=
  List.length_map _

theorem rename_injective (π : O ≃ O) : Function.Injective (rename π : Record O → Record O) :=
  fun r s same => by rw [← rename_symm_rename π r, same, rename_symm_rename]

/-! ## Isomorphisms and automorphisms -/

/-- Isomorphisms of records invert. -/
theorem rename_eq_symm {π : O ≃ O} {r s : Record O} (carried : rename π r = s) :
    rename π.symm s = r := by
  rw [← carried, rename_symm_rename]

/-- Isomorphisms of records compose. -/
theorem rename_eq_trans {π ρ : O ≃ O} {r s u : Record O} (first : rename π r = s)
    (second : rename ρ s = u) : rename (π.trans ρ) r = u := by
  rw [rename_trans, first, second]

/-- **The automorphism group of a record**: the renamings that carry every recorded relation to
itself, the stabilizer of the record. -/
def automorphisms (r : Record O) : Subgroup (Equiv.Perm O) where
  carrier := {π | rename π r = r}
  one_mem' := rename_refl r
  mul_mem' {π ρ} first second := by
    show rename (ρ.trans π) r = r
    exact rename_eq_trans second first
  inv_mem' {π} carried := by
    show rename π.symm r = r
    exact rename_eq_symm carried

theorem mem_automorphisms {r : Record O} {π : Equiv.Perm O} :
    π ∈ automorphisms r ↔ rename π r = r :=
  Iff.rfl

/-- The automorphisms of an appended record are the common automorphisms of its parts. -/
theorem rename_append_eq_iff {π : O ≃ O} {r s : Record O} :
    rename π (r ++ s) = r ++ s ↔ rename π r = r ∧ rename π s = s := by
  rw [rename_append]
  exact ⟨fun same => List.append_inj same (length_rename π r), fun ⟨first, second⟩ => by rw [first, second]⟩

/-- The common past of two records related by a renaming is carried to itself. -/
theorem rename_prefix {π : O ≃ O} {r s s' : Record O} (carried : rename π (r ++ s) = r ++ s') :
    rename π r = r ∧ rename π s = s' := by
  rw [rename_append] at carried
  exact List.append_inj carried (length_rename π r)

/-! ## Held references -/

theorem renameEntry_reference (π : O ≃ O) (o : O) : renameEntry π (reference o) = reference (π o) := by
  simp [renameEntry, reference, tupleEmbedding]

theorem reference_injective : Function.Injective (reference : O → Finset (List O)) := fun a b same => by
  have := Finset.singleton_inj.mp same
  exact List.singleton_inj.mp this

theorem renameEntry_tuple (π : O ≃ O) (l : List O) : renameEntry π (tuple l) = tuple (l.map π) := by
  simp [renameEntry, tuple, tupleEmbedding]

theorem renameEntry_sighting (π : O ≃ O) (s : Finset O) :
    renameEntry π (sighting s) = sighting (s.map π.toEmbedding) := by
  simp only [renameEntry, sighting, Finset.map_map]
  rfl

/-- **A record of held references.** -/
def references (l : List O) : Record O := l.map reference

/-- **The automorphisms of a record of references fix every reference.** -/
theorem references_rename_eq_iff {π : O ≃ O} {l : List O} :
    rename π (references l) = references l ↔ ∀ o ∈ l, π o = o := by
  simp only [rename, references, List.map_map]
  rw [List.map_inj_left]
  exact forall₂_congr fun o _ => by
    rw [Function.comp_apply, renameEntry_reference]
    exact reference_injective.eq_iff

/-! ## The identities a record mentions -/

section Support

variable [DecidableEq O]

/-- **The identities a record mentions.** -/
def support : Record O → Finset O
  | [] => ∅
  | e :: rest => e.biUnion List.toFinset ∪ support rest

theorem mem_support {o : O} : ∀ {r : Record O}, o ∈ support r ↔ ∃ e ∈ r, ∃ l ∈ e, o ∈ l
  | [] => by simp [support]
  | e :: rest => by
      rw [support, Finset.mem_union, Finset.mem_biUnion, mem_support]
      simp only [List.mem_toFinset, List.mem_cons, exists_eq_or_imp]

theorem support_append (r s : Record O) : support (r ++ s) = support r ∪ support s := by
  ext o
  simp only [mem_support, Finset.mem_union, List.mem_append]
  constructor
  · rintro ⟨e, here | there, rest⟩
    · exact Or.inl ⟨e, here, rest⟩
    · exact Or.inr ⟨e, there, rest⟩
  · rintro (⟨e, here, rest⟩ | ⟨e, there, rest⟩)
    · exact ⟨e, Or.inl here, rest⟩
    · exact ⟨e, Or.inr there, rest⟩

/-- **Fixing every mentioned identity is an automorphism**: the pointwise fixer lies in the
stabilizer. -/
theorem rename_eq_self_of_fixes {π : O ≃ O} {r : Record O} (fixes : ∀ o ∈ support r, π o = o) :
    rename π r = r := by
  refine list_map_eq_self fun e member => ?_
  have fixed : ∀ l ∈ e, tupleEmbedding π l = l := fun l inside =>
    list_map_eq_self fun o there => fixes o (mem_support.mpr ⟨e, member, l, inside, there⟩)
  ext l
  simp only [renameEntry, Finset.mem_map]
  constructor
  · rintro ⟨a, inside, rfl⟩
    rw [fixed a inside]
    exact inside
  · intro inside
    exact ⟨l, inside, fixed l inside⟩

theorem support_reference (o : O) : (reference o).biUnion List.toFinset = {o} := by
  simp [reference]

theorem support_references (l : List O) : support (references l) = l.toFinset := by
  ext o
  simp [mem_support, references, reference]

theorem support_sighting (s : Finset O) : (sighting s).biUnion List.toFinset = s := by
  ext o
  simp only [sighting, Finset.mem_biUnion, Finset.mem_map, List.mem_toFinset]
  constructor
  · rintro ⟨_, ⟨a, member, rfl⟩, inside⟩
    have same : o = a := List.mem_singleton.mp inside
    rw [same]
    exact member
  · intro member
    exact ⟨[o], ⟨o, member, rfl⟩, List.mem_singleton_self o⟩

/-- **A client context of the client layer as a record**: each escaped identity is a held
reference. Its sets carry no order, so the record lists them in some order; its automorphisms do not
depend on that order (`ofClient_rename_eq_iff`). -/
noncomputable def ofClient (c : Client O) : Record O := references c.escaped.toList

theorem support_ofClient (c : Client O) : support (ofClient c) = c.escaped := by
  rw [ofClient, support_references, Finset.toList_toFinset]

/-- **The pointwise case**: the automorphisms of a client context, as a record, are the renamings
that fix every escaped identity. -/
theorem ofClient_rename_eq_iff {π : O ≃ O} (c : Client O) :
    rename π (ofClient c) = ofClient c ↔ ∀ o ∈ c.escaped, π o = o := by
  rw [ofClient, references_rename_eq_iff]
  simp only [Finset.mem_toList]

end Support

end Record

/-! ## Sightings of predicate queries -/

section Sightings

variable {T : Type uT} {S : Type uS} {O : Type uO}

open Record

/-- **The sightings of a list of predicate queries**: each sighted set, as one unary relation. -/
def querySightings (queries : List (PredicateQueryAdmission.Query T S O)) : Record O :=
  queries.map fun query => sighting query.seen

/-- **The sightings of a run**: those of its firings, in order. -/
def runSightings (w : List (Firing T S O)) : Record O :=
  w.flatMap fun f => querySightings f.queries

/-- **Renaming a query renames the relation it records.** -/
theorem querySightings_rename (π : O ≃ O) (queries : List (PredicateQueryAdmission.Query T S O)) :
    querySightings (queries.map (renameQuery π)) = rename π (querySightings queries) := by
  simp only [querySightings, rename, List.map_map]
  exact List.map_congr_left fun query _ => (renameEntry_sighting π query.seen).symm

theorem runSightings_cons (f : Firing T S O) (w : List (Firing T S O)) :
    runSightings (f :: w) = querySightings f.queries ++ runSightings w :=
  List.flatMap_cons

variable [DecidableEq O]

theorem support_querySightings :
    ∀ queries : List (PredicateQueryAdmission.Query T S O), support (querySightings queries) = sighted queries
  | [] => rfl
  | query :: rest => by
      show (sighting query.seen).biUnion List.toFinset ∪ support (querySightings rest) =
        query.seen ∪ sighted rest
      rw [support_sighting, support_querySightings rest]

/-- **Flattened, a run's sightings are the client layer's.** -/
theorem support_runSightings : ∀ w : List (Firing T S O), support (runSightings w) = runSighted w
  | [] => rfl
  | f :: rest => by
      rw [runSightings_cons, support_append, support_querySightings, support_runSightings rest]
      rfl

end Sightings

/-! ## Controls -/

namespace RecordControls

open Record

/-- The record that sighted `{5, 6}`. -/
def sawTwins : Record ℕ := [sighting {5, 6}]

/-- **The exchange of the two sighted identities is an automorphism**, and it fixes neither. -/
theorem sighting_swap :
    Equiv.swap 5 6 ∈ automorphisms sawTwins ∧ Equiv.swap 5 6 5 ≠ 5 ∧ Equiv.swap 5 6 6 ≠ 6 := by
  refine ⟨?_, by decide, by decide⟩
  show rename (Equiv.swap 5 6) sawTwins = sawTwins
  decide

/-- **Holding `5` as well blocks it.** -/
theorem reference_blocks : Equiv.swap 5 6 ∉ automorphisms (sawTwins ++ [reference 5]) := by
  show ¬ rename (Equiv.swap 5 6) (sawTwins ++ [reference 5]) = sawTwins ++ [reference 5]
  decide

/-- **Sighting the ordered pair `(5, 6)` blocks it.** -/
theorem pair_blocks : Equiv.swap 5 6 ∉ automorphisms [tuple [5, 6]] := by
  show ¬ rename (Equiv.swap 5 6) [tuple [5, 6]] = [tuple [5, 6]]
  decide

/-- **Sighting `{5}` alone blocks it.** -/
theorem singleton_blocks : Equiv.swap 5 6 ∉ automorphisms [sighting {5}] := by
  show ¬ rename (Equiv.swap 5 6) [sighting {5}] = [sighting {5}]
  decide

/-- **A renaming that carries the sighted set onto another set is refused.** -/
theorem onto_other_refused :
    rename (Equiv.swap 6 7) sawTwins = [sighting {5, 7}] ∧ Equiv.swap 6 7 ∉ automorphisms sawTwins := by
  refine ⟨by decide, ?_⟩
  show ¬ rename (Equiv.swap 6 7) sawTwins = sawTwins
  decide

/-- The cyclic relation on `5, 6, 7`. -/
def cycle : Record ℕ := [{[5, 6], [6, 7], [7, 5]}]

/-- The rotation `5 ↦ 6 ↦ 7 ↦ 5`. -/
def rotation : ℕ ≃ ℕ := (Equiv.swap 5 7).trans (Equiv.swap 6 7)

/-- **The rotation is an automorphism of the cyclic relation.** -/
theorem cycle_rotation : rotation ∈ automorphisms cycle ∧ rotation 5 = 6 := by
  refine ⟨?_, by decide⟩
  show rename rotation cycle = cycle
  decide

/-- **The exchange of `5` and `6` is not**, although it carries the identities the relation mentions
to themselves, as a set. -/
theorem cycle_not_swap :
    Equiv.swap 5 6 ∉ automorphisms cycle ∧ (support cycle).map (Equiv.swap 5 6).toEmbedding = support cycle := by
  refine ⟨?_, by decide⟩
  show ¬ rename (Equiv.swap 5 6) cycle = cycle
  decide

end RecordControls

#print axioms Record.rename_trans
#print axioms Record.automorphisms
#print axioms Record.rename_append_eq_iff
#print axioms Record.rename_prefix
#print axioms Record.references_rename_eq_iff
#print axioms Record.rename_eq_self_of_fixes
#print axioms Record.support_ofClient
#print axioms Record.ofClient_rename_eq_iff
#print axioms querySightings_rename
#print axioms support_runSightings
#print axioms RecordControls.sighting_swap
#print axioms RecordControls.reference_blocks
#print axioms RecordControls.pair_blocks
#print axioms RecordControls.singleton_blocks
#print axioms RecordControls.onto_other_refused
#print axioms RecordControls.cycle_rotation
#print axioms RecordControls.cycle_not_swap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
