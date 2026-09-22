import Mettapedia.GSLT.LanguageDef.MatchDecisionContract

/-!
# Code trees: the match-decision filter, compiled

`MatchDecisionContract.candidates` keeps, in source order with multiplicity, every
stored equation whose pattern the sampled positions cannot refute against the
observation. It is a filter over the whole source list: one refutation test per
candidate per sampled position.

A code tree shares those tests. It branches on one sampled position per level. At a
node for position `p`, every candidate whose pattern requires tag `v` at `p` lives
under `tagged v`, and every candidate whose pattern leaves `p` unconstrained lives
under `free`. Traversing with an observation that knows `p` visits exactly two
subtrees, `tagged (o p)` and `free`; one that does not know `p` visits all of them.
Leaves hold occurrence ids. Selection filters the source by id membership, so source
order and multiplicity are definitional, as in the contract.

Laws proved here:
* `mem_traverse_build_iff` — an occurrence id reaches a leaf of the traversal iff the
  sampled positions do not refute its pattern (`conflictsOn`), for sources whose
  occurrence ids are distinct.
* `select_build_eq_candidates` — the compiled decision is `candidates`, exactly.
* `realizes_iff_residual` — fusion with head unification: once a candidate has passed
  the tree, a total query realizes its pattern iff it agrees on the positions the tree
  did not decide. The tree's comparisons are the first part of head unification and are
  never repeated.
* `mem_traverse_insert_iff`, `mem_traverse_remove_iff` — incremental maintenance:
  adding an occurrence adds exactly its id, and only when unrefuted; removing an id
  removes exactly it. This is what a revision-qualified tree owes when equations are
  added or removed.

Scope. This is the flat layer of the contract (two-valued observations). Repeated
pattern variables and the shaped `absent` observation are the contract's `eqRefutes`
and `Shaped` layers and are not re-derived here. Nothing here claims conformance of a C
implementation; that is differential testing against `candidates`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MatchDecisionContract

namespace CodeTree

universe u

variable {V : Type u}

/-- A code tree over a fixed order of sampled positions. `tagged` is total: a tag no
candidate requires maps to an empty subtree. `tags` lists the tags that occur, so a
traversal that does not know the position can visit them. -/
inductive Tree (V : Type u) : Type u where
  | leaf (ids : List Nat) : Tree V
  | node (p : Path) (tags : List V) (tagged : V → Tree V) (free : Tree V) : Tree V

/-- Traverse with an observation: a known position selects one tag branch and the free
branch; an unknown position cannot refute anything, so every listed branch is visited. -/
def traverse : Tree V → Skeleton V → List Nat
  | .leaf ids, _ => ids
  | .node p tags tagged free, o =>
    match o p with
    | some w => traverse (tagged w) o ++ traverse free o
    | none => (tags.flatMap fun v => traverse (tagged v) o) ++ traverse free o

/-- The compiled decision: the source, in order, restricted to ids the traversal reached. -/
def select (t : Tree V) (o : Skeleton V) (source : List (Candidate V)) : List (Candidate V) :=
  source.filter fun c => decide (c.id ∈ traverse t o)

/-- Order and multiplicity: the compiled decision is a sublist of the source. -/
theorem select_sublist (t : Tree V) (o : Skeleton V) (source : List (Candidate V)) :
    (select t o source).Sublist source :=
  List.filter_sublist

/-- Occurrence ids are distinct: two source occurrences never share an id. -/
def DistinctIds (cs : List (Candidate V)) : Prop := (cs.map (·.id)).Nodup

theorem DistinctIds.filter {cs : List (Candidate V)} (h : DistinctIds cs)
    (q : Candidate V → Bool) : DistinctIds (cs.filter q) :=
  h.sublist (List.Sublist.map _ List.filter_sublist)

theorem DistinctIds.eq_of_id_eq {cs : List (Candidate V)} (h : DistinctIds cs)
    {a b : Candidate V} (ha : a ∈ cs) (hb : b ∈ cs) (hid : a.id = b.id) : a = b :=
  List.inj_on_of_nodup_map h ha hb hid

/-- A tree with nothing at any leaf. -/
def IsEmpty : Tree V → Prop
  | .leaf ids => ids = []
  | .node _ _ tagged free => (∀ v, IsEmpty (tagged v)) ∧ IsEmpty free

theorem traverse_eq_nil_of_isEmpty {t : Tree V} (h : IsEmpty t) (o : Skeleton V) :
    traverse t o = [] := by
  induction t with
  | leaf ids => exact h
  | node p tags tagged free ihTag ihFree =>
    obtain ⟨htag, hfree⟩ := h
    simp only [traverse]
    cases o p with
    | some w => simp [ihTag w (htag w), ihFree hfree]
    | none =>
      rw [ihFree hfree, List.append_nil]
      exact List.flatMap_eq_nil_iff.mpr fun v _ => ihTag v (htag v)

/-- A tree whose node positions are the sampled positions in order, and whose unlisted
tag branches are empty. -/
def Shaped : List Path → Tree V → Prop
  | [], .leaf _ => True
  | p :: ps, .node q tags tagged free =>
      p = q ∧ (∀ v, Shaped ps (tagged v)) ∧ Shaped ps free ∧ ∀ v, v ∉ tags → IsEmpty (tagged v)
  | _, _ => False

/-- Remove every leaf occurrence of an id. -/
def remove (id : Nat) : Tree V → Tree V
  | .leaf ids => .leaf (ids.filter fun x => decide (x ≠ id))
  | .node p tags tagged free => .node p tags (fun u => remove id (tagged u)) (remove id free)

theorem isEmpty_remove {t : Tree V} (id : Nat) (h : IsEmpty t) : IsEmpty (remove id t) := by
  induction t with
  | leaf ids => simp only [IsEmpty] at h; simp [remove, IsEmpty, h]
  | node p tags tagged free ihTag ihFree =>
    obtain ⟨htag, hfree⟩ := h
    exact ⟨fun v => ihTag v (htag v), ihFree hfree⟩

theorem shaped_remove {ps : List Path} {t : Tree V} (id : Nat) (h : Shaped ps t) :
    Shaped ps (remove id t) := by
  induction ps generalizing t with
  | nil =>
    cases t with
    | leaf _ => trivial
    | node _ _ _ _ => exact False.elim h
  | cons p ps ih =>
    cases t with
    | leaf _ => exact False.elim h
    | node q tags tagged free =>
      obtain ⟨rfl, htag, hfree, hidden⟩ := h
      exact ⟨rfl, fun u => ih (htag u), ih hfree, fun v hv => isEmpty_remove id (hidden v hv)⟩

/-- Removing an id removes exactly it. -/
theorem mem_traverse_remove_iff (t : Tree V) (id : Nat) (o : Skeleton V) (x : Nat) :
    x ∈ traverse (remove id t) o ↔ x ∈ traverse t o ∧ x ≠ id := by
  induction t with
  | leaf ids => simp [remove, traverse]
  | node p tags tagged free ihTag ihFree =>
    simp only [remove, traverse]
    cases o p with
    | some w =>
      simp only [List.mem_append, ihTag, ihFree]
      tauto
    | none =>
      simp only [List.mem_append, List.mem_flatMap, ihTag, ihFree]
      constructor
      · rintro (⟨v, hv, h, hne⟩ | ⟨h, hne⟩)
        · exact ⟨Or.inl ⟨v, hv, h⟩, hne⟩
        · exact ⟨Or.inr h, hne⟩
      · rintro ⟨(⟨v, hv, h⟩ | h), hne⟩
        · exact Or.inl ⟨v, hv, h, hne⟩
        · exact Or.inr ⟨h, hne⟩

section Decidable

variable [DecidableEq V]

/-- The constructor tags some candidate requires at `p`. -/
def tagsAt (p : Path) (cs : List (Candidate V)) : List V :=
  (cs.filterMap fun c => c.pat p).dedup

/-- Compile a source list against the sampled positions, in order. -/
def build : List Path → List (Candidate V) → Tree V
  | [], cs => .leaf (cs.map (·.id))
  | p :: ps, cs =>
    .node p (tagsAt p cs)
      (fun v => build ps (cs.filter fun c => decide (c.pat p = some v)))
      (build ps (cs.filter fun c => decide (c.pat p = none)))

theorem isEmpty_build_nil (ps : List Path) : IsEmpty (build ps ([] : List (Candidate V))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact ⟨fun _ => ih, ih⟩

theorem shaped_build (ps : List Path) (cs : List (Candidate V)) : Shaped ps (build ps cs) := by
  induction ps generalizing cs with
  | nil => trivial
  | cons p ps ih =>
    refine ⟨rfl, fun _ => ih _, ih _, fun v hv => ?_⟩
    have : (cs.filter fun c => decide (c.pat p = some v)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcv
      exact hv (List.mem_dedup.mpr (List.mem_filterMap.mpr ⟨c, hc, of_decide_eq_true hcv⟩))
    show IsEmpty (build ps (cs.filter fun c => decide (c.pat p = some v)))
    rw [this]
    exact isEmpty_build_nil ps

/-! ## Every id a traversal returns names a source occurrence -/

theorem mem_traverse_build {ps : List Path} {cs : List (Candidate V)} {o : Skeleton V}
    {id : Nat} (h : id ∈ traverse (build ps cs) o) : ∃ c ∈ cs, c.id = id := by
  induction ps generalizing cs with
  | nil =>
    simp only [build, traverse, List.mem_map] at h
    exact h
  | cons p ps ih =>
    simp only [build, traverse] at h
    cases hop : o p with
    | some w =>
      rw [hop] at h
      rcases List.mem_append.mp h with hl | hr
      · obtain ⟨c, hc, rfl⟩ := ih hl
        exact ⟨c, (List.mem_filter.mp hc).1, rfl⟩
      · obtain ⟨c, hc, rfl⟩ := ih hr
        exact ⟨c, (List.mem_filter.mp hc).1, rfl⟩
    | none =>
      rw [hop] at h
      rcases List.mem_append.mp h with hl | hr
      · obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hl
        obtain ⟨c, hc, rfl⟩ := ih hv
        exact ⟨c, (List.mem_filter.mp hc).1, rfl⟩
      · obtain ⟨c, hc, rfl⟩ := ih hr
        exact ⟨c, (List.mem_filter.mp hc).1, rfl⟩

/-! ## Pointwise refutation, unpacked -/

private theorem posConflict_false_of_some {o s : Skeleton V} {p : Path} {w : V}
    (ho : o p = some w) : posConflict o s p = false ↔ s p = none ∨ s p = some w := by
  unfold posConflict
  rw [ho]
  cases s p with
  | none => simp
  | some v =>
    simp
    try exact ⟨Eq.symm, Eq.symm⟩

private theorem posConflict_false_of_none {o s : Skeleton V} {p : Path}
    (ho : o p = none) : posConflict o s p = false := by
  unfold posConflict
  rw [ho]

private theorem conflictsOn_cons_false {p : Path} {ps : List Path} {o s : Skeleton V} :
    conflictsOn (p :: ps) o s = false ↔
      posConflict o s p = false ∧ conflictsOn ps o s = false := by
  simp [conflictsOn, List.any_cons]

/-! ## The traversal is the refutation filter -/

theorem mem_traverse_build_iff {ps : List Path} {cs : List (Candidate V)} {o : Skeleton V}
    (distinct : DistinctIds cs) {c : Candidate V} (hc : c ∈ cs) :
    c.id ∈ traverse (build ps cs) o ↔ conflictsOn ps o c.pat = false := by
  induction ps generalizing cs with
  | nil =>
    simp only [build, traverse, conflictsOn, List.any_nil, iff_true]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  | cons p ps ih =>
    -- membership in a subtree built from a filtered source pins the candidate's tag at `p`
    have sub_tag : ∀ {v : V},
        c.id ∈ traverse (build ps (cs.filter fun d => decide (d.pat p = some v))) o →
          c.pat p = some v := by
      intro v h
      obtain ⟨d, hd, hid⟩ := mem_traverse_build h
      have hd' := List.mem_filter.mp hd
      have := distinct.eq_of_id_eq hd'.1 hc hid
      subst this
      exact of_decide_eq_true hd'.2
    have sub_free :
        c.id ∈ traverse (build ps (cs.filter fun d => decide (d.pat p = none))) o →
          c.pat p = none := by
      intro h
      obtain ⟨d, hd, hid⟩ := mem_traverse_build h
      have hd' := List.mem_filter.mp hd
      have := distinct.eq_of_id_eq hd'.1 hc hid
      subst this
      exact of_decide_eq_true hd'.2
    have in_tag : ∀ {v : V}, c.pat p = some v →
        (c.id ∈ traverse (build ps (cs.filter fun d => decide (d.pat p = some v))) o ↔
          conflictsOn ps o c.pat = false) := by
      intro v hv
      exact ih (distinct.filter _) (List.mem_filter.mpr ⟨hc, decide_eq_true hv⟩)
    have in_free : c.pat p = none →
        (c.id ∈ traverse (build ps (cs.filter fun d => decide (d.pat p = none))) o ↔
          conflictsOn ps o c.pat = false) := by
      intro hv
      exact ih (distinct.filter _) (List.mem_filter.mpr ⟨hc, decide_eq_true hv⟩)
    rw [conflictsOn_cons_false]
    simp only [build, traverse]
    cases hop : o p with
    | some w =>
      dsimp only
      rw [posConflict_false_of_some hop, List.mem_append]
      cases hcp : c.pat p with
      | none =>
        have not_tag :
            c.id ∉ traverse (build ps (cs.filter fun d => decide (d.pat p = some w))) o := by
          intro h
          have := sub_tag h
          rw [hcp] at this
          cases this
        constructor
        · rintro (h | h)
          · exact absurd h not_tag
          · exact ⟨Or.inl rfl, (in_free hcp).mp h⟩
        · rintro ⟨_, h⟩
          exact Or.inr ((in_free hcp).mpr h)
      | some v =>
        by_cases hvw : v = w
        · subst hvw
          have not_free :
              c.id ∉ traverse (build ps (cs.filter fun d => decide (d.pat p = none))) o := by
            intro h
            have := sub_free h
            rw [hcp] at this
            cases this
          constructor
          · rintro (h | h)
            · exact ⟨Or.inr rfl, (in_tag hcp).mp h⟩
            · exact absurd h not_free
          · rintro ⟨_, h⟩
            exact Or.inl ((in_tag hcp).mpr h)
        · have not_tag :
              c.id ∉ traverse (build ps (cs.filter fun d => decide (d.pat p = some w))) o := by
            intro h
            have := sub_tag h
            rw [hcp] at this
            exact hvw (Option.some.inj this)
          have not_free :
              c.id ∉ traverse (build ps (cs.filter fun d => decide (d.pat p = none))) o := by
            intro h
            have := sub_free h
            rw [hcp] at this
            cases this
          constructor
          · rintro (h | h)
            · exact absurd h not_tag
            · exact absurd h not_free
          · rintro ⟨hor, _⟩
            rcases hor with h | h
            · cases h
            · exact absurd (Option.some.inj h) hvw
    | none =>
      dsimp only
      simp only [posConflict_false_of_none hop, true_and, List.mem_append, List.mem_flatMap]
      cases hcp : c.pat p with
      | none =>
        have not_tag : ∀ v,
            c.id ∉ traverse (build ps (cs.filter fun d => decide (d.pat p = some v))) o := by
          intro v h
          have := sub_tag h
          rw [hcp] at this
          cases this
        constructor
        · rintro (⟨v, _, h⟩ | h)
          · exact absurd h (not_tag v)
          · exact (in_free hcp).mp h
        · intro h
          exact Or.inr ((in_free hcp).mpr h)
      | some v =>
        have not_free :
            c.id ∉ traverse (build ps (cs.filter fun d => decide (d.pat p = none))) o := by
          intro h
          have := sub_free h
          rw [hcp] at this
          cases this
        have v_tag : v ∈ tagsAt p cs :=
          List.mem_dedup.mpr (List.mem_filterMap.mpr ⟨c, hc, hcp⟩)
        constructor
        · rintro (⟨u, _, h⟩ | h)
          · have hu := sub_tag h
            rw [hcp] at hu
            cases Option.some.inj hu
            exact (in_tag hcp).mp h
          · exact absurd h not_free
        · intro h
          exact Or.inl ⟨v, v_tag, (in_tag hcp).mpr h⟩

/-- **The compiled decision is the contract's decision.** -/
theorem select_build_eq_candidates {ps : List Path} {o : Skeleton V}
    {source : List (Candidate V)} (distinct : DistinctIds source) :
    select (build ps source) o source = candidates ps o source := by
  unfold select candidates
  apply List.filter_congr
  intro c hc
  have h := mem_traverse_build_iff (ps := ps) (o := o) distinct hc
  cases hcf : conflictsOn ps o c.pat with
  | false => simp [h.mpr hcf]
  | true =>
    have : c.id ∉ traverse (build ps source) o := by
      intro m
      have := h.mp m
      rw [hcf] at this
      cases this
    simp [this]

/-! ## Fusion with head unification -/

/-- A position the tree has already decided: sampled, and known in the observation. -/
def Decided (ps : List Path) (o : Skeleton V) (p : Path) : Prop := p ∈ ps ∧ (o p).isSome

/-- **Fusion law.** For a total query `t` that realizes the observation, and a candidate
the tree did not refute, realizing the candidate's pattern is exactly agreement on the
positions the tree did not decide. Head unification after selection resumes on those
residual positions; the sampled comparisons are never repeated. -/
theorem realizes_iff_residual {ps : List Path} {o pat : Skeleton V} {t : Path → V}
    (hto : Realizes t o) (hnc : conflictsOn ps o pat = false) :
    Realizes t pat ↔ ∀ p v, pat p = some v → ¬ Decided ps o p → t p = v := by
  constructor
  · intro h p v hp _
    exact h p v hp
  · intro h p v hp
    by_cases hd : Decided ps o p
    · obtain ⟨hps, hsome⟩ := hd
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
      have hpc : posConflict o pat p = false :=
        Bool.eq_false_iff.mpr (List.any_eq_false.mp hnc p hps)
      have hvw : v = w := by
        rcases (posConflict_false_of_some hw).mp hpc with hn | hs
        · rw [hn] at hp
          cases hp
        · exact Option.some.inj (hp.symm.trans hs)
      rw [hvw]
      exact hto p w hw
    · exact h p v hp hd

/-! ## Incremental maintenance -/

/-- Add an occurrence along the tree's own positions. -/
def insert (c : Candidate V) : Tree V → Tree V
  | .leaf ids => .leaf (ids ++ [c.id])
  | .node p tags tagged free =>
    match c.pat p with
    | some v =>
      .node p (if v ∈ tags then tags else v :: tags)
        (fun u => if u = v then insert c (tagged u) else tagged u) free
    | none => .node p tags tagged (insert c free)

private theorem mem_tags_insert {tags : List V} {v u : V} :
    u ∈ (if v ∈ tags then tags else v :: tags) ↔ u ∈ tags ∨ u = v := by
  by_cases hv : v ∈ tags
  · rw [if_pos hv]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact hv
  · rw [if_neg hv, List.mem_cons]
    exact or_comm

theorem shaped_insert {ps : List Path} {t : Tree V} (c : Candidate V) (h : Shaped ps t) :
    Shaped ps (insert c t) := by
  induction ps generalizing t with
  | nil =>
    cases t with
    | leaf _ => trivial
    | node _ _ _ _ => exact False.elim h
  | cons p ps ih =>
    cases t with
    | leaf _ => exact False.elim h
    | node q tags tagged free =>
      obtain ⟨rfl, htag, hfree, hidden⟩ := h
      simp only [insert]
      cases hcp : c.pat p with
      | some v =>
        dsimp only
        refine ⟨rfl, fun u => ?_, hfree, fun u hu => ?_⟩
        · show Shaped ps (if u = v then insert c (tagged u) else tagged u)
          by_cases huv : u = v
          · rw [if_pos huv]
            exact ih (htag u)
          · rw [if_neg huv]
            exact htag u
        · show IsEmpty (if u = v then insert c (tagged u) else tagged u)
          rw [mem_tags_insert] at hu
          have huv : u ≠ v := fun e => hu (Or.inr e)
          have hut : u ∉ tags := fun m => hu (Or.inl m)
          rw [if_neg huv]
          exact hidden u hut
      | none =>
        dsimp only
        exact ⟨rfl, htag, ih hfree, hidden⟩

/-- Under a node, the inserted occurrence lands in the branch of its own tag and
nowhere else. -/
private theorem mem_traverse_tagged_insert {ps : List Path} {tagged : V → Tree V}
    {c : Candidate V} {o : Skeleton V} {x : Nat}
    (hshaped : ∀ u, Shaped ps (tagged u))
    (ih : ∀ {t : Tree V}, Shaped ps t →
      (x ∈ traverse (insert c t) o ↔
        x ∈ traverse t o ∨ (x = c.id ∧ conflictsOn ps o c.pat = false)))
    (v u : V) :
    x ∈ traverse (if u = v then insert c (tagged u) else tagged u) o ↔
      x ∈ traverse (tagged u) o ∨ (u = v ∧ x = c.id ∧ conflictsOn ps o c.pat = false) := by
  by_cases huv : u = v
  · rw [if_pos huv, ih (hshaped u)]
    simp [huv]
  · rw [if_neg huv]
    simp [huv]

/-- Inserting an occurrence adds exactly its id, and only when the sampled positions
cannot refute it. -/
theorem mem_traverse_insert_iff {ps : List Path} {t : Tree V} (h : Shaped ps t)
    (c : Candidate V) (o : Skeleton V) (x : Nat) :
    x ∈ traverse (insert c t) o ↔
      x ∈ traverse t o ∨ (x = c.id ∧ conflictsOn ps o c.pat = false) := by
  induction ps generalizing t with
  | nil =>
    cases t with
    | leaf ids => simp [insert, traverse, conflictsOn]
    | node _ _ _ _ => exact False.elim h
  | cons p ps ih =>
    cases t with
    | leaf _ => exact False.elim h
    | node q tags tagged free =>
      obtain ⟨rfl, htag, hfree, hidden⟩ := h
      rw [conflictsOn_cons_false]
      simp only [insert]
      cases hcp : c.pat p with
      | some v =>
        dsimp only
        simp only [traverse]
        cases hop : o p with
        | some w =>
          dsimp only
          rw [posConflict_false_of_some hop, hcp, List.mem_append, List.mem_append,
            mem_traverse_tagged_insert htag ih v w]
          by_cases hvw : v = w
          · subst hvw
            simp
            try tauto
          · have hne : w ≠ v := fun e => hvw e.symm
            simp [hne, hvw]
        | none =>
          dsimp only
          simp only [posConflict_false_of_none hop, true_and, List.mem_append, List.mem_flatMap,
            mem_traverse_tagged_insert htag ih v, mem_tags_insert]
          have hidden_v : v ∉ tags → x ∉ traverse (tagged v) o := by
            intro hv hx
            rw [traverse_eq_nil_of_isEmpty (hidden v hv) o] at hx
            exact List.not_mem_nil hx
          constructor
          · rintro (⟨u, hu, hx | ⟨rfl, hx⟩⟩ | hx)
            · rcases hu with hu | rfl
              · exact Or.inl (Or.inl ⟨u, hu, hx⟩)
              · by_cases hv : u ∈ tags
                · exact Or.inl (Or.inl ⟨u, hv, hx⟩)
                · exact absurd hx (hidden_v hv)
            · exact Or.inr hx
            · exact Or.inl (Or.inr hx)
          · rintro ((⟨u, hu, hx⟩ | hx) | ⟨rfl, hc⟩)
            · exact Or.inl ⟨u, Or.inl hu, Or.inl hx⟩
            · exact Or.inr hx
            · exact Or.inl ⟨v, Or.inr rfl, Or.inr ⟨rfl, rfl, hc⟩⟩
      | none =>
        dsimp only
        simp only [traverse]
        cases hop : o p with
        | some w =>
          dsimp only
          rw [posConflict_false_of_some hop, hcp, List.mem_append, List.mem_append, ih hfree]
          simp
          try tauto
        | none =>
          dsimp only
          simp only [posConflict_false_of_none hop, true_and, List.mem_append, ih hfree]
          tauto

/-! ## Canaries -/

section Canary

private def cA : Candidate Nat := ⟨0, fun p => if p = [0] then some 1 else none⟩
private def cB : Candidate Nat := ⟨1, fun p => if p = [0] then some 2 else none⟩
private def cC : Candidate Nat := ⟨2, fun _ => none⟩
private def cD : Candidate Nat :=
  ⟨3, fun p => if p = [0] then some 1 else if p = [1] then some 7 else none⟩

private def src : List (Candidate Nat) := [cA, cB, cC, cD]
private def ps : List Path := [[0], [1]]

/-- Query with tag 1 at `[0]` and tag 7 at `[1]`. -/
private def oFull : Skeleton Nat :=
  fun p => if p = [0] then some 1 else if p = [1] then some 7 else none
/-- Query that knows `[0]` only. -/
private def oHead : Skeleton Nat := fun p => if p = [0] then some 1 else none
/-- Query that knows nothing. -/
private def oNone : Skeleton Nat := fun _ => none
/-- Query with tag 2 at `[0]`. -/
private def oOther : Skeleton Nat := fun p => if p = [0] then some 2 else none

private theorem src_distinct : DistinctIds src := by
  unfold DistinctIds
  decide

theorem canary_full_selects_by_id :
    (select (build ps src) oFull src).map (·.id) = [0, 2, 3] := by decide

theorem canary_full_agrees_with_contract :
    select (build ps src) oFull src = candidates ps oFull src :=
  select_build_eq_candidates src_distinct

theorem canary_head_only_keeps_unsampled_second_position :
    (select (build ps src) oHead src).map (·.id) = [0, 2, 3] := by decide

theorem canary_unknown_query_is_the_enumeration :
    (select (build ps src) oNone src).map (·.id) = [0, 1, 2, 3] := by decide

/-- Tag 2 at `[0]` refutes `cA` and `cD` and keeps `cB`, `cC`. -/
theorem canary_other_tag :
    (select (build ps src) oOther src).map (·.id) = [1, 2] := by decide

/-- Remove `cB`, then insert it again: the traversal lists the same ids. -/
theorem canary_remove_then_insert :
    ∀ x, x ∈ traverse (insert cB (remove 1 (build ps src))) oNone ↔
      x ∈ traverse (build ps src) oNone := by
  intro x
  rw [mem_traverse_insert_iff (shaped_remove 1 (shaped_build ps src)),
    mem_traverse_remove_iff]
  have hb : x ∈ traverse (build ps src) oNone ↔ x ∈ [1, 3, 0, 2] := by
    rw [show traverse (build ps src) oNone = [1, 3, 0, 2] from by decide]
  rw [hb]
  have : conflictsOn ps oNone cB.pat = false := by decide
  simp only [this, and_true]
  constructor
  · rintro (⟨h, _⟩ | rfl)
    · exact h
    · decide
  · intro h
    by_cases h1 : x = 1
    · exact Or.inr h1
    · exact Or.inl ⟨h, h1⟩

end Canary

end Decidable

end CodeTree

end Mettapedia.GSLT.LanguageDef.MatchDecisionContract
