import Mettapedia.InformationTheory.SymmetryKeys.TreeCanon

/-!
# The hard class: a set of two-element sets of variables is a graph

A graph on the variables is written as the term `(E (P $u $v) …)`, one `(P $u $v)` for each edge
(`encG`), with both heads declared unordered.  Example: the path `a - b - c` is
`(E (P $a $b) (P $b $c))`.

* `iso_iff_orbit`: two graphs, each listed edge by edge (`Lists`), are isomorphic **iff** their
  terms are in one orbit of renamings and argument permutations.  So deciding whether two terms of
  this shape are in one orbit decides graph isomorphism, and a key that is equal exactly on orbits
  is a canonical form for graphs (`orbitKeys_eq_iff_iso`).  This is a reduction in both directions;
  it states no complexity bound.
* The arguments of `E` share variables, so these terms are outside the easy class of `TreeCanon`
  whenever two edges meet.
* Controls (`GraphControls`): the six-cycle and two disjoint triangles, both 2-regular on six
  vertices, are not isomorphic (one has a triangle), so their terms are in two orbits; a relabeled
  six-cycle is in the orbit of the six-cycle.
-/

namespace Mettapedia.InformationTheory.SymmetryKeys

open Mettapedia.InformationTheory.RelationStoreVariantKeys

namespace ETm

variable {A V : Type*} (comm : A → Prop) [DecidablePred comm] (E P : A)

/-- `(P $u $v)`. -/
def pairTm (p : V × V) : ETm A V := .node P [.var p.1, .var p.2]

/-- `(E (P $u $v) …)`: one argument per listed edge. -/
def encG (es : List (V × V)) : ETm A V := .node E (es.map (pairTm P))

/-- The unordered edge of an ordered pair. -/
def sym (p : V × V) : Sym2 V := s(p.1, p.2)

/-- `es` lists the edges of `G`, each exactly once, in either orientation. -/
structure Lists (G : SimpleGraph V) (es : List (V × V)) : Prop where
  adj : ∀ p ∈ es, G.Adj p.1 p.2
  cover : ∀ u v, G.Adj u v → s(u, v) ∈ es.map sym
  nodup : (es.map sym).Nodup

theorem Lists.mem_iff {G : SimpleGraph V} {es : List (V × V)} (h : Lists G es) (u v : V) :
    s(u, v) ∈ es.map sym ↔ G.Adj u v := by
  constructor
  · intro hm
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
    have hadj := h.adj p hp
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  · exact h.cover u v

theorem perm_lift_map {α β : Type*} {f : α → β} {l l' : List α}
    (h : (l.map f).Perm (l'.map f)) :
      ∃ n, List.Forall₂ (fun a b => f a = f b) l n ∧ n.Perm l' := by
  have hv : List.Forall₂ (fun b a => b = f a) (l'.map f) l' := by
    rw [List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun _ _ => rfl
  obtain ⟨n, hn, hp⟩ := List.perm_comp_forall₂ h hv
  exact ⟨n, List.forall₂_map_left_iff.mp hn, hp⟩

omit [DecidablePred comm] in
theorem arr_pairTm (hP : comm P) {p q : V × V} (h : sym p = sym q) :
    Arr comm (pairTm P p) (pairTm P q) := by
  rcases Sym2.mk_eq_mk_iff.mp h with h' | h'
  · rw [h']
    exact arr_refl comm _
  · rw [h', pairTm, pairTm, arr_node]
    exact ⟨[.var q.2, .var q.1], [.var q.1, .var q.2], rfl, arr_refl_args comm _,
      fun _ => .swap _ _ _, fun h'' => absurd hP h''⟩

omit [DecidablePred comm] in
/-- Two listings of one graph give arrangements of one term. -/
theorem arr_encG_of_lists (hE : comm E) (hP : comm P) {G : SimpleGraph V} {es fs : List (V × V)}
    (hes : Lists G es) (hfs : Lists G fs) : Arr comm (encG E P es) (encG E P fs) := by
  have hperm : (es.map sym).Perm (fs.map sym) := by
    rw [List.perm_ext_iff_of_nodup hes.nodup hfs.nodup]
    intro e
    induction e using Sym2.ind with
    | h u v => rw [hes.mem_iff, hfs.mem_iff]
  obtain ⟨n, hn, hnp⟩ := perm_lift_map hperm
  rw [encG, encG, arr_node]
  refine ⟨n.map (pairTm P), fs.map (pairTm P), rfl, ?_,
    fun _ => hnp.map _, fun h' => absurd hE h'⟩
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hn.imp fun {_ _} h => arr_pairTm comm P hP h

theorem rename_encG (σ : V → V) (es : List (V × V)) :
    (encG E P es).rename σ = encG E P (es.map (Prod.map σ σ)) := by
  simp [encG, pairTm, rename_node, List.map_map, Function.comp_def]

theorem lists_map_iso [DecidableEq V] {G H : SimpleGraph V} (φ : G ≃g H) {es : List (V × V)}
    (hes : Lists G es) : Lists H (es.map (Prod.map φ φ)) where
  adj := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact φ.map_adj_iff.mpr (hes.adj q hq)
  cover := by
    intro u v huv
    have hg : G.Adj (φ.symm u) (φ.symm v) := by
      rw [← φ.map_adj_iff]
      simpa using huv
    obtain ⟨q, hq, he⟩ := List.mem_map.mp (hes.cover _ _ hg)
    refine List.mem_map.mpr ⟨Prod.map φ φ q, List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    have := congrArg (Sym2.map φ) he
    simpa [sym, Sym2.map_mk] using this
  nodup := by
    have hmap : (es.map (Prod.map φ φ)).map sym = (es.map sym).map (Sym2.map φ) := by
      simp [sym, Function.comp_def, Sym2.map_mk]
    rw [hmap]
    exact hes.nodup.map (Sym2.map.injective φ.injective)

/-- **Isomorphic graphs give terms in one orbit.** -/
theorem orbit_of_iso [DecidableEq V] (hE : comm E) (hP : comm P) {G H : SimpleGraph V}
    {es fs : List (V × V)} (hes : Lists G es) (hfs : Lists H fs) (φ : G ≃g H) :
    encG E P fs ∈ MulAction.orbit (Sym comm V) (encG E P es) := by
  set σ : Equiv.Perm V := φ.toEquiv
  have h1 : encG E P (es.map (Prod.map φ φ)) ∈ MulAction.orbit (Sym comm V) (encG E P es) := by
    refine MulAction.mem_orbit_iff.mpr ⟨(σ, 1), ?_⟩
    rw [sym_smul_def, one_smul, perm_smul_def]
    exact rename_encG E P σ es
  have h2 : encG E P fs ∈ MulAction.orbit (Sym comm V) (encG E P (es.map (Prod.map φ φ))) :=
    (mem_orbit_sym_iff comm).mpr ⟨_, arr_encG_of_lists comm E P hE hP
      (lists_map_iso φ hes) hfs, variant_refl _⟩
  rw [MulAction.orbit_eq_iff.mpr h1] at h2
  exact h2

/-- The two-element multiset of a pair. -/
def pairMs (p : V × V) : Multiset V := ↑[p.1, p.2]

theorem pairMs_eq_iff {p q : V × V} : pairMs p = pairMs q ↔ sym p = sym q := by
  rw [pairMs, pairMs, Multiset.coe_eq_coe, List.perm_pair, sym, sym, Sym2.eq_iff]
  simp only [List.cons.injEq, and_true]

/-- **Terms in one orbit come from isomorphic graphs.** -/
theorem iso_of_orbit [DecidableEq V] {G H : SimpleGraph V} {es fs : List (V × V)}
    (hes : Lists G es) (hfs : Lists H fs)
    (h : encG E P fs ∈ MulAction.orbit (Sym comm V) (encG E P es)) : Nonempty (G ≃g H) := by
  obtain ⟨u, hu, hv⟩ := (mem_orbit_sym_iff comm).mp h
  obtain ⟨σ, hσ⟩ := variant_iff_exists_perm.mp hv
  rw [encG, arr_node] at hu
  obtain ⟨m, l', rfl, hf, hp, he⟩ := hu
  -- the multiset of variables of each argument survives arrangement
  have hms : (es.map pairMs) = m.map (fun c => (c.vars : Multiset V)) := by
    have hf' := vars_perm_of_arr_args comm _ _ hf
    rw [List.forall₂_map_left_iff] at hf'
    have := map_eq_of_forall₂ (g := pairMs) (g' := fun c => (c.vars : Multiset V))
      (hf'.imp fun {p c} hpc => by
        simp only [pairMs]
        exact Multiset.coe_eq_coe.mpr (by simpa [pairTm] using hpc))
    exact this
  have hml : (m.map (fun c => (c.vars : Multiset V))).Perm
      (l'.map fun c => (c.vars : Multiset V)) := by
    by_cases hE : comm E
    · exact (hp hE).map _
    · rw [he hE]
  have hren : l'.map (rename σ) = fs.map (pairTm P) := by
    simp only [rename_node, encG] at hσ
    exact (ETm.node.inj hσ).2
  have hfsms : (l'.map fun c => (c.vars : Multiset V)).map (Multiset.map σ) = fs.map pairMs := by
    have := congrArg (List.map fun c => (c.vars : Multiset V)) hren
    simp only [List.map_map] at this
    rw [List.map_map]
    convert this using 1
    · apply List.map_congr_left
      intro c _
      simp [vars_rename]
    · apply List.map_congr_left
      intro p _
      simp [pairMs, pairTm]
  have hall : ((es.map pairMs).map (Multiset.map σ)).Perm (fs.map pairMs) := by
    rw [hms]
    rw [← hfsms]
    exact hml.map _
  have hadj : ∀ x y, H.Adj (σ x) (σ y) ↔ G.Adj x y := by
    intro x y
    have key : ∀ (L : List (V × V)) (a b : V),
        pairMs (a, b) ∈ L.map pairMs ↔ s(a, b) ∈ L.map sym := by
      intro L a b
      simp only [List.mem_map]
      constructor
      · rintro ⟨q, hq, hqe⟩
        exact ⟨q, hq, (pairMs_eq_iff.mp hqe)⟩
      · rintro ⟨q, hq, hqe⟩
        exact ⟨q, hq, pairMs_eq_iff.mpr hqe⟩
    rw [← hfs.mem_iff, ← hes.mem_iff, ← key, ← key, ← hall.mem_iff]
    simp only [List.mem_map]
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, hpq⟩
      refine ⟨p, hp, ?_⟩
      have hinj : Function.Injective (Multiset.map σ) := Multiset.map_injective σ.injective
      apply hinj
      rw [hpq]
      simp [pairMs]
    · rintro ⟨p, hp, hpe⟩
      exact ⟨pairMs p, ⟨p, hp, rfl⟩, by rw [hpe]; simp [pairMs]⟩
  exact ⟨{ toEquiv := σ, map_rel_iff' := fun {x y} => hadj x y }⟩

/-- **Graph isomorphism is orbit equivalence of these terms**, in both directions. -/
theorem iso_iff_orbit [DecidableEq V] (hE : comm E) (hP : comm P) {G H : SimpleGraph V}
    {es fs : List (V × V)} (hes : Lists G es) (hfs : Lists H fs) :
    Nonempty (G ≃g H) ↔ encG E P fs ∈ MulAction.orbit (Sym comm V) (encG E P es) :=
  ⟨fun ⟨φ⟩ => orbit_of_iso comm E P hE hP hes hfs φ, iso_of_orbit comm E P hes hfs⟩

/-- **A key equal exactly on orbits is a canonical form for graphs.** -/
theorem orbitKeys_eq_iff_iso [DecidableEq A] [DecidableEq V] {N : Numbering V}
    (hsep : Separates N) (hinv : RenameInvariant N) (hE : comm E) (hP : comm P)
    {G H : SimpleGraph V} {es fs : List (V × V)} (hes : Lists G es) (hfs : Lists H fs) :
    orbitKeys comm N (encG E P es) = orbitKeys comm N (encG E P fs) ↔ Nonempty (G ≃g H) :=
  (key_eq_iff_orbit comm hsep hinv).trans (iso_iff_orbit comm E P hE hP hes hfs).symm

end ETm

/-! ### Controls -/

namespace GraphControls

open ETm

/-- The six-cycle `0 - 1 - 2 - 3 - 4 - 5 - 0`. -/
def cycle6 : SimpleGraph (Fin 6) where
  Adj i j := j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel cycle6.Adj := fun i j =>
  inferInstanceAs (Decidable (j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6))

/-- Two disjoint triangles `0 1 2` and `3 4 5`. -/
def twoTriangles : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ i.val / 3 = j.val / 3
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by decide⟩

instance : DecidableRel twoTriangles.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ i.val / 3 = j.val / 3))

def cycleEdges : List (Fin 6 × Fin 6) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]

/-- The six-cycle relabeled and listed in another order and orientation. -/
def cycleEdges' : List (Fin 6 × Fin 6) := [(3, 5), (0, 2), (4, 1), (2, 4), (5, 0), (1, 3)]

def triangleEdges : List (Fin 6 × Fin 6) := [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]

/-- The six-cycle relabeled: `0 - 2 - 4 - 1 - 3 - 5 - 0`, read from its edge list. -/
def cycle6' : SimpleGraph (Fin 6) where
  Adj i j := (i, j) ∈ cycleEdges' ∨ (j, i) ∈ cycleEdges'
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel cycle6'.Adj := fun i j =>
  inferInstanceAs (Decidable ((i, j) ∈ cycleEdges' ∨ (j, i) ∈ cycleEdges'))

/-- The relabeling `i ↦ [0, 2, 4, 1, 3, 5][i]`. -/
def relabel : Equiv.Perm (Fin 6) :=
  ⟨![0, 2, 4, 1, 3, 5], ![0, 3, 1, 4, 2, 5], by decide, by decide⟩

theorem relabel_adj : ∀ a b : Fin 6, cycle6'.Adj (relabel a) (relabel b) ↔ cycle6.Adj a b := by
  decide

def relabelIso : cycle6 ≃g cycle6' := { toEquiv := relabel, map_rel_iff' := relabel_adj _ _ }

theorem cycle_lists : Lists cycle6 cycleEdges := ⟨by decide, by decide, by decide⟩

theorem cycle_lists' : Lists cycle6' cycleEdges' := ⟨by decide, by decide, by decide⟩

theorem triangle_lists : Lists twoTriangles triangleEdges := ⟨by decide, by decide, by decide⟩

/-- Both graphs are 2-regular on six vertices; only one has a triangle. -/
theorem not_iso : ¬ Nonempty (cycle6 ≃g twoTriangles) := by
  rintro ⟨φ⟩
  have hc : ∀ a b c : Fin 6, ¬ (cycle6.Adj a b ∧ cycle6.Adj b c ∧ cycle6.Adj a c) := by
    decide
  apply hc (φ.symm 0) (φ.symm 1) (φ.symm 2)
  refine ⟨?_, ?_, ?_⟩ <;> rw [← φ.map_adj_iff] <;> simp <;> decide

/-- `bag` heads: `0` is `E`, `1` is `P`. -/
def declared (h : ℕ) : Prop := h = 0 ∨ h = 1

instance : DecidablePred declared := fun h => inferInstanceAs (Decidable (h = 0 ∨ h = 1))

/-- **The hard pair**: the six-cycle and two triangles give terms in two orbits. -/
theorem hard_pair_two_orbits :
    encG 0 1 triangleEdges ∉ MulAction.orbit (Sym declared (Fin 6)) (encG 0 1 cycleEdges) :=
  fun h => not_iso ((iso_iff_orbit declared 0 1 (Or.inl rfl) (Or.inr rfl) cycle_lists
    triangle_lists).mpr h)

/-- A relabeled six-cycle, listed in another order and orientation, is in the orbit of the
six-cycle. -/
theorem relabeled_one_orbit :
    encG 0 1 cycleEdges' ∈ MulAction.orbit (Sym declared (Fin 6)) (encG 0 1 cycleEdges) :=
  orbit_of_iso declared 0 1 (Or.inl rfl) (Or.inr rfl) cycle_lists cycle_lists' relabelIso

end GraphControls

end Mettapedia.InformationTheory.SymmetryKeys
