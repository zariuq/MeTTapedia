import Mettapedia.InformationTheory.SymmetryKeys.Graphs

/-!
# Colour-refinement keys are sound, and not complete

Colour refinement (1-dimensional Weisfeiler–Leman) gives every vertex a colour, round by round:
the colour after round `k + 1` is the colour after round `k` together with the multiset of the
neighbours' colours after round `k` (`colour`).  The key of a graph after `k` rounds is the
multiset of all its vertices' colours (`key`).

* `colour_iso`, `key_iso`: an isomorphism keeps every colour, so isomorphic graphs have equal keys
  after every round.
* **Soundness** (`not_iso_of_key_ne`, `not_orbit_of_key_ne`): different keys after any round mean
  the graphs are not isomorphic, so their terms (`Graphs.encG`) are in different orbits.
* **Not complete** (`RefinementControls`): the six-cycle and two disjoint triangles are both
  2-regular, so every vertex of either has the same colour after every round, and the keys agree
  after every round (`key_cycle_eq_key_triangles`).  Yet the graphs are not isomorphic, so their
  terms are in two orbits (`collision_two_orbits`).  A collision of refinement keys must therefore
  be confirmed by an exact test.
* A positive control: a path and a triangle on three vertices differ after one round
  (`path_triangle_apart`).
-/

namespace Mettapedia.InformationTheory.SymmetryKeys

open Mettapedia.InformationTheory.RelationStoreVariantKeys

namespace Refinement

/-- The colours after `k` rounds. -/
def Col : ℕ → Type
  | 0 => Unit
  | k + 1 => Col k × Multiset (Col k)

variable {V : Type*} [Fintype V]

/-- The colour of a vertex after `k` rounds of refinement. -/
def colour (G : SimpleGraph V) [DecidableRel G.Adj] : (k : ℕ) → V → Col k
  | 0, _ => ()
  | k + 1, v =>
      ((colour G k v, (G.neighborFinset v).val.map (colour G k)) : Col k × Multiset (Col k))

/-- The refinement key after `k` rounds: the multiset of all vertices' colours. -/
def key (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Multiset (Col k) :=
  (Finset.univ : Finset V).val.map (colour G k)

theorem colour_succ (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (v : V) :
    colour G (k + 1) v =
      ((colour G k v, (G.neighborFinset v).val.map (colour G k)) : Col k × Multiset (Col k)) :=
  rfl

theorem neighborFinset_iso {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (φ : G ≃g H) (v : V) :
    H.neighborFinset (φ v) = (G.neighborFinset v).map φ.toEquiv.toEmbedding := by
  ext x
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_map_equiv, SimpleGraph.mem_neighborFinset]
  have hx : x = φ (φ.toEquiv.symm x) := (φ.toEquiv.apply_symm_apply x).symm
  conv_lhs => rw [hx]
  exact φ.map_adj_iff

/-- **An isomorphism keeps every colour.** -/
theorem colour_iso {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] (φ : G ≃g H) :
    ∀ (k : ℕ) (v : V), colour H k (φ v) = colour G k v
  | 0, _ => rfl
  | k + 1, v => by
      rw [colour_succ, colour_succ, colour_iso φ k v, neighborFinset_iso φ v, Finset.map_val,
        Multiset.map_map]
      congr 2
      funext x
      exact colour_iso φ k x

/-- **Isomorphic graphs have equal keys after every round.** -/
theorem key_iso {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] (φ : G ≃g H)
    (k : ℕ) : key G k = key H k := by
  unfold key
  calc (Finset.univ : Finset V).val.map (colour G k)
      = (Finset.univ : Finset V).val.map (colour H k ∘ φ) := by
        congr 1
        funext v
        exact (colour_iso φ k v).symm
    _ = ((Finset.univ : Finset V).map φ.toEquiv.toEmbedding).val.map (colour H k) := by
        rw [Finset.map_val, Multiset.map_map]
        rfl
    _ = (Finset.univ : Finset V).val.map (colour H k) := by rw [Finset.map_univ_equiv]

/-- **Refinement keys are sound**: different keys after some round, no isomorphism. -/
theorem not_iso_of_key_ne {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (k : ℕ) (h : key G k ≠ key H k) : ¬ Nonempty (G ≃g H) :=
  fun ⟨φ⟩ => h (key_iso φ k)

/-- **Different refinement keys, different orbits**, for the terms of graphs. -/
theorem not_orbit_of_key_ne [DecidableEq V] {A : Type*} (comm : A → Prop)
    [DecidablePred comm] (E P : A)
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] {es fs : List (V × V)}
    (hes : ETm.Lists G es) (hfs : ETm.Lists H fs) (k : ℕ) (h : key G k ≠ key H k) :
    ETm.encG E P fs ∉ MulAction.orbit (ETm.Sym comm V) (ETm.encG E P es) :=
  fun ho => not_iso_of_key_ne k h (ETm.iso_of_orbit comm E P hes hfs ho)

/-! ### Regular graphs: refinement sees only the degree -/

/-- The colour of every vertex of a 2-regular graph after `k` rounds. -/
def regColour : (k : ℕ) → Col k
  | 0 => ()
  | k + 1 => ((regColour k, Multiset.replicate 2 (regColour k)) : Col k × Multiset (Col k))

theorem colour_regular {G : SimpleGraph V} [DecidableRel G.Adj]
    (hreg : ∀ v, (G.neighborFinset v).card = 2) :
      ∀ (k : ℕ) (v : V), colour G k v = regColour k
  | 0, _ => rfl
  | k + 1, v => by
      rw [colour_succ, colour_regular hreg k v]
      have hc : colour G k = fun _ => regColour k := funext (colour_regular hreg k)
      rw [hc, Multiset.map_const', Finset.card_val, hreg v]
      rfl

theorem key_regular {G : SimpleGraph V} [DecidableRel G.Adj]
    (hreg : ∀ v, (G.neighborFinset v).card = 2) (k : ℕ) :
    key G k = Multiset.replicate (Fintype.card V) (regColour k) := by
  unfold key
  have hc : colour G k = fun _ => regColour k := funext (colour_regular hreg k)
  rw [hc, Multiset.map_const', Finset.card_val, Finset.card_univ]

/-- After one round the key records the degrees. -/
theorem degrees_of_key (G : SimpleGraph V) [DecidableRel G.Adj] :
    (key G 1).map (fun c : Col 1 => Multiset.card (c : Col 0 × Multiset (Col 0)).2) =
      (Finset.univ : Finset V).val.map fun v => (G.neighborFinset v).card := by
  unfold key
  rw [Multiset.map_map]
  congr 1
  funext v
  simp [colour_succ, Finset.card_val]

end Refinement

/-! ### Controls -/

namespace RefinementControls

open ETm Refinement GraphControls

theorem cycle_regular : ∀ v, (cycle6.neighborFinset v).card = 2 := by decide

theorem triangles_regular : ∀ v, (twoTriangles.neighborFinset v).card = 2 := by decide

/-- **Refinement cannot tell the six-cycle from two triangles, at any round.** -/
theorem key_cycle_eq_key_triangles (k : ℕ) : key cycle6 k = key twoTriangles k := by
  rw [key_regular cycle_regular, key_regular triangles_regular]

/-- **The collision is not an orbit**: equal refinement keys, two orbits. -/
theorem collision_two_orbits :
    (∀ k, key cycle6 k = key twoTriangles k) ∧
      encG 0 1 triangleEdges ∉ MulAction.orbit (Sym GraphControls.declared (Fin 6))
        (encG 0 1 cycleEdges) :=
  ⟨key_cycle_eq_key_triangles, hard_pair_two_orbits⟩

/-- The path `0 - 1 - 2`. -/
def path3 : SimpleGraph (Fin 3) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel path3.Adj := fun i j =>
  inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))

/-- The triangle on three vertices. -/
def triangle3 : SimpleGraph (Fin 3) where
  Adj i j := i ≠ j
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel triangle3.Adj := fun i j => inferInstanceAs (Decidable (i ≠ j))

/-- **A positive control**: the path and the triangle differ after one round. -/
theorem path_triangle_apart : key path3 1 ≠ key triangle3 1 := by
  intro h
  have := congrArg (Multiset.map fun c : Col 1 => Multiset.card (c : Col 0 × Multiset (Col 0)).2) h
  rw [degrees_of_key, degrees_of_key] at this
  revert this
  decide

end RefinementControls

end Mettapedia.InformationTheory.SymmetryKeys
