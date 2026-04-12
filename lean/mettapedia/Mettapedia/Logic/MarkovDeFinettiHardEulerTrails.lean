import Mettapedia.Logic.MarkovDeFinettiHardBESTCore

/-! LLM primer:
- `edgeTok G = Σ a : Fin k, Σ b : Fin k, Fin (G a b)` — one token per parallel edge copy.
- An Euler trail `f : Fin N → edgeTok G` uses each token exactly once (bijective)
  and forms a valid walk (chain condition on consecutive edges).
- `trailVertexSeq G s f : Fin (N+1) → Fin k` recovers the vertex sequence.
- Key invariant: `transCount (trailVertexSeq ...) a b = G a b` for all `a b`.

# Euler Trails over Edge Tokens (Phase B, Step 1)

## Main definitions

- `edgeSrc`, `edgeTgt` : source and target of an edge token
- `IsEulerTrail G s t f` : Euler trail predicate
- `eulerTrailFinset G s t` : finset of all Euler trails from `s` to `t`
- `trailVertexSeq G s f` : induced vertex sequence

## Main results

- `trailVertexSeq_zero`, `trailVertexSeq_succ`, `trailVertexSeq_last`
- `edgePairCount_of_isEulerTrail` : transition `(a,b)` appears `G a b` times
- `transCount_trailVertexSeq` : `transCount` of vertex sequence equals `G a b`
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardEulerTrails

open MarkovDeFinettiHardBESTCore
open MarkovExchangeability

variable {k : ℕ}

/-! ## Edge token accessors -/

/-- Source vertex of an edge token. -/
@[simp] def edgeSrc {G : EulerGraph k} (e : edgeTok G) : Fin k := e.1

/-- Target vertex of an edge token. -/
@[simp] def edgeTgt {G : EulerGraph k} (e : edgeTok G) : Fin k := e.2.1

/-- Copy index of an edge token. -/
@[simp] def edgeCopy {G : EulerGraph k} (e : edgeTok G) : Fin (G e.1 e.2.1) := e.2.2

/-- Reconstruct an edge token from source, target, copy. -/
def mkEdgeTok (G : EulerGraph k) (a b : Fin k) (c : Fin (G a b)) : edgeTok G :=
  ⟨a, b, c⟩

/-! ## Euler trail predicate -/

/-- `IsEulerTrail G s t f` asserts that `f : Fin N → edgeTok G` (where `N = totalEdgeTokens G`)
is an Euler trail from vertex `s` to vertex `t`: it uses each edge token exactly once
and forms a valid directed walk.

When `N = 0` (empty graph), the only constraint is `s = t`. -/
def IsEulerTrail (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) : Prop :=
  Function.Bijective f ∧
  (totalEdgeTokens G = 0 → s = t) ∧
  (∀ h : 0 < totalEdgeTokens G, edgeSrc (f ⟨0, h⟩) = s) ∧
  (∀ (i : ℕ) (hi : i + 1 < totalEdgeTokens G),
    edgeTgt (f ⟨i, by omega⟩) = edgeSrc (f ⟨i + 1, hi⟩)) ∧
  (∀ h : 0 < totalEdgeTokens G,
    edgeTgt (f ⟨totalEdgeTokens G - 1, by omega⟩) = t)

/-- Euler circuit: an Euler trail where start equals end. -/
def IsEulerCircuit (G : EulerGraph k) (s : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) : Prop :=
  IsEulerTrail G s s f

/-! ## Accessors for IsEulerTrail components -/

namespace IsEulerTrail

variable {G : EulerGraph k} {s t : Fin k} {f : Fin (totalEdgeTokens G) → edgeTok G}

lemma bijective (hf : IsEulerTrail G s t f) : Function.Bijective f := hf.1

lemma injective (hf : IsEulerTrail G s t f) : Function.Injective f := hf.1.1

lemma surjective (hf : IsEulerTrail G s t f) : Function.Surjective f := hf.1.2

lemma empty_eq (hf : IsEulerTrail G s t f) (h0 : totalEdgeTokens G = 0) : s = t :=
  hf.2.1 h0

lemma start_eq (hf : IsEulerTrail G s t f) (h : 0 < totalEdgeTokens G) :
    edgeSrc (f ⟨0, h⟩) = s := hf.2.2.1 h

lemma chain (hf : IsEulerTrail G s t f) (i : ℕ) (hi : i + 1 < totalEdgeTokens G) :
    edgeTgt (f ⟨i, by omega⟩) = edgeSrc (f ⟨i + 1, hi⟩) := hf.2.2.2.1 i hi

lemma end_eq (hf : IsEulerTrail G s t f) (h : 0 < totalEdgeTokens G) :
    edgeTgt (f ⟨totalEdgeTokens G - 1, by omega⟩) = t := hf.2.2.2.2 h

end IsEulerTrail

/-! ## Finsets of trails and circuits -/

def eulerTrailFinset (G : EulerGraph k) (s t : Fin k) :
    Finset (Fin (totalEdgeTokens G) → edgeTok G) :=
  Finset.univ.filter (IsEulerTrail G s t)

def eulerCircuitFinset (G : EulerGraph k) (s : Fin k) :
    Finset (Fin (totalEdgeTokens G) → edgeTok G) :=
  eulerTrailFinset G s s

@[simp] lemma mem_eulerTrailFinset (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) :
    f ∈ eulerTrailFinset G s t ↔ IsEulerTrail G s t f := by
  simp [eulerTrailFinset]

@[simp] lemma mem_eulerCircuitFinset (G : EulerGraph k) (s : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) :
    f ∈ eulerCircuitFinset G s ↔ IsEulerCircuit G s f := by
  simp [eulerCircuitFinset, IsEulerCircuit]

/-! ## Vertex sequence from a trail -/

/-- The vertex sequence `Fin (N + 1) → Fin k` induced by an Euler trail.
Position 0 is the start vertex `s`; position `i + 1` is the target of the `i`-th edge. -/
def trailVertexSeq (G : EulerGraph k) (s : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) :
    Fin (totalEdgeTokens G + 1) → Fin k := fun i =>
  if h : 0 < i.1 then edgeTgt (f ⟨i.1 - 1, by omega⟩)
  else s

@[simp] lemma trailVertexSeq_zero (G : EulerGraph k) (s : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) :
    trailVertexSeq G s f ⟨0, by omega⟩ = s := by
  simp [trailVertexSeq]

lemma trailVertexSeq_succ (G : EulerGraph k) (s : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G)
    (i : ℕ) (hi : i < totalEdgeTokens G) :
    trailVertexSeq G s f ⟨i + 1, by omega⟩ = edgeTgt (f ⟨i, hi⟩) := by
  simp only [trailVertexSeq, Nat.succ_pos, ↓reduceDIte, Nat.add_sub_cancel]

lemma trailVertexSeq_last (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (hf : IsEulerTrail G s t f) :
    trailVertexSeq G s f ⟨totalEdgeTokens G, by omega⟩ = t := by
  by_cases hN : totalEdgeTokens G = 0
  · simp [trailVertexSeq, hN, hf.empty_eq hN]
  · have hpos : 0 < totalEdgeTokens G := Nat.pos_of_ne_zero hN
    simp only [trailVertexSeq, hpos, ↓reduceDIte]
    convert hf.end_eq hpos using 2

/-! ## Edge source/target match vertex sequence -/

/-- The source of the `i`-th edge equals the `i`-th vertex in the sequence. -/
lemma isEulerTrail_edgeSrc_eq (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (hf : IsEulerTrail G s t f)
    (i : ℕ) (hi : i < totalEdgeTokens G) :
    edgeSrc (f ⟨i, hi⟩) = trailVertexSeq G s f ⟨i, by omega⟩ := by
  induction i with
  | zero =>
    simp [trailVertexSeq]
    exact hf.start_eq hi
  | succ j ih =>
    rw [trailVertexSeq_succ G s f j (by omega)]
    exact (hf.chain j (by omega : j + 1 < totalEdgeTokens G)).symm

/-- The target of the `i`-th edge equals the `(i+1)`-th vertex in the sequence. -/
lemma isEulerTrail_edgeTgt_eq (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (_hf : IsEulerTrail G s t f)
    (i : ℕ) (hi : i < totalEdgeTokens G) :
    edgeTgt (f ⟨i, hi⟩) = trailVertexSeq G s f ⟨i + 1, by omega⟩ := by
  rw [trailVertexSeq_succ G s f i hi]

/-! ## Helper: cardinality of filter through a bijection -/

/-- Filtering `Finset.univ` through `P ∘ f` when `f` is bijective preserves cardinality. -/
lemma card_filter_comp_bijective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Bijective f) (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter (P ∘ f)).card = (Finset.univ.filter P).card := by
  classical
  rw [← Finset.card_image_of_injective (Finset.univ.filter (P ∘ f)) hf.injective]
  congr 1
  ext b
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hb; obtain ⟨a, rfl⟩ := hf.surjective b; exact ⟨a, hb, rfl⟩

/-! ## Token count invariant -/

/-- The number of edge tokens from `a` to `b` in the multigraph is `G a b`. -/
lemma card_tokens_ab (G : EulerGraph k) (a b : Fin k) :
    (Finset.univ.filter (fun (e : edgeTok G) => edgeSrc e = a ∧ edgeTgt e = b)).card =
      G a b := by
  classical
  -- The set is the image of Fin (G a b) under c ↦ ⟨a, b, c⟩
  set S := Finset.univ.filter (fun (e : edgeTok G) => edgeSrc e = a ∧ edgeTgt e = b) with hS_def
  -- Define the embedding
  let emb : Fin (G a b) ↪ edgeTok G :=
    ⟨fun c => ⟨a, b, c⟩, by intro c₁ c₂ h; simpa [edgeTok, Sigma.mk.inj_iff] using h⟩
  -- Show the image equals S
  have himg : (Finset.univ : Finset (Fin (G a b))).map emb = S := by
    ext ⟨a', b', c'⟩
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, edgeSrc, edgeTgt,
      hS_def, emb]
    constructor
    · rintro ⟨c, hc⟩
      simp only [Function.Embedding.coeFn_mk] at hc
      have h1 : a = a' := congrArg Sigma.fst hc
      have h2 : b = b' := by
        subst h1
        exact congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj hc).2)
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨ha', hb'⟩
      subst ha'; subst hb'
      exact ⟨c', rfl⟩
  calc S.card
      = ((Finset.univ : Finset (Fin (G a b))).map emb).card := by rw [himg]
    _ = (Finset.univ : Finset (Fin (G a b))).card := Finset.card_map _
    _ = G a b := Fintype.card_fin _

/-- In an Euler trail, transition `(a, b)` appears exactly `G a b` times. -/
theorem edgePairCount_of_isEulerTrail (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (hf : IsEulerTrail G s t f)
    (a b : Fin k) :
    (Finset.univ.filter (fun i => edgeSrc (f i) = a ∧ edgeTgt (f i) = b)).card = G a b := by
  classical
  -- Rewrite as a filter through f, then use bijectivity
  have heq : (Finset.univ.filter (fun i => edgeSrc (f i) = a ∧ edgeTgt (f i) = b)) =
      (Finset.univ.filter ((fun e => edgeSrc e = a ∧ edgeTgt e = b) ∘ f)) := by
    ext i; simp [Function.comp]
  rw [heq, card_filter_comp_bijective f hf.bijective, card_tokens_ab]

/-! ## Fin-level source/target lemmas -/

/-- Source of the `i`-th edge equals the `castSucc i`-th vertex (Fin-level version). -/
lemma edgeSrc_eq_trailVertexSeq_castSucc (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (hf : IsEulerTrail G s t f)
    (i : Fin (totalEdgeTokens G)) :
    edgeSrc (f i) = trailVertexSeq G s f (Fin.castSucc i) :=
  isEulerTrail_edgeSrc_eq G s t f hf i.1 i.2

/-- Target of the `i`-th edge equals the `succ i`-th vertex (Fin-level version). -/
lemma edgeTgt_eq_trailVertexSeq_succ (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (hf : IsEulerTrail G s t f)
    (i : Fin (totalEdgeTokens G)) :
    edgeTgt (f i) = trailVertexSeq G s f (Fin.succ i) :=
  isEulerTrail_edgeTgt_eq G s t f hf i.1 i.2

/-! ## Connection to `transCount` -/

/-- The transition count of the vertex sequence equals the graph multiplicity.
This is the key invariant connecting Euler trails back to `stateOfTraj`. -/
theorem transCount_trailVertexSeq (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (hf : IsEulerTrail G s t f)
    (a b : Fin k) :
    transCount (n := totalEdgeTokens G) (trailVertexSeq G s f) a b = G a b := by
  classical
  simp only [transCount]
  -- Rewrite castSucc/succ vertex lookups to edgeSrc/edgeTgt via Fin-level lemmas
  have hsrc : ∀ (i : Fin (totalEdgeTokens G)),
      trailVertexSeq G s f (Fin.castSucc i) = edgeSrc (f i) :=
    fun i => (edgeSrc_eq_trailVertexSeq_castSucc G s t f hf i).symm
  have htgt : ∀ (i : Fin (totalEdgeTokens G)),
      trailVertexSeq G s f (Fin.succ i) = edgeTgt (f i) :=
    fun i => (edgeTgt_eq_trailVertexSeq_succ G s t f hf i).symm
  simp_rw [hsrc, htgt]
  exact edgePairCount_of_isEulerTrail G s t f hf a b

/-! ## Start and end vertex of the trail vertex sequence -/

lemma trailVertexSeq_start (G : EulerGraph k) (s : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) :
    trailVertexSeq G s f 0 = s := by
  simp [trailVertexSeq]

lemma trailVertexSeq_end (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (hf : IsEulerTrail G s t f) :
    trailVertexSeq G s f (Fin.last (totalEdgeTokens G)) = t := by
  simp only [Fin.last]
  exact trailVertexSeq_last G s t f hf

/-! ## Equivalence to Equiv (for counting) -/

/-- An Euler trail function can be promoted to an equivalence. -/
def eulerTrailEquiv (G : EulerGraph k) (s t : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) (hf : IsEulerTrail G s t f) :
    Fin (totalEdgeTokens G) ≃ edgeTok G :=
  Equiv.ofBijective f hf.bijective

end MarkovDeFinettiHardEulerTrails

end Mettapedia.Logic
