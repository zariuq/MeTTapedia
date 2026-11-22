import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalControls

/-!
# Deciding equality and unifiability of rational trees from finite presentations

**Equality** (`unfold_eq_iff_agree`, `decidableUnfoldEq`): two nodes of a finite graph unfold to the
same tree exactly when they agree to depth `card (N × N)`. Agreement to depth `m` is a decreasing
sequence of finite relations; it is constant from the first depth where it stops shrinking; and a
constant one is a bisimulation.

**Unifiability** (`consistent_rstore_iff_unifiable`): for equations between nodes, the closure of
`RationalUnification` read on nodes (`NodeJoined`, which also joins nodes with equal unfoldings) is
computed by iterating one step at most `card (N × N)` times (`closure`, `mem_closure_iff`). Its
refutations are exactly the refutations of the unfolded store (`clash_iff`), so the store is
solvable over rational trees exactly when the computed closure joins no two different rigid labels
(`unifiable`).

Comparing or unifying presented trees therefore needs only finitely many pairs of nodes. The
controls run both procedures by `decide`: `X = f(X)` is accepted, `f(X) = g(Y)` refuted, and the two
nodes of a two-cycle of `f` unfold alike.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP

variable {σ : LPSignature}

instance Head.decidableEq [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : DecidableEq (Head σ)
  | .var a, .var b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Head.var.inj e)
  | .const a, .const b =>
      if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Head.const.inj e)
  | .fn a, .fn b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Head.fn.inj e)
  | .var _, .const _ => isFalse fun e => by cases e
  | .var _, .fn _ => isFalse fun e => by cases e
  | .const _, .var _ => isFalse fun e => by cases e
  | .const _, .fn _ => isFalse fun e => by cases e
  | .fn _, .var _ => isFalse fun e => by cases e
  | .fn _, .const _ => isFalse fun e => by cases e

namespace Raw.Graph

variable {N : Type*} (G : Graph σ N) [DecidableEq (Head σ)]

/-- **Agreement to a depth**: equal labels, and agreement one level less below them. -/
def agree : ℕ → N → N → Bool
  | 0, k, l => decide (G.label k = G.label l)
  | m + 1, k, l => decide (G.label k = G.label l) &&
      (List.range (G.label k).arity).all fun i => agree m (G.edge k i) (G.edge l i)

variable {G}

theorem agree_succ_iff {m : ℕ} {k l : N} :
    G.agree (m + 1) k l = true ↔
      G.label k = G.label l ∧ ∀ i < (G.label k).arity, G.agree m (G.edge k i) (G.edge l i) = true := by
  simp [agree, List.all_eq_true, List.mem_range]

theorem agree_label : ∀ {m : ℕ} {k l : N}, G.agree m k l = true → G.label k = G.label l
  | 0, _, _, h => by simpa [agree] using h
  | _ + 1, _, _, h => (agree_succ_iff.mp h).1

/-- Agreement to a depth is weaker at smaller depths. -/
theorem agree_of_succ : ∀ {m : ℕ} {k l : N}, G.agree (m + 1) k l = true → G.agree m k l = true
  | 0, _, _, h => by simpa [agree] using (agree_succ_iff.mp h).1
  | m + 1, _, _, h => by
    obtain ⟨labels, kids⟩ := agree_succ_iff.mp h
    exact agree_succ_iff.mpr ⟨labels, fun i inside => agree_of_succ (kids i inside)⟩

/-- Equal unfoldings agree to every depth. -/
theorem agree_of_unfold_eq : ∀ (m : ℕ) {k l : N}, G.unfold k = G.unfold l → G.agree m k l = true
  | 0, _, _, same => by simpa [agree] using Option.some.inj (congrFun same [])
  | m + 1, k, l, same => by
    have labels : G.label k = G.label l := Option.some.inj (congrFun same [])
    refine agree_succ_iff.mpr ⟨labels, fun i inside => agree_of_unfold_eq m ?_⟩
    have kids := congrArg (child i) same
    rwa [child_unfold, child_unfold, if_pos inside, if_pos (labels ▸ inside)] at kids

variable [Fintype N]

/-- The pairs of nodes that agree to depth `m`. -/
def level (m : ℕ) : Finset (N × N) := Finset.univ.filter fun p => G.agree m p.1 p.2 = true

theorem mem_level {m : ℕ} {p : N × N} : p ∈ G.level m ↔ G.agree m p.1 p.2 = true := by
  simp [level]

theorem level_succ_subset (m : ℕ) : G.level (m + 1) ⊆ G.level m := fun _ member =>
  mem_level.mpr (agree_of_succ (mem_level.mp member))

/-- Once agreement stops shrinking it is constant. -/
theorem level_stable {m : ℕ} (stable : G.level (m + 1) = G.level m) :
    ∀ j, m ≤ j → G.level j = G.level m := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih =>
    ext p
    rw [← stable, mem_level, mem_level, agree_succ_iff, agree_succ_iff]
    refine and_congr Iff.rfl (forall₂_congr fun i _ => ?_)
    rw [← mem_level (p := (G.edge p.1 i, G.edge p.2 i)), ← mem_level (p := (G.edge p.1 i, G.edge p.2 i)), ih]

/-- **Agreement stops shrinking within `card (N × N)` steps.** -/
theorem exists_level_stable :
    ∃ m ≤ Fintype.card (N × N), G.level (m + 1) = G.level m := by
  by_contra none
  push Not at none
  have shrinking : ∀ m, m ≤ Fintype.card (N × N) + 1 →
      (G.level m).card + m ≤ Fintype.card (N × N) := by
    intro m
    induction m with
    | zero =>
      intro _
      simpa using Finset.card_le_card (Finset.subset_univ (G.level 0))
    | succ m ih =>
      intro hm
      have strict : (G.level (m + 1)).card < (G.level m).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨G.level_succ_subset m, none m (by omega)⟩)
      have := ih (by omega)
      omega
  have := shrinking (Fintype.card (N × N) + 1) le_rfl
  omega

/-- A constant agreement is a bisimulation. -/
theorem isBisimulation_of_stable {m : ℕ} (stable : G.level (m + 1) = G.level m) :
    G.IsBisimulation fun k l => G.agree m k l = true := by
  intro k l related
  have deeper : G.agree (m + 1) k l = true := by
    rw [← mem_level (p := (k, l)), stable, mem_level]
    exact related
  exact agree_succ_iff.mp deeper

/-- **Equality of unfoldings is agreement to depth `card (N × N)`.** -/
theorem unfold_eq_iff_agree (k l : N) :
    G.unfold k = G.unfold l ↔ G.agree (Fintype.card (N × N)) k l = true := by
  refine ⟨agree_of_unfold_eq _, fun agreed => ?_⟩
  obtain ⟨m, bound, stable⟩ := G.exists_level_stable
  have atM : G.agree m k l = true := by
    rw [← mem_level (p := (k, l)), ← G.level_stable stable _ bound, mem_level]
    exact agreed
  exact (G.unfold_eq_iff k l).mpr ⟨_, isBisimulation_of_stable stable, atM⟩

/-- **Equality of presented rational trees is decidable.** -/
instance decidableUnfoldEq (k l : N) : Decidable (G.unfold k = G.unfold l) :=
  decidable_of_iff _ (unfold_eq_iff_agree k l).symm


end Raw.Graph

namespace Head

/-- Whether a label is a variable. -/
def isVar : Head σ → Bool
  | .var _ => true
  | _ => false

/-- Whether a label is a function symbol. -/
def isFn : Head σ → Bool
  | .fn _ => true
  | _ => false

theorem rigid_iff_isVar (h : Head σ) : h.Rigid ↔ h.isVar = false := by
  cases h with
  | var v => exact ⟨fun rigid => absurd rfl (rigid v), fun e => by simp [isVar] at e⟩
  | const c => exact ⟨fun _ => rfl, fun _ v same => by cases same⟩
  | fn f => exact ⟨fun _ => rfl, fun _ v same => by cases same⟩

theorem isFn_iff (h : Head σ) : h.isFn = true ↔ ∃ f, h = .fn f := by
  cases h <;> simp [isFn]

end Head

/-! ## Deciding unifiability from finite presentations -/

namespace Raw.Graph

variable {N : Type*}

/-- The equations between nodes, as trees. -/
def store (G : Graph σ N) (E : List (N × N)) : List (Raw σ × Raw σ) :=
  E.map fun e => (G.unfold e.1, G.unfold e.2)

theorem unfold_nil (G : Graph σ N) (k : N) : G.unfold k [] = some (G.label k) := rfl

/-- **The closure on nodes**: the equations, equal unfoldings, symmetry, transitivity and
decomposition of equal function symbols. -/
inductive NodeJoined (G : Graph σ N) (E : List (N × N)) : N → N → Prop
  | base {k l : N} : (k, l) ∈ E → NodeJoined G E k l
  | same {k l : N} : G.unfold k = G.unfold l → NodeJoined G E k l
  | symm {k l : N} : NodeJoined G E k l → NodeJoined G E l k
  | trans {k l m : N} : NodeJoined G E k l → NodeJoined G E l m → NodeJoined G E k m
  | down {k l : N} {f : σ.functionSymbols} {i : ℕ} : NodeJoined G E k l → G.label k = .fn f →
      G.label l = .fn f → i < σ.functionArity f → NodeJoined G E (G.edge k i) (G.edge l i)

variable {G : Graph σ N} {E : List (N × N)}

/-- The closure on nodes joins their unfoldings. -/
theorem NodeJoined.joined {k l : N} (joined : NodeJoined G E k l) :
    Joined (G.store E) (G.unfold k) (G.unfold l) := by
  induction joined with
  | base member => exact Joined.base (List.mem_map.mpr ⟨_, member, rfl⟩)
  | same equal => rw [equal]; exact Joined.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @down k l f i _ lk ll inside ih =>
    have rk : G.unfold k [] = some (.fn f) := by rw [unfold_nil, lk]
    have rl : G.unfold l [] = some (.fn f) := by rw [unfold_nil, ll]
    have kids := Joined.down (i := i) ih rk rl inside
    rwa [G.child_unfold, G.child_unfold, lk, ll, if_pos (show i < (Head.fn f).arity from inside),
      if_pos (show i < (Head.fn f).arity from inside)] at kids

/-- **The closure of the unfolded store is the closure on nodes.** -/
theorem NodeJoined.of_joined {s t : Raw σ} (joined : Joined (G.store E) s t) :
    s = t ∨ ∃ k l, NodeJoined G E k l ∧ s = G.unfold k ∧ t = G.unfold l := by
  induction joined with
  | base member =>
    obtain ⟨e, present, same⟩ := List.mem_map.mp member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact Or.inr ⟨e.1, e.2, .base present, rfl, rfl⟩
  | refl t => exact Or.inl rfl
  | symm _ ih =>
    rcases ih with same | ⟨k, l, j, rfl, rfl⟩
    · exact Or.inl same.symm
    · exact Or.inr ⟨l, k, j.symm, rfl, rfl⟩
  | trans _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | ⟨k, l, j₁, rfl, rfl⟩
    · exact ih₂
    · rcases ih₂ with same | ⟨l', m, j₂, middle, rfl⟩
      · exact Or.inr ⟨k, l, j₁, rfl, same.symm⟩
      · exact Or.inr ⟨k, m, j₁.trans ((NodeJoined.same middle).trans j₂), rfl, rfl⟩
  | @down s t f i _ rs rt inside ih =>
    rcases ih with rfl | ⟨k, l, j, rfl, rfl⟩
    · exact Or.inl rfl
    · have lk : G.label k = .fn f := Option.some.inj ((G.unfold_nil k).symm.trans rs)
      have ll : G.label l = .fn f := Option.some.inj ((G.unfold_nil l).symm.trans rt)
      refine Or.inr ⟨_, _, .down j lk ll inside, ?_, ?_⟩
      · rw [G.child_unfold, lk, if_pos (show i < (Head.fn f).arity from inside)]
      · rw [G.child_unfold, ll, if_pos (show i < (Head.fn f).arity from inside)]

variable (G E) in
/-- A refutation on nodes. -/
def NodeClash : Prop :=
  ∃ k l, NodeJoined G E k l ∧ (G.label k).Rigid ∧ (G.label l).Rigid ∧ G.label k ≠ G.label l

variable (G E) in
/-- **Refutations of the unfolded store are refutations on nodes.** -/
theorem clash_iff : Clash (G.store E) ↔ G.NodeClash E := by
  constructor
  · rintro ⟨s, t, hs, ht, j, rs, rt, rigidS, rigidT, distinct⟩
    rcases NodeJoined.of_joined j with rfl | ⟨k, l, jn, rfl, rfl⟩
    · rw [rs] at rt
      exact absurd (Option.some.inj rt) distinct
    · have lk : G.label k = hs := Option.some.inj ((G.unfold_nil k).symm.trans rs)
      have ll : G.label l = ht := Option.some.inj ((G.unfold_nil l).symm.trans rt)
      subst lk ll
      exact ⟨k, l, jn, rigidS, rigidT, distinct⟩
  · rintro ⟨k, l, jn, rk, rl, distinct⟩
    exact ⟨_, _, _, _, jn.joined, G.unfold_nil k, G.unfold_nil l, rk, rl, distinct⟩

variable [Fintype N] [DecidableEq N] [DecidableEq (Head σ)]

variable (G E) in
/-- One step of the closure on a finite set of pairs. -/
def StepRel (S : Finset (N × N)) (p : N × N) : Prop :=
  p ∈ S ∨ p ∈ E ∨ G.agree (Fintype.card (N × N)) p.1 p.2 = true ∨ (p.2, p.1) ∈ S ∨
    (∃ m, (p.1, m) ∈ S ∧ (m, p.2) ∈ S) ∨
    ∃ q ∈ S, G.label q.1 = G.label q.2 ∧ (G.label q.1).isFn = true ∧
      ∃ i ∈ List.range (G.label q.1).arity, (G.edge q.1 i, G.edge q.2 i) = p

instance (S : Finset (N × N)) : DecidablePred (StepRel G E S) := fun _ => by
  unfold StepRel
  infer_instance

variable (G E) in
/-- One step of the closure, computed. -/
def closeStep (S : Finset (N × N)) : Finset (N × N) := Finset.univ.filter (StepRel G E S)

variable (G E) in
/-- The closure after `m` steps. -/
def closureAt (m : ℕ) : Finset (N × N) := (closeStep G E)^[m] ∅

variable (G E) in
/-- **The computed closure.** -/
def closure : Finset (N × N) := closureAt G E (Fintype.card (N × N))

theorem mem_closeStep {S : Finset (N × N)} {p : N × N} : p ∈ closeStep G E S ↔ StepRel G E S p := by
  simp [closeStep]

theorem closureAt_succ (m : ℕ) : closureAt G E (m + 1) = closeStep G E (closureAt G E m) :=
  Function.iterate_succ_apply' _ _ _

theorem subset_closeStep (S : Finset (N × N)) : S ⊆ closeStep G E S :=
  fun _ member => mem_closeStep.mpr (Or.inl member)

/-- Each step adds only joined pairs. -/
theorem closeStep_sound {S : Finset (N × N)} (sound : ∀ p ∈ S, NodeJoined G E p.1 p.2) :
    ∀ p ∈ closeStep G E S, NodeJoined G E p.1 p.2 := by
  intro p member
  rcases mem_closeStep.mp member with inS | inE | agreed | swapped | ⟨m, left, right⟩ |
      ⟨q, inS, labels, fnLabel, i, inside, rfl⟩
  · exact sound p inS
  · exact .base inE
  · exact .same ((unfold_eq_iff_agree p.1 p.2).mpr agreed)
  · exact (sound _ swapped).symm
  · exact (sound _ left).trans (sound _ right)
  · obtain ⟨f, lf⟩ := (Head.isFn_iff _).mp fnLabel
    have below : i < σ.functionArity f := by
      have := List.mem_range.mp inside
      rwa [lf] at this
    exact .down (sound q inS) lf (labels ▸ lf) below

theorem closureAt_sound : ∀ (m : ℕ), ∀ p ∈ closureAt G E m, NodeJoined G E p.1 p.2
  | 0, _, member => absurd member (Finset.notMem_empty _)
  | m + 1, p, member => by
    rw [closureAt_succ] at member
    exact closeStep_sound (closureAt_sound m) p member

/-- **The closure stops growing within `card (N × N)` steps.** -/
theorem exists_closureAt_stable :
    ∃ m ≤ Fintype.card (N × N), closureAt G E (m + 1) = closureAt G E m := by
  by_contra none
  push Not at none
  have growing : ∀ m, m ≤ Fintype.card (N × N) + 1 → m ≤ (closureAt G E m).card := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have strict : (closureAt G E m).card < (closureAt G E (m + 1)).card := by
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, (none m (by omega)).symm⟩)
        rw [closureAt_succ]
        exact subset_closeStep _
      have := ih (by omega)
      omega
  have big := growing (Fintype.card (N × N) + 1) le_rfl
  have small : (closureAt G E (Fintype.card (N × N) + 1)).card ≤ Fintype.card (N × N) := by
    simpa using Finset.card_le_card (Finset.subset_univ (closureAt G E (Fintype.card (N × N) + 1)))
  omega

theorem closureAt_stable {m : ℕ} (stable : closureAt G E (m + 1) = closureAt G E m) :
    ∀ j, m ≤ j → closureAt G E j = closureAt G E m := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih => rw [closureAt_succ, ih, ← closureAt_succ, stable]

/-- The computed closure is a fixed point. -/
theorem closeStep_closure : closeStep G E (closure G E) = closure G E := by
  obtain ⟨m, bound, stable⟩ := exists_closureAt_stable (G := G) (E := E)
  have atM : closure G E = closureAt G E m := closureAt_stable stable _ bound
  rw [atM, ← closureAt_succ, stable]

theorem mem_closure_of_step {p : N × N} (step : StepRel G E (closure G E) p) : p ∈ closure G E := by
  rw [← closeStep_closure]
  exact mem_closeStep.mpr step

/-- **The computed closure is the closure on nodes.** -/
theorem mem_closure_iff (k l : N) : (k, l) ∈ closure G E ↔ NodeJoined G E k l := by
  constructor
  · exact closureAt_sound _ (k, l)
  · intro joined
    induction joined with
    | base member => exact mem_closure_of_step (Or.inr (Or.inl member))
    | @same k l equal =>
      exact mem_closure_of_step (Or.inr (Or.inr (Or.inl ((unfold_eq_iff_agree k l).mp equal))))
    | symm _ ih => exact mem_closure_of_step (Or.inr (Or.inr (Or.inr (Or.inl ih))))
    | @trans k l m _ _ ih₁ ih₂ =>
      exact mem_closure_of_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, ih₁, ih₂⟩)))))
    | @down k l f i _ lk ll inside ih =>
      refine mem_closure_of_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨(k, l), ih, ?_, ?_, i, ?_, rfl⟩)))))
      · rw [lk, ll]
      · rw [lk]; rfl
      · rw [lk]
        exact List.mem_range.mpr inside

/-- **Refutation on nodes is decided by the computed closure.** -/
theorem nodeClash_iff : G.NodeClash E ↔ ∃ p ∈ closure G E, (G.label p.1).isVar = false ∧
    (G.label p.2).isVar = false ∧ G.label p.1 ≠ G.label p.2 := by
  constructor
  · rintro ⟨k, l, joined, rk, rl, distinct⟩
    exact ⟨(k, l), (mem_closure_iff k l).mpr joined, (Head.rigid_iff_isVar _).mp rk,
      (Head.rigid_iff_isVar _).mp rl, distinct⟩
  · rintro ⟨p, member, rk, rl, distinct⟩
    exact ⟨p.1, p.2, (mem_closure_iff p.1 p.2).mp member, (Head.rigid_iff_isVar _).mpr rk,
      (Head.rigid_iff_isVar _).mpr rl, distinct⟩

instance decidableNodeClash : Decidable (G.NodeClash E) :=
  decidable_of_iff _ nodeClash_iff.symm

/-! ## Rational unifiability is decidable -/

variable (G) in
/-- A node's unfolding, as a rational tree. -/
def rtree (k : N) : RTree σ := ⟨G.unfold k, G.wf_unfold k, G.rational_unfold k⟩

variable (G E) in
/-- The equations between nodes, as rational trees. -/
def rstore : EquationStore (RTree σ) := E.map fun e => (G.rtree e.1, G.rtree e.2)

omit [DecidableEq N] [DecidableEq (Head σ)] in
theorem rawStore_rstore : rawStore (G.rstore E) = G.store E := by
  simp only [rawStore, rstore, store, List.map_map]
  rfl

omit [DecidableEq N] [DecidableEq (Head σ)] in
/-- **Rational unifiability is the absence of a refutation on nodes.** -/
theorem consistent_rstore_iff :
    (rationalAction σ).Consistent (G.rstore E) ↔ ¬ G.NodeClash E := by
  rw [consistent_iff_not_refuted, Refuted, rawStore_rstore, clash_iff]

/-- **Unification over rational trees is decidable from finite presentations.** -/
def decideConsistent : Decidable ((rationalAction σ).Consistent (G.rstore E)) :=
  decidable_of_iff _ consistent_rstore_iff.symm

variable (G E) in
/-- **The decision procedure for rational unifiability**, as a computed Boolean. -/
def unifiable : Bool := !decide (G.NodeClash E)

theorem consistent_rstore_iff_unifiable :
    (rationalAction σ).Consistent (G.rstore E) ↔ G.unifiable E = true := by
  rw [consistent_rstore_iff, unifiable]
  simp

end Raw.Graph

/-! ## Controls: the procedures run -/

namespace Controls

open Raw

/-- `X = f(X)`: node `0` is `X`, node `1` is `f(node 0)`. -/
def loopPresented : Graph ctlSig (Fin 2) where
  label k := if k = 0 then .var (0 : ℕ) else .fn Sym.f
  edge _ _ := 0

/-- `f(X) = g(Y)`: nodes `X`, `Y`, `f(X)`, `g(Y)`. -/
def clashPresented : Graph ctlSig (Fin 4) where
  label k := if k = 0 then .var (0 : ℕ) else if k = 1 then .var (1 : ℕ) else
    if k = 2 then .fn Sym.f else .fn Sym.g
  edge k _ := if k = 2 then 0 else 1

/-- `f(f(f(…)))` presented by a two-cycle. -/
def twoCycle : Graph ctlSig (Fin 2) where
  label _ := .fn Sym.f
  edge k _ := if k = 0 then 1 else 0

/-- **The decision procedure accepts `X = f(X)`**, by computation. -/
theorem loopPresented_consistent :
    (rationalAction ctlSig).Consistent (loopPresented.rstore [(0, 1)]) :=
  (Graph.consistent_rstore_iff_unifiable (G := loopPresented) (E := [(0, 1)])).mpr (by decide)

/-- **The decision procedure refutes `f(X) = g(Y)`**, by computation. -/
theorem clashPresented_inconsistent :
    ¬ (rationalAction ctlSig).Consistent (clashPresented.rstore [(2, 3)]) := fun consistent =>
  absurd ((Graph.consistent_rstore_iff_unifiable (G := clashPresented) (E := [(2, 3)])).mp consistent)
    (by decide +kernel)

/-- **Equality of presented trees is computed**: the two nodes of a two-cycle unfold alike, and `X`
differs from `f(X)`. -/
theorem presented_equalities :
    twoCycle.unfold 0 = twoCycle.unfold 1 ∧ loopPresented.unfold 0 ≠ loopPresented.unfold 1 :=
  ⟨by decide, by decide⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.Raw.Graph.agree_of_unfold_eq
#print axioms Rational.Raw.Graph.exists_level_stable
#print axioms Rational.Raw.Graph.isBisimulation_of_stable
#print axioms Rational.Raw.Graph.unfold_eq_iff_agree
#print axioms Rational.Raw.Graph.decidableUnfoldEq
#print axioms Rational.Raw.Graph.NodeJoined.joined
#print axioms Rational.Raw.Graph.NodeJoined.of_joined
#print axioms Rational.Raw.Graph.clash_iff
#print axioms Rational.Raw.Graph.exists_closureAt_stable
#print axioms Rational.Raw.Graph.mem_closure_iff
#print axioms Rational.Raw.Graph.nodeClash_iff
#print axioms Rational.Raw.Graph.decidableNodeClash
#print axioms Rational.Raw.Graph.consistent_rstore_iff
#print axioms Rational.Raw.Graph.decideConsistent
#print axioms Rational.Raw.Graph.consistent_rstore_iff_unifiable
#print axioms Rational.Controls.loopPresented_consistent
#print axioms Rational.Controls.clashPresented_inconsistent
#print axioms Rational.Controls.presented_equalities

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
