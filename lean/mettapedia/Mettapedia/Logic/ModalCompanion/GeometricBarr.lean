import Mettapedia.Logic.ModalCompanion.Derivations

/-!
# Gödel's Theorem 62: a propositional Barr theorem, as a proof transformation

A *geometric implication* over atoms is a formula `p₁ ∧ … ∧ pₘ ⊃ q₁ ∨ … ∨ qₙ` with atoms
`pᵢ, qⱼ` (`m, n ≥ 0`; for `n = 0` it is `¬(p₁ ∧ … ∧ pₘ)`, for `m = 0` a disjunction).
Theorem 62 of Gödel's notebook *Resultate Grundlagen* (1941) states: if a geometric
implication `F` follows classically from a finite set `𝔄` of geometric implications, then it
follows intuitionistically. This is the finite propositional geometric fragment of what is
now called Barr's theorem; nothing in this file concerns first-order geometric theories.

Gödel's proof builds a finite *ramification tree* of sets of atoms, rooted at the antecedent
atoms of `F`. At a node, the implications of `𝔄` whose antecedents are contained in the node
are conjoined and their consequents distributed into disjuncts; the node is extended by the
atoms of each disjunct, keeping the minimal properly larger sets. A branch ends when nothing
new is added, or on a contradiction (an implication with empty consequent). If every
consistent end node contains a consequent atom of `F`, then `F` is derived intuitionistically
by modus ponens and distributivity (forward chaining); otherwise the valuation that makes
exactly the atoms of a consistent end node true satisfies `𝔄` and refutes `F`. Classical
consequence is decided by truth tables, so no choice principle is involved.

The function `ramify` below builds such a tree one implication at a time, as in root-first
proof search for geometric rules (Negri 2003), where the only step that distinguishes
classical from intuitionistic logic, the right rule for implication, is used once, at the
root: at a node it looks for an implication of `𝔄` that is violated by the node (antecedent
inside the node, no consequent atom in the node) and branches on its consequent atoms. It
returns either a derivation from assumptions of the goal disjunction or an open end node,
which is a classical countermodel. The search runs in any Foundation entailment system with
the intuitionistic axioms (`Entailment.Int`); for the calculus `IntH` of `Derivations`, whose
proofs are derivation trees, it produces derivation trees.

## Main results

* `barr`: Theorem 62 in any `Entailment.Int` system, for substitution instances (the atoms
  are read through an arbitrary map `τ`), as a derivation of `F` from the assumptions `𝔄`.
* `theorem62`: the same, producing an `IntDeriv` from the assumptions `𝔄`.
* `theorem62OfClassical`: the proof transformation from a classical derivation (`ClDeriv`)
  of a geometric implication from geometric implications to an intuitionistic one.
* `decideGeometric`: an intuitionistic derivation or a classical countermodel.
* `provable_iff_tautology`: for geometric implications over atoms, provability in
  Foundation's `Propositional.Int` coincides with truth-table consequence.
* Examples: a geometric consequence with its intuitionistic derivation, and the excluded
  middle `p ∨ ¬p`, a classical tautology with a classical derivation but no intuitionistic
  one, which is not intuitionistically equivalent to any geometric implication.

## References

* K. Gödel, *Results on Foundations*, M. Hämeen-Anttila and J. von Plato (eds.), Springer,
  2023 (notebook *Resultate Grundlagen*, Theorem 62).
* S. Negri and J. von Plato, *Intuitionistic and modal logic in Gödel's Resultate
  Grundlagen*, Logique et Analyse 268, 439–465, doi:10.2143/LEA.268.0.3295055.
* M. Barr, *Toposes without points*, J. Pure Appl. Algebra 5 (1974), 265–280.
* S. Negri, *Contraction-free sequent calculi for geometric theories with an application to
  Barr's theorem*, Arch. Math. Logic 42 (2003), 389–401.
* S. Negri and J. von Plato, *Proof Analysis*, Cambridge University Press, 2011.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalCompanion

open LO LO.Entailment

/-! ## Geometric implications -/

theorem all_congr_of_mem {α : Type*} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      all_congr_of_mem fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem any_congr_of_mem {α : Type*} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr_of_mem fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- A geometric implication `p₁ ∧ … ∧ pₘ ⊃ q₁ ∨ … ∨ qₙ` over atoms of type `β`: `ante` lists
the antecedent atoms and `cons` the consequent atoms. -/
structure GeoImp (β : Type*) where
  /-- The antecedent atoms. -/
  ante : List β
  /-- The consequent atoms. -/
  cons : List β
  deriving DecidableEq

namespace GeoImp

variable {β : Type*}

/-- Truth value under a Boolean valuation of the atoms. -/
def eval (v : β → Bool) (g : GeoImp β) : Bool := !(g.ante.all v) || g.cons.any v

theorem eval_eq_false {v : β → Bool} {g : GeoImp β} :
    g.eval v = false ↔ g.ante.all v = true ∧ g.cons.any v = false := by
  unfold eval
  cases g.ante.all v <;> cases g.cons.any v <;> decide

theorem eval_eq_true_of_ante {v : β → Bool} {g : GeoImp β} (h : g.eval v = true)
    (ha : ∀ a ∈ g.ante, v a = true) : ∃ b ∈ g.cons, v b = true := by
  unfold eval at h
  rw [List.all_eq_true.mpr ha] at h
  exact List.any_eq_true.mp h

theorem eval_congr {v w : β → Bool} {g : GeoImp β} (ha : ∀ a ∈ g.ante, v a = w a)
    (hc : ∀ c ∈ g.cons, v c = w c) : g.eval v = g.eval w := by
  unfold eval
  rw [all_congr_of_mem ha, any_congr_of_mem hc]

/-- The formula `⋀ ante ➝ ⋁ cons`, with the atoms read through `τ`. -/
def toFormula {F : Type*} [LogicalConnective F] (τ : β → F) (g : GeoImp β) : F :=
  ⋀(g.ante.map τ) ➝ ⋁(g.cons.map τ)

end GeoImp

/-! ## Truth tables -/

/-- A Boolean function that only depends on the atoms in `l` is constantly true iff it is
true on the valuations `x ↦ (x ∈ T)` for the sublists `T` of `l`. -/
theorem all_sublists_eq_true_iff {α : Type*} [DecidableEq α] (l : List α)
    (f : (α → Bool) → Bool) (hf : ∀ v w : α → Bool, (∀ x ∈ l, v x = w x) → f v = f w) :
    (l.sublists.all fun T => f fun x => decide (x ∈ T)) = true ↔ ∀ v, f v = true := by
  constructor
  · intro h v
    have hT : l.filter v ∈ l.sublists := List.mem_sublists.mpr List.filter_sublist
    rw [hf v (fun x => decide (x ∈ l.filter v)) fun x hx => ?_]
    · exact List.all_eq_true.mp h _ hT
    · cases hv : v x
      · exact (decide_eq_false fun hm => absurd (List.mem_filter.mp hm).2 (by rw [hv]; decide)).symm
      · exact (decide_eq_true (List.mem_filter.mpr ⟨hx, hv⟩)).symm
  · intro h
    exact List.all_eq_true.mpr fun T _ => h _

/-- The atoms occurring in a list of geometric implications. -/
def atomsOf {β : Type*} (𝔄 : List (GeoImp β)) : List β := 𝔄.flatMap fun g => g.ante ++ g.cons

/-- Truth-table test whether `G` follows classically from `𝔄`. -/
def followsTT {β : Type*} [DecidableEq β] (𝔄 : List (GeoImp β)) (G : GeoImp β) : Bool :=
  (atomsOf (G :: 𝔄)).eraseDups.sublists.all fun T =>
    !(𝔄.all (GeoImp.eval fun x => decide (x ∈ T))) || G.eval fun x => decide (x ∈ T)

theorem followsTT_iff {β : Type*} [DecidableEq β] (𝔄 : List (GeoImp β)) (G : GeoImp β) :
    followsTT 𝔄 G = true ↔ ∀ v : β → Bool, (∀ g ∈ 𝔄, g.eval v = true) → G.eval v = true := by
  unfold followsTT
  rw [all_sublists_eq_true_iff _ (fun v => !(𝔄.all (GeoImp.eval v)) || G.eval v)]
  · constructor
    · intro h v hv
      have := h v
      rw [List.all_eq_true.mpr hv] at this
      exact this
    · intro h v
      cases hall : 𝔄.all (GeoImp.eval v)
      · rfl
      · rw [h v (List.all_eq_true.mp hall)]
        rfl
  · intro v w hvw
    have hmem : ∀ g ∈ G :: 𝔄, ∀ x ∈ g.ante ++ g.cons, v x = w x := fun g hg x hx =>
      hvw x (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨g, hg, hx⟩))
    have hg : ∀ g ∈ G :: 𝔄, g.eval v = g.eval w := fun g hg =>
      GeoImp.eval_congr (fun a ha => hmem g hg a (List.mem_append_left _ ha))
        (fun c hc => hmem g hg c (List.mem_append_right _ hc))
    rw [all_congr_of_mem fun g h => hg g (List.mem_cons_of_mem G h), hg G List.mem_cons_self]

/-! ## The ramification tree -/

section Ramification

variable {β : Type*} [DecidableEq β]
variable {F : Type*} [LogicalConnective F] [DecidableEq F]
variable {S : Type*} [Entailment S F]

/-- The atoms that the implications of `𝔄` can add to a node: their consequent atoms. -/
def heads (𝔄 : List (GeoImp β)) : List β := 𝔄.flatMap GeoImp.cons

/-- The number of head occurrences outside the node `X`; it decreases along every branch. -/
def gap (𝔄 : List (GeoImp β)) (X : List β) : ℕ := (heads 𝔄).countP fun a => decide (a ∉ X)

theorem countP_lt_countP {α : Type*} {p q : α → Bool} {c : α} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) → c ∈ l → p c = false →
      q c = true → l.countP p < l.countP q
  | [], _, hc, _, _ => absurd hc List.not_mem_nil
  | a :: l, hpq, hc, hpc, hqc => by
    rw [List.countP_cons, List.countP_cons]
    have hmono : l.countP p ≤ l.countP q :=
      List.countP_mono_left fun x hx => hpq x (List.mem_cons_of_mem a hx)
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [if_neg (by rw [hpc]; decide), if_pos hqc]
      exact Nat.lt_succ_of_le hmono
    · have ih := countP_lt_countP (fun x hx => hpq x (List.mem_cons_of_mem a hx)) hc' hpc hqc
      have hle : (if p a = true then 1 else 0) ≤ (if q a = true then 1 else 0) := by
        cases hpa : p a
        · exact Nat.zero_le _
        · rw [if_pos rfl, if_pos (hpq a List.mem_cons_self hpa)]
      exact Nat.add_lt_add_of_lt_of_le ih hle

theorem gap_cons_lt {𝔄 : List (GeoImp β)} {X : List β} {c : β} (hc : c ∈ heads 𝔄)
    (hcX : c ∉ X) : gap 𝔄 (c :: X) < gap 𝔄 X :=
  countP_lt_countP
    (fun _ _ hx => decide_eq_true fun hxX =>
      of_decide_eq_true hx (List.mem_cons_of_mem c hxX))
    hc (decide_eq_false fun h => h List.mem_cons_self) (decide_eq_true hcX)

/-- An open end node of the ramification tree: a valuation that makes all of `𝔄` and the
atoms of the node `X` true and all of `Q` false. -/
structure OpenNode (𝔄 : List (GeoImp β)) (Q X : List β) where
  /-- The valuation. -/
  val : β → Bool
  sat : ∀ g ∈ 𝔄, g.eval val = true
  node : ∀ x ∈ X, val x = true
  refute : ∀ q ∈ Q, val q = false

/-- The assumptions available at the node `X`: its atoms, then the implications of `𝔄`. -/
def nodeCtx (τ : β → F) (𝔄 : List (GeoImp β)) (X : List β) : List F :=
  X.map τ ++ 𝔄.map (GeoImp.toFormula τ)

/-- What the search below the node `X` returns: a derivation of the goal disjunction from the
assumptions at `X`, or an open end node. -/
abbrev Outcome (𝓢 : S) (τ : β → F) (𝔄 : List (GeoImp β)) (Q X : List β) :=
  (nodeCtx τ 𝔄 X ⊢[𝓢]! ⋁(Q.map τ)) ⊕ OpenNode 𝔄 Q X

variable (𝓢 : S) [Entailment.Int 𝓢]

/-- Combine the branches of a node for the consequent atoms `l`: either every branch closes,
giving `τ c ➝ ⋁Q` at the node for each `c ∈ l`, or some branch has an open end node. -/
def branches (τ : β → F) (𝔄 : List (GeoImp β)) (Q X : List β) :
    (l : List β) → ((c : β) → c ∈ l → Outcome 𝓢 τ 𝔄 Q (c :: X)) →
      ((c : β) → c ∈ l → nodeCtx τ 𝔄 X ⊢[𝓢]! τ c ➝ ⋁(Q.map τ)) ⊕ OpenNode 𝔄 Q X
  | [], _ => .inl fun _ hc => absurd hc List.not_mem_nil
  | c :: l, f =>
    match f c List.mem_cons_self with
    | .inr o =>
      .inr ⟨o.val, o.sat, fun x hx => o.node x (List.mem_cons_of_mem c hx), o.refute⟩
    | .inl d =>
      match branches τ 𝔄 Q X l fun c' hc' => f c' (List.mem_cons_of_mem c hc') with
      | .inr o => .inr o
      | .inl ds => .inl fun c' hc' =>
        if e : c' = c then by
          subst e
          exact FiniteContext.deduct (Γ := nodeCtx τ 𝔄 X) d
        else ds c' ((List.mem_cons.mp hc').resolve_left e)

/-- One step of the ramification tree at the node `X`, given the searches below its children.
If a goal atom is in the node, the node closes. Otherwise, if no implication of `𝔄` is
violated by the node, the node is an open end node. Otherwise a violated implication is fired:
its antecedent is in the node, and the node branches on its consequent atoms. -/
def ramifyStep (τ : β → F) (𝔄 : List (GeoImp β)) (Q X : List β)
    (sub : (c : β) → c ∈ heads 𝔄 → c ∉ X → Outcome 𝓢 τ 𝔄 Q (c :: X)) :
    Outcome 𝓢 τ 𝔄 Q X :=
  match hq : Q.find? (fun q => decide (q ∈ X)) with
  | some q =>
    have hqX : q ∈ X := by
      have h := List.find?_some hq
      exact of_decide_eq_true h
    .inl (right_Disj'_intro τ Q (List.mem_of_find?_eq_some hq) ⨀
      FiniteContext.byAxm (List.mem_append_left _ (List.mem_map_of_mem hqX)))
  | none =>
    match hg : 𝔄.find? (fun g => !(g.eval fun a => decide (a ∈ X))) with
    | none =>
      .inr
        { val := fun a => decide (a ∈ X)
          sat := fun g hg' => by
            have h := List.find?_eq_none.mp hg g hg'
            cases he : g.eval fun a => decide (a ∈ X)
            · exact absurd (by rw [he]; rfl) h
            · rfl
          node := fun x hx => decide_eq_true hx
          refute := fun q hq' => by
            have h := List.find?_eq_none.mp hq q hq'
            cases he : decide (q ∈ X)
            · rfl
            · exact absurd he h }
    | some g =>
      have hg𝔄 : g ∈ 𝔄 := List.mem_of_find?_eq_some hg
      have hviol : g.eval (fun a => decide (a ∈ X)) = false := by
        have h := List.find?_some hg
        cases he : g.eval fun a => decide (a ∈ X)
        · rfl
        · rw [he] at h; exact absurd h (by decide)
      have hante : g.ante ⊆ X := fun a ha =>
        of_decide_eq_true (List.all_eq_true.mp (GeoImp.eval_eq_false.mp hviol).1 a ha)
      have hcons : ∀ c ∈ g.cons, c ∉ X := fun c hc hcX =>
        List.any_eq_false.mp (GeoImp.eval_eq_false.mp hviol).2 c hc (decide_eq_true hcX)
      match branches 𝓢 τ 𝔄 Q X g.cons
          (fun c hc => sub c (List.mem_flatMap.mpr ⟨g, hg𝔄, hc⟩) (hcons c hc)) with
      | .inr o => .inr o
      | .inl ds =>
        have hrule : nodeCtx τ 𝔄 X ⊢[𝓢]! ⋀(g.ante.map τ) ➝ ⋁(g.cons.map τ) :=
          FiniteContext.byAxm (List.mem_append_right _ (List.mem_map_of_mem hg𝔄))
        have hant : nodeCtx τ 𝔄 X ⊢[𝓢]! ⋀(g.ante.map τ) :=
          Conj₂_intro _ fun _ hφ =>
            FiniteContext.byAxm (List.mem_append_left _ (List.map_subset τ hante hφ))
        .inl (left_Disj'_intro g.cons τ ds ⨀ (hrule ⨀ hant))

/-- The ramification tree below the node `X`, by recursion on a bound `n` for `gap 𝔄 X`. -/
def ramify (τ : β → F) (𝔄 : List (GeoImp β)) (Q : List β) :
    (n : ℕ) → (X : List β) → gap 𝔄 X ≤ n → Outcome 𝓢 τ 𝔄 Q X
  | 0, X, h => ramifyStep 𝓢 τ 𝔄 Q X fun _ hc hcX =>
    absurd (Nat.lt_of_lt_of_le (gap_cons_lt hc hcX) h) (Nat.not_lt_zero _)
  | n + 1, X, h => ramifyStep 𝓢 τ 𝔄 Q X fun c hc hcX =>
    ramify τ 𝔄 Q n (c :: X) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (gap_cons_lt hc hcX) h))

/-- Replace the atoms of the root node by their conjunction. -/
def rootCut (τ : β → F) (𝔄 : List (GeoImp β)) (G : GeoImp β)
    (d : nodeCtx τ 𝔄 G.ante ⊢[𝓢]! ⋁(G.cons.map τ)) :
    (⋀(G.ante.map τ) :: 𝔄.map (GeoImp.toFormula τ)) ⊢[𝓢]! ⋁(G.cons.map τ) :=
  (FiniteContext.of d : _ ⊢[𝓢]! ⋀(nodeCtx τ 𝔄 G.ante) ➝ _) ⨀
    Conj₂_intro _ fun ψ hψ =>
      if h𝔄 : ψ ∈ 𝔄.map (GeoImp.toFormula τ) then
        FiniteContext.byAxm (List.mem_cons_of_mem _ h𝔄)
      else
        FiniteContext.of (left_Conj₂_intro ((List.mem_append.mp hψ).resolve_right h𝔄)) ⨀
          FiniteContext.byAxm List.mem_cons_self

/-- The ramification tree for `G` over `𝔄`: an intuitionistic derivation of `G` from the
assumptions `𝔄`, or an open end node, which is a classical countermodel. -/
def ramifyRoot (τ : β → F) (𝔄 : List (GeoImp β)) (G : GeoImp β) :
    (𝔄.map (GeoImp.toFormula τ) ⊢[𝓢]! G.toFormula τ) ⊕ OpenNode 𝔄 G.cons G.ante :=
  match ramify 𝓢 τ 𝔄 G.cons (gap 𝔄 G.ante) G.ante (Nat.le_refl _) with
  | .inl d => .inl (FiniteContext.deduct (rootCut 𝓢 τ 𝔄 G d))
  | .inr o => .inr o

omit [DecidableEq β] in
/-- An open end node refutes the goal classically. -/
theorem OpenNode.eval_eq_false {𝔄 : List (GeoImp β)} {G : GeoImp β}
    (o : OpenNode 𝔄 G.cons G.ante) : G.eval o.val = false :=
  GeoImp.eval_eq_false.mpr
    ⟨List.all_eq_true.mpr o.node,
      List.any_eq_false.mpr fun q hq h => absurd (o.refute q hq ▸ h) (by decide)⟩

/-- **Gödel's Theorem 62**, in any Foundation entailment system with the intuitionistic
axioms, for substitution instances: if the geometric implication `G` follows by truth tables
from the geometric implications `𝔄`, then for every reading `τ` of the atoms `G` is derivable
from the assumptions `𝔄`. The derivation is the closed ramification tree. -/
def barr (τ : β → F) (𝔄 : List (GeoImp β)) (G : GeoImp β)
    (h : ∀ v : β → Bool, (∀ g ∈ 𝔄, g.eval v = true) → G.eval v = true) :
    𝔄.map (GeoImp.toFormula τ) ⊢[𝓢]! G.toFormula τ :=
  match ramifyRoot 𝓢 τ 𝔄 G with
  | .inl d => d
  | .inr o => absurd (h o.val o.sat) (by rw [o.eval_eq_false]; decide)

end Ramification

/-! ## Theorem 62 for derivations from assumptions -/

section Derivations

variable {β : Type*} [DecidableEq β]

/-- A derivation of `⋀Γ ➝ φ` gives a derivation of `φ` from the assumptions `Γ`. -/
def IntDeriv.ofConjImp {Γ : List (Propositional.Formula ℕ)} {φ : Propositional.Formula ℕ}
    (d : IntDeriv [] (⋀Γ ➝ φ)) : IntDeriv Γ φ :=
  PropDeriv.mdp (PropDeriv.weaken (List.nil_subset Γ) d)
    (Conj₂_intro (𝓢 := (⟨Γ⟩ : IntH)) Γ fun _ hψ => PropDeriv.hyp hψ)

/-- **Gödel's Theorem 62** as an intuitionistic derivation from assumptions: if `G` follows by
truth tables from `𝔄`, the ramification tree derives `G` from the assumptions `𝔄`, for every
reading `τ` of the atoms as formulas. -/
def theorem62 (τ : β → Propositional.Formula ℕ) (𝔄 : List (GeoImp β)) (G : GeoImp β)
    (h : ∀ v : β → Bool, (∀ g ∈ 𝔄, g.eval v = true) → G.eval v = true) :
    IntDeriv (𝔄.map (GeoImp.toFormula τ)) (G.toFormula τ) :=
  IntDeriv.ofConjImp (barr (⟨[]⟩ : IntH) τ 𝔄 G h)

/-- The ramification tree as a decision procedure: an intuitionistic derivation of `G` from
the assumptions `𝔄`, or a classical countermodel. -/
def decideGeometric (τ : β → Propositional.Formula ℕ) (𝔄 : List (GeoImp β)) (G : GeoImp β) :
    IntDeriv (𝔄.map (GeoImp.toFormula τ)) (G.toFormula τ) ⊕
      {v : β → Bool // (∀ g ∈ 𝔄, g.eval v = true) ∧ G.eval v = false} :=
  match ramifyRoot (⟨[]⟩ : IntH) τ 𝔄 G with
  | .inl d => .inl (IntDeriv.ofConjImp d)
  | .inr o => .inr ⟨o.val, o.sat, o.eval_eq_false⟩

end Derivations

/-! ## Classical derivations, truth tables and Foundation -/

theorem ttVal_conj₂ (v : ℕ → Bool) :
    ∀ l : List (Propositional.Formula ℕ), ttVal v (⋀l) = l.all (ttVal v)
  | [] => rfl
  | [φ] => by simp only [List.conj₂_singleton, List.all_cons, List.all_nil, Bool.and_true]
  | φ :: ψ :: l => by
    rw [List.conj₂_cons_nonempty (List.cons_ne_nil ψ l), ttVal_and, ttVal_conj₂ v (ψ :: l)]
    rfl

theorem ttVal_disj₂ (v : ℕ → Bool) :
    ∀ l : List (Propositional.Formula ℕ), ttVal v (⋁l) = l.any (ttVal v)
  | [] => rfl
  | [φ] => by simp only [List.disj₂_singleton, List.any_cons, List.any_nil, Bool.or_false]
  | φ :: ψ :: l => by
    rw [List.disj₂_cons_nonempty (List.cons_ne_nil ψ l), ttVal_or, ttVal_disj₂ v (ψ :: l)]
    rfl

theorem ttVal_toFormula (v : ℕ → Bool) (g : GeoImp ℕ) :
    ttVal v (g.toFormula .atom) = g.eval v := by
  unfold GeoImp.toFormula GeoImp.eval
  rw [ttVal_imp, ttVal_conj₂, ttVal_disj₂, List.all_map, List.any_map]
  rfl

/-- Truth-table soundness of classical derivations between geometric implications. -/
theorem eval_of_clDeriv {𝔄 : List (GeoImp ℕ)} {G : GeoImp ℕ}
    (d : ClDeriv (𝔄.map (GeoImp.toFormula .atom)) (G.toFormula .atom)) (v : ℕ → Bool)
    (hv : ∀ g ∈ 𝔄, g.eval v = true) : G.eval v = true := by
  rw [← ttVal_toFormula]
  refine d.ttVal_sound v fun γ hγ => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hγ
  rw [ttVal_toFormula]
  exact hv g hg

/-- **Gödel's Theorem 62 as a proof transformation**: a classical derivation of a geometric
implication `G` from geometric implications `𝔄` (over atoms) is turned into an intuitionistic
derivation of `G` from the same assumptions. -/
def theorem62OfClassical (𝔄 : List (GeoImp ℕ)) (G : GeoImp ℕ)
    (d : ClDeriv (𝔄.map (GeoImp.toFormula .atom)) (G.toFormula .atom)) :
    IntDeriv (𝔄.map (GeoImp.toFormula .atom)) (G.toFormula .atom) :=
  theorem62 .atom 𝔄 G (eval_of_clDeriv d)

/-- For geometric implications over atoms, provability of `⋀𝔄 ➝ G` in Foundation's
`Propositional.Int` coincides with truth-table consequence. -/
theorem provable_iff_tautology (𝔄 : List (GeoImp ℕ)) (G : GeoImp ℕ) :
    Propositional.Int ⊢ ⋀(𝔄.map (GeoImp.toFormula .atom)) ➝ G.toFormula .atom ↔
      ∀ v : ℕ → Bool, (∀ g ∈ 𝔄, g.eval v = true) → G.eval v = true := by
  constructor
  · intro h v hv
    obtain ⟨d⟩ := IntDeriv.nonempty_of_provable h
    have hd := d.ttVal_sound v (fun _ h => absurd h List.not_mem_nil)
    rw [ttVal_imp, ttVal_toFormula, ttVal_conj₂, List.all_map] at hd
    have hall : 𝔄.all (ttVal v ∘ GeoImp.toFormula .atom) = true :=
      List.all_eq_true.mpr fun g hg => by
        simp only [Function.comp_apply, ttVal_toFormula]
        exact hv g hg
    rw [hall] at hd
    exact hd
  · intro h
    exact ⟨barr Propositional.Int .atom 𝔄 G h⟩

/-! ## Examples -/

section Examples

/-- Positive example: `p₀ ⊃ p₁ ∨ p₂`, `p₁ ⊃ p₃` and `p₂ ⊃ p₃`. -/
def exampleAxioms : List (GeoImp ℕ) := [⟨[0], [1, 2]⟩, ⟨[1], [3]⟩, ⟨[2], [3]⟩]

/-- The goal `p₀ ⊃ p₃`. -/
def exampleGoal : GeoImp ℕ := ⟨[0], [3]⟩

theorem exampleGoal_follows : followsTT exampleAxioms exampleGoal = true := by decide

/-- The intuitionistic derivation of `p₀ ⊃ p₃` from the three assumptions, built by the
ramification tree. -/
def exampleDerivation :
    IntDeriv (exampleAxioms.map (GeoImp.toFormula .atom)) (exampleGoal.toFormula .atom) :=
  theorem62 .atom exampleAxioms exampleGoal
    ((followsTT_iff exampleAxioms exampleGoal).mp exampleGoal_follows)

example : Propositional.Int ⊢
    ((#0 ➝ #1 ⋎ #2) ⋏ ((#1 ➝ #3) ⋏ (#2 ➝ #3))) ➝ (#0 ➝ #3) :=
  (provable_iff_tautology exampleAxioms exampleGoal).mpr
    ((followsTT_iff exampleAxioms exampleGoal).mp exampleGoal_follows)

/-- A non-consequence: `p₀ ⊃ p₁` does not follow from `p₀ ⊃ p₁ ∨ p₂`; the ramification tree
has an open end node. -/
theorem example_not_follows : followsTT [⟨[0], [1, 2]⟩] ⟨[0], [1]⟩ = false := by decide

/-! ### The excluded middle

The law `p ∨ ¬p` has a classical derivation and is a truth-table tautology, but it has no
intuitionistic derivation; so the transformation of classical into intuitionistic derivations
does not extend beyond geometric implications. The proof of underivability uses the
three-element Heyting chain `0 < 1 < 2`, for which intuitionistic derivations are sound. -/

/-- Heyting implication on the chain `0 < 1 < 2`. -/
def h3Imp (a b : Fin 3) : Fin 3 := if a ≤ b then 2 else b

/-- Value of a formula in the three-element Heyting chain. -/
def h3Val (v : ℕ → Fin 3) : Propositional.Formula ℕ → Fin 3
  | .atom a => v a
  | .falsum => 0
  | .and φ ψ => min (h3Val v φ) (h3Val v ψ)
  | .or φ ψ => max (h3Val v φ) (h3Val v ψ)
  | .imp φ ψ => h3Imp (h3Val v φ) (h3Val v ψ)

/-- Soundness of intuitionistic derivations for the three-element Heyting chain. -/
theorem IntDeriv.h3Val_sound {Γ : List (Propositional.Formula ℕ)} (v : ℕ → Fin 3)
    (hΓ : ∀ γ ∈ Γ, h3Val v γ = 2) :
    {φ : Propositional.Formula ℕ} → IntDeriv Γ φ → h3Val v φ = 2
  | _, .hyp h => hΓ _ h
  | _, .efq φ => by
    change h3Imp 0 (h3Val v φ) = 2
    generalize h3Val v φ = a
    revert a; decide
  | _, .lem _ h => nomatch h
  | _, .implyK φ ψ => by
    change h3Imp (h3Val v φ) (h3Imp (h3Val v ψ) (h3Val v φ)) = 2
    generalize h3Val v φ = a; generalize h3Val v ψ = b
    revert a b; decide
  | _, .implyS φ ψ χ => by
    change h3Imp (h3Imp (h3Val v φ) (h3Imp (h3Val v ψ) (h3Val v χ)))
      (h3Imp (h3Imp (h3Val v φ) (h3Val v ψ)) (h3Imp (h3Val v φ) (h3Val v χ))) = 2
    generalize h3Val v φ = a; generalize h3Val v ψ = b; generalize h3Val v χ = c
    revert a b c; decide
  | _, .andElimL φ ψ => by
    change h3Imp (min (h3Val v φ) (h3Val v ψ)) (h3Val v φ) = 2
    generalize h3Val v φ = a; generalize h3Val v ψ = b
    revert a b; decide
  | _, .andElimR φ ψ => by
    change h3Imp (min (h3Val v φ) (h3Val v ψ)) (h3Val v ψ) = 2
    generalize h3Val v φ = a; generalize h3Val v ψ = b
    revert a b; decide
  | _, .andIntro φ ψ => by
    change h3Imp (h3Val v φ) (h3Imp (h3Val v ψ) (min (h3Val v φ) (h3Val v ψ))) = 2
    generalize h3Val v φ = a; generalize h3Val v ψ = b
    revert a b; decide
  | _, .orIntroL φ ψ => by
    change h3Imp (h3Val v φ) (max (h3Val v φ) (h3Val v ψ)) = 2
    generalize h3Val v φ = a; generalize h3Val v ψ = b
    revert a b; decide
  | _, .orIntroR φ ψ => by
    change h3Imp (h3Val v ψ) (max (h3Val v φ) (h3Val v ψ)) = 2
    generalize h3Val v φ = a; generalize h3Val v ψ = b
    revert a b; decide
  | _, .orElim φ ψ χ => by
    change h3Imp (h3Imp (h3Val v φ) (h3Val v χ)) (h3Imp (h3Imp (h3Val v ψ) (h3Val v χ))
      (h3Imp (max (h3Val v φ) (h3Val v ψ)) (h3Val v χ))) = 2
    generalize h3Val v φ = a; generalize h3Val v ψ = b; generalize h3Val v χ = c
    revert a b c; decide
  | _, .mdp (φ := φ) (ψ := ψ) d₁ d₂ => by
    have h₁ : h3Imp (h3Val v φ) (h3Val v ψ) = 2 := IntDeriv.h3Val_sound v hΓ d₁
    have h₂ : h3Val v φ = 2 := IntDeriv.h3Val_sound v hΓ d₂
    rw [h₂] at h₁
    revert h₁
    generalize h3Val v ψ = b
    revert b; decide

/-- The excluded middle `p₀ ∨ ¬p₀`. -/
abbrev lem₀ : Propositional.Formula ℕ := #0 ⋎ ∼#0

theorem lem₀_tautology (v : ℕ → Bool) : ttVal v lem₀ = true := by
  simp only [ttVal_or, ttVal_neg, ttVal_atom]
  cases v 0 <;> rfl

/-- The excluded middle has a classical derivation. -/
def lem₀ClDeriv : ClDeriv [] lem₀ := PropDeriv.lem _ rfl

theorem not_nonempty_intDeriv_lem₀ : ¬ Nonempty (IntDeriv [] lem₀) := fun ⟨d⟩ =>
  absurd (d.h3Val_sound (fun _ => 1) fun _ h => absurd h List.not_mem_nil) (by decide)

/-- The excluded middle is not a theorem of Foundation's `Propositional.Int`. -/
theorem not_provable_lem₀ : ¬ Propositional.Int ⊢ lem₀ := fun h =>
  not_nonempty_intDeriv_lem₀ (IntDeriv.nonempty_of_provable h)

/-- The excluded middle is not intuitionistically equivalent to any geometric implication:
such an implication would be a truth-table tautology, hence intuitionistically derivable by
Theorem 62, and then so would be the excluded middle. -/
theorem lem₀_not_equiv_geometric (G : GeoImp ℕ) :
    ¬ (Nonempty (IntDeriv [] (G.toFormula .atom ➝ lem₀)) ∧
      Nonempty (IntDeriv [] (lem₀ ➝ G.toFormula .atom))) := by
  rintro ⟨⟨d₁⟩, ⟨d₂⟩⟩
  have hG : ∀ v : ℕ → Bool, (∀ g ∈ ([] : List (GeoImp ℕ)), g.eval v = true) →
      G.eval v = true := fun v _ => by
    have h := d₂.ttVal_sound v fun _ h => absurd h List.not_mem_nil
    rw [ttVal_imp, lem₀_tautology, ttVal_toFormula] at h
    exact h
  exact not_nonempty_intDeriv_lem₀ ⟨PropDeriv.mdp d₁ (theorem62 .atom [] G hG)⟩

end Examples

end Mettapedia.Logic.ModalCompanion
