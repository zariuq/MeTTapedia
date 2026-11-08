import Mathlib.Data.Finset.Card

/-!
# The provenance forest: support recurrences of a ground derivation forest

A ground forest has items, background items (derivable at no cost), and hypothesis
edges `(head, label, body)`.  A derivation tree of an item has a support, the set of
labels it uses, and a size, the number of hypothesis edges in it counted with
multiplicity.  In meta-interpretive learning, items are first-order goals, labels are
metarule instances, and a derivation tree is a refutation, so the supports of the
example's trees are the learner's sub-hypotheses.

* **Without reuse of hypothesis clauses** a clause limit bounds a refutation's steps.
  The dynamic programme computing, for every size `n` and item `i`, the family of
  supports of the derivations of `i` of size exactly `n` is characterised by its
  recurrences (`isForest_iff_der`, `derFamily_isForest`), and restricting body layouts
  to reachable sizes loses nothing (`bodyF_cons_reachable`).
* **With reuse** a clause limit `K` bounds the distinct labels of a refutation.  The
  least fixpoint of the recurrence without sizes, every union kept within `K`
  (`BFam`), is exactly the set of supports of derivation trees with at most `K` labels
  (`bfam_iff`): a subtree's support is part of its tree's, so the bound prunes no tree
  whose support stays within it.
* **The kernel's rounds** (`Round`): round `n + 1` adds what each edge makes from the
  supports its body holds after round `n`.  They reach exactly the bounded fixpoint
  (`bfam_iff_round`), so exactly the supports of trees with at most `K` labels
  (`round_iff_derR`).
-/

namespace Mettapedia.Logic.MetaInterpretiveLearning.ProvenanceForest

variable {Item Lab : Type} [DecidableEq Lab]

/-! ## Without reuse: supports by exact size -/

mutual
/-- `Der bk E i n S`: item `i` has a derivation using exactly `n` hypothesis edges,
counted with multiplicity, whose labels form `S`. -/
inductive Der (bk : Item → Prop) (E : List (Item × Lab × List Item)) :
    Item → ℕ → Finset Lab → Prop
  | leaf {i : Item} : bk i → Der bk E i 0 ∅
  | node {i : Item} {l : Lab} {body : List Item} {n : ℕ} {S : Finset Lab} :
      (i, l, body) ∈ E → DerBody bk E body n S → Der bk E i (n + 1) (insert l S)

/-- `DerBody bk E body n S`: every item of `body` has a derivation; the sizes add up to
`n` and the supports' union is `S`. -/
inductive DerBody (bk : Item → Prop) (E : List (Item × Lab × List Item)) :
    List Item → ℕ → Finset Lab → Prop
  | nil : DerBody bk E [] 0 ∅
  | cons {j : Item} {js : List Item} {n₁ n₂ : ℕ} {S₁ S₂ : Finset Lab} :
      Der bk E j n₁ S₁ → DerBody bk E js n₂ S₂ → DerBody bk E (j :: js) (n₁ + n₂) (S₁ ∪ S₂)
end

/-- The body recurrence of the dynamic programme, for a family `F`. -/
def BodyF (F : ℕ → Item → Set (Finset Lab)) : ℕ → List Item → Finset Lab → Prop
  | n, [], S => n = 0 ∧ S = ∅
  | n, j :: js, S =>
      ∃ n₁ n₂ S₁ S₂, n₁ + n₂ = n ∧ S₁ ∈ F n₁ j ∧ BodyF F n₂ js S₂ ∧ S = S₁ ∪ S₂

/-- `F` satisfies the recurrences of the dynamic programme. -/
structure IsForest (bk : Item → Prop) (E : List (Item × Lab × List Item))
    (F : ℕ → Item → Set (Finset Lab)) : Prop where
  zero : ∀ i S, S ∈ F 0 i ↔ bk i ∧ S = ∅
  succ : ∀ n i S, S ∈ F (n + 1) i ↔
    ∃ l body S', (i, l, body) ∈ E ∧ BodyF F n body S' ∧ S = insert l S'

variable {bk : Item → Prop} {E : List (Item × Lab × List Item)}

theorem der_zero_iff {i : Item} {S : Finset Lab} : Der bk E i 0 S ↔ bk i ∧ S = ∅ := by
  constructor
  · intro h
    cases h with
    | leaf hb => exact ⟨hb, rfl⟩
  · rintro ⟨hb, rfl⟩
    exact Der.leaf hb

theorem der_succ_iff {i : Item} {n : ℕ} {S : Finset Lab} :
    Der bk E i (n + 1) S ↔
      ∃ l body S', (i, l, body) ∈ E ∧ DerBody bk E body n S' ∧ S = insert l S' := by
  constructor
  · intro h
    cases h with
    | node he hb => exact ⟨_, _, _, he, hb, rfl⟩
  · rintro ⟨l, body, S', he, hb, rfl⟩
    exact Der.node he hb

theorem derBody_nil_iff {n : ℕ} {S : Finset Lab} :
    DerBody bk E [] n S ↔ n = 0 ∧ S = ∅ := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact DerBody.nil

theorem derBody_cons_iff {j : Item} {js : List Item} {n : ℕ} {S : Finset Lab} :
    DerBody bk E (j :: js) n S ↔
      ∃ n₁ n₂ S₁ S₂, n₁ + n₂ = n ∧ Der bk E j n₁ S₁ ∧ DerBody bk E js n₂ S₂ ∧
        S = S₁ ∪ S₂ := by
  constructor
  · intro h
    cases h with
    | cons hj hjs => exact ⟨_, _, _, _, rfl, hj, hjs, rfl⟩
  · rintro ⟨n₁, n₂, S₁, S₂, rfl, hj, hjs, rfl⟩
    exact DerBody.cons hj hjs

/-- If `F` agrees with derivations up to size `n`, its body recurrence agrees with
body derivations up to size `n`. -/
theorem bodyF_iff_of_le (F : ℕ → Item → Set (Finset Lab)) (n : ℕ)
    (ih : ∀ m ≤ n, ∀ i S, S ∈ F m i ↔ Der bk E i m S) :
    ∀ (body : List Item) (m : ℕ) (S : Finset Lab), m ≤ n →
      (BodyF F m body S ↔ DerBody bk E body m S) := by
  intro body
  induction body with
  | nil =>
    intro m S _
    simp only [BodyF]
    exact derBody_nil_iff.symm
  | cons j js ihjs =>
    intro m S hm
    simp only [BodyF]
    rw [derBody_cons_iff]
    constructor
    · rintro ⟨n₁, n₂, S₁, S₂, hsum, h₁, h₂, hS⟩
      refine ⟨n₁, n₂, S₁, S₂, hsum, ?_, ?_, hS⟩
      · exact (ih n₁ (by omega) j S₁).1 h₁
      · exact (ihjs n₂ S₂ (by omega)).1 h₂
    · rintro ⟨n₁, n₂, S₁, S₂, hsum, h₁, h₂, hS⟩
      refine ⟨n₁, n₂, S₁, S₂, hsum, ?_, ?_, hS⟩
      · exact (ih n₁ (by omega) j S₁).2 h₁
      · exact (ihjs n₂ S₂ (by omega)).2 h₂

/-- Uniqueness: every family satisfying the recurrences is the family of supports of
derivation trees, size by size. -/
theorem isForest_iff_der {F : ℕ → Item → Set (Finset Lab)} (hF : IsForest bk E F) :
    ∀ n i S, S ∈ F n i ↔ Der bk E i n S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i S
    cases n with
    | zero =>
      rw [hF.zero, der_zero_iff]
    | succ n =>
      rw [hF.succ, der_succ_iff]
      have hb := bodyF_iff_of_le F n (fun m hm => ih m (by omega))
      constructor
      · rintro ⟨l, body, S', he, hbody, hS⟩
        exact ⟨l, body, S', he, (hb body n S' le_rfl).1 hbody, hS⟩
      · rintro ⟨l, body, S', he, hbody, hS⟩
        exact ⟨l, body, S', he, (hb body n S' le_rfl).2 hbody, hS⟩

/-- The family of supports of derivation trees. -/
def derFamily (bk : Item → Prop) (E : List (Item × Lab × List Item)) :
    ℕ → Item → Set (Finset Lab) :=
  fun n i => {S | Der bk E i n S}

/-- Existence: the family of supports of derivation trees satisfies the recurrences. -/
theorem derFamily_isForest : IsForest bk E (derFamily bk E) := by
  refine ⟨fun i S => der_zero_iff, fun n i S => ?_⟩
  have hb := bodyF_iff_of_le (derFamily bk E) n (fun m _ i S => Iff.rfl)
  show Der bk E i (n + 1) S ↔ _
  rw [der_succ_iff]
  constructor
  · rintro ⟨l, body, S', he, hbody, hS⟩
    exact ⟨l, body, S', he, (hb body n S' le_rfl).2 hbody, hS⟩
  · rintro ⟨l, body, S', he, hbody, hS⟩
    exact ⟨l, body, S', he, (hb body n S' le_rfl).1 hbody, hS⟩

/-- Pruning by the Boolean pass loses nothing: a support of size `n₁` exists for an item
exactly when that item is reachable at size `n₁`, so restricting body layouts to
reachable sizes keeps every solution of the body recurrence. -/
theorem bodyF_cons_reachable {F : ℕ → Item → Set (Finset Lab)} (hF : IsForest bk E F)
    {j : Item} {js : List Item} {n : ℕ} {S : Finset Lab} :
    BodyF F n (j :: js) S ↔
      ∃ n₁ n₂ S₁ S₂, n₁ + n₂ = n ∧ (∃ T, Der bk E j n₁ T) ∧ S₁ ∈ F n₁ j ∧
        BodyF F n₂ js S₂ ∧ S = S₁ ∪ S₂ := by
  simp only [BodyF]
  constructor
  · rintro ⟨n₁, n₂, S₁, S₂, hs, h₁, h₂, hS⟩
    exact ⟨n₁, n₂, S₁, S₂, hs, ⟨S₁, (isForest_iff_der hF n₁ j S₁).1 h₁⟩, h₁, h₂, hS⟩
  · rintro ⟨n₁, n₂, S₁, S₂, hs, _, h₁, h₂, hS⟩
    exact ⟨n₁, n₂, S₁, S₂, hs, h₁, h₂, hS⟩

/-! ## With reuse: supports bounded by a clause limit -/

mutual
/-- `DerR bk E i S`: item `i` has a derivation tree, of any size, whose labels form
`S`; a label may be used any number of times. -/
inductive DerR (bk : Item → Prop) (E : List (Item × Lab × List Item)) :
    Item → Finset Lab → Prop
  | leaf {i : Item} : bk i → DerR bk E i ∅
  | node {i : Item} {l : Lab} {body : List Item} {S : Finset Lab} :
      (i, l, body) ∈ E → DerRBody bk E body S → DerR bk E i (insert l S)

/-- `DerRBody bk E body S`: every item of `body` has a derivation tree, and the
supports' union is `S`. -/
inductive DerRBody (bk : Item → Prop) (E : List (Item × Lab × List Item)) :
    List Item → Finset Lab → Prop
  | nil : DerRBody bk E [] ∅
  | cons {j : Item} {js : List Item} {S₁ S₂ : Finset Lab} :
      DerR bk E j S₁ → DerRBody bk E js S₂ → DerRBody bk E (j :: js) (S₁ ∪ S₂)
end

mutual
/-- `BFam bk E K i S`: the least fixpoint the forest computes with reuse, every
support and every partial union of a body kept within `K` labels. -/
inductive BFam (bk : Item → Prop) (E : List (Item × Lab × List Item)) (K : ℕ) :
    Item → Finset Lab → Prop
  | leaf {i : Item} : bk i → BFam bk E K i ∅
  | node {i : Item} {l : Lab} {body : List Item} {S : Finset Lab} :
      (i, l, body) ∈ E → BBody bk E K body S → (insert l S).card ≤ K →
        BFam bk E K i (insert l S)

/-- `BBody bk E K body S`: the body's part of `BFam`, every partial union within `K`. -/
inductive BBody (bk : Item → Prop) (E : List (Item × Lab × List Item)) (K : ℕ) :
    List Item → Finset Lab → Prop
  | nil : BBody bk E K [] ∅
  | cons {j : Item} {js : List Item} {S₁ S₂ : Finset Lab} :
      BFam bk E K j S₁ → BBody bk E K js S₂ → (S₁ ∪ S₂).card ≤ K →
        BBody bk E K (j :: js) (S₁ ∪ S₂)
end

mutual
/-- Everything the bounded fixpoint holds is the support of a derivation tree with at
most `K` labels. -/
theorem BFam.sound {K : ℕ} {i : Item} {S : Finset Lab} :
    BFam bk E K i S → DerR bk E i S ∧ S.card ≤ K
  | .leaf hb => ⟨.leaf hb, by simp⟩
  | .node he hb hc => ⟨.node he (BBody.sound hb).1, hc⟩

theorem BBody.sound {K : ℕ} {body : List Item} {S : Finset Lab} :
    BBody bk E K body S → DerRBody bk E body S ∧ S.card ≤ K
  | .nil => ⟨.nil, by simp⟩
  | .cons hj hjs hc => ⟨.cons (BFam.sound hj).1 (BBody.sound hjs).1, hc⟩
end

mutual
/-- Every derivation tree with at most `K` labels has its support in the bounded
fixpoint: its subtrees' supports are parts of its own, so they stay within `K`. -/
theorem DerR.bounded {K : ℕ} {i : Item} {S : Finset Lab} :
    DerR bk E i S → S.card ≤ K → BFam bk E K i S
  | .leaf hb, _ => .leaf hb
  | .node (S := S') he hb, hc =>
      .node he (DerRBody.bounded hb
        (le_trans (Finset.card_le_card (Finset.subset_insert _ S')) hc)) hc

theorem DerRBody.bounded {K : ℕ} {body : List Item} {S : Finset Lab} :
    DerRBody bk E body S → S.card ≤ K → BBody bk E K body S
  | .nil, _ => .nil
  | .cons (S₁ := S₁) (S₂ := S₂) hj hjs, hc =>
      .cons (DerR.bounded hj (le_trans (Finset.card_le_card Finset.subset_union_left) hc))
        (DerRBody.bounded hjs (le_trans (Finset.card_le_card Finset.subset_union_right) hc))
        hc
end

/-- With reuse, the forest's bounded least fixpoint is exactly the set of supports of
derivation trees with at most `K` labels. -/
theorem bfam_iff {K : ℕ} {i : Item} {S : Finset Lab} :
    BFam bk E K i S ↔ DerR bk E i S ∧ S.card ≤ K :=
  ⟨BFam.sound, fun h => DerR.bounded h.1 h.2⟩

/-- A derivation tree of an item that is not background holds the label of its root
edge, when the item has one edge. -/
theorem DerR.label_mem {i : Item} {S : Finset Lab} :
    DerR bk E i S → ∀ l body, (i, l, body) ∈ E → (∀ l' body', (i, l', body') ∈ E → l' = l) →
      ¬ bk i → l ∈ S
  | .leaf hb, _, _, _, _, hnb => absurd hb hnb
  | .node (l := l₀) he _, l, _, _, huniq, _ => by
      have : l₀ = l := huniq _ _ he
      subst this
      exact Finset.mem_insert_self _ _

/-- Each item of a body has a derivation tree whose support is part of the body's. -/
theorem DerRBody.subset {body : List Item} {S : Finset Lab} :
    DerRBody bk E body S → ∀ j ∈ body, ∃ T, DerR bk E j T ∧ T ⊆ S
  | .nil, _, hj => absurd hj (List.not_mem_nil)
  | .cons (S₁ := S₁) (S₂ := S₂) hj hjs, j, hmem => by
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact ⟨S₁, hj, Finset.subset_union_left⟩
      · obtain ⟨T, hT, hsub⟩ := DerRBody.subset hjs j hmem
        exact ⟨T, hT, hsub.trans Finset.subset_union_right⟩

/-! ## Rounds: how the kernel reaches the bounded fixpoint

The provenance kernel computes the bounded fixpoint in rounds.  Round `0` holds the
background items' empty supports; round `n + 1` adds what each edge makes from the
supports its body's items hold after round `n`, every union kept within `K`.  Every
support of the fixpoint appears in some round, and no round holds anything else. -/

/-- The supports a body takes from a family `F`: one support per item, their union,
every partial union within `K`. -/
def BodyOf (K : ℕ) (F : Item → Finset Lab → Prop) : List Item → Finset Lab → Prop
  | [], S => S = ∅
  | j :: js, S => ∃ S₁ S₂, F j S₁ ∧ BodyOf K F js S₂ ∧ S = S₁ ∪ S₂ ∧ S.card ≤ K

/-- Round `n` of the kernel. -/
def Round (bk : Item → Prop) (E : List (Item × Lab × List Item)) (K : ℕ) :
    ℕ → Item → Finset Lab → Prop
  | 0, i, S => bk i ∧ S = ∅
  | n + 1, i, S => Round bk E K n i S ∨
      ∃ l body S', (i, l, body) ∈ E ∧ BodyOf K (fun j T => Round bk E K n j T) body S' ∧
        S = insert l S' ∧ S.card ≤ K

theorem bodyOf_mono {K : ℕ} {F G : Item → Finset Lab → Prop}
    (h : ∀ i S, F i S → G i S) : ∀ {body : List Item} {S : Finset Lab},
    BodyOf K F body S → BodyOf K G body S
  | [], _, hb => hb
  | _ :: _, _, ⟨S₁, S₂, h₁, h₂, hS, hc⟩ => ⟨S₁, S₂, h _ _ h₁, bodyOf_mono h h₂, hS, hc⟩

/-- A later round holds everything an earlier one does. -/
theorem round_mono {K n m : ℕ} (hnm : n ≤ m) {i : Item} {S : Finset Lab}
    (h : Round bk E K n i S) : Round bk E K m i S := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem bodyOf_bbody {K : ℕ} {F : Item → Finset Lab → Prop}
    (hF : ∀ i S, F i S → BFam bk E K i S) : ∀ {body : List Item} {S : Finset Lab},
    BodyOf K F body S → BBody bk E K body S
  | [], _, hS => by subst hS; exact .nil
  | _ :: _, _, ⟨_, _, h₁, h₂, hS, hc⟩ => by
      subst hS; exact .cons (hF _ _ h₁) (bodyOf_bbody hF h₂) hc

/-- Every support a round holds is in the bounded fixpoint. -/
theorem round_sound {K : ℕ} : ∀ (n : ℕ) {i : Item} {S : Finset Lab},
    Round bk E K n i S → BFam bk E K i S
  | 0, _, _, ⟨hb, hS⟩ => by subst hS; exact .leaf hb
  | n + 1, _, _, Or.inl h => round_sound n h
  | n + 1, _, _, Or.inr ⟨_, _, _, he, hb, hS, hc⟩ => by
      subst hS; exact .node he (bodyOf_bbody (fun _ _ h => round_sound n h) hb) hc

mutual
/-- Every support of the bounded fixpoint appears in some round. -/
theorem BFam.round {K : ℕ} {i : Item} {S : Finset Lab} :
    BFam bk E K i S → ∃ n, Round bk E K n i S
  | .leaf hb => ⟨0, hb, rfl⟩
  | .node (l := l) (body := body) (S := S') he hb hc =>
      match BBody.round hb with
      | ⟨n, hn⟩ => ⟨n + 1, Or.inr ⟨l, body, S', he, hn, rfl, hc⟩⟩

theorem BBody.round {K : ℕ} {body : List Item} {S : Finset Lab} :
    BBody bk E K body S → ∃ n, BodyOf K (fun j T => Round bk E K n j T) body S
  | .nil => ⟨0, rfl⟩
  | .cons (S₁ := S₁) (S₂ := S₂) hj hjs hc =>
      match BFam.round hj, BBody.round hjs with
      | ⟨n₁, h₁⟩, ⟨n₂, h₂⟩ =>
          ⟨max n₁ n₂, S₁, S₂, round_mono (le_max_left _ _) h₁,
            bodyOf_mono (fun _ _ h => round_mono (le_max_right _ _) h) h₂, rfl, hc⟩
end

/-- The kernel's rounds reach exactly the bounded least fixpoint. -/
theorem bfam_iff_round {K : ℕ} {i : Item} {S : Finset Lab} :
    BFam bk E K i S ↔ ∃ n, Round bk E K n i S :=
  ⟨BFam.round, fun ⟨n, h⟩ => round_sound n h⟩

/-- So the rounds compute exactly the supports of derivation trees with at most `K`
labels. -/
theorem round_iff_derR {K : ℕ} {i : Item} {S : Finset Lab} :
    (∃ n, Round bk E K n i S) ↔ DerR bk E i S ∧ S.card ≤ K :=
  bfam_iff_round.symm.trans bfam_iff

/-! ## Examples

Two background items `a`, `b`; edge `c1 : s ← a, b`; edge `c2 : t ← s, s`.
The tree for `t` uses `c1` twice: size 3 (with multiplicity), support `{c1, c2}`. -/

section Examples

inductive It | a | b | s | t
  deriving DecidableEq

def exBk : It → Prop
  | .a => True
  | .b => True
  | _ => False

def exE : List (It × ℕ × List It) := [(.s, 1, [.a, .b]), (.t, 2, [.s, .s])]

/-- Positive: `s` has a derivation of size 1 with support `{1}`. -/
theorem ex_s : Der exBk exE .s 1 {1} := by
  have h : Der exBk exE .s (0 + 0 + 1) (insert 1 (∅ ∪ (∅ ∪ ∅))) :=
    Der.node (i := It.s) (l := 1) (body := [It.a, It.b]) (by simp [exE])
      (DerBody.cons (Der.leaf (i := It.a) trivial)
        (DerBody.cons (Der.leaf (i := It.b) trivial) DerBody.nil))
  have e : (insert 1 (∅ ∪ (∅ ∪ ∅)) : Finset ℕ) = {1} := by decide
  rw [e] at h
  exact h

/-- Positive: `t` has a derivation of size 3 (c1 counted twice) with support `{2, 1}`. -/
theorem ex_t : Der exBk exE .t 3 {2, 1} := by
  have h : Der exBk exE .t (1 + (1 + 0) + 1) (insert 2 ({1} ∪ ({1} ∪ ∅))) :=
    Der.node (i := It.t) (l := 2) (body := [It.s, It.s]) (by simp [exE])
      (DerBody.cons ex_s (DerBody.cons ex_s DerBody.nil))
  have e : (insert 2 ({1} ∪ ({1} ∪ ∅)) : Finset ℕ) = {2, 1} := by decide
  rw [e] at h
  exact h

/-- Negative: `s` has no derivation of size 0 (it is not background). -/
example (S : Finset ℕ) : ¬ Der exBk exE .s 0 S := by
  rw [der_zero_iff]
  simp [exBk]

/-- Negative: `t` has no derivation of size 2: its only edge needs two derivations of
`s`, each of size at least 1, plus itself. -/
example (S : Finset ℕ) : ¬ Der exBk exE .t 2 S := by
  intro h
  rw [der_succ_iff] at h
  obtain ⟨l, body, S', he, hb, _⟩ := h
  simp [exE] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [derBody_cons_iff] at hb
  obtain ⟨n₁, n₂, S₁, S₂, hsum, h₁, h₂, _⟩ := hb
  rw [derBody_cons_iff] at h₂
  obtain ⟨m₁, m₂, T₁, T₂, hsum2, h₃, h₄, _⟩ := h₂
  have hpos : ∀ n T, Der exBk exE .s n T → 1 ≤ n := by
    intro n T hd
    cases n with
    | zero => rw [der_zero_iff] at hd; simp [exBk] at hd
    | succ n => omega
  have := hpos _ _ h₁
  have := hpos _ _ h₃
  omega

/-- Positive, with reuse: `t`'s tree uses `c1` twice and has two labels, so it is in the
bounded fixpoint at clause limit 2. -/
example : BFam exBk exE 2 .t {2, 1} := by
  have hs : DerR exBk exE .s {1} := by
    have h : DerR exBk exE .s (insert 1 (∅ ∪ (∅ ∪ ∅))) :=
      DerR.node (i := It.s) (l := 1) (body := [It.a, It.b]) (by simp [exE])
        (DerRBody.cons (DerR.leaf (i := It.a) trivial)
          (DerRBody.cons (DerR.leaf (i := It.b) trivial) DerRBody.nil))
    have e : (insert 1 (∅ ∪ (∅ ∪ ∅)) : Finset ℕ) = {1} := by decide
    rw [e] at h
    exact h
  have ht : DerR exBk exE .t (insert 2 ({1} ∪ ({1} ∪ ∅))) :=
    DerR.node (i := It.t) (l := 2) (body := [It.s, It.s]) (by simp [exE])
      (DerRBody.cons hs (DerRBody.cons hs DerRBody.nil))
  have e : (insert 2 ({1} ∪ ({1} ∪ ∅)) : Finset ℕ) = {2, 1} := by decide
  rw [e] at ht
  exact bfam_iff.2 ⟨ht, by decide⟩

/-- Negative, with reuse: at clause limit 1 `t` has no support, since every tree for `t`
uses both `c2` and `c1`. -/
example (S : Finset ℕ) : ¬ BFam exBk exE 1 .t S := by
  intro h
  obtain ⟨ht, hcard⟩ := bfam_iff.1 h
  cases ht with
  | leaf hb => simp [exBk] at hb
  | node he hb =>
    rename_i l body S'
    simp [exE] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨T, hT, hsub⟩ := DerRBody.subset hb .s (by simp)
    have h1 : 1 ∈ T := DerR.label_mem hT 1 [.a, .b] (by simp [exE])
      (by intro l' body' hm; simp [exE] at hm; exact hm.1) (by simp [exBk])
    have h1S : (1 : ℕ) ∈ insert 2 S' := Finset.mem_insert_of_mem (hsub h1)
    have : ({2, 1} : Finset ℕ) ⊆ insert 2 S' := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact h1S
    have hle := Finset.card_le_card this
    have hc : ({2, 1} : Finset ℕ).card = 2 := by decide
    omega

/-- Positive, the rounds: `s` gets `{1}` in round `1` and `t` gets `{2, 1}` in round `2`. -/
example : Round exBk exE 2 2 .t {2, 1} := by
  have hs : Round exBk exE 2 1 .s {1} :=
    Or.inr ⟨1, [.a, .b], ∅, by simp [exE],
      ⟨∅, ∅, ⟨by simp [exBk], rfl⟩, ⟨∅, ∅, ⟨by simp [exBk], rfl⟩, rfl, by simp, by simp⟩,
        by simp, by simp⟩,
      by simp, by decide⟩
  exact Or.inr ⟨2, [.s, .s], {1}, by simp [exE],
    ⟨{1}, {1}, hs, ⟨{1}, ∅, hs, rfl, by simp, by decide⟩, by simp, by decide⟩,
    by decide, by decide⟩

/-- Negative, the rounds: at clause limit 1 no round gives `t` a support. -/
example (n : ℕ) (S : Finset ℕ) : ¬ Round exBk exE 1 n .t S := by
  intro h
  obtain ⟨ht, hcard⟩ := round_iff_derR.1 ⟨n, h⟩
  cases ht with
  | leaf hb => simp [exBk] at hb
  | node he hb =>
    rename_i l body S'
    simp [exE] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨T, hT, hsub⟩ := DerRBody.subset hb .s (by simp)
    have h1 : 1 ∈ T := DerR.label_mem hT 1 [.a, .b] (by simp [exE])
      (by intro l' body' hm; simp [exE] at hm; exact hm.1) (by simp [exBk])
    have h1S : (1 : ℕ) ∈ insert 2 S' := Finset.mem_insert_of_mem (hsub h1)
    have : ({2, 1} : Finset ℕ) ⊆ insert 2 S' := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact h1S
    have hle := Finset.card_le_card this
    have hc : ({2, 1} : Finset ℕ).card = 2 := by decide
    omega

end Examples

end Mettapedia.Logic.MetaInterpretiveLearning.ProvenanceForest
