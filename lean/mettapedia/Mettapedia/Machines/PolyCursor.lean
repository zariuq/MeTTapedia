import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Cursors as zippers over polynomial trees

One construction, used several times.  A polynomial `Σ a, X ^ (β a)` (positions
`a : α`, directions `β a`) has trees `WType β`.  A *hole* is a position, the
direction of the hole and the subtrees in every other direction: the
derivative of the polynomial.  A *zipper* is a subtree in focus and the stack of
holes above it.  Moving down unplugs a child, moving up plugs it back.

The same zipper, at three polynomials:
* **tries** (positions: an accept flag and the letters that have children):
  the language below the focus is the residual of the root's language by the
  path; a trie with no empty subtrie is canonical (two of them with the same
  language are equal), so with shared nodes set equality is node identity, and
  every choice a cursor makes has a completion below it;
* **cursors over words** (coalgebras `X → Prop × X ^ σ`): the dependent
  product of two cursors reads the dependent concatenation of their languages,
  and the plain product is the case of constant dependence;
* **version trees** (positions: the edits to the children): a binding store
  with an undo trail is a zipper over its version tree; undo is moving up, and
  restoring after a bind is the identity.

Also here: leapfrog intersection of sorted key lists (each list a cursor with
`seek`), sound and complete; and the condition under which grafting the next
factor only at leaves (as a product zipper over tries does) reads the full
concatenation: the first factor's language is prefix-free, which holds for
prefix-encoded terms.

Main results:
* `up_down`, `down_up`, `tree_down`: the zipper laws;
* `mem_lang_focus`: the focus's language is the residual by the path;
* `Trie.eq_of_lang_eq`: reduced tries with equal languages are equal;
* `Trie.no_dead_end`: below a reduced nonempty trie every focus is nonempty;
* `Trie.card_words`: the count recursion gives the size of the language;
* `lang_depProd`, `lang_prod`: products of cursors read concatenations;
* `range_spell`, `range_spell_const`: the words of the polynomial composite
  `langPoly ◁ langPoly` are the dependent concatenation, and the product with
  constant dependence;
* `leafConcat_eq_of_prefixFree`, `leafConcat_ne_example`, `enc_prefixFree`;
* `mem_leapfrog`: leapfrog intersection is sound and complete;
* `undo_bind`, `Version.store_up_down`, `Version.live_down`, `Version.live_up`:
  the trail laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PolyCursor

/-! ## 1. Holes and zippers -/

section Generic

variable {α : Type} {β : α → Type}

/-- A one-hole context of the polynomial `Σ a, X ^ (β a)`: a position, the
direction of the hole, and the values in every other direction. -/
structure Hole (β : α → Type) (X : Type) where
  a : α
  d : β a
  rest : ∀ e : β a, e ≠ d → X

/-- The position at the root of a tree. -/
def rootPos : WType β → α
  | ⟨a, _⟩ => a

/-- A zipper: a subtree in focus and the holes above it, innermost first. -/
structure Zipper (β : α → Type) where
  focus : WType β
  ctx : List (Hole β (WType β))

/-- Unplugging the value in direction `d`. -/
def unplug {X : Type} (a : α) (f : β a → X) (d : β a) : Hole β X × X :=
  (⟨a, d, fun e _ => f e⟩, f d)

/-- Moving down in a direction of the focus. -/
def Zipper.down : (z : Zipper β) → β (rootPos z.focus) → Zipper β
  | ⟨⟨a, f⟩, hs⟩, d => ⟨f d, (unplug a f d).1 :: hs⟩

variable [∀ a, DecidableEq (β a)]

/-- Plugging a value into a hole. -/
def Hole.plug {X : Type} (h : Hole β X) (x : X) : β h.a → X :=
  fun e => if he : e = h.d then x else h.rest e he

theorem plug_unplug_apply {X : Type} (a : α) (f : β a → X) (d : β a) (e : β a) :
    Hole.plug (⟨a, d, fun e _ => f e⟩ : Hole β X) (f d) e = f e := by
  unfold Hole.plug
  by_cases h : e = d
  · subst h; simp
  · simp [h]

theorem plug_unplug {X : Type} (a : α) (f : β a → X) (d : β a) :
    (unplug a f d).1.plug (unplug a f d).2 = f :=
  funext fun e => plug_unplug_apply a f d e

theorem unplug_plug {X : Type} (h : Hole β X) (x : X) :
    unplug h.a (h.plug x) h.d = (h, x) := by
  obtain ⟨a, d, rest⟩ := h
  simp only [unplug, Hole.plug, dite_true, Prod.mk.injEq, and_true]
  congr
  funext e he
  simp [he]

/-- Plugging a subtree into a stack of holes. -/
def plugAll : List (Hole β (WType β)) → WType β → WType β
  | [], t => t
  | h :: hs, t => plugAll hs (WType.mk h.a (h.plug t))

namespace Zipper

/-- The whole tree a zipper stands in. -/
def tree (z : Zipper β) : WType β := plugAll z.ctx z.focus

/-- Moving up: plugging the focus back into the innermost hole. -/
def up : Zipper β → Option (Zipper β)
  | ⟨_, []⟩ => none
  | ⟨t, h :: hs⟩ => some ⟨WType.mk h.a (h.plug t), hs⟩

theorem up_down (z : Zipper β) (d : β (rootPos z.focus)) : (z.down d).up = some z := by
  obtain ⟨⟨a, f⟩, hs⟩ := z
  have := plug_unplug a f d
  simp only [down, up, unplug] at this ⊢
  rw [this]

theorem down_up (t : WType β) (h : Hole β (WType β)) (hs : List (Hole β (WType β))) :
    (⟨WType.mk h.a (h.plug t), hs⟩ : Zipper β).down h.d = ⟨t, h :: hs⟩ := by
  have := unplug_plug h t
  simp only [unplug, Prod.mk.injEq] at this
  simp only [down, unplug]
  rw [this.1, this.2]

theorem tree_down (z : Zipper β) (d : β (rootPos z.focus)) : (z.down d).tree = z.tree := by
  obtain ⟨⟨a, f⟩, hs⟩ := z
  have := plug_unplug a f d
  simp only [down, tree, plugAll, unplug] at this ⊢
  rw [this]

end Zipper

/-! ## 2. Path languages -/

variable {σ : Type} (acc : α → Prop) (lbl : ∀ a, β a → σ)

/-- The words of a tree: the direction labels on a path from the root to an
accepting position. -/
def lang : WType β → Set (List σ)
  | ⟨a, f⟩ => {w | (w = [] ∧ acc a) ∨ ∃ d w', w = lbl a d :: w' ∧ w' ∈ lang (f d)}

omit [∀ a, DecidableEq (β a)] in
theorem mem_lang_mk (a : α) (f : β a → WType β) (w : List σ) :
    w ∈ lang acc lbl (WType.mk a f) ↔
      (w = [] ∧ acc a) ∨ ∃ d w', w = lbl a d :: w' ∧ w' ∈ lang acc lbl (f d) := Iff.rfl

omit [∀ a, DecidableEq (β a)] in
theorem nil_mem_lang (a : α) (f : β a → WType β) :
    ([] : List σ) ∈ lang acc lbl (WType.mk a f) ↔ acc a := by
  rw [mem_lang_mk]; simp

omit [∀ a, DecidableEq (β a)] in
theorem cons_mem_lang (a : α) (f : β a → WType β) (c : σ) (w : List σ) :
    (c :: w) ∈ lang acc lbl (WType.mk a f) ↔ ∃ d, lbl a d = c ∧ w ∈ lang acc lbl (f d) := by
  rw [mem_lang_mk]
  simp only [reduceCtorEq, false_and, false_or, List.cons.injEq]
  constructor
  · rintro ⟨d, w', ⟨rfl, rfl⟩, h⟩; exact ⟨d, rfl, h⟩
  · rintro ⟨d, rfl, h⟩; exact ⟨d, w, ⟨rfl, rfl⟩, h⟩

/-- The path from the root to the focus, as labels. -/
def Zipper.path (z : Zipper β) : List σ := (z.ctx.map fun h => lbl h.a h.d).reverse

/-- With labels that tell the directions of a position apart, the language
below the focus is the residual of the whole tree's language by the path. -/
theorem mem_lang_focus (hl : ∀ a, Function.Injective (lbl a)) (z : Zipper β) (w : List σ) :
    w ∈ lang acc lbl z.focus ↔ z.path lbl ++ w ∈ lang acc lbl z.tree := by
  obtain ⟨t, hs⟩ := z
  induction hs generalizing t w with
  | nil => simp [Zipper.path, Zipper.tree, plugAll]
  | cons h hs ih =>
    have step : w ∈ lang acc lbl t ↔
        (lbl h.a h.d :: w) ∈ lang acc lbl (WType.mk h.a (h.plug t)) := by
      rw [cons_mem_lang]
      constructor
      · intro hw; exact ⟨h.d, rfl, by simpa [Hole.plug] using hw⟩
      · rintro ⟨e, he, hw⟩
        have := hl h.a he; subst this
        simpa [Hole.plug] using hw
    rw [step, ih]
    simp [Zipper.path, Zipper.tree, plugAll]

end Generic

/-! ## 3. Tries -/

section Tries

variable {σ : Type}

/-- The directions of the trie polynomial at a position: its letters. -/
abbrev TrieB (σ : Type) : Bool × Finset σ → Type := fun p => {c : σ // c ∈ p.2}

/-- Tries over an alphabet: trees of the polynomial whose positions are an
accept flag and a finite set of letters. -/
abbrev Trie (σ : Type) := WType (TrieB σ)

namespace Trie

/-- The language of a trie. -/
def tlang : Trie σ → Set (List σ) := lang (fun p => p.1 = true) (fun _ c => c.val)

/-- A reduced trie has no empty subtrie. -/
def Reduced : Trie σ → Prop
  | ⟨_, f⟩ => ∀ d, (tlang (f d)).Nonempty ∧ Reduced (f d)

theorem nil_mem (p : Bool × Finset σ) (f : TrieB σ p → Trie σ) :
    ([] : List σ) ∈ tlang (WType.mk p f) ↔ p.1 = true :=
  nil_mem_lang _ _ p f

theorem cons_mem (p : Bool × Finset σ) (f : TrieB σ p → Trie σ) (c : σ) (w : List σ) :
    (c :: w) ∈ tlang (WType.mk p f) ↔ ∃ h : c ∈ p.2, w ∈ tlang (f ⟨c, h⟩) := by
  unfold tlang; rw [cons_mem_lang]
  constructor
  · rintro ⟨⟨c', hc⟩, rfl, hw⟩; exact ⟨hc, hw⟩
  · rintro ⟨hc, hw⟩; exact ⟨⟨c, hc⟩, rfl, hw⟩

/-- Reduced tries with the same language are equal: with shared nodes, set
equality is node identity. -/
theorem eq_of_lang_eq : ∀ (t₁ t₂ : Trie σ), Reduced t₁ → Reduced t₂ → tlang t₁ = tlang t₂ → t₁ = t₂
  | ⟨⟨b₁, S₁⟩, f₁⟩, ⟨⟨b₂, S₂⟩, f₂⟩, r₁, r₂, h => by
    have hb : b₁ = b₂ := by
      have e₁ := nil_mem (b₁, S₁) f₁
      have e₂ := nil_mem (b₂, S₂) f₂
      rw [h] at e₁
      have := e₁.symm.trans e₂
      cases b₁ <;> cases b₂ <;> simp_all
    have hS : S₁ = S₂ := by
      ext c
      constructor
      · intro hc
        obtain ⟨w, hw⟩ := (r₁ ⟨c, hc⟩).1
        have : (c :: w) ∈ tlang (WType.mk (b₁, S₁) f₁) := (cons_mem _ _ c w).2 ⟨hc, hw⟩
        rw [h] at this
        exact ((cons_mem _ _ c w).1 this).1
      · intro hc
        obtain ⟨w, hw⟩ := (r₂ ⟨c, hc⟩).1
        have : (c :: w) ∈ tlang (WType.mk (b₂, S₂) f₂) := (cons_mem _ _ c w).2 ⟨hc, hw⟩
        rw [← h] at this
        exact ((cons_mem _ _ c w).1 this).1
    subst hb; subst hS
    congr
    funext d
    apply eq_of_lang_eq (f₁ d) (f₂ d) (r₁ d).2 (r₂ d).2
    ext w
    have e₁ := cons_mem (b₁, S₁) f₁ d.val w
    have e₂ := cons_mem (b₁, S₁) f₂ d.val w
    rw [h] at e₁
    constructor
    · intro hw; exact (e₂.1 (e₁.2 ⟨d.2, hw⟩)).2
    · intro hw; exact (e₁.1 (e₂.2 ⟨d.2, hw⟩)).2

/-- The zippers reachable from a trie by moving down. -/
inductive Below (t : Trie σ) : Zipper (TrieB σ) → Prop
  | start : Below t ⟨t, []⟩
  | down {z : Zipper (TrieB σ)} (d : TrieB σ (rootPos z.focus)) : Below t z → Below t (z.down d)

/-- Below a reduced trie with a nonempty language every focus has a nonempty
language: a cursor that walks down never reaches a dead end. -/
theorem no_dead_end {t : Trie σ} (hr : Reduced t) (hn : (tlang t).Nonempty)
    {z : Zipper (TrieB σ)} (hz : Below t z) : Reduced z.focus ∧ (tlang z.focus).Nonempty := by
  induction hz with
  | start => exact ⟨hr, hn⟩
  | @down z d _ ih =>
    obtain ⟨hr', _⟩ := ih
    obtain ⟨⟨p, f⟩, hs⟩ := z
    exact ⟨(hr' d).2, (hr' d).1⟩

variable [DecidableEq σ]

/-- The number of words, by one pass over the nodes. -/
def count : Trie σ → ℕ
  | ⟨⟨b, S⟩, f⟩ => (if b then 1 else 0) + ∑ d ∈ S.attach, count (f d)

/-- The words of a trie, as a finite set. -/
def words : Trie σ → Finset (List σ)
  | ⟨⟨b, S⟩, f⟩ => (if b then {[]} else ∅) ∪
      S.attach.biUnion fun d => (words (f d)).map ⟨List.cons d.val, List.cons_injective⟩

theorem coe_words : ∀ t : Trie σ, (words t : Set (List σ)) = tlang t
  | ⟨⟨b, S⟩, f⟩ => by
    ext w
    cases w with
    | nil =>
      rw [nil_mem]; cases b <;> simp [words]
    | cons c w =>
      rw [cons_mem]
      simp only [words, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_biUnion,
        Finset.mem_attach, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro (h | ⟨⟨c', hc'⟩, w', hw', he⟩)
        · cases b <;> simp at h
        · simp only [List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨hc', ?_⟩
          rw [← coe_words (f ⟨c', hc'⟩)]; exact hw'
      · rintro ⟨hc, hw⟩
        right
        refine ⟨⟨c, hc⟩, w, ?_, rfl⟩
        rw [← Finset.mem_coe, coe_words (f ⟨c, hc⟩)]; exact hw

/-- The count recursion gives the size of the language. -/
theorem card_words : ∀ t : Trie σ, (words t).card = count t
  | ⟨⟨b, S⟩, f⟩ => by
    simp only [words, count]
    rw [Finset.card_union_of_disjoint]
    · congr 1
      · cases b <;> simp
      · rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.card_map, card_words (f d)]
        · intro d₁ _ d₂ _ hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro w h₁ h₂
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h₁ h₂
          obtain ⟨u₁, _, rfl⟩ := h₁
          obtain ⟨u₂, _, he⟩ := h₂
          simp only [List.cons.injEq] at he
          exact hne (Subtype.ext he.1.symm)
    · rw [Finset.disjoint_left]
      intro w h₁ h₂
      cases b
      · simp at h₁
      · simp only [if_true, Finset.mem_singleton] at h₁
        subst h₁
        simp at h₂

end Trie

end Tries

/-! ## 4. Cursors over words and their products -/

section Products

variable {σ : Type}

/-- A cursor over words: a coalgebra of `X ↦ Prop × X ^ σ`. -/
structure Cursor (σ X : Type) where
  acc : X → Prop
  step : X → σ → X

variable {X Y : Type}

def Cursor.run (c : Cursor σ X) : X → List σ → X
  | x, [] => x
  | x, a :: w => c.run (c.step x a) w

/-- The language a cursor reads from a state. -/
def Cursor.lang (c : Cursor σ X) (x : X) : Set (List σ) := {w | c.acc (c.run x w)}

theorem Cursor.nil_mem (c : Cursor σ X) (x : X) : ([] : List σ) ∈ c.lang x ↔ c.acc x := Iff.rfl

theorem Cursor.cons_mem (c : Cursor σ X) (x : X) (a : σ) (w : List σ) :
    (a :: w) ∈ c.lang x ↔ w ∈ c.lang (c.step x a) := Iff.rfl

/-- A trie as a cursor: a missing child is the dead state `none`. -/
def trieCursor [DecidableEq σ] : Cursor σ (Option (Trie σ)) where
  acc := fun | some ⟨p, _⟩ => p.1 = true | none => False
  step := fun
    | some ⟨p, f⟩, a => if h : a ∈ p.2 then some (f ⟨a, h⟩) else none
    | none, _ => none

theorem trieCursor_lang [DecidableEq σ] (t : Trie σ) :
    (trieCursor : Cursor σ _).lang (some t) = Trie.tlang t := by
  ext w
  induction w generalizing t with
  | nil => obtain ⟨p, f⟩ := t; rw [Cursor.nil_mem, Trie.nil_mem]; rfl
  | cons a w ih =>
    obtain ⟨p, f⟩ := t
    rw [Cursor.cons_mem, Trie.cons_mem]
    have hstep : (trieCursor : Cursor σ (Option (Trie σ))).step (some (WType.mk p f)) a =
        if h : a ∈ p.2 then some (f ⟨a, h⟩) else none := rfl
    rw [hstep]
    by_cases ha : a ∈ p.2
    · rw [dif_pos ha, ih]
      exact ⟨fun hw => ⟨ha, hw⟩, fun ⟨_, hw⟩ => hw⟩
    · rw [dif_neg ha]
      have dead : ∀ v : List σ, v ∉ (trieCursor : Cursor σ (Option (Trie σ))).lang none := by
        intro v; induction v with
        | nil => exact fun h => h
        | cons b v ihv => exact ihv
      exact ⟨fun hw => absurd hw (dead w), fun ⟨h, _⟩ => absurd h ha⟩

/-- The dependent concatenation: each word of `L` continued by a word of the
language its own prefix selects. -/
def depConcat (L : Set (List σ)) (F : List σ → Set (List σ)) : Set (List σ) :=
  {w | ∃ u ∈ L, ∃ v ∈ F u, w = u ++ v}

/-- The dependent product of two cursors: the first cursor, the prefix read so
far, and the second-factor states entered so far.  At an accepting state of the
first cursor, the second factor that its prefix selects is entered. -/
def depProd (c₁ : Cursor σ X) (c₂ : Cursor σ Y) (F : List σ → Y) :
    Cursor σ (X × List σ × Set Y) where
  acc := fun s => (c₁.acc s.1 ∧ c₂.acc (F s.2.1)) ∨ ∃ y ∈ s.2.2, c₂.acc y
  step := fun s a =>
    (c₁.step s.1 a, s.2.1 ++ [a],
      (fun y => c₂.step y a) '' (s.2.2 ∪ {y | c₁.acc s.1 ∧ y = F s.2.1}))

theorem depProd_acc (c₁ : Cursor σ X) (c₂ : Cursor σ Y) (F : List σ → Y) (x : X) (u : List σ)
    (S : Set Y) : (depProd c₁ c₂ F).acc (x, u, S) ↔ (c₁.acc x ∧ c₂.acc (F u)) ∨ ∃ y ∈ S, c₂.acc y :=
  Iff.rfl

theorem depProd_step (c₁ : Cursor σ X) (c₂ : Cursor σ Y) (F : List σ → Y) (x : X) (u : List σ)
    (S : Set Y) (a : σ) : (depProd c₁ c₂ F).step (x, u, S) a =
      (c₁.step x a, u ++ [a], (fun y => c₂.step y a) '' (S ∪ {y | c₁.acc x ∧ y = F u})) := rfl

theorem lang_depProd_state (c₁ : Cursor σ X) (c₂ : Cursor σ Y) (F : List σ → Y)
    (w : List σ) : ∀ (x : X) (u : List σ) (S : Set Y),
    w ∈ (depProd c₁ c₂ F).lang (x, u, S) ↔
      (∃ w₁ w₂, w = w₁ ++ w₂ ∧ w₁ ∈ c₁.lang x ∧ w₂ ∈ c₂.lang (F (u ++ w₁))) ∨
        ∃ y ∈ S, w ∈ c₂.lang y := by
  induction w with
  | nil =>
    intro x u S
    rw [Cursor.nil_mem, depProd_acc]
    constructor
    · rintro (⟨h₁, h₂⟩ | h)
      · exact Or.inl ⟨[], [], rfl, h₁, by rw [List.append_nil]; exact h₂⟩
      · exact Or.inr h
    · rintro (⟨w₁, w₂, he, h₁, h₂⟩ | h)
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 he.symm
        exact Or.inl ⟨h₁, by rw [List.append_nil] at h₂; exact h₂⟩
      · exact Or.inr h
  | cons a w ih =>
    intro x u S
    rw [Cursor.cons_mem, depProd_step, ih]
    constructor
    · rintro (⟨w₁, w₂, rfl, h₁, h₂⟩ | ⟨y', hy', hw⟩)
      · refine Or.inl ⟨a :: w₁, w₂, rfl, h₁, ?_⟩
        simpa [List.append_assoc] using h₂
      · obtain ⟨y, hy, rfl⟩ := hy'
        rcases hy with hy | ⟨hx, rfl⟩
        · exact Or.inr ⟨y, hy, hw⟩
        · exact Or.inl ⟨[], a :: w, rfl, hx, by rw [List.append_nil]; exact hw⟩
    · rintro (⟨w₁, w₂, he, h₁, h₂⟩ | ⟨y, hy, hw⟩)
      · cases w₁ with
        | nil =>
          simp only [List.nil_append] at he
          subst he
          exact Or.inr ⟨c₂.step (F u) a, ⟨F u, Or.inr ⟨h₁, rfl⟩, rfl⟩,
            by rw [List.append_nil] at h₂; exact h₂⟩
        | cons b w₁ =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact Or.inl ⟨w₁, w₂, rfl, h₁, by simpa [List.append_assoc] using h₂⟩
      · exact Or.inr ⟨c₂.step y a, ⟨y, Or.inl hy, rfl⟩, hw⟩

/-- The dependent product reads the dependent concatenation. -/
theorem lang_depProd (c₁ : Cursor σ X) (c₂ : Cursor σ Y) (F : List σ → Y) (x : X) :
    (depProd c₁ c₂ F).lang (x, [], ∅) = depConcat (c₁.lang x) fun u => c₂.lang (F u) := by
  ext w
  rw [lang_depProd_state]
  constructor
  · rintro (⟨w₁, w₂, rfl, h₁, h₂⟩ | ⟨y, hy, _⟩)
    · exact ⟨w₁, h₁, w₂, by simpa using h₂, rfl⟩
    · exact absurd hy (Set.notMem_empty y)
  · rintro ⟨w₁, h₁, w₂, h₂, rfl⟩; exact Or.inl ⟨w₁, w₂, rfl, h₁, by simpa using h₂⟩

/-- The product of two cursors is the dependent product with constant
dependence, and reads the concatenation of the two languages. -/
theorem lang_prod (c₁ : Cursor σ X) (c₂ : Cursor σ Y) (x : X) (y : Y) :
    (depProd c₁ c₂ fun _ => y).lang (x, [], ∅) = Set.image2 (· ++ ·) (c₁.lang x) (c₂.lang y) := by
  rw [lang_depProd]
  ext w
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩

/-- The same, as the product of Mathlib's languages. -/
theorem lang_prod_language (c₁ : Cursor σ X) (c₂ : Cursor σ Y) (x : X) (y : Y) :
    (show Language σ from (depProd c₁ c₂ fun _ => y).lang (x, [], ∅)) =
      (show Language σ from c₁.lang x) * (show Language σ from c₂.lang y) := by
  rw [Language.mul_def]; exact lang_prod c₁ c₂ x y

/-! ### The composition product of polynomials -/

/-- The polynomial of languages: a position is a language, its directions are
its words. -/
def langPoly (σ : Type) : PFunctor.{0, 0} := ⟨Set (List σ), fun L => {w // w ∈ L}⟩

/-- The word a direction of `langPoly σ ◁ langPoly σ` spells: the first
factor's word, then the second's. -/
def spell (p : (PFunctor.comp (langPoly σ) (langPoly σ)).A) :
    (PFunctor.comp (langPoly σ) (langPoly σ)).B p → List σ :=
  fun d => d.1.1 ++ d.2.1

/-- The words spelled by the directions of a composite position are the
dependent concatenation: the language of `◁` is concatenation. -/
theorem range_spell (L : Set (List σ)) (F : List σ → Set (List σ)) :
    Set.range (spell (σ := σ) ⟨L, fun u => F u.1⟩) = depConcat L F := by
  ext w
  constructor
  · rintro ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, rfl⟩

/-- With constant dependence the composite spells the product of languages. -/
theorem range_spell_const (L M : Set (List σ)) :
    Set.range (spell (σ := σ) ⟨L, fun _ => M⟩) = Set.image2 (· ++ ·) L M := by
  rw [range_spell L fun _ => M]
  ext w
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩

/-! ### Grafting at leaves -/

/-- The words of `L` that no other word of `L` extends: the leaves of its trie. -/
def maximal (L : Set (List σ)) : Set (List σ) := {u | u ∈ L ∧ ∀ v, u ++ v ∈ L → v = []}

/-- Entering the next factor only at leaves. -/
def leafConcat (L : Set (List σ)) (F : List σ → Set (List σ)) : Set (List σ) :=
  depConcat (maximal L) F

/-- No word of the language is a proper prefix of another. -/
def PrefixFree (L : Set (List σ)) : Prop := ∀ u ∈ L, ∀ v, u ++ v ∈ L → v = []

theorem leafConcat_eq_of_prefixFree (L : Set (List σ)) (F : List σ → Set (List σ))
    (h : PrefixFree L) : leafConcat L F = depConcat L F := by
  have : maximal L = L := by
    ext u; exact ⟨fun hu => hu.1, fun hu => ⟨hu, h u hu⟩⟩
  simp [leafConcat, this]

/-- Without prefix-freeness the two differ: with `arr` and `arrow` both
stored, grafting at leaves loses `arr` followed by the second factor. -/
theorem leafConcat_ne_example :
    leafConcat ({['a', 'r', 'r'], ['a', 'r', 'r', 'o', 'w']} : Set (List Char)) (fun _ => {['a']}) ≠
      depConcat ({['a', 'r', 'r'], ['a', 'r', 'r', 'o', 'w']} : Set (List Char)) (fun _ => {['a']}) := by
  intro h
  have hmem : ['a', 'r', 'r', 'a'] ∈ depConcat ({['a', 'r', 'r'], ['a', 'r', 'r', 'o', 'w']} : Set (List Char))
      (fun _ => {['a']}) :=
    ⟨['a', 'r', 'r'], Set.mem_insert _ _, ['a'], Set.mem_singleton _, by decide⟩
  rw [← h] at hmem
  obtain ⟨u, ⟨hu, hmax⟩, v, hv, he⟩ := hmem
  rw [Set.mem_singleton_iff] at hv
  subst hv
  rcases (Set.mem_insert_iff.1 hu) with rfl | hu'
  · have := hmax ['o', 'w'] (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    exact absurd this (by decide)
  · rw [Set.mem_singleton_iff] at hu'
    subst hu'
    exact absurd he (by decide)

/-- Terms in prefix encoding: each node is a marker followed by its two parts. -/
inductive Tm (γ : Type) where
  | atom (c : γ)
  | node (l r : Tm γ)

/-- The prefix encoding of a term, over the alphabet `Option γ` (`none` marks a node). -/
def enc {γ : Type} : Tm γ → List (Option γ)
  | .atom c => [some c]
  | .node l r => none :: (enc l ++ enc r)

theorem enc_append_inj {γ : Type} :
    ∀ (t t' : Tm γ) (v v' : List (Option γ)), enc t ++ v = enc t' ++ v' → t = t' ∧ v = v'
  | .atom c, .atom c', v, v', h => by
    simp only [enc, List.cons_append, List.nil_append, List.cons.injEq, Option.some.injEq] at h
    exact ⟨by rw [h.1], h.2⟩
  | .atom c, .node l r, v, v', h => by simp [enc] at h
  | .node l r, .atom c, v, v', h => by simp [enc] at h
  | .node l r, .node l' r', v, v', h => by
    simp only [enc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨rfl, h₁⟩ := enc_append_inj l l' _ _ h
    obtain ⟨rfl, h₂⟩ := enc_append_inj r r' _ _ h₁
    exact ⟨rfl, h₂⟩

/-- Encoded terms form a prefix-free language, so grafting at leaves and at
accepting positions agree on a space of encoded terms. -/
theorem enc_prefixFree {γ : Type} : PrefixFree {w : List (Option γ) | ∃ t, enc t = w} := by
  rintro u ⟨t, rfl⟩ v ⟨t', h⟩
  exact (enc_append_inj t t' v [] (by simpa using h.symm)).2

end Products

/-! ## 5. Leapfrog intersection -/

section Leapfrog

variable {κ : Type} [LinearOrder κ]

/-- A cursor over a sorted key list moves forward to the first key `≥ k`. -/
def seek (k : κ) (l : List κ) : List κ := l.dropWhile fun x => decide (x < k)

theorem seek_sublist (k : κ) (l : List κ) : (seek k l).Sublist l :=
  (List.dropWhile_suffix _).sublist

theorem seek_cons_of_lt {k y : κ} (l : List κ) (hy : y < k) : seek k (y :: l) = seek k l := by
  simp [seek, hy]

theorem seek_cons_of_le {k y : κ} (l : List κ) (hy : k ≤ y) : seek k (y :: l) = y :: l := by
  simp [seek, not_lt.2 hy]

theorem mem_seek {k x : κ} {l : List κ} (hs : l.Pairwise (· < ·)) :
    x ∈ seek k l ↔ x ∈ l ∧ k ≤ x := by
  induction l with
  | nil => simp [seek]
  | cons y l ih =>
    by_cases hy : y < k
    · rw [seek_cons_of_lt l hy, ih hs.of_cons]
      constructor
      · rintro ⟨h₁, h₂⟩; exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩
      · rintro ⟨h₁, h₂⟩
        rcases List.mem_cons.1 h₁ with rfl | h₁
        · exact absurd h₂ (not_le.2 hy)
        · exact ⟨h₁, h₂⟩
    · rw [seek_cons_of_le l (not_lt.1 hy)]
      constructor
      · intro hx; refine ⟨hx, ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact not_lt.1 hy
        · exact le_of_lt (lt_of_le_of_lt (not_lt.1 hy) (List.rel_of_pairwise_cons hs hx))
      · exact fun h => h.1

/-- The heads of the lists, when none is empty. -/
def heads : List (List κ) → Option (List κ)
  | [] => some []
  | [] :: _ => none
  | (x :: _) :: Ls => (heads Ls).map (x :: ·)

/-- Every cursor moves one step. -/
def tails (Ls : List (List κ)) : List (List κ) := Ls.map List.tail

/-- Every cursor seeks to `k`. -/
def seekAll (k : κ) (Ls : List (List κ)) : List (List κ) := Ls.map (seek k)

/-- The total length of the lists. -/
def total (Ls : List (List κ)) : ℕ := (Ls.map List.length).sum

omit [LinearOrder κ] in
theorem total_tails_lt : ∀ (Ls : List (List κ)) (hs : List κ), heads Ls = some hs → Ls ≠ [] →
    total (tails Ls) < total Ls
  | [], _, _, hne => absurd rfl hne
  | [] :: _, _, h, _ => by simp [heads] at h
  | (x :: l) :: Ls, hs, h, _ => by
    simp only [heads, Option.map_eq_some_iff] at h
    obtain ⟨hs', h', rfl⟩ := h
    by_cases hL : Ls = []
    · subst hL; simp [total, tails]
    · have := total_tails_lt Ls hs' h' hL
      simp only [total, tails, List.map_cons, List.sum_cons, List.tail_cons, List.length_cons] at this ⊢
      omega

theorem total_seekAll_le (k : κ) : ∀ Ls : List (List κ), total (seekAll k Ls) ≤ total Ls
  | [] => by simp [total, seekAll]
  | L :: Ls => by
    have := total_seekAll_le k Ls
    simp only [total, seekAll, List.map_cons, List.sum_cons] at this ⊢
    exact Nat.add_le_add (seek_sublist k L).length_le this

theorem total_seekAll_lt (k : κ) : ∀ (Ls : List (List κ)) (hs : List κ), heads Ls = some hs →
    (∃ x ∈ hs, x < k) → total (seekAll k Ls) < total Ls
  | [], hs, h, hlt => by simp [heads] at h; subst h; simp at hlt
  | [] :: _, _, h, _ => by simp [heads] at h
  | (y :: l) :: Ls, hs, h, hlt => by
    simp only [heads, Option.map_eq_some_iff] at h
    obtain ⟨hs', h', rfl⟩ := h
    rcases hlt with ⟨x, hx, hxk⟩
    have hle := total_seekAll_le k Ls
    simp only [total, seekAll, List.map_cons, List.sum_cons] at hle ⊢
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [seek_cons_of_lt l hxk]
      have := (seek_sublist k l).length_le
      simp only [List.length_cons]
      omega
    · have := total_seekAll_lt k Ls hs' h' ⟨x, hx, hxk⟩
      simp only [total, seekAll] at this
      have := (seek_sublist k (y :: l)).length_le
      omega

/-- Leapfrog intersection of sorted key lists: every cursor seeks to the
largest head; when all heads agree the key is emitted and every cursor moves
on. -/
def leapfrog (Ls : List (List κ)) : List κ :=
  match _hh : heads Ls with
  | none => []
  | some hs =>
    match _hm : hs.max? with
    | none => []
    | some m =>
      if _hall : ∀ x ∈ hs, x = m then
        m :: leapfrog (tails Ls)
      else
        leapfrog (seekAll m Ls)
termination_by total Ls
decreasing_by
  · apply total_tails_lt Ls hs _hh
    rintro rfl; simp [heads] at _hh; subst _hh; simp at _hm
  · apply total_seekAll_lt m Ls hs _hh
    simp only [not_forall] at _hall
    obtain ⟨x, hx, hne⟩ := _hall
    exact ⟨x, hx, lt_of_le_of_ne ((List.max?_eq_some_iff.1 _hm).2 x hx) hne⟩

theorem leapfrog_of_none {Ls : List (List κ)} (h : heads Ls = none) : leapfrog Ls = [] := by
  rw [leapfrog]; split
  · rfl
  · rename_i hs hh; rw [h] at hh; cases hh

theorem leapfrog_of_empty {Ls : List (List κ)} {hs : List κ} (h : heads Ls = some hs)
    (hm : hs.max? = none) : leapfrog Ls = [] := by
  rw [leapfrog]; split
  · rfl
  · rename_i hs' hh
    rw [h] at hh; cases hh
    split
    · rfl
    · rename_i m hm'; rw [hm] at hm'; cases hm'

theorem leapfrog_of_all {Ls : List (List κ)} {hs : List κ} {m : κ} (h : heads Ls = some hs)
    (hm : hs.max? = some m) (hall : ∀ x ∈ hs, x = m) : leapfrog Ls = m :: leapfrog (tails Ls) := by
  rw [leapfrog]; split
  · rename_i hh; rw [h] at hh; cases hh
  · rename_i hs' hh
    rw [h] at hh; cases hh
    split
    · rename_i hm'; rw [hm] at hm'; cases hm'
    · rename_i m' hm'
      rw [hm] at hm'; cases hm'
      rw [dif_pos hall]

theorem leapfrog_of_not_all {Ls : List (List κ)} {hs : List κ} {m : κ} (h : heads Ls = some hs)
    (hm : hs.max? = some m) (hall : ¬ ∀ x ∈ hs, x = m) : leapfrog Ls = leapfrog (seekAll m Ls) := by
  rw [leapfrog]; split
  · rename_i hh; rw [h] at hh; cases hh
  · rename_i hs' hh
    rw [h] at hh; cases hh
    split
    · rename_i hm'; rw [hm] at hm'; cases hm'
    · rename_i m' hm'
      rw [hm] at hm'; cases hm'
      rw [dif_neg hall]

omit [LinearOrder κ] in
theorem heads_none : ∀ Ls : List (List κ), heads Ls = none → [] ∈ Ls
  | [], h => by simp [heads] at h
  | [] :: _, _ => List.mem_cons_self
  | (x :: l) :: Ls, h => by
    simp only [heads, Option.map_eq_none_iff] at h
    exact List.mem_cons_of_mem _ (heads_none Ls h)

omit [LinearOrder κ] in
theorem heads_nil : ∀ (Ls : List (List κ)), heads Ls = some [] → Ls = []
  | [], _ => rfl
  | [] :: _, h => by simp [heads] at h
  | (x :: l) :: Ls, h => by simp [heads] at h

omit [LinearOrder κ] in
theorem head_mem_heads : ∀ (Ls : List (List κ)) (hs : List κ), heads Ls = some hs →
    ∀ L ∈ Ls, ∃ y l, L = y :: l ∧ y ∈ hs
  | [], _, _, L, hL => by simp at hL
  | [] :: _, _, h, _, _ => by simp [heads] at h
  | (x :: l) :: Ls, hs, h, L, hL => by
    simp only [heads, Option.map_eq_some_iff] at h
    obtain ⟨hs', h', rfl⟩ := h
    rcases List.mem_cons.1 hL with rfl | hL
    · exact ⟨x, l, rfl, List.mem_cons_self⟩
    · obtain ⟨y, l', rfl, hy⟩ := head_mem_heads Ls hs' h' L hL
      exact ⟨y, l', rfl, List.mem_cons_of_mem _ hy⟩

omit [LinearOrder κ] in
theorem mem_heads_list : ∀ (Ls : List (List κ)) (hs : List κ), heads Ls = some hs →
    ∀ y ∈ hs, ∃ l, (y :: l) ∈ Ls
  | [], hs, h, y, hy => by simp [heads] at h; subst h; simp at hy
  | [] :: _, _, h, _, _ => by simp [heads] at h
  | (x :: l) :: Ls, hs, h, y, hy => by
    simp only [heads, Option.map_eq_some_iff] at h
    obtain ⟨hs', h', rfl⟩ := h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨l, List.mem_cons_self⟩
    · obtain ⟨l', hl'⟩ := mem_heads_list Ls hs' h' y hy
      exact ⟨l', List.mem_cons_of_mem _ hl'⟩

/-- Leapfrog is sound and complete: it yields exactly the keys in every list. -/
theorem mem_leapfrog : ∀ (n : ℕ) (Ls : List (List κ)), total Ls ≤ n →
    (∀ L ∈ Ls, L.Pairwise (· < ·)) → ∀ x, x ∈ leapfrog Ls ↔ Ls ≠ [] ∧ ∀ L ∈ Ls, x ∈ L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Ls hn hs x
  rcases hh : heads Ls with _ | hs'
  · rw [leapfrog_of_none hh]
    simp only [List.not_mem_nil, false_iff, not_and, not_forall]
    intro _; exact ⟨[], heads_none Ls hh, by simp⟩
  · rcases hm : hs'.max? with _ | m
    · rw [leapfrog_of_empty hh hm]
      rw [List.max?_eq_none_iff] at hm; subst hm
      have := heads_nil Ls hh
      simp [this]
    · have hne : Ls ≠ [] := by
        rintro rfl; simp [heads] at hh; subst hh; simp at hm
      by_cases hall : ∀ y ∈ hs', y = m
      · rw [leapfrog_of_all hh hm hall, List.mem_cons]
        have hlt := total_tails_lt Ls hs' hh hne
        have hsT : ∀ L ∈ tails Ls, L.Pairwise (· < ·) := by
          intro L hL
          obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
          cases L' with
          | nil => simp
          | cons y l => exact (hs _ hL').of_cons
        rw [ih (total (tails Ls)) (by omega) (tails Ls) le_rfl hsT x]
        have hTne : tails Ls ≠ [] := by simpa [tails] using hne
        constructor
        · rintro (rfl | ⟨_, hT⟩)
          · refine ⟨hne, fun L hL => ?_⟩
            obtain ⟨y, l, rfl, hy⟩ := head_mem_heads Ls hs' hh L hL
            rw [hall y hy]; exact List.mem_cons_self
          · refine ⟨hne, fun L hL => ?_⟩
            exact List.mem_of_mem_tail (hT _ (List.mem_map_of_mem hL))
        · rintro ⟨_, hA⟩
          by_cases hx : x = m
          · exact Or.inl hx
          · refine Or.inr ⟨hTne, fun L hL => ?_⟩
            obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
            obtain ⟨y, l, rfl, hy⟩ := head_mem_heads Ls hs' hh L' hL'
            rcases List.mem_cons.1 (hA _ hL') with h | h
            · exact absurd (h.trans (hall y hy)) hx
            · exact h
      · rw [leapfrog_of_not_all hh hm hall]
        have hlt : total (seekAll m Ls) < total Ls := by
          apply total_seekAll_lt m Ls hs' hh
          simp only [not_forall] at hall
          obtain ⟨y, hy, hne'⟩ := hall
          exact ⟨y, hy, lt_of_le_of_ne ((List.max?_eq_some_iff.1 hm).2 y hy) hne'⟩
        have hsS : ∀ L ∈ seekAll m Ls, L.Pairwise (· < ·) := by
          intro L hL
          obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
          exact (hs _ hL').sublist (seek_sublist m L')
        rw [ih (total (seekAll m Ls)) (by omega) (seekAll m Ls) le_rfl hsS x]
        have hSne : seekAll m Ls ≠ [] := by simpa [seekAll] using hne
        constructor
        · rintro ⟨_, hA⟩
          exact ⟨hne, fun L hL => (seek_sublist m L).subset (hA _ (List.mem_map_of_mem hL))⟩
        · rintro ⟨_, hA⟩
          refine ⟨hSne, fun L hL => ?_⟩
          obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
          rw [mem_seek (hs _ hL')]
          refine ⟨hA _ hL', ?_⟩
          -- the list whose head is the largest head holds no key below it
          obtain ⟨l, hml⟩ := mem_heads_list Ls hs' hh m (List.max?_mem hm)
          rcases List.mem_cons.1 (hA _ hml) with h | h
          · exact le_of_eq h.symm
          · exact le_of_lt (List.rel_of_pairwise_cons (hs _ hml) h)

end Leapfrog

/-! ## 6. Trails: a binding store is a zipper over its version tree -/

section Trails

variable {V T : Type} [DecidableEq V]

/-- A binding store with an undo trail: each entry is a variable and the value
it had before. -/
structure Live (V T : Type) where
  store : V → Option T
  trail : List (V × Option T)

/-- Binding records the old value. -/
def bindL (x : V) (v : T) (s : Live V T) : Live V T :=
  ⟨Function.update s.store x (some v), (x, s.store x) :: s.trail⟩

/-- Undo restores the recorded value. -/
def undoL : Live V T → Option (Live V T)
  | ⟨_, []⟩ => none
  | ⟨st, (x, o) :: tr⟩ => some ⟨Function.update st x o, tr⟩

/-- Restoring after a bind is the identity. -/
theorem undo_bind (x : V) (v : T) (s : Live V T) : undoL (bindL x v s) = some s := by
  obtain ⟨st, tr⟩ := s
  simp [bindL, undoL]

/-- The store as a lens on one variable: put-get, get-put and put-put. -/
theorem store_put_get (st : V → Option T) (x : V) (o : Option T) :
    Function.update st x o x = o := by simp

theorem store_get_put (st : V → Option T) (x : V) : Function.update st x (st x) = st := by simp

theorem store_put_put (st : V → Option T) (x : V) (o o' : Option T) :
    Function.update (Function.update st x o) x o' = Function.update st x o' := by simp

/-- The version-tree polynomial: a position is the list of edits that lead to
its children; a direction picks one of them. -/
abbrev VB (E : Type) : List E → Type := fun l => Fin l.length

namespace Version

/-- An edit binds a variable. -/
abbrev Edit (V T : Type) := V × T

/-- Applying an edit to a store. -/
def apply (st : V → Option T) (e : Edit V T) : V → Option T := Function.update st e.1 (some e.2)

/-- The edit that leads to each child. -/
def edit (l : List (Edit V T)) (i : Fin l.length) : Edit V T := l[i]

/-- The edits from the root of the version tree down to the focus. -/
def edits (z : Zipper (VB (Edit V T))) : List (Edit V T) := Zipper.path edit z

/-- The store at a version: the initial store with the edits on its path applied. -/
def storeAt (st₀ : V → Option T) (z : Zipper (VB (Edit V T))) : V → Option T :=
  (edits z).foldl apply st₀

omit [DecidableEq V] in
theorem edits_down (z : Zipper (VB (Edit V T))) (d : Fin (rootPos z.focus).length) :
    edits (z.down d) = edits z ++ [edit (rootPos z.focus) d] := by
  obtain ⟨⟨l, f⟩, hs⟩ := z
  simp [edits, Zipper.path, Zipper.down, unplug, rootPos]

/-- Moving down applies the edit that leads there. -/
theorem storeAt_down (st₀ : V → Option T) (z : Zipper (VB (Edit V T)))
    (d : Fin (rootPos z.focus).length) :
    storeAt st₀ (z.down d) = apply (storeAt st₀ z) (edit (rootPos z.focus) d) := by
  simp [storeAt, edits_down, List.foldl_append]

/-- Moving down and back up returns to the same version and the same store. -/
theorem store_up_down (st₀ : V → Option T) (z : Zipper (VB (Edit V T)))
    (d : Fin (rootPos z.focus).length) :
    ((z.down d).up).map (storeAt st₀) = some (storeAt st₀ z) := by
  rw [Zipper.up_down]; rfl

/-- The trail along a list of edits, innermost first: each edit's variable and
the value it had before. -/
def trailAux : (V → Option T) → List (Edit V T) → List (V × Option T) → List (V × Option T)
  | _, [], acc => acc
  | st, e :: es, acc => trailAux (apply st e) es ((e.1, st e.1) :: acc)

theorem trailAux_concat (e : Edit V T) : ∀ (es : List (Edit V T)) (st : V → Option T)
    (acc : List (V × Option T)),
    trailAux st (es ++ [e]) acc = (e.1, (es.foldl apply st) e.1) :: trailAux st es acc
  | [], st, acc => by simp [trailAux]
  | e' :: es, st, acc => by simp [trailAux, trailAux_concat e es]

/-- A live store tracks a version when it holds that version's store and the
trail of the edits leading to it. -/
def Tracks (st₀ : V → Option T) (es : List (Edit V T)) (s : Live V T) : Prop :=
  s.store = es.foldl apply st₀ ∧ s.trail = trailAux st₀ es []

/-- Binding follows a move down the version tree. -/
theorem live_down (st₀ : V → Option T) (es : List (Edit V T)) (s : Live V T)
    (h : Tracks st₀ es s) (e : Edit V T) : Tracks st₀ (es ++ [e]) (bindL e.1 e.2 s) := by
  obtain ⟨hs, ht⟩ := h
  refine ⟨?_, ?_⟩
  · simp [bindL, List.foldl_append, apply, hs]
  · simp [bindL, trailAux_concat, hs, ht]

/-- Undo follows a move up the version tree. -/
theorem live_up (st₀ : V → Option T) (es : List (Edit V T)) (e : Edit V T) (s : Live V T)
    (h : Tracks st₀ (es ++ [e]) s) : ∃ s', undoL s = some s' ∧ Tracks st₀ es s' := by
  obtain ⟨hs, ht⟩ := h
  obtain ⟨st, tr⟩ := s
  simp only [trailAux_concat] at ht
  simp only at hs ht
  subst ht
  refine ⟨⟨Function.update st e.1 ((es.foldl apply st₀) e.1), trailAux st₀ es []⟩, rfl, ?_, rfl⟩
  simp [hs, List.foldl_append, apply]

end Version

end Trails

end Mettapedia.Machines.PolyCursor
