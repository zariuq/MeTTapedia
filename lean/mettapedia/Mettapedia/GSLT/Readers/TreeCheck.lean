import Mettapedia.GSLT.Readers.SLR

/-!
# The trusted tree check of a two-level reader

A reader engine (in MeTTa or in C) parses with untrusted SLR tables and returns trees. Each tree
is accepted only after a check that is independent of the tables: the tree is printed back from
the grammar's productions, and the printed tokens must be the tokens the tree covers. This module
defines that check (`printTree`), a token-level derivation relation (`Derives`), and proves that
they agree both ways (`printTree_iff`).

A tree is a production node with its children in order (phrase subtrees and token leaves; the
fixed spellings of the production are implied, as in `GrammarDerives` trees) or a token leaf
(a token sort and the token's text).

Example: with `s ::= "a" s | "b"`, the tree `node "more" [node "end" []]` prints to `a b`.
Negative example: `node "more" []` prints to nothing, because `more` needs a phrase child.

`GrammarCorrespondence` connects this relation to `GrammarDerives.Derives` over the authored rows.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.TreeCheck

open Mettapedia.GSLT.Readers.SLR

/-- A reader tree. -/
inductive Tree where
  | leaf (sort : String) (text : String)
  | node (label : String) (kids : List Tree)
  deriving Repr

/-- A token-level grammar: productions, the token sorts, and token-sort membership. -/
structure Grammar where
  prods : List Prod
  tokenSorts : List String
  inSort : String → String → Bool

/-- The production with this label, when exactly one has it. -/
def Grammar.prodOf? (g : Grammar) (label : String) : Option Prod :=
  match g.prods.filter (·.label == label) with
  | [p] => some p
  | _ => none

mutual
/-- Token-level derivations: a node derives what its production's items derive, in order; a leaf
derives its own text at its token sort. -/
inductive Derives (g : Grammar) : String → List String → Tree → Prop
  | node (p : Prod) (hp : g.prodOf? p.label = some p) (toks : List String) (kids : List Tree)
      (items : DerivesItems g p.rhs toks kids) : Derives g p.lhs toks (.node p.label kids)
  | leaf (c x : String) (hc : g.tokenSorts.contains c = true) (hx : g.inSort c x = true) :
      Derives g c [x] (.leaf c x)

/-- The items of a production derive the concatenation of their parts. -/
inductive DerivesItems (g : Grammar) : List Sym → List String → List Tree → Prop
  | nil : DerivesItems g [] [] []
  | lit (s : String) {rest : List Sym} {toks : List String} {kids : List Tree}
      (h : DerivesItems g rest toks kids) : DerivesItems g (.lit s :: rest) (s :: toks) kids
  | tok (c x : String) {rest : List Sym} {toks : List String} {kids : List Tree}
      (hc : g.tokenSorts.contains c = true) (hx : g.inSort c x = true)
      (h : DerivesItems g rest toks kids) :
      DerivesItems g (.tok c :: rest) (x :: toks) (.leaf c x :: kids)
  | nt (n : String) {sub : List String} {t : Tree} {rest : List Sym} {toks : List String}
      {kids : List Tree} (hsub : Derives g n sub t) (h : DerivesItems g rest toks kids) :
      DerivesItems g (.nt n :: rest) (sub ++ toks) (t :: kids)
end

/-! ## The check -/

/-- The leading fixed spellings of an item list, and the items after them. -/
def leadingLits : List Sym → List String × List Sym
  | .lit s :: rest => ((s :: (leadingLits rest).1), (leadingLits rest).2)
  | rest => ([], rest)

mutual
/-- Print a tree back from the productions: its sort and its tokens, or nothing if a node does
not fit its production. -/
def printTree (g : Grammar) : Tree → Option (String × List String)
  | .leaf c x => if g.tokenSorts.contains c && g.inSort c x then some (c, [x]) else none
  | .node label kids =>
      match g.prodOf? label with
      | none => none
      | some p =>
          match printItems g p.rhs kids with
          | none => none
          | some toks => some (p.lhs, toks)

/-- Print the children of a node along its production's items. -/
def printItems (g : Grammar) (rhs : List Sym) : List Tree → Option (List String)
  | [] => if (leadingLits rhs).2 = [] then some (leadingLits rhs).1 else none
  | kid :: kids =>
      match (leadingLits rhs).2 with
      | .tok c :: rest =>
          match kid with
          | .leaf c' x =>
              if c == c' && g.tokenSorts.contains c && g.inSort c x then
                match printItems g rest kids with
                | none => none
                | some toks => some ((leadingLits rhs).1 ++ x :: toks)
              else none
          | .node _ _ => none
      | .nt n :: rest =>
          match kid with
          | .leaf _ _ => none
          | .node _ _ =>
              match printTree g kid with
              | none => none
              | some (s, sub) =>
                  if s == n then
                    match printItems g rest kids with
                    | none => none
                    | some toks => some ((leadingLits rhs).1 ++ sub ++ toks)
                  else none
      | _ => none
end

/-- The check the engines run: the tree prints to exactly the tokens it covers, at its sort. -/
def check (g : Grammar) (sort : String) (toks : List String) (t : Tree) : Bool :=
  printTree g t == some (sort, toks)

/-! ## Agreement -/

mutual
/-- Height of a tree, for induction. -/
def Tree.height : Tree → Nat
  | .leaf _ _ => 0
  | .node _ kids => heights kids + 1
/-- The largest height in a list of trees. -/
def heights : List Tree → Nat
  | [] => 0
  | t :: ts => max t.height (heights ts)
end

theorem leadingLits_spec : ∀ (rhs : List Sym),
    rhs = (leadingLits rhs).1.map Sym.lit ++ (leadingLits rhs).2 ∧
      ∀ s rest, (leadingLits rhs).2 ≠ Sym.lit s :: rest
  | [] => by simp [leadingLits]
  | .lit s :: rest => by
      have ih := leadingLits_spec rest
      refine ⟨?_, ?_⟩
      · simp only [leadingLits, List.map_cons, List.cons_append, List.cons.injEq, true_and]
        exact ih.1
      · simpa [leadingLits] using ih.2
  | .tok c :: rest => by simp [leadingLits]
  | .nt n :: rest => by simp [leadingLits]
  | .eof :: rest => by simp [leadingLits]

/-- Items that begin with fixed spellings derive those spellings followed by what the rest
derives. -/
theorem derivesItems_lits (g : Grammar) :
    ∀ (ls : List String) (rest : List Sym) (toks : List String) (kids : List Tree),
      DerivesItems g (ls.map Sym.lit ++ rest) toks kids ↔
        ∃ toks', toks = ls ++ toks' ∧ DerivesItems g rest toks' kids
  | [], rest, toks, kids => by simp
  | s :: ls, rest, toks, kids => by
      constructor
      · intro h
        cases h with
        | lit _ h' =>
            rename_i toks''
            obtain ⟨toks', rfl, h''⟩ := (derivesItems_lits g ls rest toks'' kids).mp h'
            exact ⟨toks', rfl, h''⟩
      · rintro ⟨toks', rfl, h⟩
        exact .lit s ((derivesItems_lits g ls rest (ls ++ toks') kids).mpr ⟨toks', rfl, h⟩)

/-- Soundness of the check, items level, given soundness for smaller trees. -/
theorem printItems_sound (g : Grammar) {N : Nat}
    (ih : ∀ t s toks, t.height < N → printTree g t = some (s, toks) → Derives g s toks t) :
    ∀ (kids : List Tree) (rhs : List Sym) (toks : List String),
      heights kids < N → printItems g rhs kids = some toks → DerivesItems g rhs toks kids := by
  intro kids
  induction kids with
  | nil =>
      intro rhs toks _ h
      obtain ⟨hsplit, _⟩ := leadingLits_spec rhs
      unfold printItems at h
      generalize (leadingLits rhs).1 = ls at hsplit h
      generalize (leadingLits rhs).2 = r at hsplit h
      subst hsplit
      by_cases hr : r = []
      · subst hr
        simp only [↓reduceIte, Option.some.injEq] at h
        subst h
        exact (derivesItems_lits g _ [] _ []).mpr ⟨[], by simp, .nil⟩
      · rw [if_neg hr] at h
        exact absurd h (by simp)
  | cons kid kids ihk =>
      intro rhs toks hh h
      obtain ⟨hsplit, _⟩ := leadingLits_spec rhs
      have hkid : kid.height < N := by simp only [heights] at hh; omega
      have hkids : heights kids < N := by simp only [heights] at hh; omega
      unfold printItems at h
      generalize (leadingLits rhs).1 = ls at hsplit h
      generalize (leadingLits rhs).2 = r at hsplit h
      subst hsplit
      match r, kid with
      | .tok c :: rest, .leaf c' x =>
          simp only at h
          by_cases hcond : (c == c' && g.tokenSorts.contains c && g.inSort c x) = true
          · rw [if_pos hcond] at h
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨⟨rfl, hc⟩, hx⟩ := hcond
            cases hp : printItems g rest kids with
            | none => simp [hp] at h
            | some toks' =>
                simp only [hp, Option.some.injEq] at h
                subst h
                exact (derivesItems_lits g _ _ _ _).mpr
                  ⟨x :: toks', rfl, .tok c x hc hx (ihk rest toks' hkids hp)⟩
          · rw [if_neg hcond] at h
            exact absurd h (by simp)
      | .tok c :: rest, .node _ _ => simp at h
      | .nt n :: rest, .leaf _ _ => simp at h
      | .nt n :: rest, .node l ks =>
          simp only at h
          cases hpt : printTree g (.node l ks) with
          | none => simp [hpt] at h
          | some pr =>
              obtain ⟨s, sub⟩ := pr
              simp only [hpt] at h
              by_cases hs : (s == n) = true
              · rw [if_pos hs] at h
                simp only [beq_iff_eq] at hs
                subst hs
                cases hp : printItems g rest kids with
                | none => simp [hp] at h
                | some toks' =>
                    simp only [hp, Option.some.injEq] at h
                    subst h
                    refine (derivesItems_lits g _ _ _ _).mpr ⟨sub ++ toks', by simp, ?_⟩
                    exact .nt s (ih _ s sub hkid hpt) (ihk rest toks' hkids hp)
              · rw [if_neg hs] at h
                exact absurd h (by simp)
      | [], _ => simp at h
      | .lit _ :: _, _ => simp at h
      | .eof :: _, _ => simp at h

/-- Soundness of the check: a tree that prints to `toks` at `sort` is a derivation. -/
theorem printTree_sound (g : Grammar) :
    ∀ (t : Tree) (s : String) (toks : List String),
      printTree g t = some (s, toks) → Derives g s toks t := by
  suffices key : ∀ N (t : Tree) (s : String) (toks : List String),
      t.height < N → printTree g t = some (s, toks) → Derives g s toks t by
    intro t s toks h
    exact key (t.height + 1) t s toks (Nat.lt_succ_self _) h
  intro N
  induction N with
  | zero => intro t _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
      intro t s toks hh h
      cases t with
      | leaf c x =>
          unfold printTree at h
          by_cases hcond : (g.tokenSorts.contains c && g.inSort c x) = true
          · rw [if_pos hcond] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Bool.and_eq_true] at hcond
            exact .leaf c x hcond.1 hcond.2
          · rw [if_neg hcond] at h
            exact absurd h (by simp)
      | node label kids =>
          unfold printTree at h
          cases hp : g.prodOf? label with
          | none => simp [hp] at h
          | some p =>
              cases hi : printItems g p.rhs kids with
              | none => simp [hp, hi] at h
              | some toks' =>
                  simp only [hp, hi, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hlabel : p.label = label := by
                    unfold Grammar.prodOf? at hp
                    split at hp
                    · rename_i q hq
                      simp only [Option.some.injEq] at hp
                      subst hp
                      have : q ∈ g.prods.filter (·.label == label) := by simp [hq]
                      simpa using (List.mem_filter.mp this).2
                    · simp at hp
                  have hkids : heights kids < N := by simp only [Tree.height] at hh; omega
                  have hitems := printItems_sound g (N := N) (fun t s toks ht h => ih t s toks ht h)
                    kids p.rhs toks' hkids hi
                  have hd := Derives.node p (hlabel ▸ hp) toks' kids hitems
                  rwa [hlabel] at hd

/-- A grammar is well formed when no production asks for a phrase of a token sort: token sorts
appear in productions only as `tok` items. (Lowering authored rows produces exactly this.) -/
def WellFormed (g : Grammar) : Prop :=
  ∀ p ∈ g.prods, ∀ n, Sym.nt n ∈ p.rhs → g.tokenSorts.contains n = false

/-- Completeness of the check, items level, given completeness for smaller trees. -/
theorem printItems_complete (g : Grammar) {N : Nat}
    (ih : ∀ t s toks, t.height < N → Derives g s toks t → printTree g t = some (s, toks)) :
    ∀ (kids : List Tree) (rhs : List Sym) (toks : List String),
      (∀ n, Sym.nt n ∈ rhs → g.tokenSorts.contains n = false) →
      heights kids < N → DerivesItems g rhs toks kids → printItems g rhs kids = some toks := by
  intro kids
  induction kids with
  | nil =>
      intro rhs toks _ _ h
      obtain ⟨hsplit, hnolit⟩ := leadingLits_spec rhs
      rw [hsplit] at h
      obtain ⟨toks', rfl, h'⟩ := (derivesItems_lits g _ _ _ _).mp h
      unfold printItems
      generalize hr : (leadingLits rhs).2 = r at h' hnolit
      cases h' with
      | nil => simp
      | lit s _ => exact absurd rfl (hnolit s _)
  | cons kid kids ihk =>
      intro rhs toks hnt hh h
      have hkid : kid.height < N := by simp only [heights] at hh; omega
      have hkids : heights kids < N := by simp only [heights] at hh; omega
      obtain ⟨hsplit, hnolit⟩ := leadingLits_spec rhs
      have h0 := h
      rw [hsplit] at h0
      obtain ⟨toks', rfl, h'⟩ := (derivesItems_lits g _ _ _ _).mp h0
      have hnt2 : ∀ n, Sym.nt n ∈ (leadingLits rhs).2 → g.tokenSorts.contains n = false := by
        intro n hn
        apply hnt n
        rw [hsplit]
        exact List.mem_append_right _ hn
      unfold printItems
      generalize hr : (leadingLits rhs).2 = r at h' hnolit hnt2
      cases h' with
      | lit s _ => exact absurd rfl (hnolit s _)
      | @tok c x rest toks'' kids' hc hx hrest =>
          have hnt' : ∀ n, Sym.nt n ∈ rest → g.tokenSorts.contains n = false :=
            fun n hn => hnt2 n (List.mem_cons_of_mem _ hn)
          have hcm : c ∈ g.tokenSorts := by simpa using hc
          simp [hcm, hx, ihk rest toks'' hnt' hkids hrest]
      | @nt n sub t rest toks'' kids' hsub hrest =>
          have hnt' : ∀ m, Sym.nt m ∈ rest → g.tokenSorts.contains m = false :=
            fun m hm => hnt2 m (List.mem_cons_of_mem _ hm)
          have hntn : g.tokenSorts.contains n = false := hnt2 n List.mem_cons_self
          have hpt := ih kid n sub hkid hsub
          cases kid with
          | leaf c x =>
              cases hsub with
              | leaf _ _ hc _ =>
                rw [hntn] at hc
                exact Bool.noConfusion hc
          | node l ks => simp [hpt, ihk rest toks'' hnt' hkids hrest]

/-- Completeness of the check: in a well-formed grammar every derivation prints back to exactly its
tokens at its sort. -/
theorem printTree_complete (g : Grammar) (wf : WellFormed g) :
    ∀ (t : Tree) (s : String) (toks : List String),
      Derives g s toks t → printTree g t = some (s, toks) := by
  suffices key : ∀ N (t : Tree) (s : String) (toks : List String),
      t.height < N → Derives g s toks t → printTree g t = some (s, toks) by
    intro t s toks h
    exact key (t.height + 1) t s toks (Nat.lt_succ_self _) h
  intro N
  induction N with
  | zero => intro t _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
      intro t s toks hh h
      cases h with
      | leaf c x hc hx =>
          unfold printTree
          simp only [hc, hx, Bool.and_self, ↓reduceIte]
      | node p hp toks kids items =>
          have hkids : heights kids < N := by simp only [Tree.height] at hh; omega
          have hmem : p ∈ g.prods := by
            unfold Grammar.prodOf? at hp
            split at hp
            · rename_i q hq
              simp only [Option.some.injEq] at hp
              subst hp
              have : q ∈ g.prods.filter (·.label == q.label) := by simp [hq]
              exact (List.mem_filter.mp this).1
            · simp at hp
          have hitems := printItems_complete g (N := N) (fun t s toks ht h => ih t s toks ht h)
            kids p.rhs toks (wf p hmem) hkids items
          unfold printTree
          simp [hp, hitems]

/-- The check and the derivation relation agree, both ways. -/
theorem printTree_iff (g : Grammar) (wf : WellFormed g) (t : Tree) (s : String)
    (toks : List String) : printTree g t = some (s, toks) ↔ Derives g s toks t :=
  ⟨printTree_sound g t s toks, printTree_complete g wf t s toks⟩

theorem check_iff (g : Grammar) (wf : WellFormed g) (t : Tree) (s : String) (toks : List String) :
    check g s toks t = true ↔ Derives g s toks t := by
  unfold check
  rw [beq_iff_eq]
  exact printTree_iff g wf t s toks

/-! ## Controls -/

private def gAB : Grammar :=
  { prods := [{ label := "more", lhs := "s", rhs := [.lit "a", .nt "s"] },
              { label := "end", lhs := "s", rhs := [.lit "b"] },
              { label := "named", lhs := "s", rhs := [.lit "n", .tok "id"] }],
    tokenSorts := ["id"], inSort := fun c x => c == "id" && x != "a" && x != "b" && x != "n" }

/-- Positive control: `more (end)` prints to `a b`. -/
theorem control_prints : printTree gAB (.node "more" [.node "end" []]) = some ("s", ["a", "b"]) := by
  decide

/-- Positive control: a token leaf of the sort `id`. -/
theorem control_leaf : check gAB "s" ["n", "x"] (.node "named" [.leaf "id" "x"]) = true := by decide

/-- Negative control: a node missing its phrase child prints nothing. -/
theorem control_missing_child : printTree gAB (.node "more" []) = none := by decide

/-- Negative control: a leaf whose text is not a token of its sort. -/
theorem control_bad_leaf : printTree gAB (.node "named" [.leaf "id" "a"]) = none := by decide

/-- Negative control: a tree that prints to other tokens fails the check. -/
theorem control_other_tokens :
    check gAB "s" ["a", "a", "b"] (.node "more" [.node "end" []]) = false := by
  decide

end Mettapedia.GSLT.Readers.TreeCheck
