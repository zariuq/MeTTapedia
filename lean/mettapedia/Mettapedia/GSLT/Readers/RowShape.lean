import Mettapedia.OSLF.Framework.GrammarDerives

/-!
# What a grammar row contributes to derivations

`GrammarDerives.Derives` reads a row through three things only: its label (the node of the
tree), its category (the sort it derives), and, item by item, either a terminal spelling or the
sort of the parameter a nonterminal item names. Parameter names are binders local to the row.

`rowShape` keeps exactly those three things. Two grammars whose rows have the same shapes derive
the same trees from the same tokens (`derives_iff_of_shapes`), and a grammar that has, for each row
of another, a row of the same shape derives at least what the other derives
(`derives_of_simulates`).

Example: the rows `f . x:A |- "f" x : B` and `f . y:A |- "f" y : B` have one shape, so
renaming `x` to `y` changes no derivation. Negative example: `f . x:A |- "f" x : B` and
`f . x:C |- "f" x : B` differ in shape (`A` against `C`), and `shape_changes_derivations` exhibits a
derivation one grammar has and the other lacks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.RowShape

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

/-- One syntax item as a derivation reads it: a terminal spelling, the sort of the named parameter,
or nothing (an item the derivation relation does not cover, or an unknown parameter). -/
def itemShape (r : GrammarRule) : SyntaxItem → Option (String ⊕ String)
  | .terminal tok => some (.inl tok)
  | .nonTerminal name => (paramSort? r name).map Sum.inr
  | _ => none

/-- A row as a derivation reads it. -/
def rowShape (r : GrammarRule) : String × String × List (Option (String ⊕ String)) :=
  (r.label, r.category, r.syntaxPattern.map (itemShape r))

/-- `lang'` has, for every row of `lang`, a row with the same shape. -/
def Simulates (lang lang' : LanguageDef) : Prop :=
  ∀ r ∈ lang.terms, ∃ r' ∈ lang'.terms, rowShape r' = rowShape r

/-- Items with the same shapes derive the same tokens and children, given that every child
derivation transfers. -/
theorem items_transfer {lang lang' : LanguageDef} {r r' : GrammarRule} {N : Nat}
    (hrec : ∀ (sort : String) (sub : List String) (tree : Pattern),
      patternHeight tree < N → Derives lang sort sub tree → Derives lang' sort sub tree) :
    ∀ (items items' : List SyntaxItem) (toks : List String) (kids : List Pattern),
      items.map (itemShape r) = items'.map (itemShape r') →
      patternsHeight kids < N →
      DerivesItems lang r items toks kids → DerivesItems lang' r' items' toks kids
  | [], [], _, _, _, _, h => by cases h; exact .nil r'
  | [], _ :: _, _, _, hshape, _, _ => by simp at hshape
  | _ :: _, [], _, _, hshape, _, _ => by simp at hshape
  | .terminal tok :: rest, item' :: rest', _, kids, hshape, hheight, h => by
      cases h
      rename_i toks' h'
      simp only [List.map_cons, List.cons.injEq] at hshape
      obtain ⟨hhead, htail⟩ := hshape
      cases item' with
      | terminal tok' =>
          simp only [itemShape, Option.some.injEq, Sum.inl.injEq] at hhead
          subst hhead
          exact .terminal r' tok rest' toks' kids
            (items_transfer hrec rest rest' toks' kids htail hheight h')
      | nonTerminal name' =>
          cases hps : paramSort? r' name' <;> simp [itemShape, hps] at hhead
      | separator _ => simp [itemShape] at hhead
      | delimiter _ _ => simp [itemShape] at hhead
      | op _ => simp [itemShape] at hhead
  | .nonTerminal name :: rest, item' :: rest', _, _, hshape, hheight, h => by
      cases h
      rename_i sort sub tree hsub toks' kids' hps h'
      simp only [List.map_cons, List.cons.injEq] at hshape
      obtain ⟨hhead, htail⟩ := hshape
      have hheight' : max (patternHeight tree) (patternsHeight kids') < N := by
        simpa [patternsHeight] using hheight
      have htree : patternHeight tree < N := lt_of_le_of_lt (le_max_left _ _) hheight'
      have hkids : patternsHeight kids' < N := lt_of_le_of_lt (le_max_right _ _) hheight'
      cases item' with
      | terminal tok' => simp [itemShape, hps] at hhead
      | nonTerminal name' =>
          have hps' : paramSort? r' name' = some sort := by
            cases hq : paramSort? r' name' <;> simp [itemShape, hps, hq] at hhead
            simp [hhead]
          exact .nonTerminal r' name' sort hps' sub tree (hrec sort sub tree htree hsub)
            rest' toks' kids' (items_transfer hrec rest rest' toks' kids' htail hkids h')
      | separator _ => simp [itemShape, hps] at hhead
      | delimiter _ _ => simp [itemShape, hps] at hhead
      | op _ => simp [itemShape, hps] at hhead
  | .separator _ :: _, _ :: _, _, _, _, _, h => by cases h
  | .delimiter _ _ :: _, _ :: _, _, _, _, _, h => by cases h
  | .op _ :: _, _ :: _, _, _, _, _, h => by cases h

/-- Derivations transfer along a simulation of rows, by induction on the height of the tree. -/
theorem derives_of_simulates {lang lang' : LanguageDef} (hsim : Simulates lang lang') :
    ∀ (sort : String) (toks : List String) (tree : Pattern),
      Derives lang sort toks tree → Derives lang' sort toks tree := by
  suffices key : ∀ (N : Nat) (sort : String) (toks : List String) (tree : Pattern),
      patternHeight tree < N → Derives lang sort toks tree → Derives lang' sort toks tree by
    intro sort toks tree h
    exact key (patternHeight tree + 1) sort toks tree (Nat.lt_succ_self _) h
  intro N
  induction N with
  | zero => intro _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ih =>
      intro sort toks tree hlt h
      cases h
      rename_i r hr kids hsort hitems
      obtain ⟨r', hr', hshape⟩ := hsim r hr
      simp only [rowShape, Prod.mk.injEq] at hshape
      obtain ⟨hlabel, hcat, hitemsShape⟩ := hshape
      have hkids : patternsHeight kids < N := by
        simp only [patternHeight] at hlt
        omega
      have hitems' := items_transfer (r := r) (r' := r') (N := N)
        (fun s sub t ht hd => ih s sub t ht hd)
        r.syntaxPattern r'.syntaxPattern toks kids hitemsShape.symm hkids hitems
      rw [← hlabel]
      exact .rule r' hr' sort (hcat.trans hsort) toks kids hitems'

/-- Grammars whose rows have the same shapes, in any order, derive exactly the same trees. -/
theorem derives_iff_of_simulates {lang lang' : LanguageDef}
    (h₁ : Simulates lang lang') (h₂ : Simulates lang' lang)
    (sort : String) (toks : List String) (tree : Pattern) :
    Derives lang sort toks tree ↔ Derives lang' sort toks tree :=
  ⟨derives_of_simulates h₁ sort toks tree, derives_of_simulates h₂ sort toks tree⟩

/-- Equal shape lists give simulations both ways. -/
theorem simulates_of_shapes {lang lang' : LanguageDef}
    (h : lang.terms.map rowShape = lang'.terms.map rowShape) : Simulates lang lang' := by
  intro r hr
  have hmem : rowShape r ∈ lang'.terms.map rowShape := h ▸ List.mem_map_of_mem hr
  obtain ⟨r', hr', heq⟩ := List.mem_map.mp hmem
  exact ⟨r', hr', heq⟩

theorem derives_iff_of_shapes {lang lang' : LanguageDef}
    (h : lang.terms.map rowShape = lang'.terms.map rowShape)
    (sort : String) (toks : List String) (tree : Pattern) :
    Derives lang sort toks tree ↔ Derives lang' sort toks tree :=
  derives_iff_of_simulates (simulates_of_shapes h) (simulates_of_shapes h.symm) sort toks tree

/-! ## Controls -/

private def rowX : GrammarRule :=
  { label := "f", category := "B", params := [.simple "x" (.base "A")],
    syntaxPattern := [.terminal "f", .nonTerminal "x"] }
private def rowY : GrammarRule :=
  { label := "f", category := "B", params := [.simple "y" (.base "A")],
    syntaxPattern := [.terminal "f", .nonTerminal "y"] }
private def rowC : GrammarRule :=
  { label := "f", category := "B", params := [.simple "x" (.base "C")],
    syntaxPattern := [.terminal "f", .nonTerminal "x"] }
private def atomA : GrammarRule :=
  { label := "a", category := "A", params := [], syntaxPattern := [.terminal "a"] }

private def langX : LanguageDef := { name := "x", types := [], terms := [rowX, atomA], equations := [], rewrites := [] }
private def langY : LanguageDef := { name := "y", types := [], terms := [rowY, atomA], equations := [], rewrites := [] }
private def langC : LanguageDef := { name := "c", types := [], terms := [rowC, atomA], equations := [], rewrites := [] }

/-- Positive control: renaming the parameter keeps every row's shape. -/
theorem renaming_keeps_shapes : langX.terms.map rowShape = langY.terms.map rowShape := by decide

private theorem langX_derives_fa : Derives langX "B" ["f", "a"] (.apply "f" [.apply "a" []]) := by
  refine .rule rowX (by simp [langX]) "B" rfl ["f", "a"] [.apply "a" []] ?_
  refine .terminal rowX "f" [.nonTerminal "x"] ["a"] [.apply "a" []] ?_
  have hsub : Derives langX "A" ["a"] (.apply "a" []) :=
    .rule atomA (by simp [langX]) "A" rfl ["a"] [] (.terminal atomA "a" [] [] [] (.nil atomA))
  have := DerivesItems.nonTerminal rowX "x" "A" (by decide) ["a"] (.apply "a" []) hsub [] [] []
    (.nil rowX)
  simpa using this

/-- The renamed grammar derives the same text, transported by the shape theorem. -/
theorem renaming_keeps_derivation : Derives langY "B" ["f", "a"] (.apply "f" [.apply "a" []]) :=
  (derives_iff_of_shapes renaming_keeps_shapes _ _ _).mp langX_derives_fa

/-- Negative control: changing a parameter's sort changes the shape. -/
theorem sort_change_changes_shape : langX.terms.map rowShape ≠ langC.terms.map rowShape := by
  decide

/-- Negative control: and the derivation is gone (`"f" "a"` needs an `A` where `langC` wants a
`C`, which nothing derives). -/
private theorem langC_nothing_at_C (toks : List String) (tree : Pattern) :
    ¬ Derives langC "C" toks tree := by
  intro h
  cases h
  rename_i r hr kids hsort hitems
  simp only [langC, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp [rowC] at hsort
  · simp [atomA] at hsort

theorem shape_changes_derivations (toks : List String) (tree : Pattern) :
    ¬ Derives langC "B" toks tree := by
  intro h
  cases h
  rename_i r hr kids hsort hitems
  simp only [langC, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · cases hitems
    rename_i toks' h'
    cases h'
    rename_i sort sub sub_tree hsub toks'' kids'' hps h''
    have hsort' : sort = "C" := by
      simp [paramSort?, rowC] at hps
      exact hps.symm
    subst hsort'
    exact langC_nothing_at_C sub sub_tree hsub
  · simp [atomA] at hsort

end Mettapedia.GSLT.Readers.RowShape
