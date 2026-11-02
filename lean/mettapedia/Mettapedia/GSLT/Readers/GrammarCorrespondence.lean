import Mettapedia.GSLT.Readers.TreeCheck
import Mettapedia.OSLF.Framework.GrammarDerives

/-!
# The reader's derivations are the authored rows' derivations

A reader works with the *lowered* grammar: each authored row of a `LanguageDef` becomes a
production whose items are fixed spellings, token sorts and phrase sorts (`SLR.lowerRow`). The
authored rows themselves derive text through `GrammarDerives.Derives`, where a token sort (a sort
with no rows) derives nothing on its own.

This module adds, for the tokens of one input, a *leaf row* per token sort and token
(`leaf:SORT:TEXT . |- "TEXT" : SORT`), and proves that a reader tree is a token-level derivation
of the lowered grammar exactly when its pattern is a `GrammarDerives` derivation of the authored rows
with those leaf rows (`derives_iff_grammarDerives`).

Example: with the row `named . x:id |- "n" x : s` and the token `x`, the reader tree
`node "named" [leaf "id" "x"]` is the pattern `named (leaf:id:x)`, derived from the authored row
and the leaf row of `x`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.GrammarCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives (paramSort?)
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TreeCheck

/-- `GrammarDerives.Derives`, the derivation relation of authored rows. -/
abbrev GDerives := @Mettapedia.OSLF.Framework.GrammarDerives.Derives
/-- `GrammarDerives.DerivesItems`. -/
abbrev GDerivesItems := @Mettapedia.OSLF.Framework.GrammarDerives.DerivesItems

/-- The label of the leaf row for token `x` of sort `c`. -/
def leafLabel (c x : String) : String := "leaf:" ++ c ++ ":" ++ x

def leafRow (c x : String) : GrammarRule :=
  { label := leafLabel c x, category := c, params := [], syntaxPattern := [.terminal x] }

/-- The authored rows with the leaf rows of the given tokens. -/
def withLeaves (lang : LanguageDef) (tokenSorts : List String) (inSort : String → String → Bool)
    (toks : List String) : LanguageDef :=
  { lang with terms := lang.terms ++
      (tokenSorts.flatMap fun c => (toks.filter (inSort c)).map (leafRow c)) }

/-- A reader tree as a `GrammarDerives` tree. -/
def toPattern : Tree → Pattern
  | .leaf c x => .apply (leafLabel c x) []
  | .node label kids => .apply label (kids.attach.map fun ⟨k, _⟩ => toPattern k)

theorem toPattern_leaf (c x : String) : toPattern (.leaf c x) = .apply (leafLabel c x) [] := by
  simp [toPattern]

theorem toPattern_node (label : String) (kids : List Tree) :
    toPattern (.node label kids) = .apply label (kids.map toPattern) := by
  simp only [toPattern]
  congr 1
  exact List.attach_map_subtype_val kids |>.symm ▸ by simp

theorem mapM_cons_some {α β : Type} (f : α → Option β) (x : α) (xs : List α) (ys : List β)
    (h : (x :: xs).mapM f = some ys) :
    ∃ y rest, f x = some y ∧ xs.mapM f = some rest ∧ ys = y :: rest := by
  simp only [List.mapM_cons] at h
  cases hx : f x with
  | none => simp [hx] at h
  | some y =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some rest =>
          simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          exact ⟨y, rest, rfl, rfl, h.symm⟩

theorem mem_of_mapM {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h, y, hy => by simp at h; subst h; simp at hy
  | x :: xs, ys, h, y, hy => by
      obtain ⟨y0, rest, hx, hrest, rfl⟩ := mapM_cons_some f x xs ys h
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact ⟨x, List.mem_cons_self, hx⟩
      · obtain ⟨x', hx', hfx'⟩ := mem_of_mapM f xs rest hrest y hy'
        exact ⟨x', List.mem_cons_of_mem _ hx', hfx'⟩

theorem mapM_of_mem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], ys, h, x, hx => by simp at hx
  | x :: xs, ys, h, x', hx' => by
      obtain ⟨y0, rest, hx, hrest, rfl⟩ := mapM_cons_some f x xs ys h
      rcases List.mem_cons.mp hx' with rfl | hx''
      · exact ⟨y0, List.mem_cons_self, hx⟩
      · obtain ⟨y', hy', hfy'⟩ := mapM_of_mem f xs rest hrest x' hx''
        exact ⟨y', List.mem_cons_of_mem _ hy', hfy'⟩

/-! ## The setting -/

/-- Authored rows, their token sorts, token membership, and their lowering. -/
structure Setting where
  lang : LanguageDef
  tokenSorts : List String
  inSort : String → String → Bool
  prods : List Prod
  lowering : lang.terms.mapM (lowerRow tokenSorts) = some prods

def Setting.grammar (S : Setting) : Grammar :=
  { prods := S.prods, tokenSorts := S.tokenSorts, inSort := S.inSort }

/-- The authored rows with the leaf rows of the tokens `toks`. -/
def Setting.leaves (S : Setting) (toks : List String) : LanguageDef :=
  withLeaves S.lang S.tokenSorts S.inSort toks

theorem leafRow_mem (S : Setting) {toks : List String} {c x : String}
    (hc : S.tokenSorts.contains c = true) (hx : S.inSort c x = true) (hxt : x ∈ toks) :
    leafRow c x ∈ (S.leaves toks).terms := by
  simp only [Setting.leaves, withLeaves, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  right
  exact ⟨c, by simpa using hc, x, ⟨hxt, hx⟩, rfl⟩

theorem authored_mem (S : Setting) {toks : List String} {r : GrammarRule}
    (hr : r ∈ S.lang.terms) : r ∈ (S.leaves toks).terms := by
  simp only [Setting.leaves, withLeaves, List.mem_append]
  exact Or.inl hr

/-! ## Soundness: a reader derivation is a derivation of the authored rows with leaf rows -/

theorem items_sound (S : Setting) (toks : List String) {N : Nat}
    (ih : ∀ t s sub, t.height < N → (∀ x ∈ sub, x ∈ toks) →
      Derives S.grammar s sub t → GDerives (S.leaves toks) s sub (toPattern t))
    (r : GrammarRule) :
    ∀ (items : List SyntaxItem) (rhs : List Sym) (sub : List String) (kids : List Tree),
      items.mapM (lowerItem S.tokenSorts r) = some rhs → heights kids < N →
      (∀ x ∈ sub, x ∈ toks) → DerivesItems S.grammar rhs sub kids →
      GDerivesItems (S.leaves toks) r items sub (kids.map toPattern)
  | [], rhs, sub, kids, hl, _, _, h => by
      simp at hl
      subst hl
      cases h
      exact .nil r
  | item :: items, rhs, sub, kids, hl, hk, hsub, h => by
      obtain ⟨sym, rest, hsym, hrest, rfl⟩ := mapM_cons_some _ item items rhs hl
      cases item with
      | terminal tok =>
          simp only [lowerItem, Option.some.injEq] at hsym
          subst hsym
          cases h with
          | lit _ h' =>
              rename_i sub'
              exact .terminal r tok items sub' _
                (items_sound S toks ih r items rest sub' kids hrest hk
                  (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) h')
      | nonTerminal name =>
          simp only [lowerItem] at hsym
          cases hps : paramSort? r name with
          | none => simp [hps] at hsym
          | some srt =>
              simp only [hps, Option.map_some, Option.some.injEq] at hsym
              by_cases hT : S.tokenSorts.contains srt = true
              · simp only [hT, ↓reduceIte] at hsym
                subst hsym
                cases h with
                | @tok _ x rest' sub' kids' hc hx h' =>
                    have hxt : x ∈ toks := hsub x List.mem_cons_self
                    have hleaf : GDerives (S.leaves toks) srt [x] (toPattern (.leaf srt x)) := by
                      rw [toPattern_leaf]
                      exact .rule (leafRow srt x) (leafRow_mem S hc hx hxt) srt rfl [x] []
                        (.terminal (leafRow srt x) x [] [] [] (.nil _))
                    have hk' : heights kids' < N := by simp only [heights] at hk; omega
                    have := Mettapedia.OSLF.Framework.GrammarDerives.DerivesItems.nonTerminal r name srt hps [x] (toPattern (.leaf srt x))
                      hleaf items sub' (kids'.map toPattern)
                      (items_sound S toks ih r items rest sub' kids' hrest hk'
                        (fun y hy => hsub y (List.mem_cons_of_mem _ hy)) h')
                    simpa using this
              · simp only [hT, Bool.false_eq_true, ↓reduceIte] at hsym
                subst hsym
                cases h with
                | @nt _ sub0 t rest' sub' kids' hd h' =>
                    have ht : t.height < N := by simp only [heights] at hk; omega
                    have hk' : heights kids' < N := by simp only [heights] at hk; omega
                    have hsub0 : ∀ x ∈ sub0, x ∈ toks := fun x hx => hsub x (List.mem_append_left _ hx)
                    have hsub' : ∀ x ∈ sub', x ∈ toks := fun x hx => hsub x (List.mem_append_right _ hx)
                    exact .nonTerminal r name srt hps sub0 (toPattern t) (ih t srt sub0 ht hsub0 hd)
                      items sub' (kids'.map toPattern)
                      (items_sound S toks ih r items rest sub' kids' hrest hk' hsub' h')
      | separator _ => simp [lowerItem] at hsym
      | delimiter _ _ => simp [lowerItem] at hsym
      | op _ => simp [lowerItem] at hsym

theorem prodOf_lowered (S : Setting) {label : String} {p : Prod}
    (hp : S.grammar.prodOf? label = some p) :
    ∃ r ∈ S.lang.terms, lowerRow S.tokenSorts r = some p ∧ p.label = label := by
  unfold Grammar.prodOf? at hp
  split at hp
  · rename_i q hq
    simp only [Option.some.injEq] at hp
    subst hp
    have hmem : q ∈ S.grammar.prods.filter (·.label == label) := by simp [hq]
    obtain ⟨hqmem, hql⟩ := List.mem_filter.mp hmem
    obtain ⟨r, hr, hlow⟩ := mem_of_mapM _ S.lang.terms S.prods S.lowering q hqmem
    exact ⟨r, hr, hlow, by simpa using hql⟩
  · simp at hp

theorem lowerRow_fields {T : List String} {r : GrammarRule} {p : Prod}
    (h : lowerRow T r = some p) :
    p.label = r.label ∧ p.lhs = r.category ∧ r.syntaxPattern.mapM (lowerItem T r) = some p.rhs := by
  unfold lowerRow at h
  cases hm : r.syntaxPattern.mapM (lowerItem T r) with
  | none => simp [hm] at h
  | some rhs =>
      simp only [hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩

/-- **Soundness.** A reader derivation of the lowered grammar is a `GrammarDerives` derivation of
the authored rows with the leaf rows of the input's tokens. -/
theorem derives_sound (S : Setting) (toks : List String) :
    ∀ (t : Tree) (s : String) (sub : List String), (∀ x ∈ sub, x ∈ toks) →
      Derives S.grammar s sub t → GDerives (S.leaves toks) s sub (toPattern t) := by
  suffices key : ∀ N (t : Tree) (s : String) (sub : List String), t.height < N →
      (∀ x ∈ sub, x ∈ toks) →
      Derives S.grammar s sub t → GDerives (S.leaves toks) s sub (toPattern t) by
    intro t s sub hsub h
    exact key (t.height + 1) t s sub (Nat.lt_succ_self _) hsub h
  intro N
  induction N with
  | zero => intro t _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
      intro t s sub hh hsub h
      cases h with
      | leaf _ x hc hx =>
          rw [toPattern_leaf]
          exact .rule (leafRow s x) (leafRow_mem S hc hx (hsub x List.mem_cons_self)) s rfl [x] []
            (.terminal (leafRow s x) x [] [] [] (.nil _))
      | node p hp sub kids items =>
          obtain ⟨r, hr, hlow, _⟩ := prodOf_lowered S hp
          obtain ⟨hlabel, hlhs, hrhs⟩ := lowerRow_fields hlow
          have hkids : heights kids < N := by simp only [Tree.height] at hh; omega
          have hitems := items_sound S toks (N := N) (fun t s sub ht hs hd => ih t s sub ht hs hd)
            r r.syntaxPattern p.rhs sub kids hrhs hkids hsub items
          rw [toPattern_node, hlabel, hlhs]
          exact .rule r (authored_mem S hr) r.category rfl sub (kids.map toPattern) hitems

/-! ## Completeness: every derivation of the authored rows with leaf rows is a reader derivation -/

open Mettapedia.OSLF.Framework.GrammarDerives (patternHeight patternsHeight) in
/-- What completeness needs of the authored rows: token sorts have no rows, and each production
is the one its label names. -/
structure Setting.Admissible (S : Setting) : Prop where
  token_sorts_have_no_rows : ∀ r ∈ S.lang.terms, S.tokenSorts.contains r.category = false
  labels_name_productions : ∀ p ∈ S.prods, S.grammar.prodOf? p.label = some p

theorem leaf_rows_only (S : Setting) (adm : S.Admissible) :
    ∀ (s : String) (sub : List String) (t : Tree), S.tokenSorts.contains s = true →
      Derives S.grammar s sub t → ∃ x, t = .leaf s x ∧ sub = [x] ∧ S.inSort s x = true := by
  intro s sub t hs h
  cases h with
  | leaf _ x hc hx => exact ⟨x, rfl, rfl, hx⟩
  | node p hp sub kids items =>
      obtain ⟨r, hr, hlow, _⟩ := prodOf_lowered S hp
      obtain ⟨_, hlhs, _⟩ := lowerRow_fields hlow
      have := adm.token_sorts_have_no_rows r hr
      rw [← hlhs, hs] at this
      exact absurd this (by decide)

open Mettapedia.OSLF.Framework.GrammarDerives (patternHeight patternsHeight) in
theorem items_complete (S : Setting) (adm : S.Admissible) (toks : List String) {N : Nat}
    (ih : ∀ (P : Pattern) (s : String) (sub : List String), patternHeight P < N →
      GDerives (S.leaves toks) s sub P → ∃ t, toPattern t = P ∧ Derives S.grammar s sub t)
    (r : GrammarRule) :
    ∀ (items : List SyntaxItem) (rhs : List Sym) (sub : List String) (kids : List Pattern),
      items.mapM (lowerItem S.tokenSorts r) = some rhs → patternsHeight kids < N →
      GDerivesItems (S.leaves toks) r items sub kids →
      ∃ trees : List Tree, trees.map toPattern = kids ∧ DerivesItems S.grammar rhs sub trees
  | [], rhs, sub, kids, hl, _, h => by
      simp at hl
      subst hl
      cases h
      exact ⟨[], rfl, .nil⟩
  | item :: items, rhs, sub, kids, hl, hk, h => by
      obtain ⟨sym, rest, hsym, hrest, rfl⟩ := mapM_cons_some _ item items rhs hl
      cases item with
      | terminal tok =>
          simp only [lowerItem, Option.some.injEq] at hsym
          subst hsym
          cases h with
          | terminal _ _ _ sub' _ h' =>
              obtain ⟨trees, htrees, hd⟩ := items_complete S adm toks ih r items rest sub' kids hrest hk h'
              exact ⟨trees, htrees, .lit tok hd⟩
      | nonTerminal name =>
          simp only [lowerItem] at hsym
          cases hps : paramSort? r name with
          | none => simp [hps] at hsym
          | some srt =>
              simp only [hps, Option.map_some, Option.some.injEq] at hsym
              cases h with
              | nonTerminal _ _ srt' hps' sub0 P0 hsub _ sub' kids' h' =>
                  have hsrt : srt' = srt := by rw [hps] at hps'; exact (Option.some.inj hps').symm
                  subst hsrt
                  have hP0 : patternHeight P0 < N := by
                    simp only [patternsHeight] at hk; omega
                  have hk' : patternsHeight kids' < N := by
                    simp only [patternsHeight] at hk; omega
                  obtain ⟨t0, ht0, hd0⟩ := ih P0 srt' sub0 hP0 hsub
                  obtain ⟨trees, htrees, hd⟩ :=
                    items_complete S adm toks ih r items rest sub' kids' hrest hk' h'
                  by_cases hT : S.tokenSorts.contains srt' = true
                  · simp only [hT, ↓reduceIte] at hsym
                    subst hsym
                    obtain ⟨x, rfl, rfl, hx⟩ := leaf_rows_only S adm srt' sub0 t0 hT hd0
                    exact ⟨.leaf srt' x :: trees, by simp [ht0, htrees], .tok srt' x hT hx hd⟩
                  · simp only [hT, Bool.false_eq_true, ↓reduceIte] at hsym
                    subst hsym
                    exact ⟨t0 :: trees, by simp [ht0, htrees], .nt srt' hd0 hd⟩
      | separator _ => simp [lowerItem] at hsym
      | delimiter _ _ => simp [lowerItem] at hsym
      | op _ => simp [lowerItem] at hsym

open Mettapedia.OSLF.Framework.GrammarDerives (patternHeight patternsHeight) in
/-- **Completeness.** Every `GrammarDerives` derivation of the authored rows with the leaf rows of
the input's tokens is the image of a reader derivation of the lowered grammar. -/
theorem derives_complete (S : Setting) (adm : S.Admissible) (toks : List String) :
    ∀ (P : Pattern) (s : String) (sub : List String),
      GDerives (S.leaves toks) s sub P → ∃ t, toPattern t = P ∧ Derives S.grammar s sub t := by
  suffices key : ∀ N (P : Pattern) (s : String) (sub : List String), patternHeight P < N →
      GDerives (S.leaves toks) s sub P → ∃ t, toPattern t = P ∧ Derives S.grammar s sub t by
    intro P s sub h
    exact key (patternHeight P + 1) P s sub (Nat.lt_succ_self _) h
  intro N
  induction N with
  | zero => intro P _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
      intro P s sub hh h
      cases h with
      | rule r hr _ hsort _ kids hitems =>
          simp only [Setting.leaves, withLeaves, List.mem_append, List.mem_flatMap, List.mem_map,
            List.mem_filter] at hr
          rcases hr with hr | ⟨c, hc, x, ⟨hxt, hx⟩, rfl⟩
          · obtain ⟨p, hp, hlow⟩ := mapM_of_mem _ S.lang.terms S.prods S.lowering r hr
            obtain ⟨hlabel, hlhs, hrhs⟩ := lowerRow_fields hlow
            have hkids : patternsHeight kids < N := by simp only [patternHeight] at hh; omega
            obtain ⟨trees, htrees, hd⟩ := items_complete S adm toks (N := N)
              (fun P s sub hP hD => ih P s sub hP hD) r r.syntaxPattern p.rhs sub kids hrhs hkids hitems
            refine ⟨.node r.label trees, by rw [toPattern_node, htrees], ?_⟩
            have hpd := Derives.node p (adm.labels_name_productions p hp) sub trees hd
            rw [hlabel, hlhs, hsort] at hpd
            exact hpd
          · cases hitems with
            | terminal _ _ _ sub' _ h' =>
                cases h'
                refine ⟨.leaf c x, by rw [toPattern_leaf]; rfl, ?_⟩
                simp only [leafRow] at hsort
                subst hsort
                exact .leaf c x (by simpa [Setting.grammar] using hc) hx

/-- **The correspondence.** For admissible authored rows and the tokens `toks` of one input: a
reader derivation over those tokens is a derivation of the authored rows with the input's leaf
rows, and every derivation of the authored rows with those leaf rows is the pattern of a reader
derivation. -/
theorem reader_correspondence (S : Setting) (adm : S.Admissible) (toks : List String)
    (s : String) (sub : List String) (hsub : ∀ x ∈ sub, x ∈ toks) :
    (∀ t, Derives S.grammar s sub t → GDerives (S.leaves toks) s sub (toPattern t)) ∧
      (∀ P, GDerives (S.leaves toks) s sub P → ∃ t, toPattern t = P ∧ Derives S.grammar s sub t) :=
  ⟨fun t h => derives_sound S toks t s sub hsub h, fun P h => derives_complete S adm toks P s sub h⟩

end Mettapedia.GSLT.Readers.GrammarCorrespondence
