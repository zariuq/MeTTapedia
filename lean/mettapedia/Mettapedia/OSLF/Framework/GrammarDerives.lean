import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Generic grammar derivability over a `LanguageDef`

`Derives lang sort toks tree` — the parse RELATION of a languageDef's grammar
rows: `toks` derives at `sort` with derivation tree `tree` (constructor
labels = rule labels). This is the framework piece the mode-A/mode-B
equivalence ladder and the per-string uniqueness certificates are stated
against, and — for signature-generated grammars like Metamath's — a
`Derives`-tree at a grammar sort *is* a syntax proof (leaves/nodes are the
generating declaration labels).

v0 domain: `terminal`/`nonTerminal` syntax items only (exactly what
signature-derived grammars emit). Rules using separators/delimiters/ops are
simply not derivable through v0 — a domain gate, not a semantics for them.

This is a RELATION, not a parser: parsers (untrusted producers) find trees;
`parse-cert`-style trusted recheck corresponds to checking a `Derives`
witness. Nothing here is language-specific.

`enumDerives` below is the bounded reference enumerator for the relation —
all derivation trees of height ≤ fuel, characterized exactly by
`mem_enumDerives_iff` — whose singleton runs yield per-string uniqueness
certificates (`uniqueDerivationUpTo_of_enum`, and unconditionally
`uniqueDerivation_of_enum` for consuming grammars). It is a certificate
engine, not an efficient parser.
-/

namespace Mettapedia.OSLF.Framework.GrammarDerives

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Sort of a named first-order parameter of a rule. -/
def paramSort? (r : GrammarRule) (n : String) : Option String :=
  r.params.findSome? (fun p =>
    match p with
    | .simple m (.base s) => if m == n then some s else none
    | _ => none)

mutual

inductive Derives (lang : LanguageDef) : String → List String → Pattern → Prop where
  | rule (r : GrammarRule) (hr : r ∈ lang.terms) (sort : String)
      (hsort : r.category = sort) (toks : List String) (kids : List Pattern)
      (hitems : DerivesItems lang r r.syntaxPattern toks kids) :
      Derives lang sort toks (.apply r.label kids)

inductive DerivesItems (lang : LanguageDef) :
    GrammarRule → List SyntaxItem → List String → List Pattern → Prop where
  | nil (r : GrammarRule) : DerivesItems lang r [] [] []
  | terminal (r : GrammarRule) (tok : String) (rest : List SyntaxItem)
      (toks : List String) (kids : List Pattern)
      (h : DerivesItems lang r rest toks kids) :
      DerivesItems lang r (.terminal tok :: rest) (tok :: toks) kids
  | nonTerminal (r : GrammarRule) (n : String) (sort : String)
      (hsort : paramSort? r n = some sort)
      (sub : List String) (tree : Pattern)
      (hsub : Derives lang sort sub tree)
      (rest : List SyntaxItem) (toks : List String) (kids : List Pattern)
      (h : DerivesItems lang r rest toks kids) :
      DerivesItems lang r (.nonTerminal n :: rest) (sub ++ toks) (tree :: kids)

end

/-- Per-string uniqueness — the honest, decidable-per-formula shape of an
"unambiguity" claim (a certificate target, never a decision procedure for the
grammar). -/
def UniqueDerivation (lang : LanguageDef) (sort : String)
    (toks : List String) : Prop :=
  ∀ t₁ t₂, Derives lang sort toks t₁ → Derives lang sort toks t₂ → t₁ = t₂

/-! ## Bounded derivation enumeration

`enumDerives lang fuel sort toks` lists ALL derivation trees of height ≤
`fuel` (repetitions permitted — every meta-theorem is stated via list
membership). The items-level worker `enumDerivesItems` is higher-order in the
sub-enumerator `recur`, which keeps both functions plain structural recursions
(on the item list, resp. on `fuel`): kernel reduction works, so `decide`/`rfl`
certificates go through on concrete languages, and each meta-theorem factors
into an items lemma parametric in a `recur` hypothesis plus a fuel induction —
no mutual induction anywhere. -/

universe u

/-- All ways to split a list into a contiguous prefix and suffix, in order. -/
def splits {α : Type u} : List α → List (List α × List α)
  | [] => [([], [])]
  | a :: as => ([], a :: as) :: (splits as).map (fun p => (a :: p.1, p.2))

theorem splits_sound {α : Type u} :
    ∀ (l : List α) (p : List α × List α), p ∈ splits l → p.1 ++ p.2 = l
  | [], _, hp => by
      simp only [splits, List.mem_singleton] at hp
      simp [hp]
  | a :: as, p, hp => by
      simp only [splits, List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩
      · rfl
      · simp [splits_sound as q hq]

theorem splits_complete {α : Type u} :
    ∀ (pre post : List α), (pre, post) ∈ splits (pre ++ post)
  | [], post => by cases post <;> simp [splits]
  | a :: pre, post => by
      simp only [List.cons_append, splits, List.mem_cons, List.mem_map]
      exact Or.inr ⟨(pre, post), splits_complete pre post, rfl⟩

/-- Items-level enumeration worker, higher-order in the sub-enumerator
`recur` (instantiated with `enumDerives lang fuel` at each rule application).
Mirrors `DerivesItems`: a terminal consumes exactly its token, a nonterminal
tries every prefix/suffix split at the hole's sort, and any item outside the
v0 `terminal`/`nonTerminal` domain contributes nothing. -/
def enumDerivesItems (recur : String → List String → List Pattern)
    (r : GrammarRule) : List SyntaxItem → List String → List (List Pattern)
  | [], [] => [[]]
  | [], _ :: _ => []
  | .terminal _ :: _, [] => []
  | .terminal tok :: rest, tk :: toks =>
      if tk = tok then enumDerivesItems recur r rest toks else []
  | .nonTerminal n :: rest, toks =>
      match paramSort? r n with
      | some sort =>
          (splits toks).flatMap fun s =>
            (recur sort s.1).flatMap fun tree =>
              (enumDerivesItems recur r rest s.2).map (tree :: ·)
      | none => []
  | .separator _ :: _, _ => []
  | .delimiter _ _ :: _, _ => []
  | .op _ :: _, _ => []

/-- Bounded enumeration of ALL `Derives`-trees for `toks` at `sort`: each unit
of fuel admits one more level of rule application. Sound (`enumDerives_sound`),
complete up to fuel (`enumDerives_complete`), and exact
(`mem_enumDerives_iff`). The output list may contain repetitions; theorems are
stated via membership. -/
def enumDerives (lang : LanguageDef) (fuel : Nat) (sort : String)
    (toks : List String) : List Pattern :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      lang.terms.flatMap fun r =>
        if r.category = sort then
          (enumDerivesItems (fun s ts => enumDerives lang fuel s ts) r
            r.syntaxPattern toks).map (Pattern.apply r.label)
        else []

/-! ## Soundness: everything enumerated derives -/

theorem enumDerivesItems_sound {lang : LanguageDef} {r : GrammarRule}
    {recur : String → List String → List Pattern}
    (hrec : ∀ sort sub tree, tree ∈ recur sort sub → Derives lang sort sub tree) :
    ∀ (items : List SyntaxItem) (toks : List String) (kids : List Pattern),
      kids ∈ enumDerivesItems recur r items toks →
      DerivesItems lang r items toks kids
  | [], [], _, h => by
      simp only [enumDerivesItems, List.mem_singleton] at h
      subst h
      exact DerivesItems.nil r
  | [], _ :: _, _, h => by simp [enumDerivesItems] at h
  | .terminal _ :: _, [], _, h => by simp [enumDerivesItems] at h
  | .terminal tok :: rest, tk :: toks, kids, h => by
      simp only [enumDerivesItems] at h
      by_cases htk : tk = tok
      · rw [if_pos htk] at h
        subst htk
        exact DerivesItems.terminal r tk rest toks kids
          (enumDerivesItems_sound hrec rest toks kids h)
      · rw [if_neg htk] at h
        simp at h
  | .nonTerminal n :: rest, toks, kids, h => by
      simp only [enumDerivesItems] at h
      cases hps : paramSort? r n with
      | none => rw [hps] at h; simp at h
      | some sort =>
          rw [hps] at h
          simp only [List.mem_flatMap, List.mem_map] at h
          obtain ⟨s, hs, tree, htree, kids', hkids', rfl⟩ := h
          rw [← splits_sound toks s hs]
          exact DerivesItems.nonTerminal r n sort hps s.1 tree
            (hrec sort s.1 tree htree) rest s.2 kids'
            (enumDerivesItems_sound hrec rest s.2 kids' hkids')
  | .separator _ :: _, _, _, h => by simp [enumDerivesItems] at h
  | .delimiter _ _ :: _, _, _, h => by simp [enumDerivesItems] at h
  | .op _ :: _, _, _, h => by simp [enumDerivesItems] at h

/-- SOUNDNESS: everything the bounded enumerator finds is a derivation. -/
theorem enumDerives_sound (lang : LanguageDef) :
    ∀ (fuel : Nat) (sort : String) (toks : List String) (t : Pattern),
      t ∈ enumDerives lang fuel sort toks → Derives lang sort toks t
  | 0, _, _, _, h => by simp [enumDerives] at h
  | fuel + 1, sort, toks, t, h => by
      simp only [enumDerives, List.mem_flatMap] at h
      obtain ⟨r, hr, ht⟩ := h
      by_cases hcat : r.category = sort
      · rw [if_pos hcat] at ht
        simp only [List.mem_map] at ht
        obtain ⟨kids, hkids, rfl⟩ := ht
        exact Derives.rule r hr sort hcat toks kids
          (enumDerivesItems_sound
            (fun s sub tree hmem => enumDerives_sound lang fuel s sub tree hmem)
            r.syntaxPattern toks kids hkids)
      · rw [if_neg hcat] at ht
        simp at ht

/-! ## Derivation height

`Derives` is a `Prop`, but each derivation node produces exactly one `.apply`
node, so the height of the PRODUCED tree is the height of the derivation.
`patternHeight`/`patternsHeight` measure it; `mem_enumDerives_iff` connects it
to `enumDerives` in both directions. -/

mutual

/-- Height of a pattern tree: `.apply` nodes count `1 + max` over children;
every other pattern form counts `1`. On the image of `Derives` this is exactly
derivation height. -/
def patternHeight : Pattern → Nat
  | .apply _ kids => patternsHeight kids + 1
  | _ => 1

/-- Maximum height over a list of patterns (0 for `[]`). -/
def patternsHeight : List Pattern → Nat
  | [] => 0
  | p :: ps => max (patternHeight p) (patternsHeight ps)

end

/-- Everything enumerated at `fuel` has height ≤ `fuel` (items level). -/
theorem enumDerivesItems_height_le {r : GrammarRule}
    {recur : String → List String → List Pattern} {fuel : Nat}
    (hrec : ∀ sort sub tree, tree ∈ recur sort sub → patternHeight tree ≤ fuel) :
    ∀ (items : List SyntaxItem) (toks : List String) (kids : List Pattern),
      kids ∈ enumDerivesItems recur r items toks → patternsHeight kids ≤ fuel
  | [], [], _, h => by
      simp only [enumDerivesItems, List.mem_singleton] at h
      subst h
      simp [patternsHeight]
  | [], _ :: _, _, h => by simp [enumDerivesItems] at h
  | .terminal _ :: _, [], _, h => by simp [enumDerivesItems] at h
  | .terminal tok :: rest, tk :: toks, kids, h => by
      simp only [enumDerivesItems] at h
      by_cases htk : tk = tok
      · rw [if_pos htk] at h
        exact enumDerivesItems_height_le hrec rest toks kids h
      · rw [if_neg htk] at h
        simp at h
  | .nonTerminal n :: rest, toks, kids, h => by
      simp only [enumDerivesItems] at h
      cases hps : paramSort? r n with
      | none => rw [hps] at h; simp at h
      | some sort =>
          rw [hps] at h
          simp only [List.mem_flatMap, List.mem_map] at h
          obtain ⟨s, _, tree, htree, kids', hkids', rfl⟩ := h
          simp only [patternsHeight, Nat.max_le]
          exact ⟨hrec sort s.1 tree htree,
            enumDerivesItems_height_le hrec rest s.2 kids' hkids'⟩
  | .separator _ :: _, _, _, h => by simp [enumDerivesItems] at h
  | .delimiter _ _ :: _, _, _, h => by simp [enumDerivesItems] at h
  | .op _ :: _, _, _, h => by simp [enumDerivesItems] at h

/-- Everything enumerated at `fuel` has height ≤ `fuel`. -/
theorem enumDerives_height_le (lang : LanguageDef) :
    ∀ (fuel : Nat) (sort : String) (toks : List String) (t : Pattern),
      t ∈ enumDerives lang fuel sort toks → patternHeight t ≤ fuel
  | 0, _, _, _, h => by simp [enumDerives] at h
  | fuel + 1, sort, toks, t, h => by
      simp only [enumDerives, List.mem_flatMap] at h
      obtain ⟨r, hr, ht⟩ := h
      by_cases hcat : r.category = sort
      · rw [if_pos hcat] at ht
        simp only [List.mem_map] at ht
        obtain ⟨kids, hkids, rfl⟩ := ht
        have hk := enumDerivesItems_height_le
          (fun s sub tree hmem => enumDerives_height_le lang fuel s sub tree hmem)
          r.syntaxPattern toks kids hkids
        simp only [patternHeight]
        omega
      · rw [if_neg hcat] at ht
        simp at ht

/-! ## Fuel-completeness: every derivation of height ≤ fuel is enumerated -/

theorem enumDerivesItems_complete {lang : LanguageDef} {r : GrammarRule}
    {recur : String → List String → List Pattern} {fuel : Nat}
    (hrec : ∀ sort sub tree, Derives lang sort sub tree →
      patternHeight tree ≤ fuel → tree ∈ recur sort sub) :
    ∀ (items : List SyntaxItem) (toks : List String) (kids : List Pattern),
      DerivesItems lang r items toks kids → patternsHeight kids ≤ fuel →
      kids ∈ enumDerivesItems recur r items toks
  | [], _, _, h, _ => by
      cases h
      simp [enumDerivesItems]
  | .terminal tok :: rest, _, kids, h, hh => by
      cases h
      rename_i toks' h'
      simpa [enumDerivesItems] using
        enumDerivesItems_complete hrec rest toks' kids h' hh
  | .nonTerminal n :: rest, _, _, h, hh => by
      cases h
      rename_i sort sub tree hsub toks' kids' hps h'
      simp only [patternsHeight, Nat.max_le] at hh
      simp only [enumDerivesItems, hps, List.mem_flatMap, List.mem_map]
      exact ⟨(sub, toks'), splits_complete sub toks', tree,
        hrec sort sub tree hsub hh.1, kids',
        enumDerivesItems_complete hrec rest toks' kids' h' hh.2, rfl⟩
  | .separator _ :: _, _, _, h, _ => by cases h
  | .delimiter _ _ :: _, _, _, h, _ => by cases h
  | .op _ :: _, _, _, h, _ => by cases h

/-- FUEL-COMPLETENESS: every derivation tree of height ≤ `fuel` is found by
the fuel-`fuel` enumerator. -/
theorem enumDerives_complete (lang : LanguageDef) :
    ∀ (fuel : Nat) (sort : String) (toks : List String) (t : Pattern),
      Derives lang sort toks t → patternHeight t ≤ fuel →
      t ∈ enumDerives lang fuel sort toks
  | 0, _, _, _, h, hh => by
      cases h
      simp only [patternHeight] at hh
      omega
  | fuel + 1, sort, toks, t, h, hh => by
      cases h
      rename_i r hr kids hsort hitems
      simp only [patternHeight] at hh
      simp only [enumDerives, List.mem_flatMap]
      refine ⟨r, hr, ?_⟩
      rw [if_pos hsort]
      exact List.mem_map.mpr ⟨kids,
        enumDerivesItems_complete
          (fun s sub tree hd hht => enumDerives_complete lang fuel s sub tree hd hht)
          r.syntaxPattern toks kids hitems (by omega), rfl⟩

/-- Exact characterization: the fuel-`fuel` enumerator lists precisely the
derivation trees of height ≤ `fuel` (the two-way fuel/`Derives` connection). -/
theorem mem_enumDerives_iff (lang : LanguageDef) (fuel : Nat) (sort : String)
    (toks : List String) (t : Pattern) :
    t ∈ enumDerives lang fuel sort toks ↔
      Derives lang sort toks t ∧ patternHeight t ≤ fuel :=
  ⟨fun h => ⟨enumDerives_sound lang fuel sort toks t h,
             enumDerives_height_le lang fuel sort toks t h⟩,
   fun ⟨hd, hh⟩ => enumDerives_complete lang fuel sort toks t hd hh⟩

/-! ## Fuel-bounded uniqueness certificates -/

/-- Fuel-bounded per-string uniqueness: all derivations of height ≤ `fuel`
agree. The honest bounded form of `UniqueDerivation`. -/
def UniqueDerivationUpTo (lang : LanguageDef) (fuel : Nat) (sort : String)
    (toks : List String) : Prop :=
  ∀ t₁ t₂, Derives lang sort toks t₁ → Derives lang sort toks t₂ →
    patternHeight t₁ ≤ fuel → patternHeight t₂ ≤ fuel → t₁ = t₂

/-- CERTIFICATE: if everything the fuel-`fuel` enumerator finds equals one
fixed tree `w`, uniqueness holds up to that fuel. The premise is checkable on
concrete inputs (`Pattern` has `DecidableEq`; `enumDerives` is structurally
recursive, so kernel evaluation goes through). -/
theorem uniqueDerivationUpTo_of_enum {lang : LanguageDef} {fuel : Nat}
    {sort : String} {toks : List String} (w : Pattern)
    (h : ∀ t ∈ enumDerives lang fuel sort toks, t = w) :
    UniqueDerivationUpTo lang fuel sort toks :=
  fun t₁ t₂ h₁ h₂ hh₁ hh₂ =>
    (h t₁ (enumDerives_complete lang fuel sort toks t₁ h₁ hh₁)).trans
      (h t₂ (enumDerives_complete lang fuel sort toks t₂ h₂ hh₂)).symm

/-- BRIDGE: uniqueness at every fuel is exactly unbounded uniqueness. -/
theorem uniqueDerivation_iff_upTo (lang : LanguageDef) (sort : String)
    (toks : List String) :
    UniqueDerivation lang sort toks ↔
      ∀ fuel, UniqueDerivationUpTo lang fuel sort toks := by
  constructor
  · exact fun h _ t₁ t₂ h₁ h₂ _ _ => h t₁ t₂ h₁ h₂
  · intro h t₁ t₂ h₁ h₂
    exact h (max (patternHeight t₁) (patternHeight t₂)) t₁ t₂ h₁ h₂
      (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-! ## Consuming grammars: the unconditional bridge

If every production's syntax pattern contains a terminal, every rule
application consumes ≥ 1 token, so derivation height is bounded by
`toks.length` — one finite enumeration then seals full `UniqueDerivation`,
with no fuel qualifier surviving in the conclusion. (This hypothesis rules
out ε-productions and unit-production cycles at once. Grammars with unit
productions — e.g. set.mm's `cv : class ← setvar` — need the fuel-bounded
form or a no-unit-cycle bound instead.) -/

/-- The rule's syntax pattern contains at least one terminal, so every
application of it consumes at least one token. -/
def RuleConsumes (r : GrammarRule) : Prop :=
  ∃ tok, SyntaxItem.terminal tok ∈ r.syntaxPattern

/-- Every production consumes ≥ 1 token. -/
def ConsumingGrammar (lang : LanguageDef) : Prop :=
  ∀ r ∈ lang.terms, RuleConsumes r

/-- Executable check for `ConsumingGrammar`. -/
def consumingGrammarB (lang : LanguageDef) : Bool :=
  lang.terms.all fun r =>
    r.syntaxPattern.any fun i =>
      match i with
      | .terminal _ => true
      | _ => false

theorem consumingGrammarB_sound {lang : LanguageDef}
    (h : consumingGrammarB lang = true) : ConsumingGrammar lang := by
  intro r hr
  obtain ⟨i, hi, hterm⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp h r hr)
  cases i with
  | terminal tok => exact ⟨tok, hi⟩
  | nonTerminal _ => simp at hterm
  | separator _ => simp at hterm
  | delimiter _ _ => simp at hterm
  | op _ => simp at hterm

/-- An item list containing a terminal only derives nonempty token lists. -/
theorem derivesItems_toks_pos {lang : LanguageDef} {r : GrammarRule} :
    ∀ (items : List SyntaxItem) (toks : List String) (kids : List Pattern),
      DerivesItems lang r items toks kids →
      (∃ tok, SyntaxItem.terminal tok ∈ items) → 0 < toks.length
  | [], _, _, _, hex => by
      obtain ⟨tok, htok⟩ := hex
      simp at htok
  | .terminal _ :: _, _, _, h, _ => by
      cases h
      simp
  | .nonTerminal n :: rest, _, _, h, hex => by
      cases h
      rename_i _sort sub _tree _hsub toks' kids' _hps h'
      obtain ⟨tok, htok⟩ := hex
      rcases List.mem_cons.mp htok with heq | hmem
      · exact absurd heq (by simp)
      · have hpos := derivesItems_toks_pos rest toks' kids' h' ⟨tok, hmem⟩
        simp only [List.length_append]
        omega
  | .separator _ :: _, _, _, h, _ => by cases h
  | .delimiter _ _ :: _, _, _, h, _ => by cases h
  | .op _ :: _, _, _, h, _ => by cases h

/-- Items-level height bound: given the outer bound `N` and either a terminal
still ahead in the items or strict slack `toks.length < N`, all children stay
strictly below `N`. -/
theorem derivesItems_heights_lt {lang : LanguageDef} {r : GrammarRule} {N : Nat}
    (hrec : ∀ (sort : String) (sub : List String) (tree : Pattern),
      Derives lang sort sub tree → sub.length < N →
      patternHeight tree ≤ sub.length) :
    ∀ (items : List SyntaxItem) (toks : List String) (kids : List Pattern),
      DerivesItems lang r items toks kids → toks.length ≤ N →
      ((∃ tok, SyntaxItem.terminal tok ∈ items) ∨ toks.length < N) →
      patternsHeight kids < N
  | [], _, _, h, _, hdisj => by
      cases h
      rcases hdisj with ⟨tok, htok⟩ | hlt
      · simp at htok
      · simpa [patternsHeight] using hlt
  | .terminal tok :: rest, _, kids, h, hle, _hdisj => by
      cases h
      rename_i toks' h'
      simp only [List.length_cons] at hle
      exact derivesItems_heights_lt hrec rest toks' kids h' (by omega)
        (Or.inr (by omega))
  | .nonTerminal n :: rest, _, _, h, hle, hdisj => by
      cases h
      rename_i sort sub tree hsub toks' kids' _hps h'
      simp only [List.length_append] at hle
      obtain ⟨hsubN, hrestLe, hrestDisj⟩ : sub.length < N ∧ toks'.length ≤ N ∧
          ((∃ tok, SyntaxItem.terminal tok ∈ rest) ∨ toks'.length < N) := by
        rcases hdisj with ⟨tok, htok⟩ | hlt
        · rcases List.mem_cons.mp htok with heq | hmem
          · exact absurd heq (by simp)
          · have hpos := derivesItems_toks_pos rest toks' kids' h' ⟨tok, hmem⟩
            exact ⟨by omega, by omega, Or.inl ⟨tok, hmem⟩⟩
        · simp only [List.length_append] at hlt
          exact ⟨by omega, by omega, Or.inr (by omega)⟩
      have htree : patternHeight tree ≤ sub.length :=
        hrec sort sub tree hsub hsubN
      have hrest : patternsHeight kids' < N :=
        derivesItems_heights_lt hrec rest toks' kids' h' hrestLe hrestDisj
      simp only [patternsHeight]
      exact Nat.max_lt.mpr ⟨by omega, hrest⟩
  | .separator _ :: _, _, _, h, _, _ => by cases h
  | .delimiter _ _ :: _, _, _, h, _, _ => by cases h
  | .op _ :: _, _, _, h, _, _ => by cases h

theorem derives_height_le_length {lang : LanguageDef}
    (hcons : ConsumingGrammar lang) :
    ∀ (N : Nat) (sort : String) (toks : List String) (t : Pattern),
      toks.length ≤ N → Derives lang sort toks t →
      patternHeight t ≤ toks.length := by
  intro N
  induction N with
  | zero =>
      intro sort toks t hlen h
      cases h
      rename_i r hr kids _hsort hitems
      have hpos := derivesItems_toks_pos r.syntaxPattern toks kids hitems
        (hcons r hr)
      omega
  | succ N ih =>
      intro sort toks t hlen h
      cases h
      rename_i r hr kids _hsort hitems
      have hpos := derivesItems_toks_pos r.syntaxPattern toks kids hitems
        (hcons r hr)
      have hk : patternsHeight kids < toks.length :=
        derivesItems_heights_lt
          (fun s sub tree hd hlt => ih s sub tree (by omega) hd)
          r.syntaxPattern toks kids hitems le_rfl (Or.inl (hcons r hr))
      simp only [patternHeight]
      omega

/-- For consuming grammars, derivation height never exceeds the token count —
so `enumDerives lang toks.length` already sees EVERY derivation. -/
theorem derives_height_le {lang : LanguageDef} (hcons : ConsumingGrammar lang)
    {sort : String} {toks : List String} {t : Pattern}
    (h : Derives lang sort toks t) : patternHeight t ≤ toks.length :=
  derives_height_le_length hcons toks.length sort toks t le_rfl h

/-- UNCONDITIONAL CERTIFICATE for consuming grammars: a singleton enumeration
at any fuel ≥ `toks.length` seals full `UniqueDerivation`. -/
theorem uniqueDerivation_of_enum {lang : LanguageDef}
    (hcons : ConsumingGrammar lang) {fuel : Nat} {sort : String}
    {toks : List String} (hfuel : toks.length ≤ fuel) (w : Pattern)
    (h : ∀ t ∈ enumDerives lang fuel sort toks, t = w) :
    UniqueDerivation lang sort toks := fun t₁ t₂ h₁ h₂ =>
  (h t₁ (enumDerives_complete lang fuel sort toks t₁ h₁
      ((derives_height_le hcons h₁).trans hfuel))).trans
    (h t₂ (enumDerives_complete lang fuel sort toks t₂ h₂
      ((derives_height_le hcons h₂).trans hfuel))).symm

end Mettapedia.OSLF.Framework.GrammarDerives
