/-
# Robots exclusion (RFC 9309): path matching and the decision rule

A robots.txt group is a list of allow and disallow rules. A rule's path may
contain `*` (any sequence of characters) and may end in `$` (the end of the
path); without `$` a rule matches every path that starts with what it
describes. RFC 9309 §2.2.2: the matching rule with the most octets decides,
an allow rule wins a tie, and a path no rule matches is allowed. `/robots.txt`
itself is always allowed (§2.2.2).

Results:
* `verdict_iff`: the one-pass decision procedure `verdict` computes exactly
  the declarative rule `Allowed`.
* `verdict_order_independent`: the decision depends only on which rules are
  present, never on their order; so merging the groups of one user agent
  (§2.2.1) cannot change a decision by the order it merges them in.
* `firstMatch_not_rfc`: deciding by the first matching rule, as older parsers
  do, is not the RFC rule.
* Group selection (§2.2.1): the groups naming the crawler's product token are
  merged; only when there is none do the `*` groups apply.
* Access purpose: robots.txt governs crawling. A read an agent makes for the
  task it was given is a user-triggered fetch, which the rules here do not
  govern; `crawl_respects_robots` states that an automated traversal never
  fetches a path the rules disallow.

Paths are characters after percent-encoding normalisation (RFC 3986 §6.2.2),
where one character is one octet; product tokens are compared lowercased.
Core Lean only.
-/

namespace Mettapedia.Protocols.Web.RobotsExclusion

/-- A piece of a rule's path: a literal character or the `*` wildcard. -/
inductive Tok where
  | lit (c : Char)
  | star
  deriving DecidableEq, Repr

/-- Whether `f` holds of some suffix of the path, the path itself included. -/
def anySuffix (f : List Char → Bool) : List Char → Bool
  | [] => f []
  | x :: xs => f (x :: xs) || anySuffix f xs

/-- The pattern describes a prefix of the path (a rule without `$`). -/
def matchPrefix : List Tok → List Char → Bool
  | [], _ => true
  | .lit _ :: _, [] => false
  | .lit c :: ps, x :: xs => c == x && matchPrefix ps xs
  | .star :: ps, xs => anySuffix (matchPrefix ps) xs

/-- The pattern describes the whole path (a rule ending in `$`). -/
def matchFull : List Tok → List Char → Bool
  | [], xs => xs.isEmpty
  | .lit _ :: _, [] => false
  | .lit c :: ps, x :: xs => c == x && matchFull ps xs
  | .star :: ps, xs => anySuffix (matchFull ps) xs

/-- One allow or disallow line of a group. -/
structure Rule where
  allow : Bool
  toks : List Tok
  anchored : Bool
  deriving DecidableEq, Repr

/-- The rule's path length, `*` and `$` included: the RFC's measure of how
specific a match is. -/
def Rule.len (r : Rule) : Nat := r.toks.length + (if r.anchored then 1 else 0)

/-- The rule matches the path. -/
def Rule.hits (r : Rule) (p : List Char) : Bool :=
  if r.anchored then matchFull r.toks p else matchPrefix r.toks p

/-- The declarative rule of §2.2.2: allowed when no rule matches, or when an
allow rule matches that is at least as long as every matching rule. -/
def Allowed (rs : List Rule) (p : List Char) : Prop :=
  (∀ r ∈ rs, r.hits p = false) ∨
  ∃ a ∈ rs, a.allow = true ∧ a.hits p = true ∧ ∀ r ∈ rs, r.hits p = true → r.len ≤ a.len

/-- Fold one rule into the best match so far: its length, and whether an
allow rule of that length matched. -/
def step (p : List Char) (r : Rule) : Option (Nat × Bool) → Option (Nat × Bool)
  | none => if r.hits p then some (r.len, r.allow) else none
  | some (l, a) =>
    if r.hits p then
      if l < r.len then some (r.len, r.allow)
      else if r.len = l then some (l, a || r.allow) else some (l, a)
    else some (l, a)

/-- The best match over all rules, in one pass. -/
def best (p : List Char) : List Rule → Option (Nat × Bool)
  | [] => none
  | r :: rs => step p r (best p rs)

/-- The decision: allowed unless the best match is a disallow rule. -/
def verdict (rs : List Rule) (p : List Char) : Bool :=
  match best p rs with
  | none => true
  | some (_, a) => a

theorem best_none_iff (p : List Char) :
    ∀ rs : List Rule, best p rs = none ↔ ∀ r ∈ rs, r.hits p = false
  | [] => by simp [best]
  | r :: rs => by
    have ih := best_none_iff p rs
    cases h : best p rs with
    | none =>
      have hall := ih.mp h
      by_cases hr : r.hits p = true
      · simp [best, h, step, hr]
      · have hf : r.hits p = false := by simpa using hr
        simp only [best, h, step, hf]
        constructor
        · intro _ x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hf
          · exact hall x hx
        · intro _; rfl
    | some la =>
      obtain ⟨l, a⟩ := la
      have hnot : ¬ ∀ x ∈ rs, x.hits p = false := fun hall => by
        have := ih.mpr hall; simp [h] at this
      constructor
      · intro hb
        exfalso
        simp only [best, h, step] at hb
        split at hb
        · split at hb
          · simp at hb
          · split at hb <;> simp at hb
        · simp at hb
      · intro hall
        exact absurd (fun x hx => hall x (List.mem_cons_of_mem r hx)) hnot

/-- What the one-pass best match records: the longest matching length, and
whether an allow rule of that length matched. -/
theorem best_some (p : List Char) :
    ∀ (rs : List Rule) (l : Nat) (a : Bool), best p rs = some (l, a) →
      (∃ x ∈ rs, x.hits p = true ∧ x.len = l) ∧
      (∀ x ∈ rs, x.hits p = true → x.len ≤ l) ∧
      (a = true ↔ ∃ x ∈ rs, x.hits p = true ∧ x.len = l ∧ x.allow = true)
  | [], l, a, h => by simp [best] at h
  | r :: rs, l, a, h => by
    cases hb : best p rs with
    | none =>
      have hall := (best_none_iff p rs).mp hb
      simp only [best, hb, step] at h
      by_cases hr : r.hits p = true
      · simp only [hr, if_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨⟨r, List.mem_cons_self .., hr, rfl⟩, ?_, ?_⟩
        · intro x hx hxh
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Nat.le_refl _
          · simp [hall x hx] at hxh
        · constructor
          · intro ha; exact ⟨r, List.mem_cons_self .., hr, rfl, ha⟩
          · rintro ⟨x, hx, hxh, _, hxa⟩
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hxa
            · simp [hall x hx] at hxh
      · have hf : r.hits p = false := by simpa using hr
        simp [hf] at h
    | some lb =>
      obtain ⟨l', a'⟩ := lb
      obtain ⟨⟨w, hw, hwh, hwl⟩, hmax, hiff⟩ := best_some p rs l' a' hb
      simp only [best, hb, step] at h
      by_cases hr : r.hits p = true
      · simp only [hr, if_true] at h
        by_cases hlt : l' < r.len
        · simp only [hlt, if_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨⟨r, List.mem_cons_self .., hr, rfl⟩, ?_, ?_⟩
          · intro x hx hxh
            rcases List.mem_cons.mp hx with rfl | hx
            · exact Nat.le_refl _
            · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax x hx hxh) hlt)
          · constructor
            · intro ha; exact ⟨r, List.mem_cons_self .., hr, rfl, ha⟩
            · rintro ⟨x, hx, hxh, hxl, hxa⟩
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hxa
              · have := hmax x hx hxh; omega
        · simp only [hlt, if_false] at h
          by_cases heq : r.len = l'
          · simp only [heq, if_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨⟨w, List.mem_cons_of_mem r hw, hwh, hwl⟩, ?_, ?_⟩
            · intro x hx hxh
              rcases List.mem_cons.mp hx with rfl | hx
              · exact Nat.le_of_eq heq
              · exact hmax x hx hxh
            · constructor
              · intro ha
                rcases Bool.or_eq_true_iff.mp ha with ha | ha
                · obtain ⟨x, hx, hxh, hxl, hxa⟩ := hiff.mp ha
                  exact ⟨x, List.mem_cons_of_mem r hx, hxh, hxl, hxa⟩
                · exact ⟨r, List.mem_cons_self .., hr, heq, ha⟩
              · rintro ⟨x, hx, hxh, hxl, hxa⟩
                rcases List.mem_cons.mp hx with rfl | hx
                · simp [hxa]
                · simp [hiff.mpr ⟨x, hx, hxh, hxl, hxa⟩]
          · simp only [heq, if_false, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨⟨w, List.mem_cons_of_mem r hw, hwh, hwl⟩, ?_, ?_⟩
            · intro x hx hxh
              rcases List.mem_cons.mp hx with rfl | hx
              · omega
              · exact hmax x hx hxh
            · constructor
              · intro ha
                obtain ⟨x, hx, hxh, hxl, hxa⟩ := hiff.mp ha
                exact ⟨x, List.mem_cons_of_mem r hx, hxh, hxl, hxa⟩
              · rintro ⟨x, hx, hxh, hxl, hxa⟩
                rcases List.mem_cons.mp hx with rfl | hx
                · exact absurd hxl heq
                · exact hiff.mpr ⟨x, hx, hxh, hxl, hxa⟩
      · have hf : r.hits p = false := by simpa using hr
        simp only [hf] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨⟨w, List.mem_cons_of_mem r hw, hwh, hwl⟩, ?_, ?_⟩
        · intro x hx hxh
          rcases List.mem_cons.mp hx with rfl | hx
          · simp [hf] at hxh
          · exact hmax x hx hxh
        · constructor
          · intro ha
            obtain ⟨x, hx, hxh, hxl, hxa⟩ := hiff.mp ha
            exact ⟨x, List.mem_cons_of_mem r hx, hxh, hxl, hxa⟩
          · rintro ⟨x, hx, hxh, hxl, hxa⟩
            rcases List.mem_cons.mp hx with rfl | hx
            · simp [hf] at hxh
            · exact hiff.mpr ⟨x, hx, hxh, hxl, hxa⟩

/-- The one-pass procedure decides exactly the RFC's rule. -/
theorem verdict_iff (rs : List Rule) (p : List Char) :
    verdict rs p = true ↔ Allowed rs p := by
  unfold verdict Allowed
  cases hb : best p rs with
  | none =>
    simp only [true_iff]
    exact Or.inl ((best_none_iff p rs).mp hb)
  | some la =>
    obtain ⟨l, a⟩ := la
    obtain ⟨⟨w, hw, hwh, hwl⟩, hmax, hiff⟩ := best_some p rs l a hb
    simp only
    constructor
    · intro ha
      obtain ⟨x, hx, hxh, hxl, hxa⟩ := hiff.mp ha
      exact Or.inr ⟨x, hx, hxa, hxh, fun r hr hrh => hxl ▸ hmax r hr hrh⟩
    · rintro (hall | ⟨x, hx, hxa, hxh, hxmax⟩)
      · simp [hall w hw] at hwh
      · have hle := hmax x hx hxh
        have hge := hxmax w hw hwh
        exact hiff.mpr ⟨x, hx, hxh, by omega, hxa⟩

/-- The decision depends only on which rules are present. -/
theorem verdict_order_independent (rs rs' : List Rule) (p : List Char)
    (h : ∀ r, r ∈ rs ↔ r ∈ rs') : verdict rs p = verdict rs' p := by
  have hA : Allowed rs p ↔ Allowed rs' p := by
    unfold Allowed
    constructor
    · rintro (hall | ⟨a, ha, h1, h2, h3⟩)
      · exact Or.inl fun r hr => hall r ((h r).mpr hr)
      · exact Or.inr ⟨a, (h a).mp ha, h1, h2, fun r hr => h3 r ((h r).mpr hr)⟩
    · rintro (hall | ⟨a, ha, h1, h2, h3⟩)
      · exact Or.inl fun r hr => hall r ((h r).mp hr)
      · exact Or.inr ⟨a, (h a).mpr ha, h1, h2, fun r hr => h3 r ((h r).mp hr)⟩
  cases hv : verdict rs p <;> cases hv' : verdict rs' p
  · rfl
  · exact absurd ((verdict_iff rs p).mpr (hA.mpr ((verdict_iff rs' p).mp hv'))) (by simp [hv])
  · exact absurd ((verdict_iff rs' p).mpr (hA.mp ((verdict_iff rs p).mp hv))) (by simp [hv'])
  · rfl

/-! ## The path `/robots.txt` and older first-match parsers -/

def robotsTxtPath : List Char := ['/', 'r', 'o', 'b', 'o', 't', 's', '.', 't', 'x', 't']

/-- RFC 9309's decision for a path: `/robots.txt` is always allowed. -/
def rfcAllows (rs : List Rule) (p : List Char) : Bool := p == robotsTxtPath || verdict rs p

/-- Deciding by the first rule that matches. -/
def firstMatch (rs : List Rule) (p : List Char) : Bool :=
  match rs.find? (fun r => r.hits p) with
  | none => true
  | some r => r.allow

/-- A rule from a literal path. -/
def rule (allow : Bool) (path : List Char) : Rule :=
  { allow := allow, toks := path.map .lit, anchored := false }

/-- First-match deciding is not the RFC rule: a disallow line before an allow
line of the same path (vector V03a). -/
theorem firstMatch_not_rfc :
    firstMatch [rule false ['/', 'p'], rule true ['/', 'p']] ['/', 'p'] = false ∧
    verdict [rule false ['/', 'p'], rule true ['/', 'p']] ['/', 'p'] = true := by
  decide

/-! ## Group selection (§2.2.1) -/

/-- A group: the product tokens it names (lowercased; `*` as `['*']`) and its rules. -/
structure Group where
  agents : List (List Char)
  rules : List Rule

/-- The rules for a crawler: the merged groups naming its token, or, when no
group names it, the merged `*` groups. -/
def rulesFor (gs : List Group) (ua : List Char) : List Rule :=
  let own := gs.filter (fun g => g.agents.contains ua)
  if own.isEmpty then (gs.filter (fun g => g.agents.contains ['*'])).flatMap Group.rules
  else own.flatMap Group.rules

/-- A group naming the crawler hides every `*` rule: the crawler's own rules
are the only ones in force. -/
theorem own_group_hides_star (gs : List Group) (ua : List Char)
    (hown : ∃ g ∈ gs, g.agents.contains ua = true) :
    rulesFor gs ua = (gs.filter (fun g => g.agents.contains ua)).flatMap Group.rules := by
  obtain ⟨g, hg, hc⟩ := hown
  have hmem : g ∈ gs.filter (fun g => g.agents.contains ua) := List.mem_filter.mpr ⟨hg, hc⟩
  have hne : (gs.filter (fun g => g.agents.contains ua)).isEmpty = false := by
    cases hf : gs.filter (fun g => g.agents.contains ua) with
    | nil => rw [hf] at hmem; simp at hmem
    | cons _ _ => rfl
  simp only [rulesFor]
  rw [if_neg (by rw [hne]; exact Bool.false_ne_true)]

/-! ## Access purpose -/

/-- Why the agent fetches a page: for the task it was given (a user-triggered
fetch, one page at a time), or as an automated traversal of a site. -/
inductive Purpose where
  | task
  | crawl
  deriving DecidableEq, Repr

/-- robots.txt governs crawling; a read for the task is not crawling. -/
def mayFetch : Purpose → List Rule → List Char → Bool
  | .task, _, _ => true
  | .crawl, rs, p => rfcAllows rs p

/-- An automated traversal fetches only what the rules allow (or robots.txt itself). -/
theorem crawl_respects_robots (rs : List Rule) (p : List Char)
    (h : mayFetch .crawl rs p = true) : p = robotsTxtPath ∨ Allowed rs p := by
  simp only [mayFetch, rfcAllows, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((verdict_iff rs p).mp h)

/-! ## Test vectors

The vectors of a survey of RFC 9309 against two parsers (Python's
urllib.robotparser and Google's robotstxt library), where they concern
matching and the decision rule. -/

def slash : Char := '/'

/-- V01, V02: a longer allow inside a disallowed folder. -/
example : verdict [rule true ['/', 'f', '/', 'p'], rule false ['/', 'f']] ['/', 'f', '/', 'p'] = true := by decide
example : verdict [rule true ['/', 'f', '/', 'p'], rule false ['/', 'f']] ['/', 'f', '/', 'o'] = false := by decide

/-- V03a, V03b: a tie goes to allow, in either order. -/
example : verdict [rule false ['/', 'p'], rule true ['/', 'p']] ['/', 'p'] = true := by decide
example : verdict [rule true ['/', 'p'], rule false ['/', 'p']] ['/', 'p'] = true := by decide

/-- V04a, V04b: `Disallow: /*.gif$` blocks `/a/b.gif` but not `/a/b.gif?x=1`. -/
def gifRule : Rule :=
  { allow := false, toks := [.lit '/', .star, .lit '.', .lit 'g', .lit 'i', .lit 'f'], anchored := true }
example : verdict [gifRule] ['/', 'a', '/', 'b', '.', 'g', 'i', 'f'] = false := by decide
example : verdict [gifRule] ['/', 'a', '/', 'b', '.', 'g', 'i', 'f', '?', 'x', '=', '1'] = true := by decide

/-- V06: paths are case-sensitive. -/
example : verdict [rule false ['/', 'P']] ['/', 'p'] = true := by decide

/-- V11: `/robots.txt` is allowed even under `Disallow: /`. -/
example : rfcAllows [rule false [slash]] robotsTxtPath = true := by decide

/-- V18: `Disallow: /` with `Allow: /index.html` still denies `/`. -/
example : verdict [rule false [slash], rule true ['/', 'i', 'n', 'd', 'e', 'x', '.', 'h', 't', 'm', 'l']] [slash] = false := by decide

/-- V19: `?` is an ordinary character: `Disallow: /foo?bar` blocks `/foo?bar=1`. -/
example : verdict [rule false ['/', 'f', 'o', 'o', '?', 'b', 'a', 'r']] ['/', 'f', 'o', 'o', '?', 'b', 'a', 'r', '=', '1'] = false := by decide

/-- V08: two groups for the same crawler are merged. -/
example : verdict (rulesFor [⟨[['e', 'b']], [rule false ['/', 'f']]⟩, ⟨[['e', 'b']], [rule false ['/', 'z']]⟩] ['e', 'b']) ['/', 'z'] = false := by decide

/-- V10: the crawler's own empty-disallow group overrides `Disallow: /` for `*`. -/
example : verdict (rulesFor [⟨[['*']], [rule false [slash]]⟩, ⟨[['e', 'b']], []⟩] ['e', 'b']) ['/', 'x'] = true := by decide

end Mettapedia.Protocols.Web.RobotsExclusion
