/-!
# Indexed cost vs. woven cost: does a separate cost index make faithfulness free?

A self-contained probe.  No project imports: the point is to isolate the
*shape* of the obligation, not to re-run the real machinery.

Setting: an uncoloured term language with `zero`, binary `par`, `quote`,
`drop`, and a canonicalizer that orients `quote (drop x) = x` and
flattens / unit-filters `par`.

Two presentations of the same language carrying a two-valued cost colour:

* **woven** (`WTerm`) — the colour is part of the constructor name, so
  `baseQuote` and `wrappedQuote` are literally different constructors and a
  single term may carry both;
* **indexed** (`Term × Colour`) — the colour is a separate component.

The probe asks whether the indexed presentation makes faithfulness free, and
if so what the bridge between the two presentations costs.
-/

namespace ClaudeIndexedCost

/-! ## 1. Uncoloured syntax and canonicalizer -/

inductive Term where
  | zero : Term
  | par : Term → Term → Term
  | quote : Term → Term
  | drop : Term → Term
  deriving DecidableEq

/-- Top-level `par` spine with `zero` units filtered out.  Every element of
the result is a `quote` or a `drop`. -/
def collect : Term → List Term
  | .zero => []
  | .par a b => collect a ++ collect b
  | .quote t => [.quote t]
  | .drop t => [.drop t]

/-- Right-nested rebuild of a `par` spine. -/
def rebuild : List Term → Term
  | [] => .zero
  | [t] => t
  | t :: ts => .par t (rebuild ts)

/-- The oriented collapse `quote (drop x) ⟶ x`. -/
def quoteStep : Term → Term
  | .drop u => u
  | t => .quote t

def canon : Term → Term
  | .zero => .zero
  | .par a b => rebuild (collect (canon a) ++ collect (canon b))
  | .quote t => quoteStep (canon t)
  | .drop t => .drop (canon t)

def isAtom : Term → Bool
  | .quote _ => true
  | .drop _ => true
  | _ => false

theorem collect_atoms (t : Term) : (collect t).all isAtom = true := by
  induction t with
  | zero => rfl
  | par a b iha ihb => simp [collect, List.all_append, iha, ihb]
  | quote t _ => rfl
  | drop t _ => rfl

theorem rebuild_cons_of_ne_nil (x : Term) :
    ∀ (l : List Term), l ≠ [] → rebuild (x :: l) = .par x (rebuild l)
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem collect_rebuild :
    ∀ (l : List Term), l.all isAtom = true → collect (rebuild l) = l
  | [], _ => rfl
  | [t], h => by
      have ht : isAtom t = true := by simpa using h
      cases t with
      | zero => simp [isAtom] at ht
      | par a b => simp [isAtom] at ht
      | quote u => rfl
      | drop u => rfl
  | t :: u :: us, h => by
      have hsplit : isAtom t = true ∧ ((u :: us).all isAtom) = true := by
        simpa [List.all_cons] using h
      have ih := collect_rebuild (u :: us) hsplit.2
      have ht := hsplit.1
      cases t with
      | zero => simp [isAtom] at ht
      | par a b => simp [isAtom] at ht
      | quote v => simp [rebuild, collect, ih]
      | drop v => simp [rebuild, collect, ih]

/-! ## 2. Colours and the two presentations -/

inductive Colour where
  | base
  | wrapped
  deriving DecidableEq

/-- The **woven** presentation: colour is woven into the constructor
namespace, exactly as `base(NQuote)` and `wrapped(NQuote)` are different wire
constructor names.  Nothing prevents a single term from carrying both. -/
inductive WTerm where
  | baseZero : WTerm
  | wrappedZero : WTerm
  | basePar : WTerm → WTerm → WTerm
  | wrappedPar : WTerm → WTerm → WTerm
  | baseQuote : WTerm → WTerm
  | wrappedQuote : WTerm → WTerm
  | baseDrop : WTerm → WTerm
  | wrappedDrop : WTerm → WTerm
  deriving DecidableEq

def eraseW : WTerm → Term
  | .baseZero => .zero
  | .wrappedZero => .zero
  | .basePar a b => .par (eraseW a) (eraseW b)
  | .wrappedPar a b => .par (eraseW a) (eraseW b)
  | .baseQuote t => .quote (eraseW t)
  | .wrappedQuote t => .quote (eraseW t)
  | .baseDrop t => .drop (eraseW t)
  | .wrappedDrop t => .drop (eraseW t)

/-- Uniform decoration: the only way an indexed pair can name a woven term. -/
def decorate : Colour → Term → WTerm
  | .base, .zero => .baseZero
  | .base, .par a b => .basePar (decorate .base a) (decorate .base b)
  | .base, .quote t => .baseQuote (decorate .base t)
  | .base, .drop t => .baseDrop (decorate .base t)
  | .wrapped, .zero => .wrappedZero
  | .wrapped, .par a b => .wrappedPar (decorate .wrapped a) (decorate .wrapped b)
  | .wrapped, .quote t => .wrappedQuote (decorate .wrapped t)
  | .wrapped, .drop t => .wrappedDrop (decorate .wrapped t)

def isUniform : Colour → WTerm → Bool
  | .base, .baseZero => true
  | .base, .basePar a b => isUniform .base a && isUniform .base b
  | .base, .baseQuote t => isUniform .base t
  | .base, .baseDrop t => isUniform .base t
  | .wrapped, .wrappedZero => true
  | .wrapped, .wrappedPar a b => isUniform .wrapped a && isUniform .wrapped b
  | .wrapped, .wrappedQuote t => isUniform .wrapped t
  | .wrapped, .wrappedDrop t => isUniform .wrapped t
  | _, _ => false

def rootColour : WTerm → Colour
  | .baseZero => .base
  | .basePar _ _ => .base
  | .baseQuote _ => .base
  | .baseDrop _ => .base
  | .wrappedZero => .wrapped
  | .wrappedPar _ _ => .wrapped
  | .wrappedQuote _ => .wrapped
  | .wrappedDrop _ => .wrapped

/-- Analogue of `CollapsingRoot`: the root is the declaration colour's quote
constructor or its parallel collection. -/
def collapsingRoot : Colour → WTerm → Bool
  | .base, .baseQuote _ => true
  | .base, .basePar _ _ => true
  | .wrapped, .wrappedQuote _ => true
  | .wrapped, .wrappedPar _ _ => true
  | _, _ => false

/-! ### The woven canonicalizer at one declaration colour

The real `canonicalize` takes a `declarationColor` and the declaration's
`quoteConstructor` / `dropConstructor` are `d.constructorTag ++ …`.  A rule
therefore fires only on a redex whose constructors all carry colour `d`. -/

def stepBaseQuote : Colour → WTerm → WTerm
  | .base, .baseDrop u => u
  | _, t => .baseQuote t

def stepWrappedQuote : Colour → WTerm → WTerm
  | .wrapped, .wrappedDrop u => u
  | _, t => .wrappedQuote t

def collectW : Colour → WTerm → List WTerm
  | .base, .baseZero => []
  | .base, .basePar a b => collectW .base a ++ collectW .base b
  | .wrapped, .wrappedZero => []
  | .wrapped, .wrappedPar a b => collectW .wrapped a ++ collectW .wrapped b
  | _, t => [t]

def rebuildW : Colour → List WTerm → WTerm
  | .base, [] => .baseZero
  | .wrapped, [] => .wrappedZero
  | _, [t] => t
  | .base, t :: ts => .basePar t (rebuildW .base ts)
  | .wrapped, t :: ts => .wrappedPar t (rebuildW .wrapped ts)

def canonW : Colour → WTerm → WTerm
  | _, .baseZero => .baseZero
  | _, .wrappedZero => .wrappedZero
  | .base, .basePar a b =>
      rebuildW .base (collectW .base (canonW .base a) ++ collectW .base (canonW .base b))
  | .wrapped, .basePar a b => .basePar (canonW .wrapped a) (canonW .wrapped b)
  | .base, .wrappedPar a b => .wrappedPar (canonW .base a) (canonW .base b)
  | .wrapped, .wrappedPar a b =>
      rebuildW .wrapped (collectW .wrapped (canonW .wrapped a) ++ collectW .wrapped (canonW .wrapped b))
  | d, .baseQuote t => stepBaseQuote d (canonW d t)
  | d, .wrappedQuote t => stepWrappedQuote d (canonW d t)
  | d, .baseDrop t => .baseDrop (canonW d t)
  | d, .wrappedDrop t => .wrappedDrop (canonW d t)

/-! ## 3. Faithfulness in the INDEXED presentation

This is the whole of it. -/

abbrev Indexed := Term × Colour

def eraseI (p : Indexed) : Term := p.1

def canonI (p : Indexed) : Indexed := (canon p.1, p.2)

theorem indexed_erasure_is_a_projection (p : Indexed) : eraseI p = p.1 := rfl

theorem indexed_square (p : Indexed) : eraseI (canonI p) = canon (eraseI p) := rfl

/-- **Indexed faithfulness.**  Canonically equal terms are observationally
aligned across both colours. -/
theorem indexed_faithful {t₁ t₂ : Term} (c₁ c₂ : Colour) (h : canon t₁ = canon t₂) :
    eraseI (canonI (t₁, c₁)) = eraseI (canonI (t₂, c₂)) := h

/-! ## 4. The bridge, good half: uniform decoration -/

theorem eraseW_decorate (c : Colour) (t : Term) : eraseW (decorate c t) = t := by
  induction t with
  | zero => cases c <;> rfl
  | par a b iha ihb => cases c <;> simp [decorate, eraseW, iha, ihb]
  | quote t ih => cases c <;> simp [decorate, eraseW, ih]
  | drop t ih => cases c <;> simp [decorate, eraseW, ih]

theorem isUniform_decorate (c : Colour) (t : Term) : isUniform c (decorate c t) = true := by
  induction t with
  | zero => cases c <;> rfl
  | par a b iha ihb => cases c <;> simp [decorate, isUniform, iha, ihb]
  | quote t ih => cases c <;> simp [decorate, isUniform, ih]
  | drop t ih => cases c <;> simp [decorate, isUniform, ih]

/-- **The image of the indexed presentation is exactly the uniform terms.** -/
theorem exists_decorate_iff_isUniform :
    ∀ (w : WTerm) (c : Colour), (∃ t, decorate c t = w) ↔ isUniform c w = true := by
  intro w
  induction w with
  | baseZero =>
      intro c; cases c
      · exact ⟨fun _ => rfl, fun _ => ⟨.zero, rfl⟩⟩
      · exact ⟨fun ⟨t, ht⟩ => by
            have := isUniform_decorate .wrapped t
            rw [ht] at this; simp [isUniform] at this,
          fun h => by simp [isUniform] at h⟩
  | wrappedZero =>
      intro c; cases c
      · exact ⟨fun ⟨t, ht⟩ => by
            have := isUniform_decorate .base t
            rw [ht] at this; simp [isUniform] at this,
          fun h => by simp [isUniform] at h⟩
      · exact ⟨fun _ => rfl, fun _ => ⟨.zero, rfl⟩⟩
  | basePar a b iha ihb =>
      intro c; cases c
      · constructor
        · intro h; exact (isUniform_decorate .base h.choose) ▸ h.choose_spec ▸ rfl
        · intro h
          simp [isUniform] at h
          obtain ⟨ta, hta⟩ := (iha .base).mpr h.1
          obtain ⟨tb, htb⟩ := (ihb .base).mpr h.2
          exact ⟨.par ta tb, by simp [decorate, hta, htb]⟩
      · exact ⟨fun ⟨t, ht⟩ => by
            have := isUniform_decorate .wrapped t
            rw [ht] at this; simp [isUniform] at this,
          fun h => by simp [isUniform] at h⟩
  | wrappedPar a b iha ihb =>
      intro c; cases c
      · exact ⟨fun ⟨t, ht⟩ => by
            have := isUniform_decorate .base t
            rw [ht] at this; simp [isUniform] at this,
          fun h => by simp [isUniform] at h⟩
      · constructor
        · intro h; exact (isUniform_decorate .wrapped h.choose) ▸ h.choose_spec ▸ rfl
        · intro h
          simp [isUniform] at h
          obtain ⟨ta, hta⟩ := (iha .wrapped).mpr h.1
          obtain ⟨tb, htb⟩ := (ihb .wrapped).mpr h.2
          exact ⟨.par ta tb, by simp [decorate, hta, htb]⟩
  | baseQuote t ih =>
      intro c; cases c
      · constructor
        · intro h; exact (isUniform_decorate .base h.choose) ▸ h.choose_spec ▸ rfl
        · intro h
          simp [isUniform] at h
          obtain ⟨s, hs⟩ := (ih .base).mpr h
          exact ⟨.quote s, by simp [decorate, hs]⟩
      · exact ⟨fun ⟨t, ht⟩ => by
            have := isUniform_decorate .wrapped t
            rw [ht] at this; simp [isUniform] at this,
          fun h => by simp [isUniform] at h⟩
  | wrappedQuote t ih =>
      intro c; cases c
      · exact ⟨fun ⟨t, ht⟩ => by
            have := isUniform_decorate .base t
            rw [ht] at this; simp [isUniform] at this,
          fun h => by simp [isUniform] at h⟩
      · constructor
        · intro h; exact (isUniform_decorate .wrapped h.choose) ▸ h.choose_spec ▸ rfl
        · intro h
          simp [isUniform] at h
          obtain ⟨s, hs⟩ := (ih .wrapped).mpr h
          exact ⟨.quote s, by simp [decorate, hs]⟩
  | baseDrop t ih =>
      intro c; cases c
      · constructor
        · intro h; exact (isUniform_decorate .base h.choose) ▸ h.choose_spec ▸ rfl
        · intro h
          simp [isUniform] at h
          obtain ⟨s, hs⟩ := (ih .base).mpr h
          exact ⟨.drop s, by simp [decorate, hs]⟩
      · exact ⟨fun ⟨t, ht⟩ => by
            have := isUniform_decorate .wrapped t
            rw [ht] at this; simp [isUniform] at this,
          fun h => by simp [isUniform] at h⟩
  | wrappedDrop t ih =>
      intro c; cases c
      · exact ⟨fun ⟨t, ht⟩ => by
            have := isUniform_decorate .base t
            rw [ht] at this; simp [isUniform] at this,
          fun h => by simp [isUniform] at h⟩
      · constructor
        · intro h; exact (isUniform_decorate .wrapped h.choose) ▸ h.choose_spec ▸ rfl
        · intro h
          simp [isUniform] at h
          obtain ⟨s, hs⟩ := (ih .wrapped).mpr h
          exact ⟨.drop s, by simp [decorate, hs]⟩

/-- A term carrying both colours. -/
def mixed : WTerm := .baseQuote (.wrappedDrop .baseZero)

theorem mixed_not_uniform (c : Colour) : isUniform c mixed = false := by
  cases c <;> rfl

/-- **The indexed presentation cannot name a mixed term.** -/
theorem decorate_ne_mixed (c : Colour) (t : Term) : decorate c t ≠ mixed := by
  intro h
  have h1 : isUniform c mixed = true := by rw [← h]; exact isUniform_decorate c t
  rw [mixed_not_uniform c] at h1
  exact Bool.noConfusion h1

/-! ## 5. The bridge, good half continued: the square holds on uniform terms -/

theorem collectW_decorate (c : Colour) (t : Term) :
    collectW c (decorate c t) = (collect t).map (decorate c) := by
  induction t with
  | zero => cases c <;> rfl
  | par a b iha ihb => cases c <;> simp [decorate, collectW, collect, iha, ihb]
  | quote t _ => cases c <;> rfl
  | drop t _ => cases c <;> rfl

theorem rebuildW_map_decorate (c : Colour) :
    ∀ (l : List Term), rebuildW c (l.map (decorate c)) = decorate c (rebuild l)
  | [] => by cases c <;> rfl
  | [_] => by cases c <;> rfl
  | _ :: u :: us => by
      cases c <;>
        simp [rebuildW, rebuild, decorate, rebuildW_map_decorate _ (u :: us)]

theorem canonW_decorate (c : Colour) (t : Term) :
    canonW c (decorate c t) = decorate c (canon t) := by
  induction t with
  | zero => cases c <;> rfl
  | par a b iha ihb =>
      cases c <;>
        simp [decorate, canonW, canon, iha, ihb, collectW_decorate,
          ← List.map_append, rebuildW_map_decorate]
  | quote t ih =>
      cases c
      · simp only [decorate, canonW, ih]
        cases hc : canon t with
        | zero => rfl
        | par a b => rfl
        | quote u => rfl
        | drop u => rfl
      · simp only [decorate, canonW, ih]
        cases hc : canon t with
        | zero => rfl
        | par a b => rfl
        | quote u => rfl
        | drop u => rfl
  | drop t ih => cases c <;> simp [decorate, canonW, canon, ih]

/-- On uniform terms the erasure square commutes definitionally-ish: this is
the whole content the indexed presentation ever sees. -/
theorem square_on_uniform (c : Colour) (t : Term) :
    eraseW (canonW c (decorate c t)) = canon (eraseW (decorate c t)) := by
  rw [canonW_decorate, eraseW_decorate, eraseW_decorate]

/-! ## 6. THE CRUX: the square fails on mixed terms -/

theorem canonW_mixed : canonW .base mixed = mixed := rfl

theorem erase_canonW_mixed : eraseW (canonW .base mixed) = .quote (.drop .zero) := rfl

theorem canon_erase_mixed : canon (eraseW mixed) = .zero := rfl

/-- **The erasure square does not commute on the woven presentation.**
The single-colour canonicalizer cannot fire at a cross-colour redex, while the
uncoloured canonicalizer can. -/
theorem square_fails :
    ¬ ∀ (d : Colour) (w : WTerm), eraseW (canonW d w) = canon (eraseW w) := by
  intro h
  have := h .base mixed
  rw [erase_canonW_mixed, canon_erase_mixed] at this
  exact Term.noConfusion this

/-! ## 7. The cross-colour collapsing configuration

The exact configuration of the real cross-colour obligation: two root views of
*different* colours, canonically equal under *one* declaration colour, with a
collapsing root on one side. -/

def leftA2x : WTerm := .baseQuote (.baseDrop .wrappedZero)

def rightA2x : WTerm := .wrappedZero

theorem a2x_root_colours_differ : rootColour leftA2x ≠ rootColour rightA2x := by decide

theorem a2x_collapsing_root : collapsingRoot .base leftA2x = true := rfl

theorem a2x_canonically_equal : canonW .base leftA2x = canonW .base rightA2x := rfl

/-- …and the left endpoint of that configuration is a mixed term, hence not
nameable by the indexed presentation. -/
theorem a2x_left_is_mixed (c : Colour) : isUniform c leftA2x = false := by cases c <;> rfl

theorem a2x_left_not_decorated (c : Colour) (t : Term) : decorate c t ≠ leftA2x := by
  intro h
  have h1 : isUniform c leftA2x = true := by rw [← h]; exact isUniform_decorate c t
  rw [a2x_left_is_mixed c] at h1
  exact Bool.noConfusion h1

/-! ## 8. The residual obligation

An identity key that is invariant under the single-colour canonicalizer.  In
the external record-based model this is a field (`nf_key`) and its invariance
is a projection.  Here it must be *constructed* and its invariance *proved*. -/

def key (w : WTerm) : List Term := collect (canon (eraseW w))

def keyList : List WTerm → List Term
  | [] => []
  | w :: ws => key w ++ keyList ws

/-- Toy Cost₁: canonically equal woven terms have equal identity keys. -/
def Cost1Toy (d : Colour) : Prop :=
  ∀ w₁ w₂ : WTerm, canonW d w₁ = canonW d w₂ → key w₁ = key w₂

/-- The residual: the key is invariant under the single-colour canonicalizer. -/
def KeyInvariant (d : Colour) : Prop := ∀ w : WTerm, key (canonW d w) = key w

theorem cost1Toy_of_keyInvariant (d : Colour) (h : KeyInvariant d) : Cost1Toy d := by
  intro w₁ w₂ hcanon
  rw [← h w₁, ← h w₂, hcanon]

theorem key_atoms (w : WTerm) : (key w).all isAtom = true := collect_atoms _

theorem keyList_atoms : ∀ (l : List WTerm), (keyList l).all isAtom = true
  | [] => rfl
  | w :: ws => by simp [keyList, List.all_append, key_atoms w, keyList_atoms ws]

theorem keyList_append :
    ∀ (l₁ l₂ : List WTerm), keyList (l₁ ++ l₂) = keyList l₁ ++ keyList l₂
  | [], _ => rfl
  | w :: ws, l₂ => by simp [keyList, keyList_append ws l₂, List.append_assoc]

theorem key_par (a b : WTerm) (h : eraseW a = eraseW a) :
    collect (canon (.par (eraseW a) (eraseW b))) = key a ++ key b := by
  simp only [canon, key]
  exact collect_rebuild _ (by simp [List.all_append, collect_atoms])

end ClaudeIndexedCost
