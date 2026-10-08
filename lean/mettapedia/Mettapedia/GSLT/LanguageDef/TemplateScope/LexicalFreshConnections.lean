import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus
import Mettapedia.GSLT.LanguageDef.TemplateScope.Adjoints
import Mettapedia.GSLT.LanguageDef.TemplateScope.Hygiene

/-!
# Lexical fresh: connections

Readings of the lexical-fresh model against other parts of Mettapedia, each a
small theorem on the model with a positive and a negative example.

* **Metadata survival** (`canon_roundtrip`, `translation_text_roundtrip`,
  `copy_keeps_identity`, `quotation_forgets_new`): the elaborated term carries
  every identity and own list through the canonical form; the translation
  writes rule M's inferred metadata into the surface (crossing sets and `new`),
  so printing and reading the translated text back elaborates to rule M's term
  exactly; activation copies keep the identity they copy; quotation is lossy.
* **Matching, not unification** (`matchSteps_length_le`, `unify_is_matching`,
  `unify_nonground_no_answer`): in the model a pattern is matched against a
  ground value by one structural pass that demands at most one binding per
  hole; `unify` elaborates to the same matching, so the model never poses the
  general unification problem, and it gives no answer where a unifier would
  return a constraint.
* **Freshness** (`elabLFId_keys`, `let_slot_fresh_in_value`,
  `sibling_slots_apart`): every slot an elaborated term mentions comes from its
  environment or is introduced inside it; hence a pattern's fresh slot is apart
  from the `let`'s value and from every sibling, the content of a GSLT
  `FreshnessCondition` premise `x # P` (`OSLF.MeTTaIL.Syntax`).
* **The adjoint reading** (remark, one lemma per row) and **the rho reading**
  (`per_call_replicas`, `per_closure_shared`, with the corpus rows).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v} [DecidableEq X]

/-! ## Metadata survival -/

/-- **The canonical form carries every identity.**  Printing an elaborated
term in the canonical form and reading it back gives the term, its binder
identities and its derived own lists included. -/
theorem canon_roundtrip (R : Owner) (t : Src S X) :
    readCanon (printCanon (elabLFFormAt R t)) = some (elabLFFormAt R t) ∧
      readCanon (printCanon (elabMFormAt R t)) = some (elabMFormAt R t) :=
  ⟨readCanon_printCanon _, readCanon_printCanon _⟩

/-- The translation writes no pattern quotation into a text that has none. -/
theorem noPQuote_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    t.NoPQuote = true → (toLexAt E cr env fr pos t).NoPQuote = true
  | .sym _, _, _, _, _, _, h => h
  | .fn _, _, _, _, _, _, h => h
  | .sv _, _, _, _, _, _, h => h
  | .par _, _, _, _, _, _, h => h
  | .quote _, _, _, _, _, _, h => h
  | .pquote _, _, _, _, _, _, h => by simp [Src.NoPQuote] at h
  | .lam z none b, E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote] at h
      simp only [toLexAt, Src.NoPQuote]
      cases mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b (ownRuleMDefault E b) <;>
        simp only [wrapNew, Src.NoPQuote] <;> exact noPQuote_toLexAt b _ _ _ _ _ h
  | .lam z (some sh) b, E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote] at h
      simp only [toLexAt, Src.NoPQuote]
      exact noPQuote_toLexAt b _ _ _ _ _ h
  | .app f a, E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      simp only [toLexAt, Src.NoPQuote, Bool.and_eq_true]
      exact ⟨noPQuote_toLexAt f _ _ _ _ _ h.1, noPQuote_toLexAt a _ _ _ _ _ h.2⟩
  | .letS p w b none, E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      simp only [toLexAt, Src.NoPQuote, Bool.and_eq_true]
      exact ⟨⟨noPQuote_toLexAt p _ _ _ _ _ h.1.1, noPQuote_toLexAt w _ _ _ _ _ h.1.2⟩,
        noPQuote_toLexAt b _ _ _ _ _ h.2⟩
  | .letS p w b (some _), E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      simp only [toLexAt, Src.NoPQuote, Bool.and_eq_true]
      exact ⟨⟨noPQuote_toLexAt p _ _ _ _ _ h.1.1, noPQuote_toLexAt w _ _ _ _ _ h.1.2⟩,
        noPQuote_toLexAt b _ _ _ _ _ h.2⟩
  | .unify p w b, E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      simp only [toLexAt, Src.NoPQuote, Bool.and_eq_true]
      exact ⟨⟨noPQuote_toLexAt p _ _ _ _ _ h.1.1, noPQuote_toLexAt w _ _ _ _ _ h.1.2⟩,
        noPQuote_toLexAt b _ _ _ _ _ h.2⟩
  | .alt t₁ t₂, E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      simp only [toLexAt, Src.NoPQuote, Bool.and_eq_true]
      exact ⟨noPQuote_toLexAt t₁ _ _ _ _ _ h.1, noPQuote_toLexAt t₂ _ _ _ _ _ h.2⟩
  | .new ys b, E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote] at h
      simp only [toLexAt, Src.NoPQuote]
      exact noPQuote_toLexAt b _ _ _ _ _ h
  | .form _ b, E, cr, env, fr, pos, h => by
      simp only [Src.NoPQuote] at h
      simp only [toLexAt, Src.NoPQuote]
      exact noPQuote_toLexAt b _ _ _ _ _ h

/-- **A semantic round trip through text.**  The translated program, printed as
Prime text and read back, elaborates under lexical fresh to the very term rule
M elaborates the source to: the surface of the translation carries rule M's
inferred metadata (crossing sets and `new` blocks), so nothing is lost. -/
theorem translation_text_roundtrip (R : Owner) (t : Src S X) (h : t.NoPQuote = true) :
    (readSrc (printSrc (toLexicalAt R t))).map (elabLFFormAt R) = some (elabMFormAt R t) := by
  have hr : readSrc (printSrc (toLexicalAt R t)) = some (toLexicalAt R t) :=
    readSrc_printSrc (noPQuote_toLexAt t _ _ _ _ _ h)
  rw [hr, Option.map_some, elabLFFormAt_toLexicalAt]

/-- The identity a store name copies. -/
def Nm.base {Y : Type v} : Nm Y → Y
  | .src y => y
  | .inst _ n => Nm.base n

/-- **Activation keeps identities**: the copy an activation makes of an own
slot is tagged by the activation's path and keeps the slot's identity. -/
theorem copy_keeps_identity (ρ : Path) (own : List (BId X)) {k : BId X} (hk : k ∈ own) :
    (renameOwn ρ own (.src k) : Option (Tm S (BId X))) = some (.var (.inst ρ (.src k))) ∧
      Nm.base (Nm.inst ρ (.src k)) = k := by
  refine ⟨?_, rfl⟩
  simp [renameOwn, ownKey, hk]

/-! ## Matching, not unification -/

/-- The store-name holes of a pattern: the matcher binds at most one value per
hole.  Inside code the count follows the code matcher under binders. -/
def holeCount {Y : Type v} : Tm S Y → ℕ
  | .var _ => 1
  | .lam _ _ b => holeCount b
  | .app f a => holeCount f + holeCount a
  | .quote c => holeCount c
  | .pquote c => holeCount c
  | .letP p w b => holeCount p + holeCount w + holeCount b
  | .alt t₁ t₂ => holeCount t₁ + holeCount t₂
  | _ => 0

/-- Code matching binds at most one value per hole, binders included. -/
theorem matchCodeStepsIn_length_le [DecidableEq S] :
    ∀ (bound : List (Nm (BId X))) (p t : Tm S (BId X))
      (s : Steps (Nm (BId X)) (GVal S (BId X))),
      matchCodeStepsIn bound p t = some s → s.length ≤ holeCount p
  | _, .var n, t, s, h => by
      simp only [matchCodeStepsIn] at h
      by_cases hh : CodeId.hole n = true
      · rw [if_pos hh] at h
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        simp [holeCount]
      · rw [if_neg hh] at h
        cases t with
        | var m =>
            simp only at h
            by_cases hs : CodeId.same n m = true
            · rw [if_pos hs] at h
              cases h
              exact Nat.zero_le _
            · rw [if_neg hs] at h
              cases h
        | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
            cases h
  | _, .pvar _, .pvar _, s, h => by
      simp only [matchCodeStepsIn] at h
      split at h <;> cases h
      exact Nat.zero_le _
  | _, .pvar _, .sym _, _, h | _, .pvar _, .fn _, _, h | _, .pvar _, .var _, _, h
    | _, .pvar _, .lam _ _ _, _, h | _, .pvar _, .app _ _, _, h | _, .pvar _, .quote _, _, h
    | _, .pvar _, .pquote _, _, h | _, .pvar _, .letP _ _ _, _, h | _, .pvar _, .alt _ _, _, h
    | _, .pvar _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | bound, .lam x₁ own₁ b₁, .lam x₂ own₂ b₂, s, h => by
      simp only [matchCodeStepsIn] at h
      by_cases hc : (CodeId.same x₁ x₂ && decide (own₁ = own₂)) = true
      · rw [if_pos hc] at h
        simpa [holeCount] using matchCodeStepsIn_length_le (bound ++ [x₂]) b₁ b₂ s h
      · rw [if_neg hc] at h
        cases h
  | _, .lam _ _ _, .sym _, _, h | _, .lam _ _ _, .fn _, _, h | _, .lam _ _ _, .var _, _, h
    | _, .lam _ _ _, .pvar _, _, h | _, .lam _ _ _, .app _ _, _, h | _, .lam _ _ _, .quote _, _, h
    | _, .lam _ _ _, .pquote _, _, h | _, .lam _ _ _, .letP _ _ _, _, h
    | _, .lam _ _ _, .alt _ _, _, h | _, .lam _ _ _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | bound, .app p₁ p₂, .app t₁ t₂, s, h => by
      simp only [matchCodeStepsIn, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨s₁, h₁, s₂, h₂, rfl⟩ := h
      have := matchCodeStepsIn_length_le bound p₁ t₁ s₁ h₁
      have := matchCodeStepsIn_length_le bound p₂ t₂ s₂ h₂
      simp only [List.length_append, holeCount]
      omega
  | _, .app _ _, .sym _, _, h | _, .app _ _, .fn _, _, h | _, .app _ _, .var _, _, h
    | _, .app _ _, .pvar _, _, h | _, .app _ _, .lam _ _ _, _, h | _, .app _ _, .quote _, _, h
    | _, .app _ _, .pquote _, _, h | _, .app _ _, .letP _ _ _, _, h | _, .app _ _, .alt _ _, _, h
    | _, .app _ _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | bound, .letP p₁ w₁ b₁, .letP p₂ w₂ b₂, s, h => by
      simp only [matchCodeStepsIn, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, rfl⟩ := h
      have := matchCodeStepsIn_length_le bound p₁ p₂ s₁ h₁
      have := matchCodeStepsIn_length_le bound w₁ w₂ s₂ h₂
      have := matchCodeStepsIn_length_le bound b₁ b₂ s₃ h₃
      simp only [List.length_append, holeCount]
      omega
  | _, .letP _ _ _, .sym _, _, h | _, .letP _ _ _, .fn _, _, h | _, .letP _ _ _, .var _, _, h
    | _, .letP _ _ _, .pvar _, _, h | _, .letP _ _ _, .lam _ _ _, _, h | _, .letP _ _ _, .app _ _, _, h
    | _, .letP _ _ _, .quote _, _, h | _, .letP _ _ _, .pquote _, _, h | _, .letP _ _ _, .alt _ _, _, h
    | _, .letP _ _ _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | bound, .alt p₁ p₂, .alt t₁ t₂, s, h => by
      simp only [matchCodeStepsIn, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨s₁, h₁, s₂, h₂, rfl⟩ := h
      have := matchCodeStepsIn_length_le bound p₁ t₁ s₁ h₁
      have := matchCodeStepsIn_length_le bound p₂ t₂ s₂ h₂
      simp only [List.length_append, holeCount]
      omega
  | _, .alt _ _, .sym _, _, h | _, .alt _ _, .fn _, _, h | _, .alt _ _, .var _, _, h
    | _, .alt _ _, .pvar _, _, h | _, .alt _ _, .lam _ _ _, _, h | _, .alt _ _, .app _ _, _, h
    | _, .alt _ _, .quote _, _, h | _, .alt _ _, .pquote _, _, h | _, .alt _ _, .letP _ _ _, _, h
    | _, .alt _ _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | _, .sym _, .sym _, s, h => by
      simp only [matchCodeStepsIn] at h
      split at h <;> cases h
      exact Nat.zero_le _
  | _, .sym _, .fn _, _, h | _, .sym _, .var _, _, h | _, .sym _, .pvar _, _, h
    | _, .sym _, .lam _ _ _, _, h | _, .sym _, .app _ _, _, h | _, .sym _, .quote _, _, h
    | _, .sym _, .pquote _, _, h | _, .sym _, .letP _ _ _, _, h | _, .sym _, .alt _ _, _, h
    | _, .sym _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | _, .fn _, .fn _, s, h => by
      simp only [matchCodeStepsIn] at h
      split at h <;> cases h
      exact Nat.zero_le _
  | _, .fn _, .sym _, _, h | _, .fn _, .var _, _, h | _, .fn _, .pvar _, _, h
    | _, .fn _, .lam _ _ _, _, h | _, .fn _, .app _ _, _, h | _, .fn _, .quote _, _, h
    | _, .fn _, .pquote _, _, h | _, .fn _, .letP _ _ _, _, h | _, .fn _, .alt _ _, _, h
    | _, .fn _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | _, .quote _, .quote _, s, h => by
      simp only [matchCodeStepsIn] at h
      split at h <;> cases h
      exact Nat.zero_le _
  | _, .quote _, .sym _, _, h | _, .quote _, .fn _, _, h | _, .quote _, .var _, _, h
    | _, .quote _, .pvar _, _, h | _, .quote _, .lam _ _ _, _, h | _, .quote _, .app _ _, _, h
    | _, .quote _, .pquote _, _, h | _, .quote _, .letP _ _ _, _, h | _, .quote _, .alt _ _, _, h
    | _, .quote _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | bound, .pquote pc, .quote c, s, h => by
      simp only [matchCodeStepsIn] at h
      simpa [holeCount] using matchCodeStepsIn_length_le bound pc c s h
  | _, .pquote _, .sym _, _, h | _, .pquote _, .fn _, _, h | _, .pquote _, .var _, _, h
    | _, .pquote _, .pvar _, _, h | _, .pquote _, .lam _ _ _, _, h | _, .pquote _, .app _ _, _, h
    | _, .pquote _, .pquote _, _, h | _, .pquote _, .letP _ _ _, _, h | _, .pquote _, .alt _ _, _, h
    | _, .pquote _, .ctx _ _, _, h => by
      unfold matchCodeStepsIn at h
      cases h
  | _, .ctx _ _, _, _, h => by
      unfold matchCodeStepsIn at h
      cases h

theorem matchCodeSteps_length_le [DecidableEq S]
    (p t : Tm S (BId X)) (s : Steps (Nm (BId X)) (GVal S (BId X)))
    (h : matchCodeSteps p t = some s) : s.length ≤ holeCount p := by
  unfold matchCodeSteps at h
  exact matchCodeStepsIn_length_le [] p t s h

/-- **Matching demands at most one binding per hole**, in one structural pass:
it never introduces a constraint of its own. -/
theorem matchSteps_length_le [DecidableEq S] : ∀ (p t : Tm S (BId X)) (s : Steps (Nm (BId X)) (GVal S (BId X))),
    matchSteps p t = some s → s.length ≤ holeCount p
  | .var n, t, s, h => by
      simp only [matchSteps, Option.map_eq_some_iff] at h
      obtain ⟨g, -, rfl⟩ := h
      simp [holeCount]
  | .app p₁ p₂, .app t₁ t₂, s, h => by
      simp only [matchSteps, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨s₁, h₁, s₂, h₂, rfl⟩ := h
      have := matchSteps_length_le p₁ t₁ s₁ h₁
      have := matchSteps_length_le p₂ t₂ s₂ h₂
      simp only [List.length_append, holeCount]
      omega
  | .pquote pc, .quote c, s, h => by
      simp only [matchSteps] at h
      simpa [holeCount] using matchCodeSteps_length_le pc c s h
  | .quote _, .quote _, s, h => by
      simp only [matchSteps] at h
      split at h <;> cases h
      exact Nat.zero_le _
  | .app _ _, .sym _, _, h | .app _ _, .fn _, _, h | .app _ _, .var _, _, h | .app _ _, .pvar _, _, h
  | .app _ _, .lam _ _ _, _, h | .app _ _, .quote _, _, h | .app _ _, .pquote _, _, h
  | .app _ _, .letP _ _ _, _, h | .app _ _, .alt _ _, _, h | .app _ _, .ctx _ _, _, h
  | .pquote _, .sym _, _, h | .pquote _, .fn _, _, h | .pquote _, .var _, _, h | .pquote _, .pvar _, _, h
  | .pquote _, .lam _ _ _, _, h | .pquote _, .app _ _, _, h | .pquote _, .pquote _, _, h
  | .pquote _, .letP _ _ _, _, h | .pquote _, .alt _ _, _, h | .pquote _, .ctx _ _, _, h => by
      unfold matchSteps at h
      split at h <;> cases h; exact Nat.zero_le _
  | .sym _, t, _, h | .fn _, t, _, h | .pvar _, t, _, h
  | .lam _ _ _, t, _, h | .quote _, t, _, h | .letP _ _ _, t, _, h | .alt _ _, t, _, h => by
      cases t with
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          unfold matchSteps at h
          split at h <;> cases h; exact Nat.zero_le _
  | .ctx _ _, t, s, h => by
      simp only [matchSteps] at h
      split at h <;> cases h
      exact Nat.zero_le _

/-- **`unify` is matching in the model**: under lexical fresh it elaborates to
the same `let` node as a pattern whose names are all in force: the pattern is
matched against the value, refining slots in scope. -/
theorem unify_is_matching (cr : List X) (env : IEnv X) (pv : X → Owner) (fr pos : Owner)
    (p w b : Src S X) :
    elabLFId cr env pv fr pos (.unify p w b) =
      .letP (elabLFId cr env pv fr (pos ++ [0]) p) (elabLFId cr env pv fr (pos ++ [1]) w)
        (elabLFId cr env pv fr (pos ++ [2]) b) := rfl

/-! ## Freshness: a pattern's slot is apart from its context -/

/-- The slot identities a term mentions. -/
def slotKeys (t : Tm S (BId X)) : List (SlotId X) :=
  (Tm.vars t).filterMap fun n =>
    match n with
    | .src (.slot k) => some k
    | _ => none

omit [DecidableEq X] in
theorem mem_slotKeys {t : Tm S (BId X)} {k : SlotId X} :
    k ∈ slotKeys t ↔ Nm.src (BId.slot k) ∈ Tm.vars t := by
  unfold slotKeys
  constructor
  · intro h
    obtain ⟨n, hn, he⟩ := List.mem_filterMap.1 h
    match n, he with
    | .src (.slot k'), he =>
        simp only [Option.some.injEq] at he
        subst he
        exact hn
  · intro h
    exact List.mem_filterMap.2 ⟨_, h, rfl⟩

theorem vars_foldBind {Y : Type v} (ps : List (Nm Y)) (t : Tm S Y) :
    Tm.vars (ps.foldr (fun p acc => .lam p [] acc) t) = Tm.vars t := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldr, Tm.vars, ih]

theorem slotKeys_sealParams (t : Tm S (BId X)) : slotKeys (sealParams t) = slotKeys t := by
  unfold slotKeys sealParams
  rw [vars_foldBind]

/-- A root head slot: the query cell a sealed hole denotes. -/
def rootHead (k : SlotId X) : Prop :=
  k.frame = [] ∧ k.site = [] ∧ k.intro = .head

/-- Every slot sealed code mentions is a root head slot, at any
quotation-relative position. A binder of the code is not a slot. -/
theorem slotKeys_codeIAt (penv senv : List (X × Owner)) (pos : Owner) :
    ∀ c : Src S X, ∀ k ∈ slotKeys (codeIAt none penv senv pos c), rootHead k
  | .sym _, _, h => by simp [codeIAt, slotKeys, Tm.vars] at h
  | .fn _, _, h => by simp [codeIAt, slotKeys, Tm.vars] at h
  | .sv y, k, h => by
      rw [mem_slotKeys] at h
      simp only [codeIAt] at h
      cases hlu : codeLookup senv y with
      | some _ =>
          rw [hlu] at h
          simp only [Tm.vars] at h
          cases h
      | none =>
          rw [hlu] at h
          simp only [iVar, Tm.vars, List.mem_singleton] at h
          injection h with h
          injection h with h
          subst h
          exact ⟨rfl, rfl, rfl⟩
  | .par z, _, h => by
      rw [mem_slotKeys] at h
      simp only [codeIAt] at h
      cases hlu : codeLookup penv z with
      | some _ =>
          rw [hlu] at h
          simp only [Tm.vars] at h
          cases h
      | none =>
          rw [hlu] at h
          simp only [Tm.vars] at h
          cases h
  | .lam z _ b, k, h => by
      have h' : k ∈ slotKeys (codeIAt none ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      exact slotKeys_codeIAt ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b k h'
  | .form z b, k, h => by
      have h' : k ∈ slotKeys (codeIAt none ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      exact slotKeys_codeIAt ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b k h'
  | .app f a, k, h => by
      simp only [codeIAt, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with h | h
      · exact slotKeys_codeIAt penv senv (pos ++ [0]) f k (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt penv senv (pos ++ [1]) a k (by simpa [slotKeys] using h)
  | .quote c, k, h => by
      have hseal : k ∈ slotKeys (sealParams (codeIAt none [] [] [] c)) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      rw [slotKeys_sealParams] at hseal
      exact slotKeys_codeIAt [] [] [] c k hseal
  | .pquote c, k, h => by
      have h' : k ∈ slotKeys (codeIAt none [] [] [] c) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      exact slotKeys_codeIAt [] [] [] c k h'
  | .letS p w b _, k, h => by
      simp only [codeIAt, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with (h | h) | h
      · exact slotKeys_codeIAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p k
          (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt penv senv (pos ++ [1]) w k (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b k
          (by simpa [slotKeys] using h)
  | .unify p w b, k, h => by
      simp only [codeIAt, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with (h | h) | h
      · exact slotKeys_codeIAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p k
          (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt penv senv (pos ++ [1]) w k (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b k
          (by simpa [slotKeys] using h)
  | .alt t₁ t₂, k, h => by
      simp only [codeIAt, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with h | h
      · exact slotKeys_codeIAt penv senv (pos ++ [0]) t₁ k (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt penv senv (pos ++ [1]) t₂ k (by simpa [slotKeys] using h)
  | .new _ b, k, h => by
      have h' : k ∈ slotKeys (codeIAt none penv senv (pos ++ [0]) b) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      exact slotKeys_codeIAt penv senv (pos ++ [0]) b k h'

/-- Every slot sealed code mentions is a root head slot. -/
theorem slotKeys_codeI (c : Src S X) :
    ∀ k ∈ slotKeys (codeI c : Tm S (BId X)), rootHead k := by
  intro k hk
  rw [codeI, slotKeys_sealParams] at hk
  exact slotKeys_codeIAt [] [] [] c k hk

/-- A pattern quotation's holes are the surrounding environment's slots. -/
theorem slotKeys_codeIAt_env (env : IEnv X) (penv senv : List (X × Owner)) (pos : Owner) :
    ∀ (c : Src S X) (k : SlotId X), k ∈ slotKeys (codeIAt (some env) penv senv pos c) →
      (∃ y, env y = k) ∨ rootHead k
  | .sym _, _, h => by simp [codeIAt, slotKeys, Tm.vars] at h
  | .fn _, _, h => by simp [codeIAt, slotKeys, Tm.vars] at h
  | .sv y, k, h => by
      rw [mem_slotKeys] at h
      simp only [codeIAt] at h
      cases hlu : codeLookup senv y with
      | some _ =>
          rw [hlu] at h
          simp only [Tm.vars] at h
          cases h
      | none =>
          rw [hlu] at h
          simp only [iVar, Tm.vars, List.mem_singleton] at h
          injection h with h
          injection h with h
          exact Or.inl ⟨y, h.symm⟩
  | .par z, _, h => by
      rw [mem_slotKeys] at h
      simp only [codeIAt] at h
      cases hlu : codeLookup penv z with
      | some _ =>
          rw [hlu] at h
          simp only [Tm.vars] at h
          cases h
      | none =>
          rw [hlu] at h
          simp only [Tm.vars] at h
          cases h
  | .lam z _ b, k, h => by
      have h' : k ∈ slotKeys (codeIAt (some env) ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      exact slotKeys_codeIAt_env env ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b k h'
  | .form z b, k, h => by
      have h' : k ∈ slotKeys (codeIAt (some env) ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      exact slotKeys_codeIAt_env env ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b k h'
  | .app f a, k, h => by
      simp only [codeIAt, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with h | h
      · exact slotKeys_codeIAt_env env penv senv (pos ++ [0]) f k (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt_env env penv senv (pos ++ [1]) a k (by simpa [slotKeys] using h)
  | .quote c, k, h => by
      have hseal : k ∈ slotKeys (sealParams (codeIAt none [] [] [] c)) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      rw [slotKeys_sealParams] at hseal
      exact Or.inr (slotKeys_codeIAt [] [] [] c k hseal)
  | .pquote c, k, h => by
      have h' : k ∈ slotKeys (codeIAt (some env) [] [] [] c) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      exact slotKeys_codeIAt_env env [] [] [] c k h'
  | .letS p w b _, k, h => by
      simp only [codeIAt, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with (h | h) | h
      · exact slotKeys_codeIAt_env env penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p k
          (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt_env env penv senv (pos ++ [1]) w k (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt_env env penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b k
          (by simpa [slotKeys] using h)
  | .unify p w b, k, h => by
      simp only [codeIAt, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with (h | h) | h
      · exact slotKeys_codeIAt_env env penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p k
          (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt_env env penv senv (pos ++ [1]) w k (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt_env env penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b k
          (by simpa [slotKeys] using h)
  | .alt t₁ t₂, k, h => by
      simp only [codeIAt, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with h | h
      · exact slotKeys_codeIAt_env env penv senv (pos ++ [0]) t₁ k (by simpa [slotKeys] using h)
      · exact slotKeys_codeIAt_env env penv senv (pos ++ [1]) t₂ k (by simpa [slotKeys] using h)
  | .new _ b, k, h => by
      have h' : k ∈ slotKeys (codeIAt (some env) penv senv (pos ++ [0]) b) := by
        simpa [codeIAt, slotKeys, Tm.vars] using h
      exact slotKeys_codeIAt_env env penv senv (pos ++ [0]) b k h'

theorem prefix_of_append {pos q : Owner} {i : ℕ} (h : (pos ++ [i]) <+: q) : pos <+: q :=
  (List.prefix_append pos [i]).trans h

/-- **Every slot an elaborated term mentions is its environment's, or was
introduced inside it** (its site extends the term's position). -/
theorem elabLFId_keys : ∀ (t : Src S X) (cr : List X) (env : IEnv X) (pv : X → Owner) (fr pos : Owner),
    ∀ k ∈ slotKeys (elabLFId cr env pv fr pos t),
      (∃ y, env y = k) ∨ pos <+: k.site ∨ rootHead k
  | .sym _, _, _, _, _, _, k, h => by simp [elabLFId, slotKeys, Tm.vars] at h
  | .fn _, _, _, _, _, _, k, h => by simp [elabLFId, slotKeys, Tm.vars] at h
  | .sv y, _, env, _, _, _, k, h => by
      simp only [elabLFId, iVar, slotKeys, Tm.vars, List.filterMap_cons, List.filterMap_nil,
        List.mem_singleton] at h
      exact Or.inl ⟨y, h.symm⟩
  | .par _, _, _, _, _, _, k, h => by simp [elabLFId, slotKeys, Tm.vars] at h
  | .quote c, _, _, _, _, _, k, h => by
      simp only [elabLFId, slotKeys, Tm.vars] at h
      exact Or.inr (Or.inr (slotKeys_codeI c k (by simpa [slotKeys] using h)))
  | .lam z xs b, cr, env, pv, fr, pos, k, h => by
      simp only [elabLFId] at h
      have h' : k ∈ slotKeys (elabLFId (crossIn xs (crossOwn xs (Src.uses b) []) cr)
          (env.set (crossOwn xs (Src.uses b) []) fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩)
          (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b) := by
        simpa [slotKeys, Tm.vars] using h
      rcases elabLFId_keys b _ _ _ _ _ k h' with ⟨y, hy⟩ | hp | hr
      · by_cases hyo : y ∈ crossOwn xs (Src.uses b) []
        · rw [IEnv.set_of_mem hyo] at hy
          subst hy
          exact Or.inr (Or.inl (List.prefix_append pos [0]))
        · rw [IEnv.set_of_not_mem hyo] at hy
          exact Or.inl ⟨y, hy⟩
      · exact Or.inr (Or.inl (prefix_of_append hp))
      · exact Or.inr (Or.inr hr)
  | .app f a, cr, env, pv, fr, pos, k, h => by
      simp only [elabLFId, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with h | h
      · rcases elabLFId_keys f cr env pv fr _ k h with h | hp | hr
        · exact Or.inl h
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
      · rcases elabLFId_keys a cr env pv fr _ k h with h | hp | hr
        · exact Or.inl h
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
  | .pquote c, _, env, _, _, _, k, h => by
      have h' : k ∈ slotKeys (codeIAt (some env) [] [] [] c) := by
        have hs : k ∈ slotKeys (sealParams (codeIAt (some env) [] [] [] c)) := by
          simpa [elabLFId, slotKeys, Tm.vars] using h
        rwa [slotKeys_sealParams] at hs
      rcases slotKeys_codeIAt_env env [] [] [] c k h' with hy | hr
      · exact Or.inl hy
      · exact Or.inr (Or.inr hr)
  | .letS p w b xs, cr, env, pv, fr, pos, k, h => by
      simp only [elabLFId, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      have hset : ∀ y, (env.set (lfIntro xs p cr) fun y => ⟨y, fr, pos, .pat⟩) y = k →
          (∃ y, env y = k) ∨ pos <+: k.site ∨ rootHead k := by
        intro y hy
        by_cases hyo : y ∈ lfIntro xs p cr
        · rw [IEnv.set_of_mem hyo] at hy
          subst hy
          exact Or.inr (Or.inl (List.prefix_refl _))
        · rw [IEnv.set_of_not_mem hyo] at hy
          exact Or.inl ⟨y, hy⟩
      rcases h with (h | h) | h
      · rcases elabLFId_keys p _ _ pv fr _ k h with ⟨y, hy⟩ | hp | hr
        · exact hset y hy
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
      · rcases elabLFId_keys w cr env pv fr _ k h with h | hp | hr
        · exact Or.inl h
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
      · rcases elabLFId_keys b _ _ pv fr _ k h with ⟨y, hy⟩ | hp | hr
        · exact hset y hy
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
  | .unify p w b, cr, env, pv, fr, pos, k, h => by
      simp only [elabLFId, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with (h | h) | h
      · rcases elabLFId_keys p cr env pv fr _ k h with h | hp | hr
        · exact Or.inl h
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
      · rcases elabLFId_keys w cr env pv fr _ k h with h | hp | hr
        · exact Or.inl h
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
      · rcases elabLFId_keys b cr env pv fr _ k h with h | hp | hr
        · exact Or.inl h
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
  | .alt t₁ t₂, cr, env, pv, fr, pos, k, h => by
      simp only [elabLFId, slotKeys, Tm.vars, List.filterMap_append, List.mem_append] at h
      rcases h with h | h
      · rcases elabLFId_keys t₁ cr env pv fr _ k h with h | hp | hr
        · exact Or.inl h
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
      · rcases elabLFId_keys t₂ cr env pv fr _ k h with h | hp | hr
        · exact Or.inl h
        · exact Or.inr (Or.inl (prefix_of_append hp))
        · exact Or.inr (Or.inr hr)
  | .new ys b, cr, env, pv, fr, pos, k, h => by
      simp only [elabLFId] at h
      rcases elabLFId_keys b _ _ pv fr pos k h with ⟨y, hy⟩ | hp | hr
      · by_cases hyo : y ∈ ys
        · rw [IEnv.set_of_mem hyo] at hy
          subst hy
          exact Or.inr (Or.inl (List.prefix_refl _))
        · rw [IEnv.set_of_not_mem hyo] at hy
          exact Or.inl ⟨y, hy⟩
      · exact Or.inr (Or.inl hp)
      · exact Or.inr (Or.inr hr)
  | .form z b, cr, env, pv, _, pos, k, h => by
      simp only [elabLFId] at h
      have h' : k ∈ slotKeys (elabLFId cr (env.set [] (fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩))
          (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b) := by
        simpa [slotKeys, Tm.vars] using h
      rcases elabLFId_keys b _ _ _ _ _ k h' with ⟨y, hy⟩ | hp | hr
      · rw [IEnv.set_nil] at hy
        exact Or.inl ⟨y, hy⟩
      · exact Or.inr (Or.inl (prefix_of_append hp))
      · exact Or.inr (Or.inr hr)

/-- **A pattern's fresh slot is apart from the `let`'s value** (`x # P`): the
slot a `let` at `P` introduces does not occur in the elaboration of its value,
unless the environment already held it. -/
theorem let_slot_fresh_in_value (cr : List X) (env : IEnv X) (pv : X → Owner) (fr P : Owner)
    (w : Src S X) {k : SlotId X} (hk : k.site = P) (henv : ∀ y, env y ≠ k)
    (hnot : ¬ rootHead k) :
    k ∉ slotKeys (elabLFId cr env pv fr (P ++ [1]) w) := by
  intro h
  rcases elabLFId_keys w cr env pv fr _ k h with ⟨y, hy⟩ | hp | hr
  · exact henv y hy
  · rw [hk] at hp
    have := hp.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  · exact absurd hr hnot

/-- **The rule-M side of the same row has no such apartness.**  Row 23a,
`(Pair (let $x 1 $x) (let $x 2 $x))`: lexical fresh gives each `let` its own
slot, mentioned only inside it; rule M gives both one slot, the query's. -/
theorem sibling_slots_apart :
    slotKeys (elabLFFormAt [] SpectrumCorpus.row23a) =
        [⟨.x, [], [0, 1], .pat⟩, ⟨.x, [], [0, 1], .pat⟩, ⟨.x, [], [1], .pat⟩, ⟨.x, [], [1], .pat⟩] ∧
      slotKeys (elabMFormAt [] SpectrumCorpus.row23a) =
        [⟨.x, [], [], .head⟩, ⟨.x, [], [], .head⟩, ⟨.x, [], [], .head⟩, ⟨.x, [], [], .head⟩] := by
  constructor <;> decide +kernel

/-! ## The adjoint reading (remark, one lemma per row)

For a context extension `p : Γ.A → Γ`, the type face has `Σ_p ⊣ p* ⊣ Π_p`
(`TypeTheory.PresheafDependentAdjunction`) and the predicate face
`∃_p ⊣ p* ⊣ ∀_p` (`GSLT.Topos.PresheafPredicateFirstOrder`).  The rows read
lexical fresh's constructs; naming an adjunction establishes no surface
policy, elaboration or scheduling law, and an adjoint product need not be a
substitution-stable former (`TypeTheory.CategoryIndexedFamilyGeneralPiBoundary`).

| Construct | Reading | Lemma on the model |
|---|---|---|
| a crossing name `{…}` | `p*`: the inner scope sees the outer variable | `crossing_name_outer`, `lf_crossing_outer` |
| a fresh pattern name, per call | `∃_p`: a new variable of the frame, copied per activation | `let_slot_fresh_in_value`, `fresh_per_call` |
| `(new ($h) body)` | `Σ_y` written explicitly | `body_only_translated` |
| per-call hole / captured hole | `Π_x Σ_y R` / a parameter (`Σ_y Π_x R` when persistent) | `body_only_translated`, `run_lifted_call`, `holes_per_call_persistent` |
| a lambda; its application | the transpose of `Π`; the counit, β | `run_beta` |
| `unify` and a shared pattern | a refinement procedure for an equality constraint: it records, or fails on a conflict; the model's has no alternatives and no residuals | `matchT_eq_refineRun`, `refine_conflict`, `unify_nonground_no_answer` |
| rule M's spelling | contraction built into spelling: a refining pattern is an equation rule M adds silently, which the translation writes | `mem_tMarks` |

Effects, partiality, grades and costs keep their resumable interpretation;
the rows give no unqualified `∀` reading. -/

/-- `p*` under lexical fresh: a name a lambda's crossing set shares keeps the
slot the enclosing scope gives it. -/
theorem lf_crossing_outer (env : IEnv X) (sh U : List X) (o : Owner) {y : X} (hy : y ∈ sh) :
    (env.set (crossOwn (some sh) U []) fun y => ⟨y, o, o, .head⟩) y = env y := by
  apply IEnv.set_of_not_mem
  simp [crossOwn, List.mem_dedup, hy]

/-- Rule M's silent equations: a refining pattern name is one rule M resolves
to a slot introduced elsewhere, where lexical fresh would introduce it. -/
theorem mem_tMarks {cr : List X} {env : IEnv X} {fr pos : Owner} {p : Src S X} {y : X} :
    y ∈ tMarks cr env fr pos p ↔
      y ∈ Src.patNames p ∧ y ∉ cr ∧ env y ≠ ⟨y, fr, pos, .pat⟩ := by
  simp [tMarks, List.mem_filter]

/-! ## The rho reading -/

/-- **Per call is `!(ν z)P`.**  Two activations of one closure, at different
paths, copy each slot it owns to different names, as two replicas each
restricting their own name; a name it does not own, a crossing name included,
is left unchanged by both: every replica communicates on that existing name. -/
theorem per_call_replicas {Y : Type v} [DecidableEq Y] (own : List Y) {k k' : Y} (hk : k ∈ own)
    (hk' : k' ∉ own) {ρ ρ' : Path} (h : ρ ≠ ρ') :
    (renameOwn ρ own (.src k) : Option (Tm S Y)) ≠ renameOwn ρ' own (.src k) ∧
      (renameOwn ρ own (.src k') : Option (Tm S Y)) = none ∧
      (renameOwn ρ' own (.src k') : Option (Tm S Y)) = none := by
  refine ⟨(fresh_per_call own hk h).2, ?_, ?_⟩ <;> simp [renameOwn, ownKey, hk']

/-- **Per closure is `(ν z)!P`.**  A lambda whose own slots are hoisted to the
scope that creates it owns nothing, so its activations rename nothing: every
call shares the one restricted name. -/
theorem per_closure_shared {Y : Type v} [DecidableEq Y] (ρ : Path) (n : Nm Y) :
    (renameOwn ρ ([] : List Y) n : Option (Tm S Y)) = none := by
  rw [renameOwn_nil]
  rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope

/-! ## The connections on the corpus -/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge

/-- No equations. -/
def noClauses : Sy → Option A := fun _ => none

/-- **Matching, positive**: `(unify (d $t) (d 7) $t)` matches the pattern
against a ground value and answers `7`. -/
theorem unify_ground_matches :
    ansLFI noClauses (.unify (ap (k .d) (sv .t)) (ap (k .d) (k .n7)) (sv .t)) = some [kI .n7] ∧
      ansMI noClauses (.unify (ap (k .d) (sv .t)) (ap (k .d) (k .n7)) (sv .t)) = some [kI .n7] := by
  constructor <;> decide +kernel

/-- **Matching, negative: the model does not unify.**  Matching
`(d $t)` against `(d $u)` with `$u` unbound finds no ground value, so the
model gives no answer, under both options; a unification procedure would
answer `ok` under the residual constraint `$t = $u`.  The general problem is
left out of the model, not solved by it. -/
theorem unify_nonground_no_answer :
    ansLFI noClauses (.unify (ap (k .d) (sv .t)) (ap (k .d) (sv .u)) (k .ok)) = some [] ∧
      ansMI noClauses (.unify (ap (k .d) (sv .t)) (ap (k .d) (sv .u)) (k .ok)) = some [] := by
  constructor <;> decide +kernel

/-- **Quotation forgets `new`** (lossy, negative): the code of the translated
lambda of row H1 is the code of the source lambda, although the two
elaborate differently. -/
theorem quotation_forgets_new :
    (codeI holeT : TI) = codeI (lm .z (sv .hole)) ∧
      elabLFFormAt ([] : Owner) holeT ≠ elabLFFormAt [] (lm .z (sv .hole)) := by
  constructor <;> decide +kernel

/-- **The text round trip, on row H1**: the translated program, printed with its
`new` block, reads back to the term whose lexical-fresh elaboration is rule
M's. -/
theorem rowH1_text_roundtrip :
    printSrc (toLexical rowH1) =
        SExp.list [.atom (.kw .let_), .atom (.var .f),
          .list [.atom (.kw .lam), .atom (.par .z),
            .list [.atom (.kw .new_), .list [.atom (.var .hole)], .atom (.var .hole)]],
          .list [.atom (.sym .Pair), .list [.atom (.var .f), .atom (.sym .n1)],
            .list [.atom (.var .f), .atom (.sym .n2)]]] ∧
      (readSrc (printSrc (toLexical rowH1))).map (elabLFFormAt []) = some (elabMFormAt [] rowH1) :=
  ⟨by decide +kernel, translation_text_roundtrip [] rowH1 (by decide)⟩

end Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus

/-! ## No capture across forms -/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.HygieneCorpus

open Mettapedia.GSLT.LanguageDef.TemplateScope

/-- The program of `cross_form_capture`, `(= (mk) (lam x (lam z (let $q z (Pair $q x)))))`,
with the library's private name spelled `q`. -/
def progQ (q : HSp) : HSy → Option (Src HSy HSp) := fun F => if F = .mk then some (mkWsrc q) else none

/-- **Binder identities do not capture across forms**: the query
`(let $w 5 (((mk) $w) 1))` answers `(Pair 1 5)` whichever spelling the library
gives its private name, under lexical fresh and under rule M.  The core
evaluator with spellings answers `(Pair 1 1)` for one of them
(`cross_form_capture`). -/
theorem cross_form_identity :
    answers .static (progLF .u .unit (progQ .w)) 60 (elabLFFormAt [] queryWsrc) =
        some [.app (.app (.sym .Pair) (.sym .n1)) (.sym .n5)] ∧
      answers .static (progLF .u .unit (progQ .y)) 60 (elabLFFormAt [] queryWsrc) =
        some [.app (.app (.sym .Pair) (.sym .n1)) (.sym .n5)] ∧
      answers .static (progM .u .unit (progQ .w)) 60 (elabMFormAt [] queryWsrc) =
        some [.app (.app (.sym .Pair) (.sym .n1)) (.sym .n5)] ∧
      answers .static (progM .u .unit (progQ .y)) 60 (elabMFormAt [] queryWsrc) =
        some [.app (.app (.sym .Pair) (.sym .n1)) (.sym .n5)] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.HygieneCorpus
