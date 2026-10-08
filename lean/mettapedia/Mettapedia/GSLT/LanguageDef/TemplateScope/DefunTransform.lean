import Mettapedia.GSLT.LanguageDef.TemplateScope.Defunctionalization

/-!
# Template scope, naming part 2b: the defunctionalization transformation

`TemplateScope.Defunctionalization` proves that the target machine simulates
the model's evaluator on every pair of terms related by the closure relation.
Here is the transformation itself:

* `defun name t` replaces every lambda `L` of `t` by the closure
  `(name L  c₁ … cₖ  p₁ … pₘ)` carrying `L`'s captured store names and captured
  parameters (`refs`);
* `defunRule name L` is `L`'s apply rule: `L`'s lifted equation over those
  references, its body defunctionalized.

## Main results

* `rel_defun` — under the table hypotheses `Defunctionalizes` (every lambda's
  constructor carries `defunRule`, arguments within ranks, no captured store
  name used as a parameter of the body, no closure symbol and no pattern
  quotation in the source), `t` and `defun name t` are related.
* `defunRule_wf` — every rule `defunRule` produces is first-order and closed
  except for its own names, parameters and lambda parameter: of the table's
  well-formedness only the rank conditions are left to check.
* `answerBag_defunctionalized` — **the transformed program has the same answer
  bags**: with the equations defunctionalized as well, every lambda-free answer
  bag of the source query is the machine's answer bag of the transformed query,
  and every answer bag of the transformed query comes from a related answer bag
  of the source.  At the level of runs the stores are identical (`run_defun`).
* `defun_corpus` — the targets of rows B4, B1 and of the curried function in
  `Defunctionalization`'s examples are exactly `defun` of their sources, their
  rules are `defunRule`, and the hypotheses hold.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v}

/-- A symbol-headed call `(κ v₁ … vₖ)`. -/
def symCall (κ : S) (vs : List (Tm S X)) : Tm S X := vs.foldl .app (.sym κ)

theorem symSpine_foldl (h : Tm S X) : ∀ (vs : List (Tm S X)),
    symSpine (vs.foldl .app h) = (symSpine h).map fun p => (p.1, p.2 ++ vs)
  | [] => by simp
  | a :: as => by
      rw [List.foldl_cons, symSpine_foldl (.app h a) as]
      cases hh : symSpine h <;> simp [symSpine, hh]

theorem symSpine_symCall (κ : S) (vs : List (Tm S X)) :
    symSpine (symCall κ vs) = some (κ, vs) := by
  simp [symCall, symSpine_foldl, symSpine]

theorem foldl_app_lamFree : ∀ (h : Tm S X) (vs : List (Tm S X)), h.lamFree = true →
    (∀ v ∈ vs, v.lamFree = true) → (vs.foldl .app h).lamFree = true
  | _, [], hh, _ => hh
  | h, a :: as, hh, hv =>
      foldl_app_lamFree (.app h a) as (by simp [Tm.lamFree, hh, hv a List.mem_cons_self])
        (fun v hv' => hv v (List.mem_cons_of_mem _ hv'))

variable [DecidableEq X]

theorem mem_freeNames_foldl : ∀ (h : Tm S X) (vs : List (Tm S X)) (n : Nm X),
    n ∈ freeNames (vs.foldl .app h) → n ∈ freeNames h ∨ ∃ v ∈ vs, n ∈ freeNames v
  | _, [], _, hn => Or.inl hn
  | h, a :: as, n, hn => by
      rcases mem_freeNames_foldl (.app h a) as n hn with hn | ⟨v, hv, hn⟩
      · simp only [freeNames, List.mem_append] at hn
        rcases hn with hn | hn
        · exact Or.inl hn
        · exact Or.inr ⟨a, List.mem_cons_self, hn⟩
      · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, hn⟩

theorem mem_freeParams_foldl : ∀ (h : Tm S X) (vs : List (Tm S X)) (p : Nm X),
    p ∈ freeParams (vs.foldl .app h) → p ∈ freeParams h ∨ ∃ v ∈ vs, p ∈ freeParams v
  | _, [], _, hp => Or.inl hp
  | h, a :: as, p, hp => by
      rcases mem_freeParams_foldl (.app h a) as p hp with hp | ⟨v, hv, hp⟩
      · simp only [freeParams, List.mem_append] at hp
        rcases hp with hp | hp
        · exact Or.inl hp
        · exact Or.inr ⟨a, List.mem_cons_self, hp⟩
      · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, hp⟩

/-- The store names a lambda captures. -/
def capNames (L : Tm S X) : List (Nm X) := (freeNames L).dedup

/-- The parameters a lambda captures. -/
def capParams (L : Tm S X) : List (Nm X) := (freeParams L).dedup

/-- The references a closure carries: the captured store names, then the
captured parameters. -/
def refs (L : Tm S X) : List (Tm S X) := (capNames L).map .var ++ (capParams L).map .pvar

/-- **Defunctionalization.**  Every lambda becomes the closure of its name,
carrying its captured references.  Sealed quotations are code and stay as
they are. -/
def defun (name : Tm S X → S) : Tm S X → Tm S X
  | .lam x own b => symCall (name (.lam x own b)) (refs (.lam x own b))
  | .app f a => .app (defun name f) (defun name a)
  | .letP p w b => .letP (defun name p) (defun name w) (defun name b)
  | .alt t₁ t₂ => .alt (defun name t₁) (defun name t₂)
  | .pquote c => .pquote (defun name c)
  | .ctx ks c => .ctx ks c
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var n
  | .pvar x => .pvar x
  | .quote c => .quote c

/-- **The apply rule of a lambda**: its lifted equation over its captured
references (as `lifted` does, the parameters are named by the captured names),
with its body defunctionalized. -/
def defunRule (name : Tm S X → S) : Tm S X → Option (ApplyRule S X)
  | .lam x own b =>
      some ⟨capNames (.lam x own b) ++ capParams (.lam x own b), x, own,
        subst (absP fun n => decide (n ∈ capNames (.lam x own b))) Sub.none (defun name b)⟩
  | _ => none

/-- Every lambda of a term, at any depth, outside sealed quotations. -/
def lams : Tm S X → List (Tm S X)
  | .lam x own b => .lam x own b :: lams b
  | .app f a => lams f ++ lams a
  | .letP p w b => lams p ++ lams w ++ lams b
  | .alt t₁ t₂ => lams t₁ ++ lams t₂
  | .pquote c => lams c
  | _ => []

/-- The symbols of a term, outside sealed quotations. -/
def syms : Tm S X → List S
  | .sym s => [s]
  | .lam _ _ b => syms b
  | .app f a => syms f ++ syms a
  | .letP p w b => syms p ++ syms w ++ syms b
  | .alt t₁ t₂ => syms t₁ ++ syms t₂
  | .pquote c => syms c
  | _ => []

/-- Whether a pattern quotation occurs, outside sealed quotations. -/
def hasPQuote : Tm S X → Bool
  | .pquote _ => true
  | .lam _ _ b => hasPQuote b
  | .app f a => hasPQuote f || hasPQuote a
  | .letP p w b => hasPQuote p || hasPQuote w || hasPQuote b
  | .alt t₁ t₂ => hasPQuote t₁ || hasPQuote t₂
  | _ => false

/-- A lambda whose captured store names are not parameters of its body. -/
def apartB : Tm S X → Bool
  | .lam x own b => (capNames (.lam x own b)).all fun c => decide (c ∉ freeParams b)
  | _ => true

/-! ## Basic facts -/

omit [DecidableEq X] in
theorem refs_lamFree [DecidableEq X] (L : Tm S X) : ∀ v ∈ refs L, v.lamFree = true := by
  intro v hv
  simp only [refs, List.mem_append, List.mem_map] at hv
  rcases hv with ⟨n, -, rfl⟩ | ⟨p, -, rfl⟩ <;> rfl

theorem defun_lamFree (name : Tm S X → S) : ∀ t : Tm S X, (defun name t).lamFree = true
  | .lam _ _ _ => foldl_app_lamFree _ _ rfl (refs_lamFree _)
  | .app f a => by simp [defun, Tm.lamFree, defun_lamFree name f, defun_lamFree name a]
  | .letP p w b => by
      simp [defun, Tm.lamFree, defun_lamFree name p, defun_lamFree name w, defun_lamFree name b]
  | .alt t₁ t₂ => by simp [defun, Tm.lamFree, defun_lamFree name t₁, defun_lamFree name t₂]
  | .pquote c => by simp [defun, Tm.lamFree, defun_lamFree name c]
  | .sym _ | .fn _ | .var _ | .pvar _ | .quote _ | .ctx _ _ => rfl

/-- Defunctionalization introduces no free store name. -/
theorem freeNames_defun (name : Tm S X → S) : ∀ (t : Tm S X) (n : Nm X),
    n ∈ freeNames (defun name t) → n ∈ freeNames t
  | .lam x own b, n, hn => by
      rcases mem_freeNames_foldl _ _ n hn with hn | ⟨v, hv, hn⟩
      · simp [freeNames] at hn
      · simp only [refs, List.mem_append, List.mem_map] at hv
        rcases hv with ⟨c, hc, rfl⟩ | ⟨p, -, rfl⟩
        · simp only [freeNames, List.mem_singleton] at hn
          subst hn
          exact List.mem_dedup.1 hc
        · simp [freeNames] at hn
  | .app f a, n, hn => by
      simp only [defun, freeNames, List.mem_append] at hn ⊢
      exact hn.imp (freeNames_defun name f n) (freeNames_defun name a n)
  | .letP p w b, n, hn => by
      simp only [defun, freeNames, List.mem_append] at hn ⊢
      exact hn.imp (fun h => h.imp (freeNames_defun name p n) (freeNames_defun name w n))
        (freeNames_defun name b n)
  | .alt t₁ t₂, n, hn => by
      simp only [defun, freeNames, List.mem_append] at hn ⊢
      exact hn.imp (freeNames_defun name t₁ n) (freeNames_defun name t₂ n)
  | .pquote c, n, hn => by
      simp only [defun, freeNames] at hn ⊢
      exact freeNames_defun name c n hn
  | .sym _, _, hn | .fn _, _, hn | .var _, _, hn | .pvar _, _, hn | .quote _, _, hn
  | .ctx _ _, _, hn => hn

/-- Defunctionalization introduces no free parameter. -/
theorem freeParams_defun (name : Tm S X → S) : ∀ (t : Tm S X) (p : Nm X),
    p ∈ freeParams (defun name t) → p ∈ freeParams t
  | .lam x own b, p, hp => by
      rcases mem_freeParams_foldl _ _ p hp with hp | ⟨v, hv, hp⟩
      · simp [freeParams] at hp
      · simp only [refs, List.mem_append, List.mem_map] at hv
        rcases hv with ⟨c, -, rfl⟩ | ⟨q, hq, rfl⟩
        · simp [freeParams] at hp
        · simp only [freeParams, List.mem_singleton] at hp
          subst hp
          exact List.mem_dedup.1 hq
  | .app f a, p, hp => by
      simp only [defun, freeParams, List.mem_append] at hp ⊢
      exact hp.imp (freeParams_defun name f p) (freeParams_defun name a p)
  | .letP q w b, p, hp => by
      simp only [defun, freeParams, List.mem_append] at hp ⊢
      exact hp.imp (fun h => h.imp (freeParams_defun name q p) (freeParams_defun name w p))
        (freeParams_defun name b p)
  | .alt t₁ t₂, p, hp => by
      simp only [defun, freeParams, List.mem_append] at hp ⊢
      exact hp.imp (freeParams_defun name t₁ p) (freeParams_defun name t₂ p)
  | .pquote c, p, hp => by
      simp only [defun, freeParams] at hp ⊢
      exact freeParams_defun name c p hp
  | .sym _, _, hp | .fn _, _, hp | .var _, _, hp | .pvar _, _, hp | .quote _, _, hp
  | .ctx _ _, _, hp => hp

/-- The instantiation of the references' parameters. -/
theorem paramSub_refs (cs ps : List (Nm X)) (n : Nm X) :
    paramSub (cs ++ ps) (cs.map Tm.var ++ ps.map Tm.pvar : List (Tm S X)) n =
      if n ∈ cs then some (.var n) else if n ∈ ps then some (.pvar n) else none := by
  induction cs with
  | nil =>
      simp only [List.nil_append, List.map_nil, List.not_mem_nil, if_false]
      induction ps with
      | nil => simp [paramSub, Sub.none]
      | cons p ps ih =>
          simp only [List.map_cons, paramSub, List.mem_cons]
          by_cases hn : n = p
          · subst hn
            simp
          · simp [hn, ih]
  | cons c cs ih =>
      simp only [List.cons_append, List.map_cons, paramSub, List.mem_cons]
      by_cases hn : n = c
      · subst hn
        simp
      · simp [hn, ih]

/-- **The round trip of a rule instance.**  Abstracting the captured store
names into parameters and instantiating all parameters by the references gives
the body back, on first-order bodies with no parameter named like a captured
store name. -/
theorem inst_absP_refs (cs ps : List (Nm X)) : ∀ (B : Tm S X), B.lamFree = true →
    (∀ c ∈ cs, c ∉ freeParams B) →
    subst Sub.none (paramSub (cs ++ ps) (cs.map Tm.var ++ ps.map Tm.pvar))
      (subst (absP fun n => decide (n ∈ cs)) Sub.none B) = B
  | .sym _, _, _ | .fn _, _, _ | .quote _, _, _ | .ctx _ _, _, _ => rfl
  | .var n, _, _ => by
      by_cases hn : n ∈ cs
      · simp [subst, absP, hn, paramSub_refs]
      · simp [subst, absP, hn, Sub.none]
  | .pvar p, _, hcs => by
      have hp : p ∉ cs := fun h => hcs p h (by simp [freeParams])
      by_cases hq : p ∈ ps
      · simp [subst, Sub.none, paramSub_refs, hp, hq]
      · simp [subst, Sub.none, paramSub_refs, hp, hq]
  | .lam _ _ _, hl, _ => by simp [Tm.lamFree] at hl
  | .app f a, hl, hcs => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp only [freeParams, List.mem_append, not_or] at hcs
      simp only [subst]
      rw [inst_absP_refs cs ps f hl.1 (fun c hc => (hcs c hc).1),
        inst_absP_refs cs ps a hl.2 (fun c hc => (hcs c hc).2)]
  | .pquote c, hl, hcs => by
      simp only [Tm.lamFree] at hl
      simp only [freeParams] at hcs
      simp only [subst]
      rw [inst_absP_refs cs ps c hl hcs]
  | .letP p w b, hl, hcs => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp only [freeParams, List.mem_append, not_or] at hcs
      simp only [subst]
      rw [inst_absP_refs cs ps p hl.1.1 (fun c hc => (hcs c hc).1.1),
        inst_absP_refs cs ps w hl.1.2 (fun c hc => (hcs c hc).1.2),
        inst_absP_refs cs ps b hl.2 (fun c hc => (hcs c hc).2)]
  | .alt t₁ t₂, hl, hcs => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp only [freeParams, List.mem_append, not_or] at hcs
      simp only [subst]
      rw [inst_absP_refs cs ps t₁ hl.1 (fun c hc => (hcs c hc).1),
        inst_absP_refs cs ps t₂ hl.2 (fun c hc => (hcs c hc).2)]

/-- **The rules are well formed.**  Every rule `defunRule` produces is
first-order, its free store names are its own names, and its free parameters
are its parameters and its lambda parameter. -/
theorem defunRule_wf (name : Tm S X → S) (x : Nm X) (own : List X) (b : Tm S X)
    {r : ApplyRule S X} (h : defunRule name (.lam x own b) = some r) :
    r.body.lamFree = true ∧ (∀ n ∈ freeNames r.body, ownKey r.own n = true) ∧
      ∀ p ∈ freeParams r.body, p ∈ r.params ∨ p = r.x := by
  simp only [defunRule, Option.some.injEq] at h
  subst h
  refine ⟨?_, ?_, ?_⟩
  · refine lamFree_subst ?_ (by intro _ _ h; cases h) _ (defun_lamFree name b)
    intro n w hw
    simp only [absP] at hw
    split at hw
    · simp only [Option.some.injEq] at hw
      subst hw
      rfl
    · cases hw
  · intro n hn
    simp only at hn ⊢
    rw [freeNames_subst_absP, List.mem_filter] at hn
    obtain ⟨hn, hnc⟩ := hn
    have hb := freeNames_defun name b n hn
    by_contra hk
    simp only [Bool.not_eq_true] at hk
    apply (show ¬ n ∈ capNames (.lam x own b) by simpa using hnc)
    exact List.mem_dedup.2 (by simp [freeNames, hb, hk])
  · intro p hp
    simp only at hp ⊢
    rcases mem_freeParams_subst _ _ _ p hp with ⟨hp', -⟩ | ⟨n, w, hw, hpw⟩ | ⟨q, w, hw, -⟩
    · have hb := freeParams_defun name b p hp'
      by_cases hpx : p = x
      · exact Or.inr hpx
      · left
        apply List.mem_append_right
        exact List.mem_dedup.2 (by simp [freeParams, hb, hpx])
    · simp only [absP] at hw
      split at hw
      · rename_i hin
        simp only [Option.some.injEq] at hw
        subst hw
        simp only [freeParams, List.mem_singleton] at hpw
        subst hpw
        left
        exact List.mem_append_left _ (by simpa using hin)
      · cases hw
    · simp [Sub.none] at hw

/-! ## The transformation produces related terms -/

variable [DecidableEq S]

/-- The hypotheses under which `defun` is a closure conversion for the table. -/
structure CloTable.Defunctionalizes (T : CloTable S X) (name : Tm S X → S) (t : Tm S X) : Prop where
  rule : ∀ L ∈ lams t, T.rule (name L) = defunRule name L
  args : ∀ L ∈ lams t, T.argsOK (name L) (refs L) = true
  apart : ∀ L ∈ lams t, apartB L = true
  symsFree : ∀ s ∈ syms t, T.rule s = none
  noPQuote : hasPQuote t = false

omit [DecidableEq S] in
theorem CloTable.Defunctionalizes.mono {T : CloTable S X} {name : Tm S X → S} {t t' : Tm S X}
    (h : T.Defunctionalizes name t) (hl : ∀ L ∈ lams t', L ∈ lams t)
    (hs : ∀ s ∈ syms t', s ∈ syms t) (hp : hasPQuote t' = true → hasPQuote t = true) :
    T.Defunctionalizes name t' :=
  ⟨fun L hL => h.rule L (hl L hL), fun L hL => h.args L (hl L hL),
    fun L hL => h.apart L (hl L hL), fun s hs' => h.symsFree s (hs s hs'),
    by
      cases e : hasPQuote t'
      · rfl
      · have h0 := h.noPQuote
        rw [hp e] at h0
        cases h0⟩

/-- **The transformation is a closure conversion**: a term and its
defunctionalization are related. -/
theorem rel_defun (T : CloTable S X) (name : Tm S X → S) :
    ∀ t : Tm S X, T.Defunctionalizes name t → T.rel t (defun name t) = true
  | .sym s, h => by simp [CloTable.rel, defun, h.symsFree s (by simp [syms])]
  | .fn F, _ => by simp [CloTable.rel, defun]
  | .var n, _ => by simp [CloTable.rel, defun]
  | .pvar x, _ => by simp [CloTable.rel, defun]
  | .quote c, _ => by simp [CloTable.rel, defun]
  | .ctx _ _, _ => by simp [CloTable.rel, defun]
  | .pquote c, h => by have := h.noPQuote; simp [hasPQuote] at this
  | .app f a, h => by
      simp only [defun, CloTable.rel, Bool.and_eq_true]
      refine ⟨rel_defun T name f (h.mono ?_ ?_ ?_), rel_defun T name a (h.mono ?_ ?_ ?_)⟩ <;>
        first
        | (intro L hL; simp [lams, hL])
        | (intro s hs; simp [syms, hs])
        | (intro hp; simp [hasPQuote, hp])
  | .letP p w b, h => by
      simp only [defun, CloTable.rel, Bool.and_eq_true]
      refine ⟨⟨rel_defun T name p (h.mono ?_ ?_ ?_), rel_defun T name w (h.mono ?_ ?_ ?_)⟩,
        rel_defun T name b (h.mono ?_ ?_ ?_)⟩ <;>
        first
        | (intro L hL; simp [lams, hL])
        | (intro s hs; simp [syms, hs])
        | (intro hp; simp [hasPQuote, hp])
  | .alt t₁ t₂, h => by
      simp only [defun, CloTable.rel, Bool.and_eq_true]
      refine ⟨rel_defun T name t₁ (h.mono ?_ ?_ ?_), rel_defun T name t₂ (h.mono ?_ ?_ ?_)⟩ <;>
        first
        | (intro L hL; simp [lams, hL])
        | (intro s hs; simp [syms, hs])
        | (intro hp; simp [hasPQuote, hp])
  | .lam x own b, h => by
      have hL : Tm.lam x own b ∈ lams (Tm.lam x own b) := List.mem_cons_self
      have hr := h.rule _ hL
      simp only [defunRule] at hr
      have hb : T.Defunctionalizes name b :=
        h.mono (fun L hL' => List.mem_cons_of_mem _ hL') (fun s hs => hs)
          (fun hp => by simpa [hasPQuote] using hp)
      have hc : T.clo? (defun name (.lam x own b)) =
          some (name (.lam x own b), refs (.lam x own b),
            ⟨capNames (.lam x own b) ++ capParams (.lam x own b), x, own,
              subst (absP fun n => decide (n ∈ capNames (.lam x own b))) Sub.none (defun name b)⟩) :=
        (T.clo?_eq_some).2 ⟨symSpine_symCall _ _, hr, by simp [refs]⟩
      refine (T.rel_lam).2 ⟨_, _, _, hc, h.args _ hL, rfl, rfl, ?_⟩
      have hap := h.apart _ hL
      simp only [apartB, List.all_eq_true, decide_eq_true_eq] at hap
      unfold ApplyRule.inst
      simp only [refs]
      rw [inst_absP_refs _ _ (defun name b) (defun_lamFree name b)
        (fun c hc hcb => hap c hc (freeParams_defun name b c hcb))]
      exact rel_defun T name b hb

omit [DecidableEq S] in
/-- A term with no ranked free name or parameter defunctionalizes to a good term. -/
theorem good_defun (T : CloTable S X) (name : Tm S X → S) (t : Tm S X)
    (hn : ∀ n ∈ freeNames t, T.nameRank n = none) (hp : ∀ p ∈ freeParams t, T.paramRank p = none) :
    T.good (defun name t) = true :=
  (T.good_iff).2 ⟨fun n h => hn n (freeNames_defun name t n h),
    fun p h => hp p (freeParams_defun name t p h)⟩

/-- The defunctionalized program: every equation defunctionalized. -/
def defunProg (name : Tm S X → S) (prog : S → Option (Tm S X)) : S → Option (Tm S X) :=
  fun F => (prog F).map (defun name)

open CloTable in
/-- **The transformed program has the same answer bags.**  For a well-formed
table under which the query and every equation defunctionalize, every
lambda-free answer bag of the query is the machine's answer bag of the
transformed query with the transformed equations; every answer bag of the
transformed query comes from a related answer bag of the query.  (At the level
of runs the final stores are identical: `run_defun`.) -/
theorem answerBag_defunctionalized (T : CloTable S X) (hT : T.WF) (name : Tm S X → S)
    (prog : S → Option (Tm S X)) (t : Tm S X) (ht : T.Defunctionalizes name t)
    (hgt : T.good (defun name t) = true)
    (hprog : ∀ F e, prog F = some e → T.Defunctionalizes name e ∧ T.good (defun name e) = true) :
    (∀ bag, AnswerBag .static prog t bag → (∀ a ∈ bag, a.lamFree = true) →
      ∃ n, answersD T (defunProg name prog) n (defun name t) = some bag) ∧
    (∀ n bag', answersD T (defunProg name prog) n (defun name t) = some bag' →
      ∃ bag, AnswerBag .static prog t bag ∧
        List.Forall₂ (fun a a' => T.rel a a' = true) bag bag') := by
  have hp : ∀ F, OptRel (fun e e' => T.rel e e' = true ∧ T.good e' = true) (prog F)
      (defunProg name prog F) := by
    intro F
    unfold defunProg
    cases he : prog F with
    | none => trivial
    | some e =>
        obtain ⟨hd, hg⟩ := hprog F e he
        exact ⟨rel_defun T name e hd, hg⟩
  exact answerBag_defun T hT prog (defunProg name prog) hp t (defun name t)
    (rel_defun T name t ht) hgt

end Mettapedia.GSLT.LanguageDef.TemplateScope

/-! ## The corpus targets are `defun` of their sources -/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.DefunCorpus

open Mettapedia.GSLT.LanguageDef.TemplateScope

deriving instance DecidableEq for ApplyRule

/-- B4 and B1 name their only lambda `CloL`. -/
def nameL : DT → DSy := fun _ => .CloL

/-- The curried function: the outer lambda is `CloOut`, the inner `CloIn`. -/
def nameCur : DT → DSy := fun L => if L = Lout then .CloOut else .CloIn

/-- **The corpus targets are the transformation's output**, their rules are
`defunRule`, and the hypotheses of `answerBag_defunctionalized` hold. -/
theorem defun_corpus :
    defun nameL srcB4 = tgtB4 ∧ defunRule nameL L = some ruleL ∧
    defun nameL srcB1 = tgtB1 ∧ defunRule nameL L1 = some ruleL1 ∧
    defun nameCur srcCur = tgtCur ∧ defunRule nameCur Lout = some ruleOut ∧
    defunRule nameCur (lm .w (pair (pv .z) (pv .w))) = some ruleIn := by
  decide

theorem defunctionalizes_B4 : tabB4.Defunctionalizes nameL srcB4 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem defunctionalizes_B1 : tabB1.Defunctionalizes nameL srcB1 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem defunctionalizes_curried : tabCur.Defunctionalizes nameCur srcCur :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Row B4 through the general theorem about the transformation. -/
theorem defunctionalized_B4_bags (bag : List DT) (h : AnswerBag .static noProg srcB4 bag)
    (hlf : ∀ a ∈ bag, a.lamFree = true) :
    ∃ n, answersD tabB4 (defunProg nameL noProg) n (defun nameL srcB4) = some bag :=
  (answerBag_defunctionalized tabB4 tabB4_wf nameL noProg srcB4 defunctionalizes_B4
    (by decide) (fun _ _ h => by simp [noProg] at h)).1 bag h hlf

end Mettapedia.GSLT.LanguageDef.TemplateScope.DefunCorpus
