import Mettapedia.GSLT.LanguageDef.TemplateScope.DefunTransform
import Mettapedia.GSLT.LanguageDef.TemplateScope.Spectrum

/-!
# Template scope: hygiene of rule-M elaboration

The core model names store names by spelling, and its substitution is not
capture-avoiding.  Two results carry a hygiene side condition because of
this: `answerBag_defunctionalized` (the query's free names must carry no rank,
that is, must not be spellings a rule owns) and the evaluator's inlining step
`run_letP_lam` (the substituted lambda must not be captured).

## What rule M guarantees: hygiene of one form

* `elabTopM_hygienic` — **in every rule-M elaborated form, no free name is a
  spelling some lambda of the form owns.**  Rule M never lets a lambda own a
  spelling that an enclosing scope (the form's top level included) writes,
  and every free name of the form is written at its top level.
* `freeNames_subst_captureFree` — a substitution whose inserted values have
  no free name that a lambda of the term owns captures nothing: every free name
  of an inserted value stays free.
* `elabTopM_let_captureFree` — hence the evaluator's `let` of a lambda at the
  query (`run_letP_lam`, which performs `C[f := L]` on the elaborated term) is
  capture-free for every rule-M elaborated query.  `captureFree_negative`: a
  hand-elaborated term where a lambda of `C` owns a free name of `L` captures.

## What rule M does not guarantee: the program-wide conditions

`answerBag_defunctionalized` needs more than the form-local condition: a
closure table whose ranks are per spelling and per parameter name.  For rule
M with spelling names, such a table need not exist:

* `library_not_good` — row 13b, `(let $f (mk) (Pair ($f 1) (let $y 5 $y)))`
  with `(= (mk) L)`: the equation's lambda owns `$y` and the query writes
  `$y`; no well-formed table makes the query good.  Equations are elaborated
  separately, so the form-local guarantee does not cover them.
* `owned_rank_cycle` — one rule-M form with no equation, whose lambdas own
  crossing spellings (`A` owns `$y` and holds `D`, which owns `$w`; `B` owns
  `$w` and holds `C`, which owns `$y`): no table is well formed and
  defunctionalizes it.
* `param_rank_cycle` — the same cycle through parameter names alone, in a
  program without store names, where ownership plays no part.
* `cross_form_capture` — the failure is not only in the proof device: the
  core evaluator captures across forms.  An equation's lambda that owns `$w`
  receives the caller's `$w` through a parameter, and the answer depends on
  how the library spells its private name (`(Pair 1 1)` against
  `(Pair 1 5)`).

## The elaboration change that makes it hold: binders carry identities

`elabMI` is rule M whose binders carry identities instead of spellings: the
names a lambda owns at nesting level `d` become `(own d, y)`, its parameter
`(par d, z)`, and a name no lambda binds `(top, y)`.  The own lists are rule
M's: forgetting the identities gives `elabM` back (`untag_elabMI`).

* `answerBag_defunctionalized_MI` — **for every program elaborated by
  `elabMI`, query and equations, `answerBag_defunctionalized` holds with no
  hygiene hypothesis**: the closure table `tableMI` is well formed, every form
  defunctionalizes, and every form is good.  What remains are the theorem's
  scope conditions, which are not about names: no pattern quotation, closure
  constructors distinct and fresh, and a bound on the nesting depth (finite
  programs have one).
* `cross_form_fixed`, `owned_cycle_defunctionalized`,
  `param_cycle_defunctionalized` — the three counterexamples above, elaborated
  by `elabMI`: the capture is gone and both cycles defunctionalize with the
  same answers.

The spectrum model (`TemplateScope.Spectrum`) already gives owned names slot
identities `(owner position, spelling)`, which is why it does not capture
across forms (`cross_form_slots`); its parameters are still named by spelling
(`parName`), the case `param_rank_cycle` is about.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v}

/-! ## Owned spellings and the form-local condition -/

/-- The spellings the lambdas of a term own, outside sealed quotations. -/
def ownedIn : Tm S X → List X
  | .lam _ own b => own ++ ownedIn b
  | .app f a => ownedIn f ++ ownedIn a
  | .pquote c => ownedIn c
  | .letP p w b => ownedIn p ++ ownedIn w ++ ownedIn b
  | .alt t₁ t₂ => ownedIn t₁ ++ ownedIn t₂
  | _ => []

variable [DecidableEq X]

/-- **Hygiene of a form**: no free store name is a spelling that a lambda of
the form owns. -/
def Hygienic (t : Tm S X) : Prop := ∀ y, Nm.src y ∈ freeNames t → y ∉ ownedIn t

/-- Rule M never lets a lambda own a spelling quantified at an enclosing
scope. -/
theorem not_mem_of_mem_ownedIn_elabM : ∀ (t : Tm S X) (E : List X) {y : X},
    y ∈ ownedIn (elabM E t) → y ∉ E
  | .sym _, _, _, h => by simp [elabM, ownedIn] at h
  | .fn _, _, _, h => by simp [elabM, ownedIn] at h
  | .var _, _, _, h => by simp [elabM, ownedIn] at h
  | .pvar _, _, _, h => by simp [elabM, ownedIn] at h
  | .lam x _ b, E, y, h => by
      simp only [elabM, ownedIn, List.mem_append] at h
      rcases h with h | h
      · simp only [ownM, List.mem_dedup, List.mem_filter, decide_eq_true_eq] at h
        exact h.2
      · intro hy
        exact not_mem_of_mem_ownedIn_elabM b _ h (List.mem_append_right _ hy)
  | .app f a, E, y, h => by
      simp only [elabM, ownedIn, List.mem_append] at h
      rcases h with h | h
      · exact not_mem_of_mem_ownedIn_elabM f E h
      · exact not_mem_of_mem_ownedIn_elabM a E h
  | .quote _, _, _, h => by simp [elabM, ownedIn] at h
  | .pquote c, E, y, h => by
      simp only [elabM, ownedIn] at h
      exact not_mem_of_mem_ownedIn_elabM c E h
  | .letP p w b, E, y, h => by
      simp only [elabM, ownedIn, List.mem_append] at h
      rcases h with (h | h) | h
      · exact not_mem_of_mem_ownedIn_elabM p E h
      · exact not_mem_of_mem_ownedIn_elabM w E h
      · exact not_mem_of_mem_ownedIn_elabM b E h
  | .alt t₁ t₂, E, y, h => by
      simp only [elabM, ownedIn, List.mem_append] at h
      rcases h with h | h
      · exact not_mem_of_mem_ownedIn_elabM t₁ E h
      · exact not_mem_of_mem_ownedIn_elabM t₂ E h

/-- Under rule M, a free spelling of an elaborated term is quantified at the
enclosing scopes, provided those quantify what the term writes directly. -/
theorem mem_of_src_mem_freeNames_elabM : ∀ (t : Tm S X) (E : List X),
    (∀ y ∈ direct t, y ∈ E) → ∀ {y : X}, Nm.src y ∈ freeNames (elabM E t) → y ∈ E
  | .sym _, _, _, _, h => by simp [elabM, freeNames] at h
  | .fn _, _, _, _, h => by simp [elabM, freeNames] at h
  | .var (.src z), _, hd, y, h => by
      simp only [elabM, freeNames, List.mem_singleton, Nm.src.injEq] at h
      subst h
      exact hd _ (by simp [direct])
  | .var (.inst _ _), _, _, _, h => by simp [elabM, freeNames] at h
  | .pvar _, _, _, _, h => by simp [elabM, freeNames] at h
  | .lam x _ b, E, _, y, h => by
      simp only [elabM, freeNames, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        ownKey_src, decide_eq_false_iff_not] at h
      obtain ⟨hy, hk⟩ := h
      have hb : ∀ z ∈ direct b, z ∈ ownM E b ++ E := by
        intro z hz
        by_cases hzE : z ∈ E
        · exact List.mem_append_right _ hzE
        · exact List.mem_append_left _ (by simp [ownM, List.mem_dedup, hz, hzE])
      rcases List.mem_append.1 (mem_of_src_mem_freeNames_elabM b _ hb hy) with h' | h'
      · exact absurd h' hk
      · exact h'
  | .app f a, E, hd, y, h => by
      simp only [direct, List.mem_append] at hd
      simp only [elabM, freeNames, List.mem_append] at h
      rcases h with h | h
      · exact mem_of_src_mem_freeNames_elabM f E (fun z hz => hd z (Or.inl hz)) h
      · exact mem_of_src_mem_freeNames_elabM a E (fun z hz => hd z (Or.inr hz)) h
  | .quote _, _, _, _, h => by simp [elabM, freeNames] at h
  | .pquote c, E, hd, y, h => by
      simp only [direct] at hd
      simp only [elabM, freeNames] at h
      exact mem_of_src_mem_freeNames_elabM c E hd h
  | .letP p w b, E, hd, y, h => by
      simp only [direct, List.mem_append] at hd
      simp only [elabM, freeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · exact mem_of_src_mem_freeNames_elabM p E (fun z hz => hd z (Or.inl (Or.inl hz))) h
      · exact mem_of_src_mem_freeNames_elabM w E (fun z hz => hd z (Or.inl (Or.inr hz))) h
      · exact mem_of_src_mem_freeNames_elabM b E (fun z hz => hd z (Or.inr hz)) h
  | .alt t₁ t₂, E, hd, y, h => by
      simp only [direct, List.mem_append] at hd
      simp only [elabM, freeNames, List.mem_append] at h
      rcases h with h | h
      · exact mem_of_src_mem_freeNames_elabM t₁ E (fun z hz => hd z (Or.inl hz)) h
      · exact mem_of_src_mem_freeNames_elabM t₂ E (fun z hz => hd z (Or.inr hz)) h

/-- Every subterm elaborated in the scope of the form keeps the condition:
its free spellings are quantified at the enclosing scopes, its lambdas own
none of them. -/
theorem elabM_hygienic (t : Tm S X) (E : List X) (hd : ∀ y ∈ direct t, y ∈ E) :
    Hygienic (elabM E t) := fun _ hy ho =>
  not_mem_of_mem_ownedIn_elabM t E ho (mem_of_src_mem_freeNames_elabM t E hd hy)

/-- **Rule M is hygienic, form by form**: no free name of a rule-M
elaborated form is a spelling that a lambda of the form owns. -/
theorem elabTopM_hygienic (t : Tm S X) : Hygienic (elabTopM t) :=
  elabM_hygienic t (direct t) fun _ h => h

/-! ## Capture-free substitution -/

/-- **A substitution that inserts no owned spelling captures nothing**: every
free name of an inserted value stays free. -/
theorem freeNames_subst_captureFree : ∀ (t : Tm S X) (θ : Sub S X),
    (∀ n v, θ n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn t) →
    ∀ n ∈ freeNames t, ∀ v, θ n = some v → ∀ m ∈ freeNames v, m ∈ freeNames (subst θ Sub.none t)
  | .sym _, _, _, n, hn, _, _, _, _ => by simp [freeNames] at hn
  | .fn _, _, _, n, hn, _, _, _, _ => by simp [freeNames] at hn
  | .var n', θ, _, n, hn, v, hv, m, hm => by
      simp only [freeNames, List.mem_singleton] at hn
      subst hn
      simp [subst, hv, hm]
  | .pvar _, _, _, n, hn, _, _, _, _ => by simp [freeNames] at hn
  | .lam x own b, θ, hθ, n, hn, v, hv, m, hm => by
      simp only [freeNames, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hn
      obtain ⟨hn, hk⟩ := hn
      have hv' : θ.hideOwn own n = some v := by simp [Sub.hideOwn, hk, hv]
      have hθ' : ∀ n v, θ.hideOwn own n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn b := by
        intro n' v' h' y hy hyo
        unfold Sub.hideOwn at h'
        split at h'
        · cases h'
        · exact hθ n' v' h' y hy (by simp [ownedIn, hyo])
      have := freeNames_subst_captureFree b (θ.hideOwn own) hθ' n hn v hv' m hm
      simp only [subst, none_hideParam, freeNames, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true]
      refine ⟨this, ?_⟩
      cases m with
      | src y =>
          have hy : y ∉ own := fun h => hθ n v hv y hm (by simp [ownedIn, h])
          simp [ownKey, hy]
      | inst _ _ => rfl
  | .app f a, θ, hθ, n, hn, v, hv, m, hm => by
      simp only [freeNames, List.mem_append] at hn
      simp only [subst, freeNames, List.mem_append]
      have hf : ∀ n v, θ n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn f :=
        fun n v h y hy ho => hθ n v h y hy (by simp [ownedIn, ho])
      have ha : ∀ n v, θ n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn a :=
        fun n v h y hy ho => hθ n v h y hy (by simp [ownedIn, ho])
      rcases hn with hn | hn
      · exact Or.inl (freeNames_subst_captureFree f θ hf n hn v hv m hm)
      · exact Or.inr (freeNames_subst_captureFree a θ ha n hn v hv m hm)
  | .quote _, _, _, n, hn, _, _, _, _ => by simp [freeNames] at hn
  | .pquote c, θ, hθ, n, hn, v, hv, m, hm => by
      simp only [freeNames] at hn
      simp only [subst, freeNames]
      exact freeNames_subst_captureFree c θ (fun n v h y hy ho => hθ n v h y hy (by
        simpa [ownedIn] using ho)) n hn v hv m hm
  | .letP p w b, θ, hθ, n, hn, v, hv, m, hm => by
      simp only [freeNames, List.mem_append] at hn
      simp only [subst, freeNames, List.mem_append]
      have hp : ∀ n v, θ n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn p :=
        fun n v h y hy ho => hθ n v h y hy (by simp [ownedIn, ho])
      have hw : ∀ n v, θ n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn w :=
        fun n v h y hy ho => hθ n v h y hy (by simp [ownedIn, ho])
      have hb : ∀ n v, θ n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn b :=
        fun n v h y hy ho => hθ n v h y hy (by simp [ownedIn, ho])
      rcases hn with (hn | hn) | hn
      · exact Or.inl (Or.inl (freeNames_subst_captureFree p θ hp n hn v hv m hm))
      · exact Or.inl (Or.inr (freeNames_subst_captureFree w θ hw n hn v hv m hm))
      · exact Or.inr (freeNames_subst_captureFree b θ hb n hn v hv m hm)
  | .alt t₁ t₂, θ, hθ, n, hn, v, hv, m, hm => by
      simp only [freeNames, List.mem_append] at hn
      simp only [subst, freeNames, List.mem_append]
      have h₁ : ∀ n v, θ n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn t₁ :=
        fun n v h y hy ho => hθ n v h y hy (by simp [ownedIn, ho])
      have h₂ : ∀ n v, θ n = some v → ∀ y, Nm.src y ∈ freeNames v → y ∉ ownedIn t₂ :=
        fun n v h y hy ho => hθ n v h y hy (by simp [ownedIn, ho])
      rcases hn with hn | hn
      · exact Or.inl (freeNames_subst_captureFree t₁ θ h₁ n hn v hv m hm)
      · exact Or.inr (freeNames_subst_captureFree t₂ θ h₂ n hn v hv m hm)

/-- **The evaluator's inlining at the query is capture-free under rule M.**
For the query `(let $f L C)`, the evaluator substitutes the elaborated lambda
into the elaborated body (`run_letP_lam`); no lambda of the body owns a free
name of the lambda, so wherever `$f` occurs free, every free name of the
lambda stays free. -/
theorem elabTopM_let_captureFree (fx : X) (x : Nm X) (body C : Tm S X) :
    let E := direct (.letP (.var (.src fx)) (.lam x [] body) C : Tm S X)
    (∀ y, Nm.src y ∈ freeNames (elabM E (.lam x [] body)) → y ∉ ownedIn (elabM E C)) ∧
    (Nm.src fx ∈ freeNames (elabM E C) → ∀ m ∈ freeNames (elabM E (.lam x [] body)),
      m ∈ freeNames (subst (Sub.single (.src fx) (elabM E (.lam x [] body))) Sub.none
        (elabM E C))) := by
  intro E
  have hE : ∀ y, Nm.src y ∈ freeNames (elabM E (.lam x [] body)) → y ∉ ownedIn (elabM E C) :=
    fun y hy ho => not_mem_of_mem_ownedIn_elabM C E ho
      (mem_of_src_mem_freeNames_elabM _ E (by simp [direct]) hy)
  refine ⟨hE, fun hf m hm => freeNames_subst_captureFree _ _ ?_ _ hf _ (by simp [Sub.single]) m hm⟩
  intro n v hv y hy
  simp only [Sub.single] at hv
  split at hv
  · cases hv
    exact hE y hy
  · cases hv

/-! ## Binders with identities -/

/-- Where a name is bound: at the form level by no lambda (`top`), as an own
name of the lambda at nesting level `d` (`own d`), or as the parameter of the
lambda at level `d` (`par d`; `par 0` is a parameter no lambda binds). -/
inductive Lv where
  | top
  | own (d : ℕ)
  | par (d : ℕ)
  deriving DecidableEq, Repr

/-- The spelling of a name. -/
def Nm.spell : Nm X → X
  | .src y => y
  | .inst _ n => Nm.spell n

/-- Point the spellings `ys` at the level `l`. -/
def lvUpdate (lv : X → Lv) (ys : List X) (l : Lv) : X → Lv :=
  fun y => if y ∈ ys then l else lv y

/-- Sealed code keeps its names, at the form level. -/
def tagCode : Tm S X → Tm S (Lv × X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var (.src (.top, n.spell))
  | .pvar n => .pvar (.src (.par 0, n.spell))
  | .lam x own b => .lam (.src (.par 0, x.spell)) (own.map fun y => (.top, y)) (tagCode b)
  | .app f a => .app (tagCode f) (tagCode a)
  | .quote c => .quote (tagCode c)
  | .ctx ks c => .ctx (ks.map fun k => .src (.par 0, k.spell)) (tagCode c)
  | .pquote c => .pquote (tagCode c)
  | .letP p w b => .letP (tagCode p) (tagCode w) (tagCode b)
  | .alt t₁ t₂ => .alt (tagCode t₁) (tagCode t₂)

/-- **Rule M with binder identities.**  The own lists are rule M's (`ownM`);
each name is resolved to its binder: `lv` gives the level of the innermost
enclosing lambda that owns a spelling (`top` if none), `pv` the level of the
innermost lambda whose parameter it is.  A lambda at level `d` binds
`(par d, z)` and owns `(own d, y)`. -/
def elabMI (E : List X) (lv pv : X → Lv) (d : ℕ) : Tm S X → Tm S (Lv × X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var (.src (lv n.spell, n.spell))
  | .pvar n => .pvar (.src (pv n.spell, n.spell))
  | .lam x _ b =>
      .lam (.src (.par (d + 1), x.spell)) ((ownM E b).map fun y => (.own (d + 1), y))
        (elabMI (ownM E b ++ E) (lvUpdate lv (ownM E b) (.own (d + 1)))
          (lvUpdate pv [x.spell] (.par (d + 1))) (d + 1) b)
  | .app f a => .app (elabMI E lv pv d f) (elabMI E lv pv d a)
  | .quote c => .quote (tagCode c)
  | .ctx ks c => .ctx (ks.map fun k => .src (.par 0, k.spell)) (tagCode c)
  | .pquote c => .pquote (elabMI E lv pv d c)
  | .letP p w b => .letP (elabMI E lv pv d p) (elabMI E lv pv d w) (elabMI E lv pv d b)
  | .alt t₁ t₂ => .alt (elabMI E lv pv d t₁) (elabMI E lv pv d t₂)

/-- Rule M with binder identities, at a form. -/
def elabTopMI (t : Tm S X) : Tm S (Lv × X) :=
  elabMI (direct t) (fun _ => .top) (fun _ => .par 0) 0 t

/-! ### The identities are all the change -/

/-- Forget a name's identity. -/
def untagNm : Nm (Lv × X) → Nm X
  | .src p => .src p.2
  | .inst ρ n => .inst ρ (untagNm n)

/-- Forget the identities. -/
def untag : Tm S (Lv × X) → Tm S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var (untagNm n)
  | .pvar n => .pvar (untagNm n)
  | .lam x own b => .lam (untagNm x) (own.map Prod.snd) (untag b)
  | .app f a => .app (untag f) (untag a)
  | .quote c => .quote (untag c)
  | .ctx ks c => .ctx (ks.map untagNm) (untag c)
  | .pquote c => .pquote (untag c)
  | .letP p w b => .letP (untag p) (untag w) (untag b)
  | .alt t₁ t₂ => .alt (untag t₁) (untag t₂)

/-- Authored text writes spellings: no name is an activation copy. -/
def Tm.Authored : Tm S X → Bool
  | .var (.src _) => true
  | .pvar (.src _) => true
  | .lam (.src _) _ b => Authored b
  | .var (.inst _ _) => false
  | .pvar (.inst _ _) => false
  | .lam (.inst _ _) _ _ => false
  | .app f a => Authored f && Authored a
  | .quote c => Authored c
  | .ctx _ _ => false
  | .pquote c => Authored c
  | .letP p w b => Authored p && Authored w && Authored b
  | .alt t₁ t₂ => Authored t₁ && Authored t₂
  | .sym _ => true
  | .fn _ => true

omit [DecidableEq X] in
theorem untag_tagCode : ∀ c : Tm S X, c.Authored = true → untag (tagCode c) = c
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .var (.src _), _ => rfl
  | .var (.inst _ _), h => by simp [Tm.Authored] at h
  | .pvar (.src _), _ => rfl
  | .pvar (.inst _ _), h => by simp [Tm.Authored] at h
  | .lam (.src _) own b, h => by
      simp only [Tm.Authored] at h
      simp [tagCode, untag, untagNm, Nm.spell, untag_tagCode b h]
  | .lam (.inst _ _) _ _, h => by simp [Tm.Authored] at h
  | .app f a, h => by
      simp only [Tm.Authored, Bool.and_eq_true] at h
      simp [tagCode, untag, untag_tagCode f h.1, untag_tagCode a h.2]
  | .quote c, h => by
      simp only [Tm.Authored] at h
      simp [tagCode, untag, untag_tagCode c h]
  | .ctx _ _, h => by simp [Tm.Authored] at h
  | .pquote c, h => by
      simp only [Tm.Authored] at h
      simp [tagCode, untag, untag_tagCode c h]
  | .letP p w b, h => by
      simp only [Tm.Authored, Bool.and_eq_true] at h
      simp [tagCode, untag, untag_tagCode p h.1.1, untag_tagCode w h.1.2, untag_tagCode b h.2]
  | .alt t₁ t₂, h => by
      simp only [Tm.Authored, Bool.and_eq_true] at h
      simp [tagCode, untag, untag_tagCode t₁ h.1, untag_tagCode t₂ h.2]

/-- **Forgetting the identities gives rule M back**: `elabMI` stores rule M's
own lists, and changes nothing but how binders are named. -/
theorem untag_elabMI : ∀ (t : Tm S X) (E : List X) (lv pv : X → Lv) (d : ℕ), t.Authored = true →
    untag (elabMI E lv pv d t) = elabM E t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .var (.src _), _, _, _, _, _ => rfl
  | .var (.inst _ _), _, _, _, _, h => by simp [Tm.Authored] at h
  | .pvar (.src _), _, _, _, _, _ => rfl
  | .pvar (.inst _ _), _, _, _, _, h => by simp [Tm.Authored] at h
  | .lam (.src _) _ b, E, lv, pv, d, h => by
      simp only [Tm.Authored] at h
      simp [elabMI, elabM, untag, untagNm, Nm.spell, untag_elabMI b _ _ _ _ h]
  | .lam (.inst _ _) _ _, _, _, _, _, h => by simp [Tm.Authored] at h
  | .app f a, E, lv, pv, d, h => by
      simp only [Tm.Authored, Bool.and_eq_true] at h
      simp [elabMI, elabM, untag, untag_elabMI f _ _ _ _ h.1, untag_elabMI a _ _ _ _ h.2]
  | .quote c, _, _, _, _, h => by
      simp only [Tm.Authored] at h
      simp [elabMI, elabM, untag, untag_tagCode c h]
  | .ctx _ _, _, _, _, _, h => by simp [Tm.Authored] at h
  | .pquote c, E, lv, pv, d, h => by
      simp only [Tm.Authored] at h
      simp [elabMI, elabM, untag, untag_elabMI c _ _ _ _ h]
  | .letP p w b, E, lv, pv, d, h => by
      simp only [Tm.Authored, Bool.and_eq_true] at h
      simp [elabMI, elabM, untag, untag_elabMI p _ _ _ _ h.1.1, untag_elabMI w _ _ _ _ h.1.2,
        untag_elabMI b _ _ _ _ h.2]
  | .alt t₁ t₂, E, lv, pv, d, h => by
      simp only [Tm.Authored, Bool.and_eq_true] at h
      simp [elabMI, elabM, untag, untag_elabMI t₁ _ _ _ _ h.1, untag_elabMI t₂ _ _ _ _ h.2]

theorem untag_elabTopMI (t : Tm S X) (h : t.Authored = true) : untag (elabTopMI t) = elabTopM t :=
  untag_elabMI t _ _ _ _ h

/-! ### Scoping of the identities -/

/-- Every free name of an identity-tagged term is a spelling at the level
the environment gives it. -/
theorem freeNames_elabMI : ∀ (t : Tm S X) (E : List X) (lv pv : X → Lv) (d : ℕ),
    ∀ n ∈ freeNames (elabMI E lv pv d t), ∃ y, n = .src (lv y, y)
  | .sym _, _, _, _, _, n, h => by simp [elabMI, freeNames] at h
  | .fn _, _, _, _, _, n, h => by simp [elabMI, freeNames] at h
  | .var m, _, lv, _, _, n, h => by
      simp only [elabMI, freeNames, List.mem_singleton] at h
      exact ⟨_, h⟩
  | .pvar _, _, _, _, _, n, h => by simp [elabMI, freeNames] at h
  | .lam x _ b, E, lv, pv, d, n, h => by
      simp only [elabMI, freeNames, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨hn, hk⟩ := h
      obtain ⟨y, rfl⟩ := freeNames_elabMI b _ _ _ _ n hn
      by_cases hy : y ∈ ownM E b
      · simp [lvUpdate, hy, ownKey] at hk
      · exact ⟨y, by simp [lvUpdate, hy]⟩
  | .app f a, E, lv, pv, d, n, h => by
      simp only [elabMI, freeNames, List.mem_append] at h
      rcases h with h | h
      · exact freeNames_elabMI f E lv pv d n h
      · exact freeNames_elabMI a E lv pv d n h
  | .quote _, _, _, _, _, n, h => by simp [elabMI, freeNames] at h
  | .ctx _ _, _, _, _, _, n, h => by simp [elabMI, freeNames] at h
  | .pquote c, E, lv, pv, d, n, h => by
      simp only [elabMI, freeNames] at h
      exact freeNames_elabMI c E lv pv d n h
  | .letP p w b, E, lv, pv, d, n, h => by
      simp only [elabMI, freeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · exact freeNames_elabMI p E lv pv d n h
      · exact freeNames_elabMI w E lv pv d n h
      · exact freeNames_elabMI b E lv pv d n h
  | .alt t₁ t₂, E, lv, pv, d, n, h => by
      simp only [elabMI, freeNames, List.mem_append] at h
      rcases h with h | h
      · exact freeNames_elabMI t₁ E lv pv d n h
      · exact freeNames_elabMI t₂ E lv pv d n h

/-- Every free parameter of an identity-tagged term is a spelling at the
level the parameter environment gives it. -/
theorem freeParams_elabMI : ∀ (t : Tm S X) (E : List X) (lv pv : X → Lv) (d : ℕ),
    ∀ p ∈ freeParams (elabMI E lv pv d t), ∃ z, p = .src (pv z, z)
  | .sym _, _, _, _, _, p, h => by simp [elabMI, freeParams] at h
  | .fn _, _, _, _, _, p, h => by simp [elabMI, freeParams] at h
  | .var _, _, _, _, _, p, h => by simp [elabMI, freeParams] at h
  | .pvar m, _, _, pv, _, p, h => by
      simp only [elabMI, freeParams, List.mem_singleton] at h
      exact ⟨_, h⟩
  | .lam x _ b, E, lv, pv, d, p, h => by
      simp only [elabMI, freeParams, List.mem_filter, decide_eq_true_eq] at h
      obtain ⟨hp, hne⟩ := h
      obtain ⟨z, rfl⟩ := freeParams_elabMI b _ _ _ _ p hp
      by_cases hz : z = x.spell
      · subst hz
        simp [lvUpdate] at hne
      · exact ⟨z, by simp [lvUpdate, hz]⟩
  | .app f a, E, lv, pv, d, p, h => by
      simp only [elabMI, freeParams, List.mem_append] at h
      rcases h with h | h
      · exact freeParams_elabMI f E lv pv d p h
      · exact freeParams_elabMI a E lv pv d p h
  | .quote _, _, _, _, _, p, h => by simp [elabMI, freeParams] at h
  | .ctx _ _, _, _, _, _, p, h => by simp [elabMI, freeParams] at h
  | .pquote c, E, lv, pv, d, p, h => by
      simp only [elabMI, freeParams] at h
      exact freeParams_elabMI c E lv pv d p h
  | .letP q w b, E, lv, pv, d, p, h => by
      simp only [elabMI, freeParams, List.mem_append] at h
      rcases h with (h | h) | h
      · exact freeParams_elabMI q E lv pv d p h
      · exact freeParams_elabMI w E lv pv d p h
      · exact freeParams_elabMI b E lv pv d p h
  | .alt t₁ t₂, E, lv, pv, d, p, h => by
      simp only [elabMI, freeParams, List.mem_append] at h
      rcases h with h | h
      · exact freeParams_elabMI t₁ E lv pv d p h
      · exact freeParams_elabMI t₂ E lv pv d p h

/-- The depth of lambda nesting, outside sealed quotations. -/
def lamDepth : Tm S X → ℕ
  | .lam _ _ b => lamDepth b + 1
  | .app f a => max (lamDepth f) (lamDepth a)
  | .pquote c => lamDepth c
  | .letP p w b => max (max (lamDepth p) (lamDepth w)) (lamDepth b)
  | .alt t₁ t₂ => max (lamDepth t₁) (lamDepth t₂)
  | _ => 0

/-- A store-name environment at level `d`: every spelling is unbound or owned
by a lambda at a level from 1 to `d`. -/
def LvOK (d : ℕ) (lv : X → Lv) : Prop := ∀ y, lv y = .top ∨ ∃ j, 1 ≤ j ∧ j ≤ d ∧ lv y = .own j

/-- A parameter environment at level `d`. -/
def PvOK (d : ℕ) (pv : X → Lv) : Prop := ∀ z, ∃ j, j ≤ d ∧ pv z = .par j

/-- **A lambda at level `k`**: its parameter and own names carry `k`; its free
names come from the form level or from owners at strictly outer levels; its
free parameters are parameters of strictly outer levels; every free parameter
of its body is a parameter. -/
def LamAt (k : ℕ) (L : Tm S (Lv × X)) : Prop :=
  ∃ z own b, L = .lam (.src (.par k, z)) own b ∧ (∀ y ∈ own, y.1 = .own k) ∧
    (∀ n ∈ freeNames L, ∃ y, n = .src y ∧ (y.1 = .top ∨ ∃ j, 1 ≤ j ∧ j < k ∧ y.1 = .own j)) ∧
    (∀ p ∈ freeParams L, ∃ y, p = .src y ∧ ∃ j, j < k ∧ y.1 = .par j) ∧
    (∀ p ∈ freeParams b, ∃ y, p = .src y ∧ ∃ j, y.1 = .par j)

theorem LvOK.update {d : ℕ} {lv : X → Lv} (h : LvOK d lv) (ys : List X) :
    LvOK (d + 1) (lvUpdate lv ys (.own (d + 1))) := by
  intro y
  unfold lvUpdate
  split
  · exact Or.inr ⟨d + 1, by omega, le_refl _, rfl⟩
  · rcases h y with h | ⟨j, h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h1, by omega, h3⟩

theorem PvOK.update {d : ℕ} {pv : X → Lv} (h : PvOK d pv) (zs : List X) :
    PvOK (d + 1) (lvUpdate pv zs (.par (d + 1))) := by
  intro z
  unfold lvUpdate
  split
  · exact ⟨d + 1, le_refl _, rfl⟩
  · obtain ⟨j, h1, h2⟩ := h z
    exact ⟨j, by omega, h2⟩

/-- **Every lambda of an identity-tagged term sits at a level above the
environment's**, below the environment's level plus the nesting depth, with
its binders and free names scoped by level. -/
theorem lams_elabMI : ∀ (t : Tm S X) (E : List X) (lv pv : X → Lv) (d : ℕ), LvOK d lv →
    PvOK d pv → ∀ L ∈ lams (elabMI E lv pv d t), ∃ k, d < k ∧ k ≤ d + lamDepth t ∧ LamAt k L
  | .sym _, _, _, _, _, _, _, L, h => by simp [elabMI, lams] at h
  | .fn _, _, _, _, _, _, _, L, h => by simp [elabMI, lams] at h
  | .var _, _, _, _, _, _, _, L, h => by simp [elabMI, lams] at h
  | .pvar _, _, _, _, _, _, _, L, h => by simp [elabMI, lams] at h
  | .lam x _ b, E, lv, pv, d, hlv, hpv, L, h => by
      simp only [elabMI, lams, List.mem_cons] at h
      rcases h with rfl | h
      · refine ⟨d + 1, by omega, by simp [lamDepth], x.spell, _, _, rfl, ?_, ?_, ?_, ?_⟩
        · intro y hy
          simp only [List.mem_map] at hy
          obtain ⟨_, _, rfl⟩ := hy
          rfl
        · intro n hn
          simp only [freeNames, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hn
          obtain ⟨hn, hk⟩ := hn
          obtain ⟨y, rfl⟩ := freeNames_elabMI b _ _ _ _ n hn
          by_cases hy : y ∈ ownM E b
          · simp [lvUpdate, hy, ownKey] at hk
          · refine ⟨_, rfl, ?_⟩
            simp only [lvUpdate, hy, if_false]
            rcases hlv y with h | ⟨j, h1, h2, h3⟩
            · exact Or.inl h
            · exact Or.inr ⟨j, h1, by omega, h3⟩
        · intro p hp
          simp only [freeParams, List.mem_filter, decide_eq_true_eq] at hp
          obtain ⟨hp, hne⟩ := hp
          obtain ⟨z, rfl⟩ := freeParams_elabMI b _ _ _ _ p hp
          by_cases hz : z = x.spell
          · subst hz
            simp [lvUpdate] at hne
          · refine ⟨_, rfl, ?_⟩
            simp only [lvUpdate, List.mem_singleton, hz, if_false]
            obtain ⟨j, h1, h2⟩ := hpv z
            exact ⟨j, by omega, h2⟩
        · intro p hp
          obtain ⟨z, rfl⟩ := freeParams_elabMI b _ _ _ _ p hp
          refine ⟨_, rfl, ?_⟩
          obtain ⟨j, -, h2⟩ := (hpv.update [x.spell]) z
          exact ⟨j, h2⟩
      · obtain ⟨k, h1, h2, h3⟩ :=
          lams_elabMI b _ _ _ (d + 1) (hlv.update _) (hpv.update _) L h
        exact ⟨k, by omega, by simp only [lamDepth]; omega, h3⟩
  | .app f a, E, lv, pv, d, hlv, hpv, L, h => by
      simp only [elabMI, lams, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨k, h1, h2, h3⟩ := lams_elabMI f E lv pv d hlv hpv L h
        exact ⟨k, h1, by simp only [lamDepth]; omega, h3⟩
      · obtain ⟨k, h1, h2, h3⟩ := lams_elabMI a E lv pv d hlv hpv L h
        exact ⟨k, h1, by simp only [lamDepth]; omega, h3⟩
  | .quote _, _, _, _, _, _, _, L, h => by simp [elabMI, lams] at h
  | .ctx _ _, _, _, _, _, _, _, L, h => by simp [elabMI, lams] at h
  | .pquote c, E, lv, pv, d, hlv, hpv, L, h => by
      simp only [elabMI, lams] at h
      obtain ⟨k, h1, h2, h3⟩ := lams_elabMI c E lv pv d hlv hpv L h
      exact ⟨k, h1, by simp only [lamDepth]; omega, h3⟩
  | .letP p w b, E, lv, pv, d, hlv, hpv, L, h => by
      simp only [elabMI, lams, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨k, h1, h2, h3⟩ := lams_elabMI p E lv pv d hlv hpv L h
        exact ⟨k, h1, by simp only [lamDepth]; omega, h3⟩
      · obtain ⟨k, h1, h2, h3⟩ := lams_elabMI w E lv pv d hlv hpv L h
        exact ⟨k, h1, by simp only [lamDepth]; omega, h3⟩
      · obtain ⟨k, h1, h2, h3⟩ := lams_elabMI b E lv pv d hlv hpv L h
        exact ⟨k, h1, by simp only [lamDepth]; omega, h3⟩
  | .alt t₁ t₂, E, lv, pv, d, hlv, hpv, L, h => by
      simp only [elabMI, lams, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨k, h1, h2, h3⟩ := lams_elabMI t₁ E lv pv d hlv hpv L h
        exact ⟨k, h1, by simp only [lamDepth]; omega, h3⟩
      · obtain ⟨k, h1, h2, h3⟩ := lams_elabMI t₂ E lv pv d hlv hpv L h
        exact ⟨k, h1, by simp only [lamDepth]; omega, h3⟩

theorem syms_elabMI : ∀ (t : Tm S X) (E : List X) (lv pv : X → Lv) (d : ℕ),
    syms (elabMI E lv pv d t) = syms t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .var _, _, _, _, _ => rfl
  | .pvar _, _, _, _, _ => rfl
  | .lam _ _ b, E, lv, pv, d => by simp only [elabMI, syms]; exact syms_elabMI b _ _ _ _
  | .app f a, E, lv, pv, d => by
      simp only [elabMI, syms, syms_elabMI f, syms_elabMI a]
  | .quote _, _, _, _, _ => rfl
  | .ctx _ _, _, _, _, _ => rfl
  | .pquote c, E, lv, pv, d => by simp only [elabMI, syms, syms_elabMI c]
  | .letP p w b, E, lv, pv, d => by
      simp only [elabMI, syms, syms_elabMI p, syms_elabMI w, syms_elabMI b]
  | .alt t₁ t₂, E, lv, pv, d => by
      simp only [elabMI, syms, syms_elabMI t₁, syms_elabMI t₂]

theorem hasPQuote_elabMI : ∀ (t : Tm S X) (E : List X) (lv pv : X → Lv) (d : ℕ),
    hasPQuote (elabMI E lv pv d t) = hasPQuote t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .var _, _, _, _, _ => rfl
  | .pvar _, _, _, _, _ => rfl
  | .lam _ _ b, E, lv, pv, d => by simp only [elabMI, hasPQuote]; exact hasPQuote_elabMI b _ _ _ _
  | .app f a, E, lv, pv, d => by
      simp only [elabMI, hasPQuote, hasPQuote_elabMI f, hasPQuote_elabMI a]
  | .quote _, _, _, _, _ => rfl
  | .ctx _ _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .letP p w b, E, lv, pv, d => by
      simp only [elabMI, hasPQuote, hasPQuote_elabMI p, hasPQuote_elabMI w, hasPQuote_elabMI b]
  | .alt t₁ t₂, E, lv, pv, d => by
      simp only [elabMI, hasPQuote, hasPQuote_elabMI t₁, hasPQuote_elabMI t₂]

/-! ### The closure table of an identity-tagged program -/

/-- The level a lambda's parameter carries. -/
def lamLevel : Tm S (Lv × X) → ℕ
  | .lam (.src (.par k, _)) _ _ => k
  | _ => 0

open Classical in
/-- **The closure table of an identity-tagged program.**  `InProg` marks the
program's lambdas; a constructor's rule is the apply rule of the program
lambda it names; ranks fall with the level from the bound `B`: the names a
lambda at level `k` owns, and its parameter, have rank `B - k`, the same as
its constructor. -/
noncomputable def tableMI (name : Tm S (Lv × X) → S) (B : ℕ) (InProg : Tm S (Lv × X) → Prop) :
    CloTable S (Lv × X) where
  rule κ := if h : ∃ L, InProg L ∧ name L = κ then defunRule name h.choose else none
  rank κ := if h : ∃ L, InProg L ∧ name L = κ then B - lamLevel h.choose else 0
  ownerRank y := match y.1 with
    | .own k => some (B - k)
    | _ => none
  paramRank p := match p with
    | .src (.par k, _) => if k = 0 then none else some (B - k)
    | _ => none

section Table

variable {name : Tm S (Lv × X) → S} {B : ℕ} {InProg : Tm S (Lv × X) → Prop}

open Classical in
/-- A rule of the table is the apply rule of a program lambda, and its
constructor's rank is read off that lambda's level. -/
theorem tableMI_rule_some {κ : S} {r : ApplyRule S (Lv × X)}
    (h : (tableMI name B InProg).rule κ = some r) :
    ∃ L, InProg L ∧ name L = κ ∧ defunRule name L = some r ∧
      (tableMI name B InProg).rank κ = B - lamLevel L := by
  by_cases hex : ∃ L, InProg L ∧ name L = κ
  · have hr : (tableMI name B InProg).rule κ = defunRule name hex.choose := dif_pos hex
    have hk : (tableMI name B InProg).rank κ = B - lamLevel hex.choose := dif_pos hex
    exact ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, hr ▸ h, hk⟩
  · have hr : (tableMI name B InProg).rule κ = none := dif_neg hex
    rw [hr] at h
    cases h

open Classical in
/-- A program lambda's constructor carries its apply rule, at the rank of its
level, when the naming tells program lambdas apart. -/
theorem tableMI_rule (hinj : ∀ L L', InProg L → InProg L' → name L = name L' → L = L')
    {L : Tm S (Lv × X)} (hL : InProg L) :
    (tableMI name B InProg).rule (name L) = defunRule name L ∧
      (tableMI name B InProg).rank (name L) = B - lamLevel L := by
  have hex : ∃ L', InProg L' ∧ name L' = name L := ⟨L, hL, rfl⟩
  have hc : hex.choose = L := hinj _ _ hex.choose_spec.1 hL hex.choose_spec.2
  have hr : (tableMI name B InProg).rule (name L) = defunRule name hex.choose := dif_pos hex
  have hk : (tableMI name B InProg).rank (name L) = B - lamLevel hex.choose := dif_pos hex
  rw [hc] at hr hk
  exact ⟨hr, hk⟩

open Classical in
/-- A symbol that names no program lambda has no rule. -/
theorem tableMI_rule_none {κ : S} (h : ∀ L, InProg L → name L ≠ κ) :
    (tableMI name B InProg).rule κ = none :=
  dif_neg fun ⟨L, hL, he⟩ => h L hL he

/-- **The table is well formed** when every program lambda sits at a level
from 1 to `B`, with its binders scoped by level. -/
theorem tableMI_wf (hIn : ∀ L, InProg L → ∃ k, 1 ≤ k ∧ k ≤ B ∧ LamAt k L) :
    (tableMI name B InProg).WF := by
  have key : ∀ κ r, (tableMI name B InProg).rule κ = some r →
      ∃ k z, 1 ≤ k ∧ k ≤ B ∧ r.x = .src (.par k, z) ∧ (∀ y ∈ r.own, y.1 = .own k) ∧
        (tableMI name B InProg).rank κ = B - k ∧ ∃ L, defunRule name L = some r ∧
          ∃ x own b, L = .lam x own b := by
    intro κ r h
    obtain ⟨L, hL, -, hr, hk⟩ := tableMI_rule_some h
    obtain ⟨k, hk1, hkB, z, own, b, rfl, hown, -⟩ := hIn L hL
    simp only [defunRule, Option.some.injEq] at hr
    subst hr
    exact ⟨k, z, hk1, hkB, rfl, hown, by simpa [lamLevel] using hk, _, rfl, _, _, _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro κ r h y hy
    obtain ⟨k, z, hk1, -, -, hown, hk, -⟩ := key κ r h
    have := hown y hy
    rw [hk]
    show (match y.1 with | .own k => some (B - k) | _ => none) = _
    rw [this]
  · intro κ r h
    obtain ⟨k, z, hk1, -, hx, -, hk, -⟩ := key κ r h
    rw [hk, hx]
    show (if k = 0 then none else some (B - k)) = _
    rw [if_neg (by omega)]
  · intro κ r h
    obtain ⟨-, -, -, -, -, -, -, L, hr, x, own, b, rfl⟩ := key κ r h
    exact (defunRule_wf name x own b hr).1
  · intro κ r h
    obtain ⟨-, -, -, -, -, -, -, L, hr, x, own, b, rfl⟩ := key κ r h
    exact (defunRule_wf name x own b hr).2.1
  · intro κ r h
    obtain ⟨-, -, -, -, -, -, -, L, hr, x, own, b, rfl⟩ := key κ r h
    exact (defunRule_wf name x own b hr).2.2

/-- **Every identity-tagged form defunctionalizes under the table**: its
lambdas are program lambdas at levels from 1 to `B`, its symbols name no
program lambda, and it has no pattern quotation. -/
theorem tableMI_defunctionalizes
    (hinj : ∀ L L', InProg L → InProg L' → name L = name L' → L = L') (t' : Tm S (Lv × X))
    (hlams : ∀ L ∈ lams t', InProg L)
    (hlev : ∀ L ∈ lams t', ∃ k, 1 ≤ k ∧ k ≤ B ∧ LamAt k L)
    (hsyms : ∀ s ∈ syms t', ∀ L, InProg L → name L ≠ s) (hpq : hasPQuote t' = false) :
    (tableMI name B InProg).Defunctionalizes name t' := by
  refine ⟨fun L hL => (tableMI_rule hinj (hlams L hL)).1, ?_, ?_,
    fun s hs => tableMI_rule_none (hsyms s hs), hpq⟩
  · intro L hL
    obtain ⟨k, hk1, hkB, z, own, b, rfl, -, hfn, hfp, -⟩ := hlev L hL
    have hrank := (tableMI_rule (B := B) hinj (hlams _ hL)).2
    simp only [lamLevel] at hrank
    rw [CloTable.argsOK_iff]
    intro v hv
    simp only [refs, List.mem_append, List.mem_map] at hv
    rcases hv with ⟨n, hn, rfl⟩ | ⟨p, hp, rfl⟩
    · refine ⟨?_, by simp [freeParams]⟩
      intro m hm
      simp only [freeNames, List.mem_singleton] at hm
      subst hm
      obtain ⟨y, rfl, hy⟩ := hfn _ (List.mem_dedup.1 hn)
      obtain ⟨tg, y⟩ := y
      simp only at hy
      rcases hy with rfl | ⟨j, hj1, hjk, rfl⟩
      · rfl
      · show CloTable.rankOK _ _ (some (B - j)) = true
        simp only [CloTable.rankOK, hrank, decide_eq_true_eq]
        omega
    · refine ⟨by simp [freeNames], ?_⟩
      intro q hq
      simp only [freeParams, List.mem_singleton] at hq
      subst hq
      obtain ⟨y, rfl, j, hjk, hy⟩ := hfp _ (List.mem_dedup.1 hp)
      obtain ⟨tg, y⟩ := y
      simp only at hy
      subst hy
      by_cases hj : j = 0
      · subst hj
        rfl
      · show CloTable.rankOK _ _ (if j = 0 then none else some (B - j)) = true
        rw [if_neg hj]
        simp only [CloTable.rankOK, hrank, decide_eq_true_eq]
        omega
  · intro L hL
    obtain ⟨k, -, -, z, own, b, rfl, -, hfn, -, hpb⟩ := hlev L hL
    simp only [apartB, List.all_eq_true, decide_eq_true_eq]
    intro c hc hcb
    obtain ⟨y, rfl, hy⟩ := hfn _ (List.mem_dedup.1 hc)
    obtain ⟨y', hy', j, hj⟩ := hpb _ hcb
    simp only [Nm.src.injEq] at hy'
    subst hy'
    rw [hj] at hy
    rcases hy with h | ⟨_, _, _, h⟩ <;> cases h

end Table

/-! ### Defunctionalization of every identity-tagged program -/

/-- The lambdas of a program: those of its query and of its equations, each
elaborated as its own form by `elabTopMI`. -/
def progLams (t : Tm S X) (prog : S → Option (Tm S X)) (L : Tm S (Lv × X)) : Prop :=
  L ∈ lams (elabTopMI t) ∨ ∃ F e, prog F = some e ∧ L ∈ lams (elabTopMI e)

omit [DecidableEq X] in
theorem lvOK_top : LvOK 0 (fun _ : X => Lv.top) := fun _ => Or.inl rfl

omit [DecidableEq X] in
theorem pvOK_zero : PvOK 0 (fun _ : X => Lv.par 0) := fun _ => ⟨0, le_refl _, rfl⟩

/-- The lambdas of a form elaborated by `elabTopMI` sit at levels from 1 to its
nesting depth. -/
theorem lams_elabTopMI (t : Tm S X) :
    ∀ L ∈ lams (elabTopMI t), ∃ k, 1 ≤ k ∧ k ≤ lamDepth t ∧ LamAt k L := by
  intro L hL
  obtain ⟨k, h1, h2, h3⟩ := lams_elabMI t _ _ _ 0 lvOK_top pvOK_zero L hL
  exact ⟨k, h1, by omega, h3⟩

/-- **A form elaborated by `elabTopMI` is good under the table**: its free
names are unbound by any lambda (level `top`), its free parameters bound by
none (`par 0`); neither carries a rank. -/
theorem tableMI_good (name : Tm S (Lv × X) → S) (B : ℕ) (InProg : Tm S (Lv × X) → Prop)
    (t : Tm S X) : (tableMI name B InProg).good (defun name (elabTopMI t)) = true := by
  apply good_defun
  · intro n hn
    obtain ⟨y, rfl⟩ := freeNames_elabMI t _ _ _ _ n hn
    rfl
  · intro p hp
    obtain ⟨z, rfl⟩ := freeParams_elabMI t _ _ _ _ p hp
    rfl

/-- **Defunctionalization holds for every program elaborated with binder
identities, with no hygiene hypothesis.**  The query and the equations are
each elaborated by `elabTopMI` (rule M's own lists, binders named by level);
the closure table is `tableMI`.  Every lambda-free answer bag of the query is
the machine's answer bag of the transformed query, and every answer bag of
the transformed query comes from a related answer bag of the query.  The
hypotheses are the transformation's scope, not conditions on names: the
naming gives distinct program lambdas distinct constructors that no form
uses as a symbol, no form has a pattern quotation, and `B` bounds the nesting
depth (a finite program has such a bound). -/
theorem answerBag_defunctionalized_MI [DecidableEq S] (name : Tm S (Lv × X) → S) (B : ℕ)
    (prog : S → Option (Tm S X)) (t : Tm S X)
    (hinj : ∀ L L', progLams t prog L → progLams t prog L' → name L = name L' → L = L')
    (hfresh : ∀ L, progLams t prog L →
      name L ∉ syms t ∧ ∀ F e, prog F = some e → name L ∉ syms e)
    (hB : lamDepth t ≤ B) (hBp : ∀ F e, prog F = some e → lamDepth e ≤ B)
    (hpq : hasPQuote t = false) (hpqp : ∀ F e, prog F = some e → hasPQuote e = false) :
    (∀ bag, AnswerBag .static (fun F => (prog F).map elabTopMI) (elabTopMI t) bag →
      (∀ a ∈ bag, a.lamFree = true) →
      ∃ n, answersD (tableMI name B (progLams t prog))
        (defunProg name fun F => (prog F).map elabTopMI) n (defun name (elabTopMI t)) =
          some bag) ∧
    (∀ n bag', answersD (tableMI name B (progLams t prog))
        (defunProg name fun F => (prog F).map elabTopMI) n (defun name (elabTopMI t)) =
          some bag' →
      ∃ bag, AnswerBag .static (fun F => (prog F).map elabTopMI) (elabTopMI t) bag ∧
        List.Forall₂ (fun a a' => (tableMI name B (progLams t prog)).rel a a' = true) bag
          bag') := by
  have hIn : ∀ L, progLams t prog L → ∃ k, 1 ≤ k ∧ k ≤ B ∧ LamAt k L := by
    rintro L (hL | ⟨F, e, he, hL⟩)
    · obtain ⟨k, h1, h2, h3⟩ := lams_elabTopMI t L hL
      exact ⟨k, h1, by omega, h3⟩
    · obtain ⟨k, h1, h2, h3⟩ := lams_elabTopMI e L hL
      exact ⟨k, h1, by have := hBp F e he; omega, h3⟩
  have hT := tableMI_wf (name := name) hIn
  have ht : (tableMI name B (progLams t prog)).Defunctionalizes name (elabTopMI t) := by
    refine tableMI_defunctionalizes hinj _ (fun L hL => Or.inl hL)
      (fun L hL => hIn L (Or.inl hL)) ?_ (by rw [elabTopMI, hasPQuote_elabMI, hpq])
    intro s hs L hL he
    rw [elabTopMI, syms_elabMI] at hs
    exact (hfresh L hL).1 (he ▸ hs)
  refine answerBag_defunctionalized _ hT name _ _ ht (tableMI_good _ _ _ t) ?_
  intro F e' hF
  cases he : prog F with
  | none => rw [he] at hF; cases hF
  | some e =>
      rw [he] at hF
      simp only [Option.map_some, Option.some.injEq] at hF
      subst hF
      refine ⟨tableMI_defunctionalizes hinj _ (fun L hL => Or.inr ⟨F, e, he, hL⟩)
        (fun L hL => hIn L (Or.inr ⟨F, e, he, hL⟩)) ?_
        (by rw [elabTopMI, hasPQuote_elabMI, hpqp F e he]), tableMI_good _ _ _ e⟩
      intro s hs L hL hne
      rw [elabTopMI, syms_elabMI] at hs
      exact (hfresh L hL).2 F e he (hne ▸ hs)

end Mettapedia.GSLT.LanguageDef.TemplateScope

/-! ## Counterexamples: what the form-local condition does not give -/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.HygieneCorpus

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope

/-- Spellings of the examples. -/
inductive HSp where
  | f | y | z | w | x | a | b | c | d | u
  deriving DecidableEq, Repr

/-- Symbols of the examples, with four closure constructors. -/
inductive HSy where
  | Pair | g | n1 | n2 | n3 | n4 | n5 | mk | unit | Clo1 | Clo2 | Clo3 | Clo4
  deriving DecidableEq, Repr

abbrev HT := Tm HSy HSp

/-- `$y`. -/
def sv (q : HSp) : HT := .var (.src q)
/-- A parameter occurrence. -/
def pv (q : HSp) : HT := .pvar (.src q)
/-- A lambda as written. -/
def lm (q : HSp) (b : HT) : HT := .lam (.src q) [] b
def ap (f a : HT) : HT := .app f a
def k (c : HSy) : HT := .sym c
def pair (a b : HT) : HT := ap (ap (k .Pair) a) b
/-- `(let $q v b)`. -/
def lt (q : HSp) (v b : HT) : HT := .letP (sv q) v b

/-- No equations. -/
def noProg : HSy → Option HT := fun _ => none

/-! ### The capture the condition excludes -/

/-- `((lam w (Pair ($f 1) (let $y w $y))) 5)` with `lam w` owning `$y`: what
rule M makes of row 11's context when nothing outside writes `$y`. -/
def Ccap : HT :=
  ap (.lam (.src .w) [.y] (pair (ap (sv .f) (k .n1)) (lt .y (pv .w) (sv .y)))) (k .n5)

/-- `(lam z (Pair z $y))`, with `$y` free. -/
def Lcap : HT := lm .z (pair (pv .z) (sv .y))

/-- **Negative control of `freeNames_subst_captureFree`.**  A lambda of `Ccap`
owns the free `$y` of `Lcap`, and substituting `Lcap` for `$f` captures it.
Rule M never builds this pair in one form (`elabTopM_let_captureFree`). -/
theorem captureFree_negative :
    Nm.src .f ∈ freeNames Ccap ∧ Nm.src .y ∈ freeNames Lcap ∧ HSp.y ∈ ownedIn Ccap ∧
      Nm.src .y ∉ freeNames (subst (Sub.single (.src .f) Lcap) Sub.none Ccap) := by
  decide

/-! ### Row 13b: the query writes what an equation owns -/

/-- `L = (lam z (let $y z (g $y)))`, the body of `(= (mk) L)`. -/
def Lmk : HT := lm .z (lt .y (pv .z) (ap (k .g) (sv .y)))

/-- Row 13b: `(let $f (mk) (Pair ($f 1) (let $y 5 $y)))`. -/
def row13b : HT := lt .f (.fn .mk) (pair (ap (sv .f) (k .n1)) (lt .y (k .n5) (sv .y)))

/-- The equation, elaborated as its own form, owns `$y`. -/
theorem Lmk_elab : elabTopM Lmk = .lam (.src .z) [.y] (lt .y (pv .z) (ap (k .g) (sv .y))) := by
  decide

/-- **Row 13b has no well-formed table.**  Whatever table defunctionalizes the
equation of `mk` gives `$y` a rank, since `L` owns it; the query writes `$y`,
so it is not good.  `answerBag_defunctionalized` does not apply, although
the query is rule-M hygienic as a form (`elabTopM_hygienic`). -/
theorem library_not_good (T : CloTable HSy HSp) (name : HT → HSy) (hT : T.WF)
    (he : T.Defunctionalizes name (elabTopM Lmk)) :
    T.good (defun name (elabTopM row13b)) = false := by
  rw [Lmk_elab] at he
  have hr := he.rule (.lam (.src .z) [.y] (lt .y (pv .z) (ap (k .g) (sv .y)))) (by simp [lams])
  have hown : T.ownerRank .y = some _ := hT.own_rank _ _ hr .y (List.mem_singleton_self _)
  cases hg : T.good (defun name (elabTopM row13b)) with
  | false => rfl
  | true =>
      have hdef : defun name (elabTopM row13b) = elabTopM row13b := rfl
      have hfree : Nm.src HSp.y ∈ freeNames (defun name (elabTopM row13b)) := by
        rw [hdef]
        decide
      have := ((T.good_iff).1 hg).1 _ hfree
      simp [CloTable.nameRank, hown] at this

/-! ### One rule-M form whose owned spellings cross -/

/-- `A = (lam a (let $y a (lam d (let $w d (Pair $w $y)))))`. -/
def Acyc : HT := lm .a (lt .y (pv .a) (lm .d (lt .w (pv .d) (pair (sv .w) (sv .y)))))
/-- `B = (lam b (let $w b (lam c (let $y c (Pair $y $w)))))`. -/
def Bcyc : HT := lm .b (lt .w (pv .b) (lm .c (lt .y (pv .c) (pair (sv .y) (sv .w)))))
/-- `(Pair ((A 1) 2) ((B 3) 4))`. -/
def ownedCycle : HT := pair (ap (ap Acyc (k .n1)) (k .n2)) (ap (ap Bcyc (k .n3)) (k .n4))

/-- Rule M: `D` owns `$w` and captures `$y`. -/
def Dc : HT := .lam (.src .d) [.w] (lt .w (pv .d) (pair (sv .w) (sv .y)))
/-- Rule M: `A` owns `$y`. -/
def Ac : HT := .lam (.src .a) [.y] (lt .y (pv .a) Dc)
/-- Rule M: `C` owns `$y` and captures `$w`. -/
def Cc : HT := .lam (.src .c) [.y] (lt .y (pv .c) (pair (sv .y) (sv .w)))
/-- Rule M: `B` owns `$w`. -/
def Bc : HT := .lam (.src .b) [.w] (lt .w (pv .b) Cc)

theorem ownedCycle_elab :
    elabTopM ownedCycle = pair (ap (ap Ac (k .n1)) (k .n2)) (ap (ap Bc (k .n3)) (k .n4)) := by
  decide

/-- The form answers `(Pair (Pair 2 1) (Pair 4 3))`: no lambda in the answer,
and the form is hygienic (`elabTopM_hygienic`). -/
theorem ownedCycle_answers :
    answers .static noProg 40 (elabTopM ownedCycle) =
      some [pair (pair (k .n2) (k .n1)) (pair (k .n4) (k .n3))] := by
  decide

/-- **No table defunctionalizes the rule-M form `ownedCycle`.**  A table's
ranks are per spelling: `$y` is owned by `A` and by `C`, `$w` by `B` and by
`D`, so `rank A = rank C` and `rank B = rank D`; `D` carries `$y` and `C`
carries `$w`, so `rank D < rank A` and `rank C < rank B`.  The four make a
cycle. -/
theorem owned_rank_cycle (T : CloTable HSy HSp) (name : HT → HSy) (hT : T.WF)
    (he : T.Defunctionalizes name (elabTopM ownedCycle)) : False := by
  rw [ownedCycle_elab] at he
  have rA := he.rule Ac (by decide)
  have rB := he.rule Bc (by decide)
  have rC := he.rule Cc (by decide)
  have rD := he.rule Dc (by decide)
  have oA : T.ownerRank .y = some (T.rank (name Ac)) :=
    hT.own_rank _ _ rA .y (List.mem_singleton_self _)
  have oC : T.ownerRank .y = some (T.rank (name Cc)) :=
    hT.own_rank _ _ rC .y (List.mem_singleton_self _)
  have oB : T.ownerRank .w = some (T.rank (name Bc)) :=
    hT.own_rank _ _ rB .w (List.mem_singleton_self _)
  have oD : T.ownerRank .w = some (T.rank (name Dc)) :=
    hT.own_rank _ _ rD .w (List.mem_singleton_self _)
  have aD := ((T.argsOK_iff).1 (he.args Dc (by decide)) (.var (.src .y)) (by decide)).1
    (.src .y) (by simp [freeNames])
  have aC := ((T.argsOK_iff).1 (he.args Cc (by decide)) (.var (.src .w)) (by decide)).1
    (.src .w) (by simp [freeNames])
  simp only [CloTable.nameRank, oA, CloTable.rankOK, decide_eq_true_eq] at aD
  simp only [CloTable.nameRank, oB, CloTable.rankOK, decide_eq_true_eq] at aC
  rw [oA] at oC
  rw [oB] at oD
  simp only [Option.some.injEq] at oC oD
  omega

/-! ### The same cycle through parameter names -/

/-- `(lam a (lam d (Pair a d)))`. -/
def Apar : HT := lm .a (lm .d (pair (pv .a) (pv .d)))
/-- `(lam d (lam a (Pair a d)))`. -/
def Bpar : HT := lm .d (lm .a (pair (pv .a) (pv .d)))
/-- The inner lambda of `Apar`, capturing the parameter `a`. -/
def Dpar : HT := lm .d (pair (pv .a) (pv .d))
/-- The inner lambda of `Bpar`, capturing the parameter `d`. -/
def Cpar : HT := lm .a (pair (pv .a) (pv .d))
/-- `(Pair ((Apar 1) 2) ((Bpar 3) 4))`: no store name at all. -/
def paramCycle : HT := pair (ap (ap Apar (k .n1)) (k .n2)) (ap (ap Bpar (k .n3)) (k .n4))

theorem paramCycle_elab : elabTopM paramCycle = paramCycle := by decide

theorem paramCycle_answers :
    answers .static noProg 40 (elabTopM paramCycle) =
      some [pair (pair (k .n1) (k .n2)) (pair (k .n4) (k .n3))] := by
  decide

/-- **No table defunctionalizes `paramCycle`, whatever the ownership rule.**
Parameter ranks are per name: `a` is the parameter of `Apar` and of `Cpar`,
`d` of `Dpar` and of `Bpar`; `Dpar` carries `a`, `Cpar` carries `d`. -/
theorem param_rank_cycle (T : CloTable HSy HSp) (name : HT → HSy) (hT : T.WF)
    (he : T.Defunctionalizes name (elabTopM paramCycle)) : False := by
  rw [paramCycle_elab] at he
  have rA := he.rule Apar (by decide)
  have rB := he.rule Bpar (by decide)
  have rC := he.rule Cpar (by decide)
  have rD := he.rule Dpar (by decide)
  have xA : T.paramRank (.src .a) = some (T.rank (name Apar)) := hT.x_rank _ _ rA
  have xB : T.paramRank (.src .d) = some (T.rank (name Bpar)) := hT.x_rank _ _ rB
  have xC : T.paramRank (.src .a) = some (T.rank (name Cpar)) := hT.x_rank _ _ rC
  have xD : T.paramRank (.src .d) = some (T.rank (name Dpar)) := hT.x_rank _ _ rD
  have aD := ((T.argsOK_iff).1 (he.args Dpar (by decide)) (.pvar (.src .a)) (by decide)).2
    (.src .a) (by simp [freeParams])
  have aC := ((T.argsOK_iff).1 (he.args Cpar (by decide)) (.pvar (.src .d)) (by decide)).2
    (.src .d) (by simp [freeParams])
  rw [xA, CloTable.rankOK, decide_eq_true_eq] at aD
  rw [xB, CloTable.rankOK, decide_eq_true_eq] at aC
  rw [xA] at xC
  rw [xB] at xD
  simp only [Option.some.injEq] at xC xD
  omega

/-! ### Capture across forms, on the core evaluator -/

/-- `(= (mk) (lam x (lam z (let $w z (Pair $w x)))))`: the inner lambda owns
`$w` and captures the parameter `x`. -/
def mkW : HT := lm .x (lm .z (lt .w (pv .z) (pair (sv .w) (pv .x))))
/-- The same equation with its private name spelled `$y`. -/
def mkY : HT := lm .x (lm .z (lt .y (pv .z) (pair (sv .y) (pv .x))))
/-- A program whose only equation is `(= (mk) e)`, elaborated as its own form. -/
def progMk (e : HT) : HSy → Option HT := fun F => if F = .mk then some (elabTopM e) else none
/-- `(let $w 5 (((mk) $w) 1))`. -/
def queryW : HT := lt .w (k .n5) (ap (ap (.fn .mk) (sv .w)) (k .n1))

/-- **The core evaluator captures across forms.**  The caller passes its own
`$w` through the parameter `x`; activation puts it under the inner lambda's own
binder for `$w`, and the next activation renames it as the lambda's local.  The
answer then depends on how the library spells its private name: `(Pair 1 1)`
against `(Pair 1 5)`.  Both forms are rule-M hygienic on their own. -/
theorem cross_form_capture :
    answers .static (progMk mkW) 40 (elabTopM queryW) = some [pair (k .n1) (k .n1)] ∧
    answers .static (progMk mkY) 40 (elabTopM queryW) = some [pair (k .n1) (k .n5)] := by
  decide

/-- The spectrum's slot model, with the same program under rule M: owned
names are slots `(owner, spelling)`, the caller's `$w` is the query's slot and
the library's local is its own, so both spellings answer `(Pair 1 5)`. -/
def mkWsrc (q : HSp) : Src HSy HSp :=
  .lam .x none (.lam .z none (.letS (.sv q) (.par .z)
    (.app (.app (.sym .Pair) (.sv q)) (.par .x)) none))

/-- The query of `cross_form_capture`, as authored text. -/
def queryWsrc : Src HSy HSp :=
  .letS (.sv .w) (.sym .n5) (.app (.app (.fn .mk) (.sv .w)) (.sym .n1)) none

/-- The program of the slot model. -/
def progSlot (q : HSp) : HSy → Option (Tm HSy (Slot HSp)) :=
  fun F => if F = .mk then some (clauseOf cfgM [5] .u .unit (mkWsrc q)) else none

theorem cross_form_slots :
    answersCfg cfgM (progSlot .w) 80 queryWsrc =
      some [.app (.app (.sym .Pair) (.sym .n1)) (.sym .n5)] ∧
    answersCfg cfgM (progSlot .y) 80 queryWsrc =
      some [.app (.app (.sym .Pair) (.sym .n1)) (.sym .n5)] := by
  decide

/-! ### With binder identities: the counterexamples go through -/

/-- Identity-tagged terms of the examples. -/
abbrev HI := Tm HSy (Lv × HSp)

/-- `(Pair a b)` among identity-tagged terms. -/
def pairI (a b : HI) : HI := .app (.app (.sym .Pair) a) b
def kI (c : HSy) : HI := .sym c

/-- The equation `(= (mk) e)` as a program of text. -/
def progRaw (e : HT) : HSy → Option HT := fun F => if F = .mk then some e else none

/-- **The capture is gone with binder identities.**  Both spellings of the
library's private name answer `(Pair 1 5)`: the caller's `$w` is `(top, w)`,
the library's local `(own 2, w)`. -/
theorem cross_form_fixed :
    answers .static (fun F => (progRaw mkW F).map elabTopMI) 40 (elabTopMI queryW) =
      some [pairI (kI .n1) (kI .n5)] ∧
    answers .static (fun F => (progRaw mkY F).map elabTopMI) 40 (elabTopMI queryW) =
      some [pairI (kI .n1) (kI .n5)] := by
  decide

/-- The identities change nothing but the names of binders: forgetting them
gives rule M's elaboration of the examples. -/
theorem examples_untag :
    untag (elabTopMI ownedCycle) = elabTopM ownedCycle ∧
    untag (elabTopMI paramCycle) = elabTopM paramCycle ∧
    untag (elabTopMI mkW) = elabTopM mkW :=
  ⟨untag_elabTopMI _ (by decide), untag_elabTopMI _ (by decide), untag_elabTopMI _ (by decide)⟩

/-- A naming of closure constructors by position in a list of lambdas. -/
def nameOf (Ls : List HI) (L : HI) : HSy :=
  match Ls.idxOf L with
  | 0 => .Clo1
  | 1 => .Clo2
  | 2 => .Clo3
  | _ => .Clo4

theorem nameOf_mem (Ls : List HI) (L : HI) : nameOf Ls L ∈ [HSy.Clo1, .Clo2, .Clo3, .Clo4] := by
  unfold nameOf
  split <;> simp

/-- The four lambdas of `ownedCycle`, with identities. -/
def ownedLams : List HI := lams (elabTopMI ownedCycle)

/-- The four lambdas of `paramCycle`, with identities. -/
def paramLams : List HI := lams (elabTopMI paramCycle)

/-- **`ownedCycle` defunctionalizes once binders carry identities**: the
general theorem applies (no per-program table), and the machine answers
`(Pair (Pair 2 1) (Pair 4 3))`, as the form does. -/
theorem owned_cycle_defunctionalized :
    answers .static (fun F => (noProg F).map elabTopMI) 40 (elabTopMI ownedCycle) =
      some [pairI (pairI (kI .n2) (kI .n1)) (pairI (kI .n4) (kI .n3))] ∧
    ∃ n, answersD (tableMI (nameOf ownedLams) 2 (progLams ownedCycle noProg))
      (defunProg (nameOf ownedLams) fun F => (noProg F).map elabTopMI) n
      (defun (nameOf ownedLams) (elabTopMI ownedCycle)) =
        some [pairI (pairI (kI .n2) (kI .n1)) (pairI (kI .n4) (kI .n3))] := by
  have hans : answers .static (fun F => (noProg F).map elabTopMI) 40 (elabTopMI ownedCycle) =
      some [pairI (pairI (kI .n2) (kI .n1)) (pairI (kI .n4) (kI .n3))] := by decide
  refine ⟨hans, (answerBag_defunctionalized_MI (nameOf ownedLams) 2 noProg ownedCycle ?_ ?_
    (by decide) (by simp [noProg]) (by decide) (by simp [noProg])).1 _ ⟨40, hans⟩ (by decide)⟩
  · have hdec : ∀ L ∈ ownedLams, ∀ L' ∈ ownedLams, nameOf ownedLams L = nameOf ownedLams L' →
        L = L' := by decide
    rintro L L' (hL | ⟨F, e, he, -⟩) (hL' | ⟨F', e', he', -⟩) hn
    · exact hdec L hL L' hL' hn
    · simp [noProg] at he'
    · simp [noProg] at he
    · simp [noProg] at he
  · intro L _
    refine ⟨fun h => ?_, fun F e he => by simp [noProg] at he⟩
    have hm := nameOf_mem ownedLams L
    have hs : ∀ c ∈ [HSy.Clo1, .Clo2, .Clo3, .Clo4], c ∉ syms ownedCycle := by decide
    exact hs _ hm h

/-- **`paramCycle` defunctionalizes once binders carry identities**, with the
answer `(Pair (Pair 1 2) (Pair 4 3))`. -/
theorem param_cycle_defunctionalized :
    answers .static (fun F => (noProg F).map elabTopMI) 40 (elabTopMI paramCycle) =
      some [pairI (pairI (kI .n1) (kI .n2)) (pairI (kI .n4) (kI .n3))] ∧
    ∃ n, answersD (tableMI (nameOf paramLams) 2 (progLams paramCycle noProg))
      (defunProg (nameOf paramLams) fun F => (noProg F).map elabTopMI) n
      (defun (nameOf paramLams) (elabTopMI paramCycle)) =
        some [pairI (pairI (kI .n1) (kI .n2)) (pairI (kI .n4) (kI .n3))] := by
  have hans : answers .static (fun F => (noProg F).map elabTopMI) 40 (elabTopMI paramCycle) =
      some [pairI (pairI (kI .n1) (kI .n2)) (pairI (kI .n4) (kI .n3))] := by decide
  refine ⟨hans, (answerBag_defunctionalized_MI (nameOf paramLams) 2 noProg paramCycle ?_ ?_
    (by decide) (by simp [noProg]) (by decide) (by simp [noProg])).1 _ ⟨40, hans⟩ (by decide)⟩
  · have hdec : ∀ L ∈ paramLams, ∀ L' ∈ paramLams, nameOf paramLams L = nameOf paramLams L' →
        L = L' := by decide
    rintro L L' (hL | ⟨F, e, he, -⟩) (hL' | ⟨F', e', he', -⟩) hn
    · exact hdec L hL L' hL' hn
    · simp [noProg] at he'
    · simp [noProg] at he
    · simp [noProg] at he
  · intro L _
    refine ⟨fun h => ?_, fun F e he => by simp [noProg] at he⟩
    have hm := nameOf_mem paramLams L
    have hs : ∀ c ∈ [HSy.Clo1, .Clo2, .Clo3, .Clo4], c ∉ syms paramCycle := by decide
    exact hs _ hm h

end Mettapedia.GSLT.LanguageDef.TemplateScope.HygieneCorpus
