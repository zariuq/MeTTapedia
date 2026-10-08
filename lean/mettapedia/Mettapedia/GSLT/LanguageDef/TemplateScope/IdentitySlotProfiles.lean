import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotAnn

/-!
# Template scope: rule M and lexical fresh as annotated text

Each profile's two elaborations (slot model and identity model) factor through
one annotation of the authored text:

* `annM` — rule M's decisions: a lambda owns `ownRuleMDefault` (or its crossing
  set's complement), named after its covering pattern or a `new` at its body
  (`mKey`, `cKey`); a `let` introduces names only under a crossing set.
* `annLF` — lexical fresh's: a lambda owns names only under a crossing set,
  named after its head; a `let` introduces the pattern names not in force.

`elabMS_eq_slotOf`, `elabMId_eq_idOf`, `elabLF_eq_slotOf`, `elabLFId_eq_idOf`:
the four elaborations are `Ann.slotOf` and `Ann.idOf` of the annotation.
`annM_WF`, `annLF_WF`: the annotations are well formed on admissible text;
rule M's identities are admissible because a covering pattern is never a `let`
that introduces names (`findCover_not_letA`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v}

namespace Src

/-- No `new` block with names on the matched spine of a pattern. -/
def spineNewFree : Src S X → Bool
  | .app f a => f.spineNewFree && a.spineNewFree
  | .pquote c => c.spineNewFree
  | .letS p _ _ _ => p.spineNewFree
  | .unify p _ _ => p.spineNewFree
  | .new [] b => b.spineNewFree
  | .new (_ :: _) _ => false
  | _ => true

/-- Every pattern is without `new` blocks with names on its spine. -/
def patsNewFree : Src S X → Bool
  | .lam _ _ b => b.patsNewFree
  | .form _ b => b.patsNewFree
  | .app f a => f.patsNewFree && a.patsNewFree
  | .pquote c => c.patsNewFree
  | .letS p w b _ => p.spineNewFree && p.patsNewFree && w.patsNewFree && b.patsNewFree
  | .unify p w b => p.spineNewFree && p.patsNewFree && w.patsNewFree && b.patsNewFree
  | .alt t₁ t₂ => t₁.patsNewFree && t₂.patsNewFree
  | .new _ b => b.patsNewFree
  | _ => true

variable [DecidableEq X]

/-- Parameters not bound by a lambda of the text, outside sealed quotations. -/
def freePars : Src S X → List X
  | .par z => [z]
  | .lam z _ b => (freePars b).filter fun z' => decide (z' ≠ z)
  | .form z b => (freePars b).filter fun z' => decide (z' ≠ z)
  | .app f a => freePars f ++ freePars a
  | .pquote c => freePars c
  | .letS p w b _ => freePars p ++ freePars w ++ freePars b
  | .unify p w b => freePars p ++ freePars w ++ freePars b
  | .alt t₁ t₂ => freePars t₁ ++ freePars t₂
  | .new _ b => freePars b
  | _ => []

end Src

namespace IdSlot

/-- A `let` with the names it introduces: plain when there are none. -/
def Ann.letOf : List X → Ann S X → Ann S X → Ann S X → Ann S X
  | [], p, w, b => .letP p w b
  | y₀ :: ys, p, w, b => .letA y₀ ys p w b

variable [DecidableEq X]

/-- **Rule M's decisions**, in the identity model's context. -/
def annM (E cr : List X) (env : IEnv X) (fr pos : Owner) : Src S X → Ann S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .lam z none b =>
      .lam z (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b)
        (annM (ownRuleMDefault E b ++ Src.direct b ++ E)
          (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
            (ownRuleMDefault E b)))
          (env.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
          (pos ++ [0]) (pos ++ [0]) b)
  | .lam z (some sh) b =>
      .lam z (crossOwn (some sh) (Src.uses b) [])
        (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
          (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b)
        (annM (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
          (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)
          (env.set (crossOwn (some sh) (Src.uses b) [])
            (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
              (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b))
          (pos ++ [0]) (pos ++ [0]) b)
  | .app f a => .app (annM E cr env fr (pos ++ [0]) f) (annM E cr env fr (pos ++ [1]) a)
  | .quote c => .quote c
  | .pquote c => .pquote c
  | .letS p w b none =>
      .letP (annM E (letCr cr env fr pos p) env fr (pos ++ [0]) p) (annM E cr env fr (pos ++ [1]) w)
        (annM E (letCr cr env fr pos p) env fr (pos ++ [2]) b)
  | .letS p w b (some sh) =>
      Ann.letOf (mIntro (some sh) p)
        (annM (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0]) p)
        (annM E cr env fr (pos ++ [1]) w)
        (annM (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [2]) b)
  | .unify p w b =>
      .letP (annM E cr env fr (pos ++ [0]) p) (annM E cr env fr (pos ++ [1]) w)
        (annM E cr env fr (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (annM E cr env fr (pos ++ [0]) t₁) (annM E cr env fr (pos ++ [1]) t₂)
  | .new ys b =>
      .new ys (annM (ys ++ E) (cr.filter fun y => decide (y ∉ ys)) (env.set ys fun y => ⟨y, fr, pos, .new⟩)
        fr pos b)
  | .form z b =>
      .lam z [] (fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩)
        (annM E cr env (pos ++ [0]) (pos ++ [0]) b)

/-- **Lexical fresh's decisions.** -/
def annLF (cr : List X) (fr pos : Owner) : Src S X → Ann S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .lam z xs b =>
      .lam z (crossOwn xs (Src.uses b) []) (fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩)
        (annLF (crossIn xs (crossOwn xs (Src.uses b) []) cr) (pos ++ [0]) (pos ++ [0]) b)
  | .app f a => .app (annLF cr fr (pos ++ [0]) f) (annLF cr fr (pos ++ [1]) a)
  | .quote c => .quote c
  | .pquote c => .pquote c
  | .letS p w b xs =>
      Ann.letOf (lfIntro xs p cr) (annLF (crossIn xs (lfIntro xs p cr) cr) fr (pos ++ [0]) p)
        (annLF cr fr (pos ++ [1]) w) (annLF (crossIn xs (lfIntro xs p cr) cr) fr (pos ++ [2]) b)
  | .unify p w b =>
      .letP (annLF cr fr (pos ++ [0]) p) (annLF cr fr (pos ++ [1]) w) (annLF cr fr (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (annLF cr fr (pos ++ [0]) t₁) (annLF cr fr (pos ++ [1]) t₂)
  | .new ys b => .new ys (annLF (cr.filter fun y => decide (y ∉ ys)) fr pos b)
  | .form z b =>
      .lam z [] (fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩)
        (annLF cr (pos ++ [0]) (pos ++ [0]) b)

/-! ## The four elaborations are the annotation's -/

/-- **Rule M's slot elaboration is the annotation's.** -/
theorem elabMS_eq_slotOf : ∀ (t : Src S X) (E cr : List X) (envI : IEnv X) (fr posI : Owner)
    (env : REnv X) (posS : Owner), elabMS E env posS t = (annM E cr envI fr posI t).slotOf env posS
  | .sym _, _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _, _, _ => rfl
  | .lam z none b, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf, crossOwn_none]
      rw [elabMS_eq_slotOf b]
  | .lam z (some sh) b, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf]
      rw [elabMS_eq_slotOf b]
      rfl
  | .app f a, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf]
      rw [elabMS_eq_slotOf f, elabMS_eq_slotOf a]
  | .quote _, _, _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _, _, _ => rfl
  | .letS p w b none, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf, crossOwn_none]
      rw [elabMS_eq_slotOf p, elabMS_eq_slotOf w, elabMS_eq_slotOf b]
  | .letS p w b (some sh), E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, mIntro]
      cases h : crossOwn (some sh) (Src.patNames p) [] with
      | nil =>
          simp only [Ann.letOf, Ann.slotOf, List.nil_append]
          rw [elabMS_eq_slotOf p, elabMS_eq_slotOf w, elabMS_eq_slotOf b]
      | cons y₀ ys =>
          simp only [Ann.letOf, Ann.slotOf]
          rw [elabMS_eq_slotOf p, elabMS_eq_slotOf w, elabMS_eq_slotOf b]
  | .unify p w b, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf]
      rw [elabMS_eq_slotOf p, elabMS_eq_slotOf w, elabMS_eq_slotOf b]
  | .alt t₁ t₂, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf]
      rw [elabMS_eq_slotOf t₁, elabMS_eq_slotOf t₂]
  | .new [] b, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf, List.nil_append]
      rw [elabMS_eq_slotOf b]
  | .new (y₀ :: ys) b, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf]
      rw [elabMS_eq_slotOf b]
  | .form z b, E, cr, envI, fr, posI, env, posS => by
      simp only [elabMS, annM, Ann.slotOf, formedLam, List.map_nil]
      rw [elabMS_eq_slotOf b]

/-- **Rule M's identity elaboration is the annotation's.** -/
theorem elabMId_eq_idOf : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (pv : X → Owner)
    (fr pos : Owner), elabMId E cr env pv fr pos t = (annM E cr env fr pos t).idOf env pv fr pos
  | .sym _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _, _ => rfl
  | .lam z none b, E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM, Ann.idOf]
      rw [elabMId_eq_idOf b]
  | .lam z (some sh) b, E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM, Ann.idOf]
      rw [elabMId_eq_idOf b]
  | .app f a, E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM, Ann.idOf]
      rw [elabMId_eq_idOf f, elabMId_eq_idOf a]
  | .quote _, _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _, _ => rfl
  | .letS p w b none, E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM, Ann.idOf]
      rw [elabMId_eq_idOf p, elabMId_eq_idOf w, elabMId_eq_idOf b]
  | .letS p w b (some sh), E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM]
      rw [elabMId_eq_idOf p, elabMId_eq_idOf w, elabMId_eq_idOf b]
      cases mIntro (some sh) p with
      | nil => simp only [Ann.letOf, Ann.idOf, IEnv.set_nil]
      | cons y₀ ys => simp only [Ann.letOf, Ann.idOf]
  | .unify p w b, E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM, Ann.idOf]
      rw [elabMId_eq_idOf p, elabMId_eq_idOf w, elabMId_eq_idOf b]
  | .alt t₁ t₂, E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM, Ann.idOf]
      rw [elabMId_eq_idOf t₁, elabMId_eq_idOf t₂]
  | .new ys b, E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM, Ann.idOf]
      rw [elabMId_eq_idOf b]
  | .form z b, E, cr, env, pv, fr, pos => by
      simp only [elabMId, annM, Ann.idOf]
      rw [elabMId_eq_idOf b]
      simp only [IEnv.set_nil]

/-- **Lexical fresh's slot elaboration is the annotation's.** -/
theorem elabLF_eq_slotOf : ∀ (t : Src S X) (cr : List X) (fr posI : Owner) (env : REnv X)
    (posS : Owner), elabLF env cr posS t = (annLF cr fr posI t).slotOf env posS
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam z xs b, cr, fr, posI, env, posS => by
      simp only [elabLF, annLF, Ann.slotOf]
      rw [elabLF_eq_slotOf b]
  | .app f a, cr, fr, posI, env, posS => by
      simp only [elabLF, annLF, Ann.slotOf]
      rw [elabLF_eq_slotOf f, elabLF_eq_slotOf a]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS p w b xs, cr, fr, posI, env, posS => by
      simp only [elabLF, annLF]
      cases lfIntro xs p cr with
      | nil =>
          simp only [Ann.letOf, Ann.slotOf]
          rw [elabLF_eq_slotOf p, elabLF_eq_slotOf w, elabLF_eq_slotOf b]
      | cons y₀ ys =>
          simp only [Ann.letOf, Ann.slotOf]
          rw [elabLF_eq_slotOf p, elabLF_eq_slotOf w, elabLF_eq_slotOf b]
  | .unify p w b, cr, fr, posI, env, posS => by
      simp only [elabLF, annLF, Ann.slotOf]
      rw [elabLF_eq_slotOf p, elabLF_eq_slotOf w, elabLF_eq_slotOf b]
  | .alt t₁ t₂, cr, fr, posI, env, posS => by
      simp only [elabLF, annLF, Ann.slotOf]
      rw [elabLF_eq_slotOf t₁, elabLF_eq_slotOf t₂]
  | .new [] b, cr, fr, posI, env, posS => by
      simp only [elabLF, annLF, Ann.slotOf, filter_not_mem_nil]
      rw [elabLF_eq_slotOf b]
  | .new (y₀ :: ys) b, cr, fr, posI, env, posS => by
      simp only [elabLF, annLF, Ann.slotOf]
      rw [elabLF_eq_slotOf b]
  | .form z b, cr, fr, posI, env, posS => by
      simp only [elabLF, annLF, Ann.slotOf, formedLam, List.map_nil]
      rw [elabLF_eq_slotOf b]

/-- **Lexical fresh's identity elaboration is the annotation's.** -/
theorem elabLFId_eq_idOf : ∀ (t : Src S X) (cr : List X) (env : IEnv X) (pv : X → Owner)
    (fr pos : Owner), elabLFId cr env pv fr pos t = (annLF cr fr pos t).idOf env pv fr pos
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam z xs b, cr, env, pv, fr, pos => by
      simp only [elabLFId, annLF, Ann.idOf]
      rw [elabLFId_eq_idOf b]
  | .app f a, cr, env, pv, fr, pos => by
      simp only [elabLFId, annLF, Ann.idOf]
      rw [elabLFId_eq_idOf f, elabLFId_eq_idOf a]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS p w b xs, cr, env, pv, fr, pos => by
      simp only [elabLFId, annLF]
      rw [elabLFId_eq_idOf p, elabLFId_eq_idOf w, elabLFId_eq_idOf b]
      cases lfIntro xs p cr with
      | nil => simp only [Ann.letOf, Ann.idOf, IEnv.set_nil]
      | cons y₀ ys => simp only [Ann.letOf, Ann.idOf]
  | .unify p w b, cr, env, pv, fr, pos => by
      simp only [elabLFId, annLF, Ann.idOf]
      rw [elabLFId_eq_idOf p, elabLFId_eq_idOf w, elabLFId_eq_idOf b]
  | .alt t₁ t₂, cr, env, pv, fr, pos => by
      simp only [elabLFId, annLF, Ann.idOf]
      rw [elabLFId_eq_idOf t₁, elabLFId_eq_idOf t₂]
  | .new ys b, cr, env, pv, fr, pos => by
      simp only [elabLFId, annLF, Ann.idOf]
      rw [elabLFId_eq_idOf b]
  | .form z b, cr, env, pv, fr, pos => by
      simp only [elabLFId, annLF, Ann.idOf]
      rw [elabLFId_eq_idOf b]

/-! ## What the annotation keeps -/

omit [DecidableEq X] in
theorem Ann.names_letOf (I : List X) (p w b : Ann S X) :
    (Ann.letOf I p w b).names = p.names ++ w.names ++ b.names := by
  cases I <;> rfl

theorem Ann.freePars_letOf (I : List X) (p w b : Ann S X) :
    (Ann.letOf I p w b).freePars = p.freePars ++ w.freePars ++ b.freePars := by
  cases I <;> rfl

omit [DecidableEq X] in
theorem Ann.newFree_letOf (I : List X) (p w b : Ann S X) :
    (Ann.letOf I p w b).NewFree ↔ p.NewFree := by
  cases I <;> exact Iff.rfl

theorem Ann.WF_letOf (pos : Owner) (I : List X) (p w b : Ann S X) :
    (Ann.letOf I p w b).WF pos ↔
      p.NewFree ∧ p.WF (pos ++ [0]) ∧ w.WF (pos ++ [1]) ∧ b.WF (pos ++ [2]) := by
  cases I <;> exact Iff.rfl

omit [DecidableEq X] in
theorem Ann.letAAt_letOf (I : List X) (p w b : Ann S X) (q : Owner) :
    ((Ann.letOf I p w b).LetAAt (0 :: q) ↔ p.LetAAt q) ∧
      ((Ann.letOf I p w b).LetAAt (1 :: q) ↔ w.LetAAt q) ∧
      ((Ann.letOf I p w b).LetAAt (2 :: q) ↔ b.LetAAt q) := by
  cases I <;> exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem names_annM : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    (annM E cr env fr pos t).names = t.names
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam _ none b, _, _, _, _, _ => by simp only [annM, Ann.names, Src.names, names_annM b]
  | .lam _ (some _) b, _, _, _, _, _ => by simp only [annM, Ann.names, Src.names, names_annM b]
  | .app f a, _, _, _, _, _ => by simp only [annM, Ann.names, Src.names, names_annM f, names_annM a]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS p w b none, _, _, _, _, _ => by
      simp only [annM, Ann.names, Src.names, names_annM p, names_annM w, names_annM b]
  | .letS p w b (some _), _, _, _, _, _ => by
      simp only [annM, Ann.names_letOf, Src.names, names_annM p, names_annM w, names_annM b]
  | .unify p w b, _, _, _, _, _ => by
      simp only [annM, Ann.names, Src.names, names_annM p, names_annM w, names_annM b]
  | .alt t₁ t₂, _, _, _, _, _ => by
      simp only [annM, Ann.names, Src.names, names_annM t₁, names_annM t₂]
  | .new _ b, _, _, _, _, _ => by simp only [annM, Ann.names, Src.names, names_annM b]
  | .form _ b, _, _, _, _, _ => by simp only [annM, Ann.names, Src.names, names_annM b]

theorem srcFreePars_eq : ∀ t : Src S X, Ann.srcFreePars t = t.freePars
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .lam _ _ b => by simp only [Ann.srcFreePars, Src.freePars, srcFreePars_eq b]
  | .app f a => by simp only [Ann.srcFreePars, Src.freePars, srcFreePars_eq f, srcFreePars_eq a]
  | .quote _ => rfl
  | .pquote c => by simp only [Ann.srcFreePars, Src.freePars, srcFreePars_eq c]
  | .letS p w b _ => by
      simp only [Ann.srcFreePars, Src.freePars, srcFreePars_eq p, srcFreePars_eq w, srcFreePars_eq b]
  | .unify p w b => by
      simp only [Ann.srcFreePars, Src.freePars, srcFreePars_eq p, srcFreePars_eq w, srcFreePars_eq b]
  | .alt t₁ t₂ => by
      simp only [Ann.srcFreePars, Src.freePars, srcFreePars_eq t₁, srcFreePars_eq t₂]
  | .new _ b => by simp only [Ann.srcFreePars, Src.freePars, srcFreePars_eq b]
  | .form _ b => by simp only [Ann.srcFreePars, Src.freePars, srcFreePars_eq b]

theorem freePars_annM : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    (annM E cr env fr pos t).freePars = t.freePars
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam _ none b, _, _, _, _, _ => by
      simp only [annM, Ann.freePars, Src.freePars, freePars_annM b]
  | .lam _ (some _) b, _, _, _, _, _ => by
      simp only [annM, Ann.freePars, Src.freePars, freePars_annM b]
  | .app f a, _, _, _, _, _ => by
      simp only [annM, Ann.freePars, Src.freePars, freePars_annM f, freePars_annM a]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote c, _, _, _, _, _ => by
      simp only [annM, Ann.freePars, Src.freePars]
      exact srcFreePars_eq c
  | .letS p w b none, _, _, _, _, _ => by
      simp only [annM, Ann.freePars, Src.freePars, freePars_annM p, freePars_annM w, freePars_annM b]
  | .letS p w b (some _), _, _, _, _, _ => by
      simp only [annM, Ann.freePars_letOf, Src.freePars, freePars_annM p, freePars_annM w,
        freePars_annM b]
  | .unify p w b, _, _, _, _, _ => by
      simp only [annM, Ann.freePars, Src.freePars, freePars_annM p, freePars_annM w, freePars_annM b]
  | .alt t₁ t₂, _, _, _, _, _ => by
      simp only [annM, Ann.freePars, Src.freePars, freePars_annM t₁, freePars_annM t₂]
  | .new _ b, _, _, _, _, _ => by simp only [annM, Ann.freePars, Src.freePars, freePars_annM b]
  | .form _ b, _, _, _, _, _ => by simp only [annM, Ann.freePars, Src.freePars, freePars_annM b]

theorem names_annLF : ∀ (t : Src S X) (cr : List X) (fr pos : Owner),
    (annLF cr fr pos t).names = t.names
  | .sym _, _, _, _ => rfl
  | .fn _, _, _, _ => rfl
  | .sv _, _, _, _ => rfl
  | .par _, _, _, _ => rfl
  | .lam _ _ b, _, _, _ => by simp only [annLF, Ann.names, Src.names, names_annLF b]
  | .app f a, _, _, _ => by simp only [annLF, Ann.names, Src.names, names_annLF f, names_annLF a]
  | .quote _, _, _, _ => rfl
  | .pquote _, _, _, _ => rfl
  | .letS p w b _, _, _, _ => by
      simp only [annLF, Ann.names_letOf, Src.names, names_annLF p, names_annLF w, names_annLF b]
  | .unify p w b, _, _, _ => by
      simp only [annLF, Ann.names, Src.names, names_annLF p, names_annLF w, names_annLF b]
  | .alt t₁ t₂, _, _, _ => by
      simp only [annLF, Ann.names, Src.names, names_annLF t₁, names_annLF t₂]
  | .new _ b, _, _, _ => by simp only [annLF, Ann.names, Src.names, names_annLF b]
  | .form _ b, _, _, _ => by simp only [annLF, Ann.names, Src.names, names_annLF b]

theorem freePars_annLF : ∀ (t : Src S X) (cr : List X) (fr pos : Owner),
    (annLF cr fr pos t).freePars = t.freePars
  | .sym _, _, _, _ => rfl
  | .fn _, _, _, _ => rfl
  | .sv _, _, _, _ => rfl
  | .par _, _, _, _ => rfl
  | .lam _ _ b, _, _, _ => by simp only [annLF, Ann.freePars, Src.freePars, freePars_annLF b]
  | .app f a, _, _, _ => by
      simp only [annLF, Ann.freePars, Src.freePars, freePars_annLF f, freePars_annLF a]
  | .quote _, _, _, _ => rfl
  | .pquote c, _, _, _ => by
      simp only [annLF, Ann.freePars, Src.freePars]
      exact srcFreePars_eq c
  | .letS p w b _, _, _, _ => by
      simp only [annLF, Ann.freePars_letOf, Src.freePars, freePars_annLF p, freePars_annLF w,
        freePars_annLF b]
  | .unify p w b, _, _, _ => by
      simp only [annLF, Ann.freePars, Src.freePars, freePars_annLF p, freePars_annLF w,
        freePars_annLF b]
  | .alt t₁ t₂, _, _, _ => by
      simp only [annLF, Ann.freePars, Src.freePars, freePars_annLF t₁, freePars_annLF t₂]
  | .new _ b, _, _, _ => by simp only [annLF, Ann.freePars, Src.freePars, freePars_annLF b]
  | .form _ b, _, _, _ => by simp only [annLF, Ann.freePars, Src.freePars, freePars_annLF b]

/-! ## Patterns -/

theorem newFree_annM : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    t.spineNewFree = true → (annM E cr env fr pos t).NewFree
  | .sym _, _, _, _, _, _, _ => trivial
  | .fn _, _, _, _, _, _, _ => trivial
  | .sv _, _, _, _, _, _, _ => trivial
  | .par _, _, _, _, _, _, _ => trivial
  | .lam _ none _, _, _, _, _, _, _ => trivial
  | .lam _ (some _) _, _, _, _, _, _, _ => trivial
  | .app f a, _, _, _, _, _, h => by
      simp only [Src.spineNewFree, Bool.and_eq_true] at h
      exact ⟨newFree_annM f _ _ _ _ _ h.1, newFree_annM a _ _ _ _ _ h.2⟩
  | .quote _, _, _, _, _, _, _ => trivial
  | .pquote _, _, _, _, _, _, _ => trivial
  | .letS p _ _ none, _, _, _, _, _, h => newFree_annM p _ _ _ _ _ h
  | .letS p _ _ (some _), _, _, _, _, _, h => by
      simp only [annM]
      exact (Ann.newFree_letOf _ _ _ _).2 (newFree_annM p _ _ _ _ _ h)
  | .unify p _ _, _, _, _, _, _, h => newFree_annM p _ _ _ _ _ h
  | .alt _ _, _, _, _, _, _, _ => trivial
  | .new [] b, _, _, _, _, _, h => newFree_annM b _ _ _ _ _ h
  | .new (_ :: _) _, _, _, _, _, _, h => by simp [Src.spineNewFree] at h
  | .form _ _, _, _, _, _, _, _ => trivial

theorem newFree_annLF : ∀ (t : Src S X) (cr : List X) (fr pos : Owner),
    t.spineNewFree = true → (annLF cr fr pos t).NewFree
  | .sym _, _, _, _, _ => trivial
  | .fn _, _, _, _, _ => trivial
  | .sv _, _, _, _, _ => trivial
  | .par _, _, _, _, _ => trivial
  | .lam _ _ _, _, _, _, _ => trivial
  | .app f a, _, _, _, h => by
      simp only [Src.spineNewFree, Bool.and_eq_true] at h
      exact ⟨newFree_annLF f _ _ _ h.1, newFree_annLF a _ _ _ h.2⟩
  | .quote _, _, _, _, _ => trivial
  | .pquote _, _, _, _, _ => trivial
  | .letS p _ _ _, _, _, _, h => by
      simp only [annLF]
      exact (Ann.newFree_letOf _ _ _ _).2 (newFree_annLF p _ _ _ h)
  | .unify p _ _, _, _, _, h => newFree_annLF p _ _ _ h
  | .alt _ _, _, _, _, _ => trivial
  | .new [] b, _, _, _, h => newFree_annLF b _ _ _ h
  | .new (_ :: _) _, _, _, _, h => by simp [Src.spineNewFree] at h
  | .form _ _, _, _, _, _ => trivial

/-! ## Covering patterns are not activations -/

omit [DecidableEq X] in
theorem pick2_some {n₁ n₂ : ℕ} {r₁ r₂ : Option Owner} {P : Owner} (h : pick2 n₁ n₂ r₁ r₂ = some P) :
    (∃ P', r₁ = some P' ∧ P = 0 :: P') ∨ (∃ P', r₂ = some P' ∧ P = 1 :: P') := by
  unfold pick2 at h
  split_ifs at h
  · obtain ⟨P', hP', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Or.inl ⟨P', hP', rfl⟩
  · obtain ⟨P', hP', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Or.inr ⟨P', hP', rfl⟩

omit [DecidableEq X] in
theorem pick3_some {n₁ n₂ n₃ : ℕ} {r₁ r₂ r₃ : Option Owner} {P : Owner}
    (h : pick3 n₁ n₂ n₃ r₁ r₂ r₃ = some P) :
    (∃ P', r₁ = some P' ∧ P = 0 :: P') ∨ (∃ P', r₂ = some P' ∧ P = 1 :: P') ∨
      (∃ P', r₃ = some P' ∧ P = 2 :: P') := by
  unfold pick3 at h
  split_ifs at h
  · obtain ⟨P', hP', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Or.inl ⟨P', hP', rfl⟩
  · obtain ⟨P', hP', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Or.inr (Or.inl ⟨P', hP', rfl⟩)
  · obtain ⟨P', hP', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Or.inr (Or.inr ⟨P', hP', rfl⟩)

/-- **A covering pattern is never a `let` that introduces names**: the
position `findCover` returns is a plain `let` of the text, which rule M's
annotation keeps plain. -/
theorem findCover_not_letA : ∀ (t : Src S X) (E : List X) (y : X) (f : Bool) (P : Owner),
    findCover E y f t = some P →
      ∀ (E' cr : List X) (env : IEnv X) (fr pos : Owner), ¬ (annM E' cr env fr pos t).LetAAt P
  | .sym _, _, _, _, _, h => by simp [findCover] at h
  | .fn _, _, _, _, _, h => by simp [findCover] at h
  | .sv _, _, _, _, _, h => by simp [findCover] at h
  | .par _, _, _, _, _, h => by simp [findCover] at h
  | .lam _ _ _, _, _, _, _, h => by simp [findCover] at h
  | .form _ _, _, _, _, _, h => by simp [findCover] at h
  | .quote _, _, _, _, _, h => by simp [findCover] at h
  | .app a b, E, y, f, P, h => by
      intro E' cr env fr pos
      simp only [findCover] at h
      rcases pick2_some h with ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩
      · exact findCover_not_letA a E y f P' hP' _ _ _ _ _
      · exact findCover_not_letA b E y f P' hP' _ _ _ _ _
  | .alt a b, E, y, f, P, h => by
      intro E' cr env fr pos
      simp only [findCover] at h
      rcases pick2_some h with ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩
      · exact findCover_not_letA a E y f P' hP' _ _ _ _ _
      · exact findCover_not_letA b E y f P' hP' _ _ _ _ _
  | .pquote _, _, _, _, _, h => by
      simp only [findCover] at h
      cases h
  | .unify p w b, E, y, f, P, h => by
      intro E' cr env fr pos
      simp only [findCover] at h
      rcases pick3_some h with ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩
      · exact findCover_not_letA p E y f P' hP' _ _ _ _ _
      · exact findCover_not_letA w E y f P' hP' _ _ _ _ _
      · exact findCover_not_letA b E y f P' hP' _ _ _ _ _
  | .letS p w b none, E, y, f, P, h => by
      intro E' cr env fr pos
      simp only [findCover] at h
      split_ifs at h with hy hf
      · injection h with h
        subst h
        exact fun h => h
      · rcases pick3_some h with ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩
        · exact findCover_not_letA p E y f P' hP' _ _ _ _ _
        · exact findCover_not_letA w E y f P' hP' _ _ _ _ _
        · exact findCover_not_letA b E y f P' hP' _ _ _ _ _
  | .letS p w b (some sh), E, y, f, P, h => by
      intro E' cr env fr pos
      simp only [findCover] at h
      simp only [annM]
      split_ifs at h with hy
      · obtain ⟨P', hP', rfl⟩ := Option.map_eq_some_iff.1 h
        rw [(Ann.letAAt_letOf _ _ _ _ _).2.1]
        exact findCover_not_letA w E y f P' hP' _ _ _ _ _
      · rcases pick3_some h with ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩
        · rw [(Ann.letAAt_letOf _ _ _ _ _).1]
          exact findCover_not_letA p _ y _ P' hP' _ _ _ _ _
        · rw [(Ann.letAAt_letOf _ _ _ _ _).2.1]
          exact findCover_not_letA w E y f P' hP' _ _ _ _ _
        · rw [(Ann.letAAt_letOf _ _ _ _ _).2.2]
          exact findCover_not_letA b _ y _ P' hP' _ _ _ _ _
  | .new ys b, E, y, f, P, h => by
      intro E' cr env fr pos
      simp only [findCover] at h
      split_ifs at h with hy
      exact findCover_not_letA b _ y f P h _ _ _ _ _

/-! ## Well-formedness -/

theorem mKey_ok (E cr : List X) (F : Owner) (b : Src S X) (E' cr' : List X) (env : IEnv X)
    (y : X) : (mKey E cr F b y).spell = y ∧ (mKey E cr F b y).frame = F ∧
      KeyOK F (annM E' cr' env F F b) (mKey E cr F b y) := by
  unfold mKey
  cases h : findCover E y (decide (y ∈ cr)) b with
  | none => exact ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | some P =>
      exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, P, rfl, findCover_not_letA b E y _ P h _ _ _ _ _⟩)⟩

theorem cKey_ok (E cr : List X) (F : Owner) (b : Src S X) (E' cr' : List X) (env : IEnv X)
    (y : X) : (cKey E cr F b y).spell = y ∧ (cKey E cr F b y).frame = F ∧
      KeyOK F (annM E' cr' env F F b) (cKey E cr F b y) := by
  unfold cKey
  cases h : findCover E y (decide (y ∈ cr)) b with
  | none => exact ⟨rfl, rfl, Or.inl rfl⟩
  | some P =>
      exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, P, rfl, findCover_not_letA b E y _ P h _ _ _ _ _⟩)⟩

/-- **Rule M's annotation is well formed when no `new` stands on a pattern spine.**
A quotation in pattern position is the two elaborations of that code. -/
theorem annM_WF : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    t.patsNewFree = true → (annM E cr env fr pos t).WF pos
  | .sym _, _, _, _, _, _, _ => trivial
  | .fn _, _, _, _, _, _, _ => trivial
  | .sv _, _, _, _, _, _, _ => trivial
  | .par _, _, _, _, _, _, _ => trivial
  | .lam _ none b, _, _, _, _, _, h => by
      simp only [Src.patsNewFree] at h
      exact ⟨fun y _ => mKey_ok _ _ _ b _ _ _ y, annM_WF b _ _ _ _ _ h⟩
  | .lam _ (some _) b, _, _, _, _, _, h => by
      simp only [Src.patsNewFree] at h
      exact ⟨fun y _ => cKey_ok _ _ _ b _ _ _ y, annM_WF b _ _ _ _ _ h⟩
  | .app f a, _, _, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      exact ⟨annM_WF f _ _ _ _ _ h.1, annM_WF a _ _ _ _ _ h.2⟩
  | .quote _, _, _, _, _, _, _ => trivial
  | .pquote c, _, _, _, _, _, _ => by
      simp only [annM, Ann.WF]
      intro env envI hB hF
      exact codeRel_pattern env envI hB hF c
  | .letS p w b none, _, _, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      exact ⟨newFree_annM p _ _ _ _ _ h.1.1.1, annM_WF p _ _ _ _ _ h.1.1.2,
        annM_WF w _ _ _ _ _ h.1.2, annM_WF b _ _ _ _ _ h.2⟩
  | .letS p w b (some _), _, _, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      simp only [annM]
      exact (Ann.WF_letOf _ _ _ _ _).2 ⟨newFree_annM p _ _ _ _ _ h.1.1.1,
        annM_WF p _ _ _ _ _ h.1.1.2, annM_WF w _ _ _ _ _ h.1.2,
        annM_WF b _ _ _ _ _ h.2⟩
  | .unify p w b, _, _, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      exact ⟨newFree_annM p _ _ _ _ _ h.1.1.1, annM_WF p _ _ _ _ _ h.1.1.2,
        annM_WF w _ _ _ _ _ h.1.2, annM_WF b _ _ _ _ _ h.2⟩
  | .alt t₁ t₂, _, _, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      exact ⟨annM_WF t₁ _ _ _ _ _ h.1, annM_WF t₂ _ _ _ _ _ h.2⟩
  | .new _ b, _, _, _, _, _, h => by
      simp only [Src.patsNewFree] at h
      exact annM_WF b _ _ _ _ _ h
  | .form _ b, _, _, _, _, _, h => by
      simp only [Src.patsNewFree] at h
      exact ⟨fun y hy => by simp at hy, annM_WF b _ _ _ _ _ h⟩

/-- **Lexical fresh's annotation is well formed when no `new` stands on a pattern spine.** -/
theorem annLF_WF : ∀ (t : Src S X) (cr : List X) (fr pos : Owner),
    t.patsNewFree = true → (annLF cr fr pos t).WF pos
  | .sym _, _, _, _, _ => trivial
  | .fn _, _, _, _, _ => trivial
  | .sv _, _, _, _, _ => trivial
  | .par _, _, _, _, _ => trivial
  | .lam _ _ b, _, _, _, h => by
      simp only [Src.patsNewFree] at h
      exact ⟨fun y _ => ⟨rfl, rfl, Or.inl rfl⟩, annLF_WF b _ _ _ h⟩
  | .app f a, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      exact ⟨annLF_WF f _ _ _ h.1, annLF_WF a _ _ _ h.2⟩
  | .quote _, _, _, _, _ => trivial
  | .pquote c, _, _, _, _ => by
      simp only [annLF, Ann.WF]
      intro env envI hB hF
      exact codeRel_pattern env envI hB hF c
  | .letS p w b _, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      simp only [annLF]
      exact (Ann.WF_letOf _ _ _ _ _).2 ⟨newFree_annLF p _ _ _ h.1.1.1,
        annLF_WF p _ _ _ h.1.1.2, annLF_WF w _ _ _ h.1.2, annLF_WF b _ _ _ h.2⟩
  | .unify p w b, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      exact ⟨newFree_annLF p _ _ _ h.1.1.1, annLF_WF p _ _ _ h.1.1.2,
        annLF_WF w _ _ _ h.1.2, annLF_WF b _ _ _ h.2⟩
  | .alt t₁ t₂, _, _, _, h => by
      simp only [Src.patsNewFree, Bool.and_eq_true] at h
      exact ⟨annLF_WF t₁ _ _ _ h.1, annLF_WF t₂ _ _ _ h.2⟩
  | .new _ b, _, _, _, h => by
      simp only [Src.patsNewFree] at h
      exact annLF_WF b _ _ _ h
  | .form _ b, _, _, _, h => by
      simp only [Src.patsNewFree] at h
      exact ⟨fun y hy => by simp at hy, annLF_WF b _ _ _ h⟩

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
