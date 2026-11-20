import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ScopedText

/-!
# Hygiene along every run of a well-formed program

`ReachableHygienic` was the one hypothesis of the run theorems with arrows. It holds for every
well-formed program and query of the fragment with arrows, so the run theorems hold for them without
it, nested calls included.

**The invariant** (`ScopedAt n b Vis L Ls`): a set `Vis` of visible names, a level `L` for the
focus and a level per pending frame (`Ls`) such that

* the visible names and all levels are below the scope counter `n` (so what a copy or an opening at
  `n` makes is new);
* every name of the store and of a value is visible; the focus is scoped at run time at its level;
  every pending frame is a `let` whose pattern and body are scoped inside the `let` at its level;
* the binders of the alternative (each `let` of the focus and of the pending bodies at its level,
  each pending frame at its level) are distinct, and no visible name is an own name of one of them.

**Preservation** (`scopedAt_children`): each move of the fragment keeps it: a call adds the
equation's own names at the new scope `[n]` and the binders of the copy at `[n]`; a bind adds the
frame's own names opened at `n :: L` and gives its binders to the focus; `ret`, `choice`, a
`let` start and an unmatched call keep or permute the binders. Every other move is impossible in
the fragment. Another alternative's move only raises the counter (`ScopedAt.mono`).

**Hygiene** (`hygienic_of_scopedAt`): the own names of the first pending frame are its site at its
level; they are not visible and are not the own names of another binder, so the store, the value and
the other frames do not contain them.

What the lemma uses of well-formedness: each equation scoped (`Equation.Scoped`) with its own site
and its binder sites distinct (`(e.site :: e.rhs.sites).Nodup`); the query scoped from its site with
the same distinctness. Distinctness across different equations is not used (copies at different
scopes never share names); the patterns clause is not used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}

/-! ## The invariant -/

section Invariant

variable {Ty : Type}

/-- The pending frames, each at its level: `let` frames whose pattern and body are scoped inside the
`let`. -/
def FramesScoped (Vis : Name κ → Prop) : List (SourceLanguage.Frame κ Γ star Ty) → List (List ℕ) → Prop
  | [], [] => True
  | .bindTo s p k :: fs, L :: Ls =>
      (∀ x ∈ support p, insideLet Vis s L x) ∧ RScoped (insideLet Vis s L) L k ∧ FramesScoped Vis fs Ls
  | _, _ => False

/-- The binders of the pending frames: each frame at its level, and the `let`s of its body. -/
def framesBinders : List (SourceLanguage.Frame κ Γ star Ty) → List (List ℕ) → List (κ.Site × List ℕ)
  | .bindTo s _ k :: fs, L :: Ls => (s, L) :: (k.sites.map (·, L) ++ framesBinders fs Ls)
  | _, _ => []

/-- The focus at its level: a computation scoped at run time, or a value of visible names. -/
def FocusScoped (Vis : Name κ → Prop) (L : List ℕ) : Focus κ Γ star Ty → Prop
  | .eval c => RScoped Vis L c
  | .value v => ∀ x ∈ support v, Vis x
  | .refused _ _ => False

/-- The binders of the focus: the `let`s of the computation it runs, at its level. -/
def focusBinders (L : List ℕ) : Focus κ Γ star Ty → List (κ.Site × List ℕ)
  | .eval c => c.sites.map (·, L)
  | _ => []

/-- All binders of an alternative. -/
def binders (L : List ℕ) (Ls : List (List ℕ)) (b : Branch κ Γ star Ty) : List (κ.Site × List ℕ) :=
  focusBinders L b.focus ++ framesBinders b.frames Ls

/-- **Run-time scoping of an alternative** below the scope counter `n`. -/
structure ScopedAt (n : ℕ) (b : Branch κ Γ star Ty) (Vis : Name κ → Prop) (L : List ℕ)
    (Ls : List (List ℕ)) : Prop where
  visibleBelow : ∀ x, Vis x → Below n x
  levelBelow : LevelBelow n L
  levelsBelow : ∀ L' ∈ Ls, LevelBelow n L'
  store : ∀ e ∈ b.store, (∀ x ∈ support e.1, Vis x) ∧ ∀ x ∈ support e.2, Vis x
  focus : FocusScoped Vis L b.focus
  frames : FramesScoped Vis b.frames Ls
  distinct : (binders L Ls b).Nodup
  apart : ∀ sL ∈ binders L Ls b, ∀ x, Vis x → ¬ Own sL.1 sL.2 x

/-- **An alternative scoped at run time**, for some visible names and levels. -/
def Scoping (n : ℕ) (b : Branch κ Γ star Ty) : Prop :=
  ∃ Vis L Ls, ScopedAt n b Vis L Ls

theorem ScopedAt.mono {n n' : ℕ} {b : Branch κ Γ star Ty} {Vis : Name κ → Prop} {L : List ℕ}
    {Ls : List (List ℕ)} (inv : ScopedAt n b Vis L Ls) (le : n ≤ n') : ScopedAt n' b Vis L Ls :=
  ⟨fun x vis m head => Nat.lt_of_lt_of_le (inv.visibleBelow x vis m head) le, inv.levelBelow.mono le,
    fun L' member => (inv.levelsBelow L' member).mono le, inv.store, inv.focus, inv.frames,
    inv.distinct, inv.apart⟩

theorem FramesScoped.mono {Vis Vis' : Name κ → Prop} (more : ∀ x, Vis x → Vis' x) :
    ∀ {fs : List (SourceLanguage.Frame κ Γ star Ty)} {Ls : List (List ℕ)},
      FramesScoped Vis fs Ls → FramesScoped Vis' fs Ls
  | [], [], _ => trivial
  | .bindTo s _ k :: _, L :: _, ⟨sp, sk, rest⟩ =>
      ⟨fun x member => insideLet_mono s L more (sp x member),
        RScoped_mono k (fun _ inside => insideLet_mono s L more inside) sk, FramesScoped.mono more rest⟩
  | [], _ :: _, within => within.elim
  | .bindTo _ _ _ :: _, [], within => within.elim
  | .checkAt _ :: _, [], within => within.elim
  | .checkAt _ :: _, _ :: _, within => within.elim
  | .memo _ :: _, [], within => within.elim
  | .memo _ :: _, _ :: _, within => within.elim

theorem framesBinders_level : ∀ {fs : List (SourceLanguage.Frame κ Γ star Ty)} {Ls : List (List ℕ)}
    {sL : κ.Site × List ℕ}, sL ∈ framesBinders fs Ls → sL.2 ∈ Ls
  | .bindTo s _ k :: fs, L :: Ls, sL, member => by
      simp only [framesBinders, List.mem_cons, List.mem_append, List.mem_map] at member
      rcases member with rfl | ⟨s', _, rfl⟩ | inner
      · exact List.mem_cons_self ..
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (framesBinders_level inner)
  | [], [], _, member => nomatch member
  | [], _ :: _, _, member => nomatch member
  | .bindTo _ _ _ :: _, [], _, member => nomatch member
  | .checkAt _ :: _, [], _, member => nomatch member
  | .checkAt _ :: _, _ :: _, _, member => nomatch member
  | .memo _ :: _, [], _, member => nomatch member
  | .memo _ :: _, _ :: _, _, member => nomatch member

/-- **Every name of a pending frame** is visible, or an own name of one of the frames' binders. -/
theorem framesScoped_names {Vis : Name κ → Prop} :
    ∀ {fs : List (SourceLanguage.Frame κ Γ star Ty)} {Ls : List (List ℕ)}, FramesScoped Vis fs Ls →
      ∀ fr ∈ fs, ∀ t ∈ frameData fr, ∀ x ∈ support t,
        Vis x ∨ ∃ sL ∈ framesBinders fs Ls, Own sL.1 sL.2 x
  | .bindTo s p k :: fs, L :: Ls, ⟨sp, sk, rest⟩, fr, member, t, inT, x, inX => by
      rcases List.mem_cons.mp member with rfl | inFs
      · simp only [frameData, List.mem_cons] at inT
        rcases inT with rfl | inK
        · rcases sp x inX with ⟨vis, _⟩ | own
          · exact .inl vis
          · exact .inr ⟨(s, L), by simp [framesBinders], own⟩
        · rcases RScoped_names k sk t inK x inX with (⟨vis, _⟩ | own) | ⟨s', member', own⟩
          · exact .inl vis
          · exact .inr ⟨(s, L), by simp [framesBinders], own⟩
          · exact .inr ⟨(s', L), by simp [framesBinders, member'], own⟩
      · rcases framesScoped_names rest fr inFs t inT x inX with vis | ⟨sL, inner, own⟩
        · exact .inl vis
        · exact .inr ⟨sL, by simp [framesBinders, inner], own⟩
  | [], [], _, _, member, _, _, _, _ => nomatch member
  | [], _ :: _, within, _, _, _, _, _, _ => within.elim
  | .bindTo _ _ _ :: _, [], within, _, _, _, _, _, _ => within.elim
  | .checkAt _ :: _, [], within, _, _, _, _, _, _ => within.elim
  | .checkAt _ :: _, _ :: _, within, _, _, _, _, _, _ => within.elim
  | .memo _ :: _, [], within, _, _, _, _, _, _ => within.elim
  | .memo _ :: _, _ :: _, within, _, _, _, _, _, _ => within.elim

/-! ## Hygiene from the invariant -/

/-- **A scoped alternative is hygienic.** -/
theorem hygienic_of_scopedAt {n : ℕ} {b : Branch κ Γ star Ty} {Vis : Name κ → Prop} {L : List ℕ}
    {Ls : List (List ℕ)} (inv : ScopedAt n b Vis L Ls) : Hygienic b := by
  intro K v s p k fs ps same
  subst same
  rcases Ls with _ | ⟨L₁, Ls₁⟩
  · exact inv.frames.elim
  obtain ⟨patternIn, bodyIn, restIn⟩ := inv.frames
  have binderList : binders L (L₁ :: Ls₁) ⟨K, .value v, .bindTo s p k :: fs, ps⟩ =
      (s, L₁) :: (k.sites.map (·, L₁) ++ framesBinders fs Ls₁) := rfl
  have whole := inv.distinct
  rw [binderList] at whole
  have notInside : s ∉ k.sites := fun inK =>
    (List.nodup_cons.mp whole).1 (List.mem_append_left _ (List.mem_map.mpr ⟨s, inK, rfl⟩))
  have ownAt : ∀ x, OwnName s p k x → Own s L₁ x := by
    rintro x ⟨site, inP | ⟨t, inK, inT⟩⟩
    · exact insideLet_same (patternIn x inP) site
    · rcases RScoped_names k bodyIn t inK x inT with inside | ⟨s', member, own⟩
      · exact insideLet_same inside site
      · have same : s' = s := own.1.symm.trans site
        exact absurd (same ▸ member) notInside
  have hidden : ∀ x, Vis x → ¬ Own s L₁ x :=
    inv.apart (s, L₁) (by rw [binderList]; exact List.mem_cons_self ..)
  have otherFrames : ∀ x, (∃ sL ∈ framesBinders fs Ls₁, Own sL.1 sL.2 x) → ¬ Own s L₁ x := by
    rintro x ⟨sL, member, own⟩ ownHere
    have sameSite : sL.1 = s := own.1.symm.trans ownHere.1
    have sameLevel : sL.2 = L₁ := own.2.symm.trans ownHere.2
    have again : (s, L₁) ∈ framesBinders fs Ls₁ := by
      rw [← sameSite, ← sameLevel]
      exact member
    exact (List.nodup_cons.mp whole).1 (List.mem_append_right _ again)
  intro W target σ σ' agree
  have agreeOn : ∀ x, ¬ Own s L₁ x → σ x = σ' x := fun x notOwn => agree x (fun own => notOwn (ownAt x own))
  refine ⟨?_, ?_, ?_⟩
  · intro e member
    exact ⟨instantiate_congr σ σ' e.1 (fun x h => agreeOn x (hidden x ((inv.store e member).1 x h))),
      instantiate_congr σ σ' e.2 (fun x h => agreeOn x (hidden x ((inv.store e member).2 x h)))⟩
  · exact instantiate_congr σ σ' v (fun x h => agreeOn x (hidden x (inv.focus x h)))
  · intro fr member t inT
    apply instantiate_congr σ σ' t
    intro x inX
    apply agreeOn x
    rcases framesScoped_names restIn fr member t inT x inX with vis | other
    · exact hidden x vis
    · exact otherFrames x other

/-! ## The start -/

/-- **The start is scoped**: the query's names are its own site's, unopened; its binders are at the
level `[]`. -/
theorem scopedAt_initial {qsite : κ.Site} {q : Comp κ Γ star Ty} (arrowQ : ArrowComp q)
    (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup) :
    ScopedAt 0 ⟨[], .eval q, [], []⟩ (Own qsite []) [] [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial, ?_, ?_⟩
  · intro x own m head
    rw [own.2] at head
    exact absurd head (by simp)
  · intro m head
    exact absurd head (by simp)
  · intro L' member
    exact absurd member (by simp)
  · intro e member
    exact absurd member (by simp)
  · exact RScoped_mono q (fun x named => ⟨List.mem_singleton.mp named.2, named.1⟩)
      (RScoped_text q [qsite] arrowQ qScoped
        ((List.perm_append_singleton qsite q.sites).nodup_iff.mpr qDistinct))
  · show (q.sites.map (·, ([] : List ℕ)) ++ []).Nodup
    rw [List.append_nil]
    exact (List.nodup_cons.mp qDistinct).2.map (fun a b same => congrArg Prod.fst same)
  · intro sL member x own ownThere
    change sL ∈ q.sites.map (·, ([] : List ℕ)) ++ [] at member
    rw [List.append_nil] at member
    obtain ⟨s', inQ, rfl⟩ := List.mem_map.mp member
    have same : qsite = s' := own.1.symm.trans ownThere.1
    exact (List.nodup_cons.mp qDistinct).1 (same ▸ inQ)

/-- The names of a scoped query are unopened. -/
theorem query_unopened {qsite : κ.Site} {q : Comp κ Γ star Ty} (qScoped : q.Scoped [qsite])
    (qDistinct : (qsite :: q.sites).Nodup) (arrowQ : ArrowComp q) :
    ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  rcases RScoped_names q (RScoped_text q [qsite] arrowQ qScoped
      ((List.perm_append_singleton qsite q.sites).nodup_iff.mpr qDistinct)) t member x inside with
    ⟨scope, _⟩ | ⟨_, _, own⟩
  · exact scope
  · exact own.2

end Invariant

/-! ## Preservation -/

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **Every move of a scoped alternative makes scoped alternatives**, for a program whose equations
are scoped, with distinct binder sites, of the fragment with arrows. -/
theorem scopedAt_children
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (move : Move D P supply w b w' bs) {Vis : Name κ → Prop} {L : List ℕ} {Ls : List (List ℕ)}
    (inv : ScopedAt w.scope b Vis L Ls) : ∀ b' ∈ bs, Scoping w'.scope b' := by
  intro b' child
  cases move
  case ret K t fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    exact ⟨Vis, L, Ls, inv.visibleBelow, inv.levelBelow, inv.levelsBelow, inv.store, inv.focus,
      inv.frames, inv.distinct, inv.apart⟩
  case unmatched K t fs ps _ =>
    rw [Multiset.mem_singleton] at child
    subst child
    exact ⟨Vis, L, Ls, inv.visibleBelow, inv.levelBelow, inv.levelsBelow, inv.store, inv.focus,
      inv.frames, inv.distinct, inv.apart⟩
  case apply K t fs ps _ =>
    obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp child)
    obtain ⟨within, distinctE, arrowE⟩ := equations e eMember
    have tVisible : ∀ x ∈ support t, Vis x := inv.focus
    have framesNodup : (framesBinders fs Ls).Nodup := inv.distinct
    have framesApart : ∀ sL ∈ framesBinders fs Ls, ∀ x, Vis x → ¬ Own sL.1 sL.2 x := inv.apart
    have eSite : e.site ∉ e.rhs.sites := (List.nodup_cons.mp distinctE).1
    have focusList : binders [w.scope] Ls (callBranch D w.scope K t fs ps e) =
        e.rhs.sites.map (·, [w.scope]) ++ framesBinders fs Ls := by
      simp only [binders, callBranch, focusBinders, Comp.inst, sites_mapData]
    refine ⟨fun x => Vis x ∨ Own e.site [w.scope] x, [w.scope], Ls, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro x (vis | ⟨_, scope⟩) m head
      · exact Nat.lt_succ_of_lt (inv.visibleBelow x vis m head)
      · rw [scope] at head
        simp only [List.head?_cons, Option.some.injEq] at head
        subst head
        exact Nat.lt_succ_self _
    · intro m head
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      exact Nat.lt_succ_self _
    · exact fun L' member => (inv.levelsBelow L' member).mono (Nat.le_succ _)
    · intro c member
      rcases List.mem_append.mp member with old | new
      · exact ⟨fun x h => .inl ((inv.store c old).1 x h), fun x h => .inl ((inv.store c old).2 x h)⟩
      · rw [List.mem_singleton.mp new]
        exact ⟨fun x h => .inr (support_copy_lhs e w.scope within x h), fun x h => .inl (tVisible x h)⟩
    · exact RScoped_mono _ (fun x own => .inr own) (RScoped_copy e w.scope arrowE within distinctE)
    · exact FramesScoped.mono (fun x vis => .inl vis) inv.frames
    · rw [focusList]
      refine List.nodup_append.mpr ⟨(List.nodup_cons.mp distinctE).2.map
        (fun a b same => congrArg Prod.fst same), framesNodup, ?_⟩
      intro a aMember c cMember same
      obtain ⟨s', _, rfl⟩ := List.mem_map.mp aMember
      have level := inv.levelsBelow c.2 (framesBinders_level cMember)
      exact level.ne_cons [] (congrArg Prod.snd same).symm
    · intro sL member x visible own
      rw [focusList] at member
      rcases List.mem_append.mp member with inFocus | inFrames
      · obtain ⟨s', s'Member, rfl⟩ := List.mem_map.mp inFocus
        rcases visible with vis | ⟨site, _⟩
        · have below := inv.visibleBelow x vis w.scope (by rw [own.2]; rfl)
          exact Nat.lt_irrefl _ below
        · have same : s' = e.site := own.1.symm.trans site
          exact eSite (same ▸ s'Member)
      · rcases visible with vis | ⟨_, scope⟩
        · exact framesApart sL inFrames x vis own
        · have level := inv.levelsBelow sL.2 (framesBinders_level inFrames)
          exact level.ne_cons [] (own.2.symm.trans scope)
  case letStart K s p c k fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨cIn, pIn, kIn⟩ := inv.focus
    have perm : List.Perm (binders L (L :: Ls) ⟨K, .eval c, .bindTo s p k :: fs, ps⟩)
        (binders L Ls ⟨K, .eval (.let_ s p c k), fs, ps⟩) := by
      simp only [binders, focusBinders, framesBinders, Comp.sites, List.map_cons, List.map_append,
        List.cons_append, List.append_assoc]
      exact List.perm_middle
    exact ⟨Vis, L, L :: Ls, inv.visibleBelow, inv.levelBelow,
      List.forall_mem_cons.mpr ⟨inv.levelBelow, inv.levelsBelow⟩, inv.store, cIn, ⟨pIn, kIn, inv.frames⟩,
      perm.nodup_iff.mpr inv.distinct, fun sL member => inv.apart sL (perm.subset member)⟩
  case letBind K v s p k fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    rcases Ls with _ | ⟨L₁, Ls₁⟩
    · exact inv.frames.elim
    obtain ⟨pIn, kIn, restIn⟩ := inv.frames
    have vVisible : ∀ x ∈ support v, Vis x := inv.focus
    have binderList : binders L (L₁ :: Ls₁) ⟨K, .value v, .bindTo s p k :: fs, ps⟩ =
        (s, L₁) :: (k.sites.map (·, L₁) ++ framesBinders fs Ls₁) := rfl
    have whole := inv.distinct
    rw [binderList] at whole
    have notInside : s ∉ k.sites := fun inK =>
      (List.nodup_cons.mp whole).1 (List.mem_append_left _ (List.mem_map.mpr ⟨s, inK, rfl⟩))
    have levelOne : LevelBelow w.scope L₁ := inv.levelsBelow L₁ (List.mem_cons_self ..)
    have focusList : binders L₁ Ls₁
        ⟨K ++ [(instantiate (openAt κ s w.scope) p, v)], .eval (k.inst (openAt κ s w.scope)), fs, ps⟩ =
        k.sites.map (·, L₁) ++ framesBinders fs Ls₁ := by
      simp only [binders, focusBinders, Comp.inst, sites_mapData]
    refine ⟨fun x => Vis x ∨ Own s (w.scope :: L₁) x, L₁, Ls₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro x (vis | ⟨_, scope⟩) m head
      · exact Nat.lt_succ_of_lt (inv.visibleBelow x vis m head)
      · rw [scope] at head
        simp only [List.head?_cons, Option.some.injEq] at head
        subst head
        exact Nat.lt_succ_self _
    · exact levelOne.mono (Nat.le_succ _)
    · exact fun L' member => (inv.levelsBelow L' (List.mem_cons_of_mem _ member)).mono (Nat.le_succ _)
    · intro c member
      rcases List.mem_append.mp member with old | new
      · exact ⟨fun x h => .inl ((inv.store c old).1 x h), fun x h => .inl ((inv.store c old).2 x h)⟩
      · rw [List.mem_singleton.mp new]
        exact ⟨support_open_pattern w.scope pIn, fun x h => .inl (vVisible x h)⟩
    · exact RScoped_open w.scope kIn notInside
    · exact FramesScoped.mono (fun x vis => .inl vis) restIn
    · rw [focusList]
      exact (List.nodup_cons.mp whole).2
    · intro sL member x visible own
      rw [focusList] at member
      rcases visible with vis | ⟨_, scope⟩
      · exact inv.apart sL (by rw [binderList]; exact List.mem_cons_of_mem _ member) x vis own
      · have level : LevelBelow w.scope sL.2 := by
          rcases List.mem_append.mp member with inK | inFrames
          · obtain ⟨s', _, rfl⟩ := List.mem_map.mp inK
            exact levelOne
          · exact inv.levelsBelow sL.2 (List.mem_cons_of_mem _ (framesBinders_level inFrames))
        exact level.ne_cons L₁ (own.2.symm.trans scope)
  case choice K c d fs ps =>
    obtain ⟨cIn, dIn⟩ := inv.focus
    have subC : List.Sublist (binders L Ls ⟨K, .eval c, fs, ps⟩)
        (binders L Ls ⟨K, .eval (.choice c d), fs, ps⟩) := by
      simp only [binders, focusBinders, Comp.sites, List.map_append]
      exact (List.sublist_append_left _ _).append_right _
    have subD : List.Sublist (binders L Ls ⟨K, .eval d, fs, ps⟩)
        (binders L Ls ⟨K, .eval (.choice c d), fs, ps⟩) := by
      simp only [binders, focusBinders, Comp.sites, List.map_append]
      exact (List.sublist_append_right _ _).append_right _
    rcases Multiset.mem_cons.mp child with rfl | other
    · exact ⟨Vis, L, Ls, inv.visibleBelow, inv.levelBelow, inv.levelsBelow, inv.store, cIn, inv.frames,
        inv.distinct.sublist subC, fun sL member => inv.apart sL (subC.subset member)⟩
    · rw [Multiset.mem_singleton] at other
      subst other
      exact ⟨Vis, L, Ls, inv.visibleBelow, inv.levelBelow, inv.levelsBelow, inv.store, dIn, inv.frames,
        inv.distinct.sublist subD, fun sL member => inv.apart sL (subD.subset member)⟩
  case fail K fs ps =>
    exact absurd child (Multiset.notMem_zero _)
  all_goals first
    | exact False.elim inv.focus
    | (rcases Ls with _ | ⟨_, _⟩ <;> exact False.elim inv.frames)

/-! ## Every run -/

variable (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **Every alternative of every configuration a run reaches is scoped.** -/
theorem scoping_reachable
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) :
    ∀ C, Runs D P supply (Config.initial spaces q) C → ∀ b ∈ C.branches, Scoping C.world.scope b := by
  intro C runs
  induction runs with
  | refl =>
      intro b member
      rw [Multiset.mem_singleton.mp member]
      exact ⟨_, _, _, scopedAt_initial arrowQ qScoped qDistinct⟩
  | tail _ step ih =>
      obtain ⟨w, w', b₀, rest, bs, _, move⟩ := step
      intro b member
      rcases Multiset.mem_add.mp member with made | kept
      · obtain ⟨Vis, L, Ls, inv⟩ := ih b₀ (Multiset.mem_cons_self _ _)
        exact scopedAt_children equations move inv b made
      · obtain ⟨Vis, L, Ls, inv⟩ := ih b (Multiset.mem_cons_of_mem kept)
        exact ⟨Vis, L, Ls, inv.mono (Move.scope_le move)⟩

/-- **The hygiene lemma**, with exactly the clauses of well-formedness it uses. -/
theorem reachableHygienic_of_scoped
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) : ReachableHygienic spaces q P supply := by
  intro C runs b member
  obtain ⟨Vis, L, Ls, inv⟩ := scoping_reachable spaces q equations qScoped qDistinct arrowQ C runs b member
  exact hygienic_of_scopedAt inv

variable [DecidableEq κ.Key]

/-- What well-formedness gives each equation. -/
theorem equations_of_wellFormed (wf : WellFormed P) (arrowP : ArrowProgram P) :
    ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs :=
  fun e member => ⟨wf.inScope e member,
    (List.nodup_flatMap.mp (wf.distinctSites : (P.equations.flatMap fun e => e.site :: e.rhs.sites).Nodup)).1
      e member, arrowP e member⟩

/-- **The hygiene lemma for well-formed programs and queries with arrows.** -/
theorem reachableHygienic_of_wellFormed (wf : WellFormed P) (arrowP : ArrowProgram P) {qsite : κ.Site}
    (qwf : QueryWellFormed P qsite q) (arrowQ : ArrowComp q) : ReachableHygienic spaces q P supply :=
  reachableHygienic_of_scoped spaces q (equations_of_wellFormed wf arrowP) qwf.inScope
    (qwf.distinctSites.sublist (List.sublist_append_left _ _)) arrowQ

#print axioms hygienic_of_scopedAt
#print axioms scopedAt_children
#print axioms scoping_reachable
#print axioms reachableHygienic_of_scoped
#print axioms reachableHygienic_of_wellFormed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
