import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics

/-!
# Adding an equation whose head is only held as data changes no answer

**The condition** (`callsApart e c`, syntactic up to the separation of two data, and **sufficient,
not necessary**): every datum the program calls is *separated* from the new equation `e` (no instance
of it is an instance of a copy of `e`'s left-hand side, `Separated`), and the program never reads text
as code: `callsApart` excludes **every** `run`, whatever its text holds. For MeTTa text, separation
holds when the head of the call is a symbol other than `e`'s head
(`ExampleExtension.separated_of_heads`): `e`'s head may occur anywhere in held data, as long as the
program runs no text. A program that runs text not holding `e`'s head is outside the condition and can
still keep its bag (`ExampleExtensionApplied.condition_not_necessary`). The law applies to non-empty
programs (`ExampleExtensionApplied.law_applied`).

**The law** (`extension_forward`, `extension_backward`, `answers_related`): under the condition, the
runs of the program with `e` and the runs of the program without it correspond step for step,
configurations differing only by dead alternatives (the branches `e` makes, whose stores are
unsolvable), and related configurations have the same bag of answers.

**The control** (where the text is held as code) is in `ExampleExtension`: a program that runs held
text whose head is `e`'s head has a different bag with `e` than without it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Extension

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {D : Discipline S Γ star}

/-- No instance of `t` is an instance of a copy of `e`'s left-hand side. -/
def Separated (e : Equation κ Γ star D.Ty) (t : Data κ Γ star) : Prop :=
  ∀ (n : ℕ) {X : Type} (target : X → MetaArity S) (σ σ' : Assignment (fam κ) target),
    instantiate σ t ≠ instantiate σ' (instantiate (copyAt κ n) e.lhs)

theorem Separated.inst {e : Equation κ Γ star D.Ty} {t : Data κ Γ star} (apart : Separated e t)
    (ρ : Assignment (fam κ) (fam κ)) : Separated e (instantiate ρ t) := by
  intro n X target σ σ' same
  rw [← Assignment.instantiate_compose] at same
  exact apart n target _ σ' same

/-- **The condition**: the computation calls only data separated from `e`, and runs no text. -/
def callsApart (e : Equation κ Γ star D.Ty) : Comp κ Γ star D.Ty → Prop
  | .ret _ => True
  | .apply t => Separated e t
  | .run _ => False
  | .let_ _ _ c k => callsApart e c ∧ callsApart e k
  | .choice c d => callsApart e c ∧ callsApart e d
  | .fail => True
  | .query _ _ k => callsApart e k
  | .add _ _ k => callsApart e k
  | .remove _ _ k => callsApart e k
  | .new _ _ k => callsApart e k
  | .check _ k => callsApart e k
  | .delay _ _ c k => callsApart e c ∧ callsApart e k
  | .force _ => True

theorem callsApart_inst {e : Equation κ Γ star D.Ty} (ρ : Assignment (fam κ) (fam κ)) :
    (c : Comp κ Γ star D.Ty) → callsApart e c → callsApart e (c.inst ρ)
  | .ret _, _ => trivial
  | .apply _, apart => Separated.inst apart ρ
  | .run _, apart => apart
  | .let_ _ _ c k, ⟨hc, hk⟩ => ⟨callsApart_inst ρ c hc, callsApart_inst ρ k hk⟩
  | .choice c d, ⟨hc, hd⟩ => ⟨callsApart_inst ρ c hc, callsApart_inst ρ d hd⟩
  | .fail, _ => trivial
  | .query _ _ k, hk => callsApart_inst ρ k hk
  | .add _ _ k, hk => callsApart_inst ρ k hk
  | .remove _ _ k, hk => callsApart_inst ρ k hk
  | .new _ _ k, hk => callsApart_inst ρ k hk
  | .check _ k, hk => callsApart_inst ρ k hk
  | .delay _ _ c k, ⟨hc, hk⟩ => ⟨callsApart_inst ρ c hc, callsApart_inst ρ k hk⟩
  | .force _, _ => trivial

/-- Every computation an alternative holds calls apart from `e`. -/
def BranchApart (e : Equation κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) : Prop :=
  (∀ c, b.focus = .eval c → callsApart e c) ∧
    (∀ s p k, Frame.bindTo s p k ∈ b.frames → callsApart e k) ∧
    (∀ entry ∈ b.pending, callsApart e entry.2)

variable (supply : ℕ → Term S Γ star)

/-- The program with `e` added. -/
def extend (P : Program κ Γ star D.Ty) (e : Equation κ Γ star D.Ty) : Program κ Γ star D.Ty :=
  ⟨P.equations ++ [e], P.reflect⟩

theorem dead_new {e : Equation κ Γ star D.Ty} {t : Data κ Γ star} (apart : Separated e t) (n : ℕ)
    (K : List (Constraint κ Γ star)) : ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)]) := by
  rintro ⟨X, target, σ, solved⟩
  have same := ((models_append σ K _).mp solved).2 _ (List.mem_singleton_self _)
  exact apart n target σ σ same.symm

/-! ## The moves of the two programs -/

/-- **A move with `e` is a move without it, up to `e`'s dead alternative.** -/
theorem move_without {P : Program κ Γ star D.Ty} {e : Equation κ Γ star D.Ty}
    {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (apartB : BranchApart e b) (moved : Move D (extend P e) supply w b w' bs) :
    ∃ bs₀ dead, bs = bs₀ + dead ∧ (∀ d ∈ dead, ¬ Solvable d.store) ∧ Move D P supply w b w' bs₀ := by
  cases moved with
  | apply K t fs ps matched =>
      have apart : Separated e t := apartB.1 _ rfl
      refine ⟨_, {callBranch D w.scope K t fs ps e}, ?_, ?_, .apply _ _ _ _ _ ?_⟩
      · simp only [extend, List.map_append, List.map_cons, List.map_nil]
        rw [← Multiset.coe_singleton, Multiset.coe_add]
      · intro d member
        rw [Multiset.mem_singleton.mp member]
        exact dead_new apart w.scope K
      · obtain ⟨e', member, live⟩ := matched
        rcases List.mem_append.mp member with old | new
        · exact ⟨e', old, live⟩
        · rw [List.mem_singleton.mp new] at live
          exact absurd live (dead_new apart w.scope K)
  | unmatched K t fs ps none =>
      exact ⟨_, 0, (add_zero _).symm, by simp,
        .unmatched _ _ _ _ _ (fun e' member => none e' (List.mem_append_left _ member))⟩
  | run K t fs ps θ principal => exact absurd (apartB.1 _ rfl) (by simp [callsApart])
  | ret => exact ⟨_, 0, (add_zero _).symm, by simp, .ret _ _ _ _ _⟩
  | letStart => exact ⟨_, 0, (add_zero _).symm, by simp, .letStart _ _ _ _ _ _ _ _⟩
  | letBind => exact ⟨_, 0, (add_zero _).symm, by simp, .letBind _ _ _ _ _ _ _ _⟩
  | choice => exact ⟨_, 0, (add_zero _).symm, by simp, .choice _ _ _ _ _ _⟩
  | fail => exact ⟨_, 0, (add_zero _).symm, by simp, .fail _ _ _ _⟩
  | query K sp p k fs ps h addressed =>
      exact ⟨_, 0, (add_zero _).symm, by simp, .query _ _ _ _ _ _ _ h addressed⟩
  | add K sp t k fs ps h addressed => exact ⟨_, 0, (add_zero _).symm, by simp, .add _ _ _ _ _ _ _ h addressed⟩
  | remove K sp t k fs ps h addressed r rest split fits =>
      exact ⟨_, 0, (add_zero _).symm, by simp, .remove _ _ _ _ _ _ _ h addressed r rest split fits⟩
  | removeMissing K sp t k fs ps h addressed none =>
      exact ⟨_, 0, (add_zero _).symm, by simp, .removeMissing _ _ _ _ _ _ _ h addressed none⟩
  | new => exact ⟨_, 0, (add_zero _).symm, by simp, .new _ _ _ _ _ _ _⟩
  | checkStart => exact ⟨_, 0, (add_zero _).symm, by simp, .checkStart _ _ _ _ _ _⟩
  | admitted K v T fs ps all => exact ⟨_, 0, (add_zero _).symm, by simp, .admitted _ _ _ _ _ _ all⟩
  | refused K v T fs ps none => exact ⟨_, 0, (add_zero _).symm, by simp, .refused _ _ _ _ _ _ none⟩
  | delay => exact ⟨_, 0, (add_zero _).symm, by simp, .delay _ _ _ _ _ _ _ _⟩
  | forcePending K x cell c fs before after bound =>
      exact ⟨_, 0, (add_zero _).symm, by simp, .forcePending _ _ _ _ _ _ _ _ bound⟩
  | forceDone K x fs ps none => exact ⟨_, 0, (add_zero _).symm, by simp, .forceDone _ _ _ _ _ none⟩
  | memo => exact ⟨_, 0, (add_zero _).symm, by simp, .memo _ _ _ _ _ _⟩

/-- **A move without `e` is a move with it, up to `e`'s dead alternative.** -/
theorem move_with {P : Program κ Γ star D.Ty} {e : Equation κ Γ star D.Ty}
    {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (apartB : BranchApart e b) (moved : Move D P supply w b w' bs) :
    ∃ dead, (∀ d ∈ dead, ¬ Solvable d.store) ∧ Move D (extend P e) supply w b w' (bs + dead) := by
  cases moved with
  | apply K t fs ps matched =>
      have apart : Separated e t := apartB.1 _ rfl
      refine ⟨{callBranch D w.scope K t fs ps e}, ?_, ?_⟩
      · intro d member
        rw [Multiset.mem_singleton.mp member]
        exact dead_new apart w.scope K
      · have bag : ((P.equations.map (callBranch D w.scope K t fs ps) : List _) : Multiset _) +
            {callBranch D w.scope K t fs ps e} =
            (((extend P e).equations.map (callBranch D w.scope K t fs ps) : List _) : Multiset _) := by
          simp only [extend, List.map_append, List.map_cons, List.map_nil]
          rw [← Multiset.coe_singleton, Multiset.coe_add]
        rw [bag]
        obtain ⟨e', member, live⟩ := matched
        exact .apply _ _ _ _ _ ⟨e', List.mem_append_left _ member, live⟩
  | unmatched K t fs ps none =>
      have apart : Separated e t := apartB.1 _ rfl
      refine ⟨0, by simp, ?_⟩
      rw [add_zero]
      refine .unmatched _ _ _ _ _ (fun e' member => ?_)
      rcases List.mem_append.mp member with old | new
      · exact none e' old
      · rw [List.mem_singleton.mp new]
        exact dead_new apart w.scope K
  | run K t fs ps θ principal => exact absurd (apartB.1 _ rfl) (by simp [callsApart])
  | ret => exact ⟨0, by simp, by rw [add_zero]; exact .ret _ _ _ _ _⟩
  | letStart => exact ⟨0, by simp, by rw [add_zero]; exact .letStart _ _ _ _ _ _ _ _⟩
  | letBind => exact ⟨0, by simp, by rw [add_zero]; exact .letBind _ _ _ _ _ _ _ _⟩
  | choice => exact ⟨0, by simp, by rw [add_zero]; exact .choice _ _ _ _ _ _⟩
  | fail => exact ⟨0, by simp, by rw [add_zero]; exact .fail _ _ _ _⟩
  | query K sp p k fs ps h addressed =>
      exact ⟨0, by simp, by rw [add_zero]; exact .query _ _ _ _ _ _ _ h addressed⟩
  | add K sp t k fs ps h addressed =>
      exact ⟨0, by simp, by rw [add_zero]; exact .add _ _ _ _ _ _ _ h addressed⟩
  | remove K sp t k fs ps h addressed r rest split fits =>
      exact ⟨0, by simp, by rw [add_zero]; exact .remove _ _ _ _ _ _ _ h addressed r rest split fits⟩
  | removeMissing K sp t k fs ps h addressed none =>
      exact ⟨0, by simp, by rw [add_zero]; exact .removeMissing _ _ _ _ _ _ _ h addressed none⟩
  | new => exact ⟨0, by simp, by rw [add_zero]; exact .new _ _ _ _ _ _ _⟩
  | checkStart => exact ⟨0, by simp, by rw [add_zero]; exact .checkStart _ _ _ _ _ _⟩
  | admitted K v T fs ps all => exact ⟨0, by simp, by rw [add_zero]; exact .admitted _ _ _ _ _ _ all⟩
  | refused K v T fs ps none => exact ⟨0, by simp, by rw [add_zero]; exact .refused _ _ _ _ _ _ none⟩
  | delay => exact ⟨0, by simp, by rw [add_zero]; exact .delay _ _ _ _ _ _ _ _⟩
  | forcePending K x cell c fs before after bound =>
      exact ⟨0, by simp, by rw [add_zero]; exact .forcePending _ _ _ _ _ _ _ _ bound⟩
  | forceDone K x fs ps none => exact ⟨0, by simp, by rw [add_zero]; exact .forceDone _ _ _ _ _ none⟩
  | memo => exact ⟨0, by simp, by rw [add_zero]; exact .memo _ _ _ _ _ _⟩

/-! ## The condition is kept along moves -/

/-- The program's equations call apart from `e`. -/
def ProgramApart (P : Program κ Γ star D.Ty) (e : Equation κ Γ star D.Ty) : Prop :=
  ∀ e' ∈ P.equations, callsApart e e'.rhs

theorem move_keeps {P : Program κ Γ star D.Ty} {e : Equation κ Γ star D.Ty} (program : ProgramApart P e)
    {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (apartB : BranchApart e b) (moved : Move D P supply w b w' bs) : ∀ b' ∈ bs, BranchApart e b' := by
  obtain ⟨focus, frames, pending⟩ := apartB
  cases moved with
  | ret => intro b' member; rw [Multiset.mem_singleton.mp member]; exact ⟨by simp, frames, pending⟩
  | apply K t fs ps matched =>
      intro b' member
      obtain ⟨e', _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      refine ⟨fun c same => ?_, frames, pending⟩
      simp only [callBranch, Focus.eval.injEq] at same
      subst same
      exact callsApart_inst _ e'.rhs (program e' (by assumption))
  | unmatched => intro b' member; rw [Multiset.mem_singleton.mp member]; exact ⟨by simp, frames, pending⟩
  | run => exact absurd (focus _ rfl) (by simp [callsApart])
  | letStart K s p c k fs ps =>
      intro b' member
      rw [Multiset.mem_singleton.mp member]
      have both := focus _ rfl
      refine ⟨fun c' same => ?_, fun s' p' k' member' => ?_, pending⟩
      · simp only [Focus.eval.injEq] at same; subst same; exact both.1
      · rcases List.mem_cons.mp member' with head | tail
        · simp only [Frame.bindTo.injEq] at head; obtain ⟨_, _, rfl⟩ := head; exact both.2
        · exact frames _ _ _ tail
  | letBind K v s p k fs ps =>
      intro b' member
      rw [Multiset.mem_singleton.mp member]
      refine ⟨fun c' same => ?_, fun s' p' k' member' => frames _ _ _ (List.mem_cons_of_mem _ member'), pending⟩
      simp only [Focus.eval.injEq] at same; subst same
      exact callsApart_inst _ k (frames s p k (List.mem_cons.mpr (Or.inl rfl)))
  | choice K c d fs ps =>
      intro b' member
      have both := focus _ rfl
      rcases Multiset.mem_cons.mp member with first | second
      · rw [first]; exact ⟨fun c' same => by simp only [Focus.eval.injEq] at same; subst same; exact both.1,
          frames, pending⟩
      · rw [Multiset.mem_singleton.mp second]
        exact ⟨fun c' same => by simp only [Focus.eval.injEq] at same; subst same; exact both.2, frames, pending⟩
  | fail => intro b' member; cases member
  | query K sp p k fs ps h addressed =>
      intro b' member
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp member
      exact ⟨fun c' same => by
        simp only [Focus.eval.injEq] at same; subst same; exact focus (.query sp p k) rfl, frames, pending⟩
  | add K sp t k fs ps h addressed =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      exact ⟨fun c' same => by
        simp only [Focus.eval.injEq] at same; subst same; exact focus (.add sp t k) rfl, frames, pending⟩
  | remove K sp t k fs ps h addressed r rest split fits =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      exact ⟨fun c' same => by
        simp only [Focus.eval.injEq] at same; subst same; exact focus (.remove sp t k) rfl, frames, pending⟩
  | removeMissing K sp t k fs ps h addressed none =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      exact ⟨fun c' same => by
        simp only [Focus.eval.injEq] at same; subst same; exact focus (.remove sp t k) rfl, frames, pending⟩
  | new K s x k fs ps =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      exact ⟨fun c' same => by
        simp only [Focus.eval.injEq] at same; subst same
        exact callsApart_inst _ k (focus (.new s x k) rfl), frames, pending⟩
  | checkStart K T c fs ps =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      refine ⟨fun c' same => by
          simp only [Focus.eval.injEq] at same; subst same; exact focus (.check T c) rfl,
        fun s' p' k' member' => ?_, pending⟩
      rcases List.mem_cons.mp member' with head | tail
      · cases head
      · exact frames _ _ _ tail
  | admitted K v T fs ps all =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      exact ⟨by simp, fun s' p' k' member' => frames _ _ _ (List.mem_cons_of_mem _ member'), pending⟩
  | refused K v T fs ps none =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      exact ⟨by simp, fun s' p' k' member' => (by cases member'), pending⟩
  | delay K s x c k fs ps =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      have both := focus _ rfl
      refine ⟨fun c' same => by
        simp only [Focus.eval.injEq] at same; subst same; exact callsApart_inst _ k both.2, frames, ?_⟩
      intro entry member'
      rcases List.mem_cons.mp member' with head | tail
      · rw [head]; exact both.1
      · exact pending _ tail
  | forcePending K x cell c fs before after bound =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      refine ⟨fun c' same => ?_, fun s' p' k' member' => ?_, fun entry member' => ?_⟩
      · simp only [Focus.eval.injEq] at same; subst same
        exact pending (cell, c) (List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl)))
      · rcases List.mem_cons.mp member' with head | tail
        · cases head
        · exact frames _ _ _ tail
      · rcases List.mem_append.mp member' with left | right
        · exact pending _ (List.mem_append_left _ left)
        · exact pending _ (List.mem_append_right _ (List.mem_cons_of_mem _ right))
  | forceDone K x fs ps none =>
      intro b' member; rw [Multiset.mem_singleton.mp member]; exact ⟨by simp, frames, pending⟩
  | memo K v x fs ps =>
      intro b' member; rw [Multiset.mem_singleton.mp member]
      exact ⟨by simp, fun s' p' k' member' => frames _ _ _ (List.mem_cons_of_mem _ member'), pending⟩

/-! ## Runs and answers -/

/-- Two configurations related by `e`: same world; the one with `e` has extra dead alternatives; every
live computation calls apart from `e`. -/
def Related (e : Equation κ Γ star D.Ty) (C' C : Config κ Γ star D.Ty) : Prop :=
  C'.world = C.world ∧ (∃ dead, C'.branches = C.branches + dead ∧ ∀ d ∈ dead, ¬ Solvable d.store) ∧
    ∀ b ∈ C.branches, BranchApart e b

/-- **Forward**: a run with `e` is followed by a run without it. -/
theorem extension_forward {P : Program κ Γ star D.Ty} {e : Equation κ Γ star D.Ty} (program : ProgramApart P e)
    {C₁ C₂ : Config κ Γ star D.Ty} (runs : Runs D (extend P e) supply C₁ C₂) {C : Config κ Γ star D.Ty}
    (related : Related e C₁ C) : ∃ C', Runs D P supply C C' ∧ Related e C₂ C' := by
  induction runs with
  | refl => exact ⟨C, .refl, related⟩
  | tail _ step ih =>
      obtain ⟨Cm, path, world, ⟨dead, split, deadDead⟩, apart⟩ := ih
      cases step with
      | move w w' b rest bs live moved =>
          have split' : b ::ₘ rest = Cm.branches + dead := split
          have world' : w = Cm.world := world
          -- the moving alternative is live, so it is not dead: it is one of `Cm`'s
          have inCm : b ∈ Cm.branches := by
            have : b ∈ Cm.branches + dead := by rw [← split']; exact Multiset.mem_cons_self _ _
            rcases Multiset.mem_add.mp this with old | gone
            · exact old
            · exact absurd live (deadDead b gone)
          obtain ⟨restCm, splitCm⟩ := Multiset.exists_cons_of_mem inCm
          obtain ⟨bs₀, dead₀, bag, deadNew, movedP⟩ := move_without supply (apart b inCm) moved
          refine ⟨⟨w', bs₀ + restCm⟩, path.tail (Step.of_eq (w := Cm.world) splitCm rfl live
            (world' ▸ movedP)), rfl, ⟨dead₀ + dead, ?_, ?_⟩, ?_⟩
          · have restSplit : rest = restCm + dead := by
              have eq1 : b ::ₘ rest = b ::ₘ (restCm + dead) := by
                rw [split', splitCm, Multiset.cons_add]
              exact Multiset.cons_inj_right b |>.mp eq1
            show bs + rest = bs₀ + restCm + (dead₀ + dead)
            rw [bag, restSplit, add_assoc, ← add_assoc dead₀, add_comm dead₀ restCm, add_assoc, add_assoc]
          · intro d member
            rcases Multiset.mem_add.mp member with new | old
            · exact deadNew d new
            · exact deadDead d old
          · intro b' member
            rcases Multiset.mem_add.mp member with made | kept
            · exact move_keeps supply program (apart b inCm) movedP b' made
            · exact apart b' (by rw [splitCm]; exact Multiset.mem_cons_of_mem kept)

/-- **Backward**: a run without `e` is followed by a run with it. -/
theorem extension_backward {P : Program κ Γ star D.Ty} {e : Equation κ Γ star D.Ty} (program : ProgramApart P e)
    {C₁ C₂ : Config κ Γ star D.Ty} (runs : Runs D P supply C₁ C₂) {C' : Config κ Γ star D.Ty}
    (related : Related e C' C₁) : ∃ C'', Runs D (extend P e) supply C' C'' ∧ Related e C'' C₂ := by
  induction runs with
  | refl => exact ⟨C', .refl, related⟩
  | tail _ step ih =>
      obtain ⟨Cm', path, world, ⟨dead, split, deadDead⟩, apart⟩ := ih
      cases step with
      | move w w' b rest bs live moved =>
          have world' : Cm'.world = w := world
          have split' : Cm'.branches = b ::ₘ rest + dead := split
          obtain ⟨dead₀, deadNew, movedP⟩ := move_with supply (apart b (Multiset.mem_cons_self _ _)) moved
          refine ⟨⟨w', (bs + dead₀) + (rest + dead)⟩,
            path.tail (Step.of_eq (w := Cm'.world) (b := b) (rest := rest + dead)
              (by rw [split', Multiset.cons_add]) rfl live (world'.symm ▸ movedP)), rfl,
            ⟨dead₀ + dead, ?_, ?_⟩, ?_⟩
          · show bs + dead₀ + (rest + dead) = bs + rest + (dead₀ + dead)
            rw [add_assoc, add_assoc, ← add_assoc dead₀ rest, add_comm dead₀ rest, add_assoc]
          · intro d member
            rcases Multiset.mem_add.mp member with new | old
            · exact deadNew d new
            · exact deadDead d old
          · intro b' member
            rcases Multiset.mem_add.mp member with made | kept
            · exact move_keeps supply program (apart b (Multiset.mem_cons_self _ _)) moved b' made
            · exact apart b' (Multiset.mem_cons_of_mem kept)

/-- **Related configurations have the same bag of answers.** -/
theorem answers_related {e : Equation κ Γ star D.Ty} {C' C : Config κ Γ star D.Ty} (related : Related e C' C) :
    C'.answers = C.answers := by
  classical
  obtain ⟨_, ⟨dead, split, deadDead⟩, _⟩ := related
  simp only [Config.answers, split, Multiset.filter_add, Multiset.map_add]
  have none : Multiset.filter (fun b => b.Finished ∧ Solvable b.store) dead = 0 :=
    Multiset.filter_eq_nil.mpr fun d member hold => deadDead d member hold.2
  rw [none, Multiset.map_zero, add_zero]

#print axioms move_without
#print axioms move_with
#print axioms move_keeps
#print axioms extension_forward
#print axioms extension_backward
#print axioms answers_related

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Extension
