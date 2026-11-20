import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics

/-!
# What a configuration shows: answers, refusals, and waiting as a typed none query

An alternative's store changes only by its own moves, so a live alternative that cannot move waits
forever. The bag of answers (`Config.answers`) counts finished live alternatives only, so a waiting
alternative and a failed one look alike there. The observation (`observe`) shows, besides the
bag of answers, the bag of refusals (a value and the type that refused it) and the bag of reasons the
live alternatives wait on:

* `address sp`: a space operation (`query`, `add`, `remove`) whose address `sp` the store does not
  determine;
* `noPrincipal t`: a `run` of the text `t` whose store has no most general solution;
* `mixed v T`: a `check` of type `T` at the value `v`, some of whose readings `T` admits and some not.

Waiting is not an error: nothing is made to fail, and every law about runs is unchanged. It is a
typed none query in what a configuration shows.

* **Exactly three ways to wait** (`moves_or_rests`): a live alternative moves, or it is finished, or
  it is refused, or it waits on one of the three reasons; and an alternative with a reason does not
  move (`stuck_of_reason`). So in a quiescent configuration every live alternative is finished,
  refused or waiting with its reason (`quiescent_rests`).
* **`run` waits exactly when the store has no most general solution** (`run_moves_iff`).
* **Failing and waiting are told apart** (`ExampleWaiting`): the same empty bag of answers, different
  observations.
* **Dead alternatives are not observed** (`observe_add_dead`): so the extension law's related
  configurations, which differ by dead alternatives, have the same observation.
* **The renaming law holds with the reasons renamed** (`ObservationRenaming.observe_rConfig`). The laws
  about runs relate configurations and hold unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Observation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}

/-- **Why a live alternative waits.** -/
inductive Waiting (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) : Type where
  | address (space : Data κ Γ star)
  | noPrincipal (text : Data κ Γ star)
  | mixed (value : Data κ Γ star) (type : Ty)

variable {D : Discipline S Γ star}

open Classical in
/-- **The reason an alternative waits on**, if its shape is one that waits and its store does not let
it move. -/
noncomputable def reason (b : Branch κ Γ star D.Ty) : Option (Waiting κ Γ star D.Ty) :=
  match b.focus, b.frames with
  | .eval (.run t), _ => if ∃ θ, Principal b.store θ then none else some (.noPrincipal t)
  | .eval (.query sp _ _), _ => if ∃ h, Determines b.store sp h then none else some (.address sp)
  | .eval (.add sp _ _), _ => if ∃ h, Determines b.store sp h then none else some (.address sp)
  | .eval (.remove sp _ _), _ => if ∃ h, Determines b.store sp h then none else some (.address sp)
  | .value v, .checkAt T :: _ =>
      if (∀ g, Reads b.store v g → D.admits T g) ∨ (∀ g, Reads b.store v g → ¬ D.admits T g) then none
      else some (.mixed v T)
  | _, _ => none

/-- A refused alternative: the value and the type that refused it. -/
def refusal (b : Branch κ Γ star D.Ty) : Option (Data κ Γ star × D.Ty) :=
  match b.focus with
  | .refused v T => some (v, T)
  | _ => none

open Classical in
/-- The live alternatives of a configuration. -/
noncomputable def live (C : Config κ Γ star D.Ty) : Multiset (Branch κ Γ star D.Ty) :=
  C.branches.filter fun b => Solvable b.store

/-- **What a configuration shows.** -/
structure Shown (S : Signature) (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  answers : Multiset (Set (Term S Γ star))
  refusals : Multiset (Data κ Γ star × Ty)
  waiting : Multiset (Waiting κ Γ star Ty)

/-- **The observation**: answers, refusals of live alternatives, reasons of live waiting alternatives. -/
noncomputable def observe (C : Config κ Γ star D.Ty) : Shown S κ Γ star D.Ty :=
  ⟨C.answers, (live C).filterMap refusal, (live C).filterMap reason⟩

/-! ## Exactly three ways to wait -/

variable {P : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **An alternative with a reason does not move.** -/
theorem stuck_of_reason {w : World κ Γ star} {b : Branch κ Γ star D.Ty} {r : Waiting κ Γ star D.Ty}
    (waits : reason b = some r) : ∀ w' bs, ¬ Move D P supply w b w' bs := by
  classical
  intro w' bs moved
  cases moved with
  | run K t fs ps θ principal =>
      simp only [reason] at waits
      rw [if_pos ⟨θ, principal⟩] at waits
      cases waits
  | query K sp p k fs ps h addressed =>
      simp only [reason] at waits
      rw [if_pos ⟨h, addressed⟩] at waits
      cases waits
  | add K sp t k fs ps h addressed =>
      simp only [reason] at waits
      rw [if_pos ⟨h, addressed⟩] at waits
      cases waits
  | remove K sp t k fs ps h addressed r rest split fits =>
      simp only [reason] at waits
      rw [if_pos ⟨h, addressed⟩] at waits
      cases waits
  | removeMissing K sp t k fs ps h addressed none =>
      simp only [reason] at waits
      rw [if_pos ⟨h, addressed⟩] at waits
      cases waits
  | admitted K v T fs ps all =>
      simp only [reason] at waits
      rw [if_pos (Or.inl all)] at waits
      cases waits
  | refused K v T fs ps none =>
      simp only [reason] at waits
      rw [if_pos (Or.inr none)] at waits
      cases waits
  | ret => simp [reason] at waits
  | apply => simp [reason] at waits
  | unmatched => simp [reason] at waits
  | letStart => simp [reason] at waits
  | letBind => simp [reason] at waits
  | choice => simp [reason] at waits
  | fail => simp [reason] at waits
  | new => simp [reason] at waits
  | checkStart => simp [reason] at waits
  | delay => simp [reason] at waits
  | forcePending => simp [reason] at waits
  | forceDone => simp [reason] at waits
  | memo => simp [reason] at waits

/-- **A live alternative moves, or rests**: it is finished, or refused, or it waits with a reason. -/
theorem moves_or_rests (w : World κ Γ star) (b : Branch κ Γ star D.Ty) :
    (∃ w' bs, Move D P supply w b w' bs) ∨ b.Finished ∨ (∃ v T, b.focus = .refused v T) ∨
      ∃ r, reason b = some r := by
  classical
  rcases b with ⟨K, focus, frames, pending⟩
  cases focus with
  | eval c =>
      cases c with
      | ret t => exact .inl ⟨_, _, .ret w K t frames pending⟩
      | apply t =>
          by_cases matched : ∃ e ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])
          · exact .inl ⟨_, _, .apply w K t frames pending matched⟩
          · exact .inl ⟨_, _, .unmatched w K t frames pending fun e member live => matched ⟨e, member, live⟩⟩
      | run t =>
          by_cases principal : ∃ θ, Principal K θ
          · obtain ⟨θ, hθ⟩ := principal
            exact .inl ⟨_, _, .run w K t frames pending θ hθ⟩
          · refine .inr (.inr (.inr ⟨.noPrincipal t, ?_⟩))
            simp only [reason]
            rw [if_neg principal]
      | let_ s p c k => exact .inl ⟨_, _, .letStart w K s p c k frames pending⟩
      | choice c d => exact .inl ⟨_, _, .choice w K c d frames pending⟩
      | fail => exact .inl ⟨_, _, .fail w K frames pending⟩
      | query sp p k =>
          by_cases addressed : ∃ h, Determines K sp h
          · obtain ⟨h, hh⟩ := addressed
            exact .inl ⟨_, _, .query w K sp p k frames pending h hh⟩
          · refine .inr (.inr (.inr ⟨.address sp, ?_⟩))
            simp only [reason]
            rw [if_neg addressed]
      | add sp t k =>
          by_cases addressed : ∃ h, Determines K sp h
          · obtain ⟨h, hh⟩ := addressed
            exact .inl ⟨_, _, .add w K sp t k frames pending h hh⟩
          · refine .inr (.inr (.inr ⟨.address sp, ?_⟩))
            simp only [reason]
            rw [if_neg addressed]
      | remove sp t k =>
          by_cases addressed : ∃ h, Determines K sp h
          · obtain ⟨h, hh⟩ := addressed
            by_cases fits : ∃ r ∈ w.spaces h, Solvable (K ++ rowUse w.scope r t)
            · obtain ⟨r, member, hr⟩ := fits
              obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
              exact .inl ⟨_, _, .remove w K sp t k frames pending h hh r rest split hr⟩
            · exact .inl ⟨_, _, .removeMissing w K sp t k frames pending h hh
                fun r member live => fits ⟨r, member, live⟩⟩
          · refine .inr (.inr (.inr ⟨.address sp, ?_⟩))
            simp only [reason]
            rw [if_neg addressed]
      | new s x k => exact .inl ⟨_, _, .new w K s x k frames pending⟩
      | check T c => exact .inl ⟨_, _, .checkStart w K T c frames pending⟩
      | delay s x c k => exact .inl ⟨_, _, .delay w K s x c k frames pending⟩
      | force x =>
          by_cases bound : ∃ e ∈ pending, EntailsEq K x e.1
          · obtain ⟨⟨cell, c⟩, member, hb⟩ := bound
            obtain ⟨before, after, split⟩ := List.append_of_mem member
            subst split
            exact .inl ⟨_, _, .forcePending w K x cell c frames before after hb⟩
          · exact .inl ⟨_, _, .forceDone w K x frames pending fun e member entailed =>
              bound ⟨e, member, entailed⟩⟩
  | value v =>
      cases frames with
      | nil => exact .inr (.inl ⟨rfl, v, rfl⟩)
      | cons f fs =>
          cases f with
          | bindTo s p k => exact .inl ⟨_, _, .letBind w K v s p k fs pending⟩
          | checkAt T =>
              by_cases all : ∀ g, Reads K v g → D.admits T g
              · exact .inl ⟨_, _, .admitted w K v T fs pending all⟩
              · by_cases none : ∀ g, Reads K v g → ¬ D.admits T g
                · exact .inl ⟨_, _, .refused w K v T fs pending none⟩
                · refine .inr (.inr (.inr ⟨.mixed v T, ?_⟩))
                  simp only [reason]
                  rw [if_neg (by rintro (h | h) <;> contradiction)]
          | memo x => exact .inl ⟨_, _, .memo w K v x fs pending⟩
  | refused v T => exact .inr (.inr (.inl ⟨v, T, rfl⟩))

/-- **In a quiescent configuration, every live alternative is finished, refused, or waiting with its
reason.** -/
theorem quiescent_rests {C : Config κ Γ star D.Ty} (quiescent : C.Quiescent P supply)
    {b : Branch κ Γ star D.Ty} (member : b ∈ C.branches) (alive : Solvable b.store) :
    b.Finished ∨ (∃ v T, b.focus = .refused v T) ∨ ∃ r, reason b = some r := by
  rcases moves_or_rests (P := P) (supply := supply) C.world b with ⟨w', bs, moved⟩ | rest
  · exact absurd moved (quiescent b member alive w' bs)
  · exact rest

/-- **`run` waits exactly when the store has no most general solution.** -/
theorem run_moves_iff (w : World κ Γ star) (K : List (Constraint κ Γ star)) (t : Data κ Γ star)
    (fs : List (Frame κ Γ star D.Ty)) (ps : List (Data κ Γ star × Comp κ Γ star D.Ty)) :
    (∃ w' bs, Move D P supply w ⟨K, .eval (.run t), fs, ps⟩ w' bs) ↔ ∃ θ, Principal K θ := by
  constructor
  · rintro ⟨w', bs, moved⟩
    cases moved with
    | run _ _ _ _ θ principal => exact ⟨θ, principal⟩
  · rintro ⟨θ, principal⟩
    exact ⟨_, _, .run w K t fs ps θ principal⟩

/-- A finished alternative has no reason and no refusal. -/
theorem reason_of_finished {b : Branch κ Γ star D.Ty} (finished : b.Finished) : reason b = none := by
  obtain ⟨frames, t, focus⟩ := finished
  rcases b with ⟨K, f, fr, ps⟩
  simp only at frames focus
  subst frames focus
  simp [reason]

/-! ## Dead alternatives are not observed -/

theorem observe_add_dead (C : Config κ Γ star D.Ty) (dead : Multiset (Branch κ Γ star D.Ty))
    (allDead : ∀ d ∈ dead, ¬ Solvable d.store) :
    observe (⟨C.world, C.branches + dead⟩ : Config κ Γ star D.Ty) = observe C := by
  classical
  have noLive : dead.filter (fun b => Solvable b.store) = 0 :=
    Multiset.filter_eq_nil.mpr fun d member alive => allDead d member alive
  have noAnswers : dead.filter (fun b => b.Finished ∧ Solvable b.store) = 0 :=
    Multiset.filter_eq_nil.mpr fun d member hold => allDead d member hold.2
  simp only [observe, live, Config.answers, Multiset.filter_add, noLive, noAnswers, add_zero]

#print axioms stuck_of_reason
#print axioms moves_or_rests
#print axioms quiescent_rests
#print axioms run_moves_iff
#print axioms observe_add_dead

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Observation
