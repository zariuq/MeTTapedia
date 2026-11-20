import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowSteps

/-!
# The fragment with arrows: `ret`, `apply`, `let_`, `choice`, `fail`, step by step

`ArrowComp`, `ArrowProgram`, `ArrowBranch`: computations built from `ret`, `apply`, `let_`,
`choice`, `fail`; alternatives whose pending frames are `let` frames over such computations.
`Hygienic b`: if `b` is returning a value to a pending frame, the frame is hygienic
(`FramePrivate`).

* `simulation_arrows`: every source step of a represented alternative of the fragment is matched,
  for each live alternative it makes, by **one firing**; at a bind, for a hygienic alternative.
* `reflection_arrows`: every firing from a represented, hygienic alternative of the fragment is a
  source step of it, to a state that represents one of the alternatives the step makes.

Every alternative of the first fragment (no frames) is hygienic (`hygienic_of_plain`), so these two
theorems contain `simulation` and `reflection` of the first fragment. Every alternative that a source
run reaches from a well-formed query and program is hygienic (`Hygiene`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

/-! ## The fragment with arrows -/

section Fragment

variable {Ty : Type}

/-- **The computations of the fragment with arrows.** -/
def ArrowComp : Comp κ Γ star Ty → Prop
  | .ret _ => True
  | .apply _ => True
  | .let_ _ _ c k => ArrowComp c ∧ ArrowComp k
  | .choice c d => ArrowComp c ∧ ArrowComp d
  | .fail => True
  | _ => False

def ArrowProgram (P : SourceLanguage.Program κ Γ star Ty) : Prop := ∀ e ∈ P.equations, ArrowComp e.rhs

/-- Pending frames of the fragment: `let` frames over computations of the fragment. -/
def ArrowFrames : List (SourceLanguage.Frame κ Γ star Ty) → Prop
  | [] => True
  | .bindTo _ _ k :: fs => ArrowComp k ∧ ArrowFrames fs
  | .checkAt _ :: _ => False
  | .memo _ :: _ => False

/-- **An alternative of the fragment with arrows.** -/
def ArrowBranch (b : Branch κ Γ star Ty) : Prop :=
  ArrowFrames b.frames ∧ ((∃ c, b.focus = .eval c ∧ ArrowComp c) ∨ ∃ t, b.focus = .value t)

/-- **A hygienic alternative**: a value returned to a pending frame finds the frame hygienic. -/
def Hygienic (b : Branch κ Γ star Ty) : Prop :=
  ∀ K v s p k fs ps, b = ⟨K, .value v, .bindTo s p k :: fs, ps⟩ → FramePrivate s p k K v fs

theorem arrowComp_mapData (g : Data κ Γ star → Data κ Γ star) :
    ∀ c : Comp κ Γ star Ty, ArrowComp c → ArrowComp (c.mapData g)
  | .ret _, _ => trivial
  | .apply _, _ => trivial
  | .let_ _ _ c k, ⟨pc, pk⟩ => ⟨arrowComp_mapData g c pc, arrowComp_mapData g k pk⟩
  | .choice c d, ⟨pc, pd⟩ => ⟨arrowComp_mapData g c pc, arrowComp_mapData g d pd⟩
  | .fail, _ => trivial
  | .run _, h => h.elim
  | .query _ _ _, h => h.elim
  | .add _ _ _, h => h.elim
  | .remove _ _ _, h => h.elim
  | .new _ _ _, h => h.elim
  | .check _ _, h => h.elim
  | .delay _ _ _ _, h => h.elim
  | .force _, h => h.elim

theorem plainComp_arrow : ∀ c : Comp κ Γ star Ty, PlainComp c → ArrowComp c
  | .ret _, _ => trivial
  | .apply _, _ => trivial
  | .choice c d, ⟨pc, pd⟩ => ⟨plainComp_arrow c pc, plainComp_arrow d pd⟩
  | .fail, _ => trivial
  | .let_ _ _ _ _, h => h.elim
  | .run _, h => h.elim
  | .query _ _ _, h => h.elim
  | .add _ _ _, h => h.elim
  | .remove _ _ _, h => h.elim
  | .new _ _ _, h => h.elim
  | .check _ _, h => h.elim
  | .delay _ _ _ _, h => h.elim
  | .force _, h => h.elim

/-- The first fragment is in the fragment with arrows. -/
theorem arrowBranch_of_plain {b : Branch κ Γ star Ty} (plain : PlainBranch b) : ArrowBranch b := by
  obtain ⟨frames, shape⟩ := plain
  refine ⟨by rw [frames]; trivial, ?_⟩
  rcases shape with ⟨c, focus, pc⟩ | value
  · exact .inl ⟨c, focus, plainComp_arrow c pc⟩
  · exact .inr value

/-- An alternative of the first fragment is hygienic: it has no pending frame. -/
theorem hygienic_of_plain {b : Branch κ Γ star Ty} (plain : PlainBranch b) : Hygienic b := by
  intro K v s p k fs ps same
  have frames := plain.1
  rw [same] at frames
  cases frames

theorem arrow_eval {c : Comp κ Γ star Ty}
    (shape : (∃ c', Focus.eval c = Focus.eval c' ∧ ArrowComp c') ∨ ∃ t, Focus.eval c = (Focus.value t : Focus κ Γ star Ty)) :
    ArrowComp c := by
  rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
  · cases same; exact pc
  · cases same

end Fragment

/-! ## Simulation -/

section Simulation

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **Simulation for the fragment with arrows**: one firing for each live alternative a source step
makes; at a bind, of a hygienic alternative. -/
theorem simulation_arrows (arrowP : ArrowProgram P) {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {bs : Multiset (Branch κ Γ star D.Ty)} (move : Move D P supply w b w' bs)
    {s : HostState S} {a : ℕ} (rep : Represents N P w.scope b s a) (arrow : ArrowBranch b)
    (hygienic : Hygienic b) {b' : Branch κ Γ star D.Ty} (child : b' ∈ bs) (live : Solvable b'.store) :
    ∃ s' a', Fires N P s s' ∧ Represents N P w'.scope b' s' a' ∧ ArrowBranch b' := by
  obtain ⟨frames, shape⟩ := arrow
  cases move
  case ret K t fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨s', a', fires, rep'⟩ := fire_simple N (retRule_mem N P) rfl rfl rfl rfl rep
      (fun B q => transfer_ret N rfl q) live (entails_of_no_checks rfl rfl)
      (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    exact ⟨s', a', fires, rep', frames, .inr ⟨t, rfl⟩⟩
  case apply K t fs ps matched =>
    obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp child)
    obtain ⟨s', a', fires, rep'⟩ := fire_simple N (schema_mem N P eMember) rfl rfl rfl rfl rep
      (fun B q => transfer_schema N e rfl rep.fresh q) live (entails_of_no_checks rfl rfl)
      (branchBelow_call rep.fresh e) rep.noPending
    exact ⟨s', a', fires, rep', frames, .inl ⟨_, rfl, arrowComp_mapData _ _ (arrowP e eMember)⟩⟩
  case unmatched K t fs ps none =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨s', a', fires, rep'⟩ := fire_simple N (unmatchedRule_mem N P) rfl rfl rfl rfl rep
      (fun B q => transfer_unmatched N rfl q) live (unmatched_guard N rep none)
      (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    exact ⟨s', a', fires, rep', frames, .inr ⟨t, rfl⟩⟩
  case choice K c d fs ps =>
    have arrowCD : ArrowComp c ∧ ArrowComp d := arrow_eval shape
    rcases Multiset.mem_cons.mp child with rfl | other
    · obtain ⟨s', a', fires, rep'⟩ := fire_simple N (choiceLeftRule_mem N P) rfl rfl rfl rfl rep
        (fun B q => transfer_choiceLeft N rfl q) live (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
      exact ⟨s', a', fires, rep', frames, .inl ⟨c, rfl, arrowCD.1⟩⟩
    · rw [Multiset.mem_singleton] at other
      subst other
      obtain ⟨s', a', fires, rep'⟩ := fire_simple N (choiceRightRule_mem N P) rfl rfl rfl rfl rep
        (fun B q => transfer_choiceRight N rfl q) live (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
      exact ⟨s', a', fires, rep', frames, .inl ⟨d, rfl, arrowCD.2⟩⟩
  case fail K fs ps =>
    simp at child
  case letStart K s₁ p c k fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    have arrowCK : ArrowComp c ∧ ArrowComp k := arrow_eval shape
    obtain ⟨s', a', fires, rep'⟩ := simulation_letStart N rep live
    exact ⟨s', a', fires, rep', ⟨arrowCK.2, frames⟩, .inl ⟨c, rfl, arrowCK.1⟩⟩
  case letBind K v s₁ p k fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨s', a', fires, rep'⟩ := simulation_letBind N rep (hygienic K v s₁ p k fs ps rfl) live
    exact ⟨s', a', fires, rep', frames.2, .inl ⟨_, rfl, arrowComp_mapData _ _ frames.1⟩⟩
  all_goals first
    | exact False.elim (arrow_eval shape)
    | exact False.elim frames

end Simulation

/-! ## Reflection -/

section Reflection

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **Reflection for the fragment with arrows**: every firing from a represented, hygienic alternative
of the fragment is a source step of it. -/
theorem reflection_arrows (arrowP : ArrowProgram P) {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {s s' : HostState S} {a : ℕ} (rep : Represents N P w.scope b s a) (arrow : ArrowBranch b)
    (hygienic : Hygienic b) (fires : Fires N P s s') :
    ∃ w' bs b' a', Move D P supply w b w' bs ∧ b' ∈ bs ∧ Represents N P w'.scope b' s' a' ∧ ArrowBranch b' := by
  obtain ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, rfl⟩ := fires
  obtain ⟨K, focus, frames', ps⟩ := b
  obtain ⟨framesOk, shape⟩ := arrow
  rcases (mem_translate N).mp member with control | ⟨e, eMember, rfl⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
    · -- `ret`
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨t, rfl⟩ := shape_ret N reads
      refine ⟨w, _, _, a', .ret w K t frames' ps, Multiset.mem_singleton_self _, ?_, framesOk, .inr ⟨t, rfl⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_ret N rfl q)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    · -- an unmatched call
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
      obtain ⟨t, σ, rfl, _, _⟩ := shape_apply N reads
      refine ⟨w, _, _, a', .unmatched w K t frames' ps (unmatched_none N rep simple admitted),
        Multiset.mem_singleton_self _, ?_, framesOk, .inr ⟨t, rfl⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_unmatched N rfl q)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    · -- the left alternative of a choice
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, rfl⟩ := shape_choice N reads
      have arrowCD : ArrowComp c ∧ ArrowComp d := arrow_eval shape
      refine ⟨w, _, _, a', .choice w K c d frames' ps, Multiset.mem_cons_self _ _, ?_, framesOk,
        .inl ⟨c, rfl, arrowCD.1⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_choiceLeft N rfl q)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
    · -- the right alternative of a choice
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, rfl⟩ := shape_choice N reads
      have arrowCD : ArrowComp c ∧ ArrowComp d := arrow_eval shape
      refine ⟨w, _, _, a', .choice w K c d frames' ps, Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _),
        ?_, framesOk, .inl ⟨d, rfl, arrowCD.2⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_choiceRight N rfl q)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
    · -- pushing a `let` frame
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨s₁, p, c, k, rfl⟩ := shape_bindStart N reads
      have arrowCK : ArrowComp c ∧ ArrowComp k := arrow_eval shape
      refine ⟨w, _, _, a', .letStart w K s₁ p c k frames' ps, Multiset.mem_singleton_self _, ?_,
        ⟨arrowCK.2, framesOk⟩, .inl ⟨c, rfl, arrowCK.1⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_bindStart N rfl q)
        (branchBelow_letStart rep.fresh) rep.noPending
    · -- returning a value to a `let` frame
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨s₁, p, k, fs, rfl⟩ := shape_bindValue N reads
      have readsV := reads
      change branchReads N _ B (observe (instantiate h _)) at readsV
      rw [instantiate_altN, instantiate_valueN] at readsV
      obtain ⟨σ, _, same⟩ := (branchReads_observe N).mp readsV
      obtain ⟨onFocus, _⟩ := alt_eq_encAlt N (instantiate σ) same.symm
      obtain ⟨v, rfl, _⟩ := value_eq_encFocus N (instantiate σ) onFocus
      refine ⟨w.fresh, _, _, a', .letBind w K v s₁ p k fs ps, Multiset.mem_singleton_self _, ?_,
        framesOk.2, .inl ⟨_, rfl, arrowComp_mapData _ _ framesOk.1⟩⟩
      exact represents_after N rep simple admitted.1 fresh
        (fun B q => transfer_bindValue N rep.fresh (hygienic K v s₁ p k fs ps rfl) q)
        (branchBelow_letBind rep.fresh) rep.noPending
  · -- the schema of an equation
    obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
      (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
    change branchReads N _ B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_asUnknowns] at reads
    obtain ⟨t, σ, rfl, solved, onCall⟩ := shape_apply N reads
    have callBelow : DependsBelow w.scope t := rep.fresh.2.1 t (by simp [focusData, Comp.data])
    have matched : ∃ e' ∈ P.equations,
        Solvable (K ++ [(instantiate (copyAt κ w.scope) e'.lhs, t)]) :=
      ⟨e, eMember, (solvable_copy_iff e.lhs rep.fresh.1 callBelow).mpr ⟨_, _, σ, _, solved, onCall.symm⟩⟩
    refine ⟨w.fresh, _, _, a', .apply w K t frames' ps matched,
      Multiset.mem_coe.mpr (List.mem_map.mpr ⟨e, eMember, rfl⟩), ?_, framesOk,
      .inl ⟨_, rfl, arrowComp_mapData _ _ (arrowP e eMember)⟩⟩
    exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_schema N e rfl rep.fresh q)
      (branchBelow_call rep.fresh e) rep.noPending

end Reflection

#print axioms simulation_arrows
#print axioms reflection_arrows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
