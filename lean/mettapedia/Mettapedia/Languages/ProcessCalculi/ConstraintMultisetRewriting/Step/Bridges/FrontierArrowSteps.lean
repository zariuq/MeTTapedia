import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowNames

/-!
# Named arrow moves and actual native firings

The two sequencing cases use the existing binding transfer laws. Frame
privacy is explicit at bind-value; the actual scoped-source invariant later
discharges it. Equation ordinals remain names even if concrete schemas agree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) {P : SourceLanguage.Program κ Γ star D.Ty}

theorem simulation (arrowP : ArrowProgram P) {w w' : World κ Γ star} {b b' : Branch κ Γ star D.Ty}
    {n : Name} (move : NamedMove P w b n w' b') {s : HostState S} {a : ℕ}
    (rep : Represents N P w.scope b s a) (arrow : ArrowBranch b) (hygienic : Hygienic b) (live : Solvable b'.store) {k : ℕ}
    (hk : k ∉ s.present) :
    ∃ s', Fires N P n ⟨s, a⟩ ⟨s', k⟩ ∧ Represents N P w'.scope b' s' k ∧ ArrowBranch b' := by
  obtain ⟨framesOk, shape⟩ := arrow
  cases move with
  | ret K t fs ps =>
      obtain ⟨s', fired, rep'⟩ := fire_simple_at N (retRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_ret N rfl q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
      exact ⟨s', ⟨_, rfl, fired⟩, rep', framesOk, .inr ⟨t, rfl⟩⟩
  | unmatched K t fs ps none =>
      obtain ⟨s', fired, rep'⟩ := fire_simple_at N (unmatchedRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_unmatched N rfl q) live hk (unmatched_guard N rep none)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
      exact ⟨s', ⟨_, rfl, fired⟩, rep', framesOk, .inr ⟨t, rfl⟩⟩
  | left K c d fs ps =>
      have arrowCD : ArrowComp c ∧ ArrowComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      obtain ⟨s', fired, rep'⟩ := fire_simple_at N (choiceLeftRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_choiceLeft N rfl q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
      exact ⟨s', ⟨_, rfl, fired⟩, rep', framesOk, .inl ⟨c, rfl, arrowCD.1⟩⟩
  | right K c d fs ps =>
      have arrowCD : ArrowComp c ∧ ArrowComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      obtain ⟨s', fired, rep'⟩ := fire_simple_at N (choiceRightRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_choiceRight N rfl q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
      exact ⟨s', ⟨_, rfl, fired⟩, rep', framesOk, .inl ⟨d, rfl, arrowCD.2⟩⟩
  | eqn K t fs ps i e get matched =>
      have eMember : e ∈ P.equations := List.mem_of_getElem? get
      obtain ⟨s', fired, rep'⟩ := fire_simple_at N (schema_mem N P eMember) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_schema N e rfl rep.fresh q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_call rep.fresh e) rep.noPending
      refine ⟨s', ⟨_, by simp [catalogue, lookup, get], fired⟩, rep', framesOk, .inl ⟨_, rfl, ?_⟩⟩
      exact arrowComp_mapData _ _ (arrowP e eMember)

  | letStart K site p c k fs ps =>
      have arrowCK : ArrowComp c ∧ ArrowComp k := arrow_eval shape
      obtain ⟨s', fired, rep'⟩ := fire_simple_at N (bindStartRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_bindStart N rfl q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_letStart rep.fresh) rep.noPending
      exact ⟨s', ⟨_, rfl, fired⟩, rep', ⟨arrowCK.2, framesOk⟩, .inl ⟨c, rfl, arrowCK.1⟩⟩
  | letBind K value site p k fs ps =>
      obtain ⟨s', fired, rep'⟩ := fire_simple_at N (bindValueRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_bindValue N rep.fresh (hygienic K value site p k fs ps rfl) q)
        live hk (entails_of_no_checks rfl rfl) (branchBelow_letBind rep.fresh) rep.noPending
      exact ⟨s', ⟨_, rfl, fired⟩, rep', framesOk.2, .inl ⟨_, rfl, arrowComp_mapData _ _ framesOk.1⟩⟩

theorem reflection (arrowP : ArrowProgram P) {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {n : Name} {s s' : HostState S} {a a' : ℕ} (rep : Represents N P w.scope b s a)
    (arrow : ArrowBranch b) (hygienic : Hygienic b) (fired : Fires N P n ⟨s, a⟩ ⟨s', a'⟩) :
    ∃ w' b', NamedMove P w b n w' b' ∧ Represents N P w'.scope b' s' a' ∧ ArrowBranch b' := by
  obtain ⟨r, named, ⟨rl, member, ext, opening, selection, seen⟩, rule, admitted, _, made, rfl⟩ := fired
  simp only at rule made
  subst rule
  obtain ⟨K, focus, fs, ps⟩ := b
  obtain ⟨framesOk, shape⟩ := arrow
  cases n with
  | ret =>
      simp only [catalogue, lookup, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      obtain ⟨t, rfl⟩ := shape_ret N reads
      refine ⟨w, _, .ret K t fs ps, ?_, framesOk, .inr ⟨t, rfl⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_ret N rfl q)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
  | unmatched =>
      simp only [catalogue, lookup, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
      obtain ⟨t, σ, rfl, _, _⟩ := shape_apply N reads
      refine ⟨w, _, .unmatched K t fs ps (unmatched_none N rep simple admitted), ?_, framesOk, .inr ⟨t, rfl⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_unmatched N rfl q)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
  | left =>
      simp only [catalogue, lookup, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      obtain ⟨c, d, rfl⟩ := shape_choice N reads
      have arrowCD : ArrowComp c ∧ ArrowComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      refine ⟨w, _, .left K c d fs ps, ?_, framesOk, .inl ⟨c, rfl, arrowCD.1⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_choiceLeft N rfl q)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
  | right =>
      simp only [catalogue, lookup, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      obtain ⟨c, d, rfl⟩ := shape_choice N reads
      have arrowCD : ArrowComp c ∧ ArrowComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      refine ⟨w, _, .right K c d fs ps, ?_, framesOk, .inl ⟨d, rfl, arrowCD.2⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_choiceRight N rfl q)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
  | eqn i =>
      obtain ⟨e, get, rfl⟩ := Option.map_eq_some_iff.mp named
      have eMember : e ∈ P.equations := List.mem_of_getElem? get
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_asUnknowns] at reads
      obtain ⟨t, σ, rfl, solved, onCall⟩ := shape_apply N reads
      have callBelow : DependsBelow w.scope t := rep.fresh.2.1 t (by simp [focusData, Comp.data])
      have matched : ∃ e' ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e'.lhs, t)]) :=
        ⟨e, eMember, (solvable_copy_iff e.lhs rep.fresh.1 callBelow).mpr ⟨_, _, σ, _, solved, onCall.symm⟩⟩
      refine ⟨w.fresh, _, .eqn K t fs ps i e get matched, ?_, framesOk,
        .inl ⟨_, rfl, arrowComp_mapData _ _ (arrowP e eMember)⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_schema N e rfl rep.fresh q)
        (branchBelow_call rep.fresh e) rep.noPending
  | bindStart =>
      simp only [catalogue, lookup, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      obtain ⟨site, p, c, k, rfl⟩ := shape_bindStart N reads
      have arrowCK : ArrowComp c ∧ ArrowComp k := arrow_eval shape
      refine ⟨w, _, .letStart K site p c k fs ps, ?_,
        ⟨arrowCK.2, framesOk⟩, .inl ⟨c, rfl, arrowCK.1⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_bindStart N rfl q)
        (branchBelow_letStart rep.fresh) rep.noPending
  | bindValue =>
      simp only [catalogue, lookup, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      obtain ⟨site, p, k, tail, rfl⟩ := shape_bindValue N reads
      have readsV := reads
      change branchReads N _ B (observe (instantiate h _)) at readsV
      rw [instantiate_altN, instantiate_valueN] at readsV
      obtain ⟨σ, _, same⟩ := (branchReads_observe N).mp readsV
      obtain ⟨onFocus, _⟩ := alt_eq_encAlt N (instantiate σ) same.symm
      obtain ⟨value, rfl, _⟩ := value_eq_encFocus N (instantiate σ) onFocus
      refine ⟨w.fresh, _, .letBind K value site p k tail ps, ?_,
        framesOk.2, .inl ⟨_, rfl, arrowComp_mapData _ _ framesOk.1⟩⟩
      exact represents_after N rep simple admitted.1 fresh
        (fun B q => transfer_bindValue N rep.fresh (hygienic K value site p k tail ps rfl) q)
        (branchBelow_letBind rep.fresh) rep.noPending

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow
