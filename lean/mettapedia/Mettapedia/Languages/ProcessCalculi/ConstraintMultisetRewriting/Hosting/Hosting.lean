import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Steps

/-!
# Simulation and reflection, step by step

For a program of the first fragment (`PlainProgram`: right sides built from `ret`, `apply`, `choice`,
`fail`; left sides any data, in particular second-order patterns under binders):

* **`simulation`**: every source step of an alternative that a state represents makes a bag of
  alternatives, and every live alternative of that bag is reached from the state by **one firing**
  of the translated program, to a state that represents it.
* **`reflection`**: every firing of the translated program from such a state is a source step of the
  alternative, and the state it reaches represents one of the alternatives that step makes.

Both directions hold for every admitted firing: any extension, any fresh opening, any fresh row
identity. A step whose bag is empty (`fail`, or an equation whose copy does not unify with the call)
has no firing, and an alternative that has finished has none either.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

/-- A plain alternative evaluating `c` evaluates a plain computation. -/
theorem plain_eval {c : Comp κ Γ star D.Ty}
    (shape : (∃ c', Focus.eval c = Focus.eval c' ∧ PlainComp c') ∨ ∃ t, Focus.eval c = (Focus.value t : Focus κ Γ star D.Ty)) :
    PlainComp c := by
  rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
  · cases same; exact pc
  · cases same

/-- **Simulation**: one firing for each live alternative a source step makes. -/
theorem simulation (plainP : PlainProgram P) {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {bs : Multiset (Branch κ Γ star D.Ty)} (move : Move D P supply w b w' bs)
    {s : HostState S} {a : ℕ} (rep : Represents N P w.scope b s a) (plain : PlainBranch b)
    {b' : Branch κ Γ star D.Ty} (child : b' ∈ bs) (live : Solvable b'.store) :
    ∃ s' a', Fires N P s s' ∧ Represents N P w'.scope b' s' a' ∧ PlainBranch b' := by
  obtain ⟨noFrames, shape⟩ := plain
  cases move
  case ret K t fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨s', a', fires, rep'⟩ := fire_simple N (retRule_mem N P) rfl rfl rfl rfl rep
      (fun B q => transfer_ret N rfl q) live (entails_of_no_checks rfl rfl)
      (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    exact ⟨s', a', fires, rep', noFrames, .inr ⟨t, rfl⟩⟩
  case apply K t fs ps matched =>
    obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp child)
    obtain ⟨s', a', fires, rep'⟩ := fire_simple N (schema_mem N P eMember) rfl rfl rfl rfl rep
      (fun B q => transfer_schema N e rfl rep.fresh q) live (entails_of_no_checks rfl rfl)
      (branchBelow_call rep.fresh e) rep.noPending
    exact ⟨s', a', fires, rep', noFrames, .inl ⟨_, rfl, plainComp_mapData _ _ (plainP e eMember)⟩⟩
  case unmatched K t fs ps none =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨s', a', fires, rep'⟩ := fire_simple N (unmatchedRule_mem N P) rfl rfl rfl rfl rep
      (fun B q => transfer_unmatched N rfl q) live (unmatched_guard N rep none)
      (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    exact ⟨s', a', fires, rep', noFrames, .inr ⟨t, rfl⟩⟩
  case choice K c d fs ps =>
    have plainCD : PlainComp c ∧ PlainComp d := by
      rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
      · cases same; exact pc
      · cases same
    rcases Multiset.mem_cons.mp child with rfl | other
    · obtain ⟨s', a', fires, rep'⟩ := fire_simple N (choiceLeftRule_mem N P) rfl rfl rfl rfl rep
        (fun B q => transfer_choiceLeft N rfl q) live (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
      exact ⟨s', a', fires, rep', noFrames, .inl ⟨c, rfl, plainCD.1⟩⟩
    · rw [Multiset.mem_singleton] at other
      subst other
      obtain ⟨s', a', fires, rep'⟩ := fire_simple N (choiceRightRule_mem N P) rfl rfl rfl rfl rep
        (fun B q => transfer_choiceRight N rfl q) live (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
      exact ⟨s', a', fires, rep', noFrames, .inl ⟨d, rfl, plainCD.2⟩⟩
  case fail K fs ps =>
    simp at child
  all_goals first
    | exact False.elim (plain_eval shape)
    | (simp at noFrames)

/-- **Reflection**: every firing from a represented alternative is a source step of it. -/
theorem reflection (plainP : PlainProgram P) {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {s s' : HostState S} {a : ℕ} (rep : Represents N P w.scope b s a) (plain : PlainBranch b)
    (fires : Fires N P s s') :
    ∃ w' bs b' a', Move D P supply w b w' bs ∧ b' ∈ bs ∧ Represents N P w'.scope b' s' a' ∧ PlainBranch b' := by
  obtain ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, rfl⟩ := fires
  obtain ⟨K, focus, fs, ps⟩ := b
  obtain ⟨noFrames, shape⟩ := plain
  simp only at noFrames
  subst noFrames
  rcases (mem_translate N).mp member with control | ⟨e, eMember, rfl⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
    · -- `ret`
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨t, rfl⟩ := shape_ret N reads
      refine ⟨w, _, _, a', .ret w K t [] ps, Multiset.mem_singleton_self _, ?_, rfl, .inr ⟨t, rfl⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_ret N rfl q)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    · -- an unmatched call
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
      obtain ⟨t, σ, rfl, _, _⟩ := shape_apply N reads
      refine ⟨w, _, _, a', .unmatched w K t [] ps (unmatched_none N rep simple admitted),
        Multiset.mem_singleton_self _, ?_, rfl, .inr ⟨t, rfl⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_unmatched N rfl q)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    · -- the left alternative of a choice
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, rfl⟩ := shape_choice N reads
      have plainCD : PlainComp c ∧ PlainComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      refine ⟨w, _, _, a', .choice w K c d [] ps, Multiset.mem_cons_self _ _, ?_, rfl, .inl ⟨c, rfl, plainCD.1⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_choiceLeft N rfl q)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
    · -- the right alternative of a choice
      obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, rfl⟩ := shape_choice N reads
      have plainCD : PlainComp c ∧ PlainComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      refine ⟨w, _, _, a', .choice w K c d [] ps, Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _),
        ?_, rfl, .inl ⟨d, rfl, plainCD.2⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_choiceRight N rfl q)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
    · -- starting a `let`: not in the fragment
      obtain ⟨a', _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨s₁, p, c, k, rfl⟩ := shape_bindStart N reads
      rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
      · cases same; exact pc.elim
      · cases same
    · -- a value returned to a `let` frame: no frames in the fragment
      obtain ⟨a', _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨s₁, p, k, fs', frames⟩ := shape_bindValue N reads
      cases frames
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
    have plainE := plainP e eMember
    refine ⟨w.fresh, _, _, a', .apply w K t [] ps matched,
      Multiset.mem_coe.mpr (List.mem_map.mpr ⟨e, eMember, rfl⟩), ?_, rfl,
      .inl ⟨_, rfl, plainComp_mapData _ _ plainE⟩⟩
    exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_schema N e rfl rep.fresh q)
      (branchBelow_call rep.fresh e) rep.noPending

#print axioms simulation
#print axioms reflection

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
