import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowNames

/-!
# Every arrow move has its exact finite named child bag

Unsolvable children remain in the full source bag and disappear only in the
live filter. In particular a pattern bind may have no live child, without
being an explicit fail expression.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  {P : SourceLanguage.Program κ Γ star D.Ty} {supply : Nat → Term S Γ star}

theorem move_names {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {bs : Multiset (Branch κ Γ star D.Ty)} (arrow : ArrowBranch b)
    (move : Move D P supply w b w' bs) :
    ∃ (ns : List Name) (child : Name → Branch κ Γ star D.Ty), ns.Nodup ∧
      bs = ((ns.map child : List (Branch κ Γ star D.Ty)) : Multiset (Branch κ Γ star D.Ty)) ∧
      (∀ name ∈ ns, NamedMove P w b name w' (child name)) ∧
      (∀ name next result, NamedMove P w b name next result →
        name ∈ ns ∧ next = w' ∧ result = child name) := by
  obtain ⟨frames, shape⟩ := arrow
  cases move
  case ret K t fs ps =>
    refine ⟨[.ret], fun _ => ⟨K, .value t, fs, ps⟩, List.nodup_singleton _, rfl,
      fun name member => by rw [List.mem_singleton.mp member]; exact .ret K t fs ps, ?_⟩
    intro name next result named
    cases named
    exact ⟨List.mem_singleton_self _, rfl, rfl⟩
  case apply K t fs ps matched =>
    let child : Name → Branch κ Γ star D.Ty := fun name => match name with
      | .eqn i => ((P.equations[i]?).map (callBranch D w.scope K t fs ps)).getD ⟨K, .eval (.apply t), fs, ps⟩
      | _ => ⟨K, .eval (.apply t), fs, ps⟩
    have childAt : ∀ i (small : i < P.equations.length),
        child (.eqn i) = callBranch D w.scope K t fs ps P.equations[i] := by
      intro i small
      simp [child, List.getElem?_eq_getElem small]
    refine ⟨(List.range P.equations.length).map .eqn, child, ?_, ?_, ?_, ?_⟩
    · exact List.Nodup.map (by intro x y same; cases same; rfl) List.nodup_range
    · apply congrArg (fun l : List (Branch κ Γ star D.Ty) => (l : Multiset (Branch κ Γ star D.Ty)))
      apply List.ext_getElem
      · simp
      · intro k small _
        simp only [List.length_map] at small
        simp only [List.getElem_map, List.getElem_range]
        exact (childAt k small).symm
    · intro name member
      obtain ⟨i, small, rfl⟩ := List.mem_map.mp member
      have small' := List.mem_range.mp small
      rw [childAt i small']
      exact .eqn K t fs ps i _ (List.getElem?_eq_getElem small') matched
    · intro name next result named
      cases named with
      | unmatched _ _ _ _ none =>
          obtain ⟨e, member, solvable⟩ := matched
          exact absurd solvable (none e member)
      | eqn _ _ _ _ i e get _ =>
          have small := FrontierNames.lookup_bound get
          refine ⟨List.mem_map.mpr ⟨i, List.mem_range.mpr small, rfl⟩, rfl, ?_⟩
          rw [childAt i small]
          rw [List.getElem?_eq_getElem small] at get
          cases get
          rfl
  case unmatched K t fs ps none =>
    refine ⟨[.unmatched], fun _ => ⟨K, .value t, fs, ps⟩, List.nodup_singleton _, rfl,
      fun name member => by rw [List.mem_singleton.mp member]; exact .unmatched K t fs ps none, ?_⟩
    intro name next result named
    cases named with
    | unmatched => exact ⟨List.mem_singleton_self _, rfl, rfl⟩
    | eqn _ _ _ _ i e get matched =>
        obtain ⟨e', member, solvable⟩ := matched
        exact absurd solvable (none e' member)
  case choice K c d fs ps =>
    let child : Name → Branch κ Γ star D.Ty := fun name => match name with
      | .right => ⟨K, .eval d, fs, ps⟩
      | _ => ⟨K, .eval c, fs, ps⟩
    refine ⟨[.left, .right], child, by decide, rfl, ?_, ?_⟩
    · intro name member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .left K c d fs ps
      · exact .right K c d fs ps
    · intro name next result named
      cases named with
      | left => exact ⟨by simp, rfl, rfl⟩
      | right => exact ⟨by simp, rfl, rfl⟩
  case letStart K site p c k fs ps =>
    refine ⟨[.bindStart], fun _ => ⟨K, .eval c, .bindTo site p k :: fs, ps⟩,
      List.nodup_singleton _, rfl,
      fun name member => by rw [List.mem_singleton.mp member]; exact .letStart K site p c k fs ps, ?_⟩
    intro name next result named
    cases named
    exact ⟨List.mem_singleton_self _, rfl, rfl⟩
  case letBind K value site p k fs ps =>
    refine ⟨[.bindValue], fun _ =>
      ⟨K ++ [(instantiate (openAt κ site w.scope) p, value)], .eval (k.inst (openAt κ site w.scope)), fs, ps⟩,
      List.nodup_singleton _, rfl,
      fun name member => by rw [List.mem_singleton.mp member]; exact .letBind K value site p k fs ps, ?_⟩
    intro name next result named
    cases named
    exact ⟨List.mem_singleton_self _, rfl, rfl⟩
  case fail K fs ps =>
    refine ⟨[], fun _ => ⟨K, .eval .fail, fs, ps⟩, List.nodup_nil, rfl,
      fun name member => (by cases member), ?_⟩
    intro name next result named
    cases named
  all_goals first
    | exact False.elim (arrow_eval shape)
    | (simp [ArrowFrames] at frames)

/-- An unfinished arrow branch can take a source move even when its sole
bind child will be dead. No liveness of that child is assumed. -/
theorem moves (w : World κ Γ star) {b : Branch κ Γ star D.Ty} (arrow : ArrowBranch b)
    (unfinished : ¬ b.Finished (D := D)) : ∃ w' bs, Move D P supply w b w' bs := by
  obtain ⟨K, focus, fs, ps⟩ := b
  obtain ⟨frames, shape⟩ := arrow
  rcases shape with ⟨c, same, ac⟩ | ⟨value, same⟩
  · simp only at same
    subst same
    cases c with
    | ret t => exact ⟨_, _, .ret w K t fs ps⟩
    | apply t =>
        by_cases matched : ∃ e ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])
        · exact ⟨_, _, .apply w K t fs ps matched⟩
        · exact ⟨_, _, .unmatched w K t fs ps fun e member live => matched ⟨e, member, live⟩⟩
    | let_ site p c k => exact ⟨_, _, .letStart w K site p c k fs ps⟩
    | choice c d => exact ⟨_, _, .choice w K c d fs ps⟩
    | fail => exact ⟨_, _, .fail w K fs ps⟩
    | _ => exact ac.elim
  · simp only at same
    subst same
    cases fs with
    | nil => exact absurd ⟨rfl, value, rfl⟩ unfinished
    | cons frame rest =>
        cases frame with
        | bindTo site p k => exact ⟨_, _, .letBind w K value site p k rest ps⟩
        | checkAt _ => exact frames.elim
        | memo _ => exact frames.elim

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow
