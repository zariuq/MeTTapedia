import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContinuationLift
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowHosting

/-!
# Transporting an actual source execution beneath a pending continuation

Appending a continuation preserves each move of the source fragment with
arrows, including calls and binds within the bound computation. This extends
the existing binder-core continuation transport to actual arrow programs.
The source world, branch constraints and every generated sibling are kept.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalFrameTransport

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting
open ContinuationLift (branch configuration)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
  (supply : Nat → Term S Γ star)

theorem mapped_calls (frame : Frame κ Γ star D.Ty) (scope : Nat)
    (K : List (Constraint κ Γ star)) (term : Data κ Γ star)
    (frames : List (Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty)) :
    (((P.equations.map (callBranch D scope K term frames pending)) : Multiset (Branch κ Γ star D.Ty)).map
      (branch frame)) =
      ((P.equations.map (callBranch D scope K term (frames ++ [frame]) pending)) :
        Multiset (Branch κ Γ star D.Ty)) := by
  simp [branch, callBranch, List.map_map, Function.comp_def]
  exact List.Perm.refl _

theorem move (frame : Frame κ Γ star D.Ty)
    {world nextWorld : World κ Γ star} {before : Branch κ Γ star D.Ty}
    {children : Multiset (Branch κ Γ star D.Ty)}
    (arrow : ArrowBranch before) (moved : Move D P supply world before nextWorld children) :
    Move D P supply world (branch frame before) nextWorld (children.map (branch frame)) := by
  cases moved with
  | ret K term frames pending =>
      simpa [branch] using
        (Move.ret (D := D) (P := P) (supply := supply) world K term (frames ++ [frame]) pending)
  | apply K term frames pending matched =>
      rw [mapped_calls]
      exact .apply _ _ _ _ _ matched
  | unmatched K term frames pending none =>
      simpa [branch] using
        (Move.unmatched (D := D) (P := P) (supply := supply) world K term (frames ++ [frame]) pending none)
  | letStart K site pattern bound body frames pending =>
      simpa [branch] using
        (Move.letStart (D := D) (P := P) (supply := supply) world K site pattern bound body
          (frames ++ [frame]) pending)
  | letBind K value site pattern body frames pending =>
      simpa [branch] using
        (Move.letBind (D := D) (P := P) (supply := supply) world K value site pattern body
          (frames ++ [frame]) pending)
  | choice K left right frames pending =>
      simpa [branch] using
        (Move.choice (D := D) (P := P) (supply := supply) world K left right (frames ++ [frame]) pending)
  | fail K frames pending =>
      simpa [branch] using
        (Move.fail (D := D) (P := P) (supply := supply) world K (frames ++ [frame]) pending)
  | run | query | add | remove | removeAbsent | new | checkStart | delay | forcePending | forceDone =>
      simp [ArrowBranch, ArrowComp] at arrow
  | admitted | refused | memo => simp [ArrowBranch, ArrowFrames] at arrow

theorem children_arrows (arrowP : ArrowProgram P)
    {world nextWorld : World κ Γ star} {before : Branch κ Γ star D.Ty}
    {children : Multiset (Branch κ Γ star D.Ty)}
    (arrow : ArrowBranch before) (moved : Move D P supply world before nextWorld children) :
    ∀ child ∈ children, ArrowBranch child := by
  intro child member
  obtain ⟨frames, focus⟩ := arrow
  cases moved with
  | ret =>
      rw [Multiset.mem_singleton] at member
      subst child
      exact ⟨frames, .inr ⟨_, rfl⟩⟩
  | apply K term fs pending _ =>
      obtain ⟨clause, inside, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      exact ⟨frames, .inl ⟨_, rfl, arrowComp_mapData _ _ (arrowP clause inside)⟩⟩
  | unmatched =>
      rw [Multiset.mem_singleton] at member
      subst child
      exact ⟨frames, .inr ⟨_, rfl⟩⟩
  | letStart K site pattern bound body fs pending =>
      rw [Multiset.mem_singleton] at member
      subst child
      obtain ⟨boundArrow, bodyArrow⟩ := arrow_eval focus
      exact ⟨⟨bodyArrow, frames⟩, .inl ⟨_, rfl, boundArrow⟩⟩
  | letBind =>
      rw [Multiset.mem_singleton] at member
      subst child
      exact ⟨frames.2, .inl ⟨_, rfl, arrowComp_mapData _ _ frames.1⟩⟩
  | choice =>
      obtain ⟨leftArrow, rightArrow⟩ := arrow_eval focus
      rcases Multiset.mem_cons.mp member with rfl | later
      · exact ⟨frames, .inl ⟨_, rfl, leftArrow⟩⟩
      · rw [Multiset.mem_singleton] at later
        subst child
        exact ⟨frames, .inl ⟨_, rfl, rightArrow⟩⟩
  | fail => cases member
  | run | query | add | remove | removeAbsent | new | checkStart | delay | forcePending | forceDone =>
      exact False.elim (by simpa [ArrowComp] using arrow_eval focus)
  | admitted | refused | memo => simp [ArrowFrames] at frames

def ArrowConfiguration (current : Config κ Γ star D.Ty) : Prop :=
  ∀ before ∈ current.branches, ArrowBranch before

theorem step_arrows (arrowP : ArrowProgram P) {before after : Config κ Γ star D.Ty}
    (arrows : ArrowConfiguration D before) (edge : SourceLanguage.Step D P supply before after) :
    ArrowConfiguration D after := by
  cases edge with
  | move world nextWorld current rest children live moved =>
      intro child member
      rcases Multiset.mem_add.mp member with made | old
      · exact children_arrows D P supply arrowP (arrows _ (Multiset.mem_cons_self _ _)) moved child made
      · exact arrows child (Multiset.mem_cons_of_mem old)

theorem runs_arrows (arrowP : ArrowProgram P) {before after : Config κ Γ star D.Ty}
    (arrows : ArrowConfiguration D before) (executed : Runs D P supply before after) :
    ArrowConfiguration D after := by
  induction executed with
  | refl => exact arrows
  | tail _ edge ih => exact step_arrows D P supply arrowP ih edge

theorem step (frame : Frame κ Γ star D.Ty) {before after : Config κ Γ star D.Ty}
    (arrows : ArrowConfiguration D before) (edge : SourceLanguage.Step D P supply before after) :
    SourceLanguage.Step D P supply (configuration frame before) (configuration frame after) := by
  cases edge with
  | move world nextWorld current rest children live moved =>
      have lifted := SourceLanguage.Step.move (D := D) (P := P) (supply := supply) world nextWorld
        (branch frame current) (rest.map (branch frame)) (children.map (branch frame)) live
        (move D P supply frame (arrows _ (Multiset.mem_cons_self _ _)) moved)
      simpa only [configuration, Multiset.map_cons, Multiset.map_add] using lifted

theorem runs (arrowP : ArrowProgram P) (frame : Frame κ Γ star D.Ty)
    {before after : Config κ Γ star D.Ty} (arrows : ArrowConfiguration D before)
    (executed : Runs D P supply before after) :
    Runs D P supply (configuration frame before) (configuration frame after) := by
  induction executed with
  | refl => exact .refl
  | tail previous edge ih =>
      exact ih.tail (step D P supply frame (runs_arrows D P supply arrowP arrows previous) edge)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalFrameTransport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalFrameTransport.runs
