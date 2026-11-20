import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalFrameTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerSyntax

/-!
# A pending frame can be removed from a move of a running arrow branch

While the inner branch is running, appending a frame changes no source move:
the actual world, constraints, pending cells and generated siblings are kept.
A finished inner value is the boundary. Its appended frame may consume that
value, although the inner branch itself has no move. This module proves the
one-move law and that boundary, not an unrestricted inverse for whole runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalFrameReflection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting
open ContinuationLift (branch configuration)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
  (supply : Nat → Term S Γ star)

theorem move (frame : Frame κ Γ star D.Ty)
    {world nextWorld : World κ Γ star} {before : Branch κ Γ star D.Ty}
    {children : Multiset (Branch κ Γ star D.Ty)}
    (arrow : ArrowBranch before) (running : ¬ before.Finished (D := D))
    (moved : Move D P supply world (branch frame before) nextWorld children) :
    ∃ innerChildren, Move D P supply world before nextWorld innerChildren ∧
      children = innerChildren.map (branch frame) := by
  rcases before with ⟨K, focus, frames, pending⟩
  obtain ⟨arrowFrames, shape⟩ := arrow
  change ArrowFrames frames at arrowFrames
  rcases shape with ⟨comp, same, arrowComp⟩ | ⟨value, same⟩
  · change focus = Focus.eval comp at same
    subst focus
    cases comp with
    | ret datum =>
        cases moved with
        | ret =>
            refine ⟨{⟨K, .value datum, frames, pending⟩}, .ret world K datum frames pending, ?_⟩
            simp [branch]
    | apply term =>
        cases moved with
        | apply =>
            rename_i matched
            refine ⟨((P.equations.map (callBranch D world.scope K term frames pending)) : Multiset _),
              .apply world K term frames pending matched, ?_⟩
            exact (NormalFrameTransport.mapped_calls D P frame world.scope K term frames pending).symm
        | unmatched =>
            rename_i none
            refine ⟨{⟨K, .value term, frames, pending⟩}, .unmatched world K term frames pending none, ?_⟩
            simp [branch]
    | let_ site pattern bound body =>
        cases moved with
        | letStart =>
            refine ⟨{⟨K, .eval bound, .bindTo site pattern body :: frames, pending⟩},
              .letStart world K site pattern bound body frames pending, ?_⟩
            simp [branch]
    | choice left right =>
        cases moved with
        | choice =>
            refine ⟨{⟨K, .eval left, frames, pending⟩, ⟨K, .eval right, frames, pending⟩},
              .choice world K left right frames pending, ?_⟩
            simp [branch]
    | fail =>
        cases moved with
        | fail => exact ⟨0, .fail world K frames pending, by simp⟩
    | run | query | add | remove | new | check | delay | force =>
        exact False.elim arrowComp
  · change focus = Focus.value value at same
    subst focus
    cases frames with
    | nil => exact False.elim (running ⟨rfl, value, rfl⟩)
    | cons inner rest =>
        cases inner with
        | bindTo site pattern body =>
            cases moved with
            | letBind =>
                refine ⟨{⟨K ++ [(instantiate (openAt κ site world.scope) pattern, value)],
                    .eval (body.inst (openAt κ site world.scope)), rest, pending⟩},
                  .letBind world K value site pattern body rest pending, ?_⟩
                simp [branch]
        | checkAt | memo => exact False.elim arrowFrames

theorem move_iff (frame : Frame κ Γ star D.Ty)
    {world nextWorld : World κ Γ star} {before : Branch κ Γ star D.Ty}
    {children : Multiset (Branch κ Γ star D.Ty)}
    (arrow : ArrowBranch before) (running : ¬ before.Finished (D := D)) :
    Move D P supply world (branch frame before) nextWorld children ↔
      ∃ innerChildren, Move D P supply world before nextWorld innerChildren ∧
        children = innerChildren.map (branch frame) := by
  constructor
  · exact move D P supply frame arrow running
  · rintro ⟨innerChildren, innerMove, rfl⟩
    exact NormalFrameTransport.move D P supply frame arrow innerMove

section Controls

theorem ret_beneath_frame (frame : Frame κ Γ star D.Ty) (world : World κ Γ star)
    (K : List (Constraint κ Γ star)) (datum : Data κ Γ star)
    (frames : List (Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (arrowFrames : ArrowFrames frames) :
    ∃ innerChildren, Move D P supply world ⟨K, .eval (.ret datum), frames, pending⟩ world innerChildren ∧
      {⟨K, .value datum, frames ++ [frame], pending⟩} = innerChildren.map (branch frame) := by
  apply move D P supply frame (before := ⟨K, .eval (.ret datum), frames, pending⟩)
    ⟨arrowFrames, .inl ⟨_, rfl, trivial⟩⟩
  · rintro ⟨_, term, impossible⟩
    cases impossible
  · exact .ret world K datum (frames ++ [frame]) pending

theorem nested_let_start (frame : Frame κ Γ star D.Ty) (world : World κ Γ star)
    (K : List (Constraint κ Γ star)) (site : κ.Site) (pattern first second : Data κ Γ star) :
    ∃ innerChildren, Move D P supply world
        ⟨K, .eval (.let_ site pattern (.ret first) (.ret second)), [], []⟩ world innerChildren ∧
      {⟨K, .eval (.ret first), [.bindTo site pattern (.ret second), frame], []⟩} =
        innerChildren.map (branch frame) := by
  apply move D P supply frame (before := ⟨K, .eval (.let_ site pattern (.ret first) (.ret second)), [], []⟩)
    ⟨trivial, .inl ⟨_, rfl, ⟨trivial, trivial⟩⟩⟩
  · rintro ⟨_, term, impossible⟩
    cases impossible
  · exact .letStart world K site pattern (.ret first) (.ret second) [frame] []

theorem nested_let_bind (frame : Frame κ Γ star D.Ty) (world : World κ Γ star)
    (K : List (Constraint κ Γ star)) (site : κ.Site) (pattern value result : Data κ Γ star) :
    ∃ innerChildren, Move D P supply world
        ⟨K, .value value, [.bindTo site pattern (.ret result)], []⟩ world.fresh innerChildren ∧
      {⟨K ++ [(instantiate (openAt κ site world.scope) pattern, value)],
        .eval (.ret (instantiate (openAt κ site world.scope) result)), [frame], []⟩} =
        innerChildren.map (branch frame) := by
  apply move D P supply frame (before := ⟨K, .value value, [.bindTo site pattern (.ret result)], []⟩)
    ⟨⟨trivial, trivial⟩, .inr ⟨value, rfl⟩⟩
  · rintro ⟨impossible, _⟩
    cases impossible
  · exact .letBind world K value site pattern (.ret result) [frame] []

end Controls

section MarkerBoundary

variable {κ₀ : Keys SourceLanguage.Elaboration.MSig}
  (D₀ : Discipline SourceLanguage.Elaboration.MSig [] ())
  (P₀ : SourceLanguage.Program κ₀ [] () D₀.Ty)
  (supply₀ : Nat → SourceLanguage.Elaboration.MClosed)

theorem finished_marker_boundary (world : World κ₀ [] ()) (site : κ₀.Site) :
    let marker := NormalScanner.marker (fam κ₀)
    let before : Branch κ₀ [] () D₀.Ty := ⟨[], .value marker, [], []⟩
    let frame : Frame κ₀ [] () D₀.Ty := .bindTo site marker (.ret marker)
    ArrowBranch before ∧ before.Finished (D := D₀) ∧ Solvable before.store ∧
      ∃ children, Move D₀ P₀ supply₀ world (branch frame before) world.fresh children ∧
        ¬ ∃ innerChildren, Move D₀ P₀ supply₀ world before world.fresh innerChildren ∧
          children = innerChildren.map (branch frame) := by
  dsimp only
  have live : Solvable ([] : List (Constraint κ₀ [] ())) :=
    ⟨SourceLanguage.Name κ₀, fam κ₀, generator (fam κ₀), fun _ inside => by cases inside⟩
  refine ⟨⟨trivial, .inr ⟨_, rfl⟩⟩, ⟨rfl, _, rfl⟩, live, ?_⟩
  refine ⟨{⟨[(NormalScanner.marker (fam κ₀), NormalScanner.marker (fam κ₀))],
    .eval (.ret (NormalScanner.marker (fam κ₀))), [], []⟩}, ?_, ?_⟩
  · exact .letBind world [] (NormalScanner.marker (fam κ₀)) site
      (NormalScanner.marker (fam κ₀)) (.ret (NormalScanner.marker (fam κ₀))) [] []
  · rintro ⟨innerChildren, moved, _⟩
    exact Move.value_still moved

end MarkerBoundary

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalFrameReflection

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalFrameReflection.move
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalFrameReflection.finished_marker_boundary
