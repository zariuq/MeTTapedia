import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCore

/-!
# A pending continuation around an actual binder-core execution

Binder-core source branches only call equations or return an unmatched call.
Appending one continuation therefore transports every existing execution
step, while the machine's scope counter and knowledge are retained. The
continuation is executed only after such a call has returned a value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContinuationLift

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty : Type}

def branch (frame : Frame κ Γ star Ty) (before : Branch κ Γ star Ty) : Branch κ Γ star Ty :=
  {before with frames := before.frames ++ [frame]}

def configuration (frame : Frame κ Γ star Ty) (before : Config κ Γ star Ty) : Config κ Γ star Ty :=
  ⟨before.world, before.branches.map (branch frame)⟩

theorem mapped_calls (D : Discipline S Γ star) (P : Program κ Γ star D.Ty)
    (frame : Frame κ Γ star D.Ty) (scope : Nat) (store : List (Constraint κ Γ star))
    (term : Data κ Γ star) :
    (((P.equations.map (callBranch D scope store term [] [])) : Multiset (Branch κ Γ star D.Ty)).map
      (branch frame)) =
      ((P.equations.map (callBranch D scope store term [frame] [])) : Multiset (Branch κ Γ star D.Ty)) := by
  simp [branch, callBranch, List.map_map, Function.comp_def]
  exact List.Perm.refl _

theorem apply_move (D : Discipline S Γ star) (P : Program κ Γ star D.Ty)
    (supply : Nat → Term S Γ star) (frame : Frame κ Γ star D.Ty)
    {world afterWorld : World κ Γ star} {store : List (Constraint κ Γ star)}
    {term : Data κ Γ star} {children : Multiset (Branch κ Γ star D.Ty)}
    (moved : Move D P supply world ⟨store, .eval (.apply term), [], []⟩ afterWorld children) :
    Move D P supply world ⟨store, .eval (.apply term), [frame], []⟩ afterWorld
      (children.map (branch frame)) := by
  cases moved with
  | apply =>
      rw [mapped_calls]
      exact .apply _ _ _ _ _ (by assumption)
  | unmatched =>
      simpa [branch] using
        (Move.unmatched (D := D) (P := P) (supply := supply) world store term [frame] [] (by assumption))

variable (rows : List (ProgramBinders.Equation S Γ star)) (D : Discipline S Γ star)
  (supply : Nat → Term S Γ star) (frame : Frame (BinderCore.keys rows) Γ star D.Ty)

theorem step {call : Term S Γ star} {before after : Config (BinderCore.keys rows) Γ star D.Ty}
    (shape : BinderCore.Invariant rows D call before)
    (moved : SourceLanguage.Step D (BinderCore.program rows) supply before after) :
    SourceLanguage.Step D (BinderCore.program rows) supply
      (configuration frame before) (configuration frame after) := by
  cases moved with
  | move world afterWorld old rest children live moved =>
      obtain ⟨store, term, forms, _⟩ := shape old (Multiset.mem_cons_self _ _)
      rcases forms with rfl | rfl
      · have framed := SourceLanguage.Step.move (D := D) (P := BinderCore.program rows) (supply := supply)
          world afterWorld ⟨store, .eval (.apply term), [frame], []⟩
          (rest.map (branch frame)) (children.map (branch frame)) live
          (apply_move D (BinderCore.program rows) supply frame moved)
        simpa only [configuration, Multiset.map_cons, Multiset.map_add, branch, List.nil_append] using framed
      · cases moved

theorem runs [ProgramBinders.ClosedTerms S] {call : Term S Γ star}
    {after : Config (BinderCore.keys rows) Γ star D.Ty}
    (executed : Runs D (BinderCore.program rows) supply (BinderCore.start rows call) after) :
    Runs D (BinderCore.program rows) supply
      (configuration frame (BinderCore.start rows call)) (configuration frame after) := by
  induction executed with
  | refl => exact .refl
  | tail previous last ih =>
      exact ih.tail (step rows D supply frame (BinderCore.invariant_runs rows D supply previous) last)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContinuationLift

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContinuationLift.runs
