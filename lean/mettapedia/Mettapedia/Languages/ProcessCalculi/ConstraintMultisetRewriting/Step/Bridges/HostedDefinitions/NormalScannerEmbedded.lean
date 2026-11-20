import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalFrameReflection

/-!
# Scanner certificates beneath real enclosing source frames

A running scanner step can be reflected through an appended continuation.
Its actual children retain both their inner certificate and the enclosing
frame. The finished inner marker is a separate boundary: it certifies the
native term and lets the enclosing computation consume that result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerEmbedded

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child)
open NormalScannerCertificates (Certificate)
open ContinuationLift (branch)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

theorem arrowFrames_of_append
    (inside outside : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (known : ArrowFrames (inside ++ outside)) : ArrowFrames inside := by
  induction inside with
  | nil => trivial
  | cons first rest ih =>
      cases first with
      | bindTo site pattern body => exact ⟨known.1, ih known.2⟩
      | checkAt _ | memo _ => exact known.elim

theorem arrow_inner (frame : Frame (BinderCore.keys built.rules) [] () D.Ty)
    (before : Branch (BinderCore.keys built.rules) [] () D.Ty)
    (known : ArrowBranch (branch frame before)) : ArrowBranch before :=
  ⟨arrowFrames_of_append built D before.frames [frame] known.1, known.2⟩

theorem fresh_inner {scope : Nat} (frame : Frame (BinderCore.keys built.rules) [] () D.Ty)
    (before : Branch (BinderCore.keys built.rules) [] () D.Ty)
    (fresh : NormalScannerReflection.FreshCalls built D scope (branch frame before)) :
    NormalScannerReflection.FreshCalls built D scope before := fresh

theorem move {outer : Child}
    (frame : Frame (BinderCore.keys built.rules) [] () D.Ty)
    {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {before : Branch (BinderCore.keys built.rules) [] () D.Ty}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (known : Certificate built D outer before)
    (arrow : ArrowBranch (branch frame before))
    (running : ¬ before.Finished (D := D))
    (fresh : NormalScannerReflection.FreshCalls built D world.scope (branch frame before))
    (moved : Move D (NormalProgram.program built D) supply world (branch frame before) nextWorld children) :
    ∀ child ∈ children, Solvable child.store →
      ∃ inside, child = branch frame inside ∧ Certificate built D outer inside := by
  obtain ⟨innerChildren, innerMove, same⟩ := NormalFrameReflection.move D (NormalProgram.program built D) supply
    frame (arrow_inner built D frame before arrow) running moved
  intro child member live
  rw [same] at member
  obtain ⟨inside, included, rfl⟩ := Multiset.mem_map.mp member
  exact ⟨inside, rfl, NormalScannerReflection.move built D supply known
    (fresh_inner built D frame before fresh) innerMove inside included live⟩

theorem finished {outer : Child} {before : Branch (BinderCore.keys built.rules) [] () D.Ty}
    (known : Certificate built D outer before) (done : before.Finished (D := D)) :
    NormalStructure.Normal built outer.2 :=
  NormalScannerCertificates.finished_normal built D known done

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerEmbedded

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerEmbedded.move
