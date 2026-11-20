import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeCoreEffects

/-!
# Actual rule-step runs behind a native frontier expansion

Each invocation is one run of the existing RuleSyntax.step with its original
firing and knowledge. An expansion supplies one such run per indexed name.
These are alternative runs from the same input representative, not successive
consumptions of one shared occurrence.

The independent frontier frame law carries arbitrary other leaves unchanged.
It adds no consistency premise on their knowledge. Shared-store interaction
is not represented by this independent-leaf composition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)

abbrev nativeStep := (RuleSyntax.step (Interface.Frames.contextual S) Nat
  (RuleSyntax.Contextual.declarations S) (translate N P)).toStep

def Invocation.run {before : Leaf S} {name : RuleName} (invocation : Invocation N P before name) :
    (nativeStep N P).Run before.state :=
  FrontierNativeCore.Invocation.run (catalogue N P) invocation

theorem Invocation.run_last {before : Leaf S} {name : RuleName} (invocation : Invocation N P before name) :
    (invocation.run N P).last = invocation.after.state := rfl

theorem Invocation.run_word {before : Leaf S} {name : RuleName} (invocation : Invocation N P before name) :
    (invocation.run N P).word = [⟨before.state, invocation.firing⟩] := rfl

theorem Invocation.result_knowledge {before : Leaf S} {name : RuleName} (invocation : Invocation N P before name) :
    invocation.after.state.knowledge =
      invocation.firing.information (Interface.Frames.contextual S) before.state := rfl

def Expansion.runs {before : Leaf S} (chosen : Expansion N P before) :
    (name : RuleName) → name ∈ chosen.names → (nativeStep N P).Run before.state :=
  fun name member => Invocation.run N P (chosen.invocation name member)

theorem Expansion.runs_one_firing {before : Leaf S} (chosen : Expansion N P before)
    (name : RuleName) (member : name ∈ chosen.names) :
    (chosen.runs N P name member).word.length = 1 := rfl

theorem Expansion.runs_deliver_children {before : Leaf S} (chosen : Expansion N P before) :
    chosen.names.attach.val.map (fun name => (chosen.runs N P name.1 name.2).last) =
      chosen.children.map Leaf.state := by
  rw [Expansion.children, Multiset.map_map]
  rfl

theorem Step.frame {before after : State S} (moved : Step N P before after) (context : Multiset (Leaf S)) :
    Step N P ⟨before.leaves + context, before.retired⟩ ⟨after.leaves + context, after.retired⟩ :=
  FrontierNativeCore.Step.frame (catalogue N P) moved context

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Invocation.run_word
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Expansion.runs_deliver_children
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Step.frame
