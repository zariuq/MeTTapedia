import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeCore

/-!
# Actual native runs supplied by every catalogue expansion

Each invocation is one firing of the original RuleSyntax step, with its
actual event record and resulting knowledge. An expansion is a family of
such alternative runs from one input representative, rather than repeated
consumption of its active occurrence by a single sequential run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNativeCore

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Hosting Hosting.Alternatives

variable {S : Signature} {Name : Type} {Prog : CProgram S}
  (catalogue : Catalogue Prog Name)

abbrev nativeStep (Prog : CProgram S) := (RuleSyntax.step (Interface.Frames.contextual S) Nat
  (RuleSyntax.Contextual.declarations S) Prog).toStep

def Invocation.run {before : Leaf S} {name : Name} (invocation : Invocation catalogue before name) :
    (nativeStep Prog).Run before.state :=
  .cons invocation.firing invocation.admitted (.nil _)

theorem Invocation.run_last {before : Leaf S} {name : Name} (invocation : Invocation catalogue before name) :
    (invocation.run catalogue).last = invocation.after.state := rfl

theorem Invocation.run_word {before : Leaf S} {name : Name} (invocation : Invocation catalogue before name) :
    (invocation.run catalogue).word = [⟨before.state, invocation.firing⟩] := rfl

theorem Invocation.result_knowledge {before : Leaf S} {name : Name} (invocation : Invocation catalogue before name) :
    invocation.after.state.knowledge =
      invocation.firing.information (Interface.Frames.contextual S) before.state := rfl

def Expansion.runs {before : Leaf S} (chosen : Expansion catalogue before) :
    (name : Name) → name ∈ chosen.names → (nativeStep Prog).Run before.state :=
  fun name member => (chosen.invocation name member).run catalogue

theorem Expansion.runs_one_firing {before : Leaf S} (chosen : Expansion catalogue before)
    (name : Name) (member : name ∈ chosen.names) :
    (chosen.runs catalogue name member).word.length = 1 := rfl

theorem Expansion.runs_deliver_children {before : Leaf S} (chosen : Expansion catalogue before) :
    chosen.names.attach.val.map (fun name => (chosen.runs catalogue name.1 name.2).last) =
      chosen.children.map Leaf.state := by
  rw [Expansion.children, Multiset.map_map]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNativeCore
