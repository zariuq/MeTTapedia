import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowChildren
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.StepAlone

/-!
# The arrow catalogue covers the actual translated native rule program

The generic catalogue may select a profile. This concrete catalogue covers
all rules of the translated arrow program, and every actual admitted firing
at a represented state has a catalogue name and an invocation with the very
same firing. Distinct raw openings may still share one name; this is coverage,
not a bijection of raw firing witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)

theorem catalogue_complete {rule : CRule S} (member : rule ∈ translate N P) :
    ∃ name, (catalogue N P).lookup name = some rule := by
  rcases (mem_translate N).mp member with control | ⟨equation, equationMember, rfl⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.ret, rfl⟩
    · exact ⟨.unmatched, rfl⟩
    · exact ⟨.left, rfl⟩
    · exact ⟨.right, rfl⟩
    · exact ⟨.bindStart, rfl⟩
    · exact ⟨.bindValue, rfl⟩
  · obtain ⟨index, small, rfl⟩ := List.getElem_of_mem equationMember
    exact ⟨.eqn index, by simp [catalogue, lookup, List.getElem?_eq_getElem small]⟩

theorem raw_firing_named {world : World κ Γ star} {branch : Branch κ Γ star D.Ty} {leaf : Leaf S}
    (paired : LeafRep N P world branch leaf)
    (firing : RuleSyntax.Firing Nat (RuleSyntax.Contextual.declarations S) (translate N P) leaf.state.frame)
    (admitted : firing.Admits (Interface.Frames.contextual S) leaf.state) :
    ∃ name, ∃ invocation : Invocation N P leaf name, invocation.firing = firing := by
  let shaped : StepAlone.Shaped N P leaf.state leaf.active :=
    ⟨paired.1.notRow, paired.1.present, paired.1.rows⟩
  obtain ⟨active, taken, made, _⟩ := StepAlone.shaped_fires N shaped admitted
  obtain ⟨name, named⟩ := catalogue_complete N P firing.member
  exact ⟨name, ⟨firing, named, active, taken, made, admitted⟩, rfl⟩

theorem no_named_iff_no_raw {world : World κ Γ star} {branch : Branch κ Γ star D.Ty} {leaf : Leaf S}
    (paired : LeafRep N P world branch leaf) :
    (∀ name, ¬ Enabled N P leaf name) ↔
      ∀ firing : RuleSyntax.Firing Nat (RuleSyntax.Contextual.declarations S) (translate N P) leaf.state.frame,
        ¬ firing.Admits (Interface.Frames.contextual S) leaf.state := by
  constructor
  · intro none firing admitted
    obtain ⟨name, invocation, _⟩ := raw_firing_named N P paired firing admitted
    exact none name ⟨invocation⟩
  · rintro none name ⟨invocation⟩
    exact none invocation.firing invocation.admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow
