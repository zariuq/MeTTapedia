import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidual

/-!
# Apart live firings leave each other clear

R81's independence of native firings (`NativeFiring.Apart`, `Step/NativeDiamond`) asks for disjoint
takes and ports, no take of what the other reads, and blindness of each to the other's takes and makes
at every solution of its own information, read with the state's rows. A residual at the published
result needs two more things (`Clear`): a **joint solution** of the two informations, and blindness to
the other's **published** outputs at joint solutions (the state's row at an identity the other makes is
not the row it publishes there).

* **Apart, joint consistency and blindness to published outputs give clearance**
  (`Clear.ofApart`): R81's blindness to the other's takes, at every solution, gives it at the joint
  solutions; pattern queries see exactly the occurrences whose rows match.
* So **apart live firings stay admitted after each other** (`LiveFiring.each_after_of_apart`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {s : NativeState S O Γ sort}

namespace Clear

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Apart live firings with a joint solution, blind to each other's published outputs, leave each
other clear.** -/
theorem ofApart {f g : LiveFiring s} (apart : f.toNative.Apart g.toNative)
    (consistent : ∃ b : Frames.Frame S,
      Nonempty (Joint s f.toNative.information (problemOf s g.selection g.rule) b))
    (blindOutputs : ∀ (b : Frames.Frame S) (J : Joint s f.toNative.information (problemOf s g.selection g.rule) b),
      ∀ o ∈ g.selection.made,
        (∀ check ∈ f.toNative.prepared.rule.checks, ¬ SeesOutput J.left J.right (g.outputs o) check) ∧
        ∀ pattern ∈ f.patterns, instantiate J.left pattern.1 ≠ instantiate J.right (g.outputs o)) :
    Clear f g.selection g.rule g.outputs where
  takes := apart.takes
  ports := apart.ports
  keeps := apart.keepsLeft
  consistent := consistent
  blindTakes := by
    intro b J o taken
    have blind := apart.blindLeft b J.left J.left_models o (Or.inl taken)
    refine ⟨blind.1, fun pattern member seen => ?_⟩
    have unseen := blind.2 _ (List.mem_map_of_mem member)
    simp only [ContextualPredicateQueryAdmission.matchingQuery, decide_eq_false_iff_not] at unseen
    exact unseen seen
  blindOutputs := blindOutputs

end Clear

namespace LiveFiring

/-- **Apart live firings stay admitted after each other**, given joint solutions and blindness to each
other's published outputs. -/
theorem each_after_of_apart {f g : LiveFiring s} (first : f.toNative.Realized) (second : g.toNative.Realized)
    (apart : f.toNative.Apart g.toNative)
    (consistentF : ∃ b : Frames.Frame S,
      Nonempty (Joint s f.toNative.information (problemOf s g.selection g.rule) b))
    (consistentG : ∃ b : Frames.Frame S,
      Nonempty (Joint s g.toNative.information (problemOf s f.selection f.rule) b))
    (blindF : ∀ (b : Frames.Frame S) (J : Joint s f.toNative.information (problemOf s g.selection g.rule) b),
      ∀ o ∈ g.selection.made,
        (∀ check ∈ f.toNative.prepared.rule.checks, ¬ SeesOutput J.left J.right (g.outputs o) check) ∧
        ∀ pattern ∈ f.patterns, instantiate J.left pattern.1 ≠ instantiate J.right (g.outputs o))
    (blindG : ∀ (b : Frames.Frame S) (J : Joint s g.toNative.information (problemOf s f.selection f.rule) b),
      ∀ o ∈ f.selection.made,
        (∀ check ∈ g.toNative.prepared.rule.checks, ¬ SeesOutput J.left J.right (f.outputs o) check) ∧
        ∀ pattern ∈ g.patterns, instantiate J.left pattern.1 ≠ instantiate J.right (f.outputs o)) :
    (residual second f).Realized ∧ (residual first g).Realized :=
  each_after first second (Clear.ofApart apart consistentF blindF) (Clear.ofApart apart.symm consistentG blindG)

end LiveFiring

#print axioms Clear.ofApart
#print axioms LiveFiring.each_after_of_apart

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
