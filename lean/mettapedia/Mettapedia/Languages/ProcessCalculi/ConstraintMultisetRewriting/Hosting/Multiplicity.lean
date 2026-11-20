import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Rules

/-!
# Programs are bags at the source and sets at the step

A program of the source is a list of equations, and a call makes one alternative per equation, so two
equations that differ only in their binder site make two alternatives with the same answers.
A program of the step (`RuleSyntax.Program`) is a set of rules, and an equation's schema does not
mention its site. So two such equations have one schema (`schema_site_free`), the translation of the
program with both is the translation with one (`translate_duplicate`), and the step's run tree has
one branch where the source has two alternatives.

The frontier theorems still count both (`Frontier` is a multiset of states, and both alternatives are
represented by states reached by the same firing), so `frontier_answers` holds as stated: the
frontier's multiplicities are those of the source's live alternatives. What fails is reading an
answer's multiplicity as a number of distinct runs of the step. This is decided by the definition of
`RuleSyntax.Program`, not by the translation.

`source_duplicate_card` counts the alternatives a call makes, dead ones included. That the source's
bag of answers has the duplicate is `Answers.Bags.p2_answers`; where the step determines the bag (the
first fragment, equations with pairwise distinct schemas) is `Alternatives.bag_of_rule_classes`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {Ty : Type}

/-- An equation's schema does not depend on its site. -/
theorem schema_site_free (s₁ s₂ : κ.Site) (lhs : Data κ Γ star) (rhs : Comp κ Γ star Ty) :
    schema N (⟨s₁, lhs, rhs⟩ : SourceLanguage.Equation κ Γ star Ty) = schema N ⟨s₂, lhs, rhs⟩ :=
  rfl

/-- **The step does not see an equation's multiplicity**: adding an equation that differs from one of
the program's only in its site does not change the translation. -/
theorem translate_duplicate (P : SourceLanguage.Program κ Γ star Ty) {e : SourceLanguage.Equation κ Γ star Ty}
    (member : e ∈ P.equations) (s : κ.Site) :
    translate N ⟨P.equations ++ [⟨s, e.lhs, e.rhs⟩], P.reflect⟩ = translate N P := by
  ext r
  constructor
  · rintro (control | ⟨e', member', rfl⟩)
    · exact .inl control
    · rcases List.mem_append.mp member' with old | new
      · exact .inr ⟨e', old, rfl⟩
      · rw [List.mem_singleton.mp new]
        exact .inr ⟨e, member, schema_site_free N s e.site e.lhs e.rhs⟩
  · rintro (control | ⟨e', member', rfl⟩)
    · exact .inl control
    · exact .inr ⟨e', List.mem_append_left _ member', rfl⟩

/-- **The source makes one alternative per equation**: the program with the duplicate makes one more
alternative than the program without it. This counts the alternatives a call makes, live or dead; it
is not a statement about answers (for those, `Answers.Bags.p2_answers`). -/
theorem source_duplicate_card (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
    (e : SourceLanguage.Equation κ Γ star D.Ty) (n : ℕ) (K : List (Constraint κ Γ star)) (t : Data κ Γ star)
    (fs : List (SourceLanguage.Frame κ Γ star D.Ty)) (ps : List (Data κ Γ star × Comp κ Γ star D.Ty)) :
    (((P.equations ++ [e]).map (callBranch D n K t fs ps) : List (Branch κ Γ star D.Ty)) :
        Multiset (Branch κ Γ star D.Ty)).card =
      ((P.equations.map (callBranch D n K t fs ps) : List (Branch κ Γ star D.Ty)) :
        Multiset (Branch κ Γ star D.Ty)).card + 1 := by
  simp

#print axioms schema_site_free
#print axioms translate_duplicate
#print axioms source_duplicate_card

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
