import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredClassifiedReduction

/-!
# Program and absence controls for authored terms-only presentations

The empty rule inventory has no root constructor in the existing firing
trees. An empty equation inventory leaves actual terms distinct. The
represented program carrier reads the independently constructed classified
model's quotient terms at every clone context.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedAuthoredTermsOnlyControls

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open IntrinsicScopedLocalPolynomial (LocalRule Tree rules)
open IntrinsicScopedAuthoredClassifiedInstance (treeModel algebra model)
open IntrinsicScopedConditionalPresheaf (Base programsAtEquiv)
open IntrinsicScopedOperationalPresheafEvents (events eventAtEquiv)
open AuthoredPositionedRulePolynomial (Judgment)

universe u
variable {S : Signature} {schema : List (MetaArity S)}

/-- Every firing tree has an authored root, so the empty inventory has none. -/
theorem no_tree (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A) :
    ¬ Nonempty (Tree ([] : List (LocalRule S)) A j) := by
  rintro ⟨tree⟩
  obtain ⟨shape, _⟩ := Mettapedia.TypeTheory.IndexedPolynomial.Fix.out
    (rules ([] : List (LocalRule S)) A) tree
  exact shape.1.index.elim0

/-- The actual contextual event object has no section at any clone stage. -/
theorem no_event (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) (s : S.Srt) (X : Base A)
    (event : (events (treeModel ([] : List (LocalRule S)) A).toAction Γ s).obj X) :
    False :=
  no_tree A _ ⟨(eventAtEquiv
    (treeModel ([] : List (LocalRule S)) A).toAction Γ s X event).2⟩

/-- Genuine interpreted reduction sections require an original authored firing tree. -/
theorem no_extended_reduction (equations : List (EqAxiom S schema))
    {Γ : Ctx S} {s : S.Srt} (source target : Term S Γ s) :
    ¬ IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction
      ([] : List (LocalRule S)) equations source target := by
  intro firing
  exact no_tree (algebra equations) _
    ((IntrinsicScopedAuthoredClassifiedReduction.extension_iff_tree
      ([] : List (LocalRule S)) equations source target).mp firing)

/-- The classified model's represented program at an actual clone context. -/
def programAtEquiv (R : List (LocalRule S)) (equations : List (EqAxiom S schema))
    (Γ : Ctx S) (s : S.Srt) :
    ((model R equations).programModel.sort s).obj
        (Opposite.op (ContextObject.ofList (algebra equations).substitution.toClone Γ)) ≃
      TermQ equations Γ s :=
  programsAtEquiv (algebra equations) s _

end Mettapedia.OSLF.Binding.IntrinsicScopedAuthoredTermsOnlyControls
