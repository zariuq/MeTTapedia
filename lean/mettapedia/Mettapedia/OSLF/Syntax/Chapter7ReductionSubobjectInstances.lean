import Mettapedia.OSLF.Syntax.LambdaIntrinsicPresentation
import Mettapedia.OSLF.Syntax.JsonTermRung
import Mettapedia.OSLF.Syntax.MonoidEquationRung
import Mettapedia.OSLF.Syntax.ContextualReductionSubobject

/-!
# The Chapter 7 ladder in the reduction-subobject model

The JSON and monoid rungs have no authored reduction events, even though the
monoid has nontrivial equations. The lambda rung has a concrete beta event.
The ambient presheaf construction retains event witnesses before taking their
endpoint image; this comparison does not claim that the presheaf model is the
free finite-limit cartesian-closed classifying category.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Chapter7ReductionSubobjectInstances

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaIntrinsicPresentation
open Mettapedia.OSLF.Binding.ContextualReductionSubobject

/-- The closed identity abstraction used as both function and argument. -/
def identity : Term sig [] .term := lamT (.var .zero)

/-- Its application is an actual firing of the generic beta schema. -/
theorem identity_beta_root :
    betaRule.RootStep (appT identity identity) identity := by
  have firing :=
    beta_root_instance (Term.var (Var.zero : Var [Srt.term] Srt.term)) identity
  exact firing

/-- Select the root occurrence, rather than merely citing beta reduction. -/
theorem identity_beta_contextual :
    betaRule.Step (appT identity identity) identity := by
  refine ⟨.var .zero, appT identity identity, identity, ?_,
    identity_beta_root, ?_, ?_⟩
  · rfl
  · exact inst_hole _
  · exact inst_hole _

/-- The closed beta event survives the equation-class endpoint map. -/
theorem identity_beta_stepModE :
    betaPresentation.StepModE (appT identity identity) identity := by
  refine ⟨⟨0, by decide⟩, appT identity identity, identity,
    EqClosure.refl _, ?_, EqClosure.refl _⟩
  exact identity_beta_contextual

/-- The source's behavior rung has a real inhabitant in the semantic
reduction subobject. -/
theorem identity_beta_member :
    (stepSubfunctor betaPresentation Srt.term).obj
      (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx sig)))
      (Quotient.mk (eqSetoid betaPresentation.eqs [] Srt.term)
          (appT identity identity),
       Quotient.mk (eqSetoid betaPresentation.eqs [] Srt.term) identity) := by
  exact (closed_membership_iff_stepModE betaPresentation Srt.term
    (appT identity identity) identity).mpr identity_beta_stepModE

/-- The equations-only source rung retains its three equations and has no
operational generators. -/
def monoidPresentation : UnpositionedPresentation
    Mettapedia.OSLF.Binding.MonoidEquationRung.sig where
  metas := Mettapedia.OSLF.Binding.MonoidEquationRung.metas
  eqs := Mettapedia.OSLF.Binding.MonoidEquationRung.monoidE
  rules := []

theorem monoid_no_reduction_member
    (X : (Syntactic.Ctxt Mettapedia.OSLF.Binding.MonoidEquationRung.sig)ᵒᵖ)
    (pair : (pairPresheaf monoidPresentation
      Mettapedia.OSLF.Binding.MonoidEquationRung.Srt.element).obj X) :
    ¬ (stepSubfunctor monoidPresentation
      Mettapedia.OSLF.Binding.MonoidEquationRung.Srt.element).obj X pair :=
  no_membership_of_empty_rules monoidPresentation rfl X _ pair

/-- A terms-only JSON presentation also has no operational endpoint pair,
including at open contexts. -/
theorem json_no_reduction_member
    (X : (Syntactic.Ctxt Mettapedia.OSLF.Binding.JsonTermRung.sig)ᵒᵖ)
    (pair : (pairPresheaf Mettapedia.OSLF.Binding.JsonTermRung.termsOnly
      Mettapedia.OSLF.Binding.JsonTermRung.Srt.value).obj X) :
    ¬ (stepSubfunctor Mettapedia.OSLF.Binding.JsonTermRung.termsOnly
      Mettapedia.OSLF.Binding.JsonTermRung.Srt.value).obj X pair :=
  no_membership_of_empty_rules _ rfl X _ pair

end Mettapedia.OSLF.Binding.Chapter7ReductionSubobjectInstances
