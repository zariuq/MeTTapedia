import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedProcess
import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentControls
import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintReachesControls

/-!
# Actual natural request activation and full-catalog reachability controls

The dependency-sensitive theorem is reachable through the natural activation
path. Its forbidden dependency prevents formation of an activated instance,
rather than becoming a later true/false dependency check. Empty theories still
cannot publish proofs.

Ordinary constructor application may repeat bound images. Its congruence
scheme keeps the original constructor check and is not given theorem-
substitution independence conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ScopedProcessControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open MM0ContextualSupport
open MM0Rewriting

theorem independent_nf_has_a_natural_activated_instance :
    (MM0ScopedRequestActivation.activate TheoremControls.signature TheoremControls.nf.arguments
      TheoremControls.independentContext "apply-nf"
      (TheoremControls.nf.hypotheses.map (proofPattern TheoremControls.independentContext.length))
      (proofPattern TheoremControls.independentContext.length TheoremControls.nf.conclusion)
      TheoremControls.arguments).isSome = true := by decide +kernel

theorem dependent_nf_cannot_form_a_natural_instance :
    MM0ScopedRequestActivation.activate TheoremControls.signature TheoremControls.nf.arguments
      TheoremControls.dependentContext "apply-nf"
      (TheoremControls.nf.hypotheses.map (proofPattern TheoremControls.dependentContext.length))
      (proofPattern TheoremControls.dependentContext.length TheoremControls.nf.conclusion)
      TheoremControls.arguments = none := by decide +kernel

theorem full_natural_catalog_reaches_the_admitted_nf_theorem :
    MM0ScopedProcess.Reaches CatalogControls.theory TheoremControls.independentContext [] TheoremControls.goal :=
  (MM0ScopedProcess.scoped_reaches_iff_derives CatalogControls.theory_formed CatalogControls.target_formed []
    TheoremControls.goal).mpr CatalogControls.independent_nf_derivation

theorem empty_theory_still_cannot_publish (expression : Preterm) :
    ¬MM0ScopedProcess.Reaches ({} : Theory) [] [] expression := by
  intro accepted
  have formed : Context.WellFormed ({} : Theory).sortSignature [] := .nil []
  exact MM0ConstraintReachesControls.empty_theory_cannot_publish_a_proof expression
    ((MM0ScopedProcess.reaches_iff_compatibility formed [] expression).mp accepted)

def constructorDeclaration : TermDecl := ⟨[.bound 0, .bound 0, .regular 0 {0, 1}], 0, ∅⟩

def constructorTheory : Theory where
  sorts := [(0, {})]
  terms := [(0, constructorDeclaration)]

def repeatedBoundApplication : Preterm :=
  .applyArgs (.term 0) [.var 0, .var 0, .var 2]

def congruenceArguments : List Preterm :=
  [.var 0, .var 0, .var 2, .var 0, .var 0, .var 2]

theorem ordinary_constructor_application_keeps_repeated_bound_images :
    Preterm.infer constructorTheory.termSignature MM0ScopedArgumentControls.dependentTarget repeatedBoundApplication =
      some ([], 0) := by decide +kernel

theorem constructor_congruence_keeps_its_distinct_data_obligation :
    (MM0ConstraintCatalog.congruenceSchema constructorTheory.termSignature
      MM0ScopedArgumentControls.dependentTarget 0 constructorDeclaration).dataCondition
      (expressionAssignment MM0ScopedArgumentControls.dependentTarget congruenceArguments) = true := by decide +kernel

theorem constructor_congruence_activates_without_theorem_independence :
    (MM0ScopedCatalogActivation.activate constructorTheory MM0ScopedArgumentControls.dependentTarget
      (.congruence 0) congruenceArguments).isSome = true := by decide +kernel

end Mettapedia.Logic.TierZero.Adequacy.MM0ScopedProcessControls
