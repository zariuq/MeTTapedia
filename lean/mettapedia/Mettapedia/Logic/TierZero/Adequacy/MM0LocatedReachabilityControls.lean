import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedInstalledAdequacy
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingControls
import Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInstallationControls

/-!
# Complete protected execution, dependency and installation controls

The positive case has a genuine bound formal and independence-sensitive
theorem application. The negative case has a closed well-typed conclusion
but no supplied initial proof; installing its actually derived schema does
not make it an axiom. Printed request names never authorize protected reads.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedReachabilityControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open MM0Rewriting

theorem dependency_sensitive_nf_has_an_actual_protected_system_run :
    MM0LocatedReachability.Reaches CatalogControls.theory TheoremControls.independentContext [] TheoremControls.goal :=
  MM0LocatedReachability.reaches_complete CatalogControls.theory_formed CatalogControls.target_formed
    [] TheoremControls.goal CatalogControls.independent_nf_derivation

theorem a_request_called_pf_is_still_unprotected (arguments : List Tm) :
    MM0LocatedCatalogShapes.layout (requestValue "pf" arguments) = .requests :=
  MM0LocatedCatalogShapes.request_layout _ _

theorem a_request_called_cv_is_still_unprotected (arguments : List Tm) :
    MM0LocatedCatalogShapes.layout (requestValue "cv" arguments) = .requests :=
  MM0LocatedCatalogShapes.request_layout _ _

theorem public_proof_shape_does_not_supply_a_physical_read :
    ¬MM0LocatedKernelControls.forgedSelection.Valid
      (MM0LocatedActivation.action MM0LocatedKernelControls.target) MM0LocatedKernelControls.label
      (MM0LocatedActivation.locate MM0LocatedKernelControls.raw) MM0LocatedKernelControls.forgedBefore :=
  MM0LocatedKernelControls.unprotected_forgery_cannot_supply_the_protected_read

theorem the_closed_local_schema_has_a_protected_run_with_its_premise :
    MM0LocatedReachability.Reaches MM0LocatedKernelControls.theory MM0LocatedKernelControls.target
      [.var 0] (.term 0) :=
  MM0LocatedReachability.reaches_complete MM0LocatedKernelControls.theory_formed
    MM0LocatedKernelControls.target_formed [.var 0] (.term 0)
    MM0SchemaInstallationControls.independent_symbolic_derivation

theorem the_closed_local_schema_has_no_protected_run_without_its_premise :
    ¬MM0LocatedReachability.Reaches MM0LocatedKernelControls.theory MM0LocatedKernelControls.target [] (.term 0) := by
  intro accepted
  exact MM0SchemaInstallationControls.primitive_theory_has_no_proof_without_a_supplied_hypothesis _ _
    (MM0LocatedReachability.reaches_sound MM0LocatedKernelControls.theory_formed
      MM0LocatedKernelControls.target_formed [] (.term 0) accepted)

theorem installed_schema_preserves_the_actual_protected_acceptance_relation
    {target : Context} (formed : Context.WellFormed MM0LocatedKernelControls.theory.sortSignature target)
    (hypotheses : List Preterm) (expression : Preterm) :
    MM0LocatedReachability.Reaches MM0SchemaInstallationControls.installation.installed target hypotheses expression ↔
      MM0LocatedReachability.Reaches MM0LocatedKernelControls.theory target hypotheses expression :=
  MM0LocatedInstalledAdequacy.installed_located_reaches_iff_base MM0SchemaInstallationControls.installation
    MM0LocatedKernelControls.theory_formed formed hypotheses expression

theorem installing_the_closed_schema_still_cannot_publish_it_without_the_used_premise :
    ¬MM0LocatedReachability.Reaches MM0SchemaInstallationControls.installation.installed
      MM0LocatedKernelControls.target [] (.term 0) := by
  intro accepted
  exact the_closed_local_schema_has_no_protected_run_without_its_premise
    ((installed_schema_preserves_the_actual_protected_acceptance_relation
      MM0LocatedKernelControls.target_formed [] (.term 0)).mp accepted)

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedReachabilityControls
