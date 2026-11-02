import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedReachability
import Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInstallation

/-! # Conservatively installed schemas preserve actual located reachability -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedInstalledAdequacy

open Mettapedia.Languages.MM0.Kernel
open MM0Rewriting

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO} [DecidableEq O]
    {theory : Theory} {formal : Context} {location : O → Space}
    {system : MM0LocatedKernel.System theory formal C X I O location} {payload : O → Tm}

theorem installed_located_reaches_iff_base (installation : MM0SchemaInstallation.Installation system payload)
    (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm) :
    MM0LocatedReachability.Reaches installation.installed target hypotheses expression ↔
      MM0LocatedReachability.Reaches theory target hypotheses expression := by
  rw [MM0LocatedReachability.located_kernel_reaches_iff_derives (installation.installed_wellFormed wellFormed) formed,
    MM0LocatedReachability.located_kernel_reaches_iff_derives wellFormed formed]
  exact installation.conservative wellFormed target hypotheses expression

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedInstalledAdequacy
