import Mettapedia.Languages.Agda.Adequacy.Controls
import Mettapedia.Languages.Agda.Adequacy.PresentedComputation
import Mettapedia.Languages.Agda.Adequacy.Retraction
import Mettapedia.Languages.Agda.Adequacy.NormalForms
import Mettapedia.Languages.Agda.Structural.Presentation
import Mettapedia.Languages.Agda.Structural.RuleInterpretation
import Mettapedia.Languages.Agda.Structural.RootCorrespondence
import Mettapedia.Languages.Agda.Structural.PresentationSoundness
import Mettapedia.Languages.Agda.Specification.Audit
import Lean.Util.CollectAxioms

/-!
# Axiom gate for the structural application fragment

This module checks the actual declarations of the independent specification,
structural fragment, and adequacy component. Only propositional extensionality
and quotient soundness are admitted. The gate rejects holes and any additional
axiom dependency; it does not qualify Agda typing or declaration admission.
-/

open Lean Lean.Elab.Command

run_cmd do
  let prefixes : List Name := [`Mettapedia.Languages.Agda.Specification,
    `Mettapedia.Languages.Agda.Structural, `Mettapedia.Languages.Agda.Adequacy,
    `Mettapedia.OSLF.Binding.CompatibleDerivations]
  let allowed := [``propext, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      let dependencies ← collectAxioms name
      let excess := dependencies.filter fun dependency => !allowed.contains dependency
      unless excess.isEmpty do
        throwError "Axiom gate failed for {name}: {excess}"
      count := count + 1
  logInfo m!"Structural application fragment: {count} declarations within [propext, Quot.sound]."
