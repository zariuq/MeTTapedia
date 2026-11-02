import Mettapedia.Logic.TierZero.Kernel2.Syntax
import Mettapedia.Logic.TierZero.Kernel2.Rules
import Mettapedia.Logic.TierZero.Kernel2.Claims
import Mettapedia.Logic.TierZero.Kernel2.Walk
import Mettapedia.Logic.TierZero.Kernel2.StoreOps
import Mettapedia.Logic.TierZero.Kernel2.Shared
import Mettapedia.Logic.TierZero.Kernel2.Declared
import Mettapedia.Logic.TierZero.Kernel2.Spaces
import Mettapedia.Logic.TierZero.Kernel2.FireWhenReady
import Mettapedia.Logic.TierZero.Kernel2.Render
import Mettapedia.Logic.TierZero.Kernel2.Examples

/-!
# The tier-0 kernel in Lean, on thinned terms

* `Kernel2.Syntax`: terms (binding trees over MeTTa-shaped heads), patterns, and the side
  conditions' term functions, binder-correct.
* `Kernel2.Rules`: rules as data, the presentation of a rule table, the kernel's matching walking
  premises in order (F1), side conditions consuming no child (F2); `accepts_iff_derivable`.
* `Kernel2.Claims`: claims (formals freshened by kind: names, scope variables, names over scope
  variables), their reading and admission checks (F4), `verdict_sound`, `verdict_complete`.
* `Kernel2.Walk`: the kernel's step at a node, and the walk in order equal to `ChildBound.runCB`.
* `Kernel2.StoreOps`, `Kernel2.Shared`: the kernel on a canonical thinned store, refined to the
  tree kernel (`Claim.verdictR_eq_verdict`, `verdictR_sound`, `verdictR_complete`).
* `Kernel2.Declared`: when an accepted claim may become a rule (finding F5): the declared
  discipline for every formal kind and dummies, and every instance of the rule it becomes is
  derivable without it (`derived_instance_derivable`, `derived_conservative`).
* `Kernel2.Spaces`: the five spaces, rights, admissions and claims; a claim step adds no theorems
  (`kernelStep_claim_conservative`).
* `Kernel2.FireWhenReady`: the walk that fires a node when its children are ready
  (`checkF_iff_derivable`).
* `Kernel2.Render`, `Kernel2.Examples`: MeTTa source of the messages, and the kernel-v2 test worlds
  as Lean data with kernel-checked verdicts.
-/
