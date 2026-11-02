import Mettapedia.Logic.TierZero.Kernel
import Mettapedia.Logic.TierZero.Dataflow
import Mettapedia.Logic.TierZero.Rights
import Mettapedia.Logic.TierZero.Extension
import Mettapedia.Logic.TierZero.Hilbert
import Mettapedia.Logic.TierZero.Criteria
import Mettapedia.Logic.TierZero.ChildBound

/-!
# MeTTa Prime's tier-0 kernel built from steps

* `TierZero.Kernel`: presentations, declarative derivability, the checker of topologically ordered
  proofs, and the step machine of the sequential kernel; soundness, completeness, determinism, and
  machine = checker.
* `TierZero.Dataflow`: the dataflow kernel; every schedule that stops ends at the valid nodes, and
  it accepts exactly the derivable judgments, as the sequential kernel does.
* `TierZero.Rights`: only kernel steps make theorems when the kernel's obligations are private; the
  forgery when clients may write them.
* `TierZero.Extension`: an accepted claim added as a rule is conservative (fresh names make the
  renamings that instantiate it).
* `TierZero.Hilbert`: Foundation's intuitionistic and classical Hilbert calculi as presentations,
  with the kernel adequate to the library's own provability.
* `TierZero.Criteria`: the naturalness criteria measured on the kernel's steps: parts used,
  what keep and the full read buy, Bennett weakness and Goertzel's counting weakness of the
  schedule constraints.
-/
