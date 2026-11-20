import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Progress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Systems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Preserved
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.BesideNeighbours
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.OneAnswer

/-!
# Progress and divergence of hosted programs

* `Progress`: no alternative of the hosted fragments waits (`arrow_progress`, `plain_progress`).
* `Systems`: the source's configurations, one alternative with its world, and the step of a translated
  program as systems; alternative by alternative the hosting is an operational correspondence
  (`alternativesCorrespondence`), and configuration by configuration its reflected half is a readback
  (`arrowReadback`, `plainReadback`); divergence is reflected (`arrow_divergence_reflected`,
  `divergence_reflected`).
* `Preserved`: divergence is preserved (`arrow_divergence_preserved`, `divergence_preserved`), by
  termination through frontiers (`acc_of_frontier`); the source diverges exactly when the translated
  program does (`arrow_diverges_iff`, `diverges_iff`).
* `Examples`: a program that diverges and a program that terminates, through both theorems.
* `BesideNeighbours`: beside a neighbour's rules, the source diverges exactly when the union has a run in
  which the translated program fires infinitely often (`arrow_diverges_iff_beside`); beside a neighbour
  that fires for ever every union diverges.
* `OneAnswer`: a reachable state shows at most one finished row (`one_finished_row`), which is why the
  forward half is a frontier of several states and not one state.
-/
