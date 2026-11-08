import Mettapedia.Logic.ASP.Kernel
import Mettapedia.Logic.ASP.Checker
import Mettapedia.Logic.ASP.CheckerControls
import Mettapedia.Logic.ASP.Approximation
import Mettapedia.Logic.ASP.WellFounded
import Mettapedia.Logic.ASP.WellFoundedControls
import Mettapedia.Logic.ASP.Nogoods
import Mettapedia.Logic.ASP.Solver
import Mettapedia.Logic.ASP.SolverControls
import Mettapedia.Logic.ASP.CNF
import Mettapedia.Logic.ASP.ProgramCNF
import Mettapedia.Logic.ASP.LRAT
import Mettapedia.Logic.ASP.FirstUIP
import Mettapedia.Logic.ASP.Counting
import Mettapedia.Logic.ASP.Borrowing
import Mettapedia.Logic.ASP.BooleanControls
import Mettapedia.Logic.ASP.RUP
import Mettapedia.Logic.ASP.HallStep
import Mettapedia.Logic.ASP.Certificate
import Mettapedia.Logic.ASP.Emission
import Mettapedia.Logic.ASP.Freshness
import Mettapedia.Logic.ASP.Watches
import Mettapedia.Logic.ASP.SourcePointers
import Mettapedia.Logic.ASP.CertificateControls
import Mettapedia.Logic.ASP.HallStepControls
import Mettapedia.Logic.ASP.PropagationControls
import Mettapedia.Logic.ASP.Projection
import Mettapedia.Logic.ASP.Circuits
import Mettapedia.Logic.ASP.CountingControls
import Mettapedia.Logic.ASP.Propagation
import Mettapedia.Logic.ASP.Driver
import Mettapedia.Logic.ASP.Enumeration
import Mettapedia.Logic.ASP.CheckerAgreement
import Mettapedia.Logic.ASP.DriverControls
import Mettapedia.Logic.ASP.CPOG
import Mettapedia.Logic.ASP.CPOGControls
import Mettapedia.Logic.ASP.WeightRulesControls
import Mettapedia.Logic.ASP.SatCertificateControls
import Mettapedia.Logic.ASP.WeightDefs
import Mettapedia.Logic.ASP.WeightStep
import Mettapedia.Logic.ASP.WeightCertificate
import Mettapedia.Logic.ASP.WeightDefsNormalize
import Mettapedia.Logic.ASP.WeightStepControls
import Mettapedia.Logic.ASP.FalsumControls
import Mettapedia.Logic.ASP.UnitBodyControls
import Mettapedia.Logic.ASP.InputStepControls

/-!
# Answer set programming

The Lean foundations of a verified answer set solver over an arbitrary atom
type:

* `Kernel`: propositional normal programs, stable and supported models, and the
  bridge that transfers the ground-program theory (Fages, Lin–Zhao, Clark's
  completion);
* `Checker`: the executable stable-model checker and the complete enumerator;
* `Approximation`, `WellFounded`: approximation fixpoint theory, Fitting's
  operator, the well-founded model by unfounded sets, and their computed forms;
* `Nogoods`: completion and loop nogoods with their origins, the completion reduced
  at falsum atoms, the heads of integrity constraints, and at unit bodies, which
  get no variable and are their one literal;
* `Solver`: the conflict-driven solver as a transition system, with soundness,
  progress, termination and completeness.

The Boolean kernel shared by the SAT, answer set and counting disciplines:

* `CNF`: literals, clauses and formulas over any variable type, satisfaction,
  sound unit propagation, monotonicity of adding clauses, renaming and
  conditioning;
* `ProgramCNF`: nogoods as clauses, and the trust bridge: the completion CNF has
  exactly the supported models, with loop nogoods exactly the stable models, in
  the numbered form a SAT solver reads;
* `LRAT`: accepted LRAT proofs for the numbered CNF refute the program;
* `FirstUIP`: first-UIP conflict analysis yields a derived, asserting nogood and
  drives a backjump step;
* `Counting`: model counting and weighted counting with the Shannon split and
  component decomposition;
* `Borrowing`: completion with loop nogoods as a conservative route between
  theories.

Certificates out, propagation in:

* `RUP`: the nogood first-UIP learns is a reverse-unit-propagation consequence of
  the reasons it resolved and the conflict, and the action-by-action LRAT checker
  accepts the emitted addition;
* `HallStep`: constraint rules, at-least-one and exclusion rules, and the counting
  step over them: groups covered by fewer cliques than there are groups force an
  atom of the remaining set;
* `Certificate`: refutation certificates with LRAT additions, loop-nogood additions
  and Hall additions, and their checker, sound for the absence of stable models;
* `Emission`: the solver with emission; a run reporting `unsat` has emitted a
  certificate the checker accepts;
* `Freshness`: under exhaustive propagation of learned nogoods, first-UIP nogoods
  are new;
* `Watches`: propagation with two watched literals, refining unit propagation and
  computing its closure;
* `SourcePointers`: the source-pointer check, which computes exactly the greatest
  unfounded set;
* `Projection`: projected model counting, with the side conditions of its laws;
* `Circuits`: decision-DNNF and partitioned-operation graphs, whose evaluation in a
  semiring is the weighted model count.

The reference driver:

* `Propagation`: a fuel bound for watched propagation, watches across backjumps
  and for learned nogoods, a scan of the nogoods too short to watch, and one loop
  alternating watches and the source-pointer check, closed under both;
* `Driver`: a deterministic, total solver whose run is a run of the solver with
  emission and of the discipline; returned models are stable, `unsat` comes with
  an accepted certificate, and emission progresses at every conflict, including
  stale ones;
* `Enumeration`: all stable models, each once, by blocking constraints over one
  fresh atom;
* `CheckerAgreement`: the certificate checker and the action-by-action LRAT
  checker run in lockstep on certificates of LRAT actions only, without loop or
  Hall steps.
* `SatCertificateControls`: a refutation CeTTa's C solver emits for a clause set
  (three pigeons, two holes) is accepted in the kernel by the action-by-action
  LRAT checker, which refuses its truncation, every proof for a satisfiable
  clause set, and a hint naming no clause.

Weight definitions, propagated natively:

* `WeightDefs`: programs with weight definitions, an atom true exactly when its literals weigh at
  least a bound; their stable models, the C solver's well-formedness and acyclicity tests;
* `WeightStep`: the weight step, a clause checked by arithmetic against a definition, sound in every
  assignment satisfying the definition;
* `WeightCertificate`: the C solver's numbering and completion of a program with definitions, reduced
  at falsum atoms and unit bodies, and the certificate checker with weight steps, sound for the absence of stable
  models; over constraints added after models, with input steps, sound for the absence of stable
  models meeting them;
* `WeightDefsNormalize`: for acyclic definitions, the stable models are those of the normalization by
  sequential weight counters, restricted to the original atoms;
* `WeightStepControls`: a refutation CeTTa's C solver emits with weight steps is accepted, mutations
  of it are refused, and a loop step over a definition atom is refused.
* `FalsumControls`: the falsum-reduced completion of integrity constraints sharing one head, a RUP
  refutation and a Hall refutation over it, and the refusal of loop steps over falsum atoms;
  `WeightCertificate` also shows that over no definitions its checker is `Program.checkCert`.
* `UnitBodyControls`: unit bodies stand as their literals in the completion and in loop nogoods; RUP
  and loop refutations over the reduced completion, and the refusal of their truncations.
* `InputStepControls`: a refutation over constraints added after models, with input steps, is
  accepted; a wrong input clause, a shortened list of constraints, a truncation and a constraint
  over an atom outside the program are refused.

Certified knowledge compilation:

* `CPOG`: the checker of CPOG certificates; an accepted certificate yields a
  decomposable, deterministic circuit over the data variables with the models of
  the input CNF, hence its weighted and unweighted model counts, computed on the
  graph.
-/
