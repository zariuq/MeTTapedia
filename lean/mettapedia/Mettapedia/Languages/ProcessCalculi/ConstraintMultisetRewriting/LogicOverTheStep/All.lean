import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ModalComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.SolutionFibration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.FrameInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.SolutionFibres
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ContextGrades
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Narrowings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.PresentationMeetsStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.FirstOrderPresentation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InfinitaryAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.CountingModalities
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RhoPast
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.DependentGrades
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StoreQuotient
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Readback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RigidReadback

/-!
# OSLF over the step, graded: how the step's modalities and predicates are carried

OSLF's modalities are derived from a reduction span by change of base (`DerivedModalities`). This
folder connects them to the step's real changes: maps between transition systems, changes of frame
and knowledge, and added contexts. Each comparison is an equality only where a stated lifting or
pullback property holds; otherwise one implication holds, and a control separates the two.

* **Modal comparison** (`ModalComparison`): Beck–Chevalley in the fibration of predicates holds
  exactly for weak pullback squares; for a map of transition systems, carrying steps and lifting
  steps are the two halves of transporting possibility and successor necessity, and predecessor
  necessity needs predecessors lifted instead. Bisimulations are spans of open maps.
* **The step's own span** (`StepSpan`): its edges are the admitted firings; its modalities are those
  of its successor relation; Hennessy–Milner adequacy comes from the tree's theorem.
* **Frames and knowledge** (`SolutionFibration`, `FrameInstances`): predicates over a frame are
  predicates on its solutions; reindexing along frame morphisms is functorial on the observational
  ones; transporting knowledge is reindexing its models; asks and solvability are carried with one
  implication, and with equality under covering. The step's firings and runs only refine knowledge,
  in the fibre over the result. First-order and dependent instances.
* **The fibre over one solution** (`SolutionFibres`): the step at a solution includes into the
  step; possibility pulls back exactly for quiet rule sets; ground rule sets are quiet; a tell is not.
* **Contexts** (`ContextGrades`): adding a store is a change with identity and composition laws;
  positive predicates survive it, absence and exact counts exactly within their grade; a firing's
  grade is that of its absences; possibility through absence and successor necessity do not survive.
* **Narrowings** (`Narrowings`): rho and sequential PeTTa are open; HE is a span of open maps; the
  precise failure of unlocked hyperpose; the first-order narrowing through heating lifts the future
  and not the past.
* **The authored presentation meets the step** (`PresentationMeetsStep`): interpreted through an
  exact encoding and the step's own preparation and admission, the presentation's steps are exactly
  the admitted firings; the step's possibility, successor necessity and predecessor necessity are
  the presentation's after a choice of firing. The presentation's diamond at a state's own code is
  false, and at a request it is strictly stronger than the step's. First-order firings carry
  predicate queries no pattern codes; without them (they add no successor) the first-order step has
  an exact encoding for encodable terms and identities, and its possibility over successors is the
  presentation's after a choice of firing (`FirstOrderPresentation`).
* **Adequacy on the real step** (`ProgramAdequacy`, `InfinitaryAdequacy`): renaming issued
  identities is a bisimulation of the first-order step; under every finite program successor sets
  are finite up to renaming, so Hennessy–Milner adequacy holds; the unrestricted step has no finite
  covers. Infinitary conjunctions are adequate on every system; one greatest fixed point already
  separates the tree's counterexample to finitary adequacy.
* **Counting** (`CountingModalities`): graded possibility over firings; graded adequacy for
  edge-finite spans, and for events under every finite program, on the real step counting firings up
  to their events; counts cross local isomorphisms of spans, and not the map from firings to
  successors; two copies against one; unboundedly many firings against one event.
* **Rho's past** (`RhoPast`): predecessors do not lift along rho's narrowing, because every
  communication records its matches; rho's predecessor necessity is the store's over the heating
  class. With an empty source (a program that makes `T` from nothing) predecessors do lift.
* **Dependent grades** (`DependentGrades`): typed absence and exact counts survive exactly beside
  stores without the pattern at the solution; along the helper weakening, at the composite solution.
* **Adding a store on the quotient** (`StoreQuotient`): bisimilarity observing knowledge and labels
  is renaming, so adding a fresh store is a map on the quotient for every program; controls for
  colliding identities and for a quotient that forgets labels.
* **Readback** (`Readback`, `RigidReadback`): an answer is determined when the knowledge entails its
  equation; determinacy survives firings and runs; injective spines determine, computing spines do
  not; equal rigid spines are equal argument by argument, so the answers of the vector lookup, the
  typed interpreter, the two-firing recursive lookup and append (with its implicit lengths) are the
  same at every solution; projections determine the components of a matched dependent pair.
-/
