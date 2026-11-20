import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Independence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.CompositionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Renaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.RenamingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Hiding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingRho
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Isolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.IsolationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Bisimulations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.StartPrivacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.ExtrusionControls

/-!
# Private unknowns: scope, hiding and composition on the step of a program

At the one-frame action of a substitution action, with the identity extension (`RuleSyntax.step`).
Shared unknowns stay a feature: a tell that binds an unknown the caller shares is how answers flow.
These modules give the other half, unknowns that only their owner can constrain, and say what
sharing costs.

**When two families of terms share no unknown** (`Independent`): every instantiation of each is
realized together. At first-order terms it is exactly disjoint mention (`independent_iff_disjoint`).

**Composition restored** (`Composition`). Systems side by side (`beside`). A positive firing (checks
are equations, no collect query) is admitted beside a solvable neighbour that shares no unknown with its
footprint exactly when it is admitted alone (`admits_beside_iff_alone`); the result commutes with the
composition (`result_beside`); the exact cost of sharing is a joint solution (`admits_beside_iff`).
Privacy is a property of reachable states along private steps (`privateFrom_along`), and reachable
success persists (`success_persists`). At first-order terms over infinitely many unknowns, privacy
at the start suffices for every positive run (`StartPrivacy.success_persists_from_start`): the run's
fresh unknowns are renamed away from the neighbour. Controls (`CompositionControls`): a shared
unknown refuses and switches success off (a positive program, with no none query involved); none queries and
collect query are refused beside a ground row although everything is independent; an unsolvable neighbour
refuses; a neighbour mentioning the opened unknown makes the opening not fresh, and opening apart
repairs it.

**Scope** (`Renaming`): renaming unknowns is a bisimulation of the step of every program
(`succ_rename_iff`, `renaming_isBisimulation`); scope extension past a neighbour the renaming fixes
(`scope_extension`), needed (`RenamingControls.scope_extension_needs_fixed`); extrusion through a row
(`RenamingControls.extrusion_through_row`, `ExtrusionControls.extrusion_by_make`): making a row that
carries a fresh unknown keeps the system private, and a cross reader of that row and the neighbour's
row links the unknown to the neighbour's knowledge.

**Hiding** (`Hiding`, `HidingFirstOrder`): states whose knowledges are seen alike from their rows
admit the same fresh firings and reach related results (`admits_iff_of_hides`, `hides_result`); at
first-order terms with the same unknowns it is a bisimulation (`succ_hiddenFO`,
`hiddenFO_isBisimulation`), and the projection by solved forms exists, keeping hidden existential
witnesses (`hideStore`, `hiddenFO_hide`); naive dropping is unsound and the hidden store is weaker
(`HidingControls`). The history control disappears after hiding (`HidingRho.hidden_knowledge_native`).

**Spaces** (`Isolation`): structural congruence is a bisimulation (`succ_congruent`), side by side is
commutative up to it (`beside_comm`), and a firing at one space does not change what is admitted at
the other when their footprints share no unknown (`isolation`); a shared unknown crosses spaces
(`IsolationControls.shared_unknown_crosses_spaces`).
-/
