import Mettapedia.Logic.ConstraintTypes.RegularTree
import Mettapedia.Logic.ConstraintTypes.Contracts
import Mettapedia.Logic.ConstraintTypes.SymbolicTypes
import Mettapedia.Logic.ConstraintTypes.ScopedConstraints
import Mettapedia.Logic.ConstraintTypes.ResidualConstraints
import Mettapedia.Logic.ConstraintTypes.ConstructorTyping
import Mettapedia.Logic.ConstraintTypes.ValuePatterns
import Mettapedia.Logic.ConstraintTypes.DeclarationTyping
import Mettapedia.Logic.ConstraintTypes.OpenTyping
import Mettapedia.Logic.ConstraintTypes.DeterminedMembership
import Mettapedia.Logic.ConstraintTypes.CallTyping
import Mettapedia.Logic.ConstraintTypes.CheckingPatterns
import Mettapedia.Logic.ConstraintTypes.PatternContracts
import Mettapedia.Logic.ConstraintTypes.UnsharedParameters
import Mettapedia.Logic.ConstraintTypes.CheckCost
import Mettapedia.Logic.ConstraintTypes.Constraints
import Mettapedia.Logic.ConstraintTypes.OpenMembership
import Mettapedia.Logic.ConstraintTypes.Execution
import Mettapedia.Logic.ConstraintTypes.Refresh
import Mettapedia.Logic.ConstraintTypes.Semantics
import Mettapedia.Logic.ConstraintTypes.Saturation
import Mettapedia.Logic.ConstraintTypes.WitnessSolver

/-!
# Predicate contracts for logic programs

One declaration judgment underlies closed checking, symbolic polymorphism,
open-value residual compilation and field-determined membership. The existing
first-order unifier supplies principal type solutions. Predicate semantics,
projection, propagation, ordered execution and incremental recompilation state
their respective assumptions explicitly. Concrete runtimes instantiate these
objects; they do not introduce another type calculus.
-/
