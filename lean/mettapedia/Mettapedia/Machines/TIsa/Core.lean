import Mettapedia.Machines.TIsa.RuleCompiler
import Mettapedia.Machines.TIsa.TheoryData
import Mettapedia.Machines.TIsa.Hosted
import Mettapedia.Machines.TIsa.Control
import Mettapedia.Machines.TIsa.Bytes
import Mettapedia.Machines.TIsa.Widths
import Mettapedia.Machines.TIsa.Address
import Mettapedia.Machines.TIsa.Registers
import Mettapedia.Machines.TIsa.Layout
import Mettapedia.Machines.TIsa.Memory
import Mettapedia.Machines.TIsa.RegisterProfile
import Mettapedia.Machines.TIsa.Typing
import Mettapedia.Machines.TIsa.P1Source
import Mettapedia.Machines.TIsa.P1Scalar
import Mettapedia.Machines.TIsa.P1Memory
import Mettapedia.Machines.TIsa.Loop
import Mettapedia.Machines.TIsa.Outcome
import Mettapedia.Machines.TIsa.Fuel
import Mettapedia.Machines.TIsa.Funding
import Mettapedia.Machines.TIsa.FundingTrace
import Mettapedia.Machines.TIsa.RelativeBranch
import Mettapedia.Machines.TIsa.Continuation
import Mettapedia.Machines.TIsa.RegisterBlock
import Mettapedia.Machines.TIsa.Admission
import Mettapedia.Machines.TIsa.Framing

/-!
# Transform-native machine profile

Operational state and firing are the existing resource calculus. The extra
interface consists of scalar words, finite machine-cell recipes, byte ranges,
and native representation obligations. External manifest transport is separate.
-/
