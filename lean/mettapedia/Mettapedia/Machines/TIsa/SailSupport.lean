import Mettapedia.Machines.TIsa.SailAttributes
import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap
import Std.Tactic.BVDecide

/-!
# Pinned Sail semantic support

The upstream support library is checked under this package's Lean version.
The source pin is lean-sail v5, commit 079463134b9c50450b8393e1566a09fc492a34d9.
Each included file retains its original definitions and checked dependency
header. Generated model clients supply their own architecture parameters.
-/

set_option autoImplicit true

tisa_model_file% "../../../repos/lean-sail/Sail/BitVec.lean"
  sha256 "34c6424c6aa606206deaefa27867358a9df749fe3f53fe8b6f50cac64c601ed4"
  imports [Lean.Elab.Term, Lean.Meta.Reduce, Std.Tactic.BVDecide]

tisa_model_file% "../../../repos/lean-sail/Sail/IntRange.lean"
  sha256 "405efd008ef4811b8dc664ccb982d5d2838a53423875f131450aad139846e4a9" imports []

tisa_model_file% "../../../repos/lean-sail/Sail/Common.lean"
  sha256 "5269603c159519b598edf26b39cc8ff5b0d54a79846b2b652f303950719d8452" imports [Sail.Attr]

set_option linter.unusedVariables false in
tisa_model_file% "../../../repos/lean-sail/Sail/ArchSem.lean"
  sha256 "fc340039f5acf1b84beb4d8fde4cf94d3cad80bf063f8f1b1a8821835bcda4aa" imports [Sail.Common]

tisa_model_file% "../../../repos/lean-sail/Sail/ConcurrencyInterfaceV1.lean"
  sha256 "977d888e1f6b29e895a00571e228259632c7f96a6cdf5c8a817f26f1afacd201"
  imports [Sail.Attr, Sail.Common, Std.Data.ExtDHashMap, Std.Data.ExtHashMap]

set_option linter.ambiguousOpen false in
tisa_model_file% "../../../repos/lean-sail/Sail/Sail.lean"
  sha256 "4a32822b287f6890bb9e527fca865a2b9751b2aed200be805c479ca6687b670f"
  imports [Sail.Attr, Sail.ArchSem, Sail.ConcurrencyInterfaceV1]

tisa_model_file% "../../../repos/lean-sail/Sail.lean"
  sha256 "24b92934ac9f5508446f2f5ce415b8f90522c3057d24f9063f93a0e46c69f973"
  imports [Sail.BitVec, Sail.IntRange, Sail.Sail]
