import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedClassGuardReduction

/-! # Checked primitive-number guards retain the source-world support gate -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceClassGuardReduction

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

@[cbv_eval] theorem number_guard (intrinsicRows : List Atom) (world : EagerDFS.World)
    (index : Nat) (store : PettaOccurrenceOverlay.Store) (number : Int) :
    PettaSourceTypeServices.orderedGuard intrinsicRows world index store (.sym "Number")
      (.grounded (.int number)) =
      if PettaSourceTypeRows.supported intrinsicRows world then
        some (if TypeEquationSolver.check store then [store ++ [(.sym "Number", .sym "Number")]] else [])
      else none := by
  simp [PettaSourceTypeServices.orderedGuard, EagerDFS.Destination.finiteStructural,
    OrderedTypeRelation.infer, TypedCertificates.Judgment.full, OrderedTypeRelation.relation,
    OrderedTypeRelation.leaf, Ty.map, OrderedClassGuardReduction.guard_class]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceClassGuardReduction
