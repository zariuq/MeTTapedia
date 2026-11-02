import Mettapedia.Machines.TypedScalar

/-! Decidable equality of the sorted scalar IR, retaining every result sort. -/

namespace Mettapedia.Machines.TypedScalar

deriving instance DecidableEq for Binary
deriving instance DecidableEq for Expr

end Mettapedia.Machines.TypedScalar
