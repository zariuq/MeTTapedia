import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Basic

/-!
# The fixed names are no instance names

The instance names `all@A` and `eq@A` spell the simple type `A` after a fixed
prefix, and `allInstance?` and `eqInstance?` (in `SetProfile.Basic`) read the
type back, computably and by constructive proofs. This module records that the
reader reads none of the profile's fixed names as an instance: the carriers,
implication, the proof family and every constant of the signature.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation (DeclName)

/-! ## The fixed names -/

theorem allInstance?_propName : allInstance? propName = none := by decide
theorem eqInstance?_propName : eqInstance? propName = none := by decide
theorem allInstance?_impName : allInstance? impName = none := by decide
theorem eqInstance?_impName : eqInstance? impName = none := by decide
theorem allInstance?_holdsName : allInstance? holdsName = none := by decide
theorem eqInstance?_holdsName : eqInstance? holdsName = none := by decide

theorem allInstance?_baseName (sort : SetBase) : allInstance? (baseName sort) = none := by
  cases sort <;> decide

theorem eqInstance?_baseName (sort : SetBase) : eqInstance? (baseName sort) = none := by
  cases sort <;> decide

theorem allInstance?_constantName {type : HOL.Ty SetBase} (symbol : SetConst type) :
    allInstance? (constantName symbol) = none := by
  cases symbol <;> decide

theorem eqInstance?_constantName {type : HOL.Ty SetBase} (symbol : SetConst type) :
    eqInstance? (constantName symbol) = none := by
  cases symbol <;> decide

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile
