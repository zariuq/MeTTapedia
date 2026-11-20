import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MatchIdentity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Unique

/-!
# Ordered CMR identity retains the existing unique-bag reading

Completeness is already related to its existing ordered-key judgment. This
module also identifies uniqueness, without changing named rule origins or
selecting a default match-identity profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bag

open Interface (Frames)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  {X : Frames Tm Hom} {s : State Tm O}

theorem admitsUniqueBy_ordered_iff (Q : Set (Rule Tm)) (bag : Bag O E P s.frame) :
    bag.AdmitsUniqueBy X s MatchIdentity.ordered (fun key => key.1 ∈ Q) ↔ bag.AdmitsUnique X s Q := by
  unfold AdmitsUniqueBy AdmitsUnique
  rw [admitsEveryBy_ordered_iff]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bag
