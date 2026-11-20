import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MatchIdentity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Independent

/-!
# CMR completeness and uniqueness survive member enumeration order

Profile: one occurrence-bag store, ambient rules, finite own-information
bags with guards after tells. An explicit match identity and region remain
parameters. This is not a law about chronological effect observers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)

universe uO uT uH uE uOcc uK

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

namespace Bag

theorem keysBy_perm (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    {a : Obj} {x : E.Ext a} {first second : List (Member O E P x)}
    (perm : first.Perm second) :
    (Bag.keysBy identity ⟨x, first⟩).Perm (Bag.keysBy identity ⟨x, second⟩) :=
  perm.map (fun member : Member O E P x => identity.key member.firing)

variable {X : Frames Tm Hom} [DecidableEq O] {s : State Tm O}

theorem admitsEveryBy_perm (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (region : identity.Key → Prop) {x : E.Ext s.frame}
    {first second : List (Member O E P x)} (perm : first.Perm second)
    (complete : (⟨x, first⟩ : Bag O E P s.frame).AdmitsEveryBy X s identity region) :
    (⟨x, second⟩ : Bag O E P s.frame).AdmitsEveryBy X s identity region := by
  have keys := keysBy_perm identity perm
  refine ⟨Bag.admitsOwn_perm X perm complete.1,
    fun key member => complete.2.1 key (keys.mem_iff.mpr member),
    keys.nodup_iff.mp complete.2.2.1, ?_⟩
  intro firing inRegion admitted
  exact keys.mem_iff.mp (complete.2.2.2 firing inRegion admitted)

theorem admitsUniqueBy_perm (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (region : identity.Key → Prop) {x : E.Ext s.frame}
    {first second : List (Member O E P x)} (perm : first.Perm second)
    (unique : (⟨x, first⟩ : Bag O E P s.frame).AdmitsUniqueBy X s identity region) :
    (⟨x, second⟩ : Bag O E P s.frame).AdmitsUniqueBy X s identity region :=
  ⟨admitsEveryBy_perm identity region perm unique.1, perm.length_eq.symm.trans unique.2⟩

end Bag

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
