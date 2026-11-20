import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Every

/-!
# CMR completeness and uniqueness with an explicit match identity

Profile: one occurrence-bag store, ambient rules, a finite bag of matches per
commit, guards at each member's own information (including its tells). No
default is selected. Identity is a parameter of completeness, not a change to
resource admission or named-origin observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)

universe uO uT uH uE uOcc uK

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- The observational identity counted by complete and unique batches. -/
structure MatchIdentity (O : Type uOcc) (E : Extensions.{uO, uH, uE} Hom) (P : Program Tm) where
  Key : Type uK
  key : {a : Obj} → Firing O E P a → Key

def MatchIdentity.ordered : MatchIdentity O E P where
  Key := Rule Tm × List O × List O
  key := firingKey

namespace Bag

def keysBy (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    {a : Obj} (f : Bag O E P a) : List identity.Key :=
  f.members.map fun m => identity.key m.firing

def DistinctBy (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    {a : Obj} (f : Bag O E P a) : Prop := (f.keysBy identity).Nodup

variable (X : Frames Tm Hom) [DecidableEq O] (s : State Tm O)

/-- A region is a predicate on the chosen match identities. -/
def CompleteBy (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (region : identity.Key → Prop) (f : Bag O E P s.frame) : Prop :=
  ∀ g : Firing O E P s.frame, region (identity.key g) → g.Admits X s →
    identity.key g ∈ f.keysBy identity

def AdmitsEveryBy (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (region : identity.Key → Prop) (f : Bag O E P s.frame) : Prop :=
  f.AdmitsOwn X s ∧ (∀ key ∈ f.keysBy identity, region key) ∧
    f.DistinctBy identity ∧ f.CompleteBy X s identity region

def AdmitsUniqueBy (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (region : identity.Key → Prop) (f : Bag O E P s.frame) : Prop :=
  f.AdmitsEveryBy X s identity region ∧ f.members.length = 1

variable {X s}

theorem AdmitsEveryBy.keys_perm
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f f' : Bag O E P s.frame}
    (first : f.AdmitsEveryBy X s identity region)
    (second : f'.AdmitsEveryBy X s identity region) :
    (f.keysBy identity).Perm (f'.keysBy identity) := by
  apply (List.perm_ext_iff_of_nodup first.2.2.1 second.2.2.1).mpr
  intro key
  constructor
  · intro member
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp member
    exact second.2.2.2 m.firing (first.2.1 _ member)
      (admits_member X inhabited first.1 inM)
  · intro member
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp member
    exact first.2.2.2 m.firing (second.2.1 _ member)
      (admits_member X inhabited second.1 inM)

theorem AdmitsEveryBy.length_eq
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f f' : Bag O E P s.frame}
    (first : f.AdmitsEveryBy X s identity region)
    (second : f'.AdmitsEveryBy X s identity region) : f.members.length = f'.members.length := by
  simpa [keysBy] using (first.keys_perm inhabited second).length_eq

theorem AdmitsUniqueBy.key_eq
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f : Bag O E P s.frame}
    (unique : f.AdmitsUniqueBy X s identity region)
    {m : Member O E P f.ext} (only : f.members = [m])
    {g : Firing O E P s.frame} (inRegion : region (identity.key g))
    (admitted : g.Admits X s) : identity.key g = identity.key m.firing := by
  have listed := unique.1.2.2.2 g inRegion admitted
  simpa [keysBy, only] using listed

theorem admitsEveryBy_ordered_iff (Q : Set (Rule Tm)) (f : Bag O E P s.frame) :
    f.AdmitsEveryBy X s MatchIdentity.ordered (fun key => key.1 ∈ Q) ↔ f.AdmitsEvery X s Q := by
  unfold AdmitsEveryBy AdmitsEvery CompleteBy Complete DistinctBy Distinct Within keysBy
  simp only [MatchIdentity.ordered, firingKey_firing]
  constructor
  · rintro ⟨admitted, within, distinct, complete⟩
    refine ⟨admitted, fun m member => ?_, distinct, complete⟩
    exact within m.key (List.mem_map.mpr ⟨m, member, rfl⟩)
  · rintro ⟨admitted, within, distinct, complete⟩
    refine ⟨admitted, ?_, distinct, complete⟩
    intro key member
    obtain ⟨m, inside, rfl⟩ := List.mem_map.mp member
    exact within m inside

end Bag

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
