import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionObservations

/-!
# Bags of firings asked at each member's own information, with region queries

The bag step (`JointFirings.bagStep`) asks every member's guards at the joint information of the bag.
Its five choices:
* the store is a bag of occurrences;
* a firing is a bag of matches, committed together;
* the guards are asked at the joint information, which includes every member's tells;
* the program is a fixed set of rules;
* there is one store of knowledge.

This module changes only the guards.

* `ownBagStep`: the restriction of the bag step to bags admitted with each member's guards at that
  member's own information (`Bag.AdmitsOwn`): the knowledge, the member's matching and its own tells.
  Guards that hold at a member's own information hold at the joint information
  (`Bag.admits_of_admitsOwn`), so its admission is exactly a nonempty bag admitted on its own
  (`ownBagStep_admits_iff`). It is a restriction (`Spaces.restrict`), so its results and runs are
  those of the bag step.
* `Profile`: region queries (`PredicateQueryAdmission.RegionQuery`) for each member, read in the
  member's extended frame. A solution is an object with a morphism out of that frame, and a query's
  fiber holds the present occurrences whose rows lie in its region there. A profile is a function of
  the member, so its queries may depend on the member's rule and opening.
* `observedOwnStep`: the bags of `ownBagStep` in which every member's queries hold at every solution of
  the member's own information (`observedOwnStep_admits_iff`). With the empty profile it is `ownBagStep`
  (`observedOwnStep_empty_admits_iff`).

Not here: the image of these bags in the base layer, and its rounds. They need the base layer's
firings to carry region queries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBags

open Interface (Frames)
open JointFirings
open PredicateQueryAdmission (RegionQuery)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Guards at each member's own information -/

section OwnStep

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
  (P : Program Tm)

/-- **The bag step with each member's guards asked at its own information.** -/
def ownBagStep : Interface.Step X O (State Tm O) (fun s => Bag O E P s.frame) :=
  Spaces.restrict (bagStep X O E P).toStep fun {s} f => f.AdmitsOwn X s

variable {X O E P}

/-- **Admission is a nonempty bag admitted on its own.** The joint guards follow from the own ones. -/
theorem ownBagStep_admits_iff {s : State Tm O} (f : Bag O E P s.frame) :
    (ownBagStep X O E P).Admits f ↔ f.members ≠ [] ∧ f.AdmitsOwn X s := by
  constructor
  · rintro ⟨⟨nonempty, _⟩, own⟩
    exact ⟨nonempty, own⟩
  · rintro ⟨nonempty, own⟩
    exact ⟨⟨nonempty, Bag.admits_of_admitsOwn X own⟩, own⟩

end OwnStep

/-! ## Region queries asked at each member's own information -/

section Profiles

variable (O : Type uOcc) (E : Extensions.{uO, uH, uE} Hom) (P : Program Tm)

/-- **An observation profile**: the region queries a member asks, read in its extended frame. A
solution of the extended frame is an object with a morphism out of it. -/
abbrev Profile : Type _ :=
  ∀ {a : Obj} {x : E.Ext a}, Member O E P x →
    List (RegionQuery (Tm (E.target x)) (Σ b : Obj, Hom (E.target x) b) O)

end Profiles

section Observed

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm}

/-- **Every member's queries hold at every solution of its own information**, against the occurrences
present before the bag, each read by its row in the member's extended frame. -/
def AsksOwn (profile : Profile O E P) {s : State Tm O} (f : Bag O E P s.frame) : Prop :=
  ∀ m ∈ f.members, ∀ q ∈ profile m,
    X.Entails (m.firing.information X s) fun b σ => q.Holds ⟨b, σ⟩ (m.firing.row X s) s.present

/-- **The bag step with each member's guards and region queries asked at its own information.** -/
def observedOwnStep (profile : Profile O E P) :
    Interface.Step X O (State Tm O) (fun s => Bag O E P s.frame) :=
  Spaces.restrict (ownBagStep X O E P) fun {_} f => AsksOwn X profile f

theorem observedOwnStep_admits_iff (profile : Profile O E P) {s : State Tm O} (f : Bag O E P s.frame) :
    (observedOwnStep X profile).Admits f ↔
      f.members ≠ [] ∧ f.AdmitsOwn X s ∧ AsksOwn X profile f := by
  show (ownBagStep X O E P).Admits f ∧ AsksOwn X profile f ↔ _
  rw [ownBagStep_admits_iff, and_assoc]

/-- **With the empty profile, the observed step is the own-guard step.** -/
theorem observedOwnStep_empty_admits_iff {s : State Tm O} (f : Bag O E P s.frame) :
    (observedOwnStep X (fun _ => [] : Profile O E P)).Admits f ↔ (ownBagStep X O E P).Admits f := by
  show (ownBagStep X O E P).Admits f ∧ AsksOwn X (fun _ => [] : Profile O E P) f ↔ _
  constructor
  · exact And.left
  · intro admitted
    exact ⟨admitted, fun _ _ q member => by cases member⟩

end Observed

/-! ## Queries scoped by the rule's terms, and freshness on them

A profile is any function of the member, so it may read the member's opening at terms that occur
nowhere in the rule. Freshness (`Bag.Fresh`, through `Realized`) constrains an opening only on the
rule's terms (`Rule.terms`: its body, its checks' patterns and its collect query). An opening may therefore
identify an unknown that only a query mentions with an unknown of the state, and still be fresh. The
scoped construction closes this: a query sees the opening only through scope terms of the rule, and
joint freshness is asked on those terms too.

Freshness on the scope is a condition on scope only. It does not make two fresh openings give the same
observations for an arbitrary `build`: a transport of observations between openings is earned for a
given construction, not asserted here. -/

section Scope

/-- **Joint realization on scope terms**: as `Realized`, with each member's rule realized on its terms
and on the scope terms of its rule. The scope is given for the rules of the program only, through
the member's witness that its rule is one of them. -/
def RealizedOn (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
    (scope : (r : Rule Tm) → r ∈ P → List (Tm r.locals)) {a : Obj} {x : E.Ext a} (b : Obj) :
    List (Member O E P x) → (Hom (E.target x) b → Prop) → Prop
  | [], Q => ∃ u, Q u
  | m :: rest, Q => ∀ h : Hom m.rule.locals b,
      RealizedOn X scope b rest fun u =>
        Q u ∧ ∀ t ∈ m.rule.terms ++ scope m.rule m.member,
          X.E (X.act u (X.act m.opening t)) (X.act h t)

/-- **With no scope terms, it is joint realization.** -/
theorem realizedOn_nil_iff (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
    {P : Program Tm} {a : Obj} {x : E.Ext a} (b : Obj) :
    ∀ (ms : List (Member O E P x)) (Q : Hom (E.target x) b → Prop),
      RealizedOn X (fun _ _ => []) b ms Q ↔ Realized X b ms Q
  | [], _ => Iff.rfl
  | m :: rest, Q => by
      simp only [RealizedOn, Realized, List.append_nil]
      exact forall_congr' fun _ => realizedOn_nil_iff X b rest _

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm}

/-- **Joint freshness on scope terms**: as `Bag.Fresh`, with each member's rule realized also on the
scope terms of its rule. -/
def FreshOn (scope : (r : Rule Tm) → r ∈ P → List (Tm r.locals)) (s : State Tm O)
    (f : Bag O E P s.frame) : Prop :=
  ∀ (b : Obj) (g : Hom s.frame b), RealizedOn X scope b f.members fun u =>
    ∀ t, s.Mentions t → X.E (X.act u (X.act (E.weaken f.ext) t)) (X.act g t)

omit [DecidableEq O] in
/-- **With no scope terms, it is joint freshness.** -/
theorem freshOn_nil_iff (s : State Tm O) (f : Bag O E P s.frame) :
    FreshOn X (fun _ _ => []) s f ↔ f.Fresh X s := by
  unfold FreshOn Bag.Fresh
  exact forall_congr' fun b => forall_congr' fun _ => realizedOn_nil_iff X b _ _

/-- **Region queries scoped by the terms of the program's rules.** For a rule of the program, `scope`
lists terms over its unknowns and `build` gives its queries from those terms once opened. Both are
given only for the rules of the program, through the witness that a rule is one of them, so no query
code is given for a rule outside it. A member's queries see its opening only through its opened scope
terms: the scope is part of the type. -/
structure ScopedQueries (Tm : Obj → Type uT) (O : Type uOcc) (E : Extensions.{uO, uH, uE} Hom)
    (P : Program Tm) where
  scope : (r : Rule Tm) → r ∈ P → List (Tm r.locals)
  build : ∀ {a : Obj} {x : E.Ext a}, (r : Rule Tm) → r ∈ P → List (Tm (E.target x)) →
    List (RegionQuery (Tm (E.target x)) (Σ b : Obj, Hom (E.target x) b) O)

/-- The profile of scoped queries: each member's queries, built from its opened scope terms. -/
def ScopedQueries.profile (sq : ScopedQueries Tm O E P) : Profile O E P :=
  fun m => sq.build m.rule m.member ((sq.scope m.rule m.member).map (X.act m.opening))

/-- **The scoped observed step**: the observed step of the scoped profile, with joint freshness also
on the scope terms. -/
def scopedStep (sq : ScopedQueries Tm O E P) :
    Interface.Step X O (State Tm O) (fun s => Bag O E P s.frame) :=
  Spaces.restrict (observedOwnStep X (sq.profile X)) fun {s} f => FreshOn X sq.scope s f

theorem scopedStep_admits_iff (sq : ScopedQueries Tm O E P) {s : State Tm O} (f : Bag O E P s.frame) :
    (scopedStep X sq).Admits f ↔
      f.members ≠ [] ∧ f.AdmitsOwn X s ∧ AsksOwn X (sq.profile X) f ∧ FreshOn X sq.scope s f := by
  show (observedOwnStep X (sq.profile X)).Admits f ∧ FreshOn X sq.scope s f ↔ _
  rw [observedOwnStep_admits_iff, and_assoc, and_assoc]

/-- **With no scope terms, the scoped step is the observed step**: joint freshness is already part of
admission on its own. -/
theorem scopedStep_admits_iff_of_scope_nil (sq : ScopedQueries Tm O E P)
    (empty : ∀ r (inside : r ∈ P), sq.scope r inside = []) {s : State Tm O} (f : Bag O E P s.frame) :
    (scopedStep X sq).Admits f ↔ (observedOwnStep X (sq.profile X)).Admits f := by
  rw [scopedStep_admits_iff, observedOwnStep_admits_iff]
  have fresh : FreshOn X sq.scope s f ↔ f.Fresh X s := by
    have same : sq.scope = fun _ _ => [] := funext fun r => funext fun inside => empty r inside
    rw [same]
    exact freshOn_nil_iff X s f
  constructor
  · rintro ⟨nonempty, own, asks, _⟩
    exact ⟨nonempty, own, asks⟩
  · rintro ⟨nonempty, own, asks⟩
    exact ⟨nonempty, own, asks, fresh.mpr own.1.1⟩

end Scope

#print axioms realizedOn_nil_iff
#print axioms freshOn_nil_iff
#print axioms scopedStep_admits_iff
#print axioms scopedStep_admits_iff_of_scope_nil
#print axioms ownBagStep_admits_iff
#print axioms observedOwnStep_admits_iff
#print axioms observedOwnStep_empty_admits_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBags
