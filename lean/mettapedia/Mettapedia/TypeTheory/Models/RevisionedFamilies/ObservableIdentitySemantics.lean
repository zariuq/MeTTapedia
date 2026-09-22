import Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyDescent
import Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
import Mettapedia.OSLF.Framework.WMCalculusQuotientFunctor

/-!
# WM observational equality as an identity fibre in Prime's semantic CwF

The existing semantic families CwF has identity formation, reflexivity,
substitution and J-elimination. Interpreting its carrier as the quotient of
WM states by all queries makes the resulting identity fibre correspond
exactly to behavioral agreement. It does not turn equality of raw backend
states into identity, nor interpret Prime's authored identity syntax.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.ObservableIdentitySemantics

open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusQuotientFunctor
open Mettapedia.OSLF.Framework.WMCalculusReadingCategory
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures

variable {State Query V : Type} (R : WMReading State Query V)

/-- The existing families-CwF identity former, specialized to two
observable WM state classes in the base-stage unit context. -/
def observableIdentity (first second : State) : Type :=
  (familiesIdentityFormation.idTy (m := stageOfNat 0)
    (Γ := PUnit)
    (fun _ => ObsState R)
    (fun _ => classOf R first)
    (fun _ => classOf R second)) PUnit.unit

/-- A genuine reflexivity inhabitant from the CwF's identity formation. -/
def observableIdentityRefl (state : State) :
    observableIdentity R state state :=
  familiesIdentityFormation.refl (fun _ : PUnit => classOf R state) PUnit.unit

/-- The semantic identity fibre is inhabited exactly for behaviorally
agreeing states. The identity is literally on quotient states, not on raw
state representations. -/
theorem observableIdentity_iff_agree (first second : State) :
    Nonempty (observableIdentity R first second) ↔
      R.Agree .state first second := by
  constructor
  · rintro ⟨⟨equalClasses⟩⟩
    exact (classOf_eq_iff_agree R first second).mp equalClasses
  · intro agree
    exact ⟨⟨(classOf_eq_iff_agree R first second).mpr agree⟩⟩

/-- Specializing the staged families semantic J eliminator transports an
arbitrary dependent family on observable WM states. The motive is the
function type from the left fibre to the right fibre; reflexivity supplies
its identity base case. -/
def observableJTransport (P : ObsState R → Type)
    {first second : State} (path : observableIdentity R first second) :
    P (classOf R first) → P (classOf R second) :=
  (familiesIdentityTypes.j (mode := stageOfNat 0) (Γ := PUnit)
    (fun _ => ObsState R)
    (fun total => P total.1.1.2 → P total.1.2)
    (fun _ value => value))
    ⟨⟨⟨PUnit.unit, classOf R first⟩, classOf R second⟩, path⟩

/-- The specialized J transport computes to the identity on reflexivity. -/
theorem observableJTransport_refl (P : ObsState R → Type)
    (state : State) (value : P (classOf R state)) :
    observableJTransport R P (observableIdentityRefl R state) value = value := by
  rfl

/-- A behavior-preserving reading arrow maps observable identity proofs
along its genuine quotient-state map. An arbitrary signature map lacks this
operation unless it preserves the source agreement relation. -/
def observableIdentity_map {source target : BehavioralReading}
    (hom : source ⟶ target)
    {first second : source.model.State}
    (path : observableIdentity source.model.reading first second) :
    observableIdentity target.model.reading
      (hom.readingMap.mapState first) (hom.readingMap.mapState second) := by
  refine ⟨?_⟩
  have mapped := congrArg (quotientMap hom).mapState path.down
  simpa [quotientObject] using mapped

private theorem jTransport_map_eq {A B : Type} (map : A → B) (P : B → Type)
    {left right : A} (equal : left = right) (value : P (map left)) :
    (familiesIdentityTypes.j (mode := stageOfNat 0) (Γ := PUnit)
      (fun _ => B)
      (fun total => P total.1.1.2 → P total.1.2)
      (fun _ argument => argument))
        ⟨⟨⟨PUnit.unit, map left⟩, map right⟩, ⟨congrArg map equal⟩⟩ value =
    (familiesIdentityTypes.j (mode := stageOfNat 0) (Γ := PUnit)
      (fun _ => A)
      (fun total => P (map total.1.1.2) → P (map total.1.2))
      (fun _ argument => argument))
        ⟨⟨⟨PUnit.unit, left⟩, right⟩, ⟨equal⟩⟩ value := by
  cases equal
  rfl

/-- Semantic J transport is natural under a behavioral backend map: moving
an observable identity proof first and then transporting in the target family
agrees with transporting in its pullback family at the source. -/
theorem observableJTransport_map {source target : BehavioralReading}
    (hom : source ⟶ target)
    (P : ObsState target.model.reading → Type)
    {first second : source.model.State}
    (path : observableIdentity source.model.reading first second)
    (value : P (classOf target.model.reading (hom.readingMap.mapState first))) :
    observableJTransport target.model.reading P
      (observableIdentity_map hom path) value =
    observableJTransport source.model.reading
      (fun observed => P ((quotientMap hom).mapState observed)) path value := by
  exact jTransport_map_eq (quotientMap hom).mapState P path.down value

/-- Compose observable identity witnesses without asserting raw-state
equality or retaining a particular rewrite occurrence history. -/
def observableIdentityTrans {first middle last : State}
    (firstPath : observableIdentity R first middle)
    (secondPath : observableIdentity R middle last) :
    observableIdentity R first last :=
  ⟨firstPath.down.trans secondPath.down⟩

private theorem jTransport_comp_eq {A : Type} (P : A → Type)
    {left middle right : A} (first : left = middle)
    (second : middle = right) (value : P left) :
    (familiesIdentityTypes.j (mode := stageOfNat 0) (Γ := PUnit)
      (fun _ => A)
      (fun total => P total.1.1.2 → P total.1.2)
      (fun _ argument => argument))
        ⟨⟨⟨PUnit.unit, left⟩, right⟩, ⟨first.trans second⟩⟩ value =
    (familiesIdentityTypes.j (mode := stageOfNat 0) (Γ := PUnit)
      (fun _ => A)
      (fun total => P total.1.1.2 → P total.1.2)
      (fun _ argument => argument))
        ⟨⟨⟨PUnit.unit, middle⟩, right⟩, ⟨second⟩⟩
      ((familiesIdentityTypes.j (mode := stageOfNat 0) (Γ := PUnit)
        (fun _ => A)
        (fun total => P total.1.1.2 → P total.1.2)
        (fun _ argument => argument))
          ⟨⟨⟨PUnit.unit, left⟩, middle⟩, ⟨first⟩⟩ value) := by
  cases first
  cases second
  rfl

/-- Dependent transport along composed observable identities is composition
of transports, as required for a coherent action on dependent fibres. -/
theorem observableJTransport_trans (P : ObsState R → Type)
    {first middle last : State}
    (firstPath : observableIdentity R first middle)
    (secondPath : observableIdentity R middle last)
    (value : P (classOf R first)) :
    observableJTransport R P
      (observableIdentityTrans R firstPath secondPath) value =
    observableJTransport R P secondPath
      (observableJTransport R P firstPath value) := by
  exact jTransport_comp_eq P firstPath.down secondPath.down value

/-- Contextual WM computation supplies an identity witness in Prime's
semantic observable-state fibre, using the existing subject-reduction proof. -/
def contextualComputationIdentity (laws : R.CoreLaws)
    {source target : WMTerm .state} (steps : WMContextStepStar source target) :
    observableIdentity R (R.denote source) (R.denote target) :=
  ⟨(classOf_eq_iff_agree R _ _).mpr (laws.agree_of_contextStepStar steps)⟩

/-- The identity witness produced by a WM computation acts on every
dependent family over observable states via the existing semantic J. -/
def contextualJTransport (laws : R.CoreLaws)
    {source target : WMTerm .state} (steps : WMContextStepStar source target)
    (P : ObsState R → Type) :
    P (classOf R (R.denote source)) → P (classOf R (R.denote target)) :=
  observableJTransport R P (contextualComputationIdentity R laws steps)

/-- The identity assigned to a composite contextual computation is the
composite identity in the observable quotient. The equality is proof
irrelevance at the quotient identity fibre, not an identification of
operational occurrence histories. -/
theorem contextualComputationIdentity_trans (laws : R.CoreLaws)
    {source middle target : WMTerm .state}
    (first : WMContextStepStar source middle)
    (second : WMContextStepStar middle target) :
    contextualComputationIdentity R laws (first.trans second) =
      observableIdentityTrans R
        (contextualComputationIdentity R laws first)
        (contextualComputationIdentity R laws second) := by
  cases contextualComputationIdentity R laws (first.trans second)
  cases observableIdentityTrans R
    (contextualComputationIdentity R laws first)
    (contextualComputationIdentity R laws second)
  rfl

/-- Consequently a multi-step WM computation acts functorially on each
semantic dependent family over observable states. -/
theorem contextualJTransport_trans (laws : R.CoreLaws)
    {source middle target : WMTerm .state}
    (first : WMContextStepStar source middle)
    (second : WMContextStepStar middle target)
    (P : ObsState R → Type)
    (value : P (classOf R (R.denote source))) :
    contextualJTransport R laws (first.trans second) P value =
      contextualJTransport R laws second P
        (contextualJTransport R laws first P value) := by
  dsimp [contextualJTransport]
  rw [contextualComputationIdentity_trans R laws first second]
  exact observableJTransport_trans R P
    (contextualComputationIdentity R laws first)
    (contextualComputationIdentity R laws second) value

/-- The theorem-list backend supplies distinct raw histories that inhabit
the same observable identity fibre. Hence this specialization of Prime's
semantic J is not an unqualified identity former for backend states. -/
theorem theoremList_observableIdentity_not_rawIdentity
    (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    let first := (theoremListReading atoms).denote
      (WMTerm.revise (.state (atoms.name axiomP)) (.state (atoms.name axiomQ)))
    let second := (theoremListReading atoms).denote
      (WMTerm.revise (.state (atoms.name axiomQ)) (.state (atoms.name axiomP)))
    Nonempty (observableIdentity (theoremListReading atoms) first second) ∧
      first ≠ second := by
  dsimp
  obtain ⟨_, distinct, agree⟩ :=
    revisionComm_changes_list_keeps_membership atoms readsBack
  exact ⟨(observableIdentity_iff_agree _ _ _).mpr agree, distinct⟩

end Mettapedia.TypeTheory.Models.RevisionedFamilies.ObservableIdentitySemantics
