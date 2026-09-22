import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.Presentation
import Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport
import Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading

/-!
# Observable WM families in the staged families semantic CwF

The staged-reflective presentation already has a noncollapsed semantic
families CwF. At its base stage, the WM observational quotient is a context
and `classOf` is a substitution into it. A raw-state dependent type comes
from that context exactly when its fibres are equal on behaviorally agreeing
states. The positive example depends on a query answer; the negative example
remembers literal raw-state identity and therefore cannot descend when a
reading hides a state distinction.

These are semantic families in the staged families model, not new authored
syntax, an identity eliminator, or a proof that the WM quotient is the
selected identity type.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyDescent

open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport

variable {State Query V : Type}

/-- The observable WM state carrier is a context in the staged families
base-stage semantic families CwF. -/
def observableContext (R : WMReading State Query V) :
    familiesCwF.Con (stageOfNat 0) := ObsState R

/-- The observational quotient map is an actual CwF substitution from raw
states to the observable context. -/
def observationSub (R : WMReading State Query V) :
    familiesCwF.Sub State (observableContext R) := classOf R

/-- Data of an observable family whose pullback is the given raw-state
dependent family. Keeping the family itself in `Type` permits computational
transport; its mere existence is the `Prop` below. -/
structure DescentData (R : WMReading State Query V) (F : State → Type) where
  family : familiesCwF.Ty (observableContext R)
  pullback : F = familiesCwF.tySub family (observationSub R)

def Descends (R : WMReading State Query V) (F : State → Type) : Prop :=
  Nonempty (DescentData R F)

/-- Coherent raw families are constructively packaged over the observable
context. This retains the family itself rather than only its existence. -/
def descentDataOfInvariant (R : WMReading State Query V)
    (F : State → Type)
    (invariant : ∀ first second,
      R.Agree .state first second → F first = F second) :
    DescentData R F where
  family := Quotient.lift F
    (fun first second agree => invariant first second agree)
  pullback := by
    funext state
    rfl

/-- Quotient descent is exactly invariance of the dependent type itself
under all WM observations. Equality of fibres, not merely equivalence of
their inhabitant sets, is the coherence required by this CwF substitution. -/
theorem descends_iff_agree_invariant (R : WMReading State Query V)
    (F : State → Type) :
    Descends R F ↔
      ∀ first second, R.Agree .state first second → F first = F second := by
  constructor
  · rintro ⟨⟨P, rfl⟩⟩ first second agree
    exact congrArg P ((classOf_eq_iff_agree R first second).2 agree)
  · intro invariant
    exact ⟨descentDataOfInvariant R F invariant⟩

/-- Reindexing an observable dependent family first along the quotient map
and then along an arbitrary raw-state substitution is the same as reindexing
along their CwF composite. -/
theorem observable_reindex_comp (R : WMReading State Query V)
    (P : familiesCwF.Ty (observableContext R))
    {Γ : Type} (substitution : Γ → State) :
    familiesCwF.tySub P
      (familiesCwF.scomp substitution (observationSub R)) =
    familiesCwF.tySub
      (familiesCwF.tySub P (observationSub R)) substitution := by
  exact familiesCwF.tySub_comp P substitution (observationSub R)

/-- The observable substitution extends across dependent comprehension:
the evidence in the second coordinate remains in its original fibre. -/
def comprehensionSub (R : WMReading State Query V)
    (P : familiesCwF.Ty (observableContext R)) :
    familiesCwF.Sub
      (familiesCwF.ext State
        (familiesCwF.tySub P (observationSub R)))
      (familiesCwF.ext (observableContext R) P) :=
  fun pair => ⟨classOf R pair.1, pair.2⟩

theorem comprehensionSub_projection (R : WMReading State Query V)
    (P : familiesCwF.Ty (observableContext R)) :
    familiesCwF.scomp (comprehensionSub R P) (familiesCwF.wk P) =
      familiesCwF.scomp
        (familiesCwF.wk (familiesCwF.tySub P (observationSub R)))
        (observationSub R) := by
  rfl

/-- Descent supplies dependent transport along behavioral agreement inside
Prime's semantic CwF, without pretending the raw states are equal. -/
def transportOfDescent (R : WMReading State Query V)
    {F : State → Type} (descent : DescentData R F)
    {first second : State} (agree : R.Agree .state first second) :
    F first → F second := by
  obtain ⟨P, equal⟩ := descent
  subst F
  exact transportQuotientFamily R P agree

/-- The family that records whether one particular query extracts zero is
observable and can therefore be reindexed through the quotient context. -/
def zeroEvidenceFamily (R : WMReading State Query V) (query : Query) :
    State → Type :=
  fun state => { _witness : Unit // R.extract state query = R.zero }

theorem zeroEvidenceFamily_descends (R : WMReading State Query V)
    (query : Query) : Descends R (zeroEvidenceFamily R query) := by
  apply (descends_iff_agree_invariant R _).2
  intro first second agree
  exact congrArg (fun value : V => { _witness : Unit // value = R.zero }) (agree query)

/-- A retained CwF descent witness for the nonconstant answer-sensitive
family, suitable for actual dependent transport. -/
def zeroEvidenceFamilyDescentData (R : WMReading State Query V)
    (query : Query) : DescentData R (zeroEvidenceFamily R query) :=
  descentDataOfInvariant R _
    ((descends_iff_agree_invariant R _).1 (zeroEvidenceFamily_descends R query))

/-- This positive family is genuinely state-dependent whenever some query
distinguishes zero evidence from nonzero evidence. -/
theorem zeroEvidenceFamily_nonconstant (R : WMReading State Query V)
    (query : Query) (first second : State)
    (zero : R.extract first query = R.zero)
    (nonzero : R.extract second query ≠ R.zero) :
    zeroEvidenceFamily R query first ≠ zeroEvidenceFamily R query second := by
  intro equal
  have atFirst : zeroEvidenceFamily R query first := ⟨(), zero⟩
  have atSecond : zeroEvidenceFamily R query second := cast equal atFirst
  exact nonzero atSecond.property

/-- Literal raw-state identity gives a counterexample to quotient descent
whenever two different states have exactly the same observable behavior. -/
theorem rawIdentityFamily_not_descend (R : WMReading State Query V)
    {first second : State} (distinct : first ≠ second)
    (agree : R.Agree .state first second) :
    ¬ Descends R (fun state => { _witness : Unit // state = first }) := by
  intro descent
  have equalFibres :=
    (descends_iff_agree_invariant R _).1 descent first second agree
  have atFirst : { _witness : Unit // first = first } := ⟨(), rfl⟩
  have atSecond : { _witness : Unit // second = first } := cast equalFibres atFirst
  exact distinct atSecond.property.symm

/-! ## A concrete multiplicity-space consumer -/

private def emptySpace : Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra.MSpace
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern := fun _ => 0

private def fullSpace : Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra.MSpace
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern := fun _ => 1

private def countReading : WMReading
    (Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra.MSpace
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) ℕ :=
  Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading.additiveReading
    (Ev := ℕ) (fun _ => emptySpace) (fun _ => [])

/-- Candidate-count evidence gives a genuinely nonconstant, yet
behaviorally invariant, dependent family in the actual MeTTa multiplicity
space reading. -/
theorem multiplicity_zeroFamily_nonconstant :
    zeroEvidenceFamily countReading
      [Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "x"] emptySpace ≠
    zeroEvidenceFamily countReading
      [Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "x"] fullSpace := by
  apply zeroEvidenceFamily_nonconstant
  · decide +kernel
  · decide +kernel

end Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyDescent
