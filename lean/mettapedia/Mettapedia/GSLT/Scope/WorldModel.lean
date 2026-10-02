import Mettapedia.GSLT.Scope.UpdateSquares
import Mettapedia.GSLT.Scope.ConsumerDescent
import Mettapedia.GSLT.Scope.Interaction
import Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport

/-!
# The world-model calculus under the scope algebra

A reading of the world-model calculus (`WMReading`) has an observational
quotient: two states are identified when every query extracts the same
evidence (`classOf`).  This module reads that quotient as a view in the sense
of the scope algebra and derives the calculus's existing results from the
general laws.

**Transport along the view.**  Agreement of two states is exactly transport
of every dependent family over the observational quotient
(`agree_iff_all_quotient_families_transport`); this is the instance of
`viewFamilies_transport_iff` whose view is `classOf`.  The raw-state boundary
is the instance of `transport_boundary`
(`distinct_agree_transport_boundary`).

**Revision is an update square.**  Revising by a fixed state is a supported
update of the observational quotient exactly when it respects agreement
(`supports_reviseRight_iff`, `supports_reviseLeft_iff`); all revisions are
supported exactly under the compositionality law `ReviseRespectsAgree`
(`revisions_supported_iff`).  The core laws imply it, and the abstract update
is the revision of the quotient reading: the square commutes by definition
(`quotient_revise_square`).
* Control: a reading whose revision exposes a hidden coordinate that no query
  reads.  Two states agree now and disagree after revising
  (`Hidden.revise_not_supported`); the reading cannot satisfy the core laws
  (`Hidden.not_coreLaws`).  Positive: the lawful counting reading supports
  every revision (`Counting.revisions_supported`).

**Consumers.**  Extraction of a query descends to the quotient
(`extract_descends`); any consumer that descends is invariant under every
contextual computation of the calculus (`descended_invariant_of_steps`).
Control: the hidden coordinate does not descend (`Hidden.hidden_not_descends`).

**Reading morphisms are forth maps.**  A reading morphism whose query map
covers the target queries satisfies the forth law for the two observational
quotients (`forth_of_surjective`), so forgetting commutes with
it in one direction (`saturation_subset_of_surjective`).  Control: a
lawful morphism whose query map misses a target query fails the forth law
(`QueryCoverage.not_forth`), the scope-algebra form of the calculus's
query-coverage canary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.WorldModel

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding

/-! ## Transport along the observational quotient -/

section Transport

variable {State Query V : Type} (R : WMReading State Query V)

/-- The observational class map is the quotient map of behavioural
agreement. -/
theorem classOf_eq_mk (state : State) :
    classOf R state = Quotient.mk (stateSetoid R) state :=
  rfl

/-- **Agreement is transport of every family over the observational
quotient**: the world-model instance of `viewFamilies_transport_iff`. -/
theorem agree_iff_all_quotient_families_transport (first second : State) :
    R.Agree .state first second ↔
      Nonempty (∀ P : ObsState R → Type, P (classOf R first) → P (classOf R second)) :=
  (classOf_eq_iff_agree R first second).symm.trans
    (viewFamilies_transport_iff (classOf R) first second).symm

/-- **The raw-state boundary**: distinct agreeing states transport every
family over the quotient and not every family over raw states.  This is the
instance of `transport_boundary`. -/
theorem distinct_agree_transport_boundary {first second : State} (distinct : first ≠ second)
    (agree : R.Agree .state first second) :
    Nonempty (∀ P : ObsState R → Type, P (classOf R first) → P (classOf R second)) ∧
      ¬ Nonempty (∀ P : State → Type, P first → P second) :=
  transport_boundary (classOf R) distinct ((classOf_eq_iff_agree R first second).mpr agree)

end Transport

/-! ## Revision as an update square -/

section Revision

variable {State Query V : Type} (R : WMReading State Query V)

/-- **Revising by a fixed update is supported by the observational quotient
exactly when it respects agreement.** -/
theorem supports_reviseRight_iff (update : State) :
    Supports (classOf R) (fun state => R.revise state update) ↔
      ∀ ⦃first second : State⦄, R.Agree .state first second →
        R.Agree .state (R.revise first update) (R.revise second update) :=
  supports_mk_iff (stateSetoid R) fun state => R.revise state update

/-- The same for revising a fixed base state by a varying update. -/
theorem supports_reviseLeft_iff (base : State) :
    Supports (classOf R) (R.revise base) ↔
      ∀ ⦃first second : State⦄, R.Agree .state first second →
        R.Agree .state (R.revise base first) (R.revise base second) :=
  supports_mk_iff (stateSetoid R) (R.revise base)

/-- **All revisions are supported updates of the observational quotient
exactly under the compositionality law of the calculus.** -/
theorem revisions_supported_iff :
    ((∀ update, Supports (classOf R) (fun state => R.revise state update)) ∧
        ∀ base, Supports (classOf R) (R.revise base)) ↔ R.ReviseRespectsAgree := by
  constructor
  · rintro ⟨right, left⟩
    exact ⟨fun first first' second agree => (supports_reviseRight_iff R second).mp
        (right second) agree,
      fun first second second' agree => (supports_reviseLeft_iff R first).mp
        (left first) agree⟩
  · intro respects
    exact ⟨fun update => (supports_reviseRight_iff R update).mpr
        fun first second agree => respects.left first second update agree,
      fun base => (supports_reviseLeft_iff R base).mpr
        fun first second agree => respects.right base first second agree⟩

/-- Under the core laws every revision is a supported update. -/
theorem revisions_supported_of_coreLaws {R : WMReading State Query V} (laws : R.CoreLaws) :
    (∀ update, Supports (classOf R) (fun state => R.revise state update)) ∧
      ∀ base, Supports (classOf R) (R.revise base) :=
  (revisions_supported_iff R).mpr laws.reviseRespectsAgree

/-- **The abstract update is the revision of the quotient reading**: the
square commutes by definition. -/
theorem quotient_revise_square (laws : R.CoreLaws) (state update : State) :
    classOf R (R.revise state update) =
      (quotientReading R laws).revise (classOf R state) (classOf R update) :=
  rfl

/-- Every revision iterates as a supported update. -/
theorem revision_iterate_supported {R : WMReading State Query V} (laws : R.CoreLaws)
    (update : State) (n : ℕ) :
    Supports (classOf R) (fun state => R.revise state update)^[n] :=
  (revisions_supported_of_coreLaws laws).1 update |>.iterate n

end Revision

/-! ## Consumers of the world state -/

section Consumers

variable {State Query V : Type} (R : WMReading State Query V)

/-- **Extraction of a query descends to the observational quotient.** -/
theorem extract_descends (query : Query) :
    Factors (classOf R) fun state => R.extract state query :=
  (function_descends_iff (stateSetoid R) fun state => R.extract state query).mpr
    fun _ _ agree => agree query

/-- **Descended consumers are invariant under computation**: every contextual
computation of the calculus preserves the observational class, so a consumer
of the quotient reads the same value before and after. -/
theorem descended_invariant_of_steps (laws : R.CoreLaws) {Z : Sort*}
    {consumer : State → Z} (descends : Factors (classOf R) consumer)
    {first second : WMTerm .state} (steps : WMContextStepStar first second) :
    consumer (R.denote first) = consumer (R.denote second) :=
  descends.constantOnFibers _ _
    ((classOf_eq_iff_agree R _ _).mpr (laws.agree_of_contextStepStar steps))

end Consumers

/-! ### Control: a hidden coordinate -/

namespace Hidden

/-- States carry a visible and a hidden bit; the only query reads the visible
bit, and revision exposes the hidden bit of its first argument. -/
def reading : WMReading (Bool × Bool) Unit Bool where
  revise first _ := (first.2, first.2)
  extract state _ := state.1
  combine := (· || ·)
  zero := false
  world _ := (false, false)
  query _ := ()

/-- The two states agree now: they have the same visible bit. -/
theorem agree_now : reading.Agree .state (true, true) (true, false) :=
  fun _ => rfl

/-- **Identified now, separated by the next revision.** -/
theorem revise_not_supported (update : Bool × Bool) :
    ¬ Supports (classOf reading) (fun state => reading.revise state update) := by
  intro supported
  have agree := (supports_reviseRight_iff reading update).mp supported agree_now
  exact Bool.noConfusion (agree () : true = false)

/-- Hence the reading does not satisfy the core laws of the calculus. -/
theorem not_coreLaws : ¬ reading.CoreLaws := fun laws =>
  revise_not_supported (false, false) ((revisions_supported_of_coreLaws laws).1 (false, false))

/-- **The hidden coordinate does not descend to the quotient.** -/
theorem hidden_not_descends : ¬ Factors (classOf reading) Prod.snd :=
  NonTrivialFiber.not_factors
    ⟨(true, true), (true, false), (classOf_eq_iff_agree reading _ _).mpr agree_now,
      Bool.noConfusion⟩

end Hidden

/-! ### Positive control: counting evidence -/

namespace Counting

/-- States are counts; revision adds counts; the only query reads the
count. -/
def reading : WMReading ℕ Unit ℕ where
  revise := (· + ·)
  extract state _ := state
  combine := (· + ·)
  zero := 0
  world _ := 0
  query _ := ()

theorem coreLaws : reading.CoreLaws where
  extract_revise _ _ _ := rfl
  combine_comm := Nat.add_comm
  combine_assoc := Nat.add_assoc
  combine_zero := Nat.add_zero

/-- **Every revision of the counting reading is supported.** -/
theorem revisions_supported :
    (∀ update, Supports (classOf reading) (fun state => reading.revise state update)) ∧
      ∀ base, Supports (classOf reading) (reading.revise base) :=
  revisions_supported_of_coreLaws coreLaws

end Counting

/-! ## Reading morphisms satisfy the forth law -/

section Morphisms

variable {State₁ Query₁ V₁ State₂ Query₂ V₂ : Type}
  {source : WMReading State₁ Query₁ V₁} {target : WMReading State₂ Query₂ V₂}

/-- **A reading morphism covering the target queries satisfies the forth
law** for the two observational quotients. -/
theorem forth_of_surjective (hom : ReadingMorphism source target)
    (query_surjective : Function.Surjective hom.mapQuery) :
    Forth hom.mapState (stateSetoid target) (stateSetoid source) :=
  fun _ _ agree => hom.agree_map query_surjective .state agree

/-- Forgetting then mapping lies inside mapping then forgetting. -/
theorem saturation_subset_of_surjective (hom : ReadingMorphism source target)
    (query_surjective : Function.Surjective hom.mapQuery) (K : Set State₂) :
    Mettapedia.Logic.TheoryModel.saturation (stateSetoid source) (hom.mapState ⁻¹' K) ⊆
      hom.mapState ⁻¹' Mettapedia.Logic.TheoryModel.saturation (stateSetoid target) K :=
  saturation_preimage_subset (forth_of_surjective hom query_surjective) K

end Morphisms

/-! ### Control: a reading morphism without query coverage -/

namespace QueryCoverage

/-- A source reading with one uninformative query. -/
def narrow : WMReading Bool Unit Bool where
  revise := (· || ·)
  extract _ _ := false
  combine := (· || ·)
  zero := false
  world _ := false
  query _ := ()

/-- A target reading whose second query separates the two states. -/
def wide : WMReading Bool Bool Bool where
  revise := (· || ·)
  extract state query := state && query
  combine := (· || ·)
  zero := false
  world _ := false
  query _ := false

/-- The morphism exposes only the target query `false`. -/
def inclusion : ReadingMorphism narrow wide where
  mapState := id
  mapQuery _ := false
  mapEvidence := id
  revise_comm _ _ := rfl
  extract_comm state query := by cases state <;> cases query <;> rfl
  combine_comm _ _ := rfl
  zero_comm := rfl
  world_comm _ := rfl
  query_comm _ := rfl

/-- The query map misses `true`. -/
theorem not_surjective : ¬ Function.Surjective inclusion.mapQuery := fun surjective =>
  let ⟨_, hit⟩ := surjective true
  Bool.noConfusion hit

/-- **Control: without query coverage the forth law fails.** -/
theorem not_forth : ¬ Forth inclusion.mapState (stateSetoid wide) (stateSetoid narrow) := by
  intro forth
  have agree : wide.Agree .state true false := forth (fun _ => rfl)
  exact Bool.noConfusion (agree true : true = false)

end QueryCoverage

end Mettapedia.GSLT.Scope.WorldModel
