import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Varying dependent motives and the separate sum-eta obligation

The positive model uses genuinely varying domains, second-component types
and a motive depending on both supplied witnesses. A nonidentity base
substitution changes those types and the actual computation.

The negative model retains an extra Boolean in each sum. Its projections
satisfy beta and strict substitution, but pairing omits that Boolean. A
motive detecting the omitted value has an inhabited branch and no section
over the whole sum context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSumComprehensionControls

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualSumComprehension

universe u

/-- Ordinary dependent sums supply all the local capabilities on set families. -/
def familySums : StableSums (familiesCwf.{u}) where
  operations := Families.sums
  beta := SigmaOperations.ofQualified_beta ContextualSumComparison.familiesSums
  eta := by
    intro Γ A B p
    funext γ
    change Sigma.mk (p γ).1 (p γ).2 = p γ
    cases p γ
    rfl
  substitution := Families.sums_substitution

abbrev varyingDomain (n : Nat) : Type := Fin (n + 1)

abbrev varyingCodomain (point : Σ n : Nat, varyingDomain n) : Type :=
  Fin (point.1 + point.2.val + 1)

abbrev varyingMotive (point : sumContext familySums varyingDomain varyingCodomain) : Type :=
  Fin (point.1 + point.2.1.val + point.2.2.val + 1)

theorem varying_pack (point : tupleContext (C := familiesCwf.{0}) varyingDomain varyingCodomain) :
    pack familySums varyingDomain varyingCodomain point =
      ⟨point.1.1, ⟨point.1.2, point.2⟩⟩ := rfl

theorem varying_unpack (point : sumContext familySums varyingDomain varyingCodomain) :
    unpack familySums varyingDomain varyingCodomain point =
      ⟨⟨point.1, point.2.1⟩, point.2.2⟩ := rfl

/-- The branch retains the exact second witness in a type depending on both. -/
def varyingBody :
    (familiesCwf.{0}).Tm (tupleContext (C := familiesCwf.{0}) varyingDomain varyingCodomain)
      ((familiesCwf.{0}).tySub varyingMotive
        (pack familySums varyingDomain varyingCodomain)) := fun point => by
  change Fin (point.1.1 + point.1.2.val + point.2.val + 1)
  exact ⟨point.2.val, by omega⟩

theorem varying_elimination_readout
    (point : sumContext familySums varyingDomain varyingCodomain) :
    (eliminate familySums varyingDomain varyingCodomain varyingMotive varyingBody point).val =
      point.2.2.val := rfl

theorem varying_elimination_beta :
    (familiesCwf.{0}).tmSub
        (eliminate familySums varyingDomain varyingCodomain varyingMotive varyingBody)
        (pack familySums varyingDomain varyingCodomain) = varyingBody :=
  eliminate_beta familySums varyingDomain varyingCodomain varyingMotive varyingBody

theorem varying_elimination_eta :
    eliminate familySums varyingDomain varyingCodomain varyingMotive
        ((familiesCwf.{0}).tmSub
          (eliminate familySums varyingDomain varyingCodomain varyingMotive varyingBody)
          (pack familySums varyingDomain varyingCodomain)) =
      eliminate familySums varyingDomain varyingCodomain varyingMotive varyingBody :=
  eliminate_eta familySums varyingDomain varyingCodomain varyingMotive _

def shift (n : Nat) : Nat := n + 2

def shiftedPoint (n : Nat) :
    sumContext familySums ((familiesCwf.{0}).tySub varyingDomain shift)
      ((familiesCwf.{0}).tySub varyingCodomain
        (TypeOver.extensionSubstitution (C := familiesCwf.{0}) shift varyingDomain)) :=
  ⟨n, ⟨⟨n, by change n < n + 2 + 1; omega⟩,
    ⟨n + 1, by change n + 1 < n + 2 + n + 1; omega⟩⟩⟩

theorem shifted_context_readout (n : Nat) :
    sumReindex familySums shift varyingDomain varyingCodomain (shiftedPoint n) =
      ⟨n + 2, (shiftedPoint n).2⟩ := rfl

theorem omitted_base_shift_is_detected (n : Nat) :
    (sumReindex familySums shift varyingDomain varyingCodomain (shiftedPoint n)).1 ≠ n := by
  rw [shifted_context_readout]
  change n + 2 ≠ n
  omega

theorem shifted_elimination_readout (n : Nat) :
    ((familiesCwf.{0}).tmSub
      (eliminate familySums varyingDomain varyingCodomain varyingMotive varyingBody)
      (sumReindex familySums shift varyingDomain varyingCodomain) (shiftedPoint n)).val = n + 1 := rfl

/-- The reindexed branch and independently reindexed motive give the same
full-motive computation at the supplied nonidentity context arrow. -/
theorem shifted_elimination_substitution :
    (familiesCwf.{0}).tmSub
        (eliminate familySums varyingDomain varyingCodomain varyingMotive varyingBody)
        (sumReindex familySums shift varyingDomain varyingCodomain) =
      eliminate familySums ((familiesCwf.{0}).tySub varyingDomain shift)
        ((familiesCwf.{0}).tySub varyingCodomain
          (TypeOver.extensionSubstitution (C := familiesCwf.{0}) shift varyingDomain))
        ((familiesCwf.{0}).tySub varyingMotive
          (sumReindex familySums shift varyingDomain varyingCodomain))
        (reindexBody familySums shift varyingDomain varyingCodomain varyingMotive varyingBody) :=
  eliminate_substitution familySums shift varyingDomain varyingCodomain varyingMotive varyingBody

/-- Both the second-component type and the elimination motive truly vary. -/
theorem varying_fibre_cardinalities :
    Fintype.card (varyingDomain 0) = 1 ∧ Fintype.card (varyingDomain 1) = 2 ∧
      Fintype.card (varyingCodomain ⟨1, ⟨0, by decide⟩⟩) = 2 ∧
      Fintype.card (varyingCodomain ⟨1, ⟨1, by decide⟩⟩) = 3 ∧
      Fintype.card (varyingMotive ⟨1, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩) = 3 ∧
      Fintype.card (varyingMotive ⟨1, ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩⟩) = 4 := by
  decide

/-! ## Beta and substitution do not supply eta or full elimination -/

def hiddenOperations : SigmaOperations (familiesCwf.{u}) where
  sigma A B γ := (Σ a : A γ, B ⟨γ, a⟩) × Bool
  pair a b γ := (⟨a γ, b γ⟩, false)
  fst p γ := (p γ).1.1
  snd p γ := (p γ).1.2

theorem hidden_beta : SigmaBeta hiddenOperations.{u} := ⟨fun _ _ => rfl, fun _ _ => HEq.rfl⟩

theorem hidden_substitution : StrictSigmaSubstitution hiddenOperations.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro Γ Δ σ A B
    rfl
  · intro Γ Δ σ A B a b reindexedSecond same
    cases eq_of_heq same
    rfl
  · intro Γ Δ σ A B p reindexedValue same
    cases eq_of_heq same
    exact ⟨HEq.rfl, HEq.rfl⟩

def hiddenValue :
    (familiesCwf.{0}).Tm Nat (hiddenOperations.sigma varyingDomain varyingCodomain) :=
  fun n => (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩, true)

theorem hidden_eta_fails : ¬ SigmaEta hiddenOperations.{0} := by
  intro eta
  have tag := congrArg (fun value => (value 0).2) (eta hiddenValue)
  exact Bool.noConfusion tag

abbrev hiddenTuple := tupleContext (C := familiesCwf.{0}) varyingDomain varyingCodomain
abbrev hiddenContext := (familiesCwf.{0}).ext Nat
  (hiddenOperations.sigma varyingDomain varyingCodomain)

def hiddenPack (point : hiddenTuple) : hiddenContext :=
  ⟨point.1.1, (⟨point.1.2, point.2⟩, false)⟩

def hiddenUnpack (point : hiddenContext) : hiddenTuple :=
  ⟨⟨point.1, point.2.1.1⟩, point.2.1.2⟩

theorem hidden_unpack_pack : hiddenUnpack ∘ hiddenPack = id := rfl

theorem hidden_pack_unpack_fails : hiddenPack ∘ hiddenUnpack ≠ id := by
  intro same
  have tag := congrArg (fun map => (map ⟨0, hiddenValue 0⟩).2.2) same
  exact Bool.noConfusion tag

/-- The motive detects the actual extra value that the pair constructor omits. -/
def hiddenMotive (point : hiddenContext) : Type :=
  match point.2.2 with
  | false => PUnit
  | true => PEmpty

def hiddenBranch : (familiesCwf.{0}).Tm hiddenTuple
    ((familiesCwf.{0}).tySub hiddenMotive hiddenPack) := fun _ => PUnit.unit

theorem hidden_motive_has_no_section : IsEmpty ((familiesCwf.{0}).Tm hiddenContext hiddenMotive) :=
  ⟨fun certificate => (certificate ⟨0, hiddenValue 0⟩).elim⟩

/-- Even though every local beta and strict-substitution equation holds,
an eliminator for all full motives cannot exist for this context packing. -/
theorem hidden_has_no_full_elimination :
    ¬ Nonempty (∀ M : (familiesCwf.{0}).Ty hiddenContext,
      (familiesCwf.{0}).Tm hiddenTuple ((familiesCwf.{0}).tySub M hiddenPack) →
        (familiesCwf.{0}).Tm hiddenContext M) := by
  rintro ⟨elimination⟩
  exact (hidden_motive_has_no_section).false (elimination hiddenMotive hiddenBranch)

end Mettapedia.TypeTheory.ContextualSumComprehensionControls
