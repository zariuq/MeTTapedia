import Mettapedia.TypeTheory.PresheafNativePredicateContextTail
import Mettapedia.TypeTheory.PresheafNativePropositionSubstitution
import Mettapedia.TypeTheory.PresheafNativeRefinementTermSubstitution
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Varying native refinement and dependent suffix controls

The source fibre is `Fin (n + 2)`. Its predicate selects value one, and a
later native fibre is `Fin (a + 2)`, depending on that exact inhabitant.
Actual chosen introduction, substitution and suffix comparisons retain the
supplied receipts. Erasing inhabitants or suffix witnesses fails the
corresponding reconstruction controls.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateRefinementControls

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers
open PresheafNativePredicateRefinement PresheafNativePropositionReadout
open PresheafNativePropositionSubstitution PresheafNativeStableRefinement
open PresheafNativeRefinementTermSubstitution

abbrev World := Discrete Unit

abbrev programs : Worldᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := 𝟙 Nat
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev finiteFamily : DisplayedFamily programs where
  obj point := Fin (point.2 + 2)
  map arrow := TypeCat.ofHom fun value =>
    Fin.cast (congrArg (fun n : Nat => n + 2) arrow.property) value
  map_id _ := by ext value; rfl
  map_comp _ _ := by ext value; rfl

abbrev argument : NativeType programs := LocalType.present finiteFamily

def world : Worldᵒᵖ := Opposite.op (Discrete.mk ())

def selectOne : Subfunctor (totalSpace argument.decoded) where
  obj _ := {receipt | receipt.2.val = 1}
  map _ _ belongs := belongs

def oneSection : argument.decoded.sections where
  val point := ⟨1, by omega⟩
  property := by
    intro first second arrow
    apply Fin.ext
    rfl

theorem oneSatisfies (world : Worldᵒᵖ) (n : programs.obj world) :
    (⟨n, oneSection.val ⟨world, n⟩⟩ : (totalSpace argument.decoded).obj world) ∈
      selectOne.obj world := rfl

noncomputable def introduced := intro argument selectOne oneSection oneSatisfies

theorem actual_introduction_retains_the_term : forget argument selectOne introduced = oneSection :=
  beta argument selectOne oneSection oneSatisfies

theorem introduced_readout (n : Nat) :
    (forget argument selectOne introduced).val ⟨world, n⟩ = (⟨1, by omega⟩ : Fin (n + 2)) := by
  rw [actual_introduction_retains_the_term]
  rfl

def advance : programs ⟶ programs where
  app _ := TypeCat.ofHom Nat.succ
  naturality := by intros; rfl

theorem actual_substitution_changes_the_fibre (n : Nat) :
    (argument.reindex advance).decoded.obj ⟨world, n⟩ = Fin (n + 3) := rfl

theorem omitted_substitution_has_the_wrong_fibre :
    (argument.reindex advance).decoded.obj ⟨world, 0⟩ ≠ argument.decoded.obj ⟨world, 0⟩ := by
  change Fin 3 ≠ Fin 2
  intro same
  have card := Fintype.card_congr (Equiv.cast same)
  simp only [Fintype.card_fin] at card
  exact (by decide : (3 : Nat) ≠ 2) card

theorem actual_native_introduction_substitution :
    substituteChosen advance argument selectOne introduced =
      intro (argument.reindex advance)
        (selectOne.preimage (totalReindexMap advance argument.decoded))
        (substituteTerm (C := presheafCwf World) (type := argument) oneSection advance)
        (substitutedSatisfaction advance argument selectOne oneSection oneSatisfies) :=
  introduction_substitution advance argument selectOne oneSection oneSatisfies

theorem actual_native_proposition_substitution :
    nativeHolds (substituteNative (totalReindexMap advance argument.decoded)
      (nativeQuote selectOne)) = selectOne.preimage (totalReindexMap advance argument.decoded) := by
  rw [nativeHolds_substituteNative, nativeHolds_nativeQuote]

theorem zero_excluded (n : Nat) :
    (⟨n, (⟨0, by omega⟩ : Fin (n + 2))⟩ : (totalSpace argument.decoded).obj world) ∉
      selectOne.obj world := by
  change (0 : Nat) ≠ 1
  decide

def argumentName : totalSpace argument.decoded ⟶ programs where
  app _ := TypeCat.ofHom fun receipt => receipt.2.val
  naturality := by intros; rfl

abbrev laterArgument : NativeType (totalSpace argument.decoded) :=
  ⟨programs, finiteFamily, argumentName⟩

def supplied (n : Nat) (later : Fin 3) :
    (PresheafNativePredicateContextTail.selected argument selectOne
      (totalProjection laterArgument.decoded)).obj world :=
  ⟨⟨⟨n, (⟨1, by omega⟩ : Fin (n + 2))⟩, later⟩, rfl⟩

noncomputable def retained (n : Nat) (later : Fin 3) :
    (totalSpace (PresheafNativePredicateTail.suffix argument selectOne laterArgument).decoded).obj world :=
  (PresheafNativePredicateContextTail.familySuffixIso argument selectOne laterArgument).inv.app world
    (supplied n later)

theorem whole_suffix_readout (n : Nat) (later : Fin 3) :
    (PresheafNativePredicateTail.suffixMap argument selectOne laterArgument).app world (retained n later) =
      (supplied n later).val := by
  have square := PresheafNativePredicateContextTail.familySuffixIso_whole argument selectOne laterArgument
  have inverseSquare :
      (PresheafNativePredicateContextTail.familySuffixIso argument selectOne laterArgument).inv ≫
        PresheafNativePredicateTail.suffixMap argument selectOne laterArgument =
      PresheafNativePredicateContextTail.includeSuffix argument selectOne
        (totalProjection laterArgument.decoded) := by
    rw [← square, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app inverseSquare world) (supplied n later)

theorem original_and_later_witnesses_retained (n : Nat) (later : Fin 3) :
    ((PresheafNativePredicateTail.suffixMap argument selectOne laterArgument).app world
      (retained n later)).1.1 = n ∧
    ((PresheafNativePredicateTail.suffixMap argument selectOne laterArgument).app world
      (retained n later)).1.2.val = 1 ∧
    ((PresheafNativePredicateTail.suffixMap argument selectOne laterArgument).app world
      (retained n later)).2.val = later.val := by
  rw [whole_suffix_readout]
  exact ⟨rfl, rfl, rfl⟩

def dependentConsequent : Subfunctor (totalSpace laterArgument.decoded) where
  obj _ := {receipt | receipt.1.2.val = 1 ∧ receipt.2.val < 3}
  map _ _ belongs := belongs

theorem guarded_consequent :
    PresheafNativePredicateTail.suffixGuard argument selectOne laterArgument ≤ dependentConsequent := by
  intro context receipt belongs
  refine ⟨belongs, ?_⟩
  have bound := receipt.2.isLt
  change receipt.2.val < receipt.1.2.val + 2 at bound
  change receipt.1.2.val = 1 at belongs
  simpa only [belongs] using bound

theorem actual_dependent_cElimination :
    ⊤ ≤ dependentConsequent.preimage
      (PresheafNativePredicateTail.suffixMap argument selectOne laterArgument) :=
  PresheafNativePredicateTail.eliminateConsequent argument selectOne laterArgument
    dependentConsequent guarded_consequent

theorem later_witnesses_remain_distinct (n : Nat) :
    retained n (⟨0, by decide⟩ : Fin 3) ≠ retained n (⟨2, by decide⟩ : Fin 3) := by
  intro same
  have readout := congrArg (fun receipt =>
    ((PresheafNativePredicateTail.suffixMap argument selectOne laterArgument).app world receipt).2.val) same
  rw [whole_suffix_readout, whole_suffix_readout] at readout
  exact (by decide : (0 : Nat) ≠ 2) readout

/-- Erasing the selected inhabitant to its base program cannot satisfy
comprehension eta, even when the predicate is true everywhere. -/
theorem base_support_cannot_reconstruct_inhabitants :
    ¬ ∃ decode : programs.obj world → (totalSpace (displayed argument.decoded ⊤)).obj world,
      ∀ receipt, decode ((totalProjection (displayed argument.decoded ⊤)).app world receipt) = receipt := by
  rintro ⟨decode, recovers⟩
  let first : (totalSpace (displayed argument.decoded ⊤)).obj world :=
    ⟨0, ⟨(⟨0, by decide⟩ : Fin 2), trivial⟩⟩
  let second : (totalSpace (displayed argument.decoded ⊤)).obj world :=
    ⟨0, ⟨(⟨1, by decide⟩ : Fin 2), trivial⟩⟩
  have same : first = second := (recovers first).symm.trans (recovers second)
  have values := congrArg (fun receipt => receipt.2.val.val) same
  exact (by decide : (0 : Nat) ≠ 1) values

end Mettapedia.TypeTheory.PresheafNativePredicateRefinementControls
