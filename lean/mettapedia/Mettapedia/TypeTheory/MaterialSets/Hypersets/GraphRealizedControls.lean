import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetTheory
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedReceiptFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedAntiFoundation

/-!
# Discriminating controls for the constructive realized material model

The controls use cyclic sets, infinitely many inequivalent finite
ordinals, a genuinely varying dependent member family and separately
retained duplicate hypothesis occurrences. Erasing witness evidence has
no inverse preserving both occurrences. Native products and material
membership cannot recover evidence which their readout discarded.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedControls

open GraphBisimulationRealizers GraphSetRealization GraphSetOperations GraphFormulaRealization
open GraphRealizedSetConstructors GraphRealizedReceiptFamilies

universe u

def loop : Graph.{u} :=
  GraphRealizedAntiFoundation.canonical (fun first second : PUnit.{u+1} => first = second) PUnit.unit

def loopChild : Receipts loop := ⟨loop.point, rfl⟩

def loopSelfMember : Member loop loop :=
  Member.transportChild (repointPoint loop) (Member.atChild loop loopChild)

def loopSingleton : Equal loop (singleton loop) :=
  extensionality
    (fun _ member => singletonIntro (member.2.trans (by
      have same : member.1.val = loop.point := Subtype.ext (Subsingleton.elim _ _)
      exact same ▸ repointPoint loop)))
    (fun _ member => Member.transportChild (singletonEliminate member).symm loopSelfMember)

theorem loop_not_empty : ¬ Nonempty (Equal loop AccessiblePointedGraph.empty.{u}) := by
  rintro ⟨same⟩
  exact PEmpty.elim (emptyEliminate (Member.transportParent same loopSelfMember))

/-- Distinct ordinal indices remain distinct under realized equality. -/
theorem ordinalOrder (first second : Nat) (same : Equal (ordinal.{u} first) (ordinal second)) :
    first ≤ second := by
  induction first using Nat.strong_induction_on generalizing second with
  | h first previous =>
    cases first with
    | zero => exact Nat.zero_le _
    | succ first =>
      let member := Member.transportParent same
        (ordinalIntro (Nat.lt_succ_self first) (Equal.refl (ordinal first)))
      let decoded := ordinalEliminate second member
      have smaller := previous first (Nat.lt_succ_self first) decoded.1.val decoded.2
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt smaller decoded.1.isLt)

theorem ordinalEquality (first second : Nat) (same : Equal (ordinal.{u} first) (ordinal second)) :
    first = second :=
  Nat.le_antisymm (ordinalOrder first second same) (ordinalOrder second first same.symm)

theorem ordinalDistinct {first second : Nat} (different : first ≠ second) :
    ¬ Nonempty (Equal (ordinal.{u} first) (ordinal second)) := by
  rintro ⟨same⟩
  exact different (ordinalEquality first second same)

/-- Infinity has a member beyond every finite ordinal list. -/
theorem infinity_unbounded (bound : Nat) :
    ∃ value : Graph.{u}, Nonempty (Member value infinity) ∧
      ∀ index ≤ bound, ¬ Nonempty (Equal value (ordinal index)) := by
  refine ⟨ordinal (bound+1), ⟨infinityIntro (bound+1) (Equal.refl _)⟩, ?_⟩
  intro index small
  exact ordinalDistinct (by omega)

def ordinalReceipt (bound : Nat) (index : Fin bound) : Receipts (ordinal.{u} bound) :=
  (ordinalIntro index.isLt (Equal.refl (ordinal index.val))).1

def ordinalReceiptPicture (bound : Nat) (index : Fin bound) :
    Equal (ordinal.{u} index.val) ((ordinal bound).repoint (ordinalReceipt bound index).val) :=
  (ordinalIntro index.isLt (Equal.refl (ordinal index.val))).2

def varyingDomain : Graph.{u} := ordinal 2
def varyingBody (argument : Receipts varyingDomain.{u}) : Graph.{u} := varyingDomain.repoint argument.val
def zeroArgument : Receipts varyingDomain.{u} := ordinalReceipt 2 ⟨0, by decide⟩
def oneArgument : Receipts varyingDomain.{u} := ordinalReceipt 2 ⟨1, by decide⟩

theorem zeroFibre_empty : IsEmpty (Receipts (varyingBody zeroArgument.{u})) := by
  constructor
  intro receipt
  let member := Member.transportParent (ordinalReceiptPicture 2 ⟨0, by decide⟩).symm
    (Member.atChild (varyingBody zeroArgument) receipt)
  exact False.elim (Nat.not_lt_zero _ (ordinalEliminate 0 member).1.isLt)

def oneFibreMember : Receipts (varyingBody oneArgument.{u}) :=
  (Member.transportParent (ordinalReceiptPicture 2 ⟨1, by decide⟩)
    (ordinalIntro (by decide : 0 < 1) (Equal.refl (ordinal 0)))).1

def varyingSumReceipt : Receipts (sigmaGraph varyingDomain.{u} varyingBody) :=
  pairReceipts _ _ oneArgument oneFibreMember

theorem varyingProduct_empty : IsEmpty (Receipts (piGraph varyingDomain.{u} varyingBody)) := by
  constructor
  intro function
  exact zeroFibre_empty.false (application _ _ function zeroArgument)

theorem varyingFibres_not_equivalent :
    ¬ Nonempty (Receipts (varyingBody zeroArgument.{u}) ≃ Receipts (varyingBody oneArgument)) := by
  rintro ⟨comparison⟩
  exact zeroFibre_empty.false (comparison.symm oneFibreMember)

def twoOccurrences : Formula 1 := .either (.equal 0 0) (.equal 0 0)
def receiptEnvironment : Environment.{u} 1 := fun _ => AccessiblePointedGraph.empty

def firstReceipt : realize twoOccurrences receiptEnvironment.{u} := .inl ⟨Equal.refl _⟩
def secondReceipt : realize twoOccurrences receiptEnvironment.{u} := .inr ⟨Equal.refl _⟩

def duplicateContextReceipts : GraphRealizedDeduction.Receipts
    [twoOccurrences, twoOccurrences] receiptEnvironment.{u} :=
  Fin.cases firstReceipt (Fin.cases secondReceipt (fun index => False.elim (Nat.not_lt_zero _ index.isLt)))

theorem duplicate_occurrences_differ :
    GraphRealizedDeduction.interpret
        (.hypothesis (assumptions := [twoOccurrences, twoOccurrences]) (0 : Fin 2))
        receiptEnvironment.{u} duplicateContextReceipts ≠
      GraphRealizedDeduction.interpret
        (.hypothesis (assumptions := [twoOccurrences, twoOccurrences]) (1 : Fin 2))
        receiptEnvironment duplicateContextReceipts := by
  exact Sum.inl_ne_inr

def erasedReceipt (value : realize twoOccurrences receiptEnvironment.{u}) :
    PLift (Nonempty (realize twoOccurrences receiptEnvironment.{u})) := ⟨⟨value⟩⟩

/-- Mere inhabitation erases the constructor/occurrence evidence, so it
cannot be inverted while preserving both actual receipts. -/
theorem erased_receipts_no_inverse :
    ¬ ∃ restore : PLift (Nonempty (realize twoOccurrences receiptEnvironment.{u})) →
        realize twoOccurrences receiptEnvironment.{u},
      restore (erasedReceipt firstReceipt) = firstReceipt ∧
      restore (erasedReceipt secondReceipt) = secondReceipt := by
  rintro ⟨restore, first, second⟩
  have erasedSame : erasedReceipt firstReceipt.{u} = erasedReceipt secondReceipt := Subsingleton.elim _ _
  have resultSame := first.symm.trans ((congrArg restore erasedSame).trans second)
  exact Sum.inl_ne_inr resultSame

theorem no_false_set_theory_derivation {count : Nat} {assumptions : List (Formula count)}
    (proof : GraphRealizedDeduction.Proof assumptions .bottom)
    (adopted : (index : Fin assumptions.length) → GraphRealizedSetTheory.Axiom assumptions[index.val]) : False :=
  PEmpty.elim (GraphRealizedSetTheory.derivationRealizer proof adopted
    (fun _ => AccessiblePointedGraph.empty.{0}))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedControls
