import Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContextsElimination
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.BoundedNaturalModel

/-!
# A proof-variable and full dependent pair model over arbitrary theories

Duplicate assumptions occupy different binding positions and recover their
actual different witnesses. The pair eliminator's motive depends on both
coordinates: at object a and proof u it has type Fin (a + u.val + 1).
This marks the boundary of an object-only motive or an erased assumption
interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.AssumptionContextsModel

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open AssumptionContexts AssumptionContexts.Interpretation

variable (C : Type) [categoryC : Category.{0} C]
abbrev objects := BoundedNaturalModel.objects C
abbrev constants := BoundedNaturalModel.constants C
abbrev predicates := BoundedNaturalModel.predicates C
noncomputable abbrev declarations : ∀ {n : Nat} {formula : Formula Nat PUnit.{1} n},
    BoundedNaturalModel.Primitive n formula →
      (PresheafInterpretation.family (objects C) (constants C) (predicates C) formula).sections :=
  @BoundedNaturalModel.declarations C _
abbrev input : Formula Nat PUnit.{1} 1 := BoundedNaturalModel.input
abbrev Declaration := BoundedNaturalModel.Primitive

abbrev objectScope : Scope Nat PUnit.{1} 1 := .objects 1
abbrev duplicateScope : Scope Nat PUnit.{1} 1 := .proof (.proof objectScope input) input
abbrev newestProof : Hypothesis duplicateScope input := .here (.proof objectScope input) input
abbrev olderProof : Hypothesis duplicateScope input := .proofThere (.here objectScope input) input

theorem distinct_assumption_positions : newestProof ≠ olderProof :=
  Hypothesis.duplicate_positions_differ objectScope input

noncomputable def duplicatePoint (world : Cᵒᵖ) (n : Nat) (earlier later : Fin (n + 1)) :
    (context (objects C) (constants C) (predicates C) duplicateScope).Elements :=
  ⟨world, ⟨⟨⟨PUnit.unit, n⟩, earlier⟩, later⟩⟩

theorem newest_witness (world : Cᵒᵖ) (n : Nat) (earlier later : Fin (n + 1)) :
    (hypothesis (objects C) (constants C) (predicates C) newestProof).val ((duplicatePoint C world) n earlier later) = later := rfl

theorem older_witness (world : Cᵒᵖ) (n : Nat) (earlier later : Fin (n + 1)) :
    (hypothesis (objects C) (constants C) (predicates C) olderProof).val ((duplicatePoint C world) n earlier later) = earlier := rfl

theorem duplicate_meanings_differ (world : Cᵒᵖ) :
    hypothesis (objects C) (constants C) (predicates C) newestProof ≠ hypothesis (objects C) (constants C) (predicates C) olderProof := by
  intro same
  have values := congrArg (fun s => (s.val ((duplicatePoint C world) 1 0 1)).val) same
  exact Nat.one_ne_zero values

abbrev emptyScope : Scope Nat PUnit.{1} 0 := .objects 0
abbrev pairScope := emptyScope.pair input
abbrev sumScope := emptyScope.sum input

/-- The code observes both the object and the actual proof's finite value. -/
noncomputable def pairCode : context (objects C) (constants C) (predicates C) sumScope ⟶ (objects C) where
  app _ := TypeCat.ofHom fun point => by
    let a : Nat := point.2.1
    let witness : Fin (a + 1) := point.2.2
    exact a + witness.val
  naturality X Y arrow := by
    ext point
    rfl

noncomputable def fullMotive : DisplayedFamily (context (objects C) (constants C) (predicates C) sumScope) :=
  reindexDisplayed (pairCode C) (BoundedNaturalModel.bounded C)

inductive Motive : {n : Nat} → Scope Nat PUnit.{1} n → Type where
  | answer : Motive sumScope

noncomputable def motives : ∀ {n : Nat} {scope : Scope Nat PUnit.{1} n},
    Motive scope → DisplayedFamily (context (objects C) (constants C) (predicates C) scope)
  | _, _, .answer => (fullMotive C)

abbrev answer : Family Declaration Motive sumScope := .atom .answer
abbrev branchFamily : Family Declaration Motive pairScope := .reindex answer (.pack emptyScope input)

inductive Primitive : {n : Nat} → (scope : Scope Nat PUnit.{1} n) → Family Declaration Motive scope → Type where
  | branch : Primitive pairScope branchFamily

private theorem maximal_cast {a b : Nat} (same : a = b) :
    cast (congrArg (fun number : Nat => Fin (number + 1)) same)
        (⟨a, Nat.lt_succ_self a⟩ : Fin (a + 1)) = (⟨b, Nat.lt_succ_self b⟩ : Fin (b + 1)) := by
  cases same
  rfl

def boundedSection : (BoundedNaturalModel.bounded C).sections where
  val point := ⟨point.2, Nat.lt_succ_self _⟩
  property arrow := maximal_cast arrow.property

noncomputable def branchSection :
    (family (objects C) (constants C) (predicates C) (declarations C) (motives C) branchFamily).sections :=
  reindexDisplayedSection ((pairIso (objects C) (constants C) (predicates C) emptyScope input).inv ≫ (pairCode C))
    (BoundedNaturalModel.bounded C) (boundedSection C)

noncomputable def primitives : ∀ {n : Nat} {scope : Scope Nat PUnit.{1} n}
    {body : Family Declaration Motive scope}, Primitive scope body →
      (family (objects C) (constants C) (predicates C) (declarations C) (motives C) body).sections
  | _, _, _, .branch => (branchSection C)

abbrev branch : Term Declaration Motive Primitive 1 pairScope branchFamily := .primitive .branch
abbrev eliminated : Term Declaration Motive Primitive 0 sumScope answer :=
  .sigmaElim emptyScope input answer branch

abbrev newestTerm : Term Declaration Motive Primitive 1 duplicateScope (.legacy duplicateScope input) :=
  .evidence (.hypothesis newestProof)

abbrev olderTerm : Term Declaration Motive Primitive 1 duplicateScope (.legacy duplicateScope input) :=
  .evidence (.hypothesis olderProof)

include categoryC in
/-- A generated equation cannot erase the two different assumption uses. -/
theorem no_assumption_erasure (world : Cᵒᵖ) : ¬ TermEquation newestTerm olderTerm := by
  intro equation
  have same := equation_sound (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) equation
  change hypothesis (objects C) (constants C) (predicates C) newestProof =
    hypothesis (objects C) (constants C) (predicates C) olderProof at same
  exact duplicate_meanings_differ C world same

abbrev ambientBranch : ScopedEvidence Declaration (.object duplicateScope)
    (.substitute input ObjectSubstitution.weaken) := .hypothesis (.objectThere newestProof)

abbrev ambientFunction : ScopedEvidence Declaration duplicateScope
    (.pi (.substitute input ObjectSubstitution.weaken)) := .lam ambientBranch

abbrev ambientCall (argument : Nat) : ScopedEvidence Declaration duplicateScope
    (.substitute (.substitute input ObjectSubstitution.weaken)
      (ObjectSubstitution.instantiate (.constant argument))) := .app ambientFunction (.constant argument)

/-- Dependent function introduction uses a genuine ambient proof variable,
and its application computes through the native Pi comparison and beta. -/
theorem ambient_function_beta (argument : Nat) :
    evidence (objects C) (constants C) (predicates C) (declarations C) (ambientCall argument) =
      evidence (objects C) (constants C) (predicates C) (declarations C)
        (.instantiate ambientBranch (.constant argument)) :=
  evidence_equation_sound (objects C) (constants C) (predicates C) (declarations C)
    (.beta ambientBranch (.constant argument))

theorem ambient_function_computes (world : Cᵒᵖ) (n argument : Nat)
    (earlier later : Fin (n + 1)) :
    ((evidence (objects C) (constants C) (predicates C) (declarations C)
      (ambientCall argument)).val (duplicatePoint C world n earlier later)).val = later.val := by
  rw [ambient_function_beta]
  rfl

noncomputable def pairPoint (world : Cᵒᵖ) (a : Nat) (witness : Fin (a + 1)) :
    (context (objects C) (constants C) (predicates C) pairScope).Elements :=
  ⟨world, ⟨⟨PUnit.unit, a⟩, witness⟩⟩

noncomputable def sumPoint (world : Cᵒᵖ) (a : Nat) (witness : Fin (a + 1)) :
    (context (objects C) (constants C) (predicates C) sumScope).Elements :=
  ⟨world, ⟨PUnit.unit, ⟨a, witness⟩⟩⟩

theorem full_motive_type (world : Cᵒᵖ) (a : Nat) (witness : Fin (a + 1)) :
    (fullMotive C).obj ((sumPoint C world) a witness) = Fin (a + witness.val + 1) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem branch_computes (world : Cᵒᵖ) (a : Nat) (witness : Fin (a + 1)) :
    ((term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) branch).val ((pairPoint C world) a witness)).val =
      a + witness.val := by
  change ((boundedSection C).val ⟨world, (pairCode C).app world
    ((pairIso (objects C) (constants C) (predicates C) emptyScope input).inv.app world ((pairPoint C world) a witness).2)⟩).val = _
  exact congrArg (fun value : (context (objects C) (constants C) (predicates C) sumScope).obj world =>
    ((boundedSection C).val ⟨world, (pairCode C).app world value⟩).val)
      (pack_value (objects C) (constants C) (predicates C) emptyScope input ((pairPoint C world) a witness))

theorem branch_recovered :
    term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) (.reindex eliminated (.pack emptyScope input)) =
      term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) branch :=
  beta (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) emptyScope input answer branch

theorem eliminated_computes (world : Cᵒᵖ) (a : Nat) (witness : Fin (a + 1)) :
    ((term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) eliminated).val ((sumPoint C world) a witness)).val =
      a + witness.val := by
  have computation := congrArg (fun s => (s.val ((pairPoint C world) a witness)).val) (branch_recovered C)
  change ((term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) eliminated).val
    ⟨world, (pairIso (objects C) (constants C) (predicates C) emptyScope input).inv.app world ((pairPoint C world) a witness).2⟩).val =
      ((term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) branch).val ((pairPoint C world) a witness)).val at computation
  have packed := congrArg (fun value : (context (objects C) (constants C) (predicates C) sumScope).obj world =>
    ((term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) eliminated).val ⟨world, value⟩).val)
      (pack_value (objects C) (constants C) (predicates C) emptyScope input ((pairPoint C world) a witness))
  exact packed.symm.trans (computation.trans ((branch_computes C world) a witness))

theorem pair_eta :
    term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C)
      (.sigmaElim emptyScope input answer (.reindex eliminated (.pack emptyScope input))) =
      term (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) eliminated :=
  eta (objects C) (constants C) (predicates C) (declarations C) (motives C) (primitives C) emptyScope input answer eliminated

end Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.AssumptionContextsModel
