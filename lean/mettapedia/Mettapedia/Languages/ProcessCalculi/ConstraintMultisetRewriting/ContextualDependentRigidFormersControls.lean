import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceControls

/-!
# Heterogeneous decomposition of rigid formers on concrete stores

* **Π types with different domains.** Over `A X : U0`, `Π X A ≐ Π A A` decomposes into `X ≐ A` and the
  family twin `(λ_. A : Π X U0) ≐ (λ_. A : Π A U0)`; the pattern rule solves `X := A` at once, and the
  rigid-former solver commits with a principal answer. The Π and in-place solvers leave it suspended.
* **A clash among the pieces.** `Π (Π A A) A ≐ Π (Σ A A) A` decomposes into the domain equation
  `Π A A ≐ Σ A A`, a rigid clash: the store is refuted with a certificate.
* **Identity types with different carriers.** Over `A : U0, a : A, X : U0, x : X`,
  `Id A a a ≐ Id X x x` decomposes into `A ≐ X` and the heterogeneous `(a : A) ≐ (x : X)`, twice. No
  rule reads `X` while `x` depends on it, but the in-place rule solves `X := A` past `x`; the next
  rounds solve `x := a`. The rigid-former solver commits with a principal answer; the in-place solver
  alone leaves the store suspended.
* **A clash between endpoints.** `Id U (Π A A) (Π A A) ≐ Id U (Σ A A) (Σ A A)` decomposes into a rigid
  clash and is refuted with a certificate.
* **Pairs.** Over `A : U0, a : A, X : A`, `(a, a) ≐ (X, a)` decomposes into `a ≐ X` and the
  heterogeneous second components; the pattern rule solves `X := a`, and the solver commits with a
  principal answer. `(Π A A, Π A A) ≐ (Σ A A, Π A A)` decomposes into a rigid clash and is refuted.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidFormers.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDynamicFragment ContextualDependentDecisiveFragment
open ContextualDependentFragment ContextualDependentFragment.Controls

/-- The rigid-former solver of the tower controls, as a fuel-indexed family. -/
abbrev formersTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  formersFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The rigid-former solver at budget 16. -/
def formersOnly : Solver setting.levels := formersTower.solver 16

/-! ## Π types with different domains -/

theorem twistedPi_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.var 0) (.var 2))).isSome := by decide +kernel

/-- `(x : X) → A` over `A X : U0`. -/
def twistedType : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.pi (.var 0) (.var 2))).get twistedPi_formed).val

theorem twisted_level : twistedType.level = familyType.level := by decide +kernel

/-- `Π A A` and `Π X A` are lowered to `U0`, the universe the metavariables are declared at. -/
theorem lowered : setting.R.cumulative familyType.level (.sort Tower.zero) := by decide +kernel

/-- `Π X A` at `U0`. -/
def towardTwisted : Term twoTypes (universeAt twoTypes) :=
  ⟨twistedType.code, .cumul twistedType.formed (by rw [twisted_level]; exact lowered)⟩

/-- `Π A A` at `U0`. -/
def towardConstant : Term twoTypes (universeAt twoTypes) :=
  ⟨constantType.code, .cumul constantType.formed (by rw [function_levels]; exact lowered)⟩

/-- `Π X A ≐ Π A A` over `A X : U0`: the domains differ. -/
def domainsStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨universeAt twoTypes, towardTwisted⟩, ⟨universeAt twoTypes, towardConstant⟩)]

/-- **The rigid-former solver commits on it.** -/
theorem domains_solved : (run formersOnly domainsStore 3).readout = .commit := by decide +kernel

theorem domains_principal :
    ∃ state finished, run formersOnly domainsStore 3 = .solved state finished ∧
      (frames setting.levels).Principal domainsStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit domains_solved
  exact ⟨state, finished, solved, drive_solved_principal formersOnly solved⟩

/-- The Π solver, with one-domain decomposition, leaves it suspended. -/
theorem domains_pi_suspended : (run piOnly domainsStore 4).readout = .suspended := by decide +kernel

/-- The in-place solver leaves it suspended. -/
theorem domains_inPlace_suspended :
    (run ContextualDependentInPlace.Controls.inPlaceOnly domainsStore 4).readout = .suspended := by decide +kernel

theorem endo_formed' : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.pi (.var 1) (.var 2)) (.var 2))).isSome := by decide +kernel

theorem pairDomain_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.sigma (.var 1) (.var 2)) (.var 2))).isSome := by decide +kernel

/-- `(f : (x : A) → A) → A`. -/
def overFunctions : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.pi (.pi (.var 1) (.var 2)) (.var 2))).get
      endo_formed').val

/-- `(p : (x : A) × A) → A`. -/
def overPairs : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.pi (.sigma (.var 1) (.var 2)) (.var 2))).get
      pairDomain_formed).val

theorem clash_levels : overFunctions.level = overPairs.level := by decide +kernel

theorem overUniverse_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.head overFunctions.level)).isSome := by decide +kernel

/-- The universe of both. -/
def overUniverse : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.head overFunctions.level)).get overUniverse_formed).val

theorem overUniverse_code : overUniverse.code = .head overFunctions.level :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.head overFunctions.level)).get
      overUniverse_formed).property

/-- `Π (Π A A) A ≐ Π (Σ A A) A`: the domains clash. -/
def clashingDomainsStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨overUniverse, ⟨overFunctions.code, by rw [overUniverse_code]; exact overFunctions.formed⟩⟩,
    ⟨overUniverse, ⟨overPairs.code, by rw [overUniverse_code, clash_levels]; exact overPairs.formed⟩⟩)]

/-- **The rigid-former solver refutes it**, with a certificate. -/
theorem clashing_domains_refuted : (run formersOnly clashingDomainsStore 2).readout = .refuted := by decide +kernel

theorem clashing_domains_unsolvable : ¬ (frames setting.levels).Solvable clashingDomainsStore :=
  drive_refuted formersOnly 2 _ clashing_domains_refuted

/-- The Π solver leaves it suspended. -/
theorem clashing_domains_pi_suspended : (run piOnly clashingDomainsStore 4).readout = .suspended := by decide +kernel

/-! ## Identity types with different carriers -/

/-- `A : U0, a : A`. -/
abbrev withElement := extend ContextualDependentInversion.Controls.typeContext
  ContextualDependentInversion.Controls.parameterType

/-- `A : U0, a : A, X : U0`. -/
abbrev withCarrier := extend withElement (universeAt withElement)

/-- `x : X`. -/
def carrierElement : TypeOver withCarrier := ⟨.var 0, .sort Tower.zero, .sort _, .var 0⟩

/-- `A : U0, a : A, X : U0, x : X`. -/
abbrev carriers := extend withCarrier carrierElement

/-- `Id A a a`. -/
def identityOfA : Term carriers (universeAt carriers) :=
  ⟨(.id (.var 3) (.var 2) (.var 2) : Tower.Tm 4), .idForm (.var 3) (.sort _) (.var 2) (.var 2)⟩

/-- `Id X x x`. -/
def identityOfX : Term carriers (universeAt carriers) :=
  ⟨(.id (.var 1) (.var 0) (.var 0) : Tower.Tm 4), .idForm (.var 1) (.sort _) (.var 0) (.var 0)⟩

/-- `Id A a a ≐ Id X x x`: the carriers differ. -/
def carriersStore : EquationStore (TotalTerm carriers) :=
  [(⟨universeAt carriers, identityOfA⟩, ⟨universeAt carriers, identityOfX⟩)]

/-- **The rigid-former solver commits on it**: `X := A` in place past `x`, then `x := a`. -/
theorem carriers_solved : (run formersOnly carriersStore 4).readout = .commit := by decide +kernel

theorem carriers_principal :
    ∃ state finished, run formersOnly carriersStore 4 = .solved state finished ∧
      (frames setting.levels).Principal carriersStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit carriers_solved
  exact ⟨state, finished, solved, drive_solved_principal formersOnly solved⟩

/-- The in-place solver alone leaves it suspended. -/
theorem carriers_inPlace_suspended :
    (run ContextualDependentInPlace.Controls.inPlaceOnly carriersStore 4).readout = .suspended := by decide +kernel

/-! ## A clash between endpoints -/

theorem pairs_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.sigma (.var 1) (.var 2))).isSome := by decide +kernel

/-- `(x : A) × A`. -/
def pairsType : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.sigma (.var 1) (.var 2))).get pairs_formed).val

theorem pairs_level : pairsType.level = constantType.level := by decide +kernel

/-- The universe of `Π A A` and `Σ A A`, and the one above it. -/
def lowUniverse : Tm Tower.Head 2 := .head constantType.level

def highUniverse : TypeOver twoTypes :=
  ⟨.head (.sort (.succ (.max Tower.zero Tower.zero))), .sort (.succ (.succ (.max Tower.zero Tower.zero))), .sort _,
    .headType (.sort _)⟩

theorem low_level : constantType.level = .sort (.max Tower.zero Tower.zero) := by decide +kernel

/-- `Id U (Π A A) (Π A A)`. -/
def identityOfFunctions : Term twoTypes highUniverse :=
  ⟨.id lowUniverse constantType.code constantType.code,
    .idForm (by rw [lowUniverse, low_level]; exact .headType (.sort _)) (.sort _)
      (by rw [lowUniverse]; exact constantType.formed) (by rw [lowUniverse]; exact constantType.formed)⟩

/-- `Id U (Σ A A) (Σ A A)`. -/
def identityOfPairs : Term twoTypes highUniverse :=
  ⟨.id lowUniverse pairsType.code pairsType.code,
    .idForm (by rw [lowUniverse, low_level]; exact .headType (.sort _)) (.sort _)
      (by rw [lowUniverse, ← pairs_level]; exact pairsType.formed)
      (by rw [lowUniverse, ← pairs_level]; exact pairsType.formed)⟩

/-- `Id U (Π A A) (Π A A) ≐ Id U (Σ A A) (Σ A A)`. -/
def clashingEndpointsStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨highUniverse, identityOfFunctions⟩, ⟨highUniverse, identityOfPairs⟩)]

/-- **The rigid-former solver refutes it**, with a certificate. -/
theorem clashing_endpoints_refuted : (run formersOnly clashingEndpointsStore 2).readout = .refuted := by
  decide +kernel

theorem clashing_endpoints_unsolvable : ¬ (frames setting.levels).Solvable clashingEndpointsStore :=
  drive_refuted formersOnly 2 _ clashing_endpoints_refuted

/-- The Π solver, whose identity decomposition runs only the locals and pattern rules, leaves it
suspended. -/
theorem clashing_endpoints_pi_suspended : (run piOnly clashingEndpointsStore 4).readout = .suspended := by
  decide +kernel

/-! ## Pairs -/

/-- `A : U0, a : A, X : A`. -/
abbrev withPoint := extend withElement ⟨.var 1, .sort Tower.zero, .sort _, .var 1⟩

theorem pairAnnotation_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 withPoint
    (.sigma (.var 2) (.var 3))).isSome := by decide +kernel

/-- `(x : A) × A` over `A a X`. -/
def pairAnnotation : TypeOver withPoint :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withPoint (.sigma (.var 2) (.var 3))).get
      pairAnnotation_formed).val

/-- A pair checked by the executable checker. -/
def checkedPair (code : Tower.Tm 3)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 withPoint.raw code pairAnnotation.code).isSome = true) :
    Term withPoint pairAnnotation :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 withPoint.raw code pairAnnotation.code).get accepted).down withPoint.formed pairAnnotation.isType⟩

theorem pointPair_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withPoint.raw (.pair (.var 1) (.var 1))
    pairAnnotation.code).isSome = true := by decide +kernel

theorem metaPair_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withPoint.raw (.pair (.var 0) (.var 1))
    pairAnnotation.code).isSome = true := by decide +kernel

/-- `(a, a) ≐ (X, a)`. -/
def pairStore : EquationStore (TotalTerm withPoint) :=
  [(⟨pairAnnotation, checkedPair _ pointPair_checked⟩, ⟨pairAnnotation, checkedPair _ metaPair_checked⟩)]

/-- **The rigid-former solver commits on it**: the first components give `X := a`. -/
theorem pair_solved : (run formersOnly pairStore 3).readout = .commit := by decide +kernel

theorem pair_principal :
    ∃ state finished, run formersOnly pairStore 3 = .solved state finished ∧
      (frames setting.levels).Principal pairStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit pair_solved
  exact ⟨state, finished, solved, drive_solved_principal formersOnly solved⟩

/-- The in-place solver leaves it suspended. -/
theorem pair_inPlace_suspended :
    (run ContextualDependentInPlace.Controls.inPlaceOnly pairStore 4).readout = .suspended := by decide +kernel

theorem universePairs_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.sigma lowUniverse (.head constantType.level))).isSome := by decide +kernel

/-- `(X : U) × U` over `A X : U0`, with `U` the universe of `Π A A`. -/
def universePairs : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.sigma lowUniverse (.head constantType.level))).get
      universePairs_formed).val

theorem universePairs_code : universePairs.code = .sigma lowUniverse (.head constantType.level) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.sigma lowUniverse (.head constantType.level))).get
      universePairs_formed).property

/-- `(Π A A, Π A A)`. -/
def functionsPair : Term twoTypes universePairs :=
  ⟨.pair constantType.code constantType.code, by
    rw [universePairs_code]
    exact .pairIntro (by rw [← universePairs_code]; exact universePairs.formed) universePairs.universeWitness
      constantType.formed constantType.formed⟩

/-- `(Σ A A, Π A A)`. -/
def pairsPair : Term twoTypes universePairs :=
  ⟨.pair pairsType.code constantType.code, by
    rw [universePairs_code]
    exact .pairIntro (by rw [← universePairs_code]; exact universePairs.formed) universePairs.universeWitness
      (by rw [lowUniverse, ← pairs_level]; exact pairsType.formed) constantType.formed⟩

/-- `(Π A A, Π A A) ≐ (Σ A A, Π A A)`: the first components clash. -/
def clashingPairsStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨universePairs, functionsPair⟩, ⟨universePairs, pairsPair⟩)]

/-- **The rigid-former solver refutes it**, with a certificate. -/
theorem clashing_pairs_refuted : (run formersOnly clashingPairsStore 2).readout = .refuted := by decide +kernel

theorem clashing_pairs_unsolvable : ¬ (frames setting.levels).Solvable clashingPairsStore :=
  drive_refuted formersOnly 2 _ clashing_pairs_refuted

theorem clashing_pairs_pi_suspended : (run piOnly clashingPairsStore 4).readout = .suspended := by decide +kernel

end ContextualDependentRigidFormers.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
