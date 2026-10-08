import Mettapedia.SetTheory.Profiles.CommonCore
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedTheory

/-!
# The common material laws in the varying constructive graph model

Each independent core adoption is mapped to the actual constructed law
realizer. The same carrier also validates the separately declared Collection
extensions. This does not make those laws consequences of the weaker core.

Existence carries a current witness, while implication and universality
retain every future context arrow. The growing excluded-middle countermodel
and a literal cyclic set exclude classical logic and Foundation from this
intuitionistic theory's consequence closure. Graph anti-foundation remains
the model's separate bounded-diagram decoration result.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreConstructive

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula)
open ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization (Environment realize extend)
open CommonCore

universe u
variable {D : Type u} [Category.{u} D]

def toConstructive {count : Nat} {body : Formula count} (adopted : Axiom body) :
    ContextualGraphRealizedTheory.Axiom body :=
  match count, body, adopted with
  | _, _, .empty => .empty
  | _, _, .pairing => .pairing
  | _, _, .union => .union
  | _, _, .infinity => .infinity
  | _, _, .extensionality => .extensionality
  | _, _, .boundedSeparation bounded => .boundedSeparation bounded
  | _, _, .substitution indices previous => .substitution indices (toConstructive previous)

def extensionToConstructive {count : Nat} {body : Formula count} (adopted : Extension body) :
    ContextualGraphRealizedTheory.Axiom body :=
  match count, body, adopted with
  | _, _, .core previous => toConstructive previous
  | _, _, .strongCollection formula => .strongCollection formula
  | _, _, .subsetCollection formula => .subsetCollection formula
  | _, _, .substitution indices previous =>
      .substitution indices (extensionToConstructive previous)

def validate {count : Nat} {body : Formula count} (adopted : Axiom body)
    (point : D) (environment : Environment D count point) : realize D body point environment :=
  ContextualGraphRealizedTheory.validate (toConstructive adopted) point environment

def validateExtension {count : Nat} {body : Formula count} (adopted : Extension body)
    (point : D) (environment : Environment D count point) : realize D body point environment :=
  ContextualGraphRealizedTheory.validate (extensionToConstructive adopted) point environment

/-- Interpretation of the independently authored logical proof, preserving
the separately indexed assumption receipts. -/
def interpret {count : Nat} {conclusion : Formula count} (derivation : Derivation conclusion)
    (point : D) (environment : Environment D count point) :
    realize D conclusion point environment :=
  ContextualGraphRealizedDeduction.interpret derivation.proof point environment
    (fun index => validate (derivation.adopted index) point environment)

def interpretExtension {count : Nat} {conclusion : Formula count}
    (derivation : ExtensionDerivation conclusion) (point : D)
    (environment : Environment D count point) : realize D conclusion point environment :=
  ContextualGraphRealizedDeduction.interpret derivation.proof point environment
    (fun index => validateExtension (derivation.adopted index) point environment)

theorem validation_substitution {count other : Nat} {body : Formula count}
    (indices : Fin count → Fin other) (adopted : Axiom body)
    (point : D) (environment : Environment D other point) :
    Nonempty (realize D (ContextualMaterialLogic.substitute indices body) point environment) :=
  ⟨validate (.substitution indices adopted) point environment⟩

def containment (point : D) (environment : Environment D 0 point) :
    realize D containmentTheorem point environment := interpret containmentDerivation point environment

theorem excluded_middle_not_adopted :
    ¬ Nonempty (Axiom ContextualGraphRealizedDeductionControls.excludedMiddle) := by
  rintro ⟨adopted⟩
  exact ContextualGraphRealizedTheory.excluded_middle_not_adopted ⟨toConstructive adopted⟩

theorem excluded_middle_not_derived :
    ¬ Nonempty (Derivation ContextualGraphRealizedDeductionControls.excludedMiddle) := by
  rintro ⟨derivation⟩
  exact ContextualGraphRealizedDeductionControls.excluded_middle_empty
    ⟨interpret derivation 0 (ContextualGraphRealizedDeductionControls.environment 1 0)⟩

def emptyEnvironment (point : D) : Environment D 0 point :=
  fun index => False.elim (Nat.not_lt_zero _ index.isLt)

/-- The cyclic singleton refutes the ordinary regularity sentence. -/
theorem foundation_has_no_realizer :
    ¬ Nonempty (realize Nat foundationAxiom 0 (emptyEnvironment 0)) := by
  rintro ⟨foundation⟩
  let quine : Value Nat 0 := ContextualGraphRealizedTheory.loopValue 0
  let parentEnvironment := extend Nat quine (emptyEnvironment 0)
  let implication := ContextualGraphRealizedDeduction.applyUniversal 0
    (emptyEnvironment 0) foundation quine
  have witness := ContextualGraphRealizedDeduction.applyImplication 0 parentEnvironment
    implication ⟨quine, ⟨ContextualGraphRealizedTheory.loopMember 0⟩⟩
  obtain ⟨candidate, member, minimal⟩ := witness
  have childSame : childValue Nat quine member.down.1 = quine := by
    cases member.down.1.val
    rfl
  have equalQuine : Equal candidate quine :=
    (congrArg (Equal candidate) childSame) ▸ member.down.2
  have quineInWitness : Member quine candidate :=
    Member.transportParent equalQuine.symm (ContextualGraphRealizedTheory.loopMember 0)
  let candidateEnvironment := extend Nat candidate parentEnvironment
  let disjoint := ContextualGraphRealizedDeduction.applyUniversal 0
    candidateEnvironment minimal quine
  let comparisonEnvironment := extend Nat quine candidateEnvironment
  let response := ContextualGraphRealizedDeduction.applyImplication 0
    comparisonEnvironment disjoint ⟨quineInWitness⟩
  exact PEmpty.elim (ContextualGraphRealizedDeduction.applyImplication 0
    comparisonEnvironment response ⟨ContextualGraphRealizedTheory.loopMember 0⟩)

theorem foundation_not_adopted : ¬ Nonempty (Axiom foundationAxiom) := by
  rintro ⟨adopted⟩
  exact foundation_has_no_realizer ⟨validate adopted 0 (emptyEnvironment 0)⟩

theorem foundation_not_derived : ¬ Nonempty (Derivation foundationAxiom) := by
  rintro ⟨derivation⟩
  exact foundation_has_no_realizer ⟨interpret derivation 0 (emptyEnvironment 0)⟩

theorem foundation_not_derived_from_collection_extension :
    ¬ Nonempty (ExtensionDerivation foundationAxiom) := by
  rintro ⟨derivation⟩
  exact foundation_has_no_realizer ⟨interpretExtension derivation 0 (emptyEnvironment 0)⟩

theorem excluded_middle_not_derived_from_collection_extension :
    ¬ Nonempty (ExtensionDerivation ContextualGraphRealizedDeductionControls.excludedMiddle) := by
  rintro ⟨derivation⟩
  exact ContextualGraphRealizedDeductionControls.excluded_middle_empty
    ⟨interpretExtension derivation 0 (ContextualGraphRealizedDeductionControls.environment 1 0)⟩

end Mettapedia.SetTheory.Profiles.CommonCoreConstructive
