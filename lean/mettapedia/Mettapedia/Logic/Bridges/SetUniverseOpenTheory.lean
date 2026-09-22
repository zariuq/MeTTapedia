import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation
import Mettapedia.Logic.HOL.TypeSubstitutionDerivation
import Mettapedia.Languages.OpenTheory.EtaCompletenessHeyting
import Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT

/-!
# Interpreting the set/universe HOL kernel in OpenTheory with eta

The existing set/universe signature has seven mathematical constants. We
interpret its set sort as an atomic OpenTheory type and its constants as
distinct undefined constants. Logical inference stays at `HOL.ExtDerivation`
on the source side and at `PolicyPrimitiveRule etaAxiomPolicy` on the target
side. Source assumptions become target hypotheses; none becomes an axiom of
the eta-only policy.

This is a kernel-preserving translation of the existing HOTG-adjacent HOL
presentation, not validity of a full HOTG preamble. In particular the eleven
formulas of `universeTheory` remain explicit assumptions. Their existing set
model requires `CofinalInaccessibles` for the universe operation. No such
model assumption is needed to translate a derivation.

The resulting theorems are observed in their native OpenTheory reachable
states by the existing WM reading. WM reduction preserves that observation;
it is not another type theory or an identification of kernel carriers.
The Prime DTT-to-set/universe kernel translation remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.SetUniverseOpenTheory

open Mettapedia.Logic
open Mettapedia.Languages.OpenTheory
open ReverseTranslation

open Mettapedia.Languages
open HOL.Embedding
abbrev SetSymbol : HOL.Ty Unit → Type :=
  _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation.UniverseSymbol

/-- The set sort is an atomic type, not the proposition sort. -/
def setAtom : AtomicTy := ⟨.var ⟨["SetUniverse"], "set"⟩, rfl, rfl⟩

def baseMap (_ : Unit) : HOL.Ty AtomicTy := .base setAtom

/-- Names retain the mathematical operations as distinct symbols. -/
def symbolName : {A : HOL.Ty Unit} → SetSymbol A → String
  | _, .core .member => "member"
  | _, .core .empty => "empty"
  | _, .core .union => "union"
  | _, .core .power => "power"
  | _, .core .separate => "separate"
  | _, .core .replace => "replace"
  | _, .universe => "universe"

def symbolMap {A : HOL.Ty Unit} (symbol : SetSymbol A) :
    OpenTheory.Symbol (HOL.Ty.substitute baseMap A) :=
  .constant (.mk ⟨["SetUniverse"], symbolName symbol⟩ .undefined)
    (reverseTy (HOL.Ty.substitute baseMap A)) (toHOL_reverseTy _)

/-- Intrinsically typed translation before encoding the logical connectives. -/
def translate {Γ : HOL.Ctx Unit} {A : HOL.Ty Unit}
    (term : HOL.Term SetSymbol Γ A) :
    HOL.Term OpenTheory.Symbol (Γ.map (HOL.Ty.substitute baseMap))
      (HOL.Ty.substitute baseMap A) :=
  HOL.mapTypes baseMap symbolMap term

def formula (φ : HOL.ClosedFormula SetSymbol) : CanonicalTerm :=
  reverseCanonical Naming.empty (translate φ)

def hypotheses (Δ : List (HOL.ClosedFormula SetSymbol)) :
    Finset CanonicalTerm :=
  reverseHypotheses Naming.empty (Δ.map translate)

/-- Every source kernel rule is respected, including binders, beta and eta. -/
theorem translate_derivation {Γ : HOL.Ctx Unit}
    {Δ : List (HOL.Formula SetSymbol Γ)}
    {φ : HOL.Formula SetSymbol Γ}
    (proof : HOL.ExtDerivation SetSymbol Δ φ) :
    HOL.ExtDerivation OpenTheory.Symbol (Δ.map translate) (translate φ) :=
  proof.mapTypes baseMap symbolMap

/-- Proof transport into the primitive kernel, with all source assumptions
retained as hypotheses. -/
theorem kernel_translation
    {Δ : List (HOL.ClosedFormula SetSymbol)}
    {φ : HOL.ClosedFormula SetSymbol}
    (proof : HOL.ExtDerivation SetSymbol Δ φ) :
    KernelProvable etaAxiomPolicy (hypotheses Δ) (formula φ).term :=
  EtaCompleteness.kernelProvable_reverse_of_extDerivation rfl
    (translate_derivation proof) Naming.empty

/-- The source theory is passed as hypotheses, not silently admitted into
OpenTheory's axiom policy. -/
theorem universeTheory_translation {φ : HOL.ClosedFormula SetSymbol}
    (proof : HOL.ExtDerivation SetSymbol ZFSetUniverseInterpretation.universeTheory φ) :
    KernelProvable etaAxiomPolicy (hypotheses ZFSetUniverseInterpretation.universeTheory) (formula φ).term :=
  kernel_translation proof

theorem formula_isBool (φ : HOL.ClosedFormula SetSymbol) :
    (formula φ).IsBool := reverseCanonical_isBool Naming.empty (translate φ)

/-- A positive control using higher-order function extensionality. -/
def setFunctionEta : HOL.ClosedFormula SetSymbol :=
  .all (.eq (.lam (.app (.var (.vs .vz)) (.var .vz))) (.var .vz))

theorem setFunctionEta_proof :
    HOL.ExtDerivation SetSymbol [] setFunctionEta :=
  .allI (.eta (.var (HOL.Var.vz (Γ := []) (τ := ZFSetHenkinInterpretation.mapping))))

theorem setFunctionEta_kernel :
    KernelProvable etaAxiomPolicy ∅ (formula setFunctionEta).term :=
  kernel_translation setFunctionEta_proof

/-- A typed target term outside the image of the formula interpretation. -/
def setVariable : CanonicalTerm :=
  ⟨.free ⟨⟨["SetUniverse"], "x"⟩, setAtom.1⟩, setAtom.1, by simp only [DBTerm.inferType]⟩

theorem formula_ne_setVariable (φ : HOL.ClosedFormula SetSymbol) :
    formula φ ≠ setVariable := by
  intro same
  have boolean := formula_isBool φ
  rw [same] at boolean
  change Ty.var _ = Ty.bool at boolean
  cases boolean

/-- The interpretation is not an identification of the two carriers. -/
theorem formula_not_surjective : ¬ Function.Surjective formula := by
  intro onto
  obtain ⟨φ, same⟩ := onto setVariable
  exact formula_ne_setVariable φ same

/-- Nonconstant control: two different set operations remain distinct. -/
theorem union_ne_power :
    translate (.const (.core .union) : HOL.ClosedTerm SetSymbol ZFSetHenkinInterpretation.mapping) ≠
      translate (.const (.core .power) : HOL.ClosedTerm SetSymbol ZFSetHenkinInterpretation.mapping) := by
  intro same
  cases same

/-- Actual primitive-kernel reachability, followed by a membership query in
the independent observation machine. -/
theorem reachable_observation
    {Δ : List (HOL.ClosedFormula SetSymbol)}
    {φ : HOL.ClosedFormula SetSymbol}
    (proof : HOL.ExtDerivation SetSymbol Δ φ) :
    ∃ (state : List OpenTheory.Theorem) (out : OpenTheory.Theorem),
      (OpenTheory.OperationalGSLT.openTheoryGSLT etaAxiomPolicy).MultiStep [] state ∧
      out.sequent = ⟨hypotheses Δ, formula φ⟩ ∧
      Nonempty (WorldModelQueryGSLT.scanGSLT.RewritePath (.scan state out) (.answer true)) := by
  obtain ⟨out, derived, sequent⟩ :=
    (kernelProvable_iff_derives_sequent (formula φ)).mp (kernel_translation proof)
  obtain ⟨state, reachable, answered⟩ :=
    WorldModelQueryGSLT.reachable_true_answer_of_derives etaAxiomPolicy derived
  exact ⟨state, out, reachable, sequent, answered⟩

end Mettapedia.Logic.Bridges.SetUniverseOpenTheory
