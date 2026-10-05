import Mettapedia.Languages.VibeITP.Presentation.InferenceEquality
import Mettapedia.Languages.VibeITP.Presentation.InferenceFormation
import Mettapedia.Languages.VibeITP.Spec.Derivation

/-!
# Exact checking of supplied static inference operands

Modus ponens is authorized only by its particular implication and premise.
Instantiation checks the actual value's formation and the independent kernel
operation. A conclusion's unrelated derivability cannot validate an invalid
submitted inference. These are operation checks, not the complete recursive
proof checker or theory-admission machine.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInference

open ComputationalData ComputationalShift ComputationalSubstitution ComputationalInstantiation
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => inferenceProgram
local notation "A" => inferenceEquations
local notation "H" => computationalHost

/-- The term-level result of the independent protocol's modus-ponens branch;
storage/phase checks are outside this operand-level computation. -/
private def mpResult (implication premise : Spec.Term) : Option Spec.Term :=
  match implication with
  | .app (.builtin .impl) [antecedent, conclusion] =>
      if antecedent = premise then some conclusion else none
  | _ => none

private theorem mp_matches (implication premise conclusion : Spec.Term) :
    mpResult implication premise = some conclusion ↔ implication = Spec.Term.impl premise conclusion := by
  cases implication with
  | bvar _ => simp [mpResult, Spec.Term.impl]
  | lit _ => simp [mpResult, Spec.Term.impl]
  | app symbol arguments =>
      cases symbol with
      | fresh _ => simp [mpResult, Spec.Term.impl]
      | builtin builtin =>
          cases builtin <;> try simp [mpResult, Spec.Term.impl]
          cases arguments with
          | nil => simp
          | cons antecedent rest =>
              cases rest with
              | nil => simp
              | cons actual rest =>
                  cases rest with
                  | nil => by_cases same : antecedent = premise <;> simp [same]
                  | cons _ _ => simp

private theorem mp_equal (same : Bool) (conclusion : Spec.Term) :
    Applies P H "vibe:mp-equal" [boolean same, encode conclusion]
      (encodeResult (if same then some conclusion else none)) := by
  cases same with
  | false => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine inference_equation (equation := A[33])
        (environment := [("conclusion", encode conclusion)]) (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
        (reuse_instantiation_call (by decide +kernel) (.constructor (by rfl) (by rfl)))

private theorem mp_implication_computes (antecedent premise conclusion : Spec.Term) :
    Applies P H "vibe:modus-ponens" [encode (Spec.Term.impl antecedent conclusion), encode premise]
      (encodeResult (if antecedent = premise then some conclusion else none)) := by
  refine inference_equation (equation := A[30])
    (environment := [("antecedent", encode antecedent), ("conclusion", encode conclusion),
      ("premise", encode premise)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (decide (antecedent = premise)), encode conclusion]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (term_equality_computes _ _)
  · by_cases same : antecedent = premise
    · simpa only [same, decide_true, ↓reduceIte] using mp_equal (decide (antecedent = premise)) conclusion
    · simpa only [same, decide_false, Bool.false_eq_true, ↓reduceIte] using mp_equal (decide (antecedent = premise)) conclusion

theorem modusPonens_computes (implication premise : Spec.Term) :
    Applies P H "vibe:modus-ponens" [encode implication, encode premise]
      (encodeResult (match implication with
        | .app (.builtin .impl) [antecedent, conclusion] =>
            if antecedent = premise then some conclusion else none
        | _ => none)) := by
  cases implication with
  | bvar _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | lit _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | app symbol arguments =>
      cases symbol with
      | fresh _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
      | builtin builtin =>
          cases builtin <;> try exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
          cases arguments with
          | nil => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
          | cons antecedent rest =>
              cases rest with
              | nil => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
              | cons conclusion rest =>
                  cases rest with
                  | nil => exact mp_implication_computes antecedent premise conclusion
                  | cons _ _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩

theorem modusPonens_accepts_iff (implication premise conclusion : Spec.Term) :
    Applies P H "vibe:modus-ponens" [encode implication, encode premise] (encodeResult (some conclusion)) ↔
      implication = Spec.Term.impl premise conclusion := by
  constructor
  · intro computed
    have result := encodeResult_injective (computed.deterministic (modusPonens_computes implication premise))
    apply (mp_matches implication premise conclusion).mp
    exact result.symm
  · intro matched
    subst implication
    simpa [Spec.Term.impl] using modusPonens_computes (Spec.Term.impl premise conclusion) premise

private theorem check_result_computes (actual : Option Spec.Term) (claimed : Spec.Term) :
    Applies P H "vibe:check-result" [encodeResult actual, encode claimed]
      (boolean (decide (actual = some claimed))) := by
  cases actual with
  | none => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | some actual =>
      simp only [Option.some.injEq]
      refine inference_equation (equation := A[35])
        (environment := [("actual", encode actual), ("claimed", encode claimed)]) (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (term_equality_computes _ _)

theorem checkModusPonens_computes (implication premise claimed : Spec.Term) :
    Applies P H "vibe:check-mp" [encode implication, encode premise, encode claimed]
      (boolean (decide (implication = Spec.Term.impl premise claimed))) := by
  refine inference_equation (equation := A[36])
    (environment := [("implication", encode implication), ("premise", encode premise),
      ("claimed", encode claimed)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeResult (mpResult implication premise), encode claimed]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (modusPonens_computes implication premise)
  · simpa only [mp_matches] using check_result_computes (mpResult implication premise) claimed

theorem checkModusPonens_result_exact (implication premise claimed : Spec.Term) (result : Term) :
    Applies P H "vibe:check-mp" [encode implication, encode premise, encode claimed] result ↔
      result = boolean (decide (implication = Spec.Term.impl premise claimed)) := by
  constructor
  · intro checked
    exact checked.deterministic (checkModusPonens_computes implication premise claimed)
  · intro same
    subst result
    exact checkModusPonens_computes implication premise claimed

theorem checkModusPonens_accepts_iff (implication premise claimed : Spec.Term) :
    Applies P H "vibe:check-mp" [encode implication, encode premise, encode claimed] (.sym "True") ↔
      implication = Spec.Term.impl premise claimed := by
  rw [checkModusPonens_result_exact]
  by_cases same : implication = Spec.Term.impl premise claimed <;> simp [same, boolean]

theorem checkModusPonens_refuses_iff (implication premise claimed : Spec.Term) :
    Applies P H "vibe:check-mp" [encode implication, encode premise, encode claimed] (.sym "False") ↔
      implication ≠ Spec.Term.impl premise claimed := by
  rw [checkModusPonens_result_exact]
  by_cases same : implication = Spec.Term.impl premise claimed <;> simp [same, boolean]

theorem checkModusPonens_completed_exact (implication premise claimed : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:check-mp" [encode implication, encode premise, encode claimed] ≠ .exhausted) :
    apply P H fuel "vibe:check-mp" [encode implication, encode premise, encode claimed] =
      .value (boolean (decide (implication = Spec.Term.impl premise claimed))) :=
  (checkModusPonens_computes implication premise claimed).completed fuel finished

theorem checkModusPonens_derived (theory : Spec.Theory) (implication premise claimed : Spec.Term)
    (implicationDerived : Spec.Derives theory implication) (premiseDerived : Spec.Derives theory premise)
    (accepted : Applies P H "vibe:check-mp" [encode implication, encode premise, encode claimed] (.sym "True")) :
    Spec.Derives theory claimed := by
  have same := (checkModusPonens_accepts_iff implication premise claimed).mp accepted
  subst implication
  exact .modusPonens implicationDerived premiseDerived

private theorem thm_inst_formed (formed : Bool) (table : SignatureTable) (symbol : Spec.SymId)
    (value statement : Spec.Term) :
    Applies P H "vibe:thm-inst-formed" [boolean formed, encodeTable table, encodeSymbol symbol,
      encode value, encode statement]
      (encodeResult (if formed then Spec.instantiateStatement (signatureOf table) symbol value statement else none)) := by
  cases formed with
  | false => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine inference_equation (equation := A[39])
        (environment := [("table", encodeTable table), ("F", encodeSymbol symbol),
          ("value", encode value), ("statement", encode statement)]) (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (reuse_instantiation_call (by decide +kernel) (instantiation_computes table symbol value statement))

theorem theoremInstantiation_computes (table : SignatureTable) (symbol : Spec.SymId) (value statement : Spec.Term) :
    Applies P H "vibe:thm-instantiate" [encodeTable table, encodeSymbol symbol, encode value, encode statement]
      (encodeResult (if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none)) := by
  refine inference_equation (equation := A[37])
    (environment := [("table", encodeTable table), ("F", encodeSymbol symbol),
      ("value", encode value), ("statement", encode statement)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
    (thm_inst_formed _ table symbol value statement)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (wellFormed_computes table value)

theorem theoremInstantiation_accepts_iff (table : SignatureTable) (symbol : Spec.SymId)
    (value statement claimed : Spec.Term) :
    Applies P H "vibe:thm-instantiate" [encodeTable table, encodeSymbol symbol, encode value, encode statement]
      (encodeResult (some claimed)) ↔
      Spec.WellFormed (signatureOf table) value = true ∧
        Spec.instantiateStatement (signatureOf table) symbol value statement = some claimed := by
  have exactResult : Applies P H "vibe:thm-instantiate"
      [encodeTable table, encodeSymbol symbol, encode value, encode statement] (encodeResult (some claimed)) ↔
      (if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none) = some claimed := by
    constructor
    · intro computed
      exact (encodeResult_injective (computed.deterministic (theoremInstantiation_computes table symbol value statement))).symm
    · intro same
      simpa only [same] using theoremInstantiation_computes table symbol value statement
  rw [exactResult]
  cases Spec.WellFormed (signatureOf table) value <;> simp

theorem checkInstantiation_computes (table : SignatureTable) (symbol : Spec.SymId) (value statement claimed : Spec.Term) :
    Applies P H "vibe:check-inst" [encodeTable table, encodeSymbol symbol, encode value, encode statement, encode claimed]
      (boolean (decide ((if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none) = some claimed))) := by
  refine inference_equation (equation := A[40])
    (environment := [("table", encodeTable table), ("F", encodeSymbol symbol),
      ("value", encode value), ("statement", encode statement), ("claimed", encode claimed)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeResult (if Spec.WellFormed (signatureOf table) value then
      Spec.instantiateStatement (signatureOf table) symbol value statement else none), encode claimed])
    (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) (check_result_computes _ _)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (theoremInstantiation_computes table symbol value statement)

theorem checkInstantiation_result_exact (table : SignatureTable) (symbol : Spec.SymId)
    (value statement claimed : Spec.Term) (result : Term) :
    Applies P H "vibe:check-inst" [encodeTable table, encodeSymbol symbol, encode value, encode statement, encode claimed]
      result ↔ result = boolean (decide ((if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none) = some claimed)) := by
  constructor
  · intro checked
    exact checked.deterministic (checkInstantiation_computes table symbol value statement claimed)
  · intro same
    subst result
    exact checkInstantiation_computes table symbol value statement claimed

theorem checkInstantiation_completed_exact (table : SignatureTable) (symbol : Spec.SymId)
    (value statement claimed : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:check-inst"
      [encodeTable table, encodeSymbol symbol, encode value, encode statement, encode claimed] ≠ .exhausted) :
    apply P H fuel "vibe:check-inst" [encodeTable table, encodeSymbol symbol, encode value, encode statement, encode claimed] =
      .value (boolean (decide ((if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none) = some claimed))) :=
  (checkInstantiation_computes table symbol value statement claimed).completed fuel finished

theorem checkInstantiation_accepts_iff (table : SignatureTable) (symbol : Spec.SymId)
    (value statement claimed : Spec.Term) :
    Applies P H "vibe:check-inst" [encodeTable table, encodeSymbol symbol, encode value, encode statement, encode claimed]
      (.sym "True") ↔
      Spec.WellFormed (signatureOf table) value = true ∧
        Spec.instantiateStatement (signatureOf table) symbol value statement = some claimed := by
  have exactResult : Applies P H "vibe:check-inst"
      [encodeTable table, encodeSymbol symbol, encode value, encode statement, encode claimed] (.sym "True") ↔
      (if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none) = some claimed := by
    constructor
    · intro computed
      have same := computed.deterministic (checkInstantiation_computes table symbol value statement claimed)
      by_cases good : (if Spec.WellFormed (signatureOf table) value then
        Spec.instantiateStatement (signatureOf table) symbol value statement else none) = some claimed
      · exact good
      · simp [good, boolean] at same
    · intro good
      simpa only [good, decide_true, boolean, ↓reduceIte] using checkInstantiation_computes table symbol value statement claimed
  rw [exactResult]
  cases Spec.WellFormed (signatureOf table) value <;> simp

theorem theoremInstantiation_computes_for_signature (signature : Spec.Sig) (symbol : Spec.SymId)
    (value statement : Spec.Term) :
    Applies P H "vibe:thm-instantiate" [encodeTable (instantiationSnapshot signature symbol value statement),
      encodeSymbol symbol, encode value, encode statement]
      (encodeResult (if Spec.WellFormed signature value then
        Spec.instantiateStatement signature symbol value statement else none)) := by
  have formation := wellFormed_on_heads _ _ value (instantiationSnapshot_info signature symbol value statement).left.right
  simpa only [formation, snapshot_instantiation] using
    theoremInstantiation_computes (instantiationSnapshot signature symbol value statement) symbol value statement

theorem checkInstantiation_for_signature_iff (signature : Spec.Sig) (symbol : Spec.SymId)
    (value statement claimed : Spec.Term) :
    Applies P H "vibe:check-inst" [encodeTable (instantiationSnapshot signature symbol value statement),
      encodeSymbol symbol, encode value, encode statement, encode claimed] (.sym "True") ↔
      Spec.WellFormed signature value = true ∧ Spec.instantiateStatement signature symbol value statement = some claimed := by
  rw [checkInstantiation_accepts_iff,
    wellFormed_on_heads _ _ value (instantiationSnapshot_info signature symbol value statement).left.right,
    snapshot_instantiation]

theorem checkInstantiation_derived (theory : Spec.Theory) (symbol : Spec.SymId) (value statement claimed : Spec.Term)
    (statementDerived : Spec.Derives theory statement)
    (accepted : Applies P H "vibe:check-inst" [encodeTable (instantiationSnapshot theory.sig symbol value statement),
      encodeSymbol symbol, encode value, encode statement, encode claimed] (.sym "True")) :
    Spec.Derives theory claimed := by
  obtain ⟨formed, instantiated⟩ := (checkInstantiation_for_signature_iff theory.sig symbol value statement claimed).mp accepted
  exact .instantiate statementDerived formed instantiated

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInference
