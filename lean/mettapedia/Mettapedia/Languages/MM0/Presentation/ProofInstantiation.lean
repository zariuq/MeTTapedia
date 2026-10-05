import Mettapedia.Languages.MM0.Presentation.ProofProgram

/-! # Exact theorem instantiation in the authored proof checker -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalProof

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "A" => proofEquations
local notation "H" => dataEqualityHost

theorem values_reused (arguments : List Preterm) :
    Applies P H "mm0:substitution-values" [encodeExpressions arguments] (encodeValues arguments) :=
  instantiation_reused _ (by decide) _ _ (ComputationalInstantiation.values_computes arguments)

theorem substitution_reused (source : Preterm) (arguments : List Preterm) :
    Applies P H "mm0:subst" [encode source, encodeValues arguments]
      (encodeResult (source.substitute (Substitution.ofList arguments))) :=
  instantiation_reused _ (by decide) _ _ (ComputationalInstantiation.substitution_reused source arguments)

theorem admissible_reused (table : SignatureTable) (formal target : Context) (arguments : List Preterm) :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions arguments]
      (boolean (Substitution.checkAdmissible (signatureOf table) formal target arguments)) :=
  instantiation_reused _ (by decide) _ _ (ComputationalInstantiation.admissible_reused table formal target arguments)

theorem substituted_tail_computes (first : Preterm) (rest : Option (List Preterm)) :
    Applies P H "mm0:subst-list-tail" [encodeResults rest, encode first]
      (encodeResults (rest.map (first :: ·))) := by
  cases rest with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some rest =>
      refine proof_equation (equation := A[6]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (.constructor (by rfl) (by rfl))
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (.primitive (by rfl) (by rfl))

theorem substituted_head_computes (first : Option Preterm) (rest arguments : List Preterm)
    (computed : Applies P H "mm0:subst-list" [encodeExpressions rest, encodeValues arguments]
      (encodeResults (Substitution.substituteList (Substitution.ofList arguments) rest))) :
    Applies P H "mm0:subst-list-head" [encodeResult first, encodeExpressions rest, encodeValues arguments]
      (encodeResults (do
        let first ← first
        let rest ← Substitution.substituteList (Substitution.ofList arguments) rest
        pure (first :: rest))) := by
  cases first with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some first =>
      refine proof_equation (equation := A[4]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [encodeResults (Substitution.substituteList (Substitution.ofList arguments) rest), encode first])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) computed
      · simpa [Option.map_eq_bind] using
          substituted_tail_computes first (Substitution.substituteList (Substitution.ofList arguments) rest)

theorem substitute_list_computes (sources arguments : List Preterm) :
    Applies P H "mm0:subst-list" [encodeExpressions sources, encodeValues arguments]
      (encodeResults (Substitution.substituteList (Substitution.ofList arguments) sources)) := by
  induction sources with
  | nil => exact ⟨3, by rw [proof_apply _ (by decide)]; rfl⟩
  | cons first rest ih =>
      refine proof_equation (equation := A[0]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [listView ((first :: rest).map encode), encodeValues arguments])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
          (.primitive (by rfl) (by rfl))
      · refine proof_equation (equation := A[2]) (by decide) (by rfl) (by rfl) ?_
        refine Evaluates.call
          (values := [encodeResult (first.substitute (Substitution.ofList arguments)), encodeExpressions rest, encodeValues arguments])
          (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
        · exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (substitution_reused first arguments)
        · simpa only [Substitution.substituteList] using
            substituted_head_computes (first.substitute (Substitution.ofList arguments)) rest arguments ih

theorem theorem_conclusion_computes (conclusion : Option Preterm) (hypotheses : List Preterm) :
    Applies P H "mm0:theorem-conclusion" [encodeResult conclusion, encodeExpressions hypotheses]
      (encodeInstance (conclusion.map fun result => ⟨hypotheses, result⟩)) := by
  cases conclusion <;> exact ⟨3, by rw [proof_apply _ (by decide)]; rfl⟩

theorem theorem_hypotheses_computes (hypotheses : Option (List Preterm)) (conclusion : Preterm)
    (arguments : List Preterm) :
    Applies P H "mm0:theorem-hypotheses" [encodeResults hypotheses, encode conclusion, encodeValues arguments]
      (encodeInstance (do
        let hypotheses ← hypotheses
        let conclusion ← conclusion.substitute (Substitution.ofList arguments)
        pure ⟨hypotheses, conclusion⟩)) := by
  cases hypotheses with
  | none => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | some hypotheses =>
      refine proof_equation (equation := A[12]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [encodeResult (conclusion.substitute (Substitution.ofList arguments)), encodeExpressions hypotheses])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (substitution_reused conclusion arguments)
      · simpa [Option.map_eq_bind] using
          theorem_conclusion_computes (conclusion.substitute (Substitution.ofList arguments)) hypotheses

theorem theorem_prepared_computes (hypotheses : List Preterm) (conclusion : Preterm) (arguments : List Preterm) :
    Applies P H "mm0:theorem-prepared" [encodeExpressions hypotheses, encode conclusion, encodeValues arguments]
      (encodeInstance (do
        let hypotheses ← Substitution.substituteList (Substitution.ofList arguments) hypotheses
        let conclusion ← conclusion.substitute (Substitution.ofList arguments)
        pure ⟨hypotheses, conclusion⟩)) := by
  refine proof_equation (equation := A[10]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (theorem_hypotheses_computes _ conclusion arguments)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (substitute_list_computes hypotheses arguments)

theorem theorem_admissible_computes (admitted : Bool) (hypotheses : List Preterm)
    (conclusion : Preterm) (arguments : List Preterm) :
    Applies P H "mm0:theorem-admissible"
      [boolean admitted, encodeExpressions hypotheses, encode conclusion, encodeExpressions arguments]
      (encodeInstance (if admitted then do
        let hypotheses ← Substitution.substituteList (Substitution.ofList arguments) hypotheses
        let conclusion ← conclusion.substitute (Substitution.ofList arguments)
        pure ⟨hypotheses, conclusion⟩ else none)) := by
  cases admitted with
  | false => exact ⟨1, by rw [proof_apply _ (by decide)]; rfl⟩
  | true =>
      refine proof_equation (equation := A[9]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ?_ .nil)))
        (theorem_prepared_computes hypotheses conclusion arguments)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (values_reused arguments)

theorem theorem_instantiation_computes (table : SignatureTable) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) :
    Applies P H "mm0:instantiate-theorem"
      [encodeTable table, encodeContext context, encodeTheorem declaration, encodeExpressions arguments]
      (encodeInstance (declaration.instantiate? (signatureOf table) context arguments)) := by
  refine proof_equation (equation := A[7]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call
    (values := [boolean (Substitution.checkAdmissible (signatureOf table) declaration.arguments context arguments),
      encodeExpressions declaration.hypotheses, encode declaration.conclusion, encodeExpressions arguments]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
      (admissible_reused table declaration.arguments context arguments)
  · exact theorem_admissible_computes _ declaration.hypotheses declaration.conclusion arguments

theorem theorem_instantiation_result_exact (table : SignatureTable) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) (result : Term) :
    Applies P H "mm0:instantiate-theorem"
      [encodeTable table, encodeContext context, encodeTheorem declaration, encodeExpressions arguments] result ↔
      result = encodeInstance (declaration.instantiate? (signatureOf table) context arguments) := by
  constructor
  · exact fun computed => computed.deterministic (theorem_instantiation_computes table context declaration arguments)
  · rintro rfl; exact theorem_instantiation_computes table context declaration arguments

theorem theorem_instantiation_accepts_iff (table : SignatureTable) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) (result : TheoremInstance) :
    Applies P H "mm0:instantiate-theorem"
      [encodeTable table, encodeContext context, encodeTheorem declaration, encodeExpressions arguments]
      (encodeInstance (some result)) ↔ TheoremDecl.Instantiates (signatureOf table) context declaration arguments result := by
  rw [theorem_instantiation_result_exact, ← TheoremDecl.instantiate_eq_some_iff]
  constructor
  · exact fun same => (encodeInstance_injective same).symm
  · exact fun same => congrArg encodeInstance same.symm

end Mettapedia.Languages.MM0.Presentation.ComputationalProof
