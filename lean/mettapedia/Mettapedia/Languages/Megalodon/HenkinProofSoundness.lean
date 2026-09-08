import Mettapedia.Languages.Megalodon.HenkinNormalizationSemantics

/-!
# Native monomorphic proof soundness in Henkin models

The actual Mathdata proof checker retains its normalization and substitution
operations. Supported native proofs are interpreted recursively, not replaced
by independently authored intrinsic derivations. Hypotheses have exact typed
erasures; named facts and definition equations have independent model meaning.

The result concerns successful checking, including successful finite-fuel
normalization. It neither proves normalization completeness nor interprets
prefix-polymorphic proof constructors. No full-function-domain assumption is
made. Native acceptance does not supply the model's declaration equations or
the truth of an open proof's hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation.NativeProof

open MathdataKernel
open Mettapedia.Logic.HOL

universe w

variable {environment : Environment} {depth fuel : Nat}

/-- The supported native proof constructors and the local term-lookup
conditions needed to interpret their payloads. This does not assert validity. -/
inductive Fragment (environment : Environment) (depth : Nat) : Pf → Prop where
  | hyp (index : Nat) : Fragment environment depth (.hyp index)
  | known (name : Name) : Fragment environment depth (.known name)
  | proofApp {function argument : Pf} :
      Fragment environment depth function → Fragment environment depth argument →
      Fragment environment depth (.proofApp function argument)
  | termApp {function : Pf} {argument : Tm} :
      Fragment environment depth function → supported argument = true →
      PlainLookups environment depth argument →
      Fragment environment depth (.termApp function argument)
  | proofLam {proposition : Tm} {body : Pf} :
      supported proposition = true → PlainLookups environment depth proposition →
      Fragment environment depth body →
      Fragment environment depth (.proofLam proposition body)
  | termLam {type : Tp} {body : Pf} :
      Fragment environment depth body → Fragment environment depth (.termLam type body)

/-- Exact erasure of every hypothesis, including its list position. -/
def ErasedHypotheses {Γ : Ctx Base}
    (hypotheses : List (Formula (Constant environment) Γ)) (raw : List Tm) : Prop :=
  hypotheses.map erase = raw.map some

theorem ErasedHypotheses.lookup {Γ : Ctx Base}
    {hypotheses : List (Formula (Constant environment) Γ)} {raw : List Tm}
    (erased : ErasedHypotheses hypotheses raw) {index : Nat} {proposition : Tm}
    (lookup : raw[index]? = some proposition) :
    ∃ formula, formula ∈ hypotheses ∧ erase formula = some proposition := by
  induction hypotheses generalizing raw index with
  | nil =>
      cases raw <;> simp_all [ErasedHypotheses]
  | cons head tail ih =>
      cases raw with
      | nil => simp [ErasedHypotheses] at erased
      | cons rawHead rawTail =>
          have parts : erase head = some rawHead ∧ ErasedHypotheses tail rawTail := by
            simpa [ErasedHypotheses] using erased
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
              exact ⟨head, List.mem_cons_self, parts.1.trans (congrArg some lookup)⟩
          | succ index =>
              obtain ⟨formula, member, formulaErased⟩ := ih parts.2 lookup
              exact ⟨formula, List.mem_cons_of_mem _ member, formulaErased⟩

theorem ErasedHypotheses.cons {Γ : Ctx Base}
    {hypotheses : List (Formula (Constant environment) Γ)} {raw : List Tm}
    (erased : ErasedHypotheses hypotheses raw) {formula : Formula (Constant environment) Γ}
    {proposition : Tm} (formulaErased : erase formula = some proposition) :
    ErasedHypotheses (formula :: hypotheses) (proposition :: raw) := by
  simpa [ErasedHypotheses, formulaErased] using erased

theorem ErasedHypotheses.weaken {Γ : Ctx Base} {type : Ty Base}
    {hypotheses : List (Formula (Constant environment) Γ)} {raw : List Tm}
    (erased : ErasedHypotheses hypotheses raw) :
    ErasedHypotheses (weakenHyps (σ := type) hypotheses) (raw.map (Tm.shift 0 1)) := by
  change _ = _ at erased ⊢
  calc
    (weakenHyps (σ := type) hypotheses).map erase =
        (hypotheses.map erase).map (Option.map (Tm.shift 0 1)) := by
      simp [weakenHyps, List.map_map, erase_weaken]
    _ = (raw.map some).map (Option.map (Tm.shift 0 1)) := congrArg _ erased
    _ = (raw.map (Tm.shift 0 1)).map some := by simp [List.map_map]

/-- A named fact is independently interpreted and valid before the source
checker may use it. This is a model condition on declarations, not a claim
about arbitrary accepted proof terms. -/
def KnownValidity (M : HenkinModel.{0, 0, w} Base (Constant environment)) : Prop :=
  ∀ name raw, environment.lookupKnown? name = some raw →
    ∃ formula : ClosedFormula (Constant environment),
      erase formula = some raw ∧ M.models formula

/-- Successful native proof inference constructs a typed interpretation with
the exact returned syntax and establishes its meaning at every satisfying
admissible valuation. All normalization sites use the actual native pipeline. -/
theorem inferProof_sound
    (checked : CheckedPlainDefinitions environment)
    (M : HenkinModel.{0, 0, w} Base (Constant environment))
    (equations : DefinitionEquations checked M) (known : KnownValidity M)
    {Γ : Ctx Base} {hypotheses : List (Formula (Constant environment) Γ)}
    {rawHypotheses : List Tm} {proof : Pf} {result : Tm}
    (fragment : Fragment environment depth proof)
    (erased : ErasedHypotheses hypotheses rawHypotheses)
    (accepted : inferProof environment fuel depth (Γ.map reifyType) rawHypotheses proof =
      some result) :
    ∃ formula : Formula (Constant environment) Γ,
      erase formula = some result ∧
      ∀ valuation : M.Valuation Γ, M.ValuationAdmissible valuation →
        Soundness.SatisfiesHyps M valuation hypotheses → (M.denote formula valuation).down := by
  induction fragment generalizing Γ hypotheses rawHypotheses result with
  | hyp index =>
      obtain ⟨formula, member, formulaErased⟩ := erased.lookup accepted
      exact ⟨formula, formulaErased, fun _ _ satisfied => satisfied formula member⟩
  | known name =>
      obtain ⟨raw, lookup, normalized⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨formula, formulaErased, valid⟩ := known name raw lookup
      obtain ⟨output, outputErased, outputMeaning⟩ :=
        nativeNormalize_interpretation.{w} checked (weakenCtx Γ formula)
          ((erase_weakenCtx formula Γ).trans formulaErased) normalized
      refine ⟨output, outputErased, ?_⟩
      intro valuation _admissible _satisfied
      rw [outputMeaning M equations valuation, M.denote_weakenCtx]
      exact valid
  | @proofApp function argument functionFragment argumentFragment ihf iha =>
      cases inferredFunction : inferProof environment fuel depth (Γ.map reifyType)
          rawHypotheses function with
      | none => simp [inferProof, inferredFunction] at accepted
      | some functionResult =>
          cases functionResult <;> try simp [inferProof, inferredFunction] at accepted
          case imp domain codomain =>
            cases inferredArgument : inferProof environment fuel depth (Γ.map reifyType)
                rawHypotheses argument with
            | none => simp [inferredArgument] at accepted
            | some argumentResult =>
                by_cases equal : argumentResult = domain
                · subst argumentResult
                  have resultEqual : codomain = result := by
                    simpa [inferProof, inferredFunction, inferredArgument] using accepted
                  subst result
                  obtain ⟨functionFormula, functionErased, functionValid⟩ := ihf erased inferredFunction
                  obtain ⟨argumentFormula, argumentErased, argumentValid⟩ := iha erased inferredArgument
                  obtain ⟨domainFormula, codomainFormula, rfl, domainErased, codomainErased⟩ :=
                    erase_imp_inv functionErased
                  have same := erase_injective_of_eq_some argumentErased domainErased
                  subst argumentFormula
                  exact ⟨codomainFormula, codomainErased, fun valuation admissible satisfied =>
                    functionValid valuation admissible satisfied
                      (argumentValid valuation admissible satisfied)⟩
                · simp [inferredArgument, equal] at accepted
  | @termApp function argument functionFragment argumentSupported argumentLookups ih =>
      cases inferredFunction : inferProof environment fuel depth (Γ.map reifyType)
          rawHypotheses function with
      | none => simp [inferProof, inferredFunction] at accepted
      | some functionResult =>
          cases functionResult <;> try simp [inferProof, inferredFunction] at accepted
          case all domain body =>
            cases inferredArgument : inferTerm environment depth (Γ.map reifyType) argument with
            | none => simp [inferredArgument] at accepted
            | some argumentType =>
                by_cases equal : argumentType = domain
                · subst argumentType
                  have normalized : (do
                      let normalizedArgument ← deltaNormalize environment fuel argument
                      normalize environment fuel (Tm.instantiate normalizedArgument body)) =
                      some result := by
                    simpa [inferProof, inferredFunction, inferredArgument] using accepted
                  obtain ⟨rawArgument, expanded, normalizedResult⟩ :=
                    Option.bind_eq_some_iff.mp normalized
                  obtain ⟨functionFormula, functionErased, functionValid⟩ := ih erased inferredFunction
                  obtain ⟨type, bodyFormula, rfl, typeErased, bodyErased⟩ := erase_all_inv functionErased
                  obtain ⟨argumentValueType, argumentTerm, typed, argumentErased⟩ :=
                    interpret_of_plainLookups argumentLookups argumentSupported inferredArgument
                  have same := reifyType_injective (typed.trans typeErased)
                  subst argumentValueType
                  obtain ⟨expandedArgument, _expansion, expandedErased⟩ :=
                    (deltaNormalize_eq_some_iff checked fuel argumentTerm argumentErased).mp expanded
                  have instantiatedErased : erase (instantiate expandedArgument bodyFormula) =
                      some (Tm.instantiate rawArgument body) := by
                    rw [erase_instantiate expandedArgument bodyFormula expandedErased, bodyErased]
                    rfl
                  obtain ⟨output, outputErased, outputMeaning⟩ :=
                    nativeNormalize_interpretation.{w} checked
                      (instantiate expandedArgument bodyFormula) instantiatedErased normalizedResult
                  refine ⟨output, outputErased, ?_⟩
                  intro valuation admissible satisfied
                  rw [outputMeaning M equations valuation, Soundness.denote_instantiate_term]
                  exact functionValid valuation admissible satisfied
                    (M.denote expandedArgument valuation)
                    (M.denote_admissible admissible expandedArgument)
                · simp [inferredArgument, equal] at accepted
  | @proofLam proposition body propositionSupported propositionLookups bodyFragment ih =>
      cases inferred : inferTerm environment depth (Γ.map reifyType) proposition with
      | none => simp [inferProof, inferred] at accepted
      | some propositionType =>
          cases propositionType <;> try simp [inferProof, inferred] at accepted
          case prop =>
            have acceptedBody : (do
                let normalized ← normalize environment fuel proposition
                return Tm.imp normalized
                  (← inferProof environment fuel depth (Γ.map reifyType)
                    (normalized :: rawHypotheses) body)) = some result := by
              simpa [inferProof, inferred] using accepted
            obtain ⟨rawDomain, normalized, returned⟩ := Option.bind_eq_some_iff.mp acceptedBody
            obtain ⟨rawBody, inferredBody, resultEqual⟩ := Option.bind_eq_some_iff.mp returned
            cases resultEqual
            obtain ⟨type, propositionTerm, typed, propositionErased⟩ :=
              interpret_of_plainLookups propositionLookups propositionSupported inferred
            have same : type = .prop := reifyType_injective typed
            subst type
            obtain ⟨domainFormula, domainErased, _domainMeaning⟩ :=
              nativeNormalize_interpretation.{w} checked propositionTerm propositionErased normalized
            obtain ⟨bodyFormula, bodyErased, bodyValid⟩ :=
              ih (erased.cons domainErased) inferredBody
            refine ⟨.imp domainFormula bodyFormula, by simp [erase, domainErased, bodyErased], ?_⟩
            intro valuation admissible satisfied
            change (M.denote domainFormula valuation).down → _
            intro domainValid
            apply bodyValid valuation admissible
            intro formula member
            rcases List.mem_cons.mp member with rfl | member
            · exact domainValid
            · exact satisfied formula member
  | @termLam type body bodyFragment ih =>
      by_cases plain : type.plainWellFormed depth = true
      · have returned : (do
            return Tm.all type (← inferProof environment fuel depth
              (type :: Γ.map reifyType) (rawHypotheses.map (Tm.shift 0 1)) body)) =
            some result := by
          simpa [inferProof, plain] using accepted
        obtain ⟨rawBody, inferredBody, resultEqual⟩ := Option.bind_eq_some_iff.mp returned
        cases resultEqual
        obtain ⟨interpretedType, typeErased⟩ := exists_reifyType_of_plain plain
        obtain ⟨bodyFormula, bodyErased, bodyValid⟩ :=
          ih (Γ := interpretedType :: Γ) erased.weaken
            (by simpa [typeErased] using inferredBody)
        refine ⟨.all bodyFormula, by simp [erase, typeErased, bodyErased], ?_⟩
        intro valuation admissible satisfied
        change ∀ value, M.adm interpretedType value → _
        intro value valueAdmissible
        exact bodyValid (M.extend valuation value) (M.extend_admissible admissible valueAdmissible)
          (Soundness.satisfies_weakenHyps M satisfied value)
      · simp [inferProof, plain] at accepted

/-- An independently typed source goal is valid when its supported native
proof is accepted. Final normalization is part of the proof, not a no-op
precondition imposed on imported syntax. -/
theorem checkProof_sound
    (checked : CheckedPlainDefinitions environment)
    (M : HenkinModel.{0, 0, w} Base (Constant environment))
    (equations : DefinitionEquations checked M) (known : KnownValidity M)
    {Γ : Ctx Base} {hypotheses : List (Formula (Constant environment) Γ)}
    {rawHypotheses : List Tm} {proof : Pf} {proposition : Tm}
    (fragment : Fragment environment depth proof)
    (erased : ErasedHypotheses hypotheses rawHypotheses)
    (formula : Formula (Constant environment) Γ) (formulaErased : erase formula = some proposition)
    (accepted : checkProof environment fuel depth (Γ.map reifyType)
      rawHypotheses proof proposition = true)
    (valuation : M.Valuation Γ) (admissible : M.ValuationAdmissible valuation)
    (satisfied : Soundness.SatisfiesHyps M valuation hypotheses) :
    (M.denote formula valuation).down := by
  cases normalized : normalize environment fuel proposition with
  | none => simp [checkProof, normalized] at accepted
  | some result =>
      have inferred : inferProof environment fuel depth (Γ.map reifyType)
          rawHypotheses proof = some result := by
        simpa [checkProof, normalized, checkNormalizedProof] using accepted
      obtain ⟨output, outputErased, outputValid⟩ :=
        inferProof_sound checked M equations known fragment erased inferred
      rw [← denote_nativeNormalize checked M equations formula output
        formulaErased outputErased normalized valuation]
      exact outputValid valuation admissible satisfied

#print axioms ErasedHypotheses.lookup
#print axioms ErasedHypotheses.weaken
#print axioms inferProof_sound
#print axioms checkProof_sound

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation.NativeProof
