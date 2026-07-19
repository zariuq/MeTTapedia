import Mettapedia.Languages.Metamath.InferenceProjection

/-!
# Formula-local agreement for Metamath substitutions

The live verifier substitutes a formula by reading its `HashMap` only at
variable symbols that occur in that formula.  This file makes that locality
explicit: two runtime maps give the same substitution result when their
lookups agree on the variables in the source body.  A second theorem obtains
the same conclusion from the projection's finite known-variable gate.
-/

namespace Mettapedia.Languages.Metamath.InferenceFormulaLookupAgreement

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection

private theorem foldlM_substStep_eq_of_lookup_agreement
    (symbols : List RuntimeSym)
    (sigmaOne sigmaTwo : Std.HashMap String RuntimeFormula)
    (lookupAgreement :
      ∀ name, .var name ∈ symbols →
        sigmaOne[name]? = sigmaTwo[name]?)
    (accumulator : RuntimeFormula) :
    symbols.foldlM (Metamath.Verify.Formula.substStep sigmaOne) accumulator =
      symbols.foldlM (Metamath.Verify.Formula.substStep sigmaTwo) accumulator := by
  induction symbols generalizing accumulator with
  | nil => rfl
  | cons symbol symbols ih =>
      have stepAgreement :
          Metamath.Verify.Formula.substStep sigmaOne accumulator symbol =
            Metamath.Verify.Formula.substStep sigmaTwo accumulator symbol := by
        cases symbol with
        | const constant => rfl
        | var name =>
            simp only [Metamath.Verify.Formula.substStep]
            rw [lookupAgreement name (by simp)]
      simp only [List.foldlM_cons]
      rw [stepAgreement]
      cases step :
          Metamath.Verify.Formula.substStep sigmaTwo accumulator symbol with
      | error error => rfl
      | ok next =>
          simp only [Bind.bind, Except.bind]
          apply ih
          intro name hmem
          exact lookupAgreement name (by simp [hmem])

/-- Formula substitution is local to lookups of tagged variables occurring in
the source body.  Constants and names absent from the body cannot distinguish
the two maps. -/
theorem formula_subst_eq_of_body_lookup_agreement
    (source : ConstantHeadedFormula)
    (sigmaOne sigmaTwo : Std.HashMap String RuntimeFormula)
    (lookupAgreement :
      ∀ name, .var name ∈ source.body →
        sigmaOne[name]? = sigmaTwo[name]?) :
    source.toRuntime.subst sigmaOne =
      source.toRuntime.subst sigmaTwo := by
  unfold Metamath.Verify.Formula.subst
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  simp only [ConstantHeadedFormula.toRuntime]
  simp only [List.foldlM_cons, Metamath.Verify.Formula.substStep, Bind.bind,
    Except.bind]
  exact foldlM_substStep_eq_of_lookup_agreement
    source.body sigmaOne sigmaTwo lookupAgreement #[.const source.typecode]

/-- The finite `formulaVariablesKnown` gate is sufficient: agreement on every
available name implies agreement on every variable the formula can read. -/
theorem formula_subst_eq_of_known_variables
    (available : List String)
    (source : ConstantHeadedFormula)
    (sigmaOne sigmaTwo : Std.HashMap String RuntimeFormula)
    (variablesKnown : formulaVariablesKnown available source = true)
    (lookupAgreement :
      ∀ name, name ∈ available →
        sigmaOne[name]? = sigmaTwo[name]?) :
    source.toRuntime.subst sigmaOne =
      source.toRuntime.subst sigmaTwo := by
  apply formula_subst_eq_of_body_lookup_agreement
  intro name hmem
  unfold formulaVariablesKnown at variablesKnown
  have hknown := List.all_eq_true.mp variablesKnown (.var name) hmem
  exact lookupAgreement name (by simpa using hknown)

/-! ## Executable boundaries -/

private def exampleSource : ConstantHeadedFormula :=
  ⟨"wff", [.var "x", .const "imp"]⟩

private def exampleReplacement (bodyConstant : String) :
    ConstantHeadedFormula :=
  ⟨"wff", [.const bodyConstant]⟩

private def exampleMap (bodyConstant : String) :
    Std.HashMap String RuntimeFormula :=
  ({} : Std.HashMap String RuntimeFormula).insert
    "x" (exampleReplacement bodyConstant).toRuntime

private def exampleMapWithUnusedKey : Std.HashMap String RuntimeFormula :=
  (exampleMap "A").insert "unused" (exampleReplacement "UNUSED").toRuntime

/-- Positive boundary: inserting an additional key absent from the source body
does not affect the substitution result. -/
example :
    exampleSource.toRuntime.subst (exampleMap "A") =
      exampleSource.toRuntime.subst exampleMapWithUnusedKey := by
  apply formula_subst_eq_of_body_lookup_agreement
  intro name hmem
  have hname : name = "x" := by
    simpa [exampleSource] using hmem
  subst name
  unfold exampleMapWithUnusedKey
  rw [Std.HashMap.getElem?_insert]
  simp [exampleMap]

private theorem example_subst_output (bodyConstant : String) :
    exampleSource.toRuntime.subst (exampleMap bodyConstant) =
      .ok #[.const "wff", .const bodyConstant, .const "imp"] := by
  have hfold :
      Array.foldl Array.push
        #[Metamath.Verify.Sym.const "wff"]
        #[Metamath.Verify.Sym.const "wff",
          Metamath.Verify.Sym.const bodyConstant] 1 2 =
      #[Metamath.Verify.Sym.const "wff",
        Metamath.Verify.Sym.const bodyConstant] := by
    apply Array.ext'
    have h := Metamath.Kernel.array_foldl_push_toList
      #[Metamath.Verify.Sym.const "wff",
        Metamath.Verify.Sym.const bodyConstant]
      #[Metamath.Verify.Sym.const "wff"] 1
    change
      (Array.foldl Array.push
        #[Metamath.Verify.Sym.const "wff"]
        #[Metamath.Verify.Sym.const "wff",
          Metamath.Verify.Sym.const bodyConstant] 1 2).toList = _ at h
    simpa using h
  simp [exampleSource, exampleMap, exampleReplacement,
    ConstantHeadedFormula.toRuntime, Metamath.Verify.Formula.subst,
    Metamath.Verify.Formula.substStep]
  simp only [Bind.bind, Except.bind]
  rw [hfold]
  simp

/-- Negative boundary: changing the image of the used variable is outside the
agreement hypothesis and concretely changes the substituted formula. -/
example :
    exampleSource.toRuntime.subst (exampleMap "A") ≠
      exampleSource.toRuntime.subst (exampleMap "B") := by
  rw [example_subst_output, example_subst_output]
  simp

end Mettapedia.Languages.Metamath.InferenceFormulaLookupAgreement
