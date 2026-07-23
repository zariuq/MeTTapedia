import Mettapedia.Languages.MeTTa.HE.UnificationCompleteness

/-!
# Semantic existence of repaired-LeaTTa binding merges

This module proves a LeaTTa-intrinsic completeness fact used by direct
conformance to the spec match/merge relation: two host-float-free binding
sets that share a satisfying valuation have a successful merge.  The proof
uses Robinson completeness, not the executable HE matcher or merger.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMergeExistence

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

private theorem reconciliation_exists
    {valuation : String → Metta.Atom} {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hbindings : LeaBindingSatisfied valuation bindings)
    (hextra : MettaEquationsSatisfied valuation extra) :
    ∃ result, Metta.Bindings.reconcileAll bindings extra = some result := by
  apply exists_reconcileAll_of_satisfied bindings extra
  · intro equation hmem
    simp only [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact leaBindingEquations_noFloat hbindingsNoFloat equation
        (by simpa [leaBindingEquations] using hmem)
    · exact hextraNoFloat equation hmem
  · apply (mettaEquationsSatisfied_append_iff valuation
      (leaBindingEquations bindings) extra).mpr
    exact ⟨(leaBindingEquations_solution_iff valuation bindings).mpr
      hbindings, hextra⟩

/-- A satisfiable alias insertion cannot fail.  The returned binding remains
in the HE-translatable fragment and retains the common valuation. -/
theorem addVarEquality_exists_of_satisfied
    {valuation : String → Metta.Atom} {bindings : Metta.Bindings}
    {left right : String}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hbindings : LeaBindingSatisfied valuation bindings)
    (hequality : valuation left = valuation right) :
    ∃ out,
      out ∈ Metta.Bindings.addVarEquality bindings left right ∧
        LeaBindingSatisfied valuation out ∧
          LeaBindingsNoFloat out := by
  let candidate := Metta.Bindings.addEqRaw bindings left right
  have hcandidateNoFloat : LeaBindingsNoFloat candidate :=
    leaBindingsNoFloat_addEqRaw hbindingsNoFloat
  have hcandidate : LeaBindingSatisfied valuation candidate :=
    (leaBindingSatisfied_addEqRaw_iff valuation bindings left right).mpr
      ⟨hbindings, hequality⟩
  cases hvalues : Metta.Bindings.classValues candidate left with
  | nil =>
      refine ⟨candidate, ?_, hcandidate, hcandidateNoFloat⟩
      simp [Metta.Bindings.addVarEquality, Metta.Bindings.unifyValues,
        candidate, hvalues]
  | cons first rest =>
      have hfirstNoFloat : MettaAtomNoFloat first :=
        leaClassValue_noFloat hcandidateNoFloat (by rw [hvalues]; simp)
      have hrestNoFloat : ∀ value ∈ rest, MettaAtomNoFloat value := by
        intro value hmem
        exact leaClassValue_noFloat hcandidateNoFloat
          (by rw [hvalues]; simp [hmem])
      have hrestSatisfied : ∀ value ∈ rest,
          applyClassSolution valuation first =
            applyClassSolution valuation value := by
        intro value hmem
        exact
          (leaBindingSatisfied_classValue hcandidate
            (by rw [hvalues]; simp)).symm.trans
          (leaBindingSatisfied_classValue hcandidate
            (by rw [hvalues]; simp [hmem]))
      obtain ⟨result, hunify⟩ :=
        exists_unifyValues_of_satisfied first rest hfirstNoFloat
          hrestNoFloat hrestSatisfied
      cases result with
      | nil =>
          refine ⟨candidate, ?_, hcandidate, hcandidateNoFloat⟩
          simp [Metta.Bindings.addVarEquality, candidate, hvalues, hunify]
      | cons binding resultRest =>
          have hextraNoFloat : ∀ equation ∈
              [(Metta.Atom.var left, Metta.Atom.var right)],
              MettaAtomNoFloat equation.1 ∧
                MettaAtomNoFloat equation.2 := by
            intro equation hmem
            simp only [List.mem_singleton] at hmem
            subst equation
            simp [MettaAtomNoFloat]
          have hextraSatisfied : MettaEquationsSatisfied valuation
              [(Metta.Atom.var left, Metta.Atom.var right)] := by
            intro equation hmem
            simp only [List.mem_singleton] at hmem
            subst equation
            simpa [MettaEquationSatisfied, applyClassSolution]
              using hequality
          obtain ⟨sigma, hreconcile⟩ := reconciliation_exists
            hbindingsNoFloat hextraNoFloat hbindings hextraSatisfied
          let out := Metta.Bindings.rebuildFromReconciliation candidate
            bindings [(Metta.Atom.var left, Metta.Atom.var right)] sigma
          have hout : out ∈
              Metta.Bindings.addVarEquality bindings left right := by
            simp [Metta.Bindings.addVarEquality, candidate, hvalues,
              hunify, hreconcile, out]
          refine ⟨out, hout, ?_,
            leaAddVarEquality_result_noFloat hbindingsNoFloat hout⟩
          exact (leaAddVarEquality_solution_iff valuation
            hbindingsNoFloat hout).mpr ⟨hbindings, hequality⟩

private theorem addVarBinding_nonVar_exists_of_satisfied
    {valuation : String → Metta.Atom} {bindings : Metta.Bindings}
    {key : String} {value : Metta.Atom}
    (hnonvar : ∀ other, value ≠ .var other)
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hbindings : LeaBindingSatisfied valuation bindings)
    (hvalue : valuation key = applyClassSolution valuation value) :
    ∃ out,
      out ∈ Metta.Bindings.addVarBinding bindings key value ∧
        LeaBindingSatisfied valuation out ∧
          LeaBindingsNoFloat out := by
  cases hvalues : Metta.Bindings.classValues bindings key with
  | nil =>
      let out := Metta.Bindings.addValRaw bindings key value
      have hout : out ∈ Metta.Bindings.addVarBinding bindings key value := by
        cases value <;> simp_all [Metta.Bindings.addVarBinding, out]
      refine ⟨out, hout, ?_,
        leaAddVarBinding_result_noFloat hbindingsNoFloat hvalueNoFloat hout⟩
      exact (leaAddVarBinding_solution_iff valuation hbindingsNoFloat
        hvalueNoFloat hout).mpr ⟨hbindings, hvalue⟩
  | cons first rest =>
      have hfirstNoFloat : MettaAtomNoFloat first :=
        leaClassValue_noFloat hbindingsNoFloat (by rw [hvalues]; simp)
      have htailNoFloat : ∀ item ∈ rest ++ [value],
          MettaAtomNoFloat item := by
        intro item hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact leaClassValue_noFloat hbindingsNoFloat
            (by rw [hvalues]; simp [hmem])
        · simp only [List.mem_singleton] at hmem
          subst item
          exact hvalueNoFloat
      have htailSatisfied : ∀ item ∈ rest ++ [value],
          applyClassSolution valuation first =
            applyClassSolution valuation item := by
        intro item hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact
            (leaBindingSatisfied_classValue hbindings
              (by rw [hvalues]; simp)).symm.trans
            (leaBindingSatisfied_classValue hbindings
              (by rw [hvalues]; simp [hmem]))
        · simp only [List.mem_singleton] at hmem
          subst item
          exact
            (leaBindingSatisfied_classValue hbindings
              (by rw [hvalues]; simp)).symm.trans hvalue
      obtain ⟨result, hunify⟩ := exists_unifyValues_of_satisfied
        first (rest ++ [value]) hfirstNoFloat htailNoFloat htailSatisfied
      cases result with
      | nil =>
          refine ⟨bindings, ?_, hbindings, hbindingsNoFloat⟩
          cases value <;>
            simp_all [Metta.Bindings.addVarBinding]
      | cons binding resultRest =>
          have hextraNoFloat : ∀ equation ∈
              [(Metta.Atom.var key, value)],
              MettaAtomNoFloat equation.1 ∧
                MettaAtomNoFloat equation.2 := by
            intro equation hmem
            simp only [List.mem_singleton] at hmem
            subst equation
            exact ⟨by simp [MettaAtomNoFloat], hvalueNoFloat⟩
          have hextraSatisfied : MettaEquationsSatisfied valuation
              [(Metta.Atom.var key, value)] := by
            intro equation hmem
            simp only [List.mem_singleton] at hmem
            subst equation
            simpa [MettaEquationSatisfied, applyClassSolution] using hvalue
          obtain ⟨sigma, hreconcile⟩ := reconciliation_exists
            hbindingsNoFloat hextraNoFloat hbindings hextraSatisfied
          let out := Metta.Bindings.rebuildFromReconciliation bindings
            bindings [(Metta.Atom.var key, value)] sigma
          have hout : out ∈
              Metta.Bindings.addVarBinding bindings key value := by
            cases value <;>
              simp_all [Metta.Bindings.addVarBinding, out]
          refine ⟨out, hout, ?_,
            leaAddVarBinding_result_noFloat hbindingsNoFloat
              hvalueNoFloat hout⟩
          exact (leaAddVarBinding_solution_iff valuation hbindingsNoFloat
            hvalueNoFloat hout).mpr ⟨hbindings, hvalue⟩

/-- A satisfiable value insertion cannot fail. -/
theorem addVarBinding_exists_of_satisfied
    {valuation : String → Metta.Atom} {bindings : Metta.Bindings}
    {key : String} {value : Metta.Atom}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hbindings : LeaBindingSatisfied valuation bindings)
    (hvalue : valuation key = applyClassSolution valuation value) :
    ∃ out,
      out ∈ Metta.Bindings.addVarBinding bindings key value ∧
        LeaBindingSatisfied valuation out ∧
          LeaBindingsNoFloat out := by
  cases value with
  | var other =>
      simpa [Metta.Bindings.addVarBinding, applyClassSolution] using
        (addVarEquality_exists_of_satisfied hbindingsNoFloat hbindings
          (by simpa [applyClassSolution] using hvalue))
  | sym symbol =>
      exact addVarBinding_nonVar_exists_of_satisfied
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat
          hbindings hvalue
  | gnd ground =>
      exact addVarBinding_nonVar_exists_of_satisfied
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat
          hbindings hvalue
  | expr atoms =>
      exact addVarBinding_nonVar_exists_of_satisfied
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat
          hbindings hvalue

private theorem mergeFold_exists_of_satisfied
    {valuation : String → Metta.Atom} :
    ∀ (relations : Metta.Bindings) (candidates : List Metta.Bindings),
      (∀ key value, Metta.BindingRel.val key value ∈ relations →
        MettaAtomNoFloat value) →
      (∀ key value, Metta.BindingRel.val key value ∈ relations →
        valuation key = applyClassSolution valuation value) →
      (∀ left right, Metta.BindingRel.eq left right ∈ relations →
        valuation left = valuation right) →
      ∀ {current}, current ∈ candidates →
        LeaBindingSatisfied valuation current →
        LeaBindingsNoFloat current →
        ∃ out,
          out ∈ relations.foldl Metta.Bindings.mergeOne candidates ∧
            LeaBindingSatisfied valuation out ∧
              LeaBindingsNoFloat out := by
  intro relations
  induction relations with
  | nil =>
      intro candidates hnoFloat hvalues hequalities current hcurrent
        hcurrentSatisfied hcurrentNoFloat
      exact ⟨current, hcurrent, hcurrentSatisfied, hcurrentNoFloat⟩
  | cons relation rest ih =>
      intro candidates hnoFloat hvalues hequalities current hcurrent
        hcurrentSatisfied hcurrentNoFloat
      have hnoFloatRest : ∀ key value,
          Metta.BindingRel.val key value ∈ rest →
            MettaAtomNoFloat value := by
        intro key value hmem
        exact hnoFloat key value (by simp [hmem])
      have hvaluesRest : ∀ key value,
          Metta.BindingRel.val key value ∈ rest →
            valuation key = applyClassSolution valuation value := by
        intro key value hmem
        exact hvalues key value (by simp [hmem])
      have hequalitiesRest : ∀ left right,
          Metta.BindingRel.eq left right ∈ rest →
            valuation left = valuation right := by
        intro left right hmem
        exact hequalities left right (by simp [hmem])
      cases relation with
      | val key value =>
          obtain ⟨next, hnext, hnextSatisfied, hnextNoFloat⟩ :=
            addVarBinding_exists_of_satisfied hcurrentNoFloat
              (hnoFloat key value (by simp)) hcurrentSatisfied
              (hvalues key value (by simp))
          apply ih (Metta.Bindings.mergeOne candidates (.val key value))
            hnoFloatRest hvaluesRest hequalitiesRest
            (current := next)
          · exact List.mem_flatMap.mpr ⟨current, hcurrent, hnext⟩
          · exact hnextSatisfied
          · exact hnextNoFloat
      | eq left right =>
          obtain ⟨next, hnext, hnextSatisfied, hnextNoFloat⟩ :=
            addVarEquality_exists_of_satisfied hcurrentNoFloat
              hcurrentSatisfied (hequalities left right (by simp))
          apply ih (Metta.Bindings.mergeOne candidates (.eq left right))
            hnoFloatRest hvaluesRest hequalitiesRest
            (current := next)
          · exact List.mem_flatMap.mpr ⟨current, hcurrent, hnext⟩
          · exact hnextSatisfied
          · exact hnextNoFloat

/-- Two repaired-LeaTTa binding sets with a common satisfying valuation have
a successful merge.  The witness retains that valuation and remains in the
host-float-free fragment. -/
theorem merge_exists_of_satisfied
    {valuation : String → Metta.Atom} {left right : Metta.Bindings}
    (hleftNoFloat : LeaBindingsNoFloat left)
    (hrightNoFloat : LeaBindingsNoFloat right)
    (hleft : LeaBindingSatisfied valuation left)
    (hright : LeaBindingSatisfied valuation right) :
    ∃ out,
      out ∈ Metta.Bindings.merge left right ∧
        LeaBindingSatisfied valuation out ∧
          LeaBindingsNoFloat out := by
  exact mergeFold_exists_of_satisfied right [left]
    hrightNoFloat hright.1 hright.2 (by simp) hleft hleftNoFloat

/-! ## Executable canaries -/

/-- Positive: the semantic theorem constructs a merge for a fresh value
constraint without reducing the executable merger by computation. -/
example : ∃ out,
    out ∈ Metta.Bindings.merge []
      [Metta.BindingRel.val "x" (.sym "a")] := by
  let valuation : String → Metta.Atom := fun _ => .sym "a"
  obtain ⟨out, hout, _⟩ := merge_exists_of_satisfied
    (valuation := valuation) (left := [])
    (right := [Metta.BindingRel.val "x" (.sym "a")])
    (by simp [LeaBindingsNoFloat])
    (by simp [LeaBindingsNoFloat, MettaAtomNoFloat])
    (by simp [LeaBindingSatisfied])
    (by simp [LeaBindingSatisfied, valuation, applyClassSolution])
  exact ⟨out, hout⟩

/-- Negative: incompatible ground values have no common satisfying valuation,
so the semantic existence theorem correctly does not apply. -/
example : ¬∃ valuation : String → Metta.Atom,
    LeaBindingSatisfied valuation
        [Metta.BindingRel.val "x" (.sym "a")] ∧
      LeaBindingSatisfied valuation
        [Metta.BindingRel.val "x" (.sym "b")] := by
  rintro ⟨valuation, hleft, hright⟩
  have hleftValue := hleft.1 "x" (.sym "a") (by simp)
  have hrightValue := hright.1 "x" (.sym "b") (by simp)
  simp [applyClassSolution] at hleftValue hrightValue
  have himpossible : "a" = "b" :=
    Metta.Atom.sym.inj (hleftValue.symm.trans hrightValue)
  simp at himpossible

end Mettapedia.Languages.MeTTa.HE.LeaTTaMergeExistence
