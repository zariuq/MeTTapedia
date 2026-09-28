import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayQualifiedBetaPath

/-!
# Bounded search recovers finite qualified beta paths

The search acts on a supplied typing certificate. It is complete relative to
the finite root-beta paths represented by `QualifiedBetaPath`; this is not a
normalization result for arbitrary accepted terms. A failed bounded search
remains inconclusive.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {n : Nat}

/-- A certificate that actually contracts a root beta redex cannot also be
a terminal neutral elimination, including through cumulative wrappers. -/
theorem Code.neutralEliminations_beta_false
    (code : Code Head NoConversion n) (body : Tm Head (n + 1))
    (argument displayed : Tm Head n) (result : Code Head NoConversion n)
    (computed : code.contractBeta body argument displayed = some result) :
    code.neutralEliminations (.app (.lam body) argument) displayed = false := by
  induction code with
  | cumul level source ih =>
      cases displayed with
      | head upper =>
          cases h : source.contractBeta body argument (.head level) with
          | none => simp [Code.contractBeta, h] at computed
          | some reduced =>
              simpa only [Code.neutralEliminations] using
                ih body argument (.head level) reduced h
      | _ => simp [Code.contractBeta] at computed
  | appElim A B function argumentCode =>
      simp [Code.neutralEliminations, Tm.neutral]
  | _ => simp [Code.contractBeta] at computed

/-- A sufficiently large fuel bound makes the executable search recover the
exact terminal term and retained certificate of any supplied finite path.
The fuel exists from the path; no unrestricted normalization is inferred. -/
theorem QualifiedBetaPath.search_complete
    (R : Rules Head) (successor : Head → Head)
    (contextCode : ContextCode Head NoConversion n) (displayed : Tm Head n)
    {sourceTerm terminalTerm : Tm Head n}
    {sourceCode terminalCode : Code Head NoConversion n}
    (path : QualifiedBetaPath R successor contextCode displayed
      sourceTerm sourceCode terminalTerm terminalCode) :
    ∃ fuel, (sourceCode.qualifiedBetaPath? R successor contextCode
      fuel sourceTerm displayed).map Subtype.val = some (terminalTerm, terminalCode) := by
  induction path with
  | terminal subject code neutral =>
      refine ⟨1, ?_⟩
      simp [Code.qualifiedBetaPath?, neutral]
  | contraction qualified computed rest ih =>
      rename_i body argument source result terminalCode terminal
      obtain ⟨fuel, found⟩ := ih
      cases hsearch : result.qualifiedBetaPath? R successor contextCode
          fuel (inst0 argument body) displayed with
      | none => simp [hsearch] at found
      | some output =>
        have endpoint : output.val = (terminal, terminalCode) := by
          simpa only [hsearch, Option.map_some, Option.some.injEq] using found
        cases hbeta : source.contractBeta body argument displayed with
        | none => rw [hbeta] at computed; cases computed
        | some reduced =>
          have same : reduced = result := Option.some.inj (hbeta.symm.trans computed)
          subst reduced
          refine ⟨fuel + 1, ?_⟩
          simp only [Code.qualifiedBetaPath?,
            Code.neutralEliminations_beta_false _ _ _ _ _ computed,
            Bool.false_eq_true, ↓reduceDIte, qualified]
          split
          · rename_i impossible
            rw [impossible] at computed
            cases computed
          · rename_i reduced matched
            have same : reduced = result :=
              Option.some.inj (matched.symm.trans computed)
            subst reduced
            simp [hsearch, endpoint]

/-- A successful search equality exposes its retained path certificate at
the exact observed terminal term and code. This extracts existing evidence;
it does not reconstruct a typing certificate from erased syntax. -/
theorem QualifiedBetaPath.ofSearch
    (R : Rules Head) (successor : Head → Head)
    (contextCode : ContextCode Head NoConversion n) (displayed : Tm Head n)
    (sourceTerm terminalTerm : Tm Head n)
    (sourceCode terminalCode : Code Head NoConversion n) (fuel : Nat)
    (found : (sourceCode.qualifiedBetaPath? R successor contextCode
      fuel sourceTerm displayed).map Subtype.val = some (terminalTerm, terminalCode)) :
    QualifiedBetaPath R successor contextCode displayed sourceTerm sourceCode
      terminalTerm terminalCode := by
  cases hsearch : sourceCode.qualifiedBetaPath? R successor contextCode
      fuel sourceTerm displayed with
  | none => simp [hsearch] at found
  | some output =>
      have terminal : output.val = (terminalTerm, terminalCode) := by
        simpa only [hsearch, Option.map_some, Option.some.injEq] using found
      obtain ⟨⟨term, code⟩, path⟩ := output
      cases terminal
      exact path

#print axioms Code.neutralEliminations_beta_false
#print axioms QualifiedBetaPath.search_complete
#print axioms QualifiedBetaPath.ofSearch

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
