import Mettapedia.Languages.VibeITP.Presentation.SimultaneousTraversalCompleteness
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousKernelSoundness
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousPackage
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousExtension

/-! The independent static v2 calculus and its actual validated first-order
presentation derive exactly the same encoded statements over hosted theories.
Completeness constructs the structural inference derivation, retaining all
replacement checks and finite-word guards. Raw-article coverage is existential;
it does not extract runtime data from an erased proof. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Spec Spec.SimultaneousInstantiation SimultaneousFormation

theorem complete_statement_many {R : List FORule} (old : kernelRules ⊆ R)
    (added : simultaneousRules ⊆ R) {T : Theory} {allocated : Nat}
    (facts : theoryRules T allocated ⊆ R) (hosted : Hosted T allocated)
    (replacements : List (SymId × Spec.Term)) (source result : Spec.Term)
    (formed : ∀ pair ∈ replacements, WellFormed T.sig pair.2 = true)
    (shape : TermShape T.sig source)
    (accepted : statement T.sig replacements source = some result)
    (premise : FODerivable R (jThm (encTerm T.sig source))) :
    FODerivable R (jThm (encTerm T.sig result)) := by
  cases prepared : prepare T.sig replacements with
  | none => simp [statement, prepared] at accepted
  | some entries =>
      have entriesShape := prepare_shape T.sig replacements entries
        (fun pair member => wellFormed_termShape T.sig pair.2 (formed pair member)) prepared
      cases entries with
      | nil =>
          simp only [statement, prepared, List.isEmpty_nil, if_true] at accepted
          split at accepted
          · rename_i closed
            have same : source = result := Option.some.inj accepted
            subst result
            exact intro_rInstantiateManyNil (added (by simp [simultaneousRules]))
              (isData_encTerm _ _) premise
              (by simpa [closed, encNat] using complete_depth old T.sig source)
          · cases accepted
      | cons first rest =>
          simp only [statement, prepared, List.isEmpty_cons, Bool.false_eq_true, if_false] at accepted
          cases traversed : go T.sig (first :: rest) 0 source with
          | none => simp only [traversed] at accepted; cases accepted
          | some output =>
              simp only [traversed] at accepted
              split at accepted
              · rename_i closed
                have same : output = result := Option.some.inj accepted
                subst result
                cases replacements with
                | nil => simp [prepare] at prepared
                | cons pair tail =>
                    have replacementData : IsData (encReplacement T.sig pair) :=
                      IsData.app2 _ (isData_encSym T.sig pair.1)
                        (IsData.app2 _ (isData_encTerm T.sig pair.2) (IsData.app0 _))
                    exact intro_rInstantiateManyCons (added (by simp [simultaneousRules]))
                      replacementData (isData_encReplacements _ _)
                      (isData_encEntry _ _) (isData_encEntries _ _)
                      (isData_encTerm _ _) (isData_encTerm _ _) premise
                      (by simpa only [encReplacements_cons, encEntries_cons] using
                        complete_prepare old added facts hosted (pair :: tail) (first :: rest) formed prepared)
                      (by simpa [encEntries_cons, encNat] using
                        complete_many old added T.sig (first :: rest) 0 source output entriesShape shape traversed)
                      (by simpa [closed, encNat] using complete_depth old T.sig output)
              · cases accepted

theorem complete_derivesV2 {R : List FORule} (old : kernelRules ⊆ R)
    (added : simultaneousRules ⊆ R) {T : Theory} {allocated : Nat}
    (facts : theoryRules T allocated ⊆ R) (hosted : Hosted T allocated)
    {claim : Spec.Term} (derived : DerivesV2 T claim) :
    FODerivable R (jThm (encTerm T.sig claim)) := by
  generalize empty : ([] : List ExecutionObservation) = observations at derived
  induction derived with
  | base original =>
      subst observations
      exact complete_derives old facts hosted (execution_free_derives_static original)
  | modusPonens _ _ implication premise =>
      exact complete_modusPonens old T.sig hosted.builtin _ _ implication premise
  | @instantiateMany source result replacements child formed accepted ih =>
      exact complete_statement_many old added facts hosted replacements source result formed
        (SimultaneousExtension.derived_termShape hosted child) accepted ih
  | jit _ member _ _ => simp at member

theorem derivesV2_iff_foDerivable {T : Theory} {allocated : Nat}
    (hosted : Hosted T allocated) (claim : Spec.Term) :
    DerivesV2 T claim ↔ FODerivable (rulesV2 ++ theoryRules T allocated) (jThm (encTerm T.sig claim)) :=
  ⟨complete_derivesV2
      (fun _ member => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))))
      (fun _ member => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
      (fun _ member => List.mem_append.mpr (Or.inr member)) hosted,
    derives_of_foDerivableV2 hosted⟩

theorem derivesV2_iff_checkRaw {T : Theory} {allocated : Nat}
    (hosted : Hosted T allocated) (claim : Spec.Term) :
    DerivesV2 T claim ↔ ∃ article : RawProof,
      checkRaw (validatedV2 T allocated) (jThm (encTerm T.sig claim)) article = true :=
  (derivesV2_iff_foDerivable hosted claim).trans
    (checkRaw_exists_iff_foDerivable (validatedV2_presents T allocated) _).symm

theorem checkRaw_soundV2 {T : Theory} {allocated : Nat} (hosted : Hosted T allocated)
    {claim : Spec.Term} {article : RawProof}
    (accepted : checkRaw (validatedV2 T allocated) (jThm (encTerm T.sig claim)) article = true) :
    DerivesV2 T claim := checkRaw_sound_presentedV2 hosted (validatedV2_presents T allocated) accepted

#print axioms complete_statement_many
#print axioms complete_derivesV2
#print axioms derivesV2_iff_checkRaw
#print axioms checkRaw_soundV2

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
