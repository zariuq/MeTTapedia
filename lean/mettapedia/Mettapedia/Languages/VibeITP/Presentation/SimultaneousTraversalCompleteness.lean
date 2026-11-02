import Mettapedia.Languages.VibeITP.Presentation.SimultaneousEnvironmentCompleteness

/-! Complete traversal certificates on the structural source profile.
Declared arities match source argument vectors. Every actual source refusal
guard remains part of the successful-operation premise; no new normalization
or unbounded physical-machine claim follows. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Spec Spec.SimultaneousInstantiation SimultaneousFormation

mutual
theorem complete_many {R : List FORule} (old : kernelRules ⊆ R) (added : simultaneousRules ⊆ R)
    (sig : Sig) (entries : List Entry) (offset : Nat) (source result : Spec.Term)
    (valid : EntriesShape sig entries) (shape : TermShape sig source)
    (computed : go sig entries offset source = some result) :
    FODerivable R (jMany (encEntries sig entries) (encNat offset) (encTerm sig source) (encTerm sig result)) := by
  by_cases absent : hasFvar sig source = false
  · have copied : go sig entries offset source = some source := by cases source <;> simp [go, absent]
    have same : source = result := Option.some.inj (copied.symm.trans computed)
    subst result
    exact intro_rManyNofv (added (by simp [simultaneousRules]))
      (isData_encEntries _ _) (isData_encNat _) (isData_encTerm _ _)
      (by simpa [absent, encBool] using complete_hasFvar old sig source)
  · cases source with
    | bvar _ => simp [hasFvar] at absent
    | lit _ => simp [hasFvar] at absent
    | app symbol arguments =>
        obtain ⟨info, declared, length, childrenShape⟩ := TermShape.app_iff.mp shape
        have binderLength : (bindersOf sig symbol).length = arguments.length := by
          simpa only [bindersOf, declared, SymInfo.arity] using length.symm
        have has : hasFvar sig (.app symbol arguments) = true := by
          cases found : hasFvar sig (.app symbol arguments) <;> simp_all
        have inputAnnotation : (isFvarSym sig symbol || hasFvarList sig arguments) = true := has
        simp only [go, if_neg absent] at computed
        cases processed : args sig entries symbol offset 0 arguments with
        | none => simp [processed] at computed
        | some output =>
            have sourceList : argumentList sig entries offset (bindersOf sig symbol) arguments = some output := by
              simpa only [args_eq_argumentList, List.drop_zero] using processed
            have outputShape := args_shape sig entries valid symbol offset 0 arguments output childrenShape processed
            have outputLength : (bindersOf sig symbol).length = output.length := binderLength.trans outputShape.2.symm
            have children := complete_many_args old added sig entries offset (bindersOf sig symbol)
              arguments output valid binderLength childrenShape sourceList
            simp only [processed] at computed
            cases selected : lookup entries symbol with
            | none =>
                have same : .app symbol output = result := by simpa only [selected, Option.some.injEq] using computed
                subst result
                have annotations := complete_annArgs old sig (bindersOf sig symbol) output outputLength
                rw [encTerm_app' sig symbol arguments, encTerm_app' sig symbol output, inputAnnotation, encSym_eq]
                cases kind : kindOf sig symbol with
                | constant =>
                    rw [isFvarSym_eq, kind]
                    exact intro_rManyConst (added (by simp [simultaneousRules]))
                      (isData_encEntries _ _) (isData_encNat _) (isData_encNat _) (isData_encNatList _)
                      (isData_encTermList _ _) (isData_encNat _) (isData_encTermList _ _) (isData_encNat _) (isData_encBool _)
                      children annotations
                | fvar =>
                    rw [isFvarSym_eq, kind]
                    exact intro_rManyAbsent (added (by simp [simultaneousRules]))
                      (isData_encEntries _ _) (isData_encNat _) (isData_encNat _) (isData_encNatList _)
                      (isData_encTermList _ _) (isData_encNat _) (isData_encTermList _ _) (isData_encNat _) (isData_encBool _)
                      (by simpa only [encSym_eq, kind, encKind] using complete_miss old added sig entries symbol valid kind selected)
                      children annotations
            | some entry =>
                obtain ⟨member, sameSymbol⟩ := lookup_member _ _ _ selected
                have entryValid := valid entry member
                have free : kindOf sig symbol = .fvar := by simpa only [sameSymbol] using entryValid.1.2.1
                have resultArity : output.length = entry.arity := by
                  rw [outputShape.2, length]
                  simpa only [IsFvarOf, symArity, sameSymbol, declared] using entryValid.1.2.2
                simp only [selected] at computed
                cases shifted : shift sig offset entry.arity entry.value with
                | none => simp [shifted] at computed
                | some replacement =>
                    have substituted : substBVars sig entry.arity output replacement 0 = some result := by
                      simpa only [shifted] using computed
                    have replacementShape := shift_termShape sig offset entry.arity entry.value replacement entryValid.2 shifted
                    rw [encTerm_app', inputAnnotation, encSym_eq, free]
                    exact intro_rManySelected (added (by simp [simultaneousRules]))
                      (isData_encEntries _ _) (isData_encNat _) (isData_encNat _) (isData_encNatList _)
                      (isData_encNat _) (isData_encTerm _ _) (isData_encTermList _ _) (isData_encNat _)
                      (isData_encTermList _ _) (isData_encTerm _ _) (isData_encTerm _ _)
                      (by simpa only [encSym_eq, free, encKind] using complete_hit old added sig entries symbol entry valid free selected)
                      children (complete_shift_shape old sig offset entry.arity entry.value replacement entryValid.2 shifted)
                      (complete_substTop_shape old sig entry.arity output replacement result resultArity outputShape.1 replacementShape substituted)
termination_by sizeOf source

theorem complete_many_args {R : List FORule} (old : kernelRules ⊆ R) (added : simultaneousRules ⊆ R)
    (sig : Sig) (entries : List Entry) (offset : Nat) (binders : List Nat) (source result : List Spec.Term)
    (valid : EntriesShape sig entries) (length : binders.length = source.length)
    (shape : TermShapeList sig source) (computed : argumentList sig entries offset binders source = some result) :
    FODerivable R (jManyArgs (encEntries sig entries) (encNat offset) (encNatList binders)
      (encTermList sig source) (encTermList sig result)) := by
  cases source with
  | nil =>
      have empty : binders = [] := List.length_eq_zero_iff.mp length
      have same : [] = result := Option.some.inj computed
      subst binders result
      exact intro_rManyArgsNil (added (by simp [simultaneousRules])) (isData_encEntries _ _) (isData_encNat _)
  | cons first rest =>
      cases binders with
      | nil => simp at length
      | cons binder tail =>
          have tailLength : tail.length = rest.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using length
          obtain ⟨firstShape, restShape⟩ := TermShapeList.cons_iff.mp shape
          change (if offset + binder < Spec.wordBound then
              match go sig entries (offset + binder) first,
                  argumentList sig entries offset tail rest with
              | some first', some rest' => some (first' :: rest')
              | _, _ => none
            else none) = some result at computed
          by_cases bounded : offset + binder < Spec.wordBound
          · rw [if_pos bounded] at computed
            cases head : go sig entries (offset + binder) first with
            | none => simp only [head] at computed; cases computed
            | some first' =>
                cases following : argumentList sig entries offset tail rest with
                | none => simp only [head, following] at computed; cases computed
                | some rest' =>
                    have same : first' :: rest' = result := by simpa only [head, following, Option.some.injEq] using computed
                    subst result
                    simp only [encNatList_cons, encTermList_cons]
                    exact intro_rManyArgsCons (added (by simp [simultaneousRules]))
                      (isData_encEntries _ _) (isData_encNat _) (isData_encNat _) (isData_encNatList _)
                      (isData_encTerm _ _) (isData_encTermList _ _) (isData_encTerm _ _) (isData_encTermList _ _) (isData_encNat _)
                      (complete_nadd old offset binder) (complete_nword old (offset + binder) bounded)
                      (complete_many old added sig entries (offset + binder) first first' valid firstShape head)
                      (complete_many_args old added sig entries offset tail rest rest' valid tailLength restShape following)
          · rw [if_neg bounded] at computed
            cases computed
termination_by sizeOf source
end

#print axioms complete_many
#print axioms complete_many_args

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
