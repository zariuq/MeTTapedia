import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.ScopedSyntax

/-!
# Scoped erasure of cost substitution

The raw cost syntax admits dangling de Bruijn indices that are not rho terms.
On the binder-safe fragment derived in `ScopedSyntax`, cost substitution erases
to the paper-facing semantic substitution up to pure structural congruence.
No executable free-drop equivalence is used.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

universe u

private theorem structuralApplyCongruenceOne {constructor : String}
    {left right : Pattern} (congruent : StructuralCongruence left right) :
    StructuralCongruence (.apply constructor [left]) (.apply constructor [right]) := by
  refine StructuralCongruence.apply_cong constructor [left] [right] rfl ?_
  intro index leftBound rightBound
  have indexBound : index < 1 := by simpa using leftBound
  have indexZero : index = 0 := by omega
  subst indexZero
  simpa using congruent

private theorem structuralApplyCongruenceTwo {constructor : String}
    {left₁ left₂ right₁ right₂ : Pattern}
    (first : StructuralCongruence left₁ right₁)
    (second : StructuralCongruence left₂ right₂) :
    StructuralCongruence
      (.apply constructor [left₁, left₂])
      (.apply constructor [right₁, right₂]) := by
  refine StructuralCongruence.apply_cong constructor
    [left₁, left₂] [right₁, right₂] rfl ?_
  intro index leftBound rightBound
  have indexBound : index < 2 := by simpa using leftBound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa using first
  · simpa using second

private theorem structuralParallelCongruenceTwo
    {left₁ left₂ right₁ right₂ : Pattern}
    (first : StructuralCongruence left₁ right₁)
    (second : StructuralCongruence left₂ right₂) :
    StructuralCongruence
      (.collection .hashBag [left₁, left₂] none)
      (.collection .hashBag [right₁, right₂] none) := by
  refine StructuralCongruence.par_cong [left₁, left₂] [right₁, right₂] rfl ?_
  intro index leftBound rightBound
  have indexBound : index < 2 := by simpa using leftBound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa using first
  · simpa using second

mutual
  /-- Erasure forgets every syntactic effect of lifting above the available
  name scope. -/
  theorem CostName.BinderSafeAt.erase_liftAbove_eq
      {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
      {scope cutoff amount : Nat} {name : CostName Ground}
      (safe : name.BinderSafeAt scope) (scopeLe : scope ≤ cutoff) :
      (name.lift amount cutoff).erase signatureName = name.erase signatureName := by
    cases safe with
    | bvar inScope =>
        have belowCutoff : ¬ cutoff ≤ _ :=
          Nat.not_le.mpr (Nat.lt_of_lt_of_le inScope scopeLe)
        simp [CostName.lift, CostName.erase, belowCutoff]
    | quote => rfl
    | signature => rfl

  /-- Process form of erasure-inert lifting. -/
  theorem CostProc.BinderSafeAt.erase_liftAbove_eq
      {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
      {scope cutoff amount : Nat} {process : CostProc Ground}
      (safe : process.BinderSafeAt scope) (scopeLe : scope ≤ cutoff) :
      (process.lift amount cutoff).erase signatureName = process.erase signatureName := by
    cases safe with
    | nil => rfl
    | par leftSafe rightSafe =>
        simp [CostProc.lift, CostProc.erase,
          leftSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe,
          rightSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe]
    | send channelSafe payloadSafe =>
        simp [CostProc.lift, CostProc.erase,
          channelSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe,
          payloadSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe]
    | recv channelSafe bodySafe =>
        simp [CostProc.lift, CostProc.erase,
          channelSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe,
          bodySafe.erase_liftAbove_eq (signatureName := signatureName)
            (Nat.add_le_add_right scopeLe 1)]

  /-- Cost-term form of erasure-inert lifting.  Purse locations may change
  syntactically, but purse erasure remains the parallel identity. -/
  theorem CostTerm.BinderSafeAt.erase_liftAbove_eq
      {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
      {scope cutoff amount : Nat} {term : CostTerm Ground}
      (safe : term.BinderSafeAt scope) (scopeLe : scope ≤ cutoff) :
      (term.lift amount cutoff).erase signatureName = term.erase signatureName := by
    cases safe with
    | nil => rfl
    | signed processSafe =>
        simp [CostTerm.lift, CostTerm.erase,
          processSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe]
    | par leftSafe rightSafe =>
        simp [CostTerm.lift, CostTerm.erase,
          leftSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe,
          rightSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe]
    | drop nameSafe =>
        simp [CostTerm.lift, CostTerm.erase,
          nameSafe.erase_liftAbove_eq (signatureName := signatureName) scopeLe]
    | purse => rfl
end

/-- A binder-safe cost name never hides the distinguished outer index beneath
a quotation after erasure. -/
theorem CostName.BinderSafeAt.erase_noBoundUnderQuote
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {scope index : Nat} {name : CostName Ground}
    (safe : name.BinderSafeAt scope) :
    noBoundUnderQuote index (name.erase signatureName) = true := by
  cases safe with
  | bvar => rfl
  | quote termSafe =>
      have typed := termSafe.erase_wellSorted signatureTyped
      simpa [CostName.erase, noBoundUnderQuote] using
        procWellSorted_noBVarAtOrAbove typed (Nat.zero_le index)
  | signature =>
      simpa [CostName.erase] using
        nameWellSorted_noBoundUnderQuoteAtOrAbove (signatureTyped _) (Nat.zero_le index)

/-- Cost name substitution is exactly generic rho opening after erasure. -/
theorem CostName.BinderSafeAt.erase_substitute_eq_rhoOpen
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {depth : Nat} {name : CostName Ground} {replacement : CostTerm Ground}
    (safe : name.BinderSafeAt (depth + 1))
    (replacementSafe : replacement.BinderSafe) :
    (CostName.substitute replacement depth name).erase signatureName =
      rhoOpenNameBVar depth
        (.apply "NQuote" [replacement.erase signatureName])
        (name.erase signatureName) := by
  cases safe with
  | @bvar safeDepth index inScope =>
      by_cases matched : index = depth
      · subst index
        simp [CostName.substitute, CostName.erase, rhoOpenNameBVar,
          replacementSafe.erase_liftAbove_eq
            (signatureName := signatureName) (scope := 0) (cutoff := 0)
            (amount := depth) (le_refl 0)]
      · have notHigher : ¬ depth < index := by omega
        have unequal : (index == depth) = false := beq_eq_false_iff_ne.mpr matched
        simp [CostName.substitute, CostName.erase, rhoOpenNameBVar,
          matched, notHigher, unequal]
  | @quote safeDepth quotedTerm quotedSafe => rfl
  | @signature safeDepth signature =>
      have typed := signatureTyped signature
      have opacity := nameWellSorted_noBoundUnderQuoteAtOrAbove typed (Nat.zero_le depth)
      have absent := nameWellSorted_noBVarAtOrAbove typed (Nat.zero_le depth)
      simp only [CostName.substitute, CostName.erase]
      rw [rhoOpenNameBVar_eq_openBVar_of_noBoundUnderQuote opacity]
      simp [openBVar_eq_self_of_noBVar absent]

/-- On the scoped fragment, cost name substitution and semantic name
substitution agree at the name-equivalence level. -/
theorem CostName.BinderSafeAt.erase_substitute_nameEquiv
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {depth : Nat} {name : CostName Ground} {replacement : CostTerm Ground}
    (safe : name.BinderSafeAt (depth + 1))
    (replacementSafe : replacement.BinderSafe) :
    NameEquiv
      ((CostName.substitute replacement depth name).erase signatureName)
      (semanticSubstName depth
        (.apply "NQuote" [semanticNormalizeProc (replacement.erase signatureName)])
        (name.erase signatureName)) := by
  rw [safe.erase_substitute_eq_rhoOpen signatureTyped replacementSafe]
  have typed := safe.erase_wellSorted signatureTyped
  have shape := nameWellSorted_rhoCoreShape typed
  have opacity := safe.erase_noBoundUnderQuote signatureTyped (index := depth)
  have rawToOpen :=
    semanticSubstName_equiv_rhoOpenNameBVar_of_rhoNameCoreShape
      depth (replacement.erase signatureName) shape opacity
  have normalizedToRaw :=
    semanticSubstName_transport_to_representative
      depth (replacement.erase signatureName) (name.erase signatureName)
  exact NameEquiv.trans _ _ _
    (NameEquiv.symm _ _ rawToOpen)
    (NameEquiv.symm _ _ normalizedToRaw)

mutual
  /-- Process substitution in the cost syntax erases to semantic rho
  substitution up to pure structural congruence. -/
  theorem CostProc.BinderSafeAt.erase_substitute_structural
      {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
      {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
      {depth : Nat} {process : CostProc Ground} {replacement : CostTerm Ground}
      (safe : process.BinderSafeAt (depth + 1))
      (replacementSafe : replacement.BinderSafe) :
      StructuralCongruence
        ((CostProc.substitute replacement depth process).erase signatureName)
        (semanticSubstProc depth
          (.apply "NQuote" [semanticNormalizeProc (replacement.erase signatureName)])
          (process.erase signatureName)) := by
    cases safe with
    | nil => exact StructuralCongruence.refl _
    | par leftSafe rightSafe =>
        simpa [CostProc.substitute, CostProc.erase, semanticSubstProc,
          semanticSubstProcList] using
          structuralParallelCongruenceTwo
            (leftSafe.erase_substitute_structural signatureTyped replacementSafe)
            (rightSafe.erase_substitute_structural signatureTyped replacementSafe)
    | send channelSafe payloadSafe =>
        simpa [CostProc.substitute, CostProc.erase, semanticSubstProc] using
          structuralApplyCongruenceTwo
            (nameEquiv_implies_struct
              (channelSafe.erase_substitute_nameEquiv signatureTyped replacementSafe))
            (payloadSafe.erase_substitute_structural signatureTyped replacementSafe)
    | recv channelSafe bodySafe =>
        have bodyCongruent := bodySafe.erase_substitute_structural
          signatureTyped replacementSafe
        simpa [CostProc.substitute, CostProc.erase, semanticSubstProc,
          Nat.add_assoc] using
          structuralApplyCongruenceTwo
            (nameEquiv_implies_struct
              (channelSafe.erase_substitute_nameEquiv signatureTyped replacementSafe))
            (StructuralCongruence.lambda_cong none _ _ bodyCongruent)

  /-- Cost-term substitution has the same scoped semantic agreement.  The
  matched-drop case is related by normalization soundness, not by executable
  free-drop congruence. -/
  theorem CostTerm.BinderSafeAt.erase_substitute_structural
      {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
      {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
      {depth : Nat} {term replacement : CostTerm Ground}
      (safe : term.BinderSafeAt (depth + 1))
      (replacementSafe : replacement.BinderSafe) :
      StructuralCongruence
        ((CostTerm.substitute replacement depth term).erase signatureName)
        (semanticSubstProc depth
          (.apply "NQuote" [semanticNormalizeProc (replacement.erase signatureName)])
          (term.erase signatureName)) := by
    cases safe with
    | nil => exact StructuralCongruence.refl _
    | signed processSafe =>
        simpa [CostTerm.substitute, CostTerm.erase] using
          processSafe.erase_substitute_structural signatureTyped replacementSafe
    | par leftSafe rightSafe =>
        simpa [CostTerm.substitute, CostTerm.erase, semanticSubstProc,
          semanticSubstProcList] using
          structuralParallelCongruenceTwo
            (leftSafe.erase_substitute_structural signatureTyped replacementSafe)
            (rightSafe.erase_substitute_structural signatureTyped replacementSafe)
    | @drop safeDepth name nameSafe =>
        cases nameSafe with
        | @bvar nameDepth index inScope =>
            by_cases matched : index = depth
            · subst index
              simpa [CostTerm.substitute, CostTerm.erase, CostName.erase,
                semanticSubstProc, semanticSubstNameMark, semanticNormalizeName,
                replacementSafe.erase_liftAbove_eq
                  (signatureName := signatureName) (scope := 0) (cutoff := 0)
                  (amount := depth) (le_refl 0)] using
                (StructuralCongruence.symm _ _
                  (semanticNormalizeProc_sound (replacement.erase signatureName)))
            · have notHigher : ¬ depth < index := by omega
              have unequal : (index == depth) = false := beq_eq_false_iff_ne.mpr matched
              simpa [CostTerm.substitute, CostTerm.erase, CostName.erase,
                semanticSubstProc, semanticSubstNameMark, semanticNormalizeName,
                matched, notHigher, unequal] using
                (StructuralCongruence.refl
                  (.apply "PDrop" [.bvar index]))
        | @quote nameDepth quotedTerm quotedSafe =>
            have nameSafe :
                CostName.BinderSafeAt (depth + 1) (.quote quotedTerm) :=
              .quote quotedSafe
            have typed := nameSafe.erase_wellSorted signatureTyped
            have shape := nameWellSorted_rhoCoreShape typed
            have absent : noBVar depth ((CostName.quote quotedTerm).erase signatureName) = true := by
              have quotedTyped := quotedSafe.erase_wellSorted signatureTyped
              simpa [CostName.erase, noBVar, noBVarList] using
                procWellSorted_noBVarAtOrAbove quotedTyped (Nat.zero_le depth)
            have notMatched :=
              semanticSubstNameMark_matched_false_of_rhoNameCoreShape_noBVar
                depth
                (.apply "NQuote" [semanticNormalizeProc (replacement.erase signatureName)])
                shape absent
            cases markEq : semanticSubstNameMark depth
                (.apply "NQuote" [semanticNormalizeProc (replacement.erase signatureName)])
                ((CostName.quote quotedTerm).erase signatureName) with
            | mk substituted matchedFlag =>
                cases matchedFlag with
                | false =>
                    have nameCongruent := nameEquiv_implies_struct
                      (nameSafe.erase_substitute_nameEquiv signatureTyped replacementSafe)
                    simpa [CostTerm.substitute, CostTerm.erase, CostName.substitute,
                      semanticSubstProc, semanticSubstName, markEq] using
                      structuralApplyCongruenceOne nameCongruent
                | true => simp [markEq] at notMatched
        | @signature nameDepth signature =>
            have nameSafe :
                CostName.BinderSafeAt (depth + 1) (.signature signature) := .signature
            have typed := nameSafe.erase_wellSorted signatureTyped
            have shape := nameWellSorted_rhoCoreShape typed
            have absent := nameWellSorted_noBVarAtOrAbove
              (signatureTyped signature) (Nat.zero_le depth)
            have notMatched :=
              semanticSubstNameMark_matched_false_of_rhoNameCoreShape_noBVar
                depth
                (.apply "NQuote" [semanticNormalizeProc (replacement.erase signatureName)])
                shape absent
            cases markEq : semanticSubstNameMark depth
                (.apply "NQuote" [semanticNormalizeProc (replacement.erase signatureName)])
                ((CostName.signature signature).erase signatureName) with
            | mk substituted matchedFlag =>
                cases matchedFlag with
                | false =>
                    have nameCongruent := nameEquiv_implies_struct
                      (nameSafe.erase_substitute_nameEquiv signatureTyped replacementSafe)
                    simpa [CostTerm.substitute, CostTerm.erase, CostName.substitute,
                      semanticSubstProc, semanticSubstName, markEq] using
                      structuralApplyCongruenceOne nameCongruent
                | true => simp [markEq] at notMatched
    | purse => exact StructuralCongruence.refl _
end

/-- The funded COMM contractum erases to the pure semantic COMM contractum on
the genuine scoped fragment. -/
theorem CostTerm.BinderSafeAt.erase_commSubst_structural
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {body payload : CostTerm Ground}
    (bodySafe : body.BinderSafeAt 1) (payloadSafe : payload.BinderSafe) :
    StructuralCongruence
      ((body.commSubst payload).erase signatureName)
      (semanticCommSubst (body.erase signatureName) (payload.erase signatureName)) := by
  simpa [CostTerm.commSubst, semanticCommSubst] using
    bodySafe.erase_substitute_structural signatureTyped payloadSafe

/-! ## Canonical configuration erasure -/

/-- A well-sorted signature interpretation stays inside the pure carrier. -/
theorem SignatureNameEncoding.WellSorted.hashSetFree
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (typed : signatureName.WellSorted free) :
    ∀ signature, HashSetFree (signatureName signature) :=
  fun signature => rhoNameWellSorted_hashSetFree (typed signature)

private theorem hashSetFreeList_map_costErase
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    (signaturePure : ∀ signature, HashSetFree (signatureName signature)) :
    ∀ terms : List (CostTerm Ground),
      HashSetFreeList (terms.map (CostTerm.erase signatureName))
  | [] => by simp [HashSetFreeList]
  | term :: terms => by
      exact ⟨CostTerm.hashSetFree_erase signaturePure term,
        hashSetFreeList_map_costErase signaturePure terms⟩

/-- Canonical pure-rho representative of a cost configuration.  The
definition descends through the multiset quotient; it never selects a list by
choice. -/
def CostConfig.eraseCanonical {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature)) :
    CostConfig Ground → Pattern :=
  Quotient.lift
    (fun terms => Canonical.canonicalize
      (.collection .hashBag (terms.map (CostTerm.erase signatureName)) none))
    (by
      intro left right permutation
      apply Canonical.canonicalize_eq_of_structuralCongruence
        (StructuralCongruence.par_perm _ _ (permutation.map _))
      · exact hashSetFreeList_map_costErase signaturePure left
      · exact hashSetFreeList_map_costErase signaturePure right)

/-- Evaluation of canonical configuration erasure on an explicit list. -/
@[simp]
theorem CostConfig.eraseCanonical_quotientMk {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (terms : List (CostTerm Ground)) :
    CostConfig.eraseCanonical signatureName signaturePure
        (Quotient.mk _ terms : CostConfig Ground) =
      Canonical.canonicalize
        (.collection .hashBag (terms.map (CostTerm.erase signatureName)) none) :=
  rfl

/-- Canonical configuration erasure is structurally congruent to every list
representative of the multiset. -/
theorem CostConfig.eraseCanonical_structural_quotientMk {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (terms : List (CostTerm Ground)) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (Quotient.mk _ terms : CostConfig Ground))
      (.collection .hashBag (terms.map (CostTerm.erase signatureName)) none) := by
  exact StructuralCongruence.symm _ _
    (Canonical.canonicalize_sound
      (.collection .hashBag (terms.map (CostTerm.erase signatureName)) none))

/-! ## Controls -/

/-- Positive control: the defining bound drop satisfies scoped COMM erasure. -/
example {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free) :
    StructuralCongruence
      (((CostTerm.drop (.bvar 0) : CostTerm Ground).commSubst .nil).erase signatureName)
      (semanticCommSubst
        ((CostTerm.drop (.bvar 0) : CostTerm Ground).erase signatureName)
        ((CostTerm.nil : CostTerm Ground).erase signatureName)) := by
  exact CostTerm.BinderSafeAt.erase_commSubst_structural signatureTyped
    (.drop (.bvar (by omega))) .nil

/-- Negative control: the raw quoted-capture counterexample is excluded by the
binder-safe premise rather than admitted through a broader equivalence. -/
example {Ground : Type u} :
    ¬(CostTerm.drop (.quote (.drop (.bvar 0))) : CostTerm Ground).BinderSafeAt 1 :=
  quoted_surrounding_binder_not_safe

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
