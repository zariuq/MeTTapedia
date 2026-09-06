import Mettapedia.Languages.SUMO.Native.Soundness

/-!
# An executable checker for native SUMO proofs

`Certificate` is untrusted proof syntax.  Its constructors name the native
logical rules, but do not carry an asserted conclusion.  `infer` reconstructs
that conclusion from the current intrinsically scoped assumption context and
rejects every mismatched rule application.

The checker therefore validates SUMO formulas at their native logical level:
it does not accept generic rule labels, imported target-logic theorems, or an
unchecked conclusion field.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native

universe uSymbol uLiteral

/-- Untrusted proof syntax for the native SUMO logical core. -/
inductive Certificate (Symbol : Type uSymbol) (Literal : Type uLiteral) :
    Nat -> Nat -> Type (max uSymbol uLiteral) where
  | hypothesis {ordinary rows : Nat} (index : Nat) :
      Certificate Symbol Literal ordinary rows
  | topIntroduction {ordinary rows : Nat} :
      Certificate Symbol Literal ordinary rows
  | bottomElimination {ordinary rows : Nat}
      (result : Formula Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | andIntroduction {ordinary rows : Nat}
      (left right : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | andEliminationLeft {ordinary rows : Nat}
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | andEliminationRight {ordinary rows : Nat}
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | orIntroductionLeft {ordinary rows : Nat}
      (right : Formula Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | orIntroductionRight {ordinary rows : Nat}
      (left : Formula Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | orElimination {ordinary rows : Nat}
      (disjunction leftBranch rightBranch :
        Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | implicationIntroduction {ordinary rows : Nat}
      (antecedent : Formula Symbol Literal ordinary rows)
      (body : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | implicationElimination {ordinary rows : Nat}
      (functionProof argumentProof : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | negationIntroduction {ordinary rows : Nat}
      (body : Formula Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | negationElimination {ordinary rows : Nat}
      (negative positive : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | iffIntroduction {ordinary rows : Nat}
      (forward reverse : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | iffEliminationLeft {ordinary rows : Nat}
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | iffEliminationRight {ordinary rows : Nat}
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | allInSpineFromAllObject {ordinary rows : Nat}
      (arguments : Spine Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | allInSpineNilIntroduction {ordinary rows : Nat}
      (body : Formula Symbol Literal (ordinary + 1) rows) :
      Certificate Symbol Literal ordinary rows
  | allInSpineTermIntroduction {ordinary rows : Nat}
      (value : Term Symbol Literal ordinary rows)
      (valueProof restProof : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | allInSpineHeadElimination {ordinary rows : Nat}
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | allInSpineTermTailElimination {ordinary rows : Nat}
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | allInSpineRowTailElimination {ordinary rows : Nat}
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | allObjectIntroduction {ordinary rows : Nat}
      (body : Certificate Symbol Literal (ordinary + 1) rows) :
      Certificate Symbol Literal ordinary rows
  | allObjectElimination {ordinary rows : Nat}
      (value : Term Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | someObjectIntroduction {ordinary rows : Nat}
      (body : Formula Symbol Literal (ordinary + 1) rows)
      (value : Term Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | someObjectElimination {ordinary rows : Nat}
      (result : Formula Symbol Literal ordinary rows)
      (existential : Certificate Symbol Literal ordinary rows)
      (branch : Certificate Symbol Literal (ordinary + 1) rows) :
      Certificate Symbol Literal ordinary rows
  | allRowIntroduction {ordinary rows : Nat}
      (body : Certificate Symbol Literal ordinary (rows + 1)) :
      Certificate Symbol Literal ordinary rows
  | allRowElimination {ordinary rows : Nat}
      (arguments : Spine Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | someRowIntroduction {ordinary rows : Nat}
      (body : Formula Symbol Literal ordinary (rows + 1))
      (arguments : Spine Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | someRowElimination {ordinary rows : Nat}
      (result : Formula Symbol Literal ordinary rows)
      (existential : Certificate Symbol Literal ordinary rows)
      (branch : Certificate Symbol Literal ordinary (rows + 1)) :
      Certificate Symbol Literal ordinary rows
  | equalityReflexivity {ordinary rows : Nat}
      (value : Term Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | equalitySubstitution {ordinary rows : Nat}
      (context : Formula Symbol Literal (ordinary + 1) rows)
      (equality contextProof : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows
  | classicalContradiction {ordinary rows : Nat}
      (body : Formula Symbol Literal ordinary rows)
      (premise : Certificate Symbol Literal ordinary rows) :
      Certificate Symbol Literal ordinary rows

namespace Certificate

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}

/-- A conclusion reconstructed together with its native derivation. -/
abbrev Checked
    {ordinary rows : Nat}
    (assumptions : List (Formula Symbol Literal ordinary rows)) :=
  { conclusion : Formula Symbol Literal ordinary rows //
    Derivation Symbol Literal assumptions conclusion }

/-- Check an untrusted certificate while constructing its native derivation.
The proof component is erased at execution time, while its type prevents an
accepted certificate from escaping the native calculus. -/
def check [DecidableEq Symbol] [DecidableEq Literal] :
    {ordinary rows : Nat} ->
    (assumptions : List (Formula Symbol Literal ordinary rows)) ->
    Certificate Symbol Literal ordinary rows ->
    Option (Checked assumptions)
  | _, _, assumptions, .hypothesis index =>
      if inBounds : index < assumptions.length then
        some ⟨assumptions[index], .hypothesis (List.getElem_mem inBounds)⟩
      else none
  | _, _, _, .topIntroduction => some ⟨.top, .topIntroduction⟩
  | _, _, assumptions, .bottomElimination result premise =>
      match check assumptions premise with
      | some ⟨.bottom, proof⟩ => some ⟨result, .bottomElimination proof⟩
      | _ => none
  | _, _, assumptions, .andIntroduction left right => do
      let ⟨leftConclusion, leftProof⟩ <- check assumptions left
      let ⟨rightConclusion, rightProof⟩ <- check assumptions right
      some ⟨.and leftConclusion rightConclusion,
        .andIntroduction leftProof rightProof⟩
  | _, _, assumptions, .andEliminationLeft premise =>
      match check assumptions premise with
      | some ⟨.and left _, proof⟩ => some ⟨left, .andEliminationLeft proof⟩
      | _ => none
  | _, _, assumptions, .andEliminationRight premise =>
      match check assumptions premise with
      | some ⟨.and _ right, proof⟩ => some ⟨right, .andEliminationRight proof⟩
      | _ => none
  | _, _, assumptions, .orIntroductionLeft right premise => do
      let ⟨left, proof⟩ <- check assumptions premise
      some ⟨.or left right, .orIntroductionLeft proof⟩
  | _, _, assumptions, .orIntroductionRight left premise => do
      let ⟨right, proof⟩ <- check assumptions premise
      some ⟨.or left right, .orIntroductionRight proof⟩
  | _, _, assumptions, .orElimination disjunction leftBranch rightBranch =>
      match check assumptions disjunction with
      | some ⟨.or left right, disjunctionProof⟩ => do
          let ⟨leftResult, leftProof⟩ <- check (left :: assumptions) leftBranch
          let ⟨rightResult, rightProof⟩ <- check (right :: assumptions) rightBranch
          if sameResult : leftResult = rightResult then
            some ⟨leftResult, .orElimination disjunctionProof leftProof
              (sameResult.symm ▸ rightProof)⟩
          else none
      | _ => none
  | _, _, assumptions, .implicationIntroduction antecedent body => do
      let ⟨consequent, proof⟩ <- check (antecedent :: assumptions) body
      some ⟨.implies antecedent consequent, .implicationIntroduction proof⟩
  | _, _, assumptions, .implicationElimination functionProof argumentProof =>
      match check assumptions functionProof with
      | some ⟨.implies antecedent consequent, functionDerivation⟩ => do
          let ⟨argument, argumentDerivation⟩ <- check assumptions argumentProof
          if sameConclusion : argument = antecedent then
            some ⟨consequent, .implicationElimination functionDerivation
              (sameConclusion ▸ argumentDerivation)⟩
          else none
      | _ => none
  | _, _, assumptions, .negationIntroduction body premise =>
      match check (body :: assumptions) premise with
      | some ⟨.bottom, proof⟩ => some ⟨.not body, .negationIntroduction proof⟩
      | _ => none
  | _, _, assumptions, .negationElimination negative positive =>
      match check assumptions negative with
      | some ⟨.not body, negativeProof⟩ => do
          let ⟨positiveBody, positiveProof⟩ <- check assumptions positive
          if sameConclusion : positiveBody = body then
            some ⟨.bottom, .negationElimination negativeProof
              (sameConclusion ▸ positiveProof)⟩
          else none
      | _ => none
  | _, _, assumptions, .iffIntroduction forward reverse =>
      match check assumptions forward, check assumptions reverse with
      | some ⟨.implies left right, forwardProof⟩,
          some ⟨.implies right' left', reverseProof⟩ =>
          if sameLeft : left = left' then
            if sameRight : right = right' then
              some ⟨.iff left right, .iffIntroduction forwardProof
                (sameRight.symm ▸ sameLeft.symm ▸ reverseProof)⟩
            else none
          else none
      | _, _ => none
  | _, _, assumptions, .iffEliminationLeft premise =>
      match check assumptions premise with
      | some ⟨.iff left right, proof⟩ =>
          some ⟨.implies left right, .iffEliminationLeft proof⟩
      | _ => none
  | _, _, assumptions, .iffEliminationRight premise =>
      match check assumptions premise with
      | some ⟨.iff left right, proof⟩ =>
          some ⟨.implies right left, .iffEliminationRight proof⟩
      | _ => none
  | _, _, assumptions, .allInSpineFromAllObject arguments premise =>
      match check assumptions premise with
      | some ⟨.allObject body, proof⟩ =>
          some ⟨.allInSpine arguments body,
            .allInSpineFromAllObject arguments proof⟩
      | _ => none
  | _, _, _, .allInSpineNilIntroduction body =>
      some ⟨.allInSpine .nil body, .allInSpineNilIntroduction body⟩
  | _, _, assumptions, .allInSpineTermIntroduction value valueProof restProof =>
      match check assumptions restProof with
      | some ⟨.allInSpine rest body, restDerivation⟩ => do
          let ⟨valueConclusion, valueDerivation⟩ <- check assumptions valueProof
          if sameConclusion : valueConclusion =
              Substitution.instantiateObjectFormula value body then
            some ⟨.allInSpine (.term value rest) body,
              .allInSpineTermIntroduction value rest
                (sameConclusion ▸ valueDerivation) restDerivation⟩
          else none
      | _ => none
  | _, _, assumptions, .allInSpineHeadElimination premise =>
      match check assumptions premise with
      | some ⟨.allInSpine (.term value rest) body, proof⟩ =>
          some ⟨Substitution.instantiateObjectFormula value body,
            .allInSpineHeadElimination proof⟩
      | _ => none
  | _, _, assumptions, .allInSpineTermTailElimination premise =>
      match check assumptions premise with
      | some ⟨.allInSpine (.term value rest) body, proof⟩ =>
          some ⟨.allInSpine rest body, .allInSpineTermTailElimination proof⟩
      | _ => none
  | _, _, assumptions, .allInSpineRowTailElimination premise =>
      match check assumptions premise with
      | some ⟨.allInSpine (.row rowIndex rest) body, proof⟩ =>
          some ⟨.allInSpine rest body, .allInSpineRowTailElimination proof⟩
      | _ => none
  | _, _, assumptions, .allObjectIntroduction body => do
      let ⟨conclusion, proof⟩ <- check (weakenObjectHypotheses assumptions) body
      some ⟨.allObject conclusion, .allObjectIntroduction proof⟩
  | _, _, assumptions, .allObjectElimination value premise =>
      match check assumptions premise with
      | some ⟨.allObject body, proof⟩ =>
          some ⟨Substitution.instantiateObjectFormula value body,
            .allObjectElimination value proof⟩
      | _ => none
  | _, _, assumptions, .someObjectIntroduction body value premise => do
      let ⟨conclusion, proof⟩ <- check assumptions premise
      if sameConclusion : conclusion =
          Substitution.instantiateObjectFormula value body then
        some ⟨.someObject body,
          .someObjectIntroduction value (sameConclusion ▸ proof)⟩
      else none
  | _, _, assumptions, .someObjectElimination result existential branch =>
      match check assumptions existential with
      | some ⟨.someObject body, existentialProof⟩ => do
          let ⟨branchConclusion, branchProof⟩ <-
            check (body :: weakenObjectHypotheses assumptions) branch
          if sameConclusion : branchConclusion =
              Renaming.weakenObjectFormula result then
            some ⟨result, .someObjectElimination existentialProof
              (sameConclusion ▸ branchProof)⟩
          else none
      | _ => none
  | _, _, assumptions, .allRowIntroduction body => do
      let ⟨conclusion, proof⟩ <- check (weakenRowHypotheses assumptions) body
      some ⟨.allRow conclusion, .allRowIntroduction proof⟩
  | _, _, assumptions, .allRowElimination arguments premise =>
      match check assumptions premise with
      | some ⟨.allRow body, proof⟩ =>
          some ⟨Substitution.instantiateRowFormula arguments body,
            .allRowElimination arguments proof⟩
      | _ => none
  | _, _, assumptions, .someRowIntroduction body arguments premise => do
      let ⟨conclusion, proof⟩ <- check assumptions premise
      if sameConclusion : conclusion =
          Substitution.instantiateRowFormula arguments body then
        some ⟨.someRow body,
          .someRowIntroduction arguments (sameConclusion ▸ proof)⟩
      else none
  | _, _, assumptions, .someRowElimination result existential branch =>
      match check assumptions existential with
      | some ⟨.someRow body, existentialProof⟩ => do
          let ⟨branchConclusion, branchProof⟩ <-
            check (body :: weakenRowHypotheses assumptions) branch
          if sameConclusion : branchConclusion =
              Renaming.weakenRowFormula result then
            some ⟨result, .someRowElimination existentialProof
              (sameConclusion ▸ branchProof)⟩
          else none
      | _ => none
  | _, _, _, .equalityReflexivity value =>
      some ⟨.equal value value, .equalityReflexivity value⟩
  | _, _, assumptions, .equalitySubstitution context equality contextProof =>
      match check assumptions equality with
      | some ⟨.equal left right, equalityDerivation⟩ => do
          let ⟨contextConclusion, contextDerivation⟩ <- check assumptions contextProof
          if sameConclusion : contextConclusion =
              Substitution.instantiateObjectFormula left context then
            some ⟨Substitution.instantiateObjectFormula right context,
              .equalitySubstitution context equalityDerivation
                (sameConclusion ▸ contextDerivation)⟩
          else none
      | _ => none
  | _, _, assumptions, .classicalContradiction body premise =>
      match check ((.not body) :: assumptions) premise with
      | some ⟨.bottom, proof⟩ => some ⟨body, .classicalContradiction proof⟩
      | _ => none

/-- Erase the checked derivation and return only the reconstructed conclusion. -/
def infer [DecidableEq Symbol] [DecidableEq Literal]
    {ordinary rows : Nat}
    (assumptions : List (Formula Symbol Literal ordinary rows))
    (certificate : Certificate Symbol Literal ordinary rows) :
    Option (Formula Symbol Literal ordinary rows) :=
  (check assumptions certificate).map Subtype.val

/-- Acceptance by `infer` yields a derivation in the native calculus. -/
theorem infer_sound [DecidableEq Symbol] [DecidableEq Literal]
    {ordinary rows : Nat}
    {assumptions : List (Formula Symbol Literal ordinary rows)}
    {body : Formula Symbol Literal ordinary rows}
    {certificate : Certificate Symbol Literal ordinary rows}
    (accepted : infer assumptions certificate = some body) :
    Derivation Symbol Literal assumptions body := by
  rw [infer, Option.map_eq_some_iff] at accepted
  obtain ⟨checked, checkedEquality, conclusionEquality⟩ := accepted
  exact conclusionEquality ▸ checked.property

/-- Every native derivation has an untrusted certificate which the executable
checker reconstructs as that derivation.  This is the completeness direction
needed to expose native derivability—not merely a hand-picked certificate
subset—as an exact checker authority. -/
theorem check_complete [DecidableEq Symbol] [DecidableEq Literal]
    {ordinary rows : Nat}
    {assumptions : List (Formula Symbol Literal ordinary rows)}
    {body : Formula Symbol Literal ordinary rows}
    (derivation : Derivation Symbol Literal assumptions body) :
    exists certificate : Certificate Symbol Literal ordinary rows,
      check assumptions certificate = some ⟨body, derivation⟩ := by
  induction derivation with
  | hypothesis member =>
      obtain ⟨index, inBounds, conclusion⟩ := List.getElem_of_mem member
      refine ⟨.hypothesis index, ?_⟩
      simp [check, inBounds, conclusion]
  | topIntroduction => exact ⟨.topIntroduction, rfl⟩
  | bottomElimination premise inductionHypothesis =>
      rename_i ordinaryDepth rowDepth result localAssumptions
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.bottomElimination result certificate, ?_⟩
      simp [check, checked]
  | andIntroduction leftProof rightProof leftIH rightIH =>
      obtain ⟨leftCertificate, leftChecked⟩ := leftIH
      obtain ⟨rightCertificate, rightChecked⟩ := rightIH
      refine ⟨.andIntroduction leftCertificate rightCertificate, ?_⟩
      simp [check, leftChecked, rightChecked]
  | andEliminationLeft premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.andEliminationLeft certificate, ?_⟩
      simp [check, checked]
  | andEliminationRight premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.andEliminationRight certificate, ?_⟩
      simp [check, checked]
  | orIntroductionLeft premise inductionHypothesis =>
      rename_i ordinaryDepth rowDepth left right localAssumptions
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.orIntroductionLeft right certificate, ?_⟩
      simp [check, checked]
  | orIntroductionRight premise inductionHypothesis =>
      rename_i ordinaryDepth rowDepth left right localAssumptions
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.orIntroductionRight right certificate, ?_⟩
      simp [check, checked]
  | orElimination disjunction leftBranch rightBranch disjunctionIH leftIH rightIH =>
      obtain ⟨disjunctionCertificate, disjunctionChecked⟩ := disjunctionIH
      obtain ⟨leftCertificate, leftChecked⟩ := leftIH
      obtain ⟨rightCertificate, rightChecked⟩ := rightIH
      refine ⟨.orElimination disjunctionCertificate leftCertificate
        rightCertificate, ?_⟩
      simp [check, disjunctionChecked, leftChecked, rightChecked]
  | implicationIntroduction premise inductionHypothesis =>
      rename_i ordinaryDepth rowDepth antecedent consequent localAssumptions
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.implicationIntroduction antecedent certificate, ?_⟩
      simp [check, checked]
  | implicationElimination functionProof argumentProof functionIH argumentIH =>
      obtain ⟨functionCertificate, functionChecked⟩ := functionIH
      obtain ⟨argumentCertificate, argumentChecked⟩ := argumentIH
      refine ⟨.implicationElimination functionCertificate argumentCertificate, ?_⟩
      simp [check, functionChecked, argumentChecked]
  | negationIntroduction premise inductionHypothesis =>
      rename_i ordinaryDepth rowDepth negatedBody localAssumptions
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.negationIntroduction negatedBody certificate, ?_⟩
      simp [check, checked]
  | negationElimination negativeProof positiveProof negativeIH positiveIH =>
      obtain ⟨negativeCertificate, negativeChecked⟩ := negativeIH
      obtain ⟨positiveCertificate, positiveChecked⟩ := positiveIH
      refine ⟨.negationElimination negativeCertificate positiveCertificate, ?_⟩
      simp [check, negativeChecked, positiveChecked]
  | iffIntroduction forwardProof reverseProof forwardIH reverseIH =>
      obtain ⟨forwardCertificate, forwardChecked⟩ := forwardIH
      obtain ⟨reverseCertificate, reverseChecked⟩ := reverseIH
      refine ⟨.iffIntroduction forwardCertificate reverseCertificate, ?_⟩
      simp [check, forwardChecked, reverseChecked]
  | iffEliminationLeft premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.iffEliminationLeft certificate, ?_⟩
      simp [check, checked]
  | iffEliminationRight premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.iffEliminationRight certificate, ?_⟩
      simp [check, checked]
  | allInSpineFromAllObject arguments premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.allInSpineFromAllObject arguments certificate, ?_⟩
      simp [check, checked]
  | allInSpineNilIntroduction body =>
      exact ⟨.allInSpineNilIntroduction body, rfl⟩
  | allInSpineTermIntroduction value rest valueProof restProof valueIH restIH =>
      obtain ⟨valueCertificate, valueChecked⟩ := valueIH
      obtain ⟨restCertificate, restChecked⟩ := restIH
      refine ⟨.allInSpineTermIntroduction value valueCertificate restCertificate, ?_⟩
      simp [check, valueChecked, restChecked]
  | allInSpineHeadElimination premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.allInSpineHeadElimination certificate, ?_⟩
      simp [check, checked]
  | allInSpineTermTailElimination premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.allInSpineTermTailElimination certificate, ?_⟩
      simp [check, checked]
  | allInSpineRowTailElimination premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.allInSpineRowTailElimination certificate, ?_⟩
      simp [check, checked]
  | allObjectIntroduction premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.allObjectIntroduction certificate, ?_⟩
      simp [check, checked]
  | allObjectElimination value premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.allObjectElimination value certificate, ?_⟩
      simp [check, checked]
  | someObjectIntroduction value premise inductionHypothesis =>
      rename_i ordinaryDepth rowDepth existentialBody localAssumptions
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.someObjectIntroduction existentialBody value certificate, ?_⟩
      simp [check, checked]
  | someObjectElimination existentialProof branchProof existentialIH branchIH =>
      rename_i ordinaryDepth rowDepth existentialBody result localAssumptions
      obtain ⟨existentialCertificate, existentialChecked⟩ := existentialIH
      obtain ⟨branchCertificate, branchChecked⟩ := branchIH
      refine ⟨.someObjectElimination result existentialCertificate branchCertificate, ?_⟩
      simp [check, existentialChecked, branchChecked]
  | allRowIntroduction premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.allRowIntroduction certificate, ?_⟩
      simp [check, checked]
  | allRowElimination arguments premise inductionHypothesis =>
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.allRowElimination arguments certificate, ?_⟩
      simp [check, checked]
  | someRowIntroduction arguments premise inductionHypothesis =>
      rename_i ordinaryDepth rowDepth existentialBody localAssumptions
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.someRowIntroduction existentialBody arguments certificate, ?_⟩
      simp [check, checked]
  | someRowElimination existentialProof branchProof existentialIH branchIH =>
      rename_i ordinaryDepth rowDepth existentialBody result localAssumptions
      obtain ⟨existentialCertificate, existentialChecked⟩ := existentialIH
      obtain ⟨branchCertificate, branchChecked⟩ := branchIH
      refine ⟨.someRowElimination result existentialCertificate branchCertificate, ?_⟩
      simp [check, existentialChecked, branchChecked]
  | equalityReflexivity value => exact ⟨.equalityReflexivity value, rfl⟩
  | equalitySubstitution context equalityProof contextProof equalityIH contextIH =>
      obtain ⟨equalityCertificate, equalityChecked⟩ := equalityIH
      obtain ⟨contextCertificate, contextChecked⟩ := contextIH
      refine ⟨.equalitySubstitution context equalityCertificate contextCertificate, ?_⟩
      simp [check, equalityChecked, contextChecked]
  | classicalContradiction premise inductionHypothesis =>
      rename_i ordinaryDepth rowDepth contradictedBody localAssumptions
      obtain ⟨certificate, checked⟩ := inductionHypothesis
      refine ⟨.classicalContradiction contradictedBody certificate, ?_⟩
      simp [check, checked]

/-- The executable checker is certificate-complete for native derivability. -/
theorem infer_complete [DecidableEq Symbol] [DecidableEq Literal]
    {ordinary rows : Nat}
    {assumptions : List (Formula Symbol Literal ordinary rows)}
    {body : Formula Symbol Literal ordinary rows}
    (derivation : Derivation Symbol Literal assumptions body) :
    exists certificate : Certificate Symbol Literal ordinary rows,
      infer assumptions certificate = some body := by
  obtain ⟨certificate, checked⟩ := check_complete derivation
  exact ⟨certificate, by simp [infer, checked]⟩

/-- An accepted closed certificate is valid in every native SUMO model. -/
theorem accepted_valid [DecidableEq Symbol] [DecidableEq Literal]
    {body : Sentence Symbol Literal}
    {certificate : Certificate Symbol Literal 0 0}
    (accepted : infer [] certificate = some body)
    (model : Model Symbol Literal) :
    model.ValidSentence body :=
  (infer_sound accepted).theorem_valid model

/-! ## Executable positive and negative controls -/

def implicationIdentity : Certificate String Unit 0 0 :=
  .implicationIntroduction SyntaxCanary.selfApplication (.hypothesis 0)

example : infer [] implicationIdentity =
    some (.implies SyntaxCanary.selfApplication SyntaxCanary.selfApplication) := rfl

example : infer ([] : List (Sentence String Unit)) (.hypothesis 0) = none := rfl

/-- A purported modus-ponens step whose first premise is truth rather than an
implication is rejected. -/
example : infer ([] : List (Sentence String Unit))
    (.implicationElimination .topIntroduction .topIntroduction) = none := rfl

private def eightArguments : Spine String Unit 0 0 :=
  Spine.ofTerms
    [(.constant "a"), (.constant "b"), (.constant "c"), (.constant "d"),
      (.constant "e"), (.constant "f"), (.constant "g"), (.constant "h")]

def eightArgumentTruth : Certificate String Unit 0 0 :=
  .allRowElimination eightArguments (.allRowIntroduction .topIntroduction)

example : infer [] eightArgumentTruth = some .top := rfl

private def twoArguments : Spine String Unit 0 0 :=
  Spine.ofTerms [(.constant "a"), (.constant "b")]

def everyExplicitMemberTruth : Certificate String Unit 0 0 :=
  .allInSpineTermIntroduction (.constant "a") .topIntroduction
    (.allInSpineTermIntroduction (.constant "b") .topIntroduction
      (.allInSpineNilIntroduction .top))

example : infer [] everyExplicitMemberTruth =
    some (.allInSpine twoArguments (.top : Formula String Unit 1 0)) := rfl

def everyMemberTruthFromUniversal : Certificate String Unit 0 0 :=
  .allInSpineFromAllObject twoArguments
    (.allObjectIntroduction .topIntroduction)

example : infer [] everyMemberTruthFromUniversal =
    some (.allInSpine twoArguments (.top : Formula String Unit 1 0)) := rfl

/-- An empty bounded universal has no head to eliminate. -/
example : infer ([] : List (Sentence String Unit))
    (.allInSpineHeadElimination (.allInSpineNilIntroduction .top)) = none := rfl

end Certificate

end Mettapedia.Languages.SUMO.Native
