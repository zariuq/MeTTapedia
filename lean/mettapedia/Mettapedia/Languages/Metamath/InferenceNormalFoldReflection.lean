import Mettapedia.Languages.Metamath.InferenceNormalStepReflection
import Mettapedia.Languages.Metamath.InferenceGeneratedProvesReflection

open Mettapedia.GSLT.LanguageDef

/-!
# Proof-relevant reflection of normal Metamath proof folds

The one-step native stack certificate extends to arbitrary left-to-right normal
proof folds.  For an empty initial stack, successful execution to one formula
is equivalent to a retained generated proof tree whose authored postfix labels
are exactly the submitted labels.

Combining that exact-label theorem with global reflection of arbitrary generic
`Proves` derivations yields the projection-conditional correspondence between
native provability and existence of some accepted normal label list.  This
module does not import parser provenance or infer chronology from a database.
-/

namespace Mettapedia.Languages.Metamath.InferenceNormalFoldReflection

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceNormalStepReflection

/-! ## Exact empty-stack seed -/

/-- Any supplied runtime state whose stack is empty is its own fixed base for
an exact empty native stack certificate. -/
def NativeStackCertificate.of_stack_eq_empty
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (state : RuntimeProofState)
    (hstack : state.stack = #[]) :
    NativeStackCertificate db projection target state [] state :=
  { formulas := []
    forest := .nil
    labels_eq := rfl
    state_eq := by
      cases state
      simp_all [runtimeFormulaArray]
    stackRespects := by
      intro index hindex
      rw [hstack] at hindex
      simp at hindex }

/-! ## Arbitrary left-to-right fold preservation -/

noncomputable section

/-- Extend an exact native stack certificate across an arbitrary successful
left-to-right normal-label fold.  The output index retains the already
processed prefix followed by the submitted labels in their original order.
Noncomputability is inherited from the one-step selection of each new local
witness; the retained forest from every preceding step is threaded directly. -/
def NativeStackCertificate.foldlM
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedCalculusLanguageDef} {base state result : RuntimeProofState}
    {processedLabels : List String}
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (certificate : NativeStackCertificate db projection target base
      processedLabels state) :
    (submittedLabels : List String) →
    submittedLabels.foldlM
        (fun current label => db.stepNormal current label) state = .ok result →
      NativeStackCertificate db projection target base
        (processedLabels ++ submittedLabels) result
  | [], hfold => by
      have hresult : result = state := by
        simpa using Except.ok.inj hfold |>.symm
      subst result
      simpa using certificate
  | label :: submittedLabels, hfold => by
      cases hstep : db.stepNormal state label with
      | error error =>
          simp only [List.foldlM_cons, hstep, bind, Except.bind] at hfold
          cases hfold
      | ok next =>
          have nextCertificate := certificate.stepNormal label hprojection
            hproject hstep
          have htail :
              submittedLabels.foldlM
                  (fun current nextLabel => db.stepNormal current nextLabel)
                  next = .ok result := by
            simpa only [List.foldlM_cons, hstep, bind, Except.bind] using hfold
          have tailCertificate := NativeStackCertificate.foldlM hprojection
            hproject nextCertificate submittedLabels htail
          simpa [List.append_assoc] using tailCertificate

end

/-! ## Runtime-image injectivity and singleton extraction -/

/-- The ordered runtime array loses no information from a list of canonical
constant-headed formulas. -/
theorem runtimeFormulaArray_injective :
    Function.Injective runtimeFormulaArray := by
  intro left right heq
  have hmaps :
      left.map ConstantHeadedFormula.toRuntime =
        right.map ConstantHeadedFormula.toRuntime := by
    have hlists := congrArg Array.toList heq
    simpa [runtimeFormulaArray] using hlists
  clear heq
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at hmaps
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp at hmaps
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at hmaps
          have hhead : leftHead = rightHead :=
            ConstantHeadedFormula.toRuntime_injective hmaps.1
          subst rightHead
          exact congrArg (List.cons leftHead) (ih hmaps.2)

/-- A certificate whose final runtime stack is one formula contains exactly
one retained source-pinned tree for that formula, with the exact processed
label list. -/
def NativeStackCertificate.extractSingletonTree
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedCalculusLanguageDef} {base state : RuntimeProofState}
    {processedLabels : List String}
    (certificate : NativeStackCertificate db projection target base
      processedLabels state)
    (formula : ConstantHeadedFormula)
    (hstack : state.stack = #[formula.toRuntime]) :
    { tree : GeneratedProvesTree projection target formula //
      tree.labels = processedLabels } := by
  have hformulas : certificate.formulas = [formula] := by
    apply runtimeFormulaArray_injective
    calc
      runtimeFormulaArray certificate.formulas = state.stack :=
        certificate.stack_eq.symm
      _ = #[formula.toRuntime] := hstack
      _ = runtimeFormulaArray [formula] := by rfl
  let singletonForest :=
    castGeneratedProvesForestIndex hformulas certificate.forest
  let tree := singletonForest.singletonTree
  refine ⟨tree, ?_⟩
  calc
    tree.labels = singletonForest.labels := by
      rw [← singletonForest.singleton_reconstruct]
      simp [GeneratedProvesForest.labels, tree]
    _ = certificate.forest.labels :=
      labels_castGeneratedProvesForestIndex hformulas certificate.forest
    _ = processedLabels := certificate.labels_eq

/-! ## Exact accepted-label theorem -/

/-- Exact normal-proof endpoint for an empty base stack: the submitted labels
are accepted with singleton result exactly when they are the authored postfix
labels of a generated proof tree for that formula. -/
theorem normalFold_accepts_iff_exactGeneratedTree
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula) (labels : List String)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[]) :
    labels.foldlM (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime) ↔
      Nonempty
        { tree : GeneratedProvesTree projection target formula //
          tree.labels = labels } := by
  constructor
  · intro hfold
    let seed := NativeStackCertificate.of_stack_eq_empty db projection target
      base hbaseStack
    have finalCertificate := NativeStackCertificate.foldlM hprojection hproject
      seed labels hfold
    have hfinalStack :
        (base.push formula.toRuntime).stack = #[formula.toRuntime] := by
      simp [Metamath.Verify.ProofState.push, hbaseStack]
    exact ⟨NativeStackCertificate.extractSingletonTree finalCertificate
      formula hfinalStack⟩
  · rintro ⟨⟨tree, hlabels⟩⟩
    have hstackRespects :
        Metamath.Kernel.StackRespectsFrame db db.frame base.stack := by
      intro index hindex
      rw [hbaseStack] at hindex
      simp at hindex
    rw [← hlabels]
    exact (tree.execute db hprojection hproject base hstackRespects).1

/-! ## Native provability and existence of accepted normal labels -/

/-- An arbitrary native `Proves` derivation supplies an exact reflected tree,
the same raw proof erasure, and acceptance of precisely that tree's authored
normal labels from an empty base stack. -/
theorem provesDerivation_reflectsAcceptedNormalLabels
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[])
    (derivation : Derivation target (proves (encodeFormula formula))) :
    ∃ tree : GeneratedProvesTree projection target formula,
      derivation.erase = (tree.toDerivation hprojection).erase ∧
      tree.labels.foldlM
          (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime) := by
  rcases provesDerivation_reflectsGeneratedTree hprojection derivation with
    ⟨reflectedFormula, hencoding, tree, herase⟩
  have hformula : formula = reflectedFormula :=
    encodeFormula_injective hencoding
  subst reflectedFormula
  refine ⟨tree, herase, ?_⟩
  apply (normalFold_accepts_iff_exactGeneratedTree db projection target base
    formula tree.labels hprojection hproject hbaseStack).2
  exact ⟨⟨tree, rfl⟩⟩

/-- Projection-conditional native provability is equivalent to existence of
some accepted normal label list.  The preceding exact theorem separately
retains which generated tree owns each accepted list. -/
theorem nonempty_provesDerivation_iff_exists_acceptedNormalLabels
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[]) :
    Nonempty (Derivation target (proves (encodeFormula formula))) ↔
      ∃ labels : List String,
        labels.foldlM (fun state label => db.stepNormal state label) base =
          .ok (base.push formula.toRuntime) := by
  constructor
  · rintro ⟨derivation⟩
    rcases provesDerivation_reflectsAcceptedNormalLabels db projection target
        base formula hprojection hproject hbaseStack derivation with
      ⟨tree, _herase, haccepts⟩
    exact ⟨tree.labels, haccepts⟩
  · rintro ⟨labels, haccepts⟩
    rcases (normalFold_accepts_iff_exactGeneratedTree db projection target base
        formula labels hprojection hproject hbaseStack).1 haccepts with
      ⟨⟨tree, _hlabels⟩⟩
    exact ⟨tree.toDerivation hprojection⟩

/-! ## Positive and negative boundaries -/

example (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (tree : GeneratedProvesTree projection target formula)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[]) :
    tree.labels.foldlM (fun state label => db.stepNormal state label) base =
      .ok (base.push formula.toRuntime) := by
  apply (normalFold_accepts_iff_exactGeneratedTree db projection target base
    formula tree.labels hprojection hproject hbaseStack).2
  exact ⟨⟨tree, rfl⟩⟩

/-- A generated tree's exact normal fold cannot produce an unequal complete
runtime state. -/
theorem normalFold_ne_wrong_final_state
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base wrong : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (tree : GeneratedProvesTree projection target formula)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[])
    (hne : wrong ≠ base.push formula.toRuntime) :
    tree.labels.foldlM (fun state label => db.stepNormal state label) base ≠
      .ok wrong := by
  have hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame base.stack := by
    intro index hindex
    rw [hbaseStack] at hindex
    simp at hindex
  exact tree.execute_ne_wrong_state db hprojection hproject base wrong
    hstackRespects hne

/-- No formula proof can be accepted from an empty base stack using an empty
normal label list. -/
theorem normalFold_empty_labels_ne_formula
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[]) :
    ([] : List String).foldlM
        (fun state label => db.stepNormal state label) base ≠
      .ok (base.push formula.toRuntime) := by
  intro haccepts
  rcases (normalFold_accepts_iff_exactGeneratedTree db projection target base
      formula [] hprojection hproject hbaseStack).1 haccepts with
    ⟨⟨tree, hlabels⟩⟩
  exact tree.labels_ne_nil hlabels

end Mettapedia.Languages.Metamath.InferenceNormalFoldReflection
