import Mettapedia.Languages.Metamath.InferenceNormalFoldReflection

/-!
# Operational provability of native normal Metamath proofs

This module closes the forward endpoint from the generated native proof layer
to `mm-lean4`'s operational `Spec.Provable`.  The endpoint is deliberately
about the runtime database and its ambient `db.frame`: the proof executes with
`DB.stepNormal` in that database, and `Kernel.fold_maintains_provable` supplies
provability in the corresponding operational database and ambient frame.

Positive example: an exact accepted normal-label fold from an empty stack is
operationally provable, and therefore so is every reflected native `Proves`
derivation under the same projection and runtime well-formedness premises.

Negative boundary: this is forward soundness.  It neither reconstructs a
native derivation from arbitrary `Spec.Provable` evidence nor identifies the
ambient runtime frame with a separately projected caller frame.
-/

namespace Mettapedia.Languages.Metamath.InferenceNormalProvabilitySoundness

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceNormalFoldReflection

/-! ## Runtime gates retained by projection -/

/-- Successful live-prefix projection retains the two runtime soundness gates
required by `Kernel.fold_maintains_provable`: no stored error and a
propositionally well-formed database. -/
theorem projectPrefix?_soundnessGates
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectPrefix? db = some projection) :
    db.error? = none ∧ Metamath.WF.WellFormedDB db := by
  unfold projectPrefix? at hproject
  simp only [bind, Option.bind_eq_some_iff] at hproject
  obtain ⟨_guardError, herror, _guardWellFormed, hwellFormed,
    _guardDV, _hdv, _guardEmbedded, _hembedded, _guardDeclarations,
    _hdeclarations, activeHypotheses, _hactive, _guardFrame, _hframe,
    assertions, _hassertions, _guardProjection, _hprojectionValid,
    hprojection⟩ := hproject
  cases hprojection
  have herrorIsNone : db.error?.isNone = true := by
    unfold guard at herror
    split at herror
    · assumption
    · simp at herror
  have hwellFormedBool : db.wellFormed? = true := by
    unfold guard at hwellFormed
    split at hwellFormed
    · assumption
    · simp at hwellFormed
  constructor
  · cases herrorValue : db.error? with
    | none => rfl
    | some error => simp [herrorValue] at herrorIsNone
  · exact Metamath.WF.wellFormedDB_of_wellFormed? hwellFormedBool

/-! ## Accepted normal folds -/

/-- An exact successful normal-label fold from an empty runtime stack is
provable in the supplied operational image of the same runtime database and
its ambient `db.frame`.

The operational frame premise mentions `db.frame` literally.  No equality to
`projection.callerFrame` is needed or assumed. -/
theorem acceptedNormalFold_to_operationalProvable
    (db : RuntimeDB) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula) (labels : List String)
    (Γ : OperationalDatabase) (fr : OperationalFrame)
    (herror : db.error? = none)
    (hwellFormed : Metamath.WF.WellFormedDB db)
    (hdatabase : Metamath.Kernel.toDatabase db = some Γ)
    (hframe : Metamath.Kernel.toFrame db db.frame = some fr)
    (hbaseStack : base.stack = #[])
    (hfold :
      labels.foldlM (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime)) :
    OperationalProvable Γ fr
      (Metamath.Kernel.toExpr formula.toRuntime) := by
  have hfoldArray :
      labels.toArray.foldlM
          (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime) := by
    rw [← Array.foldlM_toList, List.toList_toArray]
    exact hfold
  have hfinalSize :
      (base.push formula.toRuntime).stack.size = 1 := by
    simp [Metamath.Verify.ProofState.push, hbaseStack]
  have hfinalFormula :
      (base.push formula.toRuntime).stack[0]? =
        some formula.toRuntime := by
    simp [Metamath.Verify.ProofState.push, hbaseStack]
  exact Metamath.Kernel.fold_maintains_provable
    db labels.toArray base (base.push formula.toRuntime) Γ fr
      formula.toRuntime herror hwellFormed hdatabase hframe hwellFormed.1
      hfoldArray hbaseStack hfinalSize hfinalFormula

/-- Existential image form of `acceptedNormalFold_to_operationalProvable`.
Database totality and ambient-frame conversion are derived from the runtime
kernel; the returned equalities record the exact operational images used. -/
theorem acceptedNormalFold_to_exists_operationalProvable
    (db : RuntimeDB) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula) (labels : List String)
    (herror : db.error? = none)
    (hwellFormed : Metamath.WF.WellFormedDB db)
    (hbaseStack : base.stack = #[])
    (hfold :
      labels.foldlM (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime)) :
    ∃ (Γ : OperationalDatabase) (fr : OperationalFrame),
      Metamath.Kernel.toDatabase db = some Γ ∧
      Metamath.Kernel.toFrame db db.frame = some fr ∧
      OperationalProvable Γ fr
        (Metamath.Kernel.toExpr formula.toRuntime) := by
  obtain ⟨Γ, hdatabase⟩ :
      ∃ Γ : OperationalDatabase,
        Metamath.Kernel.toDatabase db = some Γ := by
    unfold Metamath.Kernel.toDatabase
    exact ⟨_, rfl⟩
  obtain ⟨fr, hframe⟩ :=
    Metamath.Kernel.toFrame_some_of_wfFrame db hwellFormed.1
  exact ⟨Γ, fr, hdatabase, hframe,
    acceptedNormalFold_to_operationalProvable db base formula labels Γ fr
      herror hwellFormed hdatabase hframe hbaseStack hfold⟩

/-! ## Generated and native proof endpoints -/

/-- A source-pinned generated proof tree is operationally provable after its
authored labels execute in the same runtime database. -/
theorem generatedProvesTree_to_operationalProvable
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (tree : GeneratedProvesTree projection target formula)
    (Γ : OperationalDatabase) (fr : OperationalFrame)
    (hprojection : presentationOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hdatabase : Metamath.Kernel.toDatabase db = some Γ)
    (hframe : Metamath.Kernel.toFrame db db.frame = some fr)
    (hbaseStack : base.stack = #[]) :
    OperationalProvable Γ fr
      (Metamath.Kernel.toExpr formula.toRuntime) := by
  have hfold :
      tree.labels.foldlM
          (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime) := by
    apply (normalFold_accepts_iff_exactGeneratedTree db projection target base
      formula tree.labels hprojection hproject hbaseStack).2
    exact ⟨⟨tree, rfl⟩⟩
  obtain ⟨herror, hwellFormed⟩ :=
    projectPrefix?_soundnessGates db projection hproject
  exact acceptedNormalFold_to_operationalProvable db base formula tree.labels
    Γ fr herror hwellFormed hdatabase hframe hbaseStack hfold

/-- Every native generated `Proves` derivation is sound for upstream
`Metamath.Spec.Provable`, using the exact reflected tree and its accepted
postfix labels. -/
theorem provesDerivation_to_operationalProvable
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (Γ : OperationalDatabase) (fr : OperationalFrame)
    (hprojection : presentationOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hdatabase : Metamath.Kernel.toDatabase db = some Γ)
    (hframe : Metamath.Kernel.toFrame db db.frame = some fr)
    (hbaseStack : base.stack = #[])
    (derivation : Derivation target (proves (encodeFormula formula))) :
    OperationalProvable Γ fr
      (Metamath.Kernel.toExpr formula.toRuntime) := by
  rcases provesDerivation_reflectsAcceptedNormalLabels db projection target
      base formula hprojection hproject hbaseStack derivation with
    ⟨tree, _herasure, hfold⟩
  obtain ⟨herror, hwellFormed⟩ :=
    projectPrefix?_soundnessGates db projection hproject
  exact acceptedNormalFold_to_operationalProvable db base formula tree.labels
    Γ fr herror hwellFormed hdatabase hframe hbaseStack hfold

/-- Existential same-database endpoint for a native generated `Proves`
derivation.  The witnesses expose the exact operational database and ambient
frame produced by the verified runtime bridge. -/
theorem provesDerivation_to_exists_operationalProvable
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hprojection : presentationOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[])
    (derivation : Derivation target (proves (encodeFormula formula))) :
    ∃ (Γ : OperationalDatabase) (fr : OperationalFrame),
      Metamath.Kernel.toDatabase db = some Γ ∧
      Metamath.Kernel.toFrame db db.frame = some fr ∧
      OperationalProvable Γ fr
        (Metamath.Kernel.toExpr formula.toRuntime) := by
  rcases provesDerivation_reflectsAcceptedNormalLabels db projection target
      base formula hprojection hproject hbaseStack derivation with
    ⟨tree, _herasure, hfold⟩
  obtain ⟨herror, hwellFormed⟩ :=
    projectPrefix?_soundnessGates db projection hproject
  exact acceptedNormalFold_to_exists_operationalProvable db base formula
    tree.labels herror hwellFormed hbaseStack hfold

/-- Native type inhabitation implies upstream operational provability.  This
is the proposition-level endpoint: it forgets which native derivation was
checked, while retaining the exact same-database image equalities. -/
theorem nonempty_provesDerivation_to_exists_operationalProvable
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hprojection : presentationOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[])
    (hnative :
      Nonempty (Derivation target (proves (encodeFormula formula)))) :
    ∃ (Γ : OperationalDatabase) (fr : OperationalFrame),
      Metamath.Kernel.toDatabase db = some Γ ∧
      Metamath.Kernel.toFrame db db.frame = some fr ∧
      OperationalProvable Γ fr
        (Metamath.Kernel.toExpr formula.toRuntime) := by
  rcases hnative with ⟨derivation⟩
  exact provesDerivation_to_exists_operationalProvable db projection target
    base formula hprojection hproject hbaseStack derivation

/-! ## Negative execution boundary -/

/-- Empty submitted evidence cannot reach the operational endpoint through a
successful singleton normal fold from an empty stack. -/
theorem emptyLabels_not_acceptedForOperationalEndpoint
    (db : RuntimeDB) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hbaseStack : base.stack = #[]) :
    ([] : List String).foldlM
        (fun state label => db.stepNormal state label) base ≠
      .ok (base.push formula.toRuntime) := by
  intro hfold
  change Except.ok base = Except.ok (base.push formula.toRuntime) at hfold
  have hstate : base = base.push formula.toRuntime := by
    exact Except.ok.inj hfold
  have hstack := congrArg (fun state : RuntimeProofState => state.stack) hstate
  rw [hbaseStack] at hstack
  simp [Metamath.Verify.ProofState.push] at hstack

end Mettapedia.Languages.Metamath.InferenceNormalProvabilitySoundness
