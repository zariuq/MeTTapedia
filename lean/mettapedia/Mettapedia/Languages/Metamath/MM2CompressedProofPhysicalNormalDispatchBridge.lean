import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoffCaptureFrame
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchWitness
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalSupportHeadFaithfulness

/-!
# Physical compressed-to-normal dispatch bridge

The compact assertion handoff activates the finite normal-verifier loader by
one rule-scoped MORK transaction.  This module isolates that transaction from
the larger assertion trace and records its exact input and output interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalDispatchBridge

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- The owner-bound request consumed by the compact-to-normal bridge. -/
def normalDispatchBridgeReloadRow (proofOwner : Atom) : Atom :=
  .expression [.symbol "mm-reload-compressed-normal-dispatch", proofOwner]

/-- The first finite-loader cursor produced by the bridge. -/
def normalDispatchBridgeInitialLoadingRow (proofOwner : Atom) : Atom :=
  .expression
    [.symbol "mm-compressed-normal-handoff-loading", proofOwner, natAtom 0]

/-- The complete canonical read slice for one bridge transaction. -/
def normalDispatchBridgeSlice (proofOwner : Atom) : List Atom :=
  [compressedNormalDispatchBridgeRule,
   normalDispatchBridgeReloadRow proofOwner,
   compressedNormalHandoffLoaderCaptureRow,
   compressedNormalHandoffFinishCaptureRow]

theorem normalDispatchBridgeSlice_nodup (proofOwner : Atom) :
    (normalDispatchBridgeSlice proofOwner).Nodup := by
  simp [normalDispatchBridgeSlice, normalDispatchBridgeReloadRow,
    compressedNormalHandoffLoaderCaptureRow,
    compressedNormalHandoffFinishCaptureRow,
    compressedNormalDispatchBridgeRule]

private theorem normalDispatchBridge_key_ne_reload (proofOwner : Atom) :
    morkSupportKey compressedNormalDispatchBridgeRule ≠
      morkSupportKey (normalDispatchBridgeReloadRow proofOwner) := by
  unfold compressedNormalDispatchBridgeRule normalDispatchBridgeReloadRow
  apply morkSupportKey_expression_symbol_head_ne <;> norm_num <;> decide

private theorem normalDispatchBridge_key_ne_loader :
    morkSupportKey compressedNormalDispatchBridgeRule ≠
      morkSupportKey compressedNormalHandoffLoaderCaptureRow := by
  unfold compressedNormalDispatchBridgeRule
    compressedNormalHandoffLoaderCaptureRow
  apply morkSupportKey_expression_symbol_head_ne <;> norm_num <;> decide

private theorem normalDispatchBridge_key_ne_finish :
    morkSupportKey compressedNormalDispatchBridgeRule ≠
      morkSupportKey compressedNormalHandoffFinishCaptureRow := by
  unfold compressedNormalDispatchBridgeRule
    compressedNormalHandoffFinishCaptureRow
  apply morkSupportKey_expression_symbol_head_ne <;> norm_num <;> decide

private theorem normalDispatchReload_key_ne_loader (proofOwner : Atom) :
    morkSupportKey (normalDispatchBridgeReloadRow proofOwner) ≠
      morkSupportKey compressedNormalHandoffLoaderCaptureRow := by
  unfold normalDispatchBridgeReloadRow compressedNormalHandoffLoaderCaptureRow
  apply morkSupportKey_expression_symbol_head_ne <;> norm_num <;> decide

private theorem normalDispatchReload_key_ne_finish (proofOwner : Atom) :
    morkSupportKey (normalDispatchBridgeReloadRow proofOwner) ≠
      morkSupportKey compressedNormalHandoffFinishCaptureRow := by
  unfold normalDispatchBridgeReloadRow compressedNormalHandoffFinishCaptureRow
  apply morkSupportKey_expression_symbol_head_ne <;> norm_num <;> decide

private theorem normalDispatchLoader_key_ne_finish :
    morkSupportKey compressedNormalHandoffLoaderCaptureRow ≠
      morkSupportKey compressedNormalHandoffFinishCaptureRow := by
  unfold compressedNormalHandoffLoaderCaptureRow
    compressedNormalHandoffFinishCaptureRow
  apply morkSupportKey_expression_symbol_head_ne <;> norm_num <;> decide

/-- The canonical bridge slice is duplicate-free at MORK's physical compact
identity, not merely at nominal atom equality. -/
theorem normalDispatchBridgeSlice_mork_nodup (proofOwner : Atom) :
    MorkSupportNodup (normalDispatchBridgeSlice proofOwner) := by
  unfold MorkSupportNodup normalDispatchBridgeSlice
  simp only [List.map_cons, List.map_nil, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨?_, ?_⟩
  · intro equal
    rcases equal with equal | equal | equal
    · exact normalDispatchBridge_key_ne_reload proofOwner equal
    · exact normalDispatchBridge_key_ne_loader equal
    · exact normalDispatchBridge_key_ne_finish equal
  · refine ⟨?_, ?_⟩
    · intro equal
      rcases equal with equal | equal
      · exact normalDispatchReload_key_ne_loader proofOwner equal
      · exact normalDispatchReload_key_ne_finish proofOwner equal
    · refine ⟨?_, ?_⟩
      · exact normalDispatchLoader_key_ne_finish
      · simp

/-- The unique source-level substitution carried by the canonical bridge. -/
def normalDispatchBridgeSubstitution (proofOwner : Atom) : Subst :=
  [("normal-handoff-finish-rule", compressedNormalHandoffFinishRule),
   ("normal-handoff-loader-rule", compressedNormalHandoffLoadRule),
   ("proof-owner", proofOwner),
   ("normal-bridge-output", outputSurface compressedNormalDispatchBridgeSinks),
   ("normal-bridge-input", inputSurface compressedNormalDispatchBridgePatterns)]

/-- Exact outputs reconstructed by the compatible bridge matcher. -/
def ExactNormalDispatchBridge (proofOwner : Atom) (space : List Atom) : Prop :=
  ∃ substitution ∈
      (cmatchInputSpec []
        (compressedNormalDispatchBridgeRule ::
          space.erase compressedNormalDispatchBridgeRule)
        compressedNormalDispatchBridgeDirective.rule.input).map Prod.fst,
    instantiateTemplateAtom? substitution
          (.var "normal-handoff-loader-rule") =
        some compressedNormalHandoffLoadRule ∧
      instantiateTemplateAtom? substitution
          (.var "normal-handoff-finish-rule") =
        some compressedNormalHandoffFinishRule ∧
      instantiateTemplateAtom? substitution
          compressedNormalHandoffInitialLoadingTemplate =
        some (normalDispatchBridgeInitialLoadingRow proofOwner)

/-- The four canonical rows determine one exact bridge substitution. -/
theorem canonical_exact_normal_dispatch_bridge (proofOwner : Atom) :
    ExactNormalDispatchBridge proofOwner
      (normalDispatchBridgeSlice proofOwner) := by
  let bridgeInput := inputSurface compressedNormalDispatchBridgePatterns
  let bridgeOutput := outputSurface compressedNormalDispatchBridgeSinks
  let afterSelf : Subst :=
    [("normal-bridge-output", bridgeOutput),
     ("normal-bridge-input", bridgeInput)]
  let afterReload : Subst := ("proof-owner", proofOwner) :: afterSelf
  let afterLoader : Subst :=
    ("normal-handoff-loader-rule", compressedNormalHandoffLoadRule) ::
      afterReload
  let final : Subst :=
    ("normal-handoff-finish-rule", compressedNormalHandoffFinishRule) ::
      afterLoader
  have selfMatch :
      cmatchAtom []
          (.expression
            [.symbol "exec",
             .expression
               [.symbol "31", .symbol "mm-compressed-normal-dispatch-bridge"],
             .var "normal-bridge-input", .var "normal-bridge-output"])
          compressedNormalDispatchBridgeRule = some afterSelf := by
    rfl
  have reloadMatch :
      cmatchAtom afterSelf compressedAssertionNormalReloadRequest
          (normalDispatchBridgeReloadRow proofOwner) = some afterReload := by
    rfl
  have loaderMatch :
      cmatchAtom afterReload compressedNormalHandoffLoaderCaptureTemplate
          compressedNormalHandoffLoaderCaptureRow = some afterLoader := by
    rfl
  have finishMatch :
      cmatchAtom afterLoader compressedNormalHandoffFinishCaptureTemplate
          compressedNormalHandoffFinishCaptureRow = some final := by
    rfl
  have path : MatchWitnessPath (normalDispatchBridgeSlice proofOwner)
      compressedNormalDispatchBridgePatterns [] [] final
        [compressedNormalHandoffFinishCaptureRow,
         compressedNormalHandoffLoaderCaptureRow,
         normalDispatchBridgeReloadRow proofOwner,
         compressedNormalDispatchBridgeRule] := by
    rw [show compressedNormalDispatchBridgePatterns =
      [.expression
        [.symbol "exec",
         .expression
           [.symbol "31", .symbol "mm-compressed-normal-dispatch-bridge"],
         .var "normal-bridge-input", .var "normal-bridge-output"],
       compressedAssertionNormalReloadRequest,
       compressedNormalHandoffLoaderCaptureTemplate,
       compressedNormalHandoffFinishCaptureTemplate] by rfl]
    exact .cons (by simp [normalDispatchBridgeSlice]) selfMatch
      (.cons (by simp [normalDispatchBridgeSlice]) reloadMatch
        (.cons (by simp [normalDispatchBridgeSlice]) loaderMatch
          (.cons (by simp [normalDispatchBridgeSlice]) finishMatch
            (.nil _ _))))
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · have member := matchWitnessPath_mem_cmatchInputSpec path
    change final ∈
      (cmatchInputSpec []
        (compressedNormalDispatchBridgeRule ::
          (normalDispatchBridgeSlice proofOwner).erase
            compressedNormalDispatchBridgeRule)
        (.compat (mkPattern compressedNormalDispatchBridgePatterns))).map
          Prod.fst
    simpa [normalDispatchBridgeSlice, mkPattern] using member
  · rfl
  · rfl
  · rfl

private theorem normalDispatchBridge_reflective_rows_exact
    (proofOwner : Atom) :
    (cmatchInputSpec []
      (compressedNormalDispatchBridgeRule ::
        (normalDispatchBridgeSlice proofOwner).erase
          compressedNormalDispatchBridgeRule)
      compressedNormalDispatchBridgeDirective.rule.input).map Prod.fst =
        [normalDispatchBridgeSubstitution proofOwner] := by
  rfl

/-- Any live frame containing the four exact bridge rows retains the canonical
positive bridge witness.  Extra rows may add matcher alternatives, but cannot
erase this source-indexed transaction. -/
theorem exact_normal_dispatch_bridge_of_live_rows
    (proofOwner : Atom) (space : List Atom)
    (reloadPresent : normalDispatchBridgeReloadRow proofOwner ∈ space)
    (loaderPresent : compressedNormalHandoffLoaderCaptureRow ∈ space)
    (finishPresent : compressedNormalHandoffFinishCaptureRow ∈ space) :
    ExactNormalDispatchBridge proofOwner space := by
  obtain ⟨substitution, canonicalMember, loader, finish, loading⟩ :=
    canonical_exact_normal_dispatch_bridge proofOwner
  refine ⟨substitution, ?_, loader, finish, loading⟩
  apply Conformance.Computable.cmatchInputSpec_compat_mono []
    (compressedNormalDispatchBridgeRule ::
      (normalDispatchBridgeSlice proofOwner).erase
        compressedNormalDispatchBridgeRule)
    (compressedNormalDispatchBridgeRule ::
      space.erase compressedNormalDispatchBridgeRule)
    compressedNormalDispatchBridgePatterns ?_ canonicalMember
  intro atom atomMember
  simp only [List.mem_cons] at atomMember ⊢
  rcases atomMember with rfl | atomMember
  · exact Or.inl rfl
  · right
    have original := List.mem_of_mem_erase atomMember
    simp only [normalDispatchBridgeSlice, List.mem_cons, List.not_mem_nil,
      or_false] at original
    rcases original with rfl | rfl | rfl | rfl
    · simp [normalDispatchBridgeSlice, normalDispatchBridgeReloadRow,
        compressedNormalHandoffLoaderCaptureRow,
        compressedNormalHandoffFinishCaptureRow,
        compressedNormalDispatchBridgeRule] at atomMember
    · apply (List.mem_erase_of_ne ?_).2 reloadPresent
      simp [normalDispatchBridgeReloadRow,
        compressedNormalDispatchBridgeRule]
    · apply (List.mem_erase_of_ne ?_).2 loaderPresent
      simp [compressedNormalHandoffLoaderCaptureRow,
        compressedNormalDispatchBridgeRule]
    · apply (List.mem_erase_of_ne ?_).2 finishPresent
      simp [compressedNormalHandoffFinishCaptureRow,
        compressedNormalDispatchBridgeRule]

/-! ## Physical compact-key matcher -/

/-- Matcher substitutions enumerated by the actual compact-key bridge firing. -/
def physicalNormalDispatchBridgeMatcherRows (space : List Atom) : List Subst :=
  let live :=
    morkEraseSupport space compressedNormalDispatchBridgeDirective.atom
  let read :=
    morkInsertSupport live compressedNormalDispatchBridgeDirective.atom
  ((cMatchInputSpecMork [] read
      compressedNormalDispatchBridgeDirective.rule.input).filter fun
      (substitution, _) =>
        matchSourceGuards substitution
          compressedNormalDispatchBridgeDirective.rule.guards).map Prod.fst

theorem compressedNormalDispatchBridgeDirective_guards_exact :
    compressedNormalDispatchBridgeDirective.rule.guards = [] := by
  rfl

private theorem instantiateRuleTemplateAtom?_of_reflective
    (input : InputSpec) {substitution : Subst} {template candidate : Atom}
    (instantiated : instantiateTemplateAtom? substitution template =
      some candidate) :
    instantiateRuleTemplateAtom? input substitution template =
      some candidate := by
  cases covered : templateCovered substitution template with
  | false => simp [instantiateTemplateAtom?, covered] at instantiated
  | true =>
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?_of_covered
        input substitution template covered]
      exact instantiated

theorem physical_normal_dispatch_bridge_live_eq
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedNormalDispatchBridgeDirective.atom ∈ space) :
    morkEraseSupport space compressedNormalDispatchBridgeDirective.atom =
      space.erase compressedNormalDispatchBridgeDirective.atom :=
  morkEraseSupport_eq_erase_of_mem space
    compressedNormalDispatchBridgeDirective.atom listNodup morkNodup
      directivePresent

theorem physical_normal_dispatch_bridge_read_perm
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedNormalDispatchBridgeDirective.atom ∈ space) :
    (morkInsertSupport
        (morkEraseSupport space compressedNormalDispatchBridgeDirective.atom)
        compressedNormalDispatchBridgeDirective.atom).Perm
      (compressedNormalDispatchBridgeDirective.atom ::
        space.erase compressedNormalDispatchBridgeDirective.atom) := by
  rw [physical_normal_dispatch_bridge_live_eq listNodup morkNodup
    directivePresent]
  have absent : morkSupportContains
      (space.erase compressedNormalDispatchBridgeDirective.atom)
        compressedNormalDispatchBridgeDirective.atom = false := by
    rw [← physical_normal_dispatch_bridge_live_eq listNodup morkNodup
      directivePresent]
    exact morkSupportContains_morkEraseSupport_self space
      compressedNormalDispatchBridgeDirective.atom
  unfold morkInsertSupport
  rw [absent]
  exact List.perm_append_singleton compressedNormalDispatchBridgeDirective.atom
    (space.erase compressedNormalDispatchBridgeDirective.atom)

theorem physical_normal_dispatch_bridge_matcher_mem_iff
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedNormalDispatchBridgeDirective.atom ∈ space)
    (substitution : Subst) (consumed : List Atom) :
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space
              compressedNormalDispatchBridgeDirective.atom)
            compressedNormalDispatchBridgeDirective.atom)
          compressedNormalDispatchBridgeDirective.rule.input ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (compressedNormalDispatchBridgeDirective.atom ::
            space.erase compressedNormalDispatchBridgeDirective.atom)
          compressedNormalDispatchBridgeDirective.rule.input := by
  change
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space
              compressedNormalDispatchBridgeDirective.atom)
            compressedNormalDispatchBridgeDirective.atom)
          (.compat (mkPattern compressedNormalDispatchBridgePatterns)) ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (compressedNormalDispatchBridgeDirective.atom ::
            space.erase compressedNormalDispatchBridgeDirective.atom)
          (.compat (mkPattern compressedNormalDispatchBridgePatterns))
  unfold cMatchInputSpecMork Conformance.Computable.cmatchInputSpec
  have readPerm := physical_normal_dispatch_bridge_read_perm listNodup
    morkNodup directivePresent
  constructor
  · intro member
    exact cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mp atomMember)
      substitution consumed member
  · intro member
    exact cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mpr atomMember)
      substitution consumed member

/-- Exact bridge outputs as instantiated by the physical compact-key matcher. -/
def PhysicalExactNormalDispatchBridge (proofOwner : Atom)
    (space : List Atom) : Prop :=
  ∃ substitution ∈ physicalNormalDispatchBridgeMatcherRows space,
    instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input substitution
          (.var "normal-handoff-loader-rule") =
        some compressedNormalHandoffLoadRule ∧
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input substitution
          (.var "normal-handoff-finish-rule") =
        some compressedNormalHandoffFinishRule ∧
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input substitution
          compressedNormalHandoffInitialLoadingTemplate =
        some (normalDispatchBridgeInitialLoadingRow proofOwner)

theorem physical_exact_normal_dispatch_bridge_of_reflective
    (proofOwner : Atom) {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : compressedNormalDispatchBridgeDirective.atom ∈ space)
    (matched : ExactNormalDispatchBridge proofOwner space) :
    PhysicalExactNormalDispatchBridge proofOwner space := by
  rcases matched with ⟨substitution, rowMember, loader, finish, loading⟩
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, reflected, equal⟩ := rowMember
  have reflected' : (substitution, consumed) ∈
      Conformance.Computable.cmatchInputSpec []
        (compressedNormalDispatchBridgeDirective.atom ::
          space.erase compressedNormalDispatchBridgeDirective.atom)
        compressedNormalDispatchBridgeDirective.rule.input := by
    cases equal
    exact reflected
  have physicalMatch :=
    (physical_normal_dispatch_bridge_matcher_mem_iff listNodup morkNodup
      directivePresent substitution consumed).2 reflected'
  have physicalRow : substitution ∈
      physicalNormalDispatchBridgeMatcherRows space := by
    unfold physicalNormalDispatchBridgeMatcherRows
    rw [List.mem_map]
    refine ⟨(substitution, consumed), ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨physicalMatch, ?_⟩
    rw [compressedNormalDispatchBridgeDirective_guards_exact]
    rfl
  exact ⟨substitution, physicalRow,
    instantiateRuleTemplateAtom?_of_reflective _ loader,
    instantiateRuleTemplateAtom?_of_reflective _ finish,
    instantiateRuleTemplateAtom?_of_reflective _ loading⟩

/-- Exact live rows plus physical duplicate freedom are sufficient for the
actual compact-key matcher to publish the owner-bound normal loader. -/
theorem physical_exact_normal_dispatch_bridge_of_live_rows
    (proofOwner : Atom) (space : List Atom)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (bridgePresent : compressedNormalDispatchBridgeRule ∈ space)
    (reloadPresent : normalDispatchBridgeReloadRow proofOwner ∈ space)
    (loaderPresent : compressedNormalHandoffLoaderCaptureRow ∈ space)
    (finishPresent : compressedNormalHandoffFinishCaptureRow ∈ space) :
    PhysicalExactNormalDispatchBridge proofOwner space := by
  exact physical_exact_normal_dispatch_bridge_of_reflective proofOwner
    listNodup morkNodup bridgePresent
    (exact_normal_dispatch_bridge_of_live_rows proofOwner space reloadPresent
      loaderPresent finishPresent)

/-- Every substitution selected by the physical matcher on the canonical
bridge slice consumes the same owner request and has the same three exact
owner-indexed outputs. -/
theorem physical_normal_dispatch_bridge_matcher_interface_exact
    (proofOwner : Atom) {substitution : Subst}
    (member : substitution ∈ physicalNormalDispatchBridgeMatcherRows
      (normalDispatchBridgeSlice proofOwner)) :
    instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input substitution
          compressedAssertionNormalReloadRequest =
        some (normalDispatchBridgeReloadRow proofOwner) ∧
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input substitution
          (.var "normal-handoff-loader-rule") =
        some compressedNormalHandoffLoadRule ∧
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input substitution
          (.var "normal-handoff-finish-rule") =
        some compressedNormalHandoffFinishRule ∧
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input substitution
          compressedNormalHandoffInitialLoadingTemplate =
        some (normalDispatchBridgeInitialLoadingRow proofOwner) := by
  unfold physicalNormalDispatchBridgeMatcherRows at member
  rw [List.mem_map] at member
  obtain ⟨⟨matchedSubstitution, consumed⟩, filtered, equal⟩ := member
  have physicalMatched := (List.mem_filter.mp filtered).1
  have ordinaryMatched :=
    (physical_normal_dispatch_bridge_matcher_mem_iff
      (normalDispatchBridgeSlice_nodup proofOwner)
      (normalDispatchBridgeSlice_mork_nodup proofOwner)
      (by
        change compressedNormalDispatchBridgeRule ∈
          normalDispatchBridgeSlice proofOwner
        simp [normalDispatchBridgeSlice]) matchedSubstitution consumed).1
        physicalMatched
  have ordinaryMember : matchedSubstitution ∈
      (cmatchInputSpec []
        (compressedNormalDispatchBridgeRule ::
          (normalDispatchBridgeSlice proofOwner).erase
            compressedNormalDispatchBridgeRule)
        compressedNormalDispatchBridgeDirective.rule.input).map Prod.fst :=
    List.mem_map_of_mem ordinaryMatched
  rw [normalDispatchBridge_reflective_rows_exact] at ordinaryMember
  simp only [List.mem_singleton] at ordinaryMember
  subst matchedSubstitution
  subst substitution
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem compressedNormalDispatchBridgeSinks_loader_split :
    compressedNormalDispatchBridgeSinks =
      [.remove compressedAssertionNormalReloadRequest] ++
        .add (.var "normal-handoff-loader-rule") ::
          [.add (.var "normal-handoff-finish-rule"),
           .add compressedNormalHandoffInitialLoadingTemplate] := by
  rfl

private theorem compressedNormalDispatchBridgeSinks_finish_split :
    compressedNormalDispatchBridgeSinks =
      [.remove compressedAssertionNormalReloadRequest,
       .add (.var "normal-handoff-loader-rule")] ++
        .add (.var "normal-handoff-finish-rule") ::
          [.add compressedNormalHandoffInitialLoadingTemplate] := by
  rfl

/-- One physically matched bridge publishes the finite loader, its terminal
step, and the exact owner-bound initial cursor. -/
theorem physical_normal_dispatch_bridge_support_present
    (proofOwner : Atom) (space : List Atom)
    (matched : PhysicalExactNormalDispatchBridge proofOwner space) :
    let result := cFireRuleScopedSourceExecFact space
      compressedNormalDispatchBridgeDirective
    morkSupportContains result compressedNormalHandoffLoadRule = true ∧
      morkSupportContains result compressedNormalHandoffFinishRule = true ∧
      morkSupportContains result
        (normalDispatchBridgeInitialLoadingRow proofOwner) = true := by
  dsimp only
  rcases matched with ⟨substitution, rowMember, loader, finish, loading⟩
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change
    let live := morkEraseSupport space
      compressedNormalDispatchBridgeDirective.atom
    cApplyRuleScopedSinkBatch
        compressedNormalDispatchBridgeDirective.rule.input
        (physicalNormalDispatchBridgeMatcherRows space) live
        compressedNormalDispatchBridgeDirective.rule.tmpl.sinks |> fun result =>
      morkSupportContains result compressedNormalHandoffLoadRule = true ∧
        morkSupportContains result compressedNormalHandoffFinishRule = true ∧
        morkSupportContains result
          (normalDispatchBridgeInitialLoadingRow proofOwner) = true
  dsimp only
  change
    morkSupportContains
        (cApplyRuleScopedSinkBatch
          compressedNormalDispatchBridgeDirective.rule.input
          (physicalNormalDispatchBridgeMatcherRows space)
          (morkEraseSupport space
            compressedNormalDispatchBridgeDirective.atom)
          compressedNormalDispatchBridgeSinks)
        compressedNormalHandoffLoadRule = true ∧
      morkSupportContains
        (cApplyRuleScopedSinkBatch
          compressedNormalDispatchBridgeDirective.rule.input
          (physicalNormalDispatchBridgeMatcherRows space)
          (morkEraseSupport space
            compressedNormalDispatchBridgeDirective.atom)
          compressedNormalDispatchBridgeSinks)
        compressedNormalHandoffFinishRule = true ∧
      morkSupportContains
        (cApplyRuleScopedSinkBatch
          compressedNormalDispatchBridgeDirective.rule.input
          (physicalNormalDispatchBridgeMatcherRows space)
          (morkEraseSupport space
            compressedNormalDispatchBridgeDirective.atom)
          compressedNormalDispatchBridgeSinks)
        (normalDispatchBridgeInitialLoadingRow proofOwner) = true
  refine ⟨?_, ?_, ?_⟩
  · rw [compressedNormalDispatchBridgeSinks_loader_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember loader (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl <;> exact Or.inl ⟨_, rfl⟩)
  · rw [compressedNormalDispatchBridgeSinks_finish_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember finish (by
        intro sink sinkMember
        simp only [List.mem_singleton] at sinkMember
        subst sink
        exact Or.inl ⟨_, rfl⟩)
  · exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _
      [.remove compressedAssertionNormalReloadRequest,
       .add (.var "normal-handoff-loader-rule"),
       .add (.var "normal-handoff-finish-rule")]
      compressedNormalHandoffInitialLoadingTemplate
      (normalDispatchBridgeInitialLoadingRow proofOwner) [] substitution
      rowMember loading (by
        intro sink sinkMember
        simp at sinkMember)

theorem compressedNormalDispatchBridgeDirective_supportSet :
    ReflectiveSupportSetTemplate
      compressedNormalDispatchBridgeDirective.rule.tmpl := by
  intro sink member
  change sink ∈ compressedNormalDispatchBridgeSinks at member
  simp only [compressedNormalDispatchBridgeSinks, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> trivial

/-- Actual physical result of the canonical owner-bound bridge transaction. -/
def physicalNormalDispatchBridgeResult (proofOwner : Atom) : List Atom :=
  cFireRuleScopedSourceExecFact (normalDispatchBridgeSlice proofOwner)
    compressedNormalDispatchBridgeDirective

/-- Complete nominal successor expected from the physical bridge. -/
def physicalNormalDispatchBridgeReference (proofOwner : Atom) : List Atom :=
  [compressedNormalHandoffLoaderCaptureRow,
   compressedNormalHandoffFinishCaptureRow,
   compressedNormalHandoffLoadRule,
   compressedNormalHandoffFinishRule,
   normalDispatchBridgeInitialLoadingRow proofOwner]

private theorem compressedNormalHandoffFinishRule_exec_shape :
    ∃ location input output,
      compressedNormalHandoffFinishRule =
        .expression [.symbol "exec", location, input, output] := by
  have present :
      (extractSupportedSourceExecFact
        compressedNormalHandoffFinishRule).isSome = true := by
    decide +kernel
  obtain ⟨directive, decoded⟩ := Option.isSome_iff_exists.mp present
  exact extractSupportedSourceExecFact_exec_shape decoded

private theorem expression_key_ne_normalHandoffLoadRule
    (head : String) (tail : List Atom)
    (arityBound : tail.length + 1 < 64)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (different : head ≠ "exec") :
    morkSupportKey (.expression (.symbol head :: tail)) ≠
      morkSupportKey compressedNormalHandoffLoadRule := by
  unfold compressedNormalHandoffLoadRule
  apply morkSupportKey_expression_symbol_head_ne
  · exact arityBound
  · norm_num
  · exact headPositive
  · decide
  · exact headBound
  · decide
  · exact different

private theorem expression_key_ne_normalHandoffFinishRule
    (head : String) (tail : List Atom)
    (arityBound : tail.length + 1 < 64)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (different : head ≠ "exec") :
    morkSupportKey (.expression (.symbol head :: tail)) ≠
      morkSupportKey compressedNormalHandoffFinishRule := by
  obtain ⟨location, input, output, finishShape⟩ :=
    compressedNormalHandoffFinishRule_exec_shape
  rw [finishShape]
  apply morkSupportKey_expression_symbol_head_ne
  · exact arityBound
  · norm_num
  · exact headPositive
  · decide
  · exact headBound
  · decide
  · exact different

private theorem normalHandoffLoad_key_ne_finish :
    morkSupportKey compressedNormalHandoffLoadRule ≠
      morkSupportKey compressedNormalHandoffFinishRule := by
  decide +kernel

/-- The exact nominal bridge successor is duplicate-free at MORK's compact
physical identity. -/
theorem physicalNormalDispatchBridgeReference_mork_nodup (proofOwner : Atom) :
    MorkSupportNodup (physicalNormalDispatchBridgeReference proofOwner) := by
  unfold MorkSupportNodup physicalNormalDispatchBridgeReference
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false]
  refine ⟨?_, ?_⟩
  · intro equal
    rcases equal with equal | equal | equal | equal
    · exact normalDispatchLoader_key_ne_finish equal
    · exact expression_key_ne_normalHandoffLoadRule _ _ (by norm_num)
        (by decide) (by decide) (by decide) equal
    · exact expression_key_ne_normalHandoffFinishRule _ _ (by norm_num)
        (by decide) (by decide) (by decide) equal
    · unfold compressedNormalHandoffLoaderCaptureRow
        normalDispatchBridgeInitialLoadingRow at equal
      exact (morkSupportKey_expression_symbol_head_ne _ _ _ _
        (by norm_num) (by norm_num) (by decide) (by decide)
        (by decide) (by decide) (by decide)) equal
  · refine ⟨?_, ?_⟩
    · intro equal
      rcases equal with equal | equal | equal
      · exact expression_key_ne_normalHandoffLoadRule _ _ (by norm_num)
          (by decide) (by decide) (by decide) equal
      · exact expression_key_ne_normalHandoffFinishRule _ _ (by norm_num)
          (by decide) (by decide) (by decide) equal
      · unfold compressedNormalHandoffFinishCaptureRow
          normalDispatchBridgeInitialLoadingRow at equal
        exact (morkSupportKey_expression_symbol_head_ne _ _ _ _
          (by norm_num) (by norm_num) (by decide) (by decide)
          (by decide) (by decide) (by decide)) equal
    · refine ⟨?_, ?_⟩
      · intro equal
        rcases equal with equal | equal
        · exact normalHandoffLoad_key_ne_finish equal
        · exact (expression_key_ne_normalHandoffLoadRule _ _ (by norm_num)
            (by decide) (by decide) (by decide)).symm equal
      · refine ⟨?_, ?_⟩
        · exact (expression_key_ne_normalHandoffFinishRule _ _ (by norm_num)
            (by decide) (by decide) (by decide)).symm
        · simp

/-- The physical remove sink consumes the owner-bound reload request, and no
loader output recreates that exact row. -/
theorem physical_normal_dispatch_bridge_consumes_reload (proofOwner : Atom) :
    normalDispatchBridgeReloadRow proofOwner ∉
      physicalNormalDispatchBridgeResult proofOwner := by
  let rows := physicalNormalDispatchBridgeMatcherRows
    (normalDispatchBridgeSlice proofOwner)
  obtain ⟨substitution, substitutionMember, _loader, _finish, _loading⟩ :=
    physical_exact_normal_dispatch_bridge_of_reflective proofOwner
      (normalDispatchBridgeSlice_nodup proofOwner)
      (normalDispatchBridgeSlice_mork_nodup proofOwner)
      (by
        change compressedNormalDispatchBridgeRule ∈
          normalDispatchBridgeSlice proofOwner
        simp [normalDispatchBridgeSlice])
      (canonical_exact_normal_dispatch_bridge proofOwner)
  have exactInterface : ∀ candidate ∈ rows,
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input candidate
          compressedAssertionNormalReloadRequest =
        some (normalDispatchBridgeReloadRow proofOwner) ∧
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input candidate
          (.var "normal-handoff-loader-rule") =
        some compressedNormalHandoffLoadRule ∧
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input candidate
          (.var "normal-handoff-finish-rule") =
        some compressedNormalHandoffFinishRule ∧
      instantiateRuleTemplateAtom?
          compressedNormalDispatchBridgeDirective.rule.input candidate
          compressedNormalHandoffInitialLoadingTemplate =
        some (normalDispatchBridgeInitialLoadingRow proofOwner) := by
    intro candidate member
    exact physical_normal_dispatch_bridge_matcher_interface_exact proofOwner
      (by simpa [rows] using member)
  have absent : normalDispatchBridgeReloadRow proofOwner ∉
      cApplyRuleScopedSinkBatch
        compressedNormalDispatchBridgeDirective.rule.input rows
        (morkEraseSupport (normalDispatchBridgeSlice proofOwner)
          compressedNormalDispatchBridgeDirective.atom)
        compressedNormalDispatchBridgeSinks := by
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      compressedNormalDispatchBridgeDirective.rule.input rows
      (morkEraseSupport (normalDispatchBridgeSlice proofOwner)
        compressedNormalDispatchBridgeDirective.atom) []
      compressedAssertionNormalReloadRequest
      (normalDispatchBridgeReloadRow proofOwner)
      [.add (.var "normal-handoff-loader-rule"),
       .add (.var "normal-handoff-finish-rule"),
       .add compressedNormalHandoffInitialLoadingTemplate]
      substitution (by simpa [rows] using substitutionMember)
      (exactInterface substitution
        (by simpa [rows] using substitutionMember)).1
    intro sink sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(exactInterface candidate member).2.1]
        simp [normalDispatchBridgeReloadRow,
          compressedNormalHandoffLoadRule]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(exactInterface candidate member).2.2.1]
        obtain ⟨location, input, output, finishShape⟩ :=
          compressedNormalHandoffFinishRule_exec_shape
        rw [finishShape]
        simp [normalDispatchBridgeReloadRow]⟩
    · exact Or.inr ⟨_, rfl, by
        intro candidate member
        rw [(exactInterface candidate member).2.2.2]
        simp [normalDispatchBridgeReloadRow,
          normalDispatchBridgeInitialLoadingRow]⟩
  simpa [physicalNormalDispatchBridgeResult,
    cFireRuleScopedSourceExecFact, cApplyRuleScopedTemplate, rows,
    physicalNormalDispatchBridgeMatcherRows,
    compressedNormalDispatchBridgeDirective, mkTemplate] using absent

private theorem physical_normal_dispatch_bridge_preserves_row
    (proofOwner candidate : Atom)
    (present : candidate ∈ normalDispatchBridgeSlice proofOwner)
    (bridgeDifferent :
      morkSupportKey candidate ≠
        morkSupportKey compressedNormalDispatchBridgeDirective.atom)
    (reloadDifferent :
      morkSupportKey candidate ≠
        morkSupportKey (normalDispatchBridgeReloadRow proofOwner)) :
    candidate ∈ physicalNormalDispatchBridgeResult proofOwner := by
  let rows := physicalNormalDispatchBridgeMatcherRows
    (normalDispatchBridgeSlice proofOwner)
  have presentLive : candidate ∈
      morkEraseSupport (normalDispatchBridgeSlice proofOwner)
        compressedNormalDispatchBridgeDirective.atom :=
    mem_morkEraseSupport_of_mem_of_key_ne present bridgeDifferent
  have preserved : candidate ∈
      cApplyRuleScopedSinkBatch
        compressedNormalDispatchBridgeDirective.rule.input rows
        (morkEraseSupport (normalDispatchBridgeSlice proofOwner)
          compressedNormalDispatchBridgeDirective.atom)
        compressedNormalDispatchBridgeSinks := by
    apply mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
      compressedNormalDispatchBridgeDirective.rule.input rows
      (present := presentLive)
    intro sink sinkMember
    simp only [compressedNormalDispatchBridgeSinks, List.mem_cons,
      List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨compressedAssertionNormalReloadRequest, rfl, by
        intro substitution substitutionMember removed instantiated
        have exact :=
          physical_normal_dispatch_bridge_matcher_interface_exact proofOwner
            (by simpa [rows] using substitutionMember)
        have removedExact := Option.some.inj (instantiated.symm.trans exact.1)
        subst removed
        exact reloadDifferent⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  simpa [physicalNormalDispatchBridgeResult,
    cFireRuleScopedSourceExecFact, cApplyRuleScopedTemplate, rows,
    physicalNormalDispatchBridgeMatcherRows,
    compressedNormalDispatchBridgeDirective, mkTemplate] using preserved

/-- Every exact row retained or added by the canonical bridge belongs to its
complete nominal successor interface. -/
theorem physical_normal_dispatch_bridge_rows_within_reference
    (proofOwner : Atom) :
    ∀ row ∈ physicalNormalDispatchBridgeResult proofOwner,
      row ∈ physicalNormalDispatchBridgeReference proofOwner := by
  intro row rowMember
  let rows := physicalNormalDispatchBridgeMatcherRows
    (normalDispatchBridgeSlice proofOwner)
  let live := morkEraseSupport (normalDispatchBridgeSlice proofOwner)
    compressedNormalDispatchBridgeDirective.atom
  have origin : row ∈ live ∨
      RuleScopedAddedAtom
        compressedNormalDispatchBridgeDirective.rule.input rows
        compressedNormalDispatchBridgeDirective.rule.tmpl.sinks row := by
    apply mem_cApplyRuleScopedTemplate_of_supportSet
      compressedNormalDispatchBridgeDirective.rule.input live rows
      compressedNormalDispatchBridgeDirective.rule.tmpl
      compressedNormalDispatchBridgeDirective_supportSet
    simpa [physicalNormalDispatchBridgeResult,
      cFireRuleScopedSourceExecFact, live, rows,
      physicalNormalDispatchBridgeMatcherRows] using rowMember
  rcases origin with prior | added
  · have prior' : row ∈
        (normalDispatchBridgeSlice proofOwner).erase
          compressedNormalDispatchBridgeDirective.atom := by
      dsimp only [live] at prior
      rw [physical_normal_dispatch_bridge_live_eq
        (normalDispatchBridgeSlice_nodup proofOwner)
        (normalDispatchBridgeSlice_mork_nodup proofOwner)
        (by
          change compressedNormalDispatchBridgeRule ∈
            normalDispatchBridgeSlice proofOwner
          simp [normalDispatchBridgeSlice])] at prior
      exact prior
    have original := List.mem_of_mem_erase prior'
    simp only [normalDispatchBridgeSlice, List.mem_cons, List.not_mem_nil,
      or_false] at original
    rcases original with rfl | rfl | rfl | rfl
    · exact False.elim
        ((normalDispatchBridgeSlice_nodup proofOwner).not_mem_erase prior')
    · exact False.elim
        (physical_normal_dispatch_bridge_consumes_reload proofOwner rowMember)
    · simp [physicalNormalDispatchBridgeReference]
    · simp [physicalNormalDispatchBridgeReference]
  · rcases added with
      ⟨sink, sinkMember, authored, sinkEqual, substitution,
        substitutionMember, instantiated⟩
    have exact :=
      physical_normal_dispatch_bridge_matcher_interface_exact proofOwner
        (by simpa [rows] using substitutionMember)
    change sink ∈ compressedNormalDispatchBridgeSinks at sinkMember
    simp only [compressedNormalDispatchBridgeSinks, List.mem_cons,
      List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl
    · cases sinkEqual
    · cases sinkEqual
      have rowExact := Option.some.inj (instantiated.symm.trans exact.2.1)
      subst row
      simp [physicalNormalDispatchBridgeReference]
    · cases sinkEqual
      have rowExact := Option.some.inj (instantiated.symm.trans exact.2.2.1)
      subst row
      simp [physicalNormalDispatchBridgeReference]
    · cases sinkEqual
      have rowExact := Option.some.inj (instantiated.symm.trans exact.2.2.2)
      subst row
      simp [physicalNormalDispatchBridgeReference]

/-- Every canonical successor row has physical support in the actual bridge
result.  The two compiler-owned captures are framed through the exact remove
sink, while the three instantiated outputs use the physical matcher witness. -/
theorem physical_normal_dispatch_bridge_reference_support_complete
    (proofOwner : Atom) :
    ∀ row ∈ physicalNormalDispatchBridgeReference proofOwner,
      morkSupportContains (physicalNormalDispatchBridgeResult proofOwner) row =
        true := by
  have outputs := physical_normal_dispatch_bridge_support_present proofOwner
    (normalDispatchBridgeSlice proofOwner)
    (physical_exact_normal_dispatch_bridge_of_reflective proofOwner
      (normalDispatchBridgeSlice_nodup proofOwner)
      (normalDispatchBridgeSlice_mork_nodup proofOwner)
      (by
        change compressedNormalDispatchBridgeRule ∈
          normalDispatchBridgeSlice proofOwner
        simp [normalDispatchBridgeSlice])
      (canonical_exact_normal_dispatch_bridge proofOwner))
  intro row member
  simp only [physicalNormalDispatchBridgeReference, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · apply morkSupportContains_eq_true_of_mem
    exact physical_normal_dispatch_bridge_preserves_row proofOwner _
      (by simp [normalDispatchBridgeSlice])
      normalDispatchBridge_key_ne_loader.symm
      (normalDispatchReload_key_ne_loader proofOwner).symm
  · apply morkSupportContains_eq_true_of_mem
    exact physical_normal_dispatch_bridge_preserves_row proofOwner _
      (by simp [normalDispatchBridgeSlice])
      normalDispatchBridge_key_ne_finish.symm
      (normalDispatchReload_key_ne_finish proofOwner).symm
  · exact outputs.1
  · exact outputs.2.1
  · exact outputs.2.2

/-- The actual MORK bridge successor is exactly the complete nominal interface
up to row permutation.  This is the representation respected by the generic
least-key scheduler, whose selection is permutation-invariant. -/
theorem physical_normal_dispatch_bridge_perm_reference (proofOwner : Atom) :
    (physicalNormalDispatchBridgeResult proofOwner).Perm
      (physicalNormalDispatchBridgeReference proofOwner) := by
  have resultNodup : (physicalNormalDispatchBridgeResult proofOwner).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (normalDispatchBridgeSlice_nodup proofOwner)
  have referenceMorkNodup :=
    physicalNormalDispatchBridgeReference_mork_nodup proofOwner
  have referenceNodup :
      (physicalNormalDispatchBridgeReference proofOwner).Nodup :=
    List.Nodup.of_map morkSupportKey referenceMorkNodup
  apply (List.perm_ext_iff_of_nodup resultNodup referenceNodup).2
  intro row
  constructor
  · exact physical_normal_dispatch_bridge_rows_within_reference proofOwner row
  · intro member
    exact mem_of_morkSupportContains_of_reference referenceMorkNodup member
      (physical_normal_dispatch_bridge_rows_within_reference proofOwner)
      (physical_normal_dispatch_bridge_reference_support_complete proofOwner
        row member)

/-! ## Canonical scheduled transaction -/

private theorem extract_supported_none_of_expression_head_ne
    (head : String) (tail : List Atom) (different : head ≠ "exec") :
    extractSupportedSourceExecFact
      (.expression (.symbol head :: tail)) = none := by
  simp [extractSupportedSourceExecFact, extractRawExecFact, different]

theorem normalDispatchBridgeSlice_supported_exact (proofOwner : Atom) :
    cSupportedSourceExecFacts (normalDispatchBridgeSlice proofOwner) =
      [compressedNormalDispatchBridgeDirective] := by
  let tail :=
    [normalDispatchBridgeReloadRow proofOwner,
     compressedNormalHandoffLoaderCaptureRow,
     compressedNormalHandoffFinishCaptureRow]
  have tailNone : cSupportedSourceExecFacts tail = [] := by
    unfold cSupportedSourceExecFacts
    rw [List.filterMap_eq_nil_iff]
    intro row member
    dsimp only [tail] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · unfold normalDispatchBridgeReloadRow
      exact extract_supported_none_of_expression_head_ne _ _ (by decide)
    · unfold compressedNormalHandoffLoaderCaptureRow
      exact extract_supported_none_of_expression_head_ne _ _ (by decide)
    · unfold compressedNormalHandoffFinishCaptureRow
      exact extract_supported_none_of_expression_head_ne _ _ (by decide)
  change cSupportedSourceExecFacts
    (compressedNormalDispatchBridgeRule :: tail) =
      [compressedNormalDispatchBridgeDirective]
  unfold cSupportedSourceExecFacts at tailNone ⊢
  rw [List.filterMap_cons, tailNone]
  change
    (match extractSupportedSourceExecFact compressedNormalDispatchBridgeRule with
      | none => []
      | some directive => [directive]) =
        [compressedNormalDispatchBridgeDirective]
  rw [extract_compressedNormalDispatchBridgeRule_exact]

theorem canonical_physical_exact_normal_dispatch_bridge (proofOwner : Atom) :
    PhysicalExactNormalDispatchBridge proofOwner
      (normalDispatchBridgeSlice proofOwner) := by
  apply physical_exact_normal_dispatch_bridge_of_live_rows proofOwner
    (normalDispatchBridgeSlice proofOwner)
    (normalDispatchBridgeSlice_nodup proofOwner)
    (normalDispatchBridgeSlice_mork_nodup proofOwner)
  · simp [normalDispatchBridgeSlice]
  · simp [normalDispatchBridgeSlice]
  · simp [normalDispatchBridgeSlice]
  · simp [normalDispatchBridgeSlice]

/-- The generic least-key rule-scoped MORK scheduler performs the bridge
transaction on the canonical owner-bound boundary. -/
theorem normalDispatchBridgeSlice_steps (proofOwner : Atom) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (normalDispatchBridgeSlice proofOwner) =
      some (cFireRuleScopedSourceExecFact
        (normalDispatchBridgeSlice proofOwner)
        compressedNormalDispatchBridgeDirective) := by
  unfold cRuleScopedSourceWorkQueueStep
  rw [normalDispatchBridgeSlice_supported_exact proofOwner]
  rfl

/-- The scheduled bridge step installs both finite-loader rules and the exact
initial owner-bound cursor in physical MORK support. -/
theorem normalDispatchBridgeSlice_step_support (proofOwner : Atom) :
    let result := cFireRuleScopedSourceExecFact
      (normalDispatchBridgeSlice proofOwner)
      compressedNormalDispatchBridgeDirective
    morkSupportContains result compressedNormalHandoffLoadRule = true ∧
      morkSupportContains result compressedNormalHandoffFinishRule = true ∧
      morkSupportContains result
        (normalDispatchBridgeInitialLoadingRow proofOwner) = true := by
  exact physical_normal_dispatch_bridge_support_present proofOwner
    (normalDispatchBridgeSlice proofOwner)
    (canonical_physical_exact_normal_dispatch_bridge proofOwner)

#print axioms canonical_exact_normal_dispatch_bridge
#print axioms normalDispatchBridgeSlice_nodup
#print axioms normalDispatchBridgeSlice_mork_nodup
#print axioms exact_normal_dispatch_bridge_of_live_rows
#print axioms physical_normal_dispatch_bridge_read_perm
#print axioms physical_normal_dispatch_bridge_matcher_mem_iff
#print axioms physical_exact_normal_dispatch_bridge_of_reflective
#print axioms physical_exact_normal_dispatch_bridge_of_live_rows
#print axioms physical_normal_dispatch_bridge_matcher_interface_exact
#print axioms physical_normal_dispatch_bridge_support_present
#print axioms compressedNormalDispatchBridgeDirective_supportSet
#print axioms physical_normal_dispatch_bridge_consumes_reload
#print axioms physical_normal_dispatch_bridge_rows_within_reference
#print axioms physicalNormalDispatchBridgeReference_mork_nodup
#print axioms physical_normal_dispatch_bridge_reference_support_complete
#print axioms physical_normal_dispatch_bridge_perm_reference
#print axioms normalDispatchBridgeSlice_supported_exact
#print axioms canonical_physical_exact_normal_dispatch_bridge
#print axioms normalDispatchBridgeSlice_steps
#print axioms normalDispatchBridgeSlice_step_support

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalDispatchBridge
