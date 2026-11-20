import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemCorrespondence

/-!
# Concrete `P5` correspondence instances (`N` and `C`)

This module instantiates the assembled `P5` correspondence (`ReflSystemCorrespondence`) on all
three concrete families required by the milestone specification:

1. **The manuscript's canary** (`canarySource := @0?(for((0) <- @0)0 | for(y <- @0)y)`):
   `instance_canary_N` and `instance_canary_C` verify initial `CleanRepresents`, `SystemInvN`/`C`,
   and `BackwardReadyN`/`C`, together with the forward `LocatedRun` reaching `CleanRepresents` and
   `SystemInvN`/`C` for the listener target and realizing `BagStep` (**N**) and `CanonicalBagStep`
   (**C**).
2. **Nested reflection** (`nestedCanarySource := @0?(@0?(for((0) <- @0)0 | for(y <- @0)y))` and
   `nestedOpenSource := @0?(@0?(for(a1 <- @0)a1 | for(0 <- @0)a))`):
   `instance_nested_refl_N`, `instance_nested_refl_C`, and `instance_nested_open_refl_N` verify
   initial and target `CleanRepresents` and `SystemInvN`/`C` through `source_step_forward_N` and
   `source_step_forward_C`.
3. **Two concurrent reflections at different children**
   (`concurrentSource := @0?(for((0) <- @0)0 | for(y <- @0)y) | @@0?(for((0) <- @0)0 | for(z <- @0)z)`):
   - `instance_concurrent_children_N` and `instance_concurrent_children_C` execute both reflections
     from `(encodeLabel concurrentSource, encodeConf)` to completion via `refl_step_forward_list_N`
     and `refl_step_forward_list_C`, realizing the 2-step `ReflTransGen` of `BagStep` (**N**) and
     `CanonicalBagStep` (**C**) into `CleanRepresents` and `SystemInvN`/`C`.
   - `instance_concurrent_commute` exercises `P2`'s `commute_different_children` directly on the
     two sibling `openRootAt` firings from the heated 2-row root configuration, proving diamond
     commutation (identical `present` sets, identical `label` maps, equivalent knowledge stores) and
     reaching a state in `SystemInvN` and `SystemInvC` with **both** child locations simultaneously
     in flight (`active.length = 2`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect
  applyDot demoChan)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil GroundPrincipal)
open MeTTaCalculus.Corrected (BagEq BagStep CanonicalBagStep conventional listener)
open FiniteProgram (channelUnknown)
open Comm (E renameBy ruleVars)
open OneFrame (embed)
open ReflNames (NameLaws nameAction QN QNE fresh_name nameLaws_heads)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok reflP anyY anyZ openRoot located
  psubst_rootLoc psubst_atLoc_any psubst_pendingTok locatedFrame_name)
open ReflPacking (psubst_doneTok nameLaws_doneTok_iff)
open ReflLocatedStep (psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff res resConf
  info_known psubst_pReflect)
open ReflUniform (predotU predotU_ground)
open ReflCorrespondence (Clean LocatedRun Splits openRootAt openRootAt_eq openRootAtX
  openRoot_admitted open_reading)

/-! ## Shared helper: initial `BackwardReadyN` / `BackwardReadyC` for non-guard single-row encodings -/

theorem encode_backwardReady (P : Pattern) :
    BackwardReadyN encodeConf [(0, P)] [] ∧ BackwardReadyC encodeConf [(0, P)] [] :=
  ⟨⟨fun q₁ m₁ q₂ m₂ _ _ _ _ _ _ ne => by
      obtain rfl := List.mem_singleton.mp m₁
      obtain rfl := List.mem_singleton.mp m₂
      exact absurd rfl ne,
    fun _ m => absurd m List.not_mem_nil,
    fun _ m => absurd m List.not_mem_nil,
    fun _ m => absurd m List.not_mem_nil⟩,
   ⟨fun q₁ m₁ q₂ m₂ _ _ _ _ _ _ ne => by
      obtain rfl := List.mem_singleton.mp m₁
      obtain rfl := List.mem_singleton.mp m₂
      exact absurd rfl ne,
    fun _ m => absurd m List.not_mem_nil,
    fun _ m => absurd m List.not_mem_nil,
    fun _ m => absurd m List.not_mem_nil,
    fun _ m => absurd m List.not_mem_nil⟩⟩

/-! ## Instance 1: The manuscript's canary (`@0?(for((0) <- @0)0 | for(y <- @0)y)`) -/

/-- The manuscript's canary reflection `@0?(for((0) <- @0)0 | for(y <- @0)y)`. -/
def canarySource : Pattern := pReflect demoChan nestedCanaryInner

/-- Canary reduct `pPar [applyDot [("y", (0))] 0, applyDot [("y", (0))] y]`. -/
def canaryReduct : Pattern :=
  pPar [applyDot nestedCanaryUnifier pZero, applyDot nestedCanaryUnifier nestedVarY]

/-- Canary target listener under **Interface N**. -/
def canaryTargetN : Pattern := pFor (tProc canaryReduct) demoChan pZero

/-- Canary target listener under **Interface C**. -/
def canaryTargetC : Pattern := listener demoChan canaryReduct

theorem canarySource_hostedNode : HostedNode canarySource :=
  .reflect ⟨by decide +kernel, by decide +kernel⟩
    (.par (.guard ⟨by decide +kernel, by decide +kernel⟩)
          (.guard ⟨by decide +kernel, by decide +kernel⟩))

private theorem canaryInner_subStepN :
    HostedSubStepN 0 nestedCanaryInner canaryReduct (nestedZeroTerm, nestedVarY)
      nestedCanaryUnifier := by
  have split₀ : Splits nestedCanaryInner
      ([] ++ pFor nestedZeroTerm demoChan pZero :: ([] ++ pFor nestedVarY demoChan nestedVarY :: [])) :=
    show Splits (par _ _) ([_] ++ [_]) from
      .split (.leaf (pFor nestedZeroTerm demoChan pZero)) (.leaf (pFor nestedVarY demoChan nestedVarY))
  have plainA : PlainPatterns (applyDot nestedCanaryUnifier pZero) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, pZero,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
  have plainB : PlainPatterns (applyDot nestedCanaryUnifier nestedVarY) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, nestedCanaryUnifier, nestedVarY, nestedZeroTerm,
      tProc, pZero, nQuote, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  exact .comm [] [] [] nestedZeroTerm nestedVarY demoChan pZero nestedVarY nestedCanaryUnifier
    split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) plainA plainB nestedCanaryUnifier_gp
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem canaryInner_subStepC :
    HostedSubStepC 0 nestedCanaryInner canaryReduct (nestedZeroTerm, nestedVarY)
      nestedCanaryUnifier := by
  have split₀ : Splits nestedCanaryInner
      ([] ++ pFor nestedZeroTerm demoChan pZero :: ([] ++ pFor nestedVarY demoChan nestedVarY :: [])) :=
    show Splits (par _ _) ([_] ++ [_]) from
      .split (.leaf (pFor nestedZeroTerm demoChan pZero)) (.leaf (pFor nestedVarY demoChan nestedVarY))
  have plainA : PlainPatterns (applyDot nestedCanaryUnifier pZero) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, pZero,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
  have plainB : PlainPatterns (applyDot nestedCanaryUnifier nestedVarY) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, nestedCanaryUnifier, nestedVarY, nestedZeroTerm,
      tProc, pZero, nQuote, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  exact .comm [] [] [] nestedZeroTerm nestedVarY demoChan pZero nestedVarY nestedCanaryUnifier
    split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) plainA plainB nestedCanaryUnifier_gp
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun _ m => absurd m List.not_mem_nil)
    (by decide +kernel) (by decide +kernel)

/-- **Instance 1 (`N`)**: the manuscript's canary `@0?(for((0) <- @0)0 | for(y <- @0)y)` under
**Interface N**. -/
theorem instance_canary_N :
    CleanRepresents (encodeLabel canarySource) encodeConf canarySource ∧
    SystemInvBy StepRelN (encodeLabel canarySource) encodeConf canarySource
      [(0, canarySource)] [] ∧
    BackwardReadyN encodeConf [(0, canarySource)] [] ∧
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ),
      LocatedRun (encodeLabel canarySource) encodeConf label' C' ∧
      CleanRepresents label' C' canaryTargetN ∧
      SystemInvN label' C' canaryTargetN ∧
      BagStep conventional canarySource canaryTargetN := by
  have anch : ∀ q ∈ [nestedZeroTerm, nestedVarY], SpineHasPattern q (predotU canarySource) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact .reflect _ (.parLeft _ (.guard _ _))
    · exact .reflect _ (.parRight _ (.guard _ _))
  have rep₀ := encode_cleanRepresentsBy canarySource_hostedNode anch
  have ms : MultiSplits [(0, canarySource)] ([] ++ pReflect demoChan nestedCanaryInner :: []) :=
    MultiSplits.of_map_snd rfl
  obtain ⟨label', C', rows', run, _, rep', bStep⟩ :=
    refl_step_forward_list_N rep₀ ms ⟨by decide +kernel, by decide +kernel⟩ canaryInner_subStepN
      (fun _ m => absurd m List.not_mem_nil) (fun _ m => absurd m List.not_mem_nil)
      (bagEq_pPar_singleton canaryTargetN)
  have initClean : CleanRepresentsBy (encodeLabel canarySource) encodeConf canarySource
      [(0, canarySource)] [] :=
    encode_cleanRepresentsBy canarySource_hostedNode fun _ m => absurd m List.not_mem_nil
  exact ⟨rep₀.toCleanRepresents, initClean.toSystemInvBy,
    (encode_backwardReady canarySource).1,
    label', C', run, rep'.toCleanRepresents, rep'.toCleanRepresents.toSystemInvN, bStep⟩

/-- **Instance 1 (`C`)**: the manuscript's canary `@0?(for((0) <- @0)0 | for(y <- @0)y)` under
**Interface C**. -/
theorem instance_canary_C :
    CleanRepresents (encodeLabel canarySource) encodeConf canarySource ∧
    SystemInvBy StepRelC (encodeLabel canarySource) encodeConf canarySource
      [(0, canarySource)] [] ∧
    BackwardReadyC encodeConf [(0, canarySource)] [] ∧
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ),
      LocatedRun (encodeLabel canarySource) encodeConf label' C' ∧
      CleanRepresents label' C' canaryTargetC ∧
      SystemInvC label' C' canaryTargetC ∧
      CanonicalBagStep conventional canarySource canaryTargetC := by
  have anch : ∀ q ∈ [nestedZeroTerm, nestedVarY], SpineHasPattern q (predotU canarySource) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact .reflect _ (.parLeft _ (.guard _ _))
    · exact .reflect _ (.parRight _ (.guard _ _))
  have rep₀ := encode_cleanRepresentsBy canarySource_hostedNode anch
  have ms : MultiSplits [(0, canarySource)] ([] ++ pReflect demoChan nestedCanaryInner :: []) :=
    MultiSplits.of_map_snd rfl
  obtain ⟨label', C', rows', run, _, rep', cStep⟩ :=
    refl_step_forward_list_C rep₀ ms ⟨by decide +kernel, by decide +kernel⟩ canaryInner_subStepC
      (fun _ m => absurd m List.not_mem_nil) (fun _ m => absurd m List.not_mem_nil)
      (bagEq_pPar_singleton canaryTargetC)
  have initClean : CleanRepresentsBy (encodeLabel canarySource) encodeConf canarySource
      [(0, canarySource)] [] :=
    encode_cleanRepresentsBy canarySource_hostedNode fun _ m => absurd m List.not_mem_nil
  exact ⟨rep₀.toCleanRepresents, initClean.toSystemInvBy,
    (encode_backwardReady canarySource).2,
    label', C', run, rep'.toCleanRepresents, rep'.toCleanRepresents.toSystemInvC, cStep⟩

/-! ## Instance 2: Nested reflection (`@0?(@0?(...))`) under `N` and `C` -/

/-- Nested canary target under **Interface N**. -/
def nestedCanaryTargetN : Pattern := pFor (tProc (pPar [canaryTargetN])) demoChan pZero

/-- Nested canary target under **Interface C**. -/
def nestedCanaryTargetC : Pattern := listener demoChan (pPar [canaryTargetC])

/-- Nested open-reduct target under **Interface N** (`"a"` remains free inside the inner quote). -/
def nestedOpenTargetN : Pattern :=
  let R₀ := pPar [applyDot nestedOpenUnifier (.fvar "a1"), applyDot nestedOpenUnifier (.fvar "a")]
  pFor (tProc (pPar [pFor (tProc R₀) demoChan pZero])) demoChan pZero

/-- **Instance 2a (`N`)**: nested canary `@0?(@0?(for((0) <- @0)0 | for(y <- @0)y))` through
`source_step_forward_N`. -/
theorem instance_nested_refl_N :
    CleanRepresents (encodeLabel nestedCanarySource) encodeConf nestedCanarySource ∧
    SystemInvN (encodeLabel nestedCanarySource) encodeConf nestedCanarySource ∧
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ),
      LocatedRun (encodeLabel nestedCanarySource) encodeConf label' C' ∧
      CleanRepresents label' C' nestedCanaryTargetN ∧
      SystemInvN label' C' nestedCanaryTargetN ∧
      BagStep conventional nestedCanarySource nestedCanaryTargetN := by
  have hNode : HostedNode nestedCanarySource :=
    .reflect ⟨by decide +kernel, by decide +kernel⟩ canarySource_hostedNode
  have anch : ∀ q ∈ [nestedZeroTerm, nestedVarY], SpineHasPattern q (predotU nestedCanarySource) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact .reflect _ (.reflect _ (.parLeft _ (.guard _ _)))
    · exact .reflect _ (.reflect _ (.parRight _ (.guard _ _)))
  have rep₀ := encode_cleanRepresentsBy hNode anch
  have sub₁ : HostedSubStepN 1 canarySource (pPar [canaryTargetN])
      (nestedZeroTerm, nestedVarY) nestedCanaryUnifier :=
    .reflect [] [] demoChan (.leaf _) (by decide +kernel) canaryInner_subStepN
  have ms : MultiSplits [(0, nestedCanarySource)] ([] ++ pReflect demoChan canarySource :: []) :=
    MultiSplits.of_map_snd rfl
  obtain ⟨label', C', rows', run, _, rep', bStep⟩ :=
    refl_step_forward_list_N rep₀ ms ⟨by decide +kernel, by decide +kernel⟩ sub₁
      (fun _ m => absurd m List.not_mem_nil) (fun _ m => absurd m List.not_mem_nil)
      (bagEq_pPar_singleton nestedCanaryTargetN)
  exact ⟨rep₀.toCleanRepresents, rep₀.toCleanRepresents.toSystemInvN,
    label', C', run, rep'.toCleanRepresents, rep'.toCleanRepresents.toSystemInvN, bStep⟩

/-- **Instance 2b (`C`)**: nested canary `@0?(@0?(for((0) <- @0)0 | for(y <- @0)y))` through
`source_step_forward_C`. -/
theorem instance_nested_refl_C :
    CleanRepresents (encodeLabel nestedCanarySource) encodeConf nestedCanarySource ∧
    SystemInvC (encodeLabel nestedCanarySource) encodeConf nestedCanarySource ∧
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ),
      LocatedRun (encodeLabel nestedCanarySource) encodeConf label' C' ∧
      CleanRepresents label' C' nestedCanaryTargetC ∧
      SystemInvC label' C' nestedCanaryTargetC ∧
      CanonicalBagStep conventional nestedCanarySource nestedCanaryTargetC := by
  have hNode : HostedNode nestedCanarySource :=
    .reflect ⟨by decide +kernel, by decide +kernel⟩ canarySource_hostedNode
  have anch : ∀ q ∈ [nestedZeroTerm, nestedVarY], SpineHasPattern q (predotU nestedCanarySource) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact .reflect _ (.reflect _ (.parLeft _ (.guard _ _)))
    · exact .reflect _ (.reflect _ (.parRight _ (.guard _ _)))
  have rep₀ := encode_cleanRepresentsBy hNode anch
  have sub₁ : HostedSubStepC 1 canarySource (pPar [canaryTargetC])
      (nestedZeroTerm, nestedVarY) nestedCanaryUnifier :=
    .reflect [] [] demoChan (.leaf _) (by decide +kernel) (fun _ m => absurd m List.not_mem_nil)
      canaryInner_subStepC
  have ms : MultiSplits [(0, nestedCanarySource)] ([] ++ pReflect demoChan canarySource :: []) :=
    MultiSplits.of_map_snd rfl
  obtain ⟨label', C', rows', run, _, rep', cStep⟩ :=
    refl_step_forward_list_C rep₀ ms ⟨by decide +kernel, by decide +kernel⟩ sub₁
      (fun _ m => absurd m List.not_mem_nil) (fun _ m => absurd m List.not_mem_nil)
      (bagEq_pPar_singleton nestedCanaryTargetC)
  exact ⟨rep₀.toCleanRepresents, rep₀.toCleanRepresents.toSystemInvC,
    label', C', run, rep'.toCleanRepresents, rep'.toCleanRepresents.toSystemInvC, cStep⟩

/-- **Instance 2c (`N`, open inner reduct)**: `@0?(@0?(for(a1 <- @0)a1 | for(0 <- @0)a))` — the
nested reflection with free variable `"a"` inside the inner reduct (`nested_reflection_missed` in
`Adequacy`), hosted to `CleanRepresents` and `SystemInvN`. -/
theorem instance_nested_open_refl_N :
    CleanRepresents (encodeLabel nestedOpenSource) encodeConf nestedOpenSource ∧
    SystemInvN (encodeLabel nestedOpenSource) encodeConf nestedOpenSource ∧
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ),
      LocatedRun (encodeLabel nestedOpenSource) encodeConf label' C' ∧
      CleanRepresents label' C' nestedOpenTargetN ∧
      SystemInvN label' C' nestedOpenTargetN ∧
      BagStep conventional nestedOpenSource nestedOpenTargetN := by
  have hNode : HostedNode nestedOpenSource :=
    .reflect ⟨by decide +kernel, by decide +kernel⟩
      (.reflect ⟨by decide +kernel, by decide +kernel⟩
        (.par (.guard ⟨by decide +kernel, by decide +kernel⟩)
              (.guard ⟨by decide +kernel, by decide +kernel⟩)))
  have anch : ∀ q ∈ [Pattern.fvar "a1", pZero], SpineHasPattern q (predotU nestedOpenSource) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact .reflect _ (.reflect _ (.parLeft _ (.guard _ _)))
    · exact .reflect _ (.reflect _ (.parRight _ (.guard _ _)))
  have rep₀ := encode_cleanRepresentsBy hNode anch
  have split₀ : Splits nestedOpenInner
      ([] ++ pFor (.fvar "a1") demoChan (.fvar "a1") :: ([] ++ pFor pZero demoChan (.fvar "a") :: [])) :=
    show Splits (par _ _) ([_] ++ [_]) from
      .split (.leaf (pFor (.fvar "a1") demoChan (.fvar "a1"))) (.leaf (pFor pZero demoChan (.fvar "a")))
  have plainA : PlainPatterns (applyDot nestedOpenUnifier (.fvar "a1")) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, nestedOpenUnifier, pZero, nQuote,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  have plainB : PlainPatterns (applyDot nestedOpenUnifier (.fvar "a")) := by
    simp [PlainPatterns, applyDot, nestedOpenUnifier, pZero, nQuote,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  have sub₀ : HostedSubStepN 0 nestedOpenInner
      (pPar [applyDot nestedOpenUnifier (.fvar "a1"), applyDot nestedOpenUnifier (.fvar "a")])
      (.fvar "a1", pZero) nestedOpenUnifier :=
    .comm [] [] [] (.fvar "a1") pZero demoChan (.fvar "a1") (.fvar "a") nestedOpenUnifier
      split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) plainA plainB nestedOpenUnifier_gp
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have sub₁ : HostedSubStepN 1 (pReflect demoChan nestedOpenInner) _ _ _ :=
    .reflect [] [] demoChan (.leaf _) (by decide +kernel) sub₀
  have ms : MultiSplits [(0, nestedOpenSource)]
      ([] ++ pReflect demoChan (pReflect demoChan nestedOpenInner) :: []) :=
    MultiSplits.of_map_snd rfl
  obtain ⟨label', C', rows', run, _, rep', bStep⟩ :=
    refl_step_forward_list_N rep₀ ms ⟨by decide +kernel, by decide +kernel⟩ sub₁
      (fun _ m => absurd m List.not_mem_nil) (fun _ m => absurd m List.not_mem_nil)
      (bagEq_pPar_singleton nestedOpenTargetN)
  exact ⟨rep₀.toCleanRepresents, rep₀.toCleanRepresents.toSystemInvN,
    label', C', run, rep'.toCleanRepresents, rep'.toCleanRepresents.toSystemInvN, bStep⟩

/-! ## Instance 3: Two concurrent reflections at different children -/

/-- Second ground channel `@@0` (`nQuote demoChan`), distinct modulo `NameLaws` from `@0`. -/
def demoChan2 : Pattern := nQuote demoChan

/-- Second canary body `for((0) <- @0)0 | for(z <- @0)z` with variable `"z"`. -/
def canaryVarZ : Pattern := .fvar "z"
def canaryUnifierZ : Bindings := [("z", nestedZeroTerm)]
def canaryInnerZ : Pattern :=
  par (pFor nestedZeroTerm demoChan pZero) (pFor canaryVarZ demoChan canaryVarZ)
def canaryReductZ : Pattern :=
  pPar [applyDot canaryUnifierZ pZero, applyDot canaryUnifierZ canaryVarZ]

/-- Concurrent two-reflection source `@0?(canary_y) | @@0?(canary_z)`. -/
def concurrentSource : Pattern :=
  par (pReflect demoChan nestedCanaryInner) (pReflect demoChan2 canaryInnerZ)

/-- Concurrent two-reflection target under **Interface N**. -/
def concurrentTargetN : Pattern :=
  pPar [canaryTargetN, pFor (tProc canaryReductZ) demoChan2 pZero]

/-- Concurrent two-reflection target under **Interface C**. -/
def concurrentTargetC : Pattern :=
  pPar [canaryTargetC, listener demoChan2 canaryReductZ]

theorem canaryUnifierZ_gp : GroundPrincipal nestedZeroTerm canaryVarZ canaryUnifierZ := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, ?_⟩
  · intro x mem
    have xEq : x = "z" := by
      simpa [nestedZeroTerm, canaryVarZ, tProc, pZero, pvars,
        MeTTaOperationsComm.pvars.pvarsList] using mem
    subst xEq; exact ⟨nestedZeroTerm, rfl, by decide +kernel⟩
  · intro σ solves x mem v found
    have xEq : x = "z" := by
      simpa [nestedZeroTerm, canaryVarZ, tProc, pZero, pvars,
        MeTTaOperationsComm.pvars.pvarsList] using mem
    subst xEq
    have vEq : v = nestedZeroTerm :=
      (by simpa [canaryUnifierZ, Bindings.lookup] using found : nestedZeroTerm = v).symm
    subst vEq
    exact solves.symm.trans (psubst_of_pvars_nil σ nestedZeroTerm (by decide +kernel))

private theorem canaryInnerZ_subStepN :
    HostedSubStepN 0 canaryInnerZ canaryReductZ (nestedZeroTerm, canaryVarZ) canaryUnifierZ := by
  have split₀ : Splits canaryInnerZ
      ([] ++ pFor nestedZeroTerm demoChan pZero :: ([] ++ pFor canaryVarZ demoChan canaryVarZ :: [])) :=
    show Splits (par _ _) ([_] ++ [_]) from
      .split (.leaf (pFor nestedZeroTerm demoChan pZero)) (.leaf (pFor canaryVarZ demoChan canaryVarZ))
  have plainA : PlainPatterns (applyDot canaryUnifierZ pZero) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, pZero,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
  have plainB : PlainPatterns (applyDot canaryUnifierZ canaryVarZ) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, canaryUnifierZ, canaryVarZ, nestedZeroTerm,
      tProc, pZero, nQuote, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  exact .comm [] [] [] nestedZeroTerm canaryVarZ demoChan pZero canaryVarZ canaryUnifierZ
    split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) plainA plainB canaryUnifierZ_gp
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem canaryInnerZ_subStepC :
    HostedSubStepC 0 canaryInnerZ canaryReductZ (nestedZeroTerm, canaryVarZ) canaryUnifierZ := by
  have split₀ : Splits canaryInnerZ
      ([] ++ pFor nestedZeroTerm demoChan pZero :: ([] ++ pFor canaryVarZ demoChan canaryVarZ :: [])) :=
    show Splits (par _ _) ([_] ++ [_]) from
      .split (.leaf (pFor nestedZeroTerm demoChan pZero)) (.leaf (pFor canaryVarZ demoChan canaryVarZ))
  have plainA : PlainPatterns (applyDot canaryUnifierZ pZero) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, pZero,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]
  have plainB : PlainPatterns (applyDot canaryUnifierZ canaryVarZ) := by
    simp [PlainPatterns, PlainPatternsList, applyDot, canaryUnifierZ, canaryVarZ, nestedZeroTerm,
      tProc, pZero, nQuote, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.dotBindings]
  exact .comm [] [] [] nestedZeroTerm canaryVarZ demoChan pZero canaryVarZ canaryUnifierZ
    split₀ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) plainA plainB canaryUnifierZ_gp
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun _ m => absurd m List.not_mem_nil)
    (by decide +kernel) (by decide +kernel)

theorem concurrentSource_hostedNode : HostedNode concurrentSource :=
  .par canarySource_hostedNode
    (.reflect ⟨by decide +kernel, by decide +kernel⟩
      (.par (.guard ⟨by decide +kernel, by decide +kernel⟩)
            (.guard ⟨by decide +kernel, by decide +kernel⟩)))

/-- **Instance 3a (`N`)**: full 2-reflection `LocatedRun` on `@0?(canary_y) | @@0?(canary_z)` under
**Interface N**, preserving `FreeOnPats` for `"z"` across `"y"`'s reflection. -/
theorem instance_concurrent_children_N :
    CleanRepresents (encodeLabel concurrentSource) encodeConf concurrentSource ∧
    SystemInvN (encodeLabel concurrentSource) encodeConf concurrentSource ∧
    ∃ (label₂ : ℕ → Pattern) (C₂ : Configuration Pattern ℕ),
      LocatedRun (encodeLabel concurrentSource) encodeConf label₂ C₂ ∧
      CleanRepresents label₂ C₂ concurrentTargetN ∧
      SystemInvN label₂ C₂ concurrentTargetN ∧
      Relation.ReflTransGen (BagStep conventional) concurrentSource concurrentTargetN := by
  have anch₀ : ∀ q ∈ [nestedZeroTerm, nestedVarY, nestedZeroTerm, canaryVarZ],
      SpineHasPattern q (predotU concurrentSource) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl | rfl | rfl
    · exact .parLeft _ (.reflect _ (.parLeft _ (.guard _ _)))
    · exact .parLeft _ (.reflect _ (.parRight _ (.guard _ _)))
    · exact .parRight _ (.reflect _ (.parLeft _ (.guard _ _)))
    · exact .parRight _ (.reflect _ (.parRight _ (.guard _ _)))
  have rep₀ := encode_cleanRepresentsBy concurrentSource_hostedNode anch₀
  have ms₀ : MultiSplits [(0, concurrentSource)]
      ([] ++ pReflect demoChan nestedCanaryInner :: [pReflect demoChan2 canaryInnerZ]) :=
    show MultiSplits [(0, par _ _)] (([_] ++ [_]) ++ []) from
      .cons (.split (.leaf _) (.leaf _)) .nil
  have disj₁ : ∀ q ∈ [nestedZeroTerm, canaryVarZ],
      ∀ v ∈ pvars q, v ∉ pvars nestedZeroTerm ++ pvars nestedVarY := by decide +kernel
  have anch₁ : ∀ q ∈ [nestedZeroTerm, canaryVarZ],
      ∃ c ∈ ([] : List Pattern) ++ [pReflect demoChan2 canaryInnerZ],
        SpineHasPattern q (predotU c) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact ⟨pReflect demoChan2 canaryInnerZ, by simp, .reflect _ (.parLeft _ (.guard _ _))⟩
    · exact ⟨pReflect demoChan2 canaryInnerZ, by simp, .reflect _ (.parRight _ (.guard _ _))⟩
  let midP := pPar [canaryTargetN, pReflect demoChan2 canaryInnerZ]
  obtain ⟨label₁, C₁, rows₁, run₁, map₁, rep₁, step₁⟩ :=
    refl_step_forward_list_N rep₀ ms₀ ⟨by decide +kernel, by decide +kernel⟩ canaryInner_subStepN
      disj₁ anch₁ (BagEq.refl midP)
  have ms₁ : MultiSplits rows₁
      ([canaryTargetN] ++ pReflect demoChan2 canaryInnerZ :: []) :=
    MultiSplits.of_map_snd map₁
  obtain ⟨label₂, C₂, rows₂, run₂, _, rep₂, step₂⟩ :=
    refl_step_forward_list_N rep₁ ms₁ ⟨by decide +kernel, by decide +kernel⟩ canaryInnerZ_subStepN
      (fun _ m => absurd m List.not_mem_nil) (fun _ m => absurd m List.not_mem_nil)
      (BagEq.refl concurrentTargetN)
  exact ⟨rep₀.toCleanRepresents, rep₀.toCleanRepresents.toSystemInvN,
    label₂, C₂, run₁.trans run₂, rep₂.toCleanRepresents, rep₂.toCleanRepresents.toSystemInvN,
    .tail (.tail .refl step₁) step₂⟩

/-- **Instance 3b (`C`)**: full 2-reflection `LocatedRun` on `@0?(canary_y) | @@0?(canary_z)` under
**Interface C**. -/
theorem instance_concurrent_children_C :
    CleanRepresents (encodeLabel concurrentSource) encodeConf concurrentSource ∧
    SystemInvC (encodeLabel concurrentSource) encodeConf concurrentSource ∧
    ∃ (label₂ : ℕ → Pattern) (C₂ : Configuration Pattern ℕ),
      LocatedRun (encodeLabel concurrentSource) encodeConf label₂ C₂ ∧
      CleanRepresents label₂ C₂ concurrentTargetC ∧
      SystemInvC label₂ C₂ concurrentTargetC ∧
      Relation.ReflTransGen (CanonicalBagStep conventional) concurrentSource concurrentTargetC := by
  have anch₀ : ∀ q ∈ [nestedZeroTerm, nestedVarY, nestedZeroTerm, canaryVarZ],
      SpineHasPattern q (predotU concurrentSource) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl | rfl | rfl
    · exact .parLeft _ (.reflect _ (.parLeft _ (.guard _ _)))
    · exact .parLeft _ (.reflect _ (.parRight _ (.guard _ _)))
    · exact .parRight _ (.reflect _ (.parLeft _ (.guard _ _)))
    · exact .parRight _ (.reflect _ (.parRight _ (.guard _ _)))
  have rep₀ := encode_cleanRepresentsBy concurrentSource_hostedNode anch₀
  have ms₀ : MultiSplits [(0, concurrentSource)]
      ([] ++ pReflect demoChan nestedCanaryInner :: [pReflect demoChan2 canaryInnerZ]) :=
    show MultiSplits [(0, par _ _)] (([_] ++ [_]) ++ []) from
      .cons (.split (.leaf _) (.leaf _)) .nil
  have disj₁ : ∀ q ∈ [nestedZeroTerm, canaryVarZ],
      ∀ v ∈ pvars q, v ∉ pvars nestedZeroTerm ++ pvars nestedVarY := by decide +kernel
  have anch₁ : ∀ q ∈ [nestedZeroTerm, canaryVarZ],
      ∃ c ∈ ([] : List Pattern) ++ [pReflect demoChan2 canaryInnerZ],
        SpineHasPattern q (predotU c) := by
    intro q m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact ⟨pReflect demoChan2 canaryInnerZ, by simp, .reflect _ (.parLeft _ (.guard _ _))⟩
    · exact ⟨pReflect demoChan2 canaryInnerZ, by simp, .reflect _ (.parRight _ (.guard _ _))⟩
  let midP := pPar [canaryTargetC, pReflect demoChan2 canaryInnerZ]
  obtain ⟨label₁, C₁, rows₁, run₁, map₁, rep₁, step₁⟩ :=
    refl_step_forward_list_C rep₀ ms₀ ⟨by decide +kernel, by decide +kernel⟩ canaryInner_subStepC
      disj₁ anch₁ (BagEq.refl midP)
  have ms₁ : MultiSplits rows₁
      ([canaryTargetC] ++ pReflect demoChan2 canaryInnerZ :: []) :=
    MultiSplits.of_map_snd map₁
  obtain ⟨label₂, C₂, rows₂, run₂, _, rep₂, step₂⟩ :=
    refl_step_forward_list_C rep₁ ms₁ ⟨by decide +kernel, by decide +kernel⟩ canaryInnerZ_subStepC
      (fun _ m => absurd m List.not_mem_nil) (fun _ m => absurd m List.not_mem_nil)
      (BagEq.refl concurrentTargetC)
  exact ⟨rep₀.toCleanRepresents, rep₀.toCleanRepresents.toSystemInvC,
    label₂, C₂, run₁.trans run₂, rep₂.toCleanRepresents, rep₂.toCleanRepresents.toSystemInvC,
    .tail (.tail .refl step₁) step₂⟩

/-! ## Concurrent diamond commutation at different child locations (`P2` + `P5`) -/

/-- Localization of `openRootAt` to its root-child footprint `Child(Root, x, p)`. -/
theorem openRoot_activeAtRootChild {O : Type*} [DecidableEq O]
    {label : O → Pattern} {C : Configuration Pattern O} {x p : Pattern} {r pr tk : O} {ρ : PSubst}
    (readsR : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r)) (psubst σ (atLoc (pReflect x p) rootLoc))) :
    ActiveAtRootChild x p label C (openRootAt ρ r pr tk) := by
  have childEq : ∀ {σ : PSubst},
      nameAction.Models σ ((openRootAt ρ r pr tk).information QN (embed label C)) →
      NameLaws (psubst σ x) (psubst σ x) ∧
      NameLaws (psubst σ (psubst ρ reflP)) (psubst σ p) ∧
      NameLaws (psubst σ (psubst ρ (childLoc rootLoc channelUnknown reflP)))
        (psubst σ (childLoc rootLoc x p)) := by
    intro σ s
    obtain ⟨chan, proc⟩ := open_reading label C x p r pr tk ρ readsR s
    refine ⟨NameLaws.refl _, proc, ?_⟩
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc, psubst_rootLoc, psubst_rootLoc]
    exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chan, proc⟩
  refine ⟨fun o oM σ s => ?_, fun t tM σ s => ?_, fun c cM pat cEq σ s => ?_⟩
  · have oEq : o = r := by simpa [openRootAt] using oM
    subst oEq; exact .inl (readsR σ s)
  · obtain ⟨_, proc, cEq⟩ := childEq s
    simp only [openRootAt, openRoot, List.mem_cons, List.not_mem_nil, or_false] at tM
    rcases tM with rfl | rfl
    · exact .inr (.inl ⟨psubst σ p, by
        rw [psubst_atLoc_any, psubst_atLoc_any]
        exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨proc, cEq⟩⟩)
    · exact .inr (.inr (.inl ⟨rootLoc, by
        rw [psubst_pendingTok, psubst_pendingTok, psubst_rootLoc, psubst_rootLoc]
        exact nameLaws_pendingTok_iff.mpr ⟨cEq, NameLaws.refl _⟩⟩))
  · obtain ⟨_, _, chLoc⟩ := childEq s
    simp only [openRootAt, openRoot, List.mem_cons, List.not_mem_nil, or_false] at cM
    rcases cM with rfl | rfl | rfl <;> cases cEq
    · exact .inl ⟨rootLoc, by
        rw [psubst_pendingTok, psubst_pendingTok, psubst_rootLoc, psubst_rootLoc]
        exact nameLaws_pendingTok_iff.mpr ⟨chLoc, NameLaws.refl _⟩⟩
    · exact .inr (.inl ⟨rootLoc, psubst σ (psubst ρ anyZ), by
        rw [psubst_doneTok, psubst_doneTok, psubst_rootLoc, psubst_rootLoc]
        exact nameLaws_doneTok_iff.mpr ⟨chLoc, NameLaws.refl _, NameLaws.refl _⟩⟩)
    · exact .inr (.inr ⟨psubst σ (psubst ρ anyY), by
        rw [psubst_atLoc_any, psubst_atLoc_any]
        exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, chLoc⟩⟩)

/-- Heated 2-row root label for `@0?(canary_y) | @@0?(canary_z)` at occurrences `1` and `2`. -/
def concurrentHeatedRows : ℕ → Pattern
  | 1 => atLoc (predotU (pReflect demoChan nestedCanaryInner)) rootLoc
  | 2 => atLoc (predotU (pReflect demoChan2 canaryInnerZ)) rootLoc
  | _ => pZero

/-- Heated 2-row root configuration `{1, 2}` with empty equation store. -/
def concurrentHeatedConf : Configuration Pattern ℕ := ⟨[], {1, 2}⟩

def openRename1 (v : String) : String := "open1_" ++ v
def openRename2 (v : String) : String := "open2_" ++ v

/-- Explicit `SystemInvBy` step across `openRootAt`, tracking the exact `rootRows` and appending
the newly opened `ActiveEntry` onto `active` (for both `StepRelN` and `StepRelC`). -/
theorem systemInvBy_openRootAt {O : Type*} [DecidableEq O] {StepRel : Pattern → Pattern → Prop}
    {label : O → Pattern} {C : Configuration Pattern O} {P x Q : Pattern}
    {rootRows : List (O × Pattern)} {active : List (ActiveEntry O)}
    (sys : SystemInvBy StepRel label C P rootRows active)
    {r₀ pr tk : O} {ρ : PSubst}
    (rMem : (r₀, pReflect x Q) ∈ rootRows) (hX : HostedChan x) (hQ : HostedNode Q)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (openRootAt ρ r₀ pr tk)) :
    SystemInvBy StepRel
      (res label C (openRootAt ρ r₀ pr tk)).label
      (resConf label C (openRootAt ρ r₀ pr tk)) P rootRows
      (active ++ [⟨rootLoc, x, Q, .root, hX, hQ, .pending tk [(pr, Q)]⟩]) := by
  obtain ⟨_, shapes, _, ⟨_, w, solved⟩, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have prNeTk : pr ≠ tk := by simpa [openRootAt] using shapes.2.1
  have zR : (atLoc (pReflect channelUnknown reflP) rootLoc, r₀) ∈
      (openRootAt ρ r₀ pr tk).rule.body.read.zip
        (openRootAt ρ r₀ pr tk).selection.read := by simp [openRootAt, openRoot]
  have rRefl : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label r₀)) (psubst σ (atLoc (pReflect x (predotU Q)) rootLoc)) := by
    intro σ s; have h := (sys.rootInv.rows _ rMem).2 σ s
    rwa [predotU_pReflect, predotU_ground x hX.1] at h
  have lEq : ∀ σ : PSubst, nameAction.Models σ (resConf label C (openRootAt ρ r₀ pr tk)).equations →
      NameLaws (psubst σ (psubst ρ (childLoc rootLoc channelUnknown reflP)))
        (psubst σ (childLoc rootLoc x (predotU Q))) := by
    intro σ s
    have h := (ReflLocatedStep.read_reads _ s zR).trans (rRefl σ (info_known _ s))
    simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at h
    obtain ⟨chEq, qEq⟩ := ReflLocatedStep.nameLaws_pReflect_iff.mp
      ((locatedFrame_name.atLoc_iff _ _ _ _).mp h).1
    rw [psubst_childLoc, psubst_childLoc, psubst_childLoc, psubst_rootLoc, psubst_rootLoc]
    exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chEq, qEq⟩
  obtain ⟨apartE, cleanPost⟩ := open_apart_and_clean sys admitted
    ReflLocatedStep.openRoot_checks.1 ReflLocatedStep.openRoot_checks.2 rfl rfl
    (by show ∀ t ∈ openRoot.body.read, "Z" ∉ pvars t; decide) (by decide) lEq
  have cNew : CellsU (childLoc rootLoc x (predotU Q)) rootLoc
      (res label C (openRootAt ρ r₀ pr tk)).label
      (resConf label C (openRootAt ρ r₀ pr tk)) tk [(pr, Q)] :=
    cellsU_of_open admitted rfl
      (fun σ s => (ReflCorrespondence.openRoot_reads label C x (predotU Q) r₀ pr tk ρ rRefl prNeTk s).2.1)
      (fun σ s => (ReflCorrespondence.openRoot_reads label C x (predotU Q) r₀ pr tk ρ rRefl prNeTk s).2.2)
      cleanPost
  let e_new : ActiveEntry O := ⟨rootLoc, x, Q, .root, hX, hQ, .pending tk [(pr, Q)]⟩
  have nonRoot : (openRootAt ρ r₀ pr tk).rule ≠ ReflLocated.atRule rootLoc FiniteProgram.commRule ∧
      (openRootAt ρ r₀ pr tk).rule ≠ ReflLocated.atRule rootLoc FiniteProgram.heatRule ∧
      (openRootAt ρ r₀ pr tk).rule ≠ ReflLocated.atRule rootLoc FiniteProgram.clearRule ∧
      (openRootAt ρ r₀ pr tk).rule ≠ ReflLocated.closeRoot := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
      { have c := congrArg (fun rl => rl.body.take.length) h
        simp [openRootAt, openRoot, ReflLocated.atRule, RuleInstance.map,
          FiniteProgram.commRule, FiniteProgram.heatRule, FiniteProgram.clearRule,
          ReflLocated.closeRoot] at c }
  refine ⟨⟨w, solved⟩, noRootTokens_preserved sys.noRootTok _ admitted,
    rootCells_keep_nonRoot sys.noRootTok sys.rootInv _ admitted nonRoot.1 nonRoot.2.1 nonRoot.2.2.1 nonRoot.2.2.2,
    sys.rootNodes, sys.rootBag, ?_, ?_, ?_⟩
  · intro e m; rcases List.mem_append.mp m with inA | inN
    · exact (active_keep_nonChildRule (sys.activeValid e inA) admitted (.inr (.inr (.inr (.inl rfl))))).1
    · simp only [List.mem_singleton] at inN; subst inN
      exact ⟨cNew, fun q qM => by simp only [List.mem_singleton] at qM; subst qM; exact hQ,
        bagEq_pPar_singleton Q⟩
  · rw [List.pairwise_append]
    refine ⟨sys.activeApart.imp (apartOn_mono _), List.pairwise_singleton _ _, fun e₁ inA e₂ inN => ?_⟩
    simp only [List.mem_singleton] at inN; subst inN; exact apartE e₁ inA
  · intro z zP; rcases ReflLocatedStep.result_row zP with made | ⟨old, -, -, -⟩
    · simp only [openRootAt, List.mem_cons, List.not_mem_nil, or_false] at made
      rcases made with rfl | rfl
      · exact .inr ⟨e_new, by simp [e_new], .inr (by simp [e_new, ActiveEntry.cells])⟩
      · exact .inr ⟨e_new, by simp [e_new], .inl (by simp [e_new, ActiveEntry.tok])⟩
    · rcases sys.presentCover z old with inR | ⟨e, inA, hE⟩
      · exact .inl inR
      · exact .inr ⟨e, List.mem_append_left _ inA, hE⟩

/-- **Instance 3c (`P2` + `P5` concurrent children commutation)**: from the heated 2-row root
configuration `{1, 2}` of `concurrentSource`, the sibling `openRootAt` firings
`f₁ = openRootAt (renameBy openRename1) 1 3 4` and `f₂ = openRootAt (renameBy openRename2) 2 5 6`
are **both** admitted, **commute in a strict diamond** via `commute_different_children` (yielding
syntactically equal `present` sets and `label` maps and logically equivalent knowledge stores), and
reach an explicit 2-active-child state (`active.length = 2`) satisfying both `SystemInvBy StepRelN`
and `SystemInvBy StepRelC` for `concurrentSource`! -/
theorem instance_concurrent_commute :
    let f₁ := openRootAt (renameBy openRename1) 1 3 4
    let f₂ := openRootAt (renameBy openRename2) 2 5 6
    (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed concurrentHeatedRows concurrentHeatedConf) f₁ ∧
    (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed concurrentHeatedRows concurrentHeatedConf) f₂ ∧
    (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed (res concurrentHeatedRows concurrentHeatedConf f₁).label
        (resConf concurrentHeatedRows concurrentHeatedConf f₁)) f₂ ∧
    (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed (res concurrentHeatedRows concurrentHeatedConf f₂).label
        (resConf concurrentHeatedRows concurrentHeatedConf f₂)) f₁ ∧
    (resConf (res concurrentHeatedRows concurrentHeatedConf f₁).label
        (resConf concurrentHeatedRows concurrentHeatedConf f₁) f₂).present =
      (resConf (res concurrentHeatedRows concurrentHeatedConf f₂).label
        (resConf concurrentHeatedRows concurrentHeatedConf f₂) f₁).present ∧
    (res (res concurrentHeatedRows concurrentHeatedConf f₁).label
        (resConf concurrentHeatedRows concurrentHeatedConf f₁) f₂).label =
      (res (res concurrentHeatedRows concurrentHeatedConf f₂).label
        (resConf concurrentHeatedRows concurrentHeatedConf f₂) f₁).label ∧
    (∀ σ : PSubst,
      nameAction.Models σ
        (resConf (res concurrentHeatedRows concurrentHeatedConf f₁).label
          (resConf concurrentHeatedRows concurrentHeatedConf f₁) f₂).equations ↔
      nameAction.Models σ
        (resConf (res concurrentHeatedRows concurrentHeatedConf f₂).label
          (resConf concurrentHeatedRows concurrentHeatedConf f₂) f₁).equations) ∧
    (∃ rootRows active, active.length = 2 ∧
      SystemInvBy StepRelN
        (res (res concurrentHeatedRows concurrentHeatedConf f₁).label
          (resConf concurrentHeatedRows concurrentHeatedConf f₁) f₂).label
        (resConf (res concurrentHeatedRows concurrentHeatedConf f₁).label
          (resConf concurrentHeatedRows concurrentHeatedConf f₁) f₂)
        concurrentSource rootRows active ∧
      SystemInvBy StepRelC
        (res (res concurrentHeatedRows concurrentHeatedConf f₁).label
          (resConf concurrentHeatedRows concurrentHeatedConf f₁) f₂).label
        (resConf (res concurrentHeatedRows concurrentHeatedConf f₁).label
          (resConf concurrentHeatedRows concurrentHeatedConf f₁) f₂)
        concurrentSource rootRows active) := by
  let f₁ := openRootAt (renameBy openRename1) 1 3 4
  let f₂ := openRootAt (renameBy openRename2) 2 5 6
  have cleanChild : ∀ x p : Pattern, Clean (childLoc rootLoc x p)
      concurrentHeatedRows concurrentHeatedConf := by
    intro x p o oIn σ _
    have oCases : o = 1 ∨ o = 2 := by simpa [concurrentHeatedConf] using oIn
    refine ⟨fun m' sm => ?_, fun m' c' sm => ?_, fun y sm => ?_⟩ <;>
      rcases oCases with rfl | rfl <;>
        simp only [concurrentHeatedRows, psubst_atLoc_any, psubst_rootLoc] at sm
    · exact absurd (nameLaws_heads sm) (by decide)
    · exact absurd (nameLaws_heads sm) (by decide)
    · exact absurd (nameLaws_heads sm) (by decide)
    · exact absurd (nameLaws_heads sm) (by decide)
    · rw [psubst_childLoc] at sm
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp sm).2.symm
    · rw [psubst_childLoc] at sm
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp sm).2.symm
  have fr₁ : f₁.Fresh QN (embed concurrentHeatedRows concurrentHeatedConf) := by
    show (ReflNames.nameFiring (openRootAtX (renameBy openRename1) 1 3 4)).Fresh QN _
    refine fresh_name (Comm.fresh_of_renaming _ (openRootAtX (renameBy openRename1) 1 3 4)
      openRename1 rfl (by decide +kernel) fun x xIn m mentions => ?_)
    rcases mentions with h | h | ⟨o, oIn, rfl⟩
    · simp [concurrentHeatedConf, embed] at h
    · simp [concurrentHeatedConf, embed] at h
    · have oCases : o = 1 ∨ o = 2 := by simpa [concurrentHeatedConf, embed] using oIn
      rcases oCases with rfl | rfl <;> revert x xIn <;> decide +kernel
  have fr₂ : f₂.Fresh QN (embed concurrentHeatedRows concurrentHeatedConf) := by
    show (ReflNames.nameFiring (openRootAtX (renameBy openRename2) 2 5 6)).Fresh QN _
    refine fresh_name (Comm.fresh_of_renaming _ (openRootAtX (renameBy openRename2) 2 5 6)
      openRename2 rfl (by decide +kernel) fun x xIn m mentions => ?_)
    rcases mentions with h | h | ⟨o, oIn, rfl⟩
    · simp [concurrentHeatedConf, embed] at h
    · simp [concurrentHeatedConf, embed] at h
    · have oCases : o = 1 ∨ o = 2 := by simpa [concurrentHeatedConf, embed] using oIn
      rcases oCases with rfl | rfl <;> revert x xIn <;> decide +kernel
  have r1 : ∀ σ : PSubst, nameAction.Models σ concurrentHeatedConf.equations →
      NameLaws (psubst σ (concurrentHeatedRows 1))
        (psubst σ (atLoc (pReflect demoChan (predotU nestedCanaryInner)) rootLoc)) := by
    intro σ _
    show NameLaws (psubst σ (atLoc (predotU (pReflect demoChan nestedCanaryInner)) rootLoc)) _
    rw [predotU_pReflect, predotU_ground demoChan (by decide +kernel)]; exact NameLaws.refl _
  have r2 : ∀ σ : PSubst, nameAction.Models σ concurrentHeatedConf.equations →
      NameLaws (psubst σ (concurrentHeatedRows 2))
        (psubst σ (atLoc (pReflect demoChan2 (predotU canaryInnerZ)) rootLoc)) := by
    intro σ _
    show NameLaws (psubst σ (atLoc (predotU (pReflect demoChan2 canaryInnerZ)) rootLoc)) _
    rw [predotU_pReflect, predotU_ground demoChan2 (by decide +kernel)]; exact NameLaws.refl _
  have adm₁ : (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed concurrentHeatedRows concurrentHeatedConf) f₁ :=
    openRoot_admitted concurrentHeatedRows concurrentHeatedConf demoChan
      (predotU nestedCanaryInner) 1 3 4 r1 (cleanChild _ _) (by simp [concurrentHeatedConf])
      (by decide) ⟨by simp [concurrentHeatedConf], by simp [concurrentHeatedConf]⟩
      (σ₀ := fun _ => none) (fun _ m => absurd m List.not_mem_nil) fr₁
  have adm₂ : (RuleSyntax.step QN ℕ QNE located).Admits
      (s := embed concurrentHeatedRows concurrentHeatedConf) f₂ :=
    openRoot_admitted concurrentHeatedRows concurrentHeatedConf demoChan2
      (predotU canaryInnerZ) 2 5 6 r2 (cleanChild _ _) (by simp [concurrentHeatedConf])
      (by decide) ⟨by simp [concurrentHeatedConf], by simp [concurrentHeatedConf]⟩
      (σ₀ := fun _ => none) (fun _ m => absurd m List.not_mem_nil) fr₂
  have fr₁₂ : f₂.Fresh QN (embed (res concurrentHeatedRows concurrentHeatedConf f₁).label
      (resConf concurrentHeatedRows concurrentHeatedConf f₁)) := by
    show (ReflNames.nameFiring (openRootAtX (renameBy openRename2) 2 5 6)).Fresh QN _
    refine fresh_name (Comm.fresh_of_renaming _ (openRootAtX (renameBy openRename2) 2 5 6)
      openRename2 rfl (by decide +kernel) fun x xIn m mentions => ?_)
    rcases mentions with h | h | ⟨o, oIn, rfl⟩
    · simp only [resConf, embed, concurrentHeatedConf] at h
      revert m h x xIn; decide +kernel
    · simp only [resConf, embed, concurrentHeatedConf] at h
      revert m h x xIn; decide +kernel
    · have oCases : o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 := by
        have p := (ReflCorrespondence.open_present concurrentHeatedRows concurrentHeatedConf
          (renameBy openRename1) 1 3 4 o).mp oIn
        simpa [concurrentHeatedConf, or_assoc] using p
      rcases oCases with rfl | rfl | rfl | rfl <;> revert x xIn <;> decide +kernel
  have fr₂₁ : f₁.Fresh QN (embed (res concurrentHeatedRows concurrentHeatedConf f₂).label
      (resConf concurrentHeatedRows concurrentHeatedConf f₂)) := by
    show (ReflNames.nameFiring (openRootAtX (renameBy openRename1) 1 3 4)).Fresh QN _
    refine fresh_name (Comm.fresh_of_renaming _ (openRootAtX (renameBy openRename1) 1 3 4)
      openRename1 rfl (by decide +kernel) fun x xIn m mentions => ?_)
    rcases mentions with h | h | ⟨o, oIn, rfl⟩
    · simp only [resConf, embed, concurrentHeatedConf] at h
      revert m h x xIn; decide +kernel
    · simp only [resConf, embed, concurrentHeatedConf] at h
      revert m h x xIn; decide +kernel
    · have oCases : o = 1 ∨ o = 2 ∨ o = 5 ∨ o = 6 := by
        have p := (ReflCorrespondence.open_present concurrentHeatedRows concurrentHeatedConf
          (renameBy openRename2) 2 5 6 o).mp oIn
        simpa [concurrentHeatedConf, or_assoc] using p
      rcases oCases with rfl | rfl | rfl | rfl <;> revert x xIn <;> decide +kernel
  let σJ : PSubst := fun v =>
    if v = "open1_X" then some demoChan
    else if v = "open1_P" then some (predotU nestedCanaryInner)
    else if v = "open2_X" then some demoChan2
    else if v = "open2_P" then some (predotU canaryInnerZ)
    else none
  have j1 : ∀ e ∈ f₁.information QN (embed concurrentHeatedRows concurrentHeatedConf),
      NameLaws (psubst σJ e.1) (psubst σJ e.2) := by decide +kernel
  have j2 : ∀ e ∈ f₂.information QN (embed concurrentHeatedRows concurrentHeatedConf),
      NameLaws (psubst σJ e.1) (psubst σJ e.2) := by decide +kernel
  have joint : ∃ σ : PSubst,
      nameAction.Models σ (f₁.information QN (embed concurrentHeatedRows concurrentHeatedConf)) ∧
      nameAction.Models σ (f₂.information QN (embed concurrentHeatedRows concurrentHeatedConf)) :=
    ⟨σJ, j1, j2⟩
  have apartLoc : ∀ σ : PSubst, nameAction.Models σ concurrentHeatedConf.equations →
      ¬ NameLaws (psubst σ (childLoc rootLoc demoChan (predotU nestedCanaryInner)))
        (psubst σ (childLoc rootLoc demoChan2 (predotU canaryInnerZ))) := by
    intro σ _ sm
    rw [psubst_childLoc, psubst_childLoc, psubst_of_pvars_nil σ demoChan (by decide +kernel),
      psubst_of_pvars_nil σ demoChan2 (by decide +kernel)] at sm
    exact absurd (nameLaws_childLoc_iff.mp sm).2.1 (by decide +kernel)
  obtain ⟨adm₁₂, adm₂₁, presEq, lblEq, eqsEq⟩ :=
    commute_different_children adm₁ adm₂ (openRoot_activeAtRootChild r1)
      (openRoot_activeAtRootChild r2) apartLoc (by decide) fr₁₂ fr₂₁ joint
  let startRows : List (ℕ × Pattern) :=
    [(1, pReflect demoChan nestedCanaryInner), (2, pReflect demoChan2 canaryInnerZ)]
  have hInnerY : HostedNode nestedCanaryInner :=
    .par (.guard ⟨by decide +kernel, by decide +kernel⟩)
         (.guard ⟨by decide +kernel, by decide +kernel⟩)
  have hInnerZ : HostedNode canaryInnerZ :=
    .par (.guard ⟨by decide +kernel, by decide +kernel⟩)
         (.guard ⟨by decide +kernel, by decide +kernel⟩)
  have sys₀ : ∀ (StepRel : Pattern → Pattern → Prop),
      SystemInvBy StepRel concurrentHeatedRows concurrentHeatedConf concurrentSource startRows [] := by
    intro StepRel
    refine ⟨⟨fun _ => none, fun _ m => absurd m List.not_mem_nil⟩,
      fun o oP σ _ => ?_,
      ⟨by decide, fun q qM => ?_, fun o oP notIn => ?_⟩,
      fun q qM => ?_,
      splits_bagEq (show Splits (par _ _) ([_] ++ [_]) from .split (.leaf _) (.leaf _)),
      fun _ m => absurd m List.not_mem_nil,
      List.Pairwise.nil,
      fun o oP => ?_⟩
    · have oC : o = 1 ∨ o = 2 := by simpa [concurrentHeatedConf] using oP
      refine ⟨fun _ sm => ?_, fun _ _ sm => ?_⟩ <;> rcases oC with rfl | rfl <;>
        { simp only [concurrentHeatedRows, psubst_atLoc_any] at sm
          exact absurd (nameLaws_heads sm) (by decide) }
    · simp only [startRows, List.mem_cons, List.not_mem_nil, or_false] at qM
      rcases qM with rfl | rfl
      · exact ⟨by simp [concurrentHeatedConf], fun _ _ => NameLaws.refl _⟩
      · exact ⟨by simp [concurrentHeatedConf], fun _ _ => NameLaws.refl _⟩
    · have oC : o = 1 ∨ o = 2 := by simpa [concurrentHeatedConf] using oP
      rcases oC with rfl | rfl <;> simp [startRows] at notIn
    · simp only [startRows, List.mem_cons, List.not_mem_nil, or_false] at qM
      rcases qM with rfl | rfl
      · exact canarySource_hostedNode
      · exact .reflect ⟨by decide +kernel, by decide +kernel⟩ hInnerZ
    · have oC : o = 1 ∨ o = 2 := by simpa [concurrentHeatedConf] using oP
      rcases oC with rfl | rfl <;> exact .inl (by simp [startRows])
  have sys₁N := systemInvBy_openRootAt (x := demoChan) (sys₀ StepRelN) (by simp [startRows])
    ⟨by decide +kernel, by decide +kernel⟩ hInnerY adm₁
  have sys₁₂N := systemInvBy_openRootAt (x := demoChan2) sys₁N (by simp [startRows])
    ⟨by decide +kernel, by decide +kernel⟩ hInnerZ adm₁₂
  have sys₁C := systemInvBy_openRootAt (x := demoChan) (sys₀ StepRelC) (by simp [startRows])
    ⟨by decide +kernel, by decide +kernel⟩ hInnerY adm₁
  have sys₁₂C := systemInvBy_openRootAt (x := demoChan2) sys₁C (by simp [startRows])
    ⟨by decide +kernel, by decide +kernel⟩ hInnerZ adm₁₂
  exact ⟨adm₁, adm₂, adm₁₂, adm₂₁, presEq, lblEq, eqsEq,
    startRows, _, rfl, sys₁₂N, sys₁₂C⟩

#print axioms instance_canary_N
#print axioms instance_canary_C
#print axioms instance_nested_refl_N
#print axioms instance_nested_refl_C
#print axioms instance_nested_open_refl_N
#print axioms instance_concurrent_children_N
#print axioms instance_concurrent_children_C
#print axioms openRoot_activeAtRootChild
#print axioms systemInvBy_openRootAt
#print axioms instance_concurrent_commute

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

