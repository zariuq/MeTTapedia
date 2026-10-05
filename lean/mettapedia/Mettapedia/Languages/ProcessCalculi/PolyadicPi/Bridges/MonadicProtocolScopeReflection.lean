import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Basic
import Mettapedia.OSLF.Syntax.Strengthening

/-!
# Actual communication reflection through private-world reindexing

An existing partial inverse to a name reindexing reconstructs every actual
raw communication endpoint. Newly added unused private names cannot invent
a firing. The proof uses the shared strengthening and binder-substitution
laws; it does not choose another successful endpoint or assume reflection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.ScopeReflection

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

private theorem strengthen_par {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (first second : Proc Δ) :
    strengthenT inverse (par first second) =
      (strengthenT inverse first).bind fun left =>
        (strengthenT inverse second).map fun right => par left right := by
  simp only [par, strengthenT, strengthenA]
  dsimp only [Strengthener.liftS, liftRen]
  cases firstFound : strengthenT inverse first <;>
    cases secondFound : strengthenT inverse second <;> rfl

private theorem strengthen_out1 {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (channel datum : Name Δ) :
    strengthenT inverse (out1 channel datum) =
      (strengthenT inverse channel).bind fun oldChannel =>
        (strengthenT inverse datum).map fun oldDatum => out1 oldChannel oldDatum := by
  simp only [out1, strengthenT, strengthenA]
  dsimp only [Strengthener.liftS, liftRen]
  cases firstFound : strengthenT inverse channel <;>
    cases secondFound : strengthenT inverse datum <;> rfl

private theorem strengthen_inp1 {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (channel : Name Δ) (body : Proc (.nm :: Δ)) :
    strengthenT inverse (inp1 channel body) =
      (strengthenT inverse channel).bind fun oldChannel =>
        (strengthenT (inverse.liftS [.nm]) body).map fun oldBody => inp1 oldChannel oldBody := by
  simp only [inp1, strengthenT, strengthenA]
  dsimp only [Strengthener.liftS, liftRen]
  cases firstFound : strengthenT inverse channel <;>
    cases secondFound : strengthenT (inverse.liftS [.nm]) body <;>
    dsimp only [Strengthener.liftS, liftRen] at secondFound <;>
    rw [secondFound] <;> rfl

private theorem strengthen_out2 {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (channel first second : Name Δ) :
    strengthenT inverse (out2 channel first second) =
      (strengthenT inverse channel).bind fun oldChannel =>
        (strengthenT inverse first).bind fun oldFirst =>
          (strengthenT inverse second).map fun oldSecond => out2 oldChannel oldFirst oldSecond := by
  simp only [out2, strengthenT, strengthenA]
  dsimp only [Strengthener.liftS, liftRen]
  cases firstFound : strengthenT inverse channel <;>
    cases secondFound : strengthenT inverse first <;>
    cases thirdFound : strengthenT inverse second <;> rfl

private theorem strengthen_inp2 {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (channel : Name Δ) (body : Proc (.nm :: .nm :: Δ)) :
    strengthenT inverse (inp2 channel body) =
      (strengthenT inverse channel).bind fun oldChannel =>
        (strengthenT (inverse.liftS [.nm, .nm]) body).map fun oldBody => inp2 oldChannel oldBody := by
  simp only [inp2, strengthenT, strengthenA]
  dsimp only [Strengthener.liftS, liftRen]
  cases firstFound : strengthenT inverse channel <;>
    cases secondFound : strengthenT (inverse.liftS [.nm, .nm]) body <;>
    dsimp only [Strengthener.liftS, liftRen] at secondFound <;>
    rw [secondFound] <;> rfl

private theorem strengthen_nu {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (body : Proc (.nm :: Δ)) :
    strengthenT inverse (nu body) =
      (strengthenT (inverse.liftS [.nm]) body).map nu := by
  simp only [nu, strengthenT, strengthenA]
  dsimp only [Strengthener.liftS, liftRen]
  cases firstFound : strengthenT (inverse.liftS [.nm]) body <;>
    dsimp only [Strengthener.liftS, liftRen] at firstFound <;>
    rw [firstFound] <;> rfl

theorem par_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (first second : Proc Δ) {old : Proc Γ}
    (found : strengthenT inverse (par first second) = some old) :
    ∃ left right, strengthenT inverse first = some left ∧
      strengthenT inverse second = some right ∧ old = par left right := by
  cases left : strengthenT inverse first with
  | none => simp [strengthen_par, left] at found
  | some oldFirst =>
      cases right : strengthenT inverse second with
      | none => simp [strengthen_par, left, right] at found
      | some oldSecond =>
          simp [strengthen_par, left, right] at found
          exact ⟨oldFirst, oldSecond, rfl, rfl, found.symm⟩

theorem out1_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (channel datum : Name Δ) {old : Proc Γ}
    (found : strengthenT inverse (out1 channel datum) = some old) :
    ∃ oldChannel oldDatum, strengthenT inverse channel = some oldChannel ∧
      strengthenT inverse datum = some oldDatum ∧ old = out1 oldChannel oldDatum := by
  cases first : strengthenT inverse channel with
  | none => simp [strengthen_out1, first] at found
  | some oldChannel =>
      cases second : strengthenT inverse datum with
      | none => simp [strengthen_out1, first, second] at found
      | some oldDatum =>
          simp [strengthen_out1, first, second] at found
          exact ⟨oldChannel, oldDatum, rfl, rfl, found.symm⟩

theorem inp1_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (channel : Name Δ) (body : Proc (.nm :: Δ))
    {old : Proc Γ} (found : strengthenT inverse (inp1 channel body) = some old) :
    ∃ oldChannel oldBody, strengthenT inverse channel = some oldChannel ∧
      strengthenT (inverse.liftS [.nm]) body = some oldBody ∧ old = inp1 oldChannel oldBody := by
  cases first : strengthenT inverse channel with
  | none => simp [strengthen_inp1, first] at found
  | some oldChannel =>
      cases second : strengthenT (inverse.liftS [.nm]) body with
      | none => simp [strengthen_inp1, first, second] at found
      | some oldBody =>
          simp [strengthen_inp1, first, second] at found
          exact ⟨oldChannel, oldBody, rfl, rfl, found.symm⟩

theorem out2_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (channel first second : Name Δ) {old : Proc Γ}
    (found : strengthenT inverse (out2 channel first second) = some old) :
    ∃ oldChannel oldFirst oldSecond,
      strengthenT inverse channel = some oldChannel ∧
      strengthenT inverse first = some oldFirst ∧ strengthenT inverse second = some oldSecond ∧
      old = out2 oldChannel oldFirst oldSecond := by
  cases subject : strengthenT inverse channel with
  | none => simp [strengthen_out2, subject] at found
  | some oldChannel =>
      cases left : strengthenT inverse first with
      | none => simp [strengthen_out2, subject, left] at found
      | some oldFirst =>
          cases right : strengthenT inverse second with
          | none => simp [strengthen_out2, subject, left, right] at found
          | some oldSecond =>
              simp [strengthen_out2, subject, left, right] at found
              exact ⟨oldChannel, oldFirst, oldSecond, rfl, rfl, rfl, found.symm⟩

theorem inp2_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (channel : Name Δ) (body : Proc (.nm :: .nm :: Δ))
    {old : Proc Γ} (found : strengthenT inverse (inp2 channel body) = some old) :
    ∃ oldChannel oldBody, strengthenT inverse channel = some oldChannel ∧
      strengthenT (inverse.liftS [.nm, .nm]) body = some oldBody ∧ old = inp2 oldChannel oldBody := by
  cases first : strengthenT inverse channel with
  | none => simp [strengthen_inp2, first] at found
  | some oldChannel =>
      cases second : strengthenT (inverse.liftS [.nm, .nm]) body with
      | none => simp [strengthen_inp2, first, second] at found
      | some oldBody =>
          simp [strengthen_inp2, first, second] at found
          exact ⟨oldChannel, oldBody, rfl, rfl, found.symm⟩

private theorem nu_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (body : Proc (.nm :: Δ)) {old : Proc Γ}
    (found : strengthenT inverse (nu body) = some old) :
    ∃ oldBody, strengthenT (inverse.liftS [.nm]) body = some oldBody ∧ old = nu oldBody := by
  cases bodyFound : strengthenT (inverse.liftS [.nm]) body with
  | none => simp [strengthen_nu, bodyFound] at found
  | some oldBody =>
      simp [strengthen_nu, bodyFound] at found
      exact ⟨oldBody, rfl, found.symm⟩

private theorem strengthen_rep {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (body : Proc Δ) :
    strengthenT inverse (rep body) = (strengthenT inverse body).map rep := by
  simp only [rep, strengthenT, strengthenA]
  dsimp only [Strengthener.liftS, liftRen]
  cases recognized : strengthenT inverse body <;> rfl

private theorem rep_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (body : Proc Δ) {old : Proc Γ}
    (found : strengthenT inverse (rep body) = some old) :
    ∃ oldBody, strengthenT inverse body = some oldBody ∧ old = rep oldBody := by
  cases recognized : strengthenT inverse body with
  | none => simp [strengthen_rep, recognized] at found
  | some oldBody =>
      simp [strengthen_rep, recognized] at found
      exact ⟨oldBody, rfl, found.symm⟩

private theorem nil_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) {old : Proc Γ}
    (found : strengthenT inverse nil = some old) : old = nil := by
  simp only [nil, strengthenT, strengthenA, Option.map_some, Option.some.injEq] at found
  exact found.symm

private theorem weaken_found {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (body : Proc Δ) {old : Proc (.nm :: Γ)}
    (found : strengthenT (inverse.liftS [.nm]) (weaken body) = some old) :
    ∃ oldBody, strengthenT inverse body = some oldBody ∧ old = weaken oldBody := by
  have reconstructed := rename_strengthenT (inverse.liftS [.nm]) _ _ found
  have unused : countVar (Var.zero : Var (.nm :: Γ) .nm) old = 0 := by
    have reflected := countVar_rename_of_reflect (liftRen environment [.nm])
      (Var.zero : Var (.nm :: Γ) .nm) (by
        intro sort name
        cases name <;> rfl) old
    change countVar (Var.zero : Var (.nm :: Δ) .nm)
      (rename (liftRen environment [.nm]) old) = _ at reflected
    rw [reconstructed, countVar_zero_of_weaken] at reflected
    exact reflected.symm
  obtain ⟨oldBody, _, reading⟩ := exists_unweaken old unused
  have oldImage : rename environment oldBody = body := by
    have images : weaken (t := Srt.nm) (rename environment oldBody) =
        weaken (t := Srt.nm) body := by
      rw [← rename_weaken, reading]
      exact reconstructed
    exact rename_injective (Strengthener.ofWeaken sig Srt.nm) images
  refine ⟨oldBody, ?_, reading.symm⟩
  rw [← oldImage, strengthenT_rename]

private def ImageReflection {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (source target : Proc Δ) : Prop :=
  ∀ oldSource, strengthenT inverse source = some oldSource →
    ∃ oldTarget, StructuralEq oldSource oldTarget ∧
      strengthenT inverse target = some oldTarget

private theorem reflect_par_comm {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (first second : Proc Δ) :
    ImageReflection inverse (par first second) (par second first) := by
  intro oldSource found
  obtain ⟨oldFirst, oldSecond, firstFound, secondFound, rfl⟩ := par_found inverse _ _ found
  refine ⟨par oldSecond oldFirst, .parComm _ _, ?_⟩
  rw [strengthen_par, secondFound, firstFound]
  rfl

private theorem reflect_nu_unused {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (body : Proc Δ) :
    ImageReflection inverse (nu (weaken body)) body ∧
      ImageReflection inverse body (nu (weaken body)) := by
  constructor
  · intro oldSource found
    obtain ⟨oldBody, bodyFound, rfl⟩ := nu_found inverse _ found
    obtain ⟨oldTerm, termFound, rfl⟩ := weaken_found inverse _ bodyFound
    exact ⟨oldTerm, .nuUnused _, termFound⟩
  · intro oldSource found
    refine ⟨nu (weaken oldSource), .symm (.nuUnused _), ?_⟩
    have image := rename_strengthenT inverse _ _ found
    have targetImage : rename environment (nu (weaken oldSource)) = nu (weaken body) := by
      rw [rename_nu, rename_weaken, image]
    rw [← targetImage, strengthenT_rename]

private theorem reflect_nu_par {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (body : Proc (.nm :: Δ)) (frame : Proc Δ) :
    ImageReflection inverse (par (nu body) frame) (nu (par body (weaken frame))) ∧
      ImageReflection inverse (nu (par body (weaken frame))) (par (nu body) frame) := by
  constructor
  · intro oldSource found
    obtain ⟨oldScope, oldFrame, scopeFound, frameFound, rfl⟩ := par_found inverse _ _ found
    obtain ⟨oldBody, bodyFound, rfl⟩ := nu_found inverse _ scopeFound
    refine ⟨nu (par oldBody (weaken oldFrame)), .nuPar _ _, ?_⟩
    have targetImage : rename environment (nu (par oldBody (weaken oldFrame))) =
        nu (par body (weaken frame)) := by
      rw [rename_nu, rename_par, rename_weaken,
        rename_strengthenT (inverse.liftS [.nm]) _ _ bodyFound,
        rename_strengthenT inverse _ _ frameFound]
    rw [← targetImage, strengthenT_rename]
  · intro oldSource found
    obtain ⟨oldScoped, scopedFound, rfl⟩ := nu_found inverse _ found
    obtain ⟨oldBody, oldFrame, bodyFound, frameFound, rfl⟩ :=
      par_found (inverse.liftS [.nm]) _ _ scopedFound
    obtain ⟨originalFrame, originalFound, rfl⟩ := weaken_found inverse _ frameFound
    refine ⟨par (nu oldBody) originalFrame, .symm (.nuPar _ _), ?_⟩
    rw [strengthen_par, strengthen_nu, bodyFound, originalFound]
    rfl

private theorem reflect_nu_swap {Γ Δ : Ctx sig} {environment : Ren sig Γ Δ}
    (inverse : Strengthener environment) (body : Proc (.nm :: .nm :: Δ)) :
    ImageReflection inverse (nu (nu body)) (nu (nu (rename swapRen body))) := by
  intro oldSource found
  obtain ⟨oldScope, scopeFound, rfl⟩ := nu_found inverse _ found
  obtain ⟨oldBody, bodyFound, rfl⟩ := nu_found (inverse.liftS [.nm]) _ scopeFound
  refine ⟨nu (nu (rename swapRen oldBody)), .nuSwap _, ?_⟩
  have image := rename_strengthenT ((inverse.liftS [.nm]).liftS [.nm]) _ _ bodyFound
  have targetImage : rename environment (nu (nu (rename swapRen oldBody))) =
      nu (nu (rename swapRen body)) := by
    simp only [rename_nu]
    rw [liftRen_two, rename_exchange_lift]
    rw [← liftRen_two environment Srt.nm Srt.nm, image]
  rw [← targetImage, strengthenT_rename]

/-- Successful source strengthening reconstructs the supplied actual target
step and its exact target. Binder lifts reconstruct locally received names. -/
theorem strengthen_actual_step {Δ : Ctx sig} {source target : Proc Δ}
    (step : Step source target) :
    ∀ {Γ : Ctx sig} {environment : Ren sig Γ Δ} (inverse : Strengthener environment)
      {oldSource : Proc Γ}, strengthenT inverse source = some oldSource →
      ∃ oldTarget, Step oldSource oldTarget ∧ strengthenT inverse target = some oldTarget := by
  induction step with
  | comm1 channel datum body =>
      intro Γ environment inverse oldSource found
      obtain ⟨output, input, outputFound, inputFound, rfl⟩ := par_found inverse _ _ found
      obtain ⟨oldChannel, oldDatum, channelFound, datumFound, rfl⟩ :=
        out1_found inverse _ _ outputFound
      obtain ⟨inputChannel, oldBody, inputChannelFound, bodyFound, rfl⟩ :=
        inp1_found inverse _ _ inputFound
      have subjects : inputChannel = oldChannel := by
        exact Option.some.inj (inputChannelFound.symm.trans channelFound)
      subst inputChannel
      refine ⟨inst oldBody oldDatum, .comm1 _ _ _, ?_⟩
      have reconstructed : rename environment (inst oldBody oldDatum) = inst body datum := by
        rw [rename_inst, rename_strengthenT (inverse.liftS [.nm]) _ _ bodyFound,
          rename_strengthenT inverse _ _ datumFound]
      rw [← reconstructed, strengthenT_rename]
  | comm2 channel first second body =>
      intro Γ environment inverse oldSource found
      obtain ⟨output, input, outputFound, inputFound, rfl⟩ := par_found inverse _ _ found
      obtain ⟨oldChannel, oldFirst, oldSecond, channelFound, firstFound, secondFound, rfl⟩ :=
        out2_found inverse _ _ _ outputFound
      obtain ⟨inputChannel, oldBody, inputChannelFound, bodyFound, rfl⟩ :=
        inp2_found inverse _ _ inputFound
      have subjects : inputChannel = oldChannel := by
        exact Option.some.inj (inputChannelFound.symm.trans channelFound)
      subst inputChannel
      refine ⟨openPair oldBody oldFirst oldSecond, .comm2 _ _ _ _, ?_⟩
      have reconstructed : rename environment (openPair oldBody oldFirst oldSecond) =
          openPair body first second := by
        rw [rename_openPair, rename_strengthenT (inverse.liftS [.nm, .nm]) _ _ bodyFound,
          rename_strengthenT inverse _ _ firstFound, rename_strengthenT inverse _ _ secondFound]
      rw [← reconstructed, strengthenT_rename]
  | parL frame firing ih =>
      intro Γ environment inverse oldSource found
      obtain ⟨active, oldFrame, activeFound, frameFound, rfl⟩ := par_found inverse _ _ found
      obtain ⟨next, reflected, nextFound⟩ := ih inverse activeFound
      refine ⟨par next oldFrame, .parL _ reflected, ?_⟩
      rw [strengthen_par, nextFound, frameFound]
      rfl
  | parR frame firing ih =>
      intro Γ environment inverse oldSource found
      obtain ⟨oldFrame, active, frameFound, activeFound, rfl⟩ := par_found inverse _ _ found
      obtain ⟨next, reflected, nextFound⟩ := ih inverse activeFound
      refine ⟨par oldFrame next, .parR _ reflected, ?_⟩
      rw [strengthen_par, nextFound, frameFound]
      rfl
  | nu firing ih =>
      intro Γ environment inverse oldSource found
      obtain ⟨oldBody, bodyFound, rfl⟩ := nu_found inverse _ found
      obtain ⟨next, reflected, nextFound⟩ := ih (inverse.liftS [.nm]) bodyFound
      refine ⟨nu next, .nu reflected, ?_⟩
      rw [strengthen_nu, nextFound]
      rfl

/-- Every actual execution step in an injective private-world image reflects
to an original step. The supplied endpoint is reconstructed exactly. -/
theorem reindexed_actual_step {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (inverse : Strengthener environment) (source : Proc Γ) {target : Proc Δ}
    (step : Step (rename environment source) target) :
    ∃ oldTarget, Step source oldTarget ∧ rename environment oldTarget = target := by
  obtain ⟨oldTarget, reflected, recognized⟩ :=
    strengthen_actual_step step inverse (strengthenT_rename inverse source)
  exact ⟨oldTarget, reflected, rename_strengthenT inverse _ _ recognized⟩

/-- Adding a fresh unused binder cannot create new raw communications or
change the result carried back across that binder. -/
theorem fresh_prefix_actual_step {Γ : Ctx sig} (binders : Ctx sig) (source : Proc Γ)
    {target : Proc (binders ++ Γ)}
    (step : Step (rename (fun _ name => weakenVar binders name) source) target) :
    ∃ oldTarget, Step source oldTarget ∧
      rename (fun _ name => weakenVar binders name) oldTarget = target :=
  reindexed_actual_step _ (Strengthener.ofWeakenPrefix sig binders) source step

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.ScopeReflection
