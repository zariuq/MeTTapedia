import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataRoots

/-!
# Native computation paths executed by the mixed rule-data language

Every computational step of the unchanged mixed presentation, including
steps under native binders, is realized by a finite generic interpreter
derivation. Each binding call uses the authored substitution calculus.
The reverse adequacy direction is a separate obligation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open DeclarationAwarePatternCodec DeclarationAwareSubstitutionLanguage
open Presentation NativeIndexedFamilies

def Computes (source target : Pattern) : Prop :=
  ∃ fuel, target ∈ execute fuel (compute source)

abbrev encoded {n : Nat} (term : Tower.Tm n) : Pattern := encodeTm towerHeadCodec term

theorem root_available {rule : RewriteRule} (member : rule ∈ rootRules) :
    rule ∈ computationRules := List.mem_append_left _ member

theorem context_available {rule : RewriteRule} (member : rule ∈ contextRules) :
    rule ∈ computationRules := List.mem_append_right _ member

theorem Computes.unary {source target : Pattern} (step : Computes source target)
    (name constructor : String)
    (available : contextRule name (.apply constructor [m "a"]) (m "a")
      (.apply constructor [m "next"]) ∈ contextRules) :
    Computes (.apply constructor [source]) (.apply constructor [target]) := by
  obtain ⟨fuel, member⟩ := step
  refine ⟨fuel + 1, executeRule_inclusion fuel (context_available available) _ ?_⟩
  rw [execute_context_unary]
  exact List.mem_map.mpr ⟨target, member, rfl⟩

theorem Computes.binaryFirst {source target : Pattern} (step : Computes source target)
    (name constructor : String) (other : Pattern)
    (available : contextRule name (.apply constructor [m "a", m "b"]) (m "a")
      (.apply constructor [m "next", m "b"]) ∈ contextRules) :
    Computes (.apply constructor [source, other]) (.apply constructor [target, other]) := by
  obtain ⟨fuel, member⟩ := step
  refine ⟨fuel + 1, executeRule_inclusion fuel (context_available available) _ ?_⟩
  rw [execute_context_binary_first]
  exact List.mem_map.mpr ⟨target, member, rfl⟩

theorem Computes.binarySecond {source target : Pattern} (step : Computes source target)
    (name constructor : String) (other : Pattern)
    (available : contextRule name (.apply constructor [m "a", m "b"]) (m "b")
      (.apply constructor [m "a", m "next"]) ∈ contextRules) :
    Computes (.apply constructor [other, source]) (.apply constructor [other, target]) := by
  obtain ⟨fuel, member⟩ := step
  refine ⟨fuel + 1, executeRule_inclusion fuel (context_available available) _ ?_⟩
  rw [execute_context_binary_second]
  exact List.mem_map.mpr ⟨target, member, rfl⟩

theorem Computes.ternaryFirst {source target : Pattern} (step : Computes source target)
    (name constructor : String) (other₁ other₂ : Pattern)
    (available : contextRule name (.apply constructor [m "a", m "b", m "c"]) (m "a")
      (.apply constructor [m "next", m "b", m "c"]) ∈ contextRules) :
    Computes (.apply constructor [source, other₁, other₂])
      (.apply constructor [target, other₁, other₂]) := by
  obtain ⟨fuel, member⟩ := step
  refine ⟨fuel + 1, executeRule_inclusion fuel (context_available available) _ ?_⟩
  rw [execute_context_ternary_first]
  exact List.mem_map.mpr ⟨target, member, rfl⟩

theorem Computes.ternarySecond {source target : Pattern} (step : Computes source target)
    (name constructor : String) (other₁ other₂ : Pattern)
    (available : contextRule name (.apply constructor [m "a", m "b", m "c"]) (m "b")
      (.apply constructor [m "a", m "next", m "c"]) ∈ contextRules) :
    Computes (.apply constructor [other₁, source, other₂])
      (.apply constructor [other₁, target, other₂]) := by
  obtain ⟨fuel, member⟩ := step
  refine ⟨fuel + 1, executeRule_inclusion fuel (context_available available) _ ?_⟩
  rw [execute_context_ternary_second]
  exact List.mem_map.mpr ⟨target, member, rfl⟩

theorem Computes.ternaryThird {source target : Pattern} (step : Computes source target)
    (name constructor : String) (other₁ other₂ : Pattern)
    (available : contextRule name (.apply constructor [m "a", m "b", m "c"]) (m "c")
      (.apply constructor [m "a", m "b", m "next"]) ∈ contextRules) :
    Computes (.apply constructor [other₁, other₂, source])
      (.apply constructor [other₁, other₂, target]) := by
  obtain ⟨fuel, member⟩ := step
  refine ⟨fuel + 1, executeRule_inclusion fuel (context_available available) _ ?_⟩
  rw [execute_context_ternary_third]
  exact List.mem_map.mpr ⟨target, member, rfl⟩

theorem native_beta {n : Nat} (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    Computes (encoded (.app (.lam body) argument)) (encoded (inst0 argument body)) := by
  have result := DeclarationAwareSubstitutionExecution.execute_substitute_exact 0
    (DeclarationAwareSubstitutionSemantics.erase argument)
    (DeclarationAwareSubstitutionSemantics.erase body)
    (encoded (inst0 argument body))
  have existsResult : ∃ fuel, encoded (inst0 argument body) ∈
      Binding.execute fuel (Binding.substitute zero (encoded argument) (encoded body)) := by
    have correct : encoded (inst0 argument body) =
        DeclarationAwareSubstitutionCompiler.encodeRaw
          (DeclarationAwareSubstitutionSemantics.substituteAt 0
            (DeclarationAwareSubstitutionSemantics.erase argument)
            (DeclarationAwareSubstitutionSemantics.erase body)) := by
      simp only [DeclarationAwareSubstitutionCompiler.encodeRaw,
        ← DeclarationAwareErasureNaturality.erase_inst0,
        DeclarationAwareSubstitutionSemantics.encode_erase]
    simpa only [DeclarationAwareSubstitutionCompiler.encodeRaw,
      DeclarationAwareSubstitutionSemantics.encode_erase, encoded, zero, encodeNat]
      using result.mpr correct
  obtain ⟨fuel, result⟩ := existsResult
  refine ⟨fuel + 1, executeRule_inclusion fuel (rule := betaRule) (root_available (by simp [rootRules]))
    (tmApp (tmLam (encoded body)) (encoded argument)) ?_⟩
  rw [execute_betaRule, beta_service_unchanged]
  exact result

theorem native_first {n : Nat} (a b : Tower.Tm n) :
    Computes (encoded (.fst (.pair a b))) (encoded a) := by
  refine ⟨1, executeRule_inclusion 0 (rule := firstRule) (root_available (by simp [rootRules]))
    (tmFst (tmPair (encoded a) (encoded b))) ?_⟩
  rw [execute_firstRule]
  exact List.mem_singleton.mpr rfl

theorem native_second {n : Nat} (a b : Tower.Tm n) :
    Computes (encoded (.snd (.pair a b))) (encoded b) := by
  refine ⟨1, executeRule_inclusion 0 (rule := secondRule) (root_available (by simp [rootRules]))
    (tmSnd (tmPair (encoded a) (encoded b))) ?_⟩
  rw [execute_secondRule]
  exact List.mem_singleton.mpr rfl

macro "mixed_root_member" : tactic => `(tactic| (apply root_available; simp [rootRules]))

theorem native_list_nil {n : Nat} (a p z s : Tower.Tm n) :
    Computes (encoded (Intrinsic.eliminateApp a p z s (Intrinsic.nilApp a))) (encoded z) := by
  refine ⟨1, executeRule_inclusion 0 (rule := listNilRule) (by mixed_root_member)
    (listEliminate (encoded a) (encoded p) (encoded z) (encoded s) (nil (encoded a))) ?_⟩
  rw [execute_listNilRule]
  exact List.mem_singleton.mpr rfl

theorem native_list_cons {n : Nat} (a p z s h t : Tower.Tm n) :
    Computes (encoded (Intrinsic.eliminateApp a p z s (Intrinsic.consApp a h t)))
      (encoded (.app (.app (.app s h) t) (Intrinsic.eliminateApp a p z s t))) := by
  refine ⟨1, executeRule_inclusion 0 (rule := listConsRule) (by mixed_root_member)
    (listEliminate (encoded a) (encoded p) (encoded z) (encoded s)
      (cons (encoded a) (encoded h) (encoded t))) ?_⟩
  rw [execute_listConsRule]
  exact List.mem_singleton.mpr rfl

theorem native_identity {n : Nat} (a x p d : Tower.Tm n) :
    Computes (encoded (Intrinsic.identityEliminateApp a x p d x (.refl x))) (encoded d) := by
  refine ⟨1, executeRule_inclusion 0 (rule := identityRule) (by mixed_root_member)
    (identityEliminate (encoded a) (encoded x) (encoded p) (encoded d) (encoded x)
      (tmRefl (encoded x))) ?_⟩
  rw [execute_identityRule]
  exact List.mem_singleton.mpr rfl

theorem native_rel_nil {n : Nat} (a b r p z s : Tower.Tm n) :
    Computes (encoded (IntrinsicRelator.eliminateApp a b r p z s
      (Intrinsic.nilApp a) (Intrinsic.nilApp b) (IntrinsicRelator.nilRelApp a b r))) (encoded z) := by
  refine ⟨1, executeRule_inclusion 0 (rule := relNilRule) (by mixed_root_member)
    (relEliminate (encoded a) (encoded b) (encoded r) (encoded p) (encoded z) (encoded s)
      (nil (encoded a)) (nil (encoded b)) (nilRel (encoded a) (encoded b) (encoded r))) ?_⟩
  rw [execute_relNilRule]
  exact List.mem_singleton.mpr rfl

theorem native_rel_cons {n : Nat} (a b r p z s h k t u he te : Tower.Tm n) :
    Computes (encoded (IntrinsicRelator.eliminateApp a b r p z s
      (Intrinsic.consApp a h t) (Intrinsic.consApp b k u)
      (IntrinsicRelator.consRelApp a b r h k t u he te)))
      (encoded (.app (.app (.app (.app (.app (.app (.app s h) k) t) u) he) te)
        (IntrinsicRelator.eliminateApp a b r p z s t u te))) := by
  refine ⟨1, executeRule_inclusion 0 (rule := relConsRule) (by mixed_root_member)
    (relEliminate (encoded a) (encoded b) (encoded r) (encoded p) (encoded z) (encoded s)
      (cons (encoded a) (encoded h) (encoded t)) (cons (encoded b) (encoded k) (encoded u))
      (consRel (encoded a) (encoded b) (encoded r) (encoded h) (encoded k)
        (encoded t) (encoded u) (encoded he) (encoded te))) ?_⟩
  rw [execute_relConsRule]
  exact List.mem_singleton.mpr rfl

theorem native_implication {n : Nat} (p q : Tower.Tm n) :
    Computes (encoded (FormationSensitiveHOLProofFamily.proof
      (FormationSensitiveHOLUniformList.rawImp p q)))
      (encoded (FormationSensitiveHOLProofFamily.implicationFamily p q)) := by
  obtain ⟨fuel, result⟩ := (Binding.intrinsic_weaken_exact
    (FormationSensitiveHOLProofFamily.proof q)
    (encoded (rename wk (FormationSensitiveHOLProofFamily.proof q)))).mpr rfl
  refine ⟨fuel + 1, executeRule_inclusion fuel (rule := implicationRule) (by mixed_root_member)
    (proof (implication (encoded p) (encoded q))) ?_⟩
  rw [execute_implicationRule, weaken_service_unchanged]
  exact List.mem_map.mpr ⟨_, result, rfl⟩

theorem native_universal {n : Nat} (a f : Tower.Tm n) :
    Computes (encoded (FormationSensitiveHOLProofFamily.proof
      (FormationSensitiveHOLProofFamily.universalProposition a f)))
      (encoded (FormationSensitiveHOLProofFamily.universalFamily a f)) := by
  obtain ⟨fuel, result⟩ := (Binding.intrinsic_weaken_exact f (encoded (rename wk f))).mpr rfl
  refine ⟨fuel + 1, executeRule_inclusion fuel (rule := universalRule) (by mixed_root_member)
    (proof (universal (encoded a) (encoded f))) ?_⟩
  rw [execute_universalRule, weaken_service_unchanged]
  exact List.mem_map.mpr ⟨_, result, rfl⟩

theorem native_root {n : Nat} {source target : Tower.Tm n}
    (root : FormationSensitiveHOLProofListIntegration.rules.computation.step source target) :
    Computes (encoded source) (encoded target) := by
  cases root with
  | inherited native =>
    cases native with
    | inherited impossible => exact impossible.elim
    | delta lookup =>
      rw [HOLNativeMixedConversionCompletion.native_opaque] at lookup
      cases lookup
    | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      cases evidence with
      | list evidence =>
        cases evidence with
        | nil => exact native_list_nil _ _ _ _
        | cons => exact native_list_cons _ _ _ _ _ _
        | identity => exact native_identity _ _ _ _
      | rel evidence =>
        cases evidence with
        | nil => exact native_rel_nil _ _ _ _ _ _
        | cons => exact native_rel_cons _ _ _ _ _ _ _ _ _ _ _ _
  | delta lookup =>
    rw [FormationSensitiveHOLProofConversion.declarations_opaque] at lookup
    cases lookup
  | declared decoder =>
    cases decoder with
    | implication p q => exact native_implication p q
    | universal a f => exact native_universal a f

macro "mixed_context_member" : tactic =>
  `(tactic| simp [contextRules, tmPi, tmSigma, tmId, tmLam, tmApp,
    tmPair, tmFst, tmSnd, tmRefl])

theorem native_step_complete {n : Nat} {source target : Tower.Tm n}
    (step : HOLNativeMixedOperationalDecomposition.ComputationalStep source target) :
    Computes (encoded source) (encoded target) := by
  induction step with
  | betaPi body argument => exact native_beta body argument
  | betaSigmaFst a b => exact native_first a b
  | betaSigmaSnd a b => exact native_second a b
  | head impossible => exact impossible.elim
  | root evidence => exact native_root evidence
  | congPiDom _ ih =>
    exact ih.binaryFirst "prime-context-pi-domain" "prime-tm-pi" _ (by mixed_context_member)
  | congPiCod _ ih =>
    exact ih.binarySecond "prime-context-pi-body" "prime-tm-pi" _ (by mixed_context_member)
  | congSigmaDom _ ih =>
    exact ih.binaryFirst "prime-context-sigma-domain" "prime-tm-sigma" _ (by mixed_context_member)
  | congSigmaCod _ ih =>
    exact ih.binarySecond "prime-context-sigma-body" "prime-tm-sigma" _ (by mixed_context_member)
  | congIdTy _ ih =>
    exact ih.ternaryFirst "prime-context-id-type" "prime-tm-id" _ _ (by mixed_context_member)
  | congIdLeft _ ih =>
    exact ih.ternarySecond "prime-context-id-left" "prime-tm-id" _ _ (by mixed_context_member)
  | congIdRight _ ih =>
    exact ih.ternaryThird "prime-context-id-right" "prime-tm-id" _ _ (by mixed_context_member)
  | congLam _ ih =>
    exact ih.unary "prime-context-lambda" "prime-tm-lam" (by mixed_context_member)
  | congAppFun _ ih =>
    exact ih.binaryFirst "prime-context-app-function" "prime-tm-app" _ (by mixed_context_member)
  | congAppArg _ ih =>
    exact ih.binarySecond "prime-context-app-argument" "prime-tm-app" _ (by mixed_context_member)
  | congPairFst _ ih =>
    exact ih.binaryFirst "prime-context-pair-first" "prime-tm-pair" _ (by mixed_context_member)
  | congPairSnd _ ih =>
    exact ih.binarySecond "prime-context-pair-second" "prime-tm-pair" _ (by mixed_context_member)
  | congFst _ ih =>
    exact ih.unary "prime-context-first" "prime-tm-fst" (by mixed_context_member)
  | congSnd _ ih =>
    exact ih.unary "prime-context-second" "prime-tm-snd" (by mixed_context_member)
  | congRefl _ ih =>
    exact ih.unary "prime-context-refl" "prime-tm-refl" (by mixed_context_member)

theorem native_derivation_complete {n : Nat} {source target : Tower.Tm n}
    (path : Relation.ReflTransGen HOLNativeMixedOperationalDecomposition.ComputationalStep
      source target) :
    Relation.ReflTransGen Computes (encoded source) (encoded target) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (native_step_complete step)

theorem Computes.iff_contextualStep (source target : Pattern) :
    Computes source target ↔
      Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
        (engineBasePremises RelationEnv.empty) language (compute source) target :=
  exists_mem_rewriteAt_iff_step

#print axioms native_beta
#print axioms native_rel_cons
#print axioms native_implication
#print axioms native_universal
#print axioms native_root
#print axioms native_step_complete
#print axioms native_derivation_complete
#print axioms Computes.iff_contextualStep

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData
