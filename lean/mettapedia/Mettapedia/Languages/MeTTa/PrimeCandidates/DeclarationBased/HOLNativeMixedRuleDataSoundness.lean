import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataShapes

/-!
# Reverse adequacy of mixed HOL/native rule-data execution

Canonical rule-data execution cannot leave the image of native terms.  Every
result returned from a canonical source decodes to a native term and is
authorized by the independently defined computational step relation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open DeclarationAwarePatternCodec DeclarationAwareSubstitutionLanguage
open Presentation NativeIndexedFamilies

theorem binding_rule_heads :
    ∀ rule ∈ Binding.rules, HasOperationHead bindingHeads rule.left := by decide

theorem pi_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmPi (m "a") (m "b")) output premises)
      (compute (encoded source))) :
    ∃ domain body, source = .pi domain body := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by native_match_correct)
  simp only [tmPi, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨domain, body, rfl, _, _⟩ := encoded_pi_inversion equation
  exact ⟨domain, body, rfl⟩

theorem sigma_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmSigma (m "a") (m "b")) output premises)
      (compute (encoded source))) :
    ∃ domain body, source = .sigma domain body := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by
      simp only [compute, tmSigma, m,
        Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux]
      rfl)
  simp only [tmSigma, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨domain, body, rfl, _, _⟩ := encoded_sigma_inversion equation
  exact ⟨domain, body, rfl⟩

theorem id_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmId (m "a") (m "b") (m "c")) output premises)
      (compute (encoded source))) :
    ∃ type left right, source = .id type left right := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by native_match_correct)
  simp only [tmId, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨type, left, right, rfl, _, _, _⟩ := encoded_id_inversion equation
  exact ⟨type, left, right, rfl⟩

theorem lam_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmLam (m "a")) output premises)
      (compute (encoded source))) :
    ∃ body, source = .lam body := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by native_match_correct)
  simp only [tmLam, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨body, rfl, _⟩ := encoded_lam_inversion equation
  exact ⟨body, rfl⟩

theorem app_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmApp (m "a") (m "b")) output premises)
      (compute (encoded source))) :
    ∃ function argument, source = .app function argument := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by native_match_correct)
  simp only [tmApp, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨function, argument, rfl, _, _⟩ := encoded_app_inversion equation
  exact ⟨function, argument, rfl⟩

theorem pair_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmPair (m "a") (m "b")) output premises)
      (compute (encoded source))) :
    ∃ first second, source = .pair first second := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by native_match_correct)
  simp only [tmPair, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨first, second, rfl, _, _⟩ := encoded_pair_inversion equation
  exact ⟨first, second, rfl⟩

theorem fst_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmFst (m "a")) output premises)
      (compute (encoded source))) :
    ∃ pair, source = .fst pair := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by native_match_correct)
  simp only [tmFst, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨pair, rfl, _⟩ := encoded_fst_inversion equation
  exact ⟨pair, rfl⟩

theorem snd_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmSnd (m "a")) output premises)
      (compute (encoded source))) :
    ∃ pair, source = .snd pair := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by native_match_correct)
  simp only [tmSnd, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨pair, rfl, _⟩ := encoded_snd_inversion equation
  exact ⟨pair, rfl⟩

theorem refl_context_match_shape {n : Nat} (source : Tower.Tm n)
    (name : String) (output : Pattern) (premises : List Premise) (bindings : Bindings)
    (matched : bindings ∈ matchPatternForRule language
      (computationRule name (tmRefl (m "a")) output premises)
      (compute (encoded source))) :
    ∃ value, source = .refl value := by
  have equation := matched_source_reconstruction source _ _ _ _ bindings matched
    (by native_match_correct)
  simp only [tmRefl, m, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
    List.map_cons, List.map_nil] at equation
  obtain ⟨value, rfl, _⟩ := encoded_refl_inversion equation
  exact ⟨value, rfl⟩

theorem execute_sound (fuel : Nat) {n : Nat} {source : Tower.Tm n} {target : Pattern}
    (result : target ∈ execute fuel (compute (encoded source))) :
    ∃ reduct : Tower.Tm n, target = encoded reduct ∧
      HOLNativeMixedOperationalDecomposition.ComputationalStep source reduct := by
  induction fuel generalizing n source target with
  | zero => cases result
  | succ fuel ih =>
      simp only [execute, rewriteAt, List.mem_flatMap] at result
      obtain ⟨rule, ruleMember, ruleResult⟩ := result
      have applied := ruleResult
      unfold applyRuleUsing at ruleResult
      rw [List.mem_flatMap] at ruleResult
      obtain ⟨bindings, matched, _⟩ := ruleResult
      change rule ∈ Binding.rules ++ computationRules at ruleMember
      rw [List.mem_append] at ruleMember
      cases ruleMember with
      | inl bindingMember =>
          rw [matchPatternForRule_eq_syntactic] at matched
          have noMatch := matchPattern_eq_nil_of_disjoint_operationHeads
            (binding_rule_heads rule bindingMember)
            (show HasOperationHead ["prime-tm-computes"] (compute (encoded source)) by
              simp [HasOperationHead, compute])
            (by decide)
          rw [noMatch] at matched
          exact (List.not_mem_nil matched).elim
      | inr computationMember =>
          change rule ∈ rootRules ++ contextRules at computationMember
          rw [List.mem_append] at computationMember
          cases computationMember with
          | inl rootMember =>
              simp only [rootRules, List.mem_cons, List.not_mem_nil, or_false] at rootMember
              rcases rootMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · change target ∈ executeRule (execute fuel) betaRule (encoded source) at applied
                obtain ⟨body, argument, rfl⟩ := beta_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) betaRule
                  (tmApp (tmLam (encoded body)) (encoded argument)) at applied
                rw [execute_betaRule (execute fuel) (encoded body) (encoded argument),
                  beta_service_unchanged] at applied
                have targetEq : target = encoded (inst0 argument body) := by
                  have exact := DeclarationAwareSubstitutionExecution.execute_substitute_exact
                    0 (DeclarationAwareSubstitutionSemantics.erase argument)
                    (DeclarationAwareSubstitutionSemantics.erase body) target
                  have computed := exact.mp ⟨fuel, by
                    simpa only [DeclarationAwareSubstitutionCompiler.encodeRaw,
                    DeclarationAwareSubstitutionSemantics.encode_erase, encoded, zero, encodeNat]
                      using applied⟩
                  have correct : encoded (inst0 argument body) =
                      DeclarationAwareSubstitutionCompiler.encodeRaw
                        (DeclarationAwareSubstitutionSemantics.substituteAt 0
                          (DeclarationAwareSubstitutionSemantics.erase argument)
                          (DeclarationAwareSubstitutionSemantics.erase body)) := by
                    simp only [DeclarationAwareSubstitutionCompiler.encodeRaw,
                      ← DeclarationAwareErasureNaturality.erase_inst0,
                      DeclarationAwareSubstitutionSemantics.encode_erase]
                  exact computed.trans correct.symm
                exact ⟨inst0 argument body, targetEq, .betaPi body argument⟩
              · change target ∈ executeRule (execute fuel) firstRule (encoded source) at applied
                obtain ⟨a, b, rfl⟩ := first_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) firstRule
                  (tmFst (tmPair (encoded a) (encoded b))) at applied
                rw [execute_firstRule (execute fuel) (encoded a) (encoded b)] at applied
                exact ⟨a, List.mem_singleton.mp applied, .betaSigmaFst a b⟩
              · change target ∈ executeRule (execute fuel) secondRule (encoded source) at applied
                obtain ⟨a, b, rfl⟩ := second_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) secondRule
                  (tmSnd (tmPair (encoded a) (encoded b))) at applied
                rw [execute_secondRule (execute fuel) (encoded a) (encoded b)] at applied
                exact ⟨b, List.mem_singleton.mp applied, .betaSigmaSnd a b⟩
              · change target ∈ executeRule (execute fuel) listNilRule (encoded source) at applied
                obtain ⟨a, p, z, s, rfl⟩ := listNil_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) listNilRule
                  (listEliminate (encoded a) (encoded p) (encoded z) (encoded s)
                    (nil (encoded a))) at applied
                rw [execute_listNilRule (execute fuel) (encoded a) (encoded p)
                  (encoded z) (encoded s)] at applied
                refine ⟨z, List.mem_singleton.mp applied, .root ?_⟩
                exact .inherited (.declared ⟨.list (.nil a p z s)⟩)
              · change target ∈ executeRule (execute fuel) listConsRule (encoded source) at applied
                obtain ⟨a, p, z, s, h, t, rfl⟩ := listCons_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) listConsRule
                  (listEliminate (encoded a) (encoded p) (encoded z) (encoded s)
                    (cons (encoded a) (encoded h) (encoded t))) at applied
                rw [execute_listConsRule (execute fuel) (encoded a) (encoded p)
                  (encoded z) (encoded s) (encoded h) (encoded t)] at applied
                have targetEq : target = encoded
                    (.app (.app (.app s h) t) (Intrinsic.eliminateApp a p z s t)) := by
                  exact (List.mem_singleton.mp applied).trans (by rfl)
                refine ⟨_, targetEq, .root ?_⟩
                exact .inherited (.declared ⟨.list (.cons a p z s h t)⟩)
              · change target ∈ executeRule (execute fuel) identityRule (encoded source) at applied
                obtain ⟨a, x, p, d, rfl⟩ := identity_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) identityRule
                  (identityEliminate (encoded a) (encoded x) (encoded p) (encoded d)
                    (encoded x) (tmRefl (encoded x))) at applied
                rw [execute_identityRule (execute fuel) (encoded a) (encoded x)
                  (encoded p) (encoded d)] at applied
                refine ⟨d, List.mem_singleton.mp applied, .root ?_⟩
                exact .inherited (.declared ⟨.list (.identity a x p d)⟩)
              · change target ∈ executeRule (execute fuel) relNilRule (encoded source) at applied
                obtain ⟨a, b, r, p, z, s, rfl⟩ := relNil_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) relNilRule
                  (relEliminate (encoded a) (encoded b) (encoded r) (encoded p)
                    (encoded z) (encoded s) (nil (encoded a)) (nil (encoded b))
                    (nilRel (encoded a) (encoded b) (encoded r))) at applied
                rw [execute_relNilRule (execute fuel) (encoded a) (encoded b)
                  (encoded r) (encoded p) (encoded z) (encoded s)] at applied
                refine ⟨z, List.mem_singleton.mp applied, .root ?_⟩
                exact .inherited (.declared ⟨.rel (.nil a b r p z s)⟩)
              · change target ∈ executeRule (execute fuel) relConsRule (encoded source) at applied
                obtain ⟨a, b, r, p, z, s, h, k, t, u, he, te, rfl⟩ :=
                  relCons_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) relConsRule
                  (relEliminate (encoded a) (encoded b) (encoded r) (encoded p)
                    (encoded z) (encoded s)
                    (cons (encoded a) (encoded h) (encoded t))
                    (cons (encoded b) (encoded k) (encoded u))
                    (consRel (encoded a) (encoded b) (encoded r) (encoded h)
                      (encoded k) (encoded t) (encoded u) (encoded he) (encoded te))) at applied
                rw [execute_relConsRule (execute fuel) (encoded a) (encoded b)
                  (encoded r) (encoded p) (encoded z) (encoded s) (encoded h)
                  (encoded k) (encoded t) (encoded u) (encoded he) (encoded te)] at applied
                have targetEq : target = encoded
                    (.app (.app (.app (.app (.app (.app (.app s h) k) t) u) he) te)
                      (IntrinsicRelator.eliminateApp a b r p z s t u te)) := by
                  exact (List.mem_singleton.mp applied).trans (by rfl)
                refine ⟨_, targetEq, .root ?_⟩
                exact .inherited (.declared ⟨.rel (.cons a b r p z s h k t u he te)⟩)
              · change target ∈ executeRule (execute fuel) implicationRule (encoded source) at applied
                obtain ⟨p, q, rfl⟩ := implication_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) implicationRule
                  (proof (implication (encoded p) (encoded q))) at applied
                rw [execute_implicationRule (execute fuel) (encoded p) (encoded q),
                  weaken_service_unchanged] at applied
                obtain ⟨lifted, liftedMember, rfl⟩ := List.mem_map.mp applied
                have liftedEq := (Binding.intrinsic_weaken_exact
                  (FormationSensitiveHOLProofFamily.proof q) lifted).mp
                  ⟨fuel, by
                    simpa only [zero, encodeNat, encoded, encodeTm,
                      FormationSensitiveHOLProofFamily.proof, proof, constant, tmConst, tmApp]
                      using liftedMember⟩
                subst lifted
                exact ⟨FormationSensitiveHOLProofFamily.implicationFamily p q, rfl,
                  .root (.declared (.implication p q))⟩
              · change target ∈ executeRule (execute fuel) universalRule (encoded source) at applied
                obtain ⟨a, f, rfl⟩ := universal_match_shape source bindings matched
                change target ∈ executeRule (execute fuel) universalRule
                  (proof (universal (encoded a) (encoded f))) at applied
                rw [execute_universalRule (execute fuel) (encoded a) (encoded f),
                  weaken_service_unchanged] at applied
                obtain ⟨lifted, liftedMember, rfl⟩ := List.mem_map.mp applied
                have liftedEq := (Binding.intrinsic_weaken_exact f lifted).mp
                  ⟨fuel, by simpa only [zero, encodeNat, encoded] using liftedMember⟩
                subst lifted
                exact ⟨FormationSensitiveHOLProofFamily.universalFamily a f, rfl,
                  .root (.declared (.universal a f))⟩
          | inr contextMember =>
              simp only [contextRules, List.mem_cons, List.not_mem_nil, or_false] at contextMember
              rcases contextMember with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨a, b, rfl⟩ := pi_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmPi (encoded a) (encoded b)) at applied
                simp only [tmPi] at applied
                rw [execute_context_binary_first (execute fuel)
                  "prime-context-pi-domain" "prime-tm-pi" (encoded a) (encoded b)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.pi reduct b, rfl, .congPiDom step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨a, b, rfl⟩ := pi_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmPi (encoded a) (encoded b)) at applied
                simp only [tmPi] at applied
                rw [execute_context_binary_second (execute fuel)
                  "prime-context-pi-body" "prime-tm-pi" (encoded a) (encoded b)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.pi a reduct, rfl, .congPiCod step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨a, b, rfl⟩ := sigma_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmSigma (encoded a) (encoded b)) at applied
                simp only [tmSigma] at applied
                rw [execute_context_binary_first (execute fuel)
                  "prime-context-sigma-domain" "prime-tm-sigma" (encoded a) (encoded b)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.sigma reduct b, rfl, .congSigmaDom step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨a, b, rfl⟩ := sigma_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmSigma (encoded a) (encoded b)) at applied
                simp only [tmSigma] at applied
                rw [execute_context_binary_second (execute fuel)
                  "prime-context-sigma-body" "prime-tm-sigma" (encoded a) (encoded b)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.sigma a reduct, rfl, .congSigmaCod step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨a, b, c, rfl⟩ := id_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmId (encoded a) (encoded b) (encoded c)) at applied
                simp only [tmId] at applied
                rw [execute_context_ternary_first (execute fuel)
                  "prime-context-id-type" "prime-tm-id" (encoded a) (encoded b) (encoded c)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.id reduct b c, rfl, .congIdTy step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨a, b, c, rfl⟩ := id_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmId (encoded a) (encoded b) (encoded c)) at applied
                simp only [tmId] at applied
                rw [execute_context_ternary_second (execute fuel)
                  "prime-context-id-left" "prime-tm-id" (encoded a) (encoded b) (encoded c)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.id a reduct c, rfl, .congIdLeft step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨a, b, c, rfl⟩ := id_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmId (encoded a) (encoded b) (encoded c)) at applied
                simp only [tmId] at applied
                rw [execute_context_ternary_third (execute fuel)
                  "prime-context-id-right" "prime-tm-id" (encoded a) (encoded b) (encoded c)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.id a b reduct, rfl, .congIdRight step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨body, rfl⟩ := lam_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmLam (encoded body)) at applied
                simp only [tmLam] at applied
                rw [execute_context_unary (execute fuel)
                  "prime-context-lambda" "prime-tm-lam" (encoded body)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.lam reduct, rfl, .congLam step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨function, argument, rfl⟩ := app_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmApp (encoded function) (encoded argument)) at applied
                simp only [tmApp] at applied
                rw [execute_context_binary_first (execute fuel)
                  "prime-context-app-function" "prime-tm-app"
                  (encoded function) (encoded argument)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.app reduct argument, rfl, .congAppFun step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨function, argument, rfl⟩ := app_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmApp (encoded function) (encoded argument)) at applied
                simp only [tmApp] at applied
                rw [execute_context_binary_second (execute fuel)
                  "prime-context-app-argument" "prime-tm-app"
                  (encoded function) (encoded argument)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.app function reduct, rfl, .congAppArg step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨first, second, rfl⟩ := pair_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmPair (encoded first) (encoded second)) at applied
                simp only [tmPair] at applied
                rw [execute_context_binary_first (execute fuel)
                  "prime-context-pair-first" "prime-tm-pair"
                  (encoded first) (encoded second)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.pair reduct second, rfl, .congPairFst step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨first, second, rfl⟩ := pair_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmPair (encoded first) (encoded second)) at applied
                simp only [tmPair] at applied
                rw [execute_context_binary_second (execute fuel)
                  "prime-context-pair-second" "prime-tm-pair"
                  (encoded first) (encoded second)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.pair first reduct, rfl, .congPairSnd step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨pair, rfl⟩ := fst_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmFst (encoded pair)) at applied
                simp only [tmFst] at applied
                rw [execute_context_unary (execute fuel)
                  "prime-context-first" "prime-tm-fst" (encoded pair)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.fst reduct, rfl, .congFst step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨pair, rfl⟩ := snd_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmSnd (encoded pair)) at applied
                simp only [tmSnd] at applied
                rw [execute_context_unary (execute fuel)
                  "prime-context-second" "prime-tm-snd" (encoded pair)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.snd reduct, rfl, .congSnd step⟩
              · change target ∈ executeRule (execute fuel) _ (encoded source) at applied
                obtain ⟨value, rfl⟩ := refl_context_match_shape source _ _ _ bindings matched
                change target ∈ executeRule (execute fuel) _
                  (tmRefl (encoded value)) at applied
                simp only [tmRefl] at applied
                rw [execute_context_unary (execute fuel)
                  "prime-context-refl" "prime-tm-refl" (encoded value)] at applied
                obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp applied
                obtain ⟨reduct, rfl, step⟩ := ih nextMember
                exact ⟨.refl reduct, rfl, .congRefl step⟩

theorem Computes.sound {n : Nat} {source : Tower.Tm n} {target : Pattern}
    (result : Computes (encoded source) target) :
    ∃ reduct : Tower.Tm n, target = encoded reduct ∧
      HOLNativeMixedOperationalDecomposition.ComputationalStep source reduct := by
  obtain ⟨fuel, member⟩ := result
  exact execute_sound fuel member

theorem Computes.encoded_iff {n : Nat} (source target : Tower.Tm n) :
    Computes (encoded source) (encoded target) ↔
      HOLNativeMixedOperationalDecomposition.ComputationalStep source target := by
  constructor
  · intro result
    obtain ⟨reduct, same, step⟩ := result.sound
    exact same_encoded_output rfl same |>.symm ▸ step
  · exact native_step_complete

theorem Computes.not_encoded_of_not_step {n : Nat} {source target : Tower.Tm n}
    (notStep : ¬ HOLNativeMixedOperationalDecomposition.ComputationalStep source target) :
    ¬ Computes (encoded source) (encoded target) :=
  fun computed ↦ notStep ((Computes.encoded_iff source target).mp computed)

theorem contextualStep_encoded_iff {n : Nat} (source target : Tower.Tm n) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
        (engineBasePremises RelationEnv.empty) language
        (compute (encoded source)) (encoded target) ↔
      HOLNativeMixedOperationalDecomposition.ComputationalStep source target :=
  (Computes.iff_contextualStep (encoded source) (encoded target)).symm.trans
    (Computes.encoded_iff source target)

theorem computes_derivation_sound {n : Nat} {source : Tower.Tm n} {target : Pattern}
    (path : Relation.ReflTransGen Computes (encoded source) target) :
    ∃ reduct : Tower.Tm n, target = encoded reduct ∧
      Relation.ReflTransGen HOLNativeMixedOperationalDecomposition.ComputationalStep
        source reduct := by
  have general : ∀ {left right : Pattern},
      Relation.ReflTransGen Computes left right →
      ∀ nativeSource : Tower.Tm n, left = encoded nativeSource →
        ∃ reduct : Tower.Tm n, right = encoded reduct ∧
          Relation.ReflTransGen
            HOLNativeMixedOperationalDecomposition.ComputationalStep
            nativeSource reduct := by
    intro left right generalPath
    induction generalPath using Relation.ReflTransGen.trans_induction_on with
    | refl value =>
        intro nativeSource sourceEq
        exact ⟨nativeSource, sourceEq, .refl⟩
    | single step =>
        intro nativeSource sourceEq
        rw [sourceEq] at step
        obtain ⟨reduct, targetEq, nativeStep⟩ := step.sound
        exact ⟨reduct, targetEq, .single nativeStep⟩
    | trans firstPath secondPath firstIH secondIH =>
        intro nativeSource sourceEq
        obtain ⟨middle, middleEq, nativeFirst⟩ := firstIH nativeSource sourceEq
        obtain ⟨reduct, targetEq, nativeSecond⟩ := secondIH middle middleEq
        exact ⟨reduct, targetEq, nativeFirst.trans nativeSecond⟩
  exact general path source rfl

theorem encoded_derivation_iff {n : Nat} (source target : Tower.Tm n) :
    Relation.ReflTransGen Computes (encoded source) (encoded target) ↔
      Relation.ReflTransGen HOLNativeMixedOperationalDecomposition.ComputationalStep
        source target := by
  constructor
  · intro path
    obtain ⟨reduct, same, nativePath⟩ := computes_derivation_sound path
    exact same_encoded_output rfl same |>.symm ▸ nativePath
  · exact native_derivation_complete

#print axioms binding_rule_heads
#print axioms pi_context_match_shape
#print axioms refl_context_match_shape
#print axioms execute_sound
#print axioms Computes.sound
#print axioms Computes.encoded_iff
#print axioms Computes.not_encoded_of_not_step
#print axioms contextualStep_encoded_iff
#print axioms computes_derivation_sound
#print axioms encoded_derivation_iff

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData
