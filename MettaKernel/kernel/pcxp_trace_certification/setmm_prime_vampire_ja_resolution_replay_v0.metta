; ============================================================================
; setmm_prime_vampire_ja_resolution_replay_v0.metta
; GENERATED from Vampire's TSTP proof by the independent adapter.
; The exact four-step refutation is replayed first.  Its Horn fragment is
; then normalized by two unit-resolution steps into a direct proof term,
; which is accepted only by Prime's unchanged type checker.
; ============================================================================

!(import! &self lib_atp)

!(bind! &v-rule-d1 ((ATP.Neg (proved (imp (ATP.Var vr0_v0) (imp (ATP.Var vr0_v1) (ATP.Var vr0_v2))))) (ATP.Pos (proved (imp (ATP.Var vr0_v0) (ATP.Var vr0_v2)))) (ATP.Neg (proved (imp (neg (ATP.Var vr0_v1)) (ATP.Var vr0_v2))))))
!(bind! &v-rule-imim2i ((ATP.Pos (proved (imp (imp (ATP.Var vr1_v0) (ATP.Var vr1_v1)) (imp (ATP.Var vr1_v0) (ATP.Var vr1_v2))))) (ATP.Neg (proved (imp (ATP.Var vr1_v1) (ATP.Var vr1_v2))))))
!(bind! &v-h1 ((ATP.Pos (proved (imp (neg f_ph_183) f_ch_183)))))
!(bind! &v-h2 ((ATP.Pos (proved (imp f_ps_183 f_ch_183)))))
!(bind! &v-goal-negative ((ATP.Neg (proved (imp (imp f_ph_183 f_ps_183) f_ch_183)))))
!(bind! &v-combined ((ATP.Pos (proved (imp (imp (ATP.Var vr1_v0) (ATP.Var vr1_v1)) (ATP.Var vr1_v2)))) (ATP.Neg (proved (imp (neg (ATP.Var vr1_v0)) (ATP.Var vr1_v2)))) (ATP.Neg (proved (imp (ATP.Var vr1_v1) (ATP.Var vr1_v2))))))
!(bind! &v-after-goal ((ATP.Neg (proved (imp (neg f_ph_183) f_ch_183))) (ATP.Neg (proved (imp f_ps_183 f_ch_183)))))
!(bind! &v-after-h1 ((ATP.Neg (proved (imp f_ps_183 f_ch_183)))))
!(bind! &v-empty ())
!(bind! &v-direct-h1 ((ATP.Pos (proved (imp (imp f_ph_183 (ATP.Var vr1_v1)) f_ch_183))) (ATP.Neg (proved (imp (ATP.Var vr1_v1) f_ch_183)))))
!(bind! &v-direct-target ((ATP.Pos (proved (imp (imp f_ph_183 f_ps_183) f_ch_183)))))

!(assertEqual
  (atp:resolution:check-step
    &v-rule-d1 &v-rule-imim2i
    (ATP.Subst ((ATP.Bind vr0_v0 (imp (ATP.Var vr1_v0) (ATP.Var vr1_v1))) (ATP.Bind vr0_v1 (ATP.Var vr1_v0)) (ATP.Bind vr0_v2 (ATP.Var vr1_v2))))
    (ATP.Neg (proved (imp (ATP.Var vr0_v0) (imp (ATP.Var vr0_v1) (ATP.Var vr0_v2)))))
    (ATP.Pos (proved (imp (imp (ATP.Var vr1_v0) (ATP.Var vr1_v1)) (imp (ATP.Var vr1_v0) (ATP.Var vr1_v2)))))
    &v-combined)
  True)

!(assertEqual
  (atp:resolution:check-step
    &v-combined &v-goal-negative
    (ATP.Subst ((ATP.Bind vr1_v0 f_ph_183) (ATP.Bind vr1_v1 f_ps_183) (ATP.Bind vr1_v2 f_ch_183)))
    (ATP.Pos (proved (imp (imp (ATP.Var vr1_v0) (ATP.Var vr1_v1)) (ATP.Var vr1_v2))))
    (ATP.Neg (proved (imp (imp f_ph_183 f_ps_183) f_ch_183)))
    &v-after-goal)
  True)

!(assertEqual
  (atp:resolution:check-step
    &v-after-goal &v-h1
    (ATP.Subst ())
    (ATP.Neg (proved (imp (neg f_ph_183) f_ch_183)))
    (ATP.Pos (proved (imp (neg f_ph_183) f_ch_183)))
    &v-after-h1)
  True)

!(assertEqual
  (atp:resolution:check-step
    &v-after-h1 &v-h2
    (ATP.Subst ())
    (ATP.Neg (proved (imp f_ps_183 f_ch_183)))
    (ATP.Pos (proved (imp f_ps_183 f_ch_183)))
    &v-empty)
  True)

; Certificate-preserving Horn normalization of the same refutation.
!(assertEqual
  (atp:resolution:check-step
    &v-combined &v-h1
    (ATP.Subst ((ATP.Bind vr1_v0 f_ph_183) (ATP.Bind vr1_v2 f_ch_183)))
    (ATP.Neg (proved (imp (neg (ATP.Var vr1_v0)) (ATP.Var vr1_v2))))
    (ATP.Pos (proved (imp (neg f_ph_183) f_ch_183)))
    &v-direct-h1)
  True)

!(assertEqual
  (atp:resolution:check-step
    &v-direct-h1 &v-h2
    (ATP.Subst ((ATP.Bind vr1_v1 f_ps_183)))
    (ATP.Neg (proved (imp (ATP.Var vr1_v1) f_ch_183)))
    (ATP.Pos (proved (imp f_ps_183 f_ch_183)))
    &v-direct-target)
  True)

; Negative: the empty clause cannot be replaced by a forged unit.
!(assertEqual
  (atp:resolution:check-step
    &v-after-h1 &v-h2 (ATP.Subst ())
    (ATP.Neg (proved (imp f_ps_183 f_ch_183)))
    (ATP.Pos (proved (imp f_ps_183 f_ch_183)))
    ((ATP.Pos (proved forged))))
  False)

; Negative: dropping a unifier binding invalidates the first step.
!(assertEqual
  (atp:resolution:check-step
    &v-rule-d1 &v-rule-imim2i (ATP.Subst ((ATP.Bind vr0_v0 (imp (ATP.Var vr1_v0) (ATP.Var vr1_v1))) (ATP.Bind vr0_v1 (ATP.Var vr1_v0))))
    (ATP.Neg (proved (imp (ATP.Var vr0_v0) (imp (ATP.Var vr0_v1) (ATP.Var vr0_v2)))))
    (ATP.Pos (proved (imp (imp (ATP.Var vr1_v0) (ATP.Var vr1_v1)) (imp (ATP.Var vr1_v0) (ATP.Var vr1_v2)))))
    &v-combined)
  False)

; The normalized direct proof crosses the unchanged Prime checker.
!(bind! &v-ja-kb (new-space))
!(add-atom &v-ja-kb (: f_ch_183 Type))
!(add-atom &v-ja-kb (: f_ph_183 Type))
!(add-atom &v-ja-kb (: f_ps_183 Type))
!(add-atom &v-ja-kb (: imp (-> Type Type Type)))
!(add-atom &v-ja-kb (: neg (-> Type Type)))
!(add-atom &v-ja-kb (: hypothesis_1 (imp (neg f_ph_183) f_ch_183)))
!(add-atom &v-ja-kb (: hypothesis_2 (imp f_ps_183 f_ch_183)))
!(add-atom &v-ja-kb (: rule_pm2_61d1 (-> (imp $vr0_v0 (imp $vr0_v1 $vr0_v2)) (imp (neg $vr0_v1) $vr0_v2) (imp $vr0_v0 $vr0_v2))))
!(add-atom &v-ja-kb (: rule_imim2i (-> (imp $vr1_v1 $vr1_v2) (imp (imp $vr1_v0 $vr1_v1) (imp $vr1_v0 $vr1_v2)))))

!(assertEqual
  (check-type &v-ja-kb (rule_pm2_61d1 (rule_imim2i hypothesis_2) hypothesis_1) (imp (imp f_ph_183 f_ps_183) f_ch_183) 100000)
  (he-accept (exact (imp (imp f_ph_183 f_ps_183) f_ch_183))))

!(println! (SetMMPrimeVampireTSTPReplaySummary ja 9 9 0))
