; ============================================================================
; setmm_prime_e_pm2_61iii_resolution_replay_v0.metta
; Generated from E's actual full-prior-theory TSTP refutation.
; E and this adapter are untrusted producers: Prime replays every binary
; resolvent and checks the extracted direct proof term independently.
; ============================================================================

!(import! &self lib_atp)

!(bind! &e182-c-0-36 ((ATP.Pos (proved (imp (ATP.Var e182-c-0-36_v0) (imp (ATP.Var e182-c-0-36_v1) (ATP.Var e182-c-0-36_v2))))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-36_v1) (imp (ATP.Var e182-c-0-36_v0) (ATP.Var e182-c-0-36_v3))))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-36_v3) (ATP.Var e182-c-0-36_v2))))))
!(bind! &e182-c-0-37 ((ATP.Pos (proved (imp f_ps_182 f_th_182)))))
!(bind! &e182-c-0-38 ((ATP.Pos (proved (imp (ATP.Var e182-c-0-38_v0) (imp (neg (ATP.Var e182-c-0-38_v1)) (ATP.Var e182-c-0-38_v2))))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-38_v0) (imp (neg (ATP.Var e182-c-0-38_v2)) (ATP.Var e182-c-0-38_v1)))))))
!(bind! &e182-c-0-39 ((ATP.Pos (proved (imp (neg f_ph_182) (imp (neg f_ps_182) (imp (neg f_ch_182) f_th_182)))))))
!(bind! &e182-c-0-31 ((ATP.Pos (proved (ATP.Var e182-c-0-31_v0))) (ATP.Neg (proved (imp (neg (ATP.Var e182-c-0-31_v1)) (imp (neg (ATP.Var e182-c-0-31_v2)) (ATP.Var e182-c-0-31_v0))))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-31_v1) (ATP.Var e182-c-0-31_v0)))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-31_v2) (ATP.Var e182-c-0-31_v0))))))
!(bind! &e182-c-0-32 ((ATP.Pos (proved (imp f_ph_182 f_th_182)))))
!(bind! &e182-c-0-33 ((ATP.Neg (proved f_th_182))))
!(bind! &e182-c-0-25 ((ATP.Pos (proved (ATP.Var e182-c-0-25_v0))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-25_v1) (ATP.Var e182-c-0-25_v0)))) (ATP.Neg (proved (imp (neg (ATP.Var e182-c-0-25_v1)) (ATP.Var e182-c-0-25_v0))))))
!(bind! &e182-c-0-26 ((ATP.Pos (proved (imp (ATP.Var e182-c-0-26_v0) (imp (imp (ATP.Var e182-c-0-26_v0) (ATP.Var e182-c-0-26_v1)) (ATP.Var e182-c-0-26_v1)))))))
!(bind! &e182-c-0-27 ((ATP.Pos (proved (imp (ATP.Var e182-c-0-27_v0) (imp (ATP.Var e182-c-0-27_v1) (ATP.Var e182-c-0-27_v2))))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-27_v0) (ATP.Var e182-c-0-27_v2))))))
!(bind! &e182-c-0-21 ((ATP.Pos (proved (imp (neg (ATP.Var e182-c-0-21_v0)) (ATP.Var e182-c-0-21_v1)))) (ATP.Neg (proved (imp (neg (ATP.Var e182-c-0-21_v1)) (ATP.Var e182-c-0-21_v0))))))
!(bind! &e182-c-0-15 ((ATP.Pos (proved (imp (neg (ATP.Var e182-c-0-15_v0)) (neg (ATP.Var e182-c-0-15_v1))))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-15_v1) (ATP.Var e182-c-0-15_v0))))))
!(bind! &e182-c-0-16 ((ATP.Pos (proved (imp f_ch_182 f_th_182)))))
!(bind! &e182-c-0-42 ((ATP.Pos (proved (imp (ATP.Var e182-c-0-36_v0) (imp (ATP.Var e182-c-0-36_v1) f_th_182)))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-36_v1) (imp (ATP.Var e182-c-0-36_v0) f_ps_182))))))
!(bind! &e182-c-0-43 ((ATP.Pos (proved (imp (neg f_ph_182) (imp (neg (imp (neg f_ch_182) f_th_182)) f_ps_182))))))
!(bind! &e182-c-0-40-nested-0-1-1 ((ATP.Pos (proved f_th_182)) (ATP.Neg (proved (imp (neg (ATP.Var e182-c-0-31_v1)) (imp (neg f_ph_182) f_th_182)))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-31_v1) f_th_182)))))
!(bind! &e182-c-0-40 ((ATP.Neg (proved (imp (neg (ATP.Var e182-c-0-31_v1)) (imp (neg f_ph_182) f_th_182)))) (ATP.Neg (proved (imp (ATP.Var e182-c-0-31_v1) f_th_182)))))
!(bind! &e182-c-0-34 ((ATP.Pos (proved (imp (imp (ATP.Var e182-c-0-26_v0) (ATP.Var e182-c-0-26_v1)) (ATP.Var e182-c-0-26_v1)))) (ATP.Neg (proved (imp (neg (ATP.Var e182-c-0-26_v0)) (imp (imp (ATP.Var e182-c-0-26_v0) (ATP.Var e182-c-0-26_v1)) (ATP.Var e182-c-0-26_v1)))))))
!(bind! &e182-c-0-22 ((ATP.Pos (proved (imp (neg f_th_182) (neg f_ch_182))))))
!(bind! &e182-c-0-28 ((ATP.Pos (proved (imp (neg (neg f_ch_182)) f_th_182)))))
!(bind! &e182-c-0-35 ((ATP.Pos (proved (imp (neg (neg f_ch_182)) (imp (ATP.Var e182-c-0-27_v1) f_th_182))))))
!(bind! &e182-c-0-41 ((ATP.Pos (proved (imp (imp (neg f_ch_182) f_th_182) f_th_182)))))
!(bind! &e182-c-0-44 ((ATP.Neg (proved (imp (neg (imp (neg f_ch_182) f_th_182)) (imp (neg f_ph_182) f_th_182))))))
!(bind! &e182-c-0-45-nested-0-1-0 ((ATP.Pos (proved (imp (neg (imp (neg f_ch_182) f_th_182)) (imp (neg f_ph_182) f_th_182))))))
!(bind! &e182-c-0-45 ())

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-36 &e182-c-0-37
    (ATP.Subst ((ATP.Bind e182-c-0-36_v2 f_th_182) (ATP.Bind e182-c-0-36_v3 f_ps_182)))
    (ATP.Neg (proved (imp (ATP.Var e182-c-0-36_v3) (ATP.Var e182-c-0-36_v2))))
    (ATP.Pos (proved (imp f_ps_182 f_th_182)))
    &e182-c-0-42)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-38 &e182-c-0-39
    (ATP.Subst ((ATP.Bind e182-c-0-38_v0 (neg f_ph_182)) (ATP.Bind e182-c-0-38_v1 (imp (neg f_ch_182) f_th_182)) (ATP.Bind e182-c-0-38_v2 f_ps_182)))
    (ATP.Neg (proved (imp (ATP.Var e182-c-0-38_v0) (imp (neg (ATP.Var e182-c-0-38_v2)) (ATP.Var e182-c-0-38_v1)))))
    (ATP.Pos (proved (imp (neg f_ph_182) (imp (neg f_ps_182) (imp (neg f_ch_182) f_th_182)))))
    &e182-c-0-43)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-31 &e182-c-0-32
    (ATP.Subst ((ATP.Bind e182-c-0-31_v0 f_th_182) (ATP.Bind e182-c-0-31_v2 f_ph_182)))
    (ATP.Neg (proved (imp (ATP.Var e182-c-0-31_v2) (ATP.Var e182-c-0-31_v0))))
    (ATP.Pos (proved (imp f_ph_182 f_th_182)))
    &e182-c-0-40-nested-0-1-1)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-40-nested-0-1-1 &e182-c-0-33
    (ATP.Subst ())
    (ATP.Pos (proved f_th_182))
    (ATP.Neg (proved f_th_182))
    &e182-c-0-40)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-25 &e182-c-0-26
    (ATP.Subst ((ATP.Bind e182-c-0-25_v0 (imp (imp (ATP.Var e182-c-0-26_v0) (ATP.Var e182-c-0-26_v1)) (ATP.Var e182-c-0-26_v1))) (ATP.Bind e182-c-0-25_v1 (ATP.Var e182-c-0-26_v0))))
    (ATP.Neg (proved (imp (ATP.Var e182-c-0-25_v1) (ATP.Var e182-c-0-25_v0))))
    (ATP.Pos (proved (imp (ATP.Var e182-c-0-26_v0) (imp (imp (ATP.Var e182-c-0-26_v0) (ATP.Var e182-c-0-26_v1)) (ATP.Var e182-c-0-26_v1)))))
    &e182-c-0-34)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-15 &e182-c-0-16
    (ATP.Subst ((ATP.Bind e182-c-0-15_v0 f_th_182) (ATP.Bind e182-c-0-15_v1 f_ch_182)))
    (ATP.Neg (proved (imp (ATP.Var e182-c-0-15_v1) (ATP.Var e182-c-0-15_v0))))
    (ATP.Pos (proved (imp f_ch_182 f_th_182)))
    &e182-c-0-22)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-21 &e182-c-0-22
    (ATP.Subst ((ATP.Bind e182-c-0-21_v0 (neg f_ch_182)) (ATP.Bind e182-c-0-21_v1 f_th_182)))
    (ATP.Neg (proved (imp (neg (ATP.Var e182-c-0-21_v1)) (ATP.Var e182-c-0-21_v0))))
    (ATP.Pos (proved (imp (neg f_th_182) (neg f_ch_182))))
    &e182-c-0-28)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-27 &e182-c-0-28
    (ATP.Subst ((ATP.Bind e182-c-0-27_v0 (neg (neg f_ch_182))) (ATP.Bind e182-c-0-27_v2 f_th_182)))
    (ATP.Neg (proved (imp (ATP.Var e182-c-0-27_v0) (ATP.Var e182-c-0-27_v2))))
    (ATP.Pos (proved (imp (neg (neg f_ch_182)) f_th_182)))
    &e182-c-0-35)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-34 &e182-c-0-35
    (ATP.Subst ((ATP.Bind e182-c-0-26_v0 (neg f_ch_182)) (ATP.Bind e182-c-0-26_v1 f_th_182) (ATP.Bind e182-c-0-27_v1 (imp (neg f_ch_182) f_th_182))))
    (ATP.Neg (proved (imp (neg (ATP.Var e182-c-0-26_v0)) (imp (imp (ATP.Var e182-c-0-26_v0) (ATP.Var e182-c-0-26_v1)) (ATP.Var e182-c-0-26_v1)))))
    (ATP.Pos (proved (imp (neg (neg f_ch_182)) (imp (ATP.Var e182-c-0-27_v1) f_th_182))))
    &e182-c-0-41)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-40 &e182-c-0-41
    (ATP.Subst ((ATP.Bind e182-c-0-31_v1 (imp (neg f_ch_182) f_th_182))))
    (ATP.Neg (proved (imp (ATP.Var e182-c-0-31_v1) f_th_182)))
    (ATP.Pos (proved (imp (imp (neg f_ch_182) f_th_182) f_th_182)))
    &e182-c-0-44)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-42 &e182-c-0-43
    (ATP.Subst ((ATP.Bind e182-c-0-36_v0 (neg (imp (neg f_ch_182) f_th_182))) (ATP.Bind e182-c-0-36_v1 (neg f_ph_182))))
    (ATP.Neg (proved (imp (ATP.Var e182-c-0-36_v1) (imp (ATP.Var e182-c-0-36_v0) f_ps_182))))
    (ATP.Pos (proved (imp (neg f_ph_182) (imp (neg (imp (neg f_ch_182) f_th_182)) f_ps_182))))
    &e182-c-0-45-nested-0-1-0)
  True)

!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-45-nested-0-1-0 &e182-c-0-44
    (ATP.Subst ())
    (ATP.Pos (proved (imp (neg (imp (neg f_ch_182) f_th_182)) (imp (neg f_ph_182) f_th_182))))
    (ATP.Neg (proved (imp (neg (imp (neg f_ch_182) f_th_182)) (imp (neg f_ph_182) f_th_182))))
    &e182-c-0-45)
  True)

; A changed final resolvent is rejected.
!(assertEqual
  (atp:resolution:check-step
    &e182-c-0-45-nested-0-1-0 &e182-c-0-44
    (ATP.Subst ())
    (ATP.Pos (proved (imp (neg (imp (neg f_ch_182) f_th_182)) (imp (neg f_ph_182) f_th_182))))
    (ATP.Neg (proved (imp (neg (imp (neg f_ch_182) f_th_182)) (imp (neg f_ph_182) f_th_182))))
    ((ATP.Pos (proved forged))))
  False)

; Reconstruct the direct Horn proof carried through the refutation.
!(bind! &e182-kb (new-space))
!(add-atom &e182-kb (: f_ch_182 Type))
!(add-atom &e182-kb (: f_ph_182 Type))
!(add-atom &e182-kb (: f_ps_182 Type))
!(add-atom &e182-kb (: f_th_182 Type))
!(add-atom &e182-kb (: imp (-> Type Type Type)))
!(add-atom &e182-kb (: neg (-> Type Type)))
!(add-atom &e182-kb (: rule_syl6com (-> (imp $e182-c-0-36_v1 (imp $e182-c-0-36_v0 $e182-c-0-36_v3)) (imp $e182-c-0-36_v3 $e182-c-0-36_v2) (imp $e182-c-0-36_v0 (imp $e182-c-0-36_v1 $e182-c-0-36_v2)))))
!(add-atom &e182-kb (chaining-rule rule_syl6com))
!(add-atom &e182-kb (: hypothesis_3 (imp f_ps_182 f_th_182)))
!(add-atom &e182-kb (: rule_con1d (-> (imp $e182-c-0-38_v0 (imp (neg $e182-c-0-38_v2) $e182-c-0-38_v1)) (imp $e182-c-0-38_v0 (imp (neg $e182-c-0-38_v1) $e182-c-0-38_v2)))))
!(add-atom &e182-kb (chaining-rule rule_con1d))
!(add-atom &e182-kb (: hypothesis_1 (imp (neg f_ph_182) (imp (neg f_ps_182) (imp (neg f_ch_182) f_th_182)))))
!(add-atom &e182-kb (: rule_pm2_61ii (-> (imp (neg $e182-c-0-31_v1) (imp (neg $e182-c-0-31_v2) $e182-c-0-31_v0)) (imp $e182-c-0-31_v1 $e182-c-0-31_v0) (imp $e182-c-0-31_v2 $e182-c-0-31_v0) $e182-c-0-31_v0)))
!(add-atom &e182-kb (chaining-rule rule_pm2_61ii))
!(add-atom &e182-kb (: hypothesis_2 (imp f_ph_182 f_th_182)))
!(add-atom &e182-kb (: rule_pm2_61i (-> (imp $e182-c-0-25_v1 $e182-c-0-25_v0) (imp (neg $e182-c-0-25_v1) $e182-c-0-25_v0) $e182-c-0-25_v0)))
!(add-atom &e182-kb (chaining-rule rule_pm2_61i))
!(add-atom &e182-kb (: rule_pm2_27 (imp $e182-c-0-26_v0 (imp (imp $e182-c-0-26_v0 $e182-c-0-26_v1) $e182-c-0-26_v1))))
!(add-atom &e182-kb (type-scheme rule_pm2_27))
!(add-atom &e182-kb (: rule_a1d (-> (imp $e182-c-0-27_v0 $e182-c-0-27_v2) (imp $e182-c-0-27_v0 (imp $e182-c-0-27_v1 $e182-c-0-27_v2)))))
!(add-atom &e182-kb (chaining-rule rule_a1d))
!(add-atom &e182-kb (: rule_con1i (-> (imp (neg $e182-c-0-21_v1) $e182-c-0-21_v0) (imp (neg $e182-c-0-21_v0) $e182-c-0-21_v1))))
!(add-atom &e182-kb (chaining-rule rule_con1i))
!(add-atom &e182-kb (: rule_con3i (-> (imp $e182-c-0-15_v1 $e182-c-0-15_v0) (imp (neg $e182-c-0-15_v0) (neg $e182-c-0-15_v1)))))
!(add-atom &e182-kb (chaining-rule rule_con3i))
!(add-atom &e182-kb (: hypothesis_4 (imp f_ch_182 f_th_182)))

!(assertEqual
  (check-type &e182-kb (rule_pm2_61ii (rule_syl6com (rule_con1d hypothesis_1) hypothesis_3) (rule_pm2_61i rule_pm2_27 (rule_a1d (rule_con1i (rule_con3i hypothesis_4)))) hypothesis_2) f_th_182 1000000)
  (he-accept (exact f_th_182)))

!(println! (SetMMPrimeEFrontierTSTPReplaySummary pm2.61iii 14 14 0))
