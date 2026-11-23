!(import! &self control.metta)

; R is uniform on 8 sensor states and 8 actions. Higher beta rewards agreement.
!(println! (tc:summary 3 0.0))
!(println! (tc:summary 3 1.0))
!(println! (tc:summary 3 2.0))
!(println! (tc:summary 3 4.0))

; At most two actuator bits may be on. The world law must still stay fixed.
!(println! (tc:summary 2 2.0))
!(println! (CausalVsPassive
   (CausalInitialDrift (tc:initial-drift (tc:joint 2 2.0)))
   (PassiveInitialDrift (tc:initial-drift (tc:passive-tilt 2 2.0)))))

; A supplied draw is reproducible; it is not an empirical sampling experiment.
!(bind! &board (new-space))
!(tc:open &board episode-1 (0 1 1) 3)
!(println! (Act (tc:step &board episode-1 2.0 0.5)))
!(println! (Replay (tc:step &board episode-1 2.0 0.5)))
!(println! (Actuators (collapse (match &board (ActuatorState $id $bits) ($id $bits)))))
!(println! (Receipt (collapse (match &board (Executed $id $world $action $u)
                         (Executed $id $world $action $u)))))

; An unauthorized supplied action leaves the pending episode untouched.
!(bind! &limited (new-space))
!(tc:open &limited episode-2 (0 0 1) 2)
!(println! (OverBudget (tc:execute &limited episode-2 (0 0 1) (1 1 1))))
!(println! (StillPending (collapse (match &limited (Pending $id) $id))))
!(println! (AdmittedAct (tc:step &limited episode-2 2.0 0.5)))
!(println! (LimitedReceipt (collapse (match &limited (Executed $id $world $action $u)
                                (Executed $id $world $action $u)))))
!(println! (AwaitObservation (tc:step &board not-yet-observed 2.0 0.5)))
