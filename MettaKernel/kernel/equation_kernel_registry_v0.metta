; =============================================================================
; equation_kernel_registry_v0.metta
;
; A registry emulation of the proposed seal primitive, so that the sealed
; kernel of equation_kernel_v0.metta runs today. Load before that file. A
; native implementation of the same operators replaces this file.
;
;   (new-seal NICK)   a seal with a new brand and both rights
;   (sealer-of S)     the same brand, right to seal only
;   (unsealer-of S)   the same brand, right to unseal only
;   (seal S V)        a sealed value holding V, which only this brand opens
;   (unseal S X)      V when X was sealed by this brand; otherwise no result
;
; Here a seal is the data (seal-cap BRAND NICK RIGHTS) and a sealed value is a
; ticket (sealed-ticket NICK N) naming an entry (seal-entry BRAND N V) of the
; registry space. These are the emulation's leaks, pinned by the controls in
; equation_kernel_leaks_v0.metta; the native primitive removes each:
;   - a seal is data: writing (seal-cap ...) grants its rights;
;   - code that reaches &seal-registry can add an entry, forging a value;
;   - matching an equation body that mentions a capability cell yields it;
;   - a ticket is an expression: its printed form is the sealed value.
; =============================================================================

!(bind! &seal-registry (new-space))
!(bind! &seal-counter (new-state 1))

(= (seal-fresh)
   (let $n (get-state &seal-counter)
     (let $advanced (change-state! &seal-counter (+ $n 1)) $n)))

(= (new-seal $nick) (let $brand (seal-fresh) (seal-cap $brand $nick both)))

; Rights: both, seal, unseal, none. Attenuation only removes rights.
(= (seal-meet both $want) $want)
(= (seal-meet seal seal) seal)
(= (seal-meet seal unseal) none)
(= (seal-meet unseal unseal) unseal)
(= (seal-meet unseal seal) none)
(= (seal-meet none $want) none)
(= (seal-may-seal $rights) (if (== $rights both) True (== $rights seal)))
(= (seal-may-unseal $rights) (if (== $rights both) True (== $rights unseal)))

(= (sealer-of $s)
   (case $s (((seal-cap $brand $nick $rights) (seal-cap $brand $nick (seal-meet $rights seal)))
             ($other (seal-refused not-a-seal)))))
(= (unsealer-of $s)
   (case $s (((seal-cap $brand $nick $rights) (seal-cap $brand $nick (seal-meet $rights unseal)))
             ($other (seal-refused not-a-seal)))))

(= (seal $s $value)
   (case $s (((seal-cap $brand $nick $rights)
              (if (seal-may-seal $rights)
                  (let $n (seal-fresh)
                    (let $added (add-atom &seal-registry (seal-entry $brand $n $value))
                      (sealed-ticket $nick $n)))
                  (seal-refused no-seal-right)))
             ($other (seal-refused not-a-seal)))))

; A value that is not a ticket of this brand unseals to no result.
(= (unseal $s $x)
   (case $s (((seal-cap $brand $nick $rights)
              (if (seal-may-unseal $rights)
                  (case $x (((sealed-ticket $nick2 $n) (match &seal-registry (seal-entry $brand $n $value) $value))
                            ($other (empty))))
                  (seal-refused no-unseal-right)))
             ($other (seal-refused not-a-seal)))))
