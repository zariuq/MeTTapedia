; =============================================================================
; equation_kernel_leaks_v0.metta
;
; Where the sealed kernel still leaks while the seal operators are emulated,
; pinned as controls. Load after equation_kernel_registry_v0.metta,
; equation_kernel_v0.metta and equation_kernel_space_v0.metta.
;
; Each line prints (ek:pass ctl-name) when the engine behaves as recorded
; here. A `leak-` control passes while the leak is present: the native seal
; primitive with frozen modules flips it. The other controls pin what the
; kernel's own design already closes, independently of the seal: there is no
; function that seals a supplied conclusion, the old value seal is gone, and
; brands and facets are respected.
; =============================================================================

(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))

; Forged claims are written as literal data: PeTTa does not evaluate an
; atom stored by add-atom, while HE and CeTTa re-evaluate results.

; ---------- closed by the kernel's design --------------------------------------

; The former public mint helper and the former value seal are gone: their
; spellings are inert data and read as no theorem.
!(ek:control ctl-no-mint-helper
   (ek:lcf-claim (ek:lcf-from (ek:some (ek:claim (ek:sym "A") (ek:sym "forged"))) ek:no-row))
   ek:none)
!(ek:control ctl-no-value-seal
   (ek:lcf-claim (ek:sealed (ek:claim (ek:sym "A") (ek:sym "forged")) ek:no-row))
   ek:none)

; A value sealed by another brand is not a theorem.
!(ek:control ctl-foreign-brand
   (let $other (new-seal intruder)
     (ek:lcf-claim (seal $other (ek:thm ek:nil (ek:claim (ek:sym "A") (ek:sym "forged")) ek:unrecorded))))
   ek:none)

; The kernel's unsealer facet cannot seal.
!(ek:control ctl-unsealer-cannot-seal
   (ek:lcf-claim (seal (get-state &ek-unsealer-cell)
                       (ek:thm ek:nil (ek:claim (ek:sym "A") (ek:sym "forged")) ek:unrecorded)))
   ek:none)

; ---------- leaks that wait for the native seal and frozen modules -------------

; LEAK 1: an emulated capability is data; writing one seals.
!(ek:control ctl-leak-capability-data
   (ek:lcf-claim (seal (seal-cap 1 ek-theorem both)
                       (ek:thm ek:nil (ek:claim (ek:sym "A") (ek:sym "forged")) ek:unrecorded)))
   (ek:some (ek:claim (ek:sym "A") (ek:sym "forged"))))

; LEAK 2: code that reaches the emulation's registry forges a sealed value.
!(ek:control ctl-leak-registry-write
   (let $added (add-atom &seal-registry
                 (seal-entry 1 99999 (ek:thm ek:nil (ek:claim (ek:sym "A") (ek:sym "forged")) ek:unrecorded)))
     (ek:lcf-claim (sealed-ticket ek-theorem 99999)))
   (ek:some (ek:claim (ek:sym "A") (ek:sym "forged"))))

; LEAK 3: the sealer cell's token is visible to code in the same module.
!(ek:control ctl-leak-sealer-token
   (ek:lcf-claim (seal (get-state &ek-sealer-cell)
                       (ek:thm ek:nil (ek:claim (ek:sym "A") (ek:sym "forged")) ek:unrecorded)))
   (ek:some (ek:claim (ek:sym "A") (ek:sym "forged"))))

; LEAK 4: matching a rule's equation body yields the sealer cell without its
; token (frozen modules hide bodies).
!(ek:control ctl-leak-rule-body-reflection
   (let $cell (match &self (= (ek:lcf-refl $theory $a) (seal (get-state $c) $content)) $c)
     (ek:lcf-claim (seal (get-state $cell)
                         (ek:thm ek:nil (ek:claim (ek:sym "A") (ek:sym "forged")) ek:unrecorded))))
   (ek:some (ek:claim (ek:sym "A") (ek:sym "forged"))))

; LEAK 5: an emulated sealed value is an expression; rebuilding its printed
; form gives the same theorem (the native sealed value has no reader syntax).
!(ek:control ctl-leak-ticket-text
   (let (sealed-ticket $nick $n) (ek:lcf-refl ek:nil (ek:sym "A"))
     (ek:lcf-claim (sealed-ticket $nick $n)))
   (ek:some (ek:claim (ek:sym "A") (ek:sym "A"))))
