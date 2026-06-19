; ============================================================================
; DoF 5 — Width-complement convention (and range normalization)
; ----------------------------------------------------------------------------
; THE KNOB.  Defining confidence as the complement of interval width,
;     c = 1 - (U - L)                       (unit gamble in [0,1])
;     c = 1 - (U - L)/(b - a)               (general bounded gamble in [a,b])
;   is natural and minimal (width 0 -> c 1; max width -> c 0), but it is a
;   CONVENTION, not a theorem of nature.  It becomes the PLN odds form only once
;   paired with Walley/IDM predictive width (then width = k/(N+k), so
;   1 - width = N/(N+k)).  The free knob after that is the RANGE [a,b].
;
; WHY KEEP IT.  Binary truth has a canonical unit scale; dollar-valued utilities
;   do not — they must be range-normalized before width-complement is meaningful.
;
; Lean oracle: PLNConfidenceWeight  walleyPredictiveWidth / WidthComplementCompatible
;   and the forcing theorem walley_width_complement_forces_plnOdds.
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

(= (wc-unit  $L $U)        (- 1.0 (- $U $L)))
(= (wc-range $L $U $a $b)  (- 1.0 (/ (- $U $L) (- $b $a))))

; Binary interval [0.2, 0.8]: width 0.6 -> confidence 0.4
!(wc-unit 0.2 0.8)              ; 0.4

; Dollar utility interval [20, 80] on full range [0, 100]: SAME normalized width
!(wc-range 20.0 80.0 0.0 100.0) ; 0.4   (matches the binary case after normalization)

; Without normalization, a raw width of 60 (dollars) would wrongly read as a huge "width":
!(wc-unit 20.0 80.0)            ; -59.0  (nonsense — the convention needs a unit/normalized scale)

; POSITIVE: binary prediction uses 1-(U-L) directly.
; NEGATIVE: utilities/scores MUST be range-normalized first, or "confidence" is meaningless.
