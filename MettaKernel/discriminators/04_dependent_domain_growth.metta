;; ============================================================
;;  04 · THE GROWING MENU
;;  Discriminator: directed dependency — Π over a domain that grows
;; ============================================================
;;
;;  Question this instrument asks:
;;    A dependent function is defined over "all dishes on the menu".
;;    Learning is monotone: revisions only ADD dishes and never take
;;    them away — the step cannot be inverted.  What happens to the
;;    function when the domain grows?  Three repairs are simulated:
;;
;;    REJECT   the function was built at revision 0; at revision 1 it is
;;             simply invalid for the new dish (domain transport is not
;;             invertible, so ordinary pointwise Π is unavailable —
;;             matching the proved restricted-Π law).
;;    DEMAND   the function is a query-at-use (continuation / demand):
;;             it recomputes from the current facts whenever called.
;;    GUARDED  the function is stamped with its revision (a "later"
;;             discipline): using it at another revision requires an
;;             explicit transport step, which is where the missing
;;             dish shows up as an obligation rather than a crash.
;; ============================================================

;; --- the menu, by revision (monotone growth) ---------------------------
!(add-atom &self (dish tea   0))
!(add-atom &self (dish scone 0))
!(add-atom &self (dish cake  1))            ; learned at revision 1
(= (on-menu $d $rev) (match &self (dish $d $r) (if (<= $r $rev) yes (empty))))
(= (base-price tea 2))
(= (base-price scone 3))
(= (base-price cake 5))

;; --- REJECT: a function frozen at revision 0 --------------------------
;;  Its domain is the revision-0 menu, recorded at construction time.
(= (price-list-at-0 $d)
   (case (collapse (on-menu $d 0))
     (((yes) (base-price $d))
      ($_ (INVALID (dish $d) not-in-domain-of revision-0-function)))))

;; --- DEMAND: query-at-use, recomputed against the current revision ----
(= (current-revision) 1)
(= (price-list-demand $d)
   (case (collapse (on-menu $d (current-revision)))
     (((yes) (base-price $d))
      ($_ (UNKNOWN (dish $d))))))

;; --- GUARDED: functions carry their revision stamp -----------------------
;;  (guarded-price-list REV) is valid exactly at REV; use elsewhere needs
;;  an explicit transport whose obligation is the new dish.
(= (guarded-price-list $rev $d)
   (case (collapse (on-menu $d $rev))
     (((yes) (at $rev (base-price $d)))
      ($_ (OBLIGATION (transport-from $rev needs-value-for $d))))))
(= (transport $from $to $d)
   (case (collapse (on-menu $d $from))
     (((yes) (guarded-price-list $from $d))               ; old value carries
      ($_ (case (collapse (on-menu $d $to))
            (((yes) (NEW-CASE (at $to (base-price $d))))   ; explicit new case
             ($_ (UNKNOWN $d))))))))

!(println! "--- a stable dish (tea) under all three repairs ---")
!(println! (REJECT  (price-list-at-0 tea)))
!(println! (DEMAND  (price-list-demand tea)))
!(println! (GUARDED (transport 0 1 tea)))

!(println! "--- the NEW dish (cake) under all three repairs ---")
!(println! (REJECT  (price-list-at-0 cake)))
!(println! (DEMAND  (price-list-demand cake)))
!(println! (GUARDED (transport 0 1 cake)))

!(println! "--- what each repair does to substitution laws ---")
!(println! (REJECT  keeps-beta-and-substitution but-domain-frozen))
!(println! (DEMAND  values-drift-with-world so-two-calls-may-disagree))
!(println! (GUARDED beta-holds-per-revision transport-is-explicit-and-typed))

;; Reading: the theorem already proved says covariant pointwise Π needs
;; invertible domain transport.  Monotone learning is the normal case
;; for an agent, so Prime must pick a repair.  This file lets you feel
;; each: REJECT is honest but brittle; DEMAND is ergonomic but breaks
;; referential transparency across revisions; GUARDED keeps both laws by
;; making the revision index part of the type.
