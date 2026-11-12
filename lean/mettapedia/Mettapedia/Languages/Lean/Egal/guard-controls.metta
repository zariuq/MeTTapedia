; Run after generate.metta and interpret.metta. Guard templates must preserve
; free variables when parameters or constructor fields enter a quantified law.
!(import! &self system)

(= (check-guard $name $actual $expected)
   (if (== $actual $expected) (println! (format-args "PASS {}" ($name)))
       (let $_error (system:write stderr
         (format-args "FAIL {}: got {}, expected {}\n" ($name $actual $expected)))
         (system:exit 1))))

!(check-guard "closed numeral matches the family representation"
  (guard-fterm (const Nat.zero) () ()) (num 0))

!(check-guard "parameter substitution avoids a bound variable"
  (guard-fterm (pi q0 (const A) (bound q0)) ((: A Type)) ((var q0)))
  (pi "q0_c" (var q0) (var "q0_c")))

!(check-guard "freshening also avoids an existing suffixed identifier"
  (guard-fterm (pi q0 (const A)
    (app (app (app (const Eq) (const A)) (bound q0)) (bound q0))) ((: A Type))
    ((app Prod ((var q0) (var q0_c)))))
  (pi "q0_c_c" (app Prod ((var q0) (var q0_c)))
    (app Eq ((app Prod ((var q0) (var q0_c))) (var "q0_c_c") (var "q0_c_c")))))

!(check-guard "field slots cannot capture a parameter named y0"
  (instantiate-field-types
    ((guard-fterm (app (app (const Eq) (const A)) (field 0))
      ((: A Type)) ((var y0))))
    ((var operation)))
  ((app Eq ((var y0) (var operation)))))

!(check-guard "repeated reads emit one substitution proof"
  (index-rewrites ((app (field 0) (app (field 0) (field 1)))) 2)
  "rewrite T0. rewrite T1. ")

!(check-guard "proposition parameters range over truth values"
  (typing-binders ((p (prop))) ()) "forall p :e LeanProp, ")

!(check-guard "predicates remain ordinary function values"
  (is-family-type (arrow (app Nat ()) (prop))) False)

!(check-guard "type families retain their separate meaning"
  (is-family-type (arrow (app Nat ()) (cons-atom sort ((lvl 1))))) True)

; A decision with an unread body must not be replaced by a canonical value
; merely because its result type is a subsingleton.
(LeanFunction GuardTest.decision (GuardTest.equation))
(LeanFunctionType GuardTest.decision (pi p (prop) (app Decidable ((var p)))))
(LeanEquation GuardTest.equation ((term p (prop))) (app Decidable ((var p)))
  (app GuardTest.decision ((var p))) (app GuardTest.missing ((var p))))
(EgalName GuardTest.decision GuardTest_decision)
(EgalName GuardTest.equation GuardTest_equation)
!(check-guard "unread decision bodies remain dependencies"
  (why-not GuardTest.decision ()) "applies GuardTest.missing, which is not read")

!(check-guard "ordinary negation is not a pattern exclusion"
  (is-cond-hyp (arrow (var q) (app False ()))) False)

!(check-guard "a prior pattern exclusion retains its classification"
  (is-cond-hyp (pi n (app Nat ())
    (arrow (app Eq ((app Nat ()) (var x) (app Nat.succ ((var n))))) (app False ())))) True)

!(check-guard "equation hypotheses contribute dependencies"
  (binder-deps ((hyp h (app GuardTest.missing ((var x))))) GuardTest.fn)
  (GuardTest.missing))

!(check-guard "native hypotheses survive into the proof context"
  (known-proof (var p) (stmt-ctx ((term p (prop)) (hyp hp (var p))))) "hp")

!(check-guard "an incomplete generated proof is not a candidate"
  (proof-candidate-text GuardTest.decision
    "Theorem GuardTest_decision_In : UNDECIDED.") False)

!(check-guard "computation replay must reconstruct its branch proof"
  (computation-candidate
    (computation GuardTest.run "rewrite Lean_Decidable_iota1 p no yes 0 UNDECIDED."))
  (stuck "a proof required by computation replay is not reconstructed"))

!(check-guard "a closed computation remains a checker candidate"
  (computation-candidate (computation GuardTest.closed "reflexivity."))
  (computation GuardTest.closed "reflexivity."))

(LeanFunction GuardTest.unsound (GuardTest.unsoundEquation))
(LeanFunctionType GuardTest.unsound (pi p (prop) (app Decidable ((var p)))))
(LeanEquation GuardTest.unsoundEquation ((term p (prop))) (app Decidable ((var p)))
  (app GuardTest.unsound ((var p))) (app Decidable.isTrue ((var p) (proof))))
(EgalName GuardTest.unsound GuardTest_unsound)
(EgalName GuardTest.unsoundEquation GuardTest_unsoundEquation)
!(check-guard "an erased proof cannot manufacture a true decision"
  (why-not GuardTest.unsound ())
  "erased proofs in the definition or its equations are not reconstructed")

(LeanFunction GuardTest.supported (GuardTest.supportedEquation))
(LeanFunctionType GuardTest.supported (arrow (app Nat ()) (app Nat ())))
(LeanEquation GuardTest.supportedEquation ((term n (app Nat ()))) (app Nat ())
  (app GuardTest.supported ((var n))) (var n))
(EgalName GuardTest.supported GuardTest_supported)
(EgalName GuardTest.supportedEquation GuardTest_supportedEquation)
(EgalProofLibrary GuardMissingLibrary (GuardTest.missing) ())
(EgalTypingUses GuardTest.supported GuardMissingLibrary)
!(check-guard "a missing proof-library dependency remains a refusal"
  (why-not GuardTest.supported ()) "applies GuardTest.missing, which is not read")

(LeanFunction GuardTest.cycle (GuardTest.cycleEquation))
(LeanFunctionType GuardTest.cycle (arrow (app Nat ()) (app Nat ())))
(LeanEquation GuardTest.cycleEquation ((term n (app Nat ()))) (app Nat ())
  (app GuardTest.cycle ((var n))) (var n))
(EgalName GuardTest.cycle GuardTest_cycle)
(EgalName GuardTest.cycleEquation GuardTest_cycleEquation)
(EgalProofLibrary GuardCyclicLibrary (GuardTest.cycle) ())
(EgalTypingUses GuardTest.cycle GuardCyclicLibrary)
!(check-guard "proof-library dependencies cannot justify themselves"
  (why-not GuardTest.cycle ()) "applies GuardTest.cycle, which is not read")

; Preparing a new immutable batch must discard the previous batch's result.
(LeanFunction GuardTest.refresh (GuardTest.refreshEquation))
(LeanFunctionType GuardTest.refresh (arrow (app Nat ()) (app Nat ())))
(LeanEquation GuardTest.refreshEquation ((term n (app Nat ()))) (app Nat ())
  (app GuardTest.refresh ((var n))) (var n))
(EgalName GuardTest.refresh GuardTest_refresh)
(EgalName GuardTest.refreshEquation GuardTest_refreshEquation)
!(prepare-readability)
!(check-guard "prepared readability retains the admitted judgment"
  (prepared-readability GuardTest.refresh) ok)
!(remove-atom &self
  (LeanEquation GuardTest.refreshEquation ((term n (app Nat ()))) (app Nat ())
    (app GuardTest.refresh ((var n))) (var n)))
!(add-atom &self
  (LeanEquation GuardTest.refreshEquation ((term n (app Nat ()))) (app Nat ())
    (app GuardTest.refresh ((var n))) (app GuardTest.missing ((var n)))))
!(prepare-readability)
!(check-guard "a new batch cannot reuse an obsolete admitted judgment"
  (prepared-readability GuardTest.refresh) "applies GuardTest.missing, which is not read")

; A typing-certificate marker cannot supply an absent source hypothesis.
(LeanFunction GuardTest.guardOnly (GuardTest.guardOnlyEquation))
(LeanFunctionType GuardTest.guardOnly (pi p (prop) (arrow (app Nat ()) (app Nat ()))))
(LeanEquation GuardTest.guardOnlyEquation ((term p (prop)) (term n (app Nat ())) (hyp h (var p)))
  (app Nat ()) (app GuardTest.guardOnly ((var p) (var n))) (var n))
(EgalName GuardTest.guardOnly GuardTest_guardOnly)
(EgalName GuardTest.guardOnlyEquation GuardTest_guardOnlyEquation)
(TypingProof GuardTest_guardOnly)
!(check-guard "an external guard is not an erased proof input"
  (proof-input-direct GuardTest.guardOnly) None)

(LeanFunction GuardTest.proofInput (GuardTest.proofInputEquation))
(LeanFunctionType GuardTest.proofInput
  (pi p (prop) (arrow (var p) (arrow (app Nat ()) (app Nat ())))))
(LeanEquation GuardTest.proofInputEquation ((term p (prop)) (hyp h (var p)) (term n (app Nat ())))
  (app Nat ()) (app GuardTest.proofInput ((var p) (proof) (var n))) (var n))
(EgalName GuardTest.proofInput GuardTest_proofInput)
(EgalName GuardTest.proofInputEquation GuardTest_proofInputEquation)
(TypingProof GuardTest_proofInput)
!(check-guard "an actual proof input accounts for the guarded equation"
  (not (== (proof-input-direct GuardTest.proofInput) None)) True)

!(check-guard "typing one value preserves the following argument and its proof"
  (typ-args-raw ((var x) (num 1)) (term term)
    ((app Nat ()) (app Nat ())) ((app Nat ()) (app Nat ())) () ((x "Hx")))
  (x "Hx" "(LeanNum 1)" "(LeanNum_In 1 (nat_ordsucc 0 nat_0))"))
