#!/usr/bin/env python3
"""Writes the review controls of the equation kernel into ``MettaKernel/kernel/``:
``equation_kernel_review_controls_v0.metta`` (the probes of the 2026-10-15 review, as
controls that pass when the kernel refuses what it must) and
``equation_kernel_review_verbatim_v0.metta`` (the theory-mixing probe in its original call
shapes). Expected values follow the Lean examples ``SpaceScenarios``
(``EquationKernel.SpaceCheck``) and ``SealedScenarios`` (``EquationKernel.Sealed``).
Prints the number of review controls written.

Run: ``python3 MettaKernel/tools/generate_equation_kernel_review_controls.py``
"""
from pathlib import Path

KERNEL = Path(__file__).resolve().parent.parent / 'kernel'

A = '(ek:sym "A")'; B = '(ek:sym "B")'; C = '(ek:sym "C")'
def eq(l, r): return '(ek:expr (ek:cons (ek:sym "=") (ek:cons ' + l + ' (ek:cons ' + r + ' ek:nil))))'
EQAB = eq(A, B); EQBC = eq(B, C)
PAB = '(ek:cons ' + EQAB + ' ek:nil)'; PBC = '(ek:cons ' + EQBC + ' ek:nil)'
def lst(*xs):
    s = 'ek:nil'
    for x in reversed(xs): s = '(ek:cons ' + x + ' ' + s + ')'
    return s
def claim(a, b): return '(ek:claim ' + a + ' ' + b + ')'
def refl(a): return '(ek:refl ' + a + ')'
def step(prior, e, copy): return '(ek:step ' + str(prior) + ' (ek:cite ' + e + ' ' + str(copy) + ') ek:nil ek:nil)'
CERTAB = '(ek:cert ' + lst(refl(A), step(0, EQAB, 0)) + ' 1)'
CERTAC = '(ek:cert ' + lst(refl(A), step(0, EQAB, 0), step(1, EQBC, 0)) + ' 2)'
def row(name, i, r): return '(ek:row ' + name + ' ' + str(i) + ' ' + r + ')'
def facts(name, size, root, rows):
    out = ['(ek:size ' + name + ' ' + str(size) + ')', '(ek:root ' + name + ' ' + str(root) + ')']
    out += [row(name, i, r) for i, r in enumerate(rows)]
    return '\n'.join(out)
def control(name, expr, expected): return '!(ek:control ctl-review-' + name + ' ' + expr + ' ' + expected + ')'
def inject(index, c, then): return '(let $next (get-state &eks-invocations) (let $added (add-atom &eks-table (ek:claim-at $next ' + str(index) + ' ' + c + ')) ' + then + '))'
L = []
L.append('''; =============================================================================
; equation_kernel_review_controls_v0.metta
;
; The probes of the 2026-10-15 review of the equation kernel, as controls
; that pass when the repaired kernel refuses what it must. Load after
; equation_kernel_registry_v0.metta, equation_kernel_v0.metta and
; equation_kernel_space_v0.metta. Expected values follow the Lean examples
; SpaceScenarios (EquationKernel.SpaceCheck) and SealedScenarios
; (EquationKernel.Sealed). Facts and stored atoms are written as literal
; data, because PeTTa stores atoms without evaluating them.
; =============================================================================

(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))
''')
L.append('; ---------- the cache and theory probes ----------------------------------------')
L.append('!(bind! &audit-second (new-space))')
L.append(facts('same-id', 2, 1, [refl(A), step(0, EQAB, 0)]))
L.append(control('valid-pure', '(ek:check ' + PAB + ' ' + CERTAB + ' ' + claim(A, B) + ')', 'True'))
L.append(control('prime-cache', '(eks:check ' + PAB + ' &self same-id ' + claim(A, B) + ')', 'True'))
L.append('!(add-atom &audit-second (ek:size same-id 0))\n!(add-atom &audit-second (ek:root same-id 1))')
L.append(control('pure-empty', '(ek:check ek:nil (ek:cert ek:nil 1) ' + claim(A, B) + ')', 'False'))
L.append('; The reviewed false acceptance, now refused.')
L.append(control('space-empty-after-other-theory', '(eks:check ek:nil &audit-second same-id ' + claim(A, B) + ')', 'False'))
L.append(control('pure-other-theory', '(ek:check ' + PBC + ' ' + CERTAB + ' ' + claim(A, B) + ')', 'False'))
L.append(control('pure-cross-theory', '(ek:check ' + PBC + ' ' + CERTAC + ' ' + claim(A, C) + ')', 'False'))
V = []
V.append('''; =============================================================================
; equation_kernel_review_verbatim_v0.metta
;
; The reviewed theory-mixing probe in its original call shapes, which the
; repaired interface no longer has. Load after equation_kernel_registry_v0,
; equation_kernel_v0 and equation_kernel_space_v0. HE and CeTTa read the old
; calls as inert data, so no theorem results; PeTTa refuses the file when it
; loads, because ek:lcf-step is called with five arguments.
; =============================================================================

(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))
''')
V.append(control('lcf-cross-theory-verbatim', '(let $t (ek:lcf-step ' + PAB + ' (ek:lcf-refl ' + A + ') (ek:cite ' + EQAB + ' 0) ek:nil ek:nil) (ek:lcf-claim (ek:lcf-step ' + PBC + ' $t (ek:cite ' + EQBC + ' 0) ek:nil ek:nil)))', 'ek:none'))
(KERNEL / 'equation_kernel_review_verbatim_v0.metta').write_text('\n'.join(V) + '\n')
L.append("; The same mixing in the current interface: the step cites the premise's own theory.")
L.append(control('lcf-cross-theory', '(let $t (ek:lcf-step (ek:lcf-refl ' + PAB + ' ' + A + ') (ek:cite ' + EQAB + ' 0) ek:nil ek:nil) (ek:lcf-claim (ek:lcf-step $t (ek:cite ' + EQBC + ' 0) ek:nil ek:nil)))', 'ek:none'))
L.append(control('lcf-cross-theory-trans', '(ek:lcf-claim (ek:lcf-trans (ek:lcf-step (ek:lcf-refl ' + PAB + ' ' + A + ') (ek:cite ' + EQAB + ' 0) ek:nil ek:nil) (ek:lcf-step (ek:lcf-refl ' + PBC + ' ' + B + ') (ek:cite ' + EQBC + ' 0) ek:nil ek:nil)))', 'ek:none'))
L.append('; ---------- the public mint probe -----------------------------------------------')
L.append(control('public-mint-helper', '(ek:lcf-claim (ek:lcf-from (ek:some (ek:claim ' + A + ' (ek:sym "forged"))) ek:no-row))', 'ek:none'))
L.append(control('old-recording-helper', '(ek:lcf-claim (ek:rec-emit (ek:rec ek:nil 0) ' + refl(A) + ' (ek:some (ek:claim ' + A + ' (ek:sym "forged")))))', 'ek:none'))
L.append('; ---------- the reader-domain probe ----------------------------------------------')
L.append('; Integers travel as canonical decimal strings, which every engine reads.')
L.append(control('big-integers-distinct', '(== (ek:int "9223372036854775808") (ek:int "9223372036854775809"))', 'False'))
BIG = '(ek:int "9223372036854775808")'
BIGCALL = '(ek:expr (ek:cons (ek:sym "big") ek:nil))'
EQBIG = eq(BIGCALL, BIG)
L.append(control('big-integer-fact', '(ek:check (ek:cons ' + EQBIG + ' ek:nil) (ek:cert ' + lst(refl(BIGCALL), step(0, EQBIG, 0)) + ' 1) ' + claim(BIGCALL, BIG) + ')', 'True'))
L.append('; ---------- the space checker: names, bounds, injection, retry -----------------')
L.append('; Two certificates under one name refuse.')
L.append(facts('dup-id', 2, 1, [refl(A), step(0, EQAB, 0)]))
L.append(facts('dup-id', 2, 1, [refl(A), step(0, EQAB, 0)]))
L.append(control('repeated-name', '(eks:check ' + PAB + ' &self dup-id ' + claim(A, B) + ')', 'False'))
L.append('; A root at the size refuses.')
L.append(facts('forward-root', 1, 1, [refl(A)]))
L.append(control('forward-root', '(eks:check ' + PAB + ' &self forward-root ' + claim(A, A) + ')', 'False'))
L.append('; A premise at or past its row refuses, even with an entry injected for it.')
L.append(facts('forward-premise', 2, 0, [step(1, EQAB, 0), refl(A)]))
L.append(control('forward-premise', inject(1, claim(A, A), '(eks:check ' + PAB + ' &self forward-premise ' + claim(A, B) + ')'), 'False'))
L.append('; An entry injected for the next invocation causes refusal, not acceptance;')
L.append('; the refused invocation removes it, so the retry is accepted.')
L.append(facts('injected', 2, 1, [refl(A), step(0, EQAB, 0)]))
L.append(control('injected-entry', inject(1, claim(A, B), '(eks:check ' + PAB + ' &self injected ' + claim(A, B) + ')'), 'False'))
L.append(control('retry-after-injection', '(eks:check ' + PAB + ' &self injected ' + claim(A, B) + ')', 'True'))
L.append('; An injected claim cannot stand in for a missing row.')
L.append(facts('missing-row', 2, 1, [refl(A)]))
L.append(control('injected-missing-row', inject(1, claim(A, B), '(eks:check ' + PAB + ' &self missing-row ' + claim(A, B) + ')'), 'False'))
L.append('; A failed invocation, then a retry with a corrected certificate.')
L.append(facts('retry-bad', 2, 1, [refl(A), step(0, EQAB, 1)]))
L.append(control('failed-invocation', '(eks:check ' + PAB + ' &self retry-bad ' + claim(A, B) + ')', 'False'))
L.append(control('retry', '(eks:check ' + PAB + ' &self same-id ' + claim(A, B) + ')', 'True'))
L.append('; A row that is not a row term refuses.')
L.append(facts('malformed', 1, 0, ['(ek:not-a-row ' + A + ')']))
L.append(control('malformed-row', '(eks:check ' + PAB + ' &self malformed ' + claim(A, A) + ')', 'False'))
L.append(control('malformed-row-pure', '(ek:check ' + PAB + ' (ek:cert ' + lst('(ek:not-a-row ' + A + ')') + ' 0) ' + claim(A, A) + ')', 'False'))
L.append('; Every invocation removed its entries.')
L.append(control('table-clean', '(collapse (match &eks-table (ek:claim-at $i $j $c) $i))', '()'))
L.append('; ---------- recording sessions -------------------------------------------------')
L.append(control('cross-session', '(let* (((ek:recorded $s1 $t1) (ek:rec-refl (ek:rec-open ' + PAB + ') ' + A + ')) ((ek:recorded $o1 $u1) (ek:rec-refl (ek:rec-open ' + PAB + ') ' + A + ')) ((ek:recorded $s2 $t2) (ek:rec-step $s1 $u1 (ek:cite ' + EQAB + ' 0) ek:nil ek:nil))) $t2)', 'ek:refused'))
L.append(control('cross-session-certificate', '(let* (((ek:recorded $s1 $t1) (ek:rec-refl (ek:rec-open ' + PAB + ') ' + A + ')) ((ek:recorded $o1 $u1) (ek:rec-refl (ek:rec-open ' + PAB + ') ' + A + '))) (ek:rec-certificate $s1 $u1))', 'ek:refused'))
L.append(control('unrecorded-premise', '(let* (((ek:recorded $s1 $t1) (ek:rec-step (ek:rec-open ' + PAB + ') (ek:lcf-refl ' + PAB + ' ' + A + ') (ek:cite ' + EQAB + ' 0) ek:nil ek:nil))) $t1)', 'ek:refused'))
L.append(control('recorded-foreign-step', '(let* (((ek:recorded $s1 $t1) (ek:rec-refl (ek:rec-open ' + PAB + ') ' + A + ')) ((ek:recorded $s2 $t2) (ek:rec-step $s1 $t1 (ek:cite ' + EQBC + ' 0) ek:nil ek:nil))) $t2)', 'ek:refused'))
(KERNEL / 'equation_kernel_review_controls_v0.metta').write_text('\n'.join(L) + '\n')
print(sum(1 for l in L for x in l.split('\n') if x.startswith('!(ek:control')))
