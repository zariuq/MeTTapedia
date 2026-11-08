import Mettapedia.Logic.ASP.WeightCertificate
import Mettapedia.Logic.ASP.WeightDefsNormalize

/-!
# Controls for weight definitions and weight steps

Values are computed by the kernel (`decide +kernel`).

## Stable models of programs with definitions

* `p :- W. a.` with `W ↔ 2 ≤ {a = 1, not b = 1}`: the stable model is `{a, W, p}`
  (`atLeast_stable`); `{a}` is not one, since the definition gives `W` (`atLeast_without_def`),
  nor `{a, W}`, which leaves `p` underived (`atLeast_without_head`), nor `{a, b, W, p}`, whose `b`
  has no rule and whose `W` the definition refuses (`atLeast_with_b`).
* **Acyclicity is needed for the correspondence with the normalization**: `a :- W.` with
  `W ↔ 1 ≤ {a = 1}` has `W` on a positive cycle (`cyclic_not_acyclic`, `cyclic_acyclicB`). `{a, W}`
  is a stable model of the program with definitions (`cyclic_stable`), but not of its weight
  program, whose least model is empty (`cyclic_weight_not_stable`).

## The C solver's refutation over the reduced completion

`(choice a () ()) (choice b () ()) (weight-constraint 1 ((a 1) (b 1)) ()) (weight-constraint 1 () ((a 1) (b 1)))`
is read by the library as six rules, `a :- not (asp:out a)`, `(asp:out a) :- not a` and the same for
`b`, and `asp:falsum :- (asp:weight k), not asp:falsum` for `k = 0, 1`, one shared falsum atom, with
the definitions `(asp:weight 0) ↔ 1 ≤ {a = 1, b = 1}` and `(asp:weight 1) ↔ 1 ≤ {not a = 1, not b = 1}`
(`cProgram`). Its numbering is the C solver's (`cProgram_varList`): atoms by last occurrence, and no
body, since the bodies of the choice rules are unit bodies and the other rules are those of
`asp:falsum`. The completion has 13 clauses (`cProgram_inputs_length`): one per choice rule,
`(asp:out a) ∨ a` for `a :- not (asp:out a)`, the unit `not (asp:weight k)` for each rule of
`asp:falsum`, then the support clauses, `not asp:falsum` among them. The C solver's literals `±(n + 1)`
are the literals of variable `n` here; identifiers, hints and definition numbers carry over unchanged.

The certificate (`cCertificate`) has the C solver's three weight steps, numbered for this completion,
and the empty clause by RUP from them and the two units of the rules of `asp:falsum`.

* The certificate is accepted (`cCertificate_accepted`), so the program has no stable model
  (`cProgram_no_stable`), and neither does the normalization of its weight program
  (`cProgram_normalize_no_stable`), by the correspondence of `WeightDefsNormalize`.
* Refused mutations: the first weight step over the other definition (`cWrongDef_refused`), whose
  clause that definition does not imply (`cWrongDef_not_implied`); the third step with `a` for `not a`
  (`cNotImplied_refused`, `cNotImplied_not_implied`); the certificate without its last step
  (`cTruncated_refused`).
* Weight steps on their own: a clause with `not W` (`cNegative_step`); two literals over one atom
  each counting (`twice_step`, `twice_step_short`).

## A loop step over a definition atom

The program whose only definition, `W ↔ 0 ≤ {}`, always holds has the stable model `{W}`
(`alwaysW_stable`), so no certificate is accepted for it (`alwaysW_certificates_refused`). The loop
clause of `{W}` over the rules alone is `not W`, which is false in that model: a definition's atom
has no rules, so its loop clause ignores the support the definition gives. The certificate of that
loop step, the weight step `W` and the empty clause would refute the program; the loop step is
refused (`alwaysW_loop_refused`), as the C checker refuses it, and so is the certificate
(`loopOverDef_refused`), while its weight step alone is accepted (`alwaysW_weight_step`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.WeightStepControls

open DefProgram Mettapedia.GSLT.Logic PropositionalFormula

/-! ## Stable models -/

/-- The atoms of the semantic examples. -/
inductive Atom
  | a
  | b
  | p
  | w
  deriving DecidableEq, Repr

/-- `p :- W. a.` with `W ↔ 2 ≤ {a = 1, not b = 1}`. -/
def atLeast : DefProgram Atom :=
  ⟨[⟨.p, [.w], []⟩, ⟨.a, [], []⟩], [⟨.w, 2, [(.a, 1)], [(.b, 1)]⟩]⟩

theorem atLeast_stable : atLeast.Stable ↑({.a, .w, .p} : Finset Atom) :=
  (atLeast.isStable_iff _).mp (by decide +kernel)

theorem atLeast_without_def : ¬ atLeast.Stable ↑({.a} : Finset Atom) := fun h =>
  absurd ((atLeast.isStable_iff _).mpr h) (by decide +kernel)

theorem atLeast_without_head : ¬ atLeast.Stable ↑({.a, .w} : Finset Atom) := fun h =>
  absurd ((atLeast.isStable_iff _).mpr h) (by decide +kernel)

theorem atLeast_with_b : ¬ atLeast.Stable ↑({.a, .b, .w, .p} : Finset Atom) := fun h =>
  absurd ((atLeast.isStable_iff _).mpr h) (by decide +kernel)

/-- `a :- W.` with `W ↔ 1 ≤ {a = 1}`: `W` depends positively on itself through `a`. -/
def cyclic : DefProgram Atom := ⟨[⟨.a, [.w], []⟩], [⟨.w, 1, [(.a, 1)], []⟩]⟩

theorem cyclic_not_acyclic : ¬ cyclic.Acyclic := fun h =>
  h _ List.mem_cons_self (.tail (.single (.inl ⟨_, List.mem_cons_self, rfl, List.mem_cons_self⟩))
    (.inr ⟨_, List.mem_cons_self, rfl, List.mem_cons_self⟩))

theorem cyclic_acyclicB : cyclic.acyclicB = false := by decide +kernel

/-- With the definition, `{a, W}` supports itself. -/
theorem cyclic_stable : cyclic.Stable ↑({.a, .w} : Finset Atom) :=
  (cyclic.isStable_iff _).mp (by decide +kernel)

/-- As a weight program, it does not. -/
theorem cyclic_weight_not_stable : ¬ cyclic.toWProgram.Stable ↑({.a, .w} : Finset Atom) := fun h =>
  absurd ((cyclic.toWProgram.isStable_iff _).mpr h) (by decide +kernel)

/-! ## The C solver's refutation -/

/-- The atoms of the library's translation. -/
inductive LAtom
  | a
  | b
  /-- `(asp:out a)` -/
  | outA
  /-- `(asp:out b)` -/
  | outB
  /-- `asp:falsum` -/
  | falsum
  /-- `(asp:weight 0)` -/
  | weight0
  /-- `(asp:weight 1)` -/
  | weight1
  deriving DecidableEq, Repr

open LAtom

/-- The library's translation of the two choices and the two weight constraints. -/
def cProgram : DefProgram LAtom where
  rules := [⟨a, [], [outA]⟩, ⟨outA, [], [a]⟩, ⟨b, [], [outB]⟩, ⟨outB, [], [b]⟩,
    ⟨falsum, [weight0], [falsum]⟩, ⟨falsum, [weight1], [falsum]⟩]
  defs := [⟨weight0, 1, [(a, 1), (b, 1)], []⟩, ⟨weight1, 1, [], [(a, 1), (b, 1)]⟩]

theorem cProgram_falsum : cProgram.rules.falsum falsum = true ∧ cProgram.rules.falsum a = false := by
  decide +kernel

/-- The C solver's numbering: atoms in the order of their last occurrence; the unit bodies of the
choice rules have no variables. -/
theorem cProgram_varList : cProgram.varList =
    [.atom outA, .atom outB, .atom falsum, .atom weight0, .atom weight1, .atom a, .atom b] := by
  decide +kernel

theorem cProgram_inputs_length : cProgram.inputs.length = 13 := by decide +kernel

/-- The clause `(asp:out a) ∨ a` of the rule `a :- not (asp:out a)`, the clauses of the two rules of
`asp:falsum` and the support clause of `asp:falsum`. -/
theorem cProgram_inputs :
    cProgram.inputs[0]? = some (1, [.pos 0, .pos 5]) ∧ cProgram.inputs[4]? = some (5, [.neg 3]) ∧
      cProgram.inputs[5]? = some (6, [.neg 4]) ∧ cProgram.inputs[8]? = some (9, [.neg 2]) := by
  decide +kernel

/-- The certificate over the reduced completion, around its first and third steps. -/
def cCertWith (first third : WCertStep) : List WCertStep :=
  [first, .weight 15 [.pos 4, .pos 6] 1, third, .lrat (.rup 17 [] [6, 5, 14, 15, 16])]

/-- `(certificate (weight 14 (5 6) 1) (weight 15 (5 7) 1) (weight 16 (-6 4) 0) (rup 17 () (6 5 14 15 16)))`. -/
def cCertificate : List WCertStep := cCertWith (.weight 14 [.pos 4, .pos 5] 1) (.weight 16 [.neg 5, .pos 3] 0)

theorem cCertificate_accepted : cProgram.checkCert cCertificate = true := by decide +kernel

theorem cProgram_no_stable (S : Set LAtom) : ¬ cProgram.Stable S :=
  cProgram.checkCert_sound cCertificate_accepted S

theorem cProgram_wellFormedB : cProgram.wellFormedB = true := by decide +kernel

/-- The normalization of the weight program has no stable model either. -/
theorem cProgram_normalize_no_stable (M : Set (LAtom ⊕ Aux LAtom)) : ¬ cProgram.toWProgram.normalize.Stable M :=
  fun h => cProgram_no_stable _ ((stable_iff_exists_normalize (cProgram.wellFormed_of_wellFormedB cProgram_wellFormedB)
    (cProgram.acyclic_of_wellFormedB cProgram_wellFormedB) _).mpr ⟨M, h, rfl⟩)

/-! ### Refused mutations -/

/-- The clause `(asp:weight 1) ∨ a` over the definition of `(asp:weight 0)`. -/
theorem cWrongDef_refused : cProgram.checkCert (cCertWith (.weight 14 [.pos 4, .pos 5] 0)
    (.weight 16 [.neg 5, .pos 3] 0)) = false := by
  decide +kernel

theorem cWrongDef_step_refused : cProgram.weightStepOk [.pos 4, .pos 5] 0 = false := by decide +kernel

/-- Everything false satisfies the definition of `(asp:weight 0)` and falsifies the clause. -/
theorem cWrongDef_not_implied :
    ((fun _ => false : ℕ → Bool) 3 = true ↔
        1 ≤ numWeight (fun x => cProgram.index (.atom x)) (fun _ => false) (cProgram.defs[0]'(by decide)).terms) ∧
      Clause.sat (fun _ => false) [.pos 4, .pos 5] = false := by
  decide +kernel

/-- The clause `a ∨ (asp:weight 0)`, which the definition does not imply. -/
theorem cNotImplied_refused : cProgram.checkCert (cCertWith (.weight 14 [.pos 4, .pos 5] 1)
    (.weight 16 [.pos 5, .pos 3] 0)) = false := by
  decide +kernel

theorem cNotImplied_not_implied :
    ((fun _ => false : ℕ → Bool) 3 = true ↔
        1 ≤ numWeight (fun x => cProgram.index (.atom x)) (fun _ => false) (cProgram.defs[0]'(by decide)).terms) ∧
      Clause.sat (fun _ => false) [.pos 5, .pos 3] = false := by
  decide +kernel

theorem cTruncated_refused : cProgram.checkCert (cCertificate.take 3) = false := by decide +kernel

/-! ### Weight steps on their own -/

/-- `not (asp:weight 1) ∨ not a ∨ not b`: with `a` and `b` true, both literals of the definition are
forced not to contribute. -/
theorem cNegative_step : cProgram.weightStepOk [.neg 4, .neg 5, .neg 6] 1 = true := by decide +kernel

/-- `W ↔ 2 ≤ {a = 1, a = 1}`. -/
def twice (bound : ℕ) : DefProgram LAtom := ⟨[], [⟨weight0, bound, [(a, 1), (a, 1)], []⟩]⟩

/-- `W ∨ not a`: `a` true forces both literals over `a`, weighing `2`. -/
theorem twice_step : (twice 2).weightStepOk [.pos 0, .neg 1] 0 = true := by decide +kernel

/-- With the bound `3`, they weigh too little. -/
theorem twice_step_short : (twice 3).weightStepOk [.pos 0, .neg 1] 0 = false := by decide +kernel

/-! ## A loop step over a definition atom -/

/-- The definition `W ↔ 0 ≤ {}`, without rules. -/
def alwaysW : DefProgram LAtom := ⟨[], [⟨weight0, 0, [], []⟩]⟩

theorem alwaysW_stable : alwaysW.Stable ↑({weight0} : Finset LAtom) :=
  (alwaysW.isStable_iff _).mp (by decide +kernel)

theorem alwaysW_certificates_refused (steps : List WCertStep) : alwaysW.checkCert steps = false := by
  cases accepted : alwaysW.checkCert steps with
  | false => rfl
  | true => exact absurd alwaysW_stable (alwaysW.checkCert_sound accepted _)

/-- The loop step `not W` over the set `{W}`, for `W`. -/
theorem alwaysW_loop_refused : alwaysW.certStep alwaysW.inputs (.loop 2 [.neg 0] [0] 0) = none := by
  decide +kernel

theorem alwaysW_weight_step : (alwaysW.certStep alwaysW.inputs (.weight 3 [.pos 0] 0)).isSome = true := by
  decide +kernel

/-- The certificate the C checker accepts for a program with a stable model. -/
def loopOverDef : List WCertStep := [.loop 2 [.neg 0] [0] 0, .weight 3 [.pos 0] 0, .lrat (.rup 4 [] [2, 3])]

theorem loopOverDef_refused : alwaysW.checkCert loopOverDef = false := by decide +kernel

end Mettapedia.Logic.ASP.WeightStepControls
