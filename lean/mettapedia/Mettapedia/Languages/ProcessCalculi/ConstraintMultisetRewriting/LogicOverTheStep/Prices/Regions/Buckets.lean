import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Cost

/-!
# Three questions, three buckets, and hints

For a claim `q` and a certificate relation `R` three questions are kept apart:

1. **Is this supplied certificate valid?** That is `R n q = true`. It is decidable exactly when the
   relation is computable (`check_decidable_iff`): this is the hypothesis on the relation, stated as
   such. Instance: the step index of bounded evaluation for halting (`haltR_computable`). Control: the
   same property with a relation that reads the answer instead of checking a certificate, whose checking
   is not decidable (`Controls.oracleR_not_computable`); so the first bucket is a property of the
   relation, not of the claim.
2. **Is there a certificate?** That is `Certified R q`. For every computable relation it is
   semidecidable (`certified_re`): the search halts exactly on the certified instances. For halting it is
   not decidable (`not_computablePred_haltR`, from Mathlib's `ComputablePred.halting_problem`); for
   perfect squares it is decidable (`Controls.square_decidable`). So provability in one fixed effective
   theory, whose proofs are checked by a computable relation, is always of this kind.
3. **Is the claim true?** For the claim "program `c` never halts on input `0`" truth is not
   semidecidable (`never_halting_not_re`, Mathlib's `ComputablePred.halting_problem_not_re`), and true
   claims of it exist (`exists_never_halting`). Hence no computable certificate relation certifies
   exactly the true claims (`no_certificates_for_never_halting`), and every computable relation that
   certifies only true claims misses a true one (`sound_misses_never_halting`); such relations exist,
   for instance one certifying a single never-halting program (`Controls.one_claim_system`).
   **This is about truth, not about any proof system**: for every fixed proof system with computable
   checking, "has a proof"
   is of kind 2; what lies beyond is the gap between having a proof and being true. Control: a
   decidable property's negation is semidecidable (`Controls.not_square_re`), and by Post's theorem a
   property is decidable exactly when it and its negation are semidecidable
   (`decidable_iff_both_semidecidable`).

## Hints

A hint is a certificate bound supplied with the instance; the hinted check searches up to the hint
(`hinted`). It is **sound for every hint** (`hinted_sound`); on a certified instance it **answers exactly
when the hint is at least the least certificate** (`hinted_iff_least_le`); a larger hint keeps an answer
(`hinted_mono`); and **the certificate it finds is the least one, whatever the hint**
(`hintedFind_eq_some_iff`, `hintedFind_agree`). So a hint cuts the search off at the hint and never
changes the answer; on a certified instance it does not make the yes come before the least certificate
(`SearchBudgets.same_yes_condition`). A hint that is too small is not a no (`Controls.small_hint`). The
hinted check is a program with a cost on every input (`hinted_program`), where the ambient search has
none on the uncertified instances (`ambient_program`).

**A region with a computable bound is exactly the case where the hint is computed from the instance**
(`boundsOn_iff_hinted`); there "not found within the hint" is a no (`not_certified_of_hinted_false`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions

open CheckerTower (Certified)
open Nat.Partrec

section Buckets

variable {Q : Type} [Primcodable Q] (R : ℕ → Q → Bool)

/-! ## 1. Checking a supplied certificate -/

/-- **Bucket 1 is the hypothesis on the relation**: checking a supplied certificate is decidable exactly
when the relation is computable. -/
theorem check_decidable_iff :
    ComputablePred (fun p : ℕ × Q => R p.1 p.2 = true) ↔ Computable₂ R := by
  constructor
  · intro decidable
    exact (ComputablePred.decide decidable).of_eq fun p => by simp
  · intro hR
    exact ComputablePred.computable_iff.mpr ⟨fun p => R p.1 p.2, hR, rfl⟩

/-! ## 2. Having a certificate -/

/-- **Bucket 2: having a certificate is semidecidable**, for every computable relation. -/
theorem certified_re (hR : Computable₂ R) : REPred (Certified R) := by
  have search : Partrec fun q : Q => Nat.rfind fun n => (R n q : Part Bool) :=
    Partrec.rfind ((hR.comp Computable.snd Computable.fst).to₂.partrec₂)
  refine search.dom_re.of_eq fun q => ?_
  constructor
  · intro dom
    exact ⟨_, (Part.mem_some_iff.mp (Nat.rfind_spec (Part.get_mem dom))).symm⟩
  · rintro ⟨n, found⟩
    obtain ⟨m, mem, _⟩ := Nat.rfind_min' (p := fun n => R n q) found
    exact Part.dom_iff_mem.mpr ⟨m, mem⟩

/-- **Post's theorem, in this setting**: decidable exactly when the property and its negation are both
semidecidable. -/
theorem decidable_iff_both_semidecidable :
    ComputablePred (Certified R) ↔ REPred (Certified R) ∧ REPred fun q => ¬ Certified R q :=
  ComputablePred.computable_iff_re_compl_re'

/-- **For a computable relation, decidable exactly when "no certificate" is semidecidable.** -/
theorem decidable_iff_uncertified_re (hR : Computable₂ R) :
    ComputablePred (Certified R) ↔ REPred fun q => ¬ Certified R q := by
  rw [decidable_iff_both_semidecidable]
  exact ⟨fun both => both.2, fun neg => ⟨certified_re R hR, neg⟩⟩

end Buckets

/-- **Bucket 2 for halting**: semidecidable and not decidable. -/
theorem halting_bucket_two : REPred (Certified haltR) ∧ ¬ ComputablePred (Certified haltR) :=
  ⟨certified_re haltR haltR_computable, not_computablePred_haltR⟩

/-! ## 3. Being true -/

/-- **Bucket 3: the truth of "never halts" is not semidecidable.** -/
theorem never_halting_not_re : ¬ REPred fun c : Code => ¬ (Code.eval c 0).Dom :=
  ComputablePred.halting_problem_not_re 0

/-- True never-halting claims exist: a program for the nowhere-defined function. -/
theorem exists_never_halting : ∃ c : Code, ¬ (Code.eval c 0).Dom := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp Nat.Partrec.none
  exact ⟨c, by rw [hc]; exact Part.not_none_dom⟩

/-- **No computable certificate relation certifies exactly the true never-halting claims.** -/
theorem no_certificates_for_never_halting :
    ¬ ∃ R' : ℕ → Code → Bool, Computable₂ R' ∧ ∀ c, Certified R' c ↔ ¬ (Code.eval c 0).Dom := by
  rintro ⟨R', hR', same⟩
  exact never_halting_not_re ((certified_re R' hR').of_eq same)

/-- **Every computable certificate relation that certifies only true never-halting claims misses a true
one.** -/
theorem sound_misses_never_halting {R' : ℕ → Code → Bool} (hR' : Computable₂ R')
    (sound : ∀ c, Certified R' c → ¬ (Code.eval c 0).Dom) :
    ∃ c, ¬ (Code.eval c 0).Dom ∧ ¬ Certified R' c := by
  by_contra complete
  apply no_certificates_for_never_halting
  refine ⟨R', hR', fun c => ⟨sound c, fun never => ?_⟩⟩
  by_contra notCertified
  exact complete ⟨c, never, notCertified⟩

/-- The program `zero` halts, so halting claims are not all false either. -/
theorem zero_halts : (Code.eval Code.zero 0).Dom := by
  have same : Code.eval (Code.const 0) 0 = Part.some 0 := Code.eval_const 0 0
  rw [show Code.const 0 = Code.zero from rfl] at same
  rw [same]
  exact Part.some_dom 0

/-! ## Hints -/

section Hints

variable {Q : Type} [Primcodable Q] (R : ℕ → Q → Bool)

/-- **The hinted check**: search for a certificate up to the hint. -/
def hinted (q : Q) (hint : ℕ) : Bool := anyBelow R q (hint + 1)

omit [Primcodable Q] in
theorem hinted_iff (q : Q) (hint : ℕ) : hinted R q hint = true ↔ ∃ n ≤ hint, R n q = true := by
  unfold hinted
  rw [anyBelow_iff]
  exact exists_congr fun n => and_congr_left fun _ => Nat.lt_succ_iff

omit [Primcodable Q] in
/-- **Sound for every hint.** -/
theorem hinted_sound {q : Q} {hint : ℕ} (yes : hinted R q hint = true) : Certified R q := by
  obtain ⟨n, _, found⟩ := (hinted_iff R q hint).mp yes
  exact ⟨n, found⟩

omit [Primcodable Q] in
/-- **Answers exactly when the hint is at least the least certificate.** -/
theorem hinted_iff_least_le {q : Q} (certified : Certified R q) (hint : ℕ) :
    hinted R q hint = true ↔ Nat.find certified ≤ hint := by
  rw [hinted_iff]
  constructor
  · rintro ⟨n, le, found⟩
    exact (Nat.find_min' certified found).trans le
  · intro le
    exact ⟨Nat.find certified, le, Nat.find_spec certified⟩

omit [Primcodable Q] in
/-- **A larger hint keeps an answer.** -/
theorem hinted_mono {q : Q} {hint hint' : ℕ} (le : hint ≤ hint') (yes : hinted R q hint = true) :
    hinted R q hint' = true := by
  obtain ⟨n, small, found⟩ := (hinted_iff R q hint).mp yes
  exact (hinted_iff R q hint').mpr ⟨n, small.trans le, found⟩

theorem hinted_computable (hR : Computable₂ R) : Computable₂ (hinted R) :=
  (computable_anyBelow (fun n (p : Q × ℕ) => R n p.1)
    (hR.comp Computable.fst (Computable.fst.comp Computable.snd)) (m := fun p => p.2 + 1)
    ((Computable.succ.comp Computable.snd).of_eq fun _ => rfl)).of_eq fun _ => rfl

/-- **The certificate found with a hint**: the least certificate, when one lies within the hint. -/
def hintedFind (q : Q) (hint : ℕ) : Option ℕ :=
  if h : ∃ n, n ≤ hint ∧ R n q = true then some (Nat.find h) else Option.none

omit [Primcodable Q] in
/-- **With any hint, the certificate found is the least certificate.** -/
theorem hintedFind_eq_some_iff (q : Q) (hint n : ℕ) :
    hintedFind R q hint = some n ↔ n ≤ hint ∧ R n q = true ∧ ∀ j < n, R j q = false := by
  unfold hintedFind
  split
  · rename_i h
    rw [Option.some.injEq, Nat.find_eq_iff]
    constructor
    · rintro ⟨⟨le, found⟩, least⟩
      exact ⟨le, found, fun j lt => Bool.eq_false_iff.mpr fun yes => least j lt ⟨by omega, yes⟩⟩
    · rintro ⟨le, found, least⟩
      refine ⟨⟨le, found⟩, fun j lt both => ?_⟩
      rw [least j lt] at both
      exact Bool.noConfusion both.2
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨le, found, _⟩
    exact h ⟨n, le, found⟩

omit [Primcodable Q] in
/-- **Hints never change the answer**: two hints that find a certificate find the same one. -/
theorem hintedFind_agree {q : Q} {hint hint' n n' : ℕ} (first : hintedFind R q hint = some n)
    (second : hintedFind R q hint' = some n') : n = n' := by
  obtain ⟨_, found, least⟩ := (hintedFind_eq_some_iff R q hint n).mp first
  obtain ⟨_, found', least'⟩ := (hintedFind_eq_some_iff R q hint' n').mp second
  rcases Nat.lt_trichotomy n n' with lt | same | gt
  · rw [least' n lt] at found
    exact absurd found Bool.false_ne_true
  · exact same
  · rw [least n' gt] at found'
    exact absurd found' Bool.false_ne_true

omit [Primcodable Q] in
/-- **A region with a bound is exactly the case where the hint is computed from the instance.** -/
theorem boundsOn_iff_hinted {D : Q → Bool} {b : Q → ℕ} :
    BoundsOn R D b ↔ ∀ q, D q = true → Certified R q → hinted R q (b q) = true :=
  ⟨fun bounds q inside certified => (hinted_iff R q (b q)).mpr (bounds q inside certified),
    fun hints q inside certified => (hinted_iff R q (b q)).mp (hints q inside certified)⟩

omit [Primcodable Q] in
/-- **On such a region, "not found within the computed hint" is a no.** -/
theorem not_certified_of_hinted_false {D : Q → Bool} {b : Q → ℕ} (bounds : BoundsOn R D b) {q : Q}
    (inside : D q = true) (notFound : hinted R q (b q) = false) : ¬ Certified R q := by
  intro certified
  rw [(boundsOn_iff_hinted R).mp bounds q inside certified] at notFound
  exact Bool.noConfusion notFound

end Hints

/-- **The hinted check is a program with a cost on every input**: on the pair of an instance and a
hint it answers `1` exactly when the hinted check says yes. -/
theorem hinted_program (R : ℕ → ℕ → Bool) (hR : Computable₂ R) :
    ∃ d : Code, ∀ q hint, (cost d (Nat.pair q hint)).Dom ∧
      (1 ∈ Code.eval d (Nat.pair q hint) ↔ hinted R q hint = true) := by
  let f : ℕ → ℕ := fun p => bif hinted R p.unpair.1 p.unpair.2 then 1 else 0
  have hf : Computable f :=
    Computable.cond ((hinted_computable R hR).comp (Computable.fst.comp Computable.unpair)
      (Computable.snd.comp Computable.unpair)) (Computable.const 1) (Computable.const 0)
  obtain ⟨d, hd⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  have evalD : ∀ p, Code.eval d p = Part.some (f p) := fun p => by
    rw [hd]
    exact PFun.coe_val f p
  refine ⟨d, fun q hint => ⟨(cost_dom_iff d _).mpr (by rw [evalD]; exact Part.some_dom _), ?_⟩⟩
  rw [evalD, Part.mem_some_iff]
  show 1 = (bif hinted R (Nat.pair q hint).unpair.1 (Nat.pair q hint).unpair.2 then 1 else 0) ↔ _
  simp only [Nat.unpair_pair]
  cases hinted R q hint <;> simp

/-! ## Controls -/

namespace Controls

/-- **A relation that reads the answer** instead of checking a certificate. -/
noncomputable def oracleR (_ : ℕ) (c : Code) : Bool := certifiedRegion haltR c

theorem certified_oracleR_iff (c : Code) : Certified oracleR c ↔ Certified haltR c :=
  ⟨fun ⟨_, found⟩ => (certifiedRegion_iff haltR c).mp found,
    fun certified => ⟨0, (certifiedRegion_iff haltR c).mpr certified⟩⟩

/-- **Control for bucket 1: the same property, a relation whose checking is not decidable.** -/
theorem oracleR_not_computable : ¬ Computable₂ oracleR := by
  intro computable
  apply not_computablePred_haltR
  refine ComputablePred.computable_iff.mpr ⟨fun c => oracleR 0 c,
    computable.comp (Computable.const 0) Computable.id, funext fun c => propext ?_⟩
  exact ((certifiedRegion_iff haltR c).symm)

/-- **Bucket 3 is not vacuous**: a computable certificate relation that certifies one true
never-halting claim and only true ones, and therefore misses another true one. -/
theorem one_claim_system :
    ∃ R' : ℕ → Code → Bool, Computable₂ R' ∧ (∃ c, Certified R' c) ∧
      (∀ c, Certified R' c → ¬ (Code.eval c 0).Dom) ∧
      ∃ c, ¬ (Code.eval c 0).Dom ∧ ¬ Certified R' c := by
  obtain ⟨c₀, never⟩ := exists_never_halting
  let _ : DecidableEq Code := Encodable.decidableEqOfEncodable Code
  let R' : ℕ → Code → Bool := fun _ c => decide (c = c₀)
  have hR' : Computable₂ R' :=
    (Primrec.eq.decide.comp Primrec.snd (Primrec.const c₀)).to_comp
  have sound : ∀ c, Certified R' c → ¬ (Code.eval c 0).Dom := by
    rintro c ⟨_, found⟩
    have same : c = c₀ := of_decide_eq_true found
    rw [same]
    exact never
  exact ⟨R', hR', ⟨c₀, 0, decide_eq_true rfl⟩, sound, sound_misses_never_halting hR' sound⟩

/-- **Control for bucket 3: the negation of a decidable property is semidecidable.** -/
theorem not_square_re : REPred fun q => ¬ Certified squareR q :=
  square_decidable.not.to_re

/-- **Control for hints: a hint that is too small is not a no**; a large enough one answers. -/
theorem small_hint :
    hinted squareR 9 2 = false ∧ Certified squareR 9 ∧ hinted squareR 9 3 = true ∧
      hintedFind squareR 9 5 = some 3 :=
  ⟨by decide, ⟨3, rfl⟩, by decide, (hintedFind_eq_some_iff squareR 9 5 3).mpr
    ⟨by decide, rfl, fun j lt => by interval_cases j <;> rfl⟩⟩

end Controls

#print axioms check_decidable_iff
#print axioms certified_re
#print axioms decidable_iff_both_semidecidable
#print axioms decidable_iff_uncertified_re
#print axioms halting_bucket_two
#print axioms never_halting_not_re
#print axioms exists_never_halting
#print axioms no_certificates_for_never_halting
#print axioms sound_misses_never_halting
#print axioms zero_halts
#print axioms hinted_iff
#print axioms hinted_sound
#print axioms hinted_iff_least_le
#print axioms hinted_mono
#print axioms hinted_computable
#print axioms hintedFind_eq_some_iff
#print axioms hintedFind_agree
#print axioms boundsOn_iff_hinted
#print axioms not_certified_of_hinted_false
#print axioms hinted_program
#print axioms Controls.certified_oracleR_iff
#print axioms Controls.oracleR_not_computable
#print axioms Controls.one_claim_system
#print axioms Controls.not_square_re
#print axioms Controls.small_hint

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions
