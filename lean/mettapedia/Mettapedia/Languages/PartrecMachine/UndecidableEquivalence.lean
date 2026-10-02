import Mettapedia.Languages.PartrecMachine.HistoryEquivalence
import Mettapedia.Languages.PartrecMachine.Rice
import Mettapedia.GSLT.LanguageDef.EffectiveSection

/-!
# An interactive theory with undecidable static equivalence

The history theory is an interactive GSLT whose static equivalence on the
interacting sort is not decidable, and which therefore has no effective
section.

The witness is one family of pairs of closed histories.  Fix a universal
program of the machine.  For each number `n`, let `c n` be the pending
evaluation of that program on the input `[n, 0]`, which runs the partial
recursive function with code `n` on `0`.  The two histories `Now(c n)` and
`Flag(c n)` are equal exactly when that function halts on `0`.

* The codes of the two histories are computable functions of `n`: only a
  unary numeral varies.
* The predicate "`Now(c n)` equals `Flag(c n)`" is not computable: it is the
  halting problem.
* An effective section would decide the predicate.  So no section of the
  history theory is effective, although, like every theory, it has sections.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.GSLT.LanguageDef
open Turing.ToPartrec

/-! ## The family -/

/-- The universal program pending on the input `[index, 0]`. -/
noncomputable def probe (index : ℕ) : Pattern :=
  normalTerm universal .halt [index, 0]

theorem probe_inImage (index : ℕ) : InImage (probe index) :=
  .inl ⟨universal, .halt, [index, 0], rfl⟩

/-- The probe halts exactly when the partial recursive function with that
code halts on `0`. -/
theorem probe_halts_iff (index : ℕ) :
    Halts (probe index) ↔ ((Denumerable.ofNat Nat.Partrec.Code index).eval 0).Dom := by
  unfold Halts probe
  simp only [adequacy, universal_eval, Part.map_eq_map, Part.mem_map_iff, Part.dom_iff_mem]
  constructor
  · rintro ⟨output, value, member, -⟩
    exact ⟨value, member⟩
  · rintro ⟨value, member⟩
    exact ⟨[value], value, member, rfl⟩

/-- The halting problem, indexed by the numbers of codes. -/
theorem halting_family_not_computable :
    ¬ ComputablePred fun index : ℕ =>
      ((Denumerable.ofNat Nat.Partrec.Code index).eval 0).Dom := by
  rintro ⟨decidable, computable⟩
  apply ComputablePred.halting_problem 0
  refine ComputablePred.of_eq
    (p := fun code : Nat.Partrec.Code =>
      ((Denumerable.ofNat Nat.Partrec.Code (Encodable.encode code)).eval 0).Dom)
    ⟨fun code => decidable (Encodable.encode code), computable.comp Computable.encode⟩ ?_
  intro code
  rw [Denumerable.ofNat_encode]

/-- Halting of the probe is not decidable. -/
theorem probe_halts_not_computable : ¬ ComputablePred fun index : ℕ => Halts (probe index) :=
  fun decided => halting_family_not_computable (decided.of_eq probe_halts_iff)

/-- `Now` of the probe, as a member of the fibre. -/
noncomputable def nowProbe (index : ℕ) : historyTheory.toGSLT.Term :=
  nowTerm (probe index) (probe_inImage index)

/-- `Flag` of the probe, as a member of the fibre. -/
noncomputable def flagProbe (index : ℕ) : historyTheory.toGSLT.Term :=
  flagTerm (probe index) (probe_inImage index)

/-- **The static equivalence of the history theory is not decidable.**  No
computable procedure decides, given `n`, whether the two histories of the
`n`th probe are equal. -/
theorem equivalence_not_computable :
    ¬ ComputablePred fun index : ℕ =>
      historyTheory.toGSLT.equations.r (nowProbe index) (flagProbe index) := by
  intro decided
  apply probe_halts_not_computable
  refine decided.of_eq fun index => ?_
  exact now_equivalent_flag_iff (probe_inImage index)

/-! ## The codes of the family are computable -/

/-- The code of a constructor application, from the code of its label and the
code of its argument list. -/
def applyCode (label arguments : ℕ) : ℕ := Nat.pair 2 (Nat.pair label arguments)

/-- The code of a nonempty list, from the codes of its head and tail. -/
def consCode (head tail : ℕ) : ℕ := Nat.succ (Nat.pair head tail)

theorem patternCode_apply (label : String) (arguments : List Pattern) :
    patternCode (.apply label arguments) =
      applyCode (stringCode label) (patternListCode arguments) := by
  simp [patternCode, applyCode]

theorem patternListCode_cons (pattern : Pattern) (patterns : List Pattern) :
    patternListCode (pattern :: patterns) =
      consCode (patternCode pattern) (patternListCode patterns) := by
  simp [patternListCode, consCode]

theorem primrec_applyCode : Primrec₂ applyCode :=
  Primrec₂.natPair.comp₂ (Primrec₂.const 2) Primrec₂.natPair

theorem primrec_consCode : Primrec₂ consCode :=
  Primrec.succ.comp₂ Primrec₂.natPair

/-- The code of the successor of a numeral, from the code of the numeral. -/
def successorCode (code : ℕ) : ℕ := applyCode (stringCode "Succ") (consCode code 0)

/-- The code of the unary numeral. -/
def numeralCode (index : ℕ) : ℕ := successorCode^[index] (applyCode (stringCode "Zero") 0)

theorem patternCode_encNat (index : ℕ) : patternCode (encNat index) = numeralCode index := by
  induction index with
  | zero => simp [encNat, numeralCode, patternCode_apply, patternListCode]
  | succ index recurse =>
      rw [numeralCode, Function.iterate_succ_apply', ← numeralCode, ← recurse]
      simp [encNat, successorCode, patternCode_apply, patternListCode, consCode]

theorem primrec_successorCode : Primrec successorCode :=
  primrec_applyCode.comp (Primrec.const _)
    (primrec_consCode.comp Primrec.id (Primrec.const 0))

theorem primrec_numeralCode : Primrec numeralCode :=
  Primrec.nat_iterate Primrec.id (Primrec.const _) (primrec_successorCode.comp₂ Primrec₂.right)

/-- The code of the probe, from the code of its numeral. -/
noncomputable def probeCode (numeral : ℕ) : ℕ :=
  applyCode (stringCode "Normal")
    (consCode (patternCode (encCode universal))
      (consCode (patternCode (encCont .halt))
        (consCode
          (applyCode (stringCode "Cons")
            (consCode numeral (consCode (patternCode (encNats [0])) 0)))
          0)))

theorem patternCode_probe (index : ℕ) :
    patternCode (probe index) = probeCode (numeralCode index) := by
  rw [← patternCode_encNat]
  simp [probe, normalTerm, encNats, probeCode, patternCode_apply, patternListCode, consCode]

theorem primrec_probeCode : Primrec probeCode :=
  primrec_applyCode.comp (Primrec.const _)
    (primrec_consCode.comp (Primrec.const _)
      (primrec_consCode.comp (Primrec.const _)
        (primrec_consCode.comp
          (primrec_applyCode.comp (Primrec.const _)
            (primrec_consCode.comp Primrec.id (Primrec.const _)))
          (Primrec.const 0))))

/-- The code of `Now` of the probe is a computable function of the index. -/
theorem computable_patternCode_now_probe :
    Computable fun index => patternCode (now (probe index)) := by
  have primrec : Primrec fun index =>
      applyCode (stringCode "Now") (consCode (probeCode (numeralCode index)) 0) :=
    primrec_applyCode.comp (Primrec.const _)
      (primrec_consCode.comp (primrec_probeCode.comp primrec_numeralCode) (Primrec.const 0))
  refine primrec.to_comp.of_eq fun index => ?_
  rw [now, patternCode_apply, patternListCode_cons, patternCode_probe]
  rfl

/-- The code of `Flag` of the probe is a computable function of the index. -/
theorem computable_patternCode_flag_probe :
    Computable fun index => patternCode (flag (probe index)) := by
  have primrec : Primrec fun index =>
      applyCode (stringCode "Flag") (consCode (probeCode (numeralCode index)) 0) :=
    primrec_applyCode.comp (Primrec.const _)
      (primrec_consCode.comp (primrec_probeCode.comp primrec_numeralCode) (Primrec.const 0))
  refine primrec.to_comp.of_eq fun index => ?_
  rw [flag, patternCode_apply, patternListCode_cons, patternCode_probe]
  rfl

/-- The same, for the members of the fibre. -/
theorem computable_code_nowProbe :
    Computable fun index => historyTheory.termCode (nowProbe index) :=
  computable_patternCode_now_probe

/-- The same, for the members of the fibre. -/
theorem computable_code_flagProbe :
    Computable fun index => historyTheory.termCode (flagProbe index) :=
  computable_patternCode_flag_probe

/-! ## No effective section -/

/-- **The history theory has no effective section.**  A section tracked by a
computable function on codes would decide the halting problem. -/
theorem historyTheory_no_effective_section
    (canonical : ComputableCanonicalSection historyTheory) : ¬ canonical.Effective :=
  fun effective => equivalence_not_computable
    (effective.computablePred computable_code_nowProbe computable_code_flagProbe)

/-- The history theory has sections, as every theory does, and none of them
is effective: effectiveness, not the existence of a section, is what fails. -/
theorem historyTheory_sections_not_effective :
    Nonempty (ComputableCanonicalSection historyTheory) ∧
      ∀ canonical : ComputableCanonicalSection historyTheory, ¬ canonical.Effective :=
  ⟨⟨ComputableCanonicalSection.ofChoice historyTheory⟩, historyTheory_no_effective_section⟩

/-- The two members of a pair can be different: for the code of a function
that diverges on `0`, `Now` and `Flag` of the probe are not equal. -/
theorem probe_separated {index : ℕ}
    (diverges : ¬ ((Denumerable.ofNat Nat.Partrec.Code index).eval 0).Dom) :
    ¬ historyTheory.toGSLT.equations.r (nowProbe index) (flagProbe index) :=
  now_not_equivalent_flag_of_diverges (probe_inImage index)
    fun halts => diverges ((probe_halts_iff index).mp halts)

/-- And they can be equal: for the code of a function that halts on `0`. -/
theorem probe_identified {index : ℕ}
    (halts : ((Denumerable.ofNat Nat.Partrec.Code index).eval 0).Dom) :
    historyTheory.toGSLT.equations.r (nowProbe index) (flagProbe index) :=
  (now_equivalent_flag_iff (probe_inImage index)).mpr ((probe_halts_iff index).mpr halts)

/-! ## Two unconditional instances -/

/-- The constant-zero program on the empty input, pending. -/
def zeroRun : Pattern := normalTerm .zero' .halt []

theorem zeroRun_inImage : InImage zeroRun := .inl ⟨.zero', .halt, [], rfl⟩

/-- The constant-zero program halts, so its two histories are equal. -/
theorem zeroRun_identified :
    historyTheory.toGSLT.equations.r (nowTerm zeroRun zeroRun_inImage)
      (flagTerm zeroRun zeroRun_inImage) :=
  (now_equivalent_flag_iff zeroRun_inImage).mpr
    ⟨[0], (adequacy .zero' [] [0]).mpr (by simp [Code.eval])⟩

/-- The silent program on the empty input, pending. -/
noncomputable def silentRun : Pattern := normalTerm silent .halt []

theorem silentRun_inImage : InImage silentRun := .inl ⟨silent, .halt, [], rfl⟩

/-- The silent program never halts, so its two histories are different
members of the quotient. -/
theorem silentRun_separated :
    ¬ historyTheory.toGSLT.equations.r (nowTerm silentRun silentRun_inImage)
      (flagTerm silentRun silentRun_inImage) :=
  now_not_equivalent_flag_of_diverges silentRun_inImage fun ⟨output, path⟩ =>
    divergence_has_no_halted_reduct (silent_eval []) output path

end Mettapedia.Languages.PartrecMachine
