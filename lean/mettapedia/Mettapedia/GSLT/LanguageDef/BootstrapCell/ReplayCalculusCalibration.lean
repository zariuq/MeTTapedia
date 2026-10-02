import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCalculus
import Mettapedia.Languages.MeTTa.PrimeCandidates.MinimalCheckingPackage

/-!
# Calibration of the reflexive cell

The replay calculi of two existing calibration packages, presented as
validated calculi with companion caches, and checked by the generic checker.

* **Modus ponens, level one.**  The replay calculus of the modus ponens
  package validates, its cache agrees with the arity projection, and the
  package's derivation of `P(B)` is accepted through the cell.  The same
  acceptance is also recomputed directly by the kernel.
* **Modus ponens, level two.**  The replay calculus of the level-one cell
  validates in turn; the tower of two checks agrees with the base check.
* **The dependently typed package.**  Its replay calculus carries the
  explicit-substitution side condition through unchanged: the β instance is
  accepted and a wrong β result is rejected through the cell.

**Negative controls.**
* An unfaithful variant, whose replay conclusions accept any goal, still
  validates; it derives acceptance of a goal the package rejects, so its
  derivations do not coincide with the checking derivations.  Validation alone
  does not establish faithfulness; the correspondence theorem does.
* A mis-cached package, with a wrong certificate arity or a missing rule atom,
  fails validation and disagrees with the projection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell.Calibration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection
open Mettapedia.GSLT.LanguageDef.BootstrapCell
open Mettapedia.Languages.MeTTa.PrimeCandidates.MinimalCheckingPackage

/-- The level-one replay calculus. -/
def levelOne : CellProfile := { accepts := "Accepts", certificate := "Certificate" }

/-- The level-two replay calculus: a different judgment head, the same
certificate constructor. -/
def levelTwo : CellProfile := { accepts := "Accepts2", certificate := "Certificate" }

def cacheProfile (name : String) : CacheProfile :=
  { dataSort := "ReplayData", cacheName := name }

/-! ## Modus ponens, level one -/

/-- Companion cache of the replay calculus of the modus ponens package. -/
def modusPonensCell : CalculusLanguageDef :=
  cacheDefinition (cacheProfile "ModusPonensReplay")
    [("P", 1), ("A", 0), ("Certificate", 3), ("a", 0), ("I", 2), ("B", 0), ("i", 0), ("m", 0)]
    [{ head := "Accepts", arity := 2 }] (replayRules levelOne mpRules)

theorem modusPonensCell_agrees :
    CacheAgrees (cacheProfile "ModusPonensReplay") (replayRules levelOne mpRules)
      modusPonensCell := by
  with_unfolding_all rfl

theorem modusPonensCell_valid : modusPonensCell.isValid = true := by
  decide +kernel

def modusPonensCellValidated : ValidatedCalculusLanguageDef :=
  ⟨modusPonensCell, modusPonensCell_valid⟩

theorem modusPonensCell_rules :
    modusPonensCellValidated.1.rules = replayRules levelOne mpValidated.1.rules := rfl

/-- **Positive control.**  The package's derivation of `P(B)` from `A` and
`A → B` is accepted through the reflexive cell. -/
theorem modusPonensCell_accepts :
    checkRaw modusPonensCellValidated
        (acceptsJudgment levelOne mpBGoal (quoteProof levelOne mpCache mpProofB))
        (replayProof levelOne mpCache mpProofB) = true := by
  exact (checkRaw_replayProof levelOne mpValidated modusPonensCellValidated
    modusPonensCell_rules mpBGoal mpProofB).trans mp_proof_b_accepted

/-- The same acceptance, recomputed by the kernel from the presentation alone. -/
theorem modusPonensCell_accepts_by_evaluation :
    checkRaw modusPonensCellValidated
        (acceptsJudgment levelOne mpBGoal (quoteProof levelOne mpCache mpProofB))
        (replayProof levelOne mpCache mpProofB) = true := by
  decide +kernel

/-- A goal the package does not prove from this certificate. -/
def mpWrongGoal : Pattern := .apply "P" [.apply "A" []]

theorem mpWrongGoal_rejected : checkRaw mpValidated mpWrongGoal mpProofB = false := by
  decide +kernel

/-- Rejection is carried through the cell. -/
theorem modusPonensCell_rejects_wrong_goal :
    checkRaw modusPonensCellValidated
        (acceptsJudgment levelOne mpWrongGoal (quoteProof levelOne mpCache mpProofB))
        (replayProof levelOne mpCache mpProofB) = false := by
  exact (checkRaw_replayProof levelOne mpValidated modusPonensCellValidated
    modusPonensCell_rules mpWrongGoal mpProofB).trans mpWrongGoal_rejected

/-- The cell's derivations coincide with the package's checking derivations. -/
theorem modusPonensCell_derivable_iff (goal code : Pattern) :
    Nonempty (Derivation modusPonensCellValidated (acceptsJudgment levelOne goal code)) ↔
      ∃ certificate : RawProof,
        code = quoteProof levelOne mpCache certificate ∧
          checkRaw mpValidated goal certificate = true :=
  accepts_derivable_iff levelOne mpValidated modusPonensCellValidated modusPonensCell_rules
    goal code

/-! ## Modus ponens, level two -/

/-- Companion cache of the replay calculus of the level-one cell. -/
def modusPonensCellTwo : CalculusLanguageDef :=
  cacheDefinition (cacheProfile "ModusPonensReplayReplay")
    [("Accepts", 2), ("P", 1), ("A", 0), ("Certificate", 3), ("a", 0), ("I", 2), ("B", 0),
      ("i", 0), ("m", 0)]
    [{ head := "Accepts2", arity := 2 }] (replayRules levelTwo modusPonensCell.rules)

theorem modusPonensCellTwo_agrees :
    CacheAgrees (cacheProfile "ModusPonensReplayReplay")
      (replayRules levelTwo modusPonensCell.rules) modusPonensCellTwo := by
  with_unfolding_all rfl

theorem modusPonensCellTwo_valid : modusPonensCellTwo.isValid = true := by
  decide +kernel

def modusPonensCellTwoValidated : ValidatedCalculusLanguageDef :=
  ⟨modusPonensCellTwo, modusPonensCellTwo_valid⟩

theorem modusPonensCellTwo_rules :
    modusPonensCellTwoValidated.1.rules =
      replayRules levelTwo modusPonensCellValidated.1.rules := rfl

/-- **The tower.**  Level two checks level one's check of level zero, and the
three verdicts agree for every goal and certificate. -/
theorem modusPonens_tower (goal : Pattern) (certificate : RawProof) :
    checkRaw modusPonensCellTwoValidated
        (acceptsJudgment levelTwo
          (acceptsJudgment levelOne goal (quoteProof levelOne mpCache certificate))
          (quoteProof levelTwo modusPonensCell (replayProof levelOne mpCache certificate)))
        (replayProof levelTwo modusPonensCell (replayProof levelOne mpCache certificate)) =
      checkRaw mpValidated goal certificate := by
  exact (checkRaw_replayProof levelTwo modusPonensCellValidated modusPonensCellTwoValidated
      modusPonensCellTwo_rules _ (replayProof levelOne mpCache certificate)).trans
    (checkRaw_replayProof levelOne mpValidated modusPonensCellValidated modusPonensCell_rules
      goal certificate)

theorem modusPonensCellTwo_accepts :
    checkRaw modusPonensCellTwoValidated
        (acceptsJudgment levelTwo
          (acceptsJudgment levelOne mpBGoal (quoteProof levelOne mpCache mpProofB))
          (quoteProof levelTwo modusPonensCell (replayProof levelOne mpCache mpProofB)))
        (replayProof levelTwo modusPonensCell (replayProof levelOne mpCache mpProofB)) =
      true := by
  exact (modusPonens_tower mpBGoal mpProofB).trans mp_proof_b_accepted

/-! ## The dependently typed package: side conditions through the cell -/

/-- Companion cache of the replay calculus of the dependently typed package. -/
def dependentCell : CalculusLanguageDef :=
  cacheDefinition (cacheProfile "DependentReplay")
    [("T", 3), ("C", 0), ("Z", 0), ("N", 0), ("Certificate", 3), ("z", 0), ("i", 0), ("F", 2),
      ("j", 0), ("@", 2), ("k", 0), ("E", 3), ("b", 0)]
    [{ head := "Accepts", arity := 2 }] (replayRules levelOne dttRules)

theorem dependentCell_agrees :
    CacheAgrees (cacheProfile "DependentReplay") (replayRules levelOne dttRules)
      dependentCell := by
  with_unfolding_all rfl

theorem dependentCell_valid : dependentCell.isValid = true := by
  decide +kernel

def dependentCellValidated : ValidatedCalculusLanguageDef :=
  ⟨dependentCell, dependentCell_valid⟩

theorem dependentCell_rules :
    dependentCellValidated.1.rules = replayRules levelOne dttValidated.1.rules := rfl

/-- The β instance, whose rule carries an explicit-substitution side
condition, is accepted through the cell. -/
theorem dependentCell_accepts_beta :
    checkRaw dependentCellValidated
        (acceptsJudgment levelOne dttBetaZeroGoal (quoteProof levelOne dttCache dttProofBetaZero))
        (replayProof levelOne dttCache dttProofBetaZero) = true := by
  exact (checkRaw_replayProof levelOne dttValidated dependentCellValidated dependentCell_rules
    dttBetaZeroGoal dttProofBetaZero).trans dtt_beta_zero_accepted

theorem dependentCell_accepts_application :
    checkRaw dependentCellValidated
        (acceptsJudgment levelOne dttIdZeroGoal (quoteProof levelOne dttCache dttProofIdZero))
        (replayProof levelOne dttCache dttProofIdZero) = true := by
  exact (checkRaw_replayProof levelOne dttValidated dependentCellValidated dependentCell_rules
    dttIdZeroGoal dttProofIdZero).trans dtt_id_zero_accepted

/-- A β instance with a wrong result: `(λ. #0) Z` claimed to reduce to `N`. -/
def wrongBetaGoal : Pattern := .apply "E" [.lambda none (.bvar 0), .apply "Z" [], .apply "N" []]

def wrongBetaProof : RawProof :=
  .node { ruleId := ⟨"b"⟩, arguments := [.bvar 0, .apply "Z" [], .apply "N" []] } []

theorem wrongBeta_rejected : checkRaw dttValidated wrongBetaGoal wrongBetaProof = false := by
  decide +kernel

/-- The side condition still rejects the wrong result through the cell. -/
theorem dependentCell_rejects_wrong_beta :
    checkRaw dependentCellValidated
        (acceptsJudgment levelOne wrongBetaGoal (quoteProof levelOne dttCache wrongBetaProof))
        (replayProof levelOne dttCache wrongBetaProof) = false := by
  exact (checkRaw_replayProof levelOne dttValidated dependentCellValidated dependentCell_rules
    wrongBetaGoal wrongBetaProof).trans wrongBeta_rejected

/-! ## Negative control: an unfaithful variant validates but accepts a wrong goal -/

/-- A replay rule whose conclusion accepts an arbitrary goal: the comparison
of the computed conclusion with the requested goal is dropped. -/
def looseReplayRule (profile : CellProfile) (rule : RuleSchema) : RuleSchema :=
  { replayRule profile rule with
    metavariables := (replayRule profile rule).metavariables ++ [("#goal", 0)]
    conclusion :=
      acceptsJudgment profile (.fvar "#goal")
        (certificateCode profile rule.id (boundVariables rule.metavariables)
          (boundVariables (childFormalsFrom rule.metavariables.length rule.premises))) }

def looseCell : CalculusLanguageDef :=
  cacheDefinition (cacheProfile "LooseModusPonensReplay")
    [("Certificate", 3), ("a", 0), ("i", 0), ("P", 1), ("I", 2), ("m", 0)]
    [{ head := "Accepts", arity := 2 }] (mpRules.map (looseReplayRule levelOne))

theorem looseCell_agrees :
    CacheAgrees (cacheProfile "LooseModusPonensReplay")
      (mpRules.map (looseReplayRule levelOne)) looseCell := by
  with_unfolding_all rfl

/-- The unfaithful variant passes validation. -/
theorem looseCell_valid : looseCell.isValid = true := by
  decide +kernel

def looseCellValidated : ValidatedCalculusLanguageDef := ⟨looseCell, looseCell_valid⟩

/-- A loose replay certificate for the wrong goal `P(A)`. -/
def looseCertificate : RawProof :=
  .node
    { ruleId := ⟨"m"⟩
      arguments :=
        [.apply "A" [], .apply "B" [],
          quoteProof levelOne mpCache (.node { ruleId := ⟨"a"⟩, arguments := [] } []),
          quoteProof levelOne mpCache (.node { ruleId := ⟨"i"⟩, arguments := [] } []),
          mpWrongGoal] }
    [.node { ruleId := ⟨"a"⟩, arguments := [.apply "P" [.apply "A" []]] } [],
      .node { ruleId := ⟨"i"⟩, arguments := [.apply "P" [.apply "I" [.apply "A" [], .apply "B" []]]] } []]

/-- The loose cell accepts the modus ponens certificate for `P(A)`. -/
theorem looseCell_accepts_wrong_goal :
    checkRaw looseCellValidated
        (acceptsJudgment levelOne mpWrongGoal (quoteProof levelOne mpCache mpProofB))
        looseCertificate = true := by
  decide +kernel

/-- **Negative control.**  The loose cell's derivations do not coincide with
the checking derivations of the package, although it validates. -/
theorem looseCell_not_faithful :
    ¬ ∀ goal code : Pattern,
        Nonempty (Derivation looseCellValidated (acceptsJudgment levelOne goal code)) ↔
          ∃ certificate : RawProof,
            code = quoteProof levelOne mpCache certificate ∧
              checkRaw mpValidated goal certificate = true := by
  intro faithful
  have derivable :
      Nonempty (Derivation looseCellValidated
        (acceptsJudgment levelOne mpWrongGoal (quoteProof levelOne mpCache mpProofB))) :=
    checkRaw_soundness looseCell_accepts_wrong_goal
  obtain ⟨certificate, codeEq, accepted⟩ := (faithful _ _).mp derivable
  have sameCertificate := quoteProof_injective levelOne mpCache _ _ codeEq
  rw [← sameCertificate, mpWrongGoal_rejected] at accepted
  exact Bool.false_ne_true accepted

/-! ## Negative control: mis-cached packages fail validation -/

/-- The certificate constructor declared with the wrong arity. -/
def wrongArityCache : CalculusLanguageDef :=
  cacheDefinition (cacheProfile "ModusPonensReplay")
    [("P", 1), ("A", 0), ("Certificate", 2), ("a", 0), ("I", 2), ("B", 0), ("i", 0), ("m", 0)]
    [{ head := "Accepts", arity := 2 }] (replayRules levelOne mpRules)

theorem wrongArityCache_invalid : wrongArityCache.isValid = false := by
  decide +kernel

theorem wrongArityCache_disagrees :
    ¬ CacheAgrees (cacheProfile "ModusPonensReplay") (replayRules levelOne mpRules)
      wrongArityCache := by
  intro agrees
  have same : wrongArityCache = modusPonensCell :=
    Except.ok.inj (agrees.symm.trans modusPonensCell_agrees)
  have arities :
      wrongArityCache.toLanguageDef.terms.map (fun term => term.params.length) ≠
        modusPonensCell.toLanguageDef.terms.map (fun term => term.params.length) := by
    decide +kernel
  exact arities (congrArg (fun definition : CalculusLanguageDef =>
    definition.toLanguageDef.terms.map (fun term => term.params.length)) same)

/-- The atom of the modus ponens rule omitted from the cache. -/
def missingAtomCache : CalculusLanguageDef :=
  cacheDefinition (cacheProfile "ModusPonensReplay")
    [("P", 1), ("A", 0), ("Certificate", 3), ("a", 0), ("I", 2), ("B", 0), ("i", 0)]
    [{ head := "Accepts", arity := 2 }] (replayRules levelOne mpRules)

theorem missingAtomCache_invalid : missingAtomCache.isValid = false := by
  decide +kernel

theorem missingAtomCache_disagrees :
    ¬ CacheAgrees (cacheProfile "ModusPonensReplay") (replayRules levelOne mpRules)
      missingAtomCache := by
  intro agrees
  have same : missingAtomCache = modusPonensCell :=
    Except.ok.inj (agrees.symm.trans modusPonensCell_agrees)
  have counts :
      missingAtomCache.toLanguageDef.terms.length ≠ modusPonensCell.toLanguageDef.terms.length := by
    decide +kernel
  exact counts (congrArg (fun definition : CalculusLanguageDef =>
    definition.toLanguageDef.terms.length) same)

end Mettapedia.GSLT.LanguageDef.BootstrapCell.Calibration
