import Foet.EvaluateTheoryParadigms

set_option autoImplicit false

namespace Foet

namespace KifKillingStayingStill

/-
KIF example: a choice point between “Killing” and “StayingStill”, and a theory that
explicitly marks killing as morally bad.

We encode:
  - actions as `Formula World` (as in the rest of the Lean MVP)
  - a `SituatedChoicePoint` carrying the options plus a context premise
  - value/deontic/util/virtue theories that all say “killing is bad”

Then we show:
  1) `evaluateTheoryUnder` yields `Bad(killing)` and `Permissible(stayingStill)`
  2) the deontic/util/virtue evaluators agree with value evaluation via the commutation theorems.
-/

abbrev World : Type := Bool

def φKilling : Formula World := fun w => w = true
def φStayingStill : Formula World := fun w => w = false

def cp : ChoicePoint World :=
  Set.insert φKilling (Set.singleton φStayingStill)

def ctx : Formula World := fun _ => True

def scp : SituatedChoicePoint World :=
  { options := cp, context := ctx }

noncomputable def semU : UtilityAssignmentSemantics World :=
  ⟨fun _ φ => by
    classical
    -- A tiny “oracle” utility: distinguish formulas by their truth-table on the two sample worlds.
    exact if φ true then (-1) else if φ false then 0 else 0⟩

noncomputable def semV : ValueSemantics World :=
  valueSemanticsOfUtility World semU

noncomputable def semD : DeonticSemantics World :=
  ⟨fun a φ w => semV.morally (deonticToMoralValue a) φ w⟩

noncomputable def semT : VirtueTargetSemantics World :=
  ⟨fun a φ w => semV.morally (virtueAspectToMoralValue a) φ w⟩

theorem alignDeontic : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w := by
  intro a φ w
  rfl

theorem alignVirtue : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w := by
  intro a φ w
  rfl

def Tval : ValueJudgmentTheory World :=
  Set.singleton (morallyBad φKilling)

def Tdeontic : DeontologicalImperativeTheory World :=
  Set.singleton ({ tag := .Prohibition, formula := φKilling } : DeonticSentence World)

def Tutil : UtilityAssignmentTheory World :=
  Set.singleton ({ tag := (-1), formula := φKilling } : UtilityAssignmentSentence World)

def Tvirt : VirtueTargetTheory World :=
  Set.singleton ({ aspect := .Vicious, formula := φKilling } : VirtueTargetSentence World)

theorem mem_cp_killing : φKilling ∈ cp := by
  exact Or.inl rfl

theorem mem_cp_stayingStill : φStayingStill ∈ cp := by
  exact Or.inr rfl

universe u v

theorem entailsUnder_of_mem {S : Type u} {M : Type v} (sem : Semantics S M) (T : Theory S) (C : M → Prop) (s : S)
    (hs : s ∈ T) : EntailsUnder sem T C s := by
  intro m hC hModels
  exact hModels s hs

private theorem model_Tval (w : World) : Models (valueJudgmentSemantics World semV) w Tval := by
  intro s hs
  cases hs
  dsimp [valueJudgmentSemantics, ValueSemantics.sat, Tval, semV, morallyBad, valueSentence, valueSemanticsOfUtility, semU,
    φKilling]
  -- reduce the `if` chain and then decide the integer comparison.
  simp

private theorem not_entailsUnder_good_killing :
    ¬ EntailsUnder (valueJudgmentSemantics World semV) Tval ctx (morallyGood φKilling) := by
  intro hEnt
  have hSat := hEnt true (by trivial) (model_Tval true)
  dsimp [valueJudgmentSemantics, ValueSemantics.sat, semV, morallyGood, valueSentence, valueSemanticsOfUtility] at hSat
  have : ¬ semU.utility true φKilling > 0 := by
    simp [semU, φKilling]
  exact this hSat

private theorem not_entailsUnder_good_stayingStill :
    ¬ EntailsUnder (valueJudgmentSemantics World semV) Tval ctx (morallyGood φStayingStill) := by
  intro hEnt
  have hSat := hEnt true (by trivial) (model_Tval true)
  dsimp [valueJudgmentSemantics, ValueSemantics.sat, semV, morallyGood, valueSentence, valueSemanticsOfUtility] at hSat
  have : ¬ semU.utility true φStayingStill > 0 := by
    simp [semU, φStayingStill]
  exact this hSat

private theorem not_entailsUnder_bad_stayingStill :
    ¬ EntailsUnder (valueJudgmentSemantics World semV) Tval ctx (morallyBad φStayingStill) := by
  intro hEnt
  have hSat := hEnt true (by trivial) (model_Tval true)
  dsimp [valueJudgmentSemantics, ValueSemantics.sat, semV, morallyBad, valueSentence, valueSemanticsOfUtility] at hSat
  have : ¬ semU.utility true φStayingStill < 0 := by
    simp [semU, φStayingStill]
  exact this hSat

private theorem entailsUnder_bad_killing :
    EntailsUnder (valueJudgmentSemantics World semV) Tval ctx (morallyBad φKilling) :=
  entailsUnder_of_mem (sem := valueJudgmentSemantics World semV) (T := Tval) (C := ctx) (s := morallyBad φKilling) rfl

noncomputable def evalValue : ValueJudgmentTheory World :=
  evaluateSituated (World := World) semV Tval scp

theorem evalValue_contains_bad_killing :
    morallyBad φKilling ∈ evalValue := by
  dsimp [evalValue, evaluateSituated, scp, ctx]
  exact morallyBad_mem_evaluateTheoryUnder (World := World) (semV := semV) (T := Tval) (ctx := ctx) (cp := cp)
    mem_cp_killing not_entailsUnder_good_killing entailsUnder_bad_killing

theorem evalValue_contains_perm_stayingStill :
    morallyPermissible φStayingStill ∈ evalValue := by
  dsimp [evalValue, evaluateSituated, scp, ctx]
  exact morallyPermissible_mem_evaluateTheoryUnder (World := World) (semV := semV) (T := Tval) (ctx := ctx) (cp := cp)
    mem_cp_stayingStill not_entailsUnder_good_stayingStill not_entailsUnder_bad_stayingStill

theorem evalDeontic_eq_evalValue :
    evaluateDeonticTheoryUnder (World := World) semD Tdeontic ctx cp = evalValue := by
  have h1 :=
    evaluateDeonticTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semD := semD) (semV := semV) alignDeontic Tdeontic ctx cp
  have hT : Tdeontic.toValueJudgmentTheory = Tval := by
    -- map(singleton) = singleton(map)
    simpa [Tdeontic, Tval, DeontologicalImperativeTheory.toValueJudgmentTheory, morallyBad, valueSentence,
      DeonticSentence.toValue, deonticToMoralValue] using
      (Theory.map_singleton (f := DeonticSentence.toValue) ({ tag := .Prohibition, formula := φKilling } : DeonticSentence World))
  -- rewrite both sides through the commutation theorem.
  simpa [evalValue, evaluateSituated, scp, evaluateTheoryUnder, hT] using h1

theorem evalUtil_eq_evalValue :
    evaluateUtilitarianTheoryUnder (World := World) semU Tutil ctx cp = evalValue := by
  have h1 :=
    evaluateUtilitarianTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semU := semU) Tutil ctx cp
  have hT : Tutil.toValueJudgmentTheory = Tval := by
    -- map(singleton) = singleton(map)
    simpa [Tutil, Tval, UtilityAssignmentTheory.toValueJudgmentTheory, morallyBad, valueSentence, UtilityAssignmentSentence.toValue,
      utilityToMoralValue] using
      (Theory.map_singleton (f := UtilityAssignmentSentence.toValue) ({ tag := (-1), formula := φKilling } : UtilityAssignmentSentence World))
  simpa [evalValue, evaluateSituated, scp, evaluateTheoryUnder, semV, hT] using h1

theorem evalVirtue_eq_evalValue :
    evaluateVirtueTargetTheoryUnder (World := World) semT Tvirt ctx cp = evalValue := by
  have h1 :=
    evaluateVirtueTargetTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semT := semT) (semV := semV) alignVirtue Tvirt ctx cp
  have hT : Tvirt.toValueJudgmentTheory = Tval := by
    simpa [Tvirt, Tval, VirtueTargetTheory.toValueJudgmentTheory, morallyBad, valueSentence, VirtueTargetSentence.toValue,
      virtueAspectToMoralValue] using
      (Theory.map_singleton (f := VirtueTargetSentence.toValue) ({ aspect := .Vicious, formula := φKilling } : VirtueTargetSentence World))
  simpa [evalValue, evaluateSituated, scp, evaluateTheoryUnder, hT] using h1

theorem evalDeontic_contains_bad_killing :
    morallyBad φKilling ∈ evaluateDeonticTheoryUnder (World := World) semD Tdeontic ctx cp := by
  rw [evalDeontic_eq_evalValue]
  exact evalValue_contains_bad_killing

theorem evalDeontic_contains_perm_stayingStill :
    morallyPermissible φStayingStill ∈ evaluateDeonticTheoryUnder (World := World) semD Tdeontic ctx cp := by
  rw [evalDeontic_eq_evalValue]
  exact evalValue_contains_perm_stayingStill

theorem evalUtil_contains_bad_killing :
    morallyBad φKilling ∈ evaluateUtilitarianTheoryUnder (World := World) semU Tutil ctx cp := by
  rw [evalUtil_eq_evalValue]
  exact evalValue_contains_bad_killing

theorem evalUtil_contains_perm_stayingStill :
    morallyPermissible φStayingStill ∈ evaluateUtilitarianTheoryUnder (World := World) semU Tutil ctx cp := by
  rw [evalUtil_eq_evalValue]
  exact evalValue_contains_perm_stayingStill

theorem evalVirtue_contains_bad_killing :
    morallyBad φKilling ∈ evaluateVirtueTargetTheoryUnder (World := World) semT Tvirt ctx cp := by
  rw [evalVirtue_eq_evalValue]
  exact evalValue_contains_bad_killing

theorem evalVirtue_contains_perm_stayingStill :
    morallyPermissible φStayingStill ∈ evaluateVirtueTargetTheoryUnder (World := World) semT Tvirt ctx cp := by
  rw [evalVirtue_eq_evalValue]
  exact evalValue_contains_perm_stayingStill

end KifKillingStayingStill

end Foet
