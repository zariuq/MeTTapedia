import Mettapedia.Languages.VibeITP.Presentation.CompleteDefinitions
import Mettapedia.Languages.VibeITP.Presentation.CompleteShift
import Mettapedia.Languages.VibeITP.Presentation.CompleteSubstitution
import Mettapedia.Languages.VibeITP.Presentation.CompleteInstantiation
import Mettapedia.Languages.VibeITP.Presentation.CompleteLiterals

/-!
# Controls for the actual hosted Vibe-ITP kernel package

The fixture declares two nullary free variables, one unary free variable and
a constant binding one variable. Its axioms supply the premises of modus
ponens and a schematic statement under the binder. The constant also has an
admissible definition, with its actual free-variable occurrence hint.

Concrete articles check the primitive inference and its malformed variants.
Operation witnesses give accepted articles through the actual `Presents`
theorem; refusal controls exclude all derivations of the operation judgment.
These statements concern the operation judgments, independently of any
unrelated theorem admitted as an axiom.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.VibeITP.Presentation.KernelControls

open Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.VibeITP.Spec

def freshInfo (n : Nat) : Option SymInfo :=
  if n = 0 then some (.fvarOf 0)
  else if n = 1 then some (.fvarOf 0)
  else if n = 2 then some (.fvarOf 1)
  else if n = 3 then some { kind := .constant, binders := [1] }
  else none

def controlSig : Sig := sigOf freshInfo
def atomA : Term := .app (.fresh 0) []
def atomB : Term := .app (.fresh 1) []
def parameter : SymId := .fresh 2
def binder : SymId := .fresh 3
def underBinder (t : Term) : Term := .app binder [t]
def definitionBody : Term := .app parameter [.lit []]
def controlDefinition : Definition := ⟨binder, [parameter], definitionBody⟩
def schematicStatement : Term := underBinder (.app parameter [.bvar 0])

def controlTheory : Theory :=
  ⟨controlSig, [.impl atomA atomB, atomA, schematicStatement], [controlDefinition]⟩

theorem controlTheory_hosted : Hosted controlTheory 4 := by
  constructor
  · intro b; rfl
  · intro n
    by_cases h0 : n = 0
    · subst n; decide +kernel
    by_cases h1 : n = 1
    · subst n; decide +kernel
    by_cases h2 : n = 2
    · subst n; decide +kernel
    by_cases h3 : n = 3
    · subst n; decide +kernel
    simp [controlTheory, controlSig, sigOf, freshInfo, h0, h1, h2, h3]
    omega
  · intro s info hs hk b hb
    cases s with
    | builtin sym =>
        have hi : info = sym.info := by simpa [controlTheory, controlSig, sigOf] using hs.symm
        subst info
        simp [Builtin.info] at hk
    | fresh n =>
        by_cases h0 : n = 0
        · subst n
          simp [controlTheory, controlSig, sigOf, freshInfo, SymInfo.fvarOf] at hs
          subst info
          simp at hb
        by_cases h1 : n = 1
        · subst n
          simp [controlTheory, controlSig, sigOf, freshInfo, SymInfo.fvarOf] at hs
          subst info
          simp at hb
        by_cases h2 : n = 2
        · subst n
          simp [controlTheory, controlSig, sigOf, freshInfo, SymInfo.fvarOf] at hs
          subst info
          simpa using hb
        by_cases h3 : n = 3
        · subst n
          simp [controlTheory, controlSig, sigOf, freshInfo] at hs
          subst info
          contradiction
        simp [controlTheory, controlSig, sigOf, freshInfo, h0, h1, h2, h3] at hs
  · intro φ hφ
    simp only [controlTheory, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl <;> decide +kernel
  · intro d hd
    have heq : d = controlDefinition := by simpa [controlTheory] using hd
    subst d
    exact ⟨by decide +kernel, by decide +kernel, [0], by decide +kernel⟩

def controlRules : List FORule := kernelRules ++ theoryRules controlTheory 4

private theorem fixed_in : kernelRules ⊆ controlRules := List.subset_append_left _ _
private theorem admitted_in : theoryRules controlTheory 4 ⊆ controlRules :=
  List.subset_append_right _ _

private theorem accepted_of_derivation {goal : Pattern} (d : FODerivable controlRules goal) :
    ∃ article, checkRaw (kernelValidated controlTheory 4) goal article = true :=
  (checkRaw_exists_iff_foDerivable (kernelValidated_presents controlTheory 4) goal).mpr d

private theorem rejects_of_nonderivability {goal : Pattern} (h : ¬ FODerivable controlRules goal)
    (article : RawProof) : checkRaw (kernelValidated controlTheory 4) goal article = false := by
  cases hc : checkRaw (kernelValidated controlTheory 4) goal article with
  | false => rfl
  | true =>
      exact False.elim (h ((checkRaw_exists_iff_foDerivable
        (kernelValidated_presents controlTheory 4) goal).mp ⟨article, hc⟩))

def axiomLeaf (k : Nat) : RawProof := .node ⟨⟨axiomRuleId k⟩, []⟩ []

def mpArguments : List Pattern :=
  [encTerm controlTheory.sig atomA, encTerm controlTheory.sig atomB, cAnn cN0 cTrue]

def mpArticle : RawProof :=
  .node ⟨⟨rMp.id⟩, mpArguments⟩ [axiomLeaf 1, axiomLeaf 2]

theorem modus_ponens_accepts :
    checkRaw (kernelValidated controlTheory 4) (jThm (encTerm controlTheory.sig atomB))
      mpArticle = true := by decide +kernel

def variationTheory : Theory :=
  { controlTheory with axioms := controlTheory.axioms ++ [atomA] }

theorem variationTheory_hosted : Hosted variationTheory 4 := by
  refine ⟨controlTheory_hosted.builtin, controlTheory_hosted.fresh,
    controlTheory_hosted.fvarBinders, ?_, controlTheory_hosted.definitionsOk⟩
  intro φ hφ
  simp only [variationTheory, List.mem_append, List.mem_singleton] at hφ
  rcases hφ with hφ | rfl
  · exact controlTheory_hosted.axiomsWf φ hφ
  · decide +kernel

theorem harmless_duplicate_premise_accepts :
    checkRaw (kernelValidated variationTheory 4) (jThm (encTerm controlTheory.sig atomB))
      (.node ⟨⟨rMp.id⟩, mpArguments⟩ [axiomLeaf 1, axiomLeaf 4]) = true := by decide +kernel

theorem modus_ponens_wrong_goal_rejects :
    checkRaw (kernelValidated controlTheory 4) (jThm (encTerm controlTheory.sig atomA))
      mpArticle = false := by decide +kernel

theorem modus_ponens_wrong_premise_rejects :
    checkRaw (kernelValidated controlTheory 4) (jThm (encTerm controlTheory.sig atomB))
      (.node ⟨⟨rMp.id⟩, mpArguments⟩ [axiomLeaf 1, axiomLeaf 1]) = false := by decide +kernel

theorem modus_ponens_reversed_premises_rejects :
    checkRaw (kernelValidated controlTheory 4) (jThm (encTerm controlTheory.sig atomB))
      (.node ⟨⟨rMp.id⟩, mpArguments⟩ [axiomLeaf 2, axiomLeaf 1]) = false := by decide +kernel

theorem modus_ponens_wrong_argument_count_rejects :
    checkRaw (kernelValidated controlTheory 4) (jThm (encTerm controlTheory.sig atomB))
      (.node ⟨⟨rMp.id⟩, mpArguments ++ [cN0]⟩ [axiomLeaf 1, axiomLeaf 2]) = false := by
  decide +kernel

theorem application_arity_no_formation :
    ¬ FODerivable controlRules (jWf (encTerm controlTheory.sig (.app parameter []))) := by
  intro d
  have hm : WfM controlTheory.sig (encTerm controlTheory.sig (.app parameter [])) :=
    meaning_of_foDerivable controlTheory_hosted d
  obtain ⟨t, ht, hwf⟩ := hm
  have heq : .app parameter [] = t := encTerm_inj controlTheory.sig ht
  subst t
  have hrefuse : WellFormed controlTheory.sig (.app parameter []) = false := by decide +kernel
  rw [hrefuse] at hwf
  contradiction

theorem application_arity_rejects (article : RawProof) :
    checkRaw (kernelValidated controlTheory 4)
      (jWf (encTerm controlTheory.sig (.app parameter []))) article = false :=
  rejects_of_nonderivability application_arity_no_formation article

/-! ## Shifting, binder offsets and pruning -/

theorem shift_under_binder_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jShift (encNat 1) (encNat 0) (encTerm controlTheory.sig (underBinder (.bvar 1)))
        (encTerm controlTheory.sig (underBinder (.bvar 2)))) article = true := by
  apply accepted_of_derivation
  exact complete_shift fixed_in controlTheory.sig 1 0
    (underBinder (.bvar 1)) (underBinder (.bvar 2)) (by decide +kernel) (by decide +kernel)

theorem shift_wrong_binder_result_no_derivation :
    ¬ FODerivable controlRules
      (jShift (encNat 1) (encNat 0) (encTerm controlTheory.sig (underBinder (.bvar 1)))
        (encTerm controlTheory.sig (underBinder (.bvar 1)))) := by
  intro d
  have hs := shift_of_foDerivable controlTheory_hosted 1 0
    (underBinder (.bvar 1)) (underBinder (.bvar 1)) d
  have hactual : shift controlTheory.sig 1 0 (underBinder (.bvar 1)) =
      some (underBinder (.bvar 2)) := by decide +kernel
  rw [hactual] at hs
  have hne : underBinder (.bvar 2) ≠ underBinder (.bvar 1) := by decide +kernel
  exact hne (Option.some.inj hs)

theorem shift_prunes_closed_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jShift (encNat 1) (encNat (wordBound - 1))
        (encTerm controlTheory.sig (underBinder (.bvar 0)))
        (encTerm controlTheory.sig (underBinder (.bvar 0)))) article = true := by
  apply accepted_of_derivation
  exact complete_shift fixed_in controlTheory.sig 1 (wordBound - 1)
    (underBinder (.bvar 0)) (underBinder (.bvar 0)) (by decide +kernel) (by decide +kernel)

theorem shift_word_overflow_no_derivation (result : Term) :
    ¬ FODerivable controlRules
      (jShift (encNat 1) (encNat 0) (encTerm controlTheory.sig (.bvar (wordBound - 2)))
        (encTerm controlTheory.sig result)) :=
  shift_refusal controlTheory_hosted 1 0 (.bvar (wordBound - 2)) (by decide +kernel) result

theorem shift_binder_offset_overflow_no_derivation (result : List Term) :
    ¬ FODerivable controlRules
      (jShiftArgs (encNat 1) (encNat (wordBound - 1)) (encNatList [1])
        (encTermList controlTheory.sig [.bvar 0]) (encTermList controlTheory.sig result)) :=
  (shiftList_refusal_iff controlTheory_hosted 1 (wordBound - 1) [1] [.bvar 0]
    rfl (.cons (.bvar 0) .nil)).mp (by decide +kernel) result

/-! ## Substitution order and capture avoidance -/

def substitutionArguments : List Term := [.lit [7], .lit [8]]

theorem substitution_last_argument_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jSubstTop (encNat 2) (encTermList controlTheory.sig substitutionArguments)
        (encTerm controlTheory.sig (.bvar 0)) (encTerm controlTheory.sig (.lit [8]))) article =
      true := by
  apply accepted_of_derivation
  exact complete_substTop fixed_in controlTheory.sig 2 substitutionArguments
    (.bvar 0) (.lit [8]) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem substitution_first_argument_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jSubstTop (encNat 2) (encTermList controlTheory.sig substitutionArguments)
        (encTerm controlTheory.sig (.bvar 1)) (encTerm controlTheory.sig (.lit [7]))) article =
      true := by
  apply accepted_of_derivation
  exact complete_substTop fixed_in controlTheory.sig 2 substitutionArguments
    (.bvar 1) (.lit [7]) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem substitution_forward_order_no_derivation :
    ¬ FODerivable controlRules
      (jSubstTop (encNat 2) (encTermList controlTheory.sig substitutionArguments)
        (encTerm controlTheory.sig (.bvar 0)) (encTerm controlTheory.sig (.lit [7]))) := by
  intro d
  have hs := substTop_of_foDerivable controlTheory_hosted 2 substitutionArguments
    (.bvar 0) (.lit [7]) rfl d
  have hactual : substBVars controlTheory.sig 2 substitutionArguments (.bvar 0) 0 =
      some (.lit [8]) := by decide +kernel
  rw [hactual] at hs
  have hne : (Term.lit [8]) ≠ .lit [7] := by decide +kernel
  exact hne (Option.some.inj hs)

theorem substitution_under_binder_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jSubstTop (encNat 1) (encTermList controlTheory.sig [.bvar 0])
        (encTerm controlTheory.sig (underBinder (.bvar 1)))
        (encTerm controlTheory.sig (underBinder (.bvar 1)))) article = true := by
  apply accepted_of_derivation
  exact complete_substTop fixed_in controlTheory.sig 1 [.bvar 0]
    (underBinder (.bvar 1)) (underBinder (.bvar 1)) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem substitution_capturing_result_no_derivation :
    ¬ FODerivable controlRules
      (jSubstTop (encNat 1) (encTermList controlTheory.sig [.bvar 0])
        (encTerm controlTheory.sig (underBinder (.bvar 1)))
        (encTerm controlTheory.sig (underBinder (.bvar 0)))) := by
  intro d
  have hs := substTop_of_foDerivable controlTheory_hosted 1 [.bvar 0]
    (underBinder (.bvar 1)) (underBinder (.bvar 0)) rfl d
  have hactual : substBVars controlTheory.sig 1 [.bvar 0] (underBinder (.bvar 1)) 0 =
      some (underBinder (.bvar 1)) := by decide +kernel
  rw [hactual] at hs
  have hne : underBinder (.bvar 1) ≠ underBinder (.bvar 0) := by decide +kernel
  exact hne (Option.some.inj hs)

theorem substitution_shift_overflow_no_derivation (result : Pattern) :
    ¬ FODerivable controlRules
      (jSubst (encNat 1) (encTermList controlTheory.sig [.bvar (wordBound - 2)]) (encNat 1)
        (encTerm controlTheory.sig (.bvar 1)) result) :=
  substGo_refusal controlTheory_hosted 1 [.bvar (wordBound - 2)] 1 (.bvar 1) rfl
    (by decide +kernel) result

theorem zero_argument_substitution_prunes_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jSubstTop (encNat 0) (encTermList controlTheory.sig [])
        (encTerm controlTheory.sig (.bvar (wordBound - 1)))
        (encTerm controlTheory.sig (.bvar (wordBound - 1)))) article = true := by
  apply accepted_of_derivation
  exact complete_substTop_shape fixed_in controlTheory.sig 0 []
    (.bvar (wordBound - 1)) (.bvar (wordBound - 1)) rfl .nil (.bvar _) (by decide +kernel)

/-! ## Instantiation under binders -/

theorem parameter_isFvarOf : IsFvarOf controlTheory.sig parameter 1 := by
  unfold IsFvarOf
  decide +kernel

theorem atomA_isFvarOf : IsFvarOf controlTheory.sig (.fresh 0) 0 := by
  unfold IsFvarOf
  decide +kernel

theorem instantiation_under_binder_operation_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jInst (encSym controlTheory.sig parameter)
        (encTerm controlTheory.sig (underBinder (.bvar 1))) (encNat 1) (encNat 0)
        (encTerm controlTheory.sig schematicStatement)
        (encTerm controlTheory.sig (underBinder (underBinder (.bvar 1))))) article = true := by
  apply accepted_of_derivation
  exact complete_inst fixed_in controlTheory.sig parameter 1 (underBinder (.bvar 1)) 0
    schematicStatement (underBinder (underBinder (.bvar 1)))
    parameter_isFvarOf (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem instantiation_under_binder_theorem_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig (underBinder (underBinder (.bvar 1))))) article = true := by
  apply accepted_of_derivation
  have haxiom : FODerivable controlRules (jThm (encTerm controlTheory.sig schematicStatement)) :=
    intro_axiomRule controlTheory.sig 3 schematicStatement
      (admitted_in (by simp [theoryRules, controlTheory, axiomRules]))
  exact complete_instantiateStatement fixed_in admitted_in controlTheory_hosted
    parameter (underBinder (.bvar 1)) schematicStatement (underBinder (underBinder (.bvar 1)))
    (by decide +kernel)
    (wellFormed_termShape _ _ (by decide +kernel)) (by decide +kernel) haxiom

theorem instantiation_capturing_result_no_derivation :
    ¬ FODerivable controlRules
      (jInst (encSym controlTheory.sig parameter)
        (encTerm controlTheory.sig (underBinder (.bvar 1))) (encNat 1) (encNat 0)
        (encTerm controlTheory.sig schematicStatement)
        (encTerm controlTheory.sig (underBinder (underBinder (.bvar 0))))) := by
  intro d
  have hs := instGo_of_foDerivable controlTheory_hosted parameter 1
    (underBinder (.bvar 1)) 0 schematicStatement (underBinder (underBinder (.bvar 0)))
    parameter_isFvarOf d
  have hactual : instGo controlTheory.sig parameter 1 (underBinder (.bvar 1)) 0
      schematicStatement = some (underBinder (underBinder (.bvar 1))) := by decide +kernel
  rw [hactual] at hs
  have hne : underBinder (underBinder (.bvar 1)) ≠ underBinder (underBinder (.bvar 0)) := by
    decide +kernel
  exact hne (Option.some.inj hs)

theorem instantiation_other_lower_head_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jInst (encSym controlTheory.sig parameter) (encTerm controlTheory.sig (.bvar 0))
        (encNat 1) (encNat 0) (encTerm controlTheory.sig atomA)
        (encTerm controlTheory.sig atomA)) article = true := by
  apply accepted_of_derivation
  exact complete_inst fixed_in controlTheory.sig parameter 1 (.bvar 0) 0 atomA atomA
    parameter_isFvarOf (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem instantiation_other_higher_head_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jInst (encSym controlTheory.sig (.fresh 0)) (encTerm controlTheory.sig (.lit [7]))
        (encNat 0) (encNat 0) (encTerm controlTheory.sig atomB)
        (encTerm controlTheory.sig atomB)) article = true := by
  apply accepted_of_derivation
  exact complete_inst fixed_in controlTheory.sig (.fresh 0) 0 (.lit [7]) 0 atomB atomB
    atomA_isFvarOf (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem instantiation_prunes_no_fvar_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jInst (encSym controlTheory.sig parameter) (encTerm controlTheory.sig (.lit []))
        (encNat 1) (encNat (wordBound - 1))
        (encTerm controlTheory.sig (underBinder (.bvar 0)))
        (encTerm controlTheory.sig (underBinder (.bvar 0)))) article = true := by
  apply accepted_of_derivation
  exact complete_inst fixed_in controlTheory.sig parameter 1 (.lit []) (wordBound - 1)
    (underBinder (.bvar 0)) (underBinder (.bvar 0))
    parameter_isFvarOf (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem instantiation_shift_overflow_no_derivation (result : Term) :
    ¬ FODerivable controlRules
      (jInst (encSym controlTheory.sig parameter)
        (encTerm controlTheory.sig (.bvar (wordBound - 2))) (encNat 1) (encNat 1)
        (encTerm controlTheory.sig definitionBody) (encTerm controlTheory.sig result)) :=
  (instGo_refusal_iff controlTheory_hosted parameter 1 (.bvar (wordBound - 2)) 1
    definitionBody parameter_isFvarOf (.bvar _)
    (wellFormed_termShape _ _ (by decide +kernel))).mp (by decide +kernel) result

theorem instantiation_binder_offset_overflow_no_derivation (result : Term) :
    ¬ FODerivable controlRules
      (jInst (encSym controlTheory.sig parameter) (encTerm controlTheory.sig (.lit []))
        (encNat 1) (encNat (wordBound - 1)) (encTerm controlTheory.sig schematicStatement)
        (encTerm controlTheory.sig result)) :=
  (instGo_refusal_iff controlTheory_hosted parameter 1 (.lit []) (wordBound - 1)
    schematicStatement parameter_isFvarOf (.lit [])
    (wellFormed_termShape _ _ (by decide +kernel))).mp (by decide +kernel) result

theorem instantiation_value_exceeds_arity_refused :
    instantiateStatement controlTheory.sig parameter (.bvar 1) schematicStatement = none := by
  decide +kernel

theorem instantiation_value_exceeds_arity_no_guard_derivation :
    ¬ FODerivable controlRules
      (jNLe (encNat (depth controlTheory.sig (.bvar 1)))
        (encNat (symArity controlTheory.sig parameter))) := by
  intro d
  have hm : NLeM (encNat 2) (encNat 1) := meaning_of_foDerivable controlTheory_hosted d
  obtain ⟨x, hx, hle⟩ := hm 1 (decNat_encNat 1)
  have heq : 2 = x := by simpa only [decNat_encNat, Option.some.injEq] using hx
  omega

theorem instantiation_value_exceeds_arity_guard_rejects (article : RawProof) :
    checkRaw (kernelValidated controlTheory 4)
      (jNLe (encNat (depth controlTheory.sig (.bvar 1)))
        (encNat (symArity controlTheory.sig parameter))) article = false :=
  rejects_of_nonderivability instantiation_value_exceeds_arity_no_guard_derivation article

theorem instantiation_constant_refused :
    instantiateStatement controlTheory.sig binder (.lit []) schematicStatement = none := by
  decide +kernel

/-! ## Definition occurrence hints and closedness -/

theorem definition_conditions_accept :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jDefStmt (encSym controlTheory.sig binder) (encSymList controlTheory.sig [parameter])
        (encNatList [0]) (encTerm controlTheory.sig definitionBody)
        (encTerm controlTheory.sig
          (definitionStatement controlTheory.sig binder [parameter] definitionBody))) article =
      true := by
  apply accepted_of_derivation
  exact complete_defStmt fixed_in admitted_in controlTheory_hosted
    binder [parameter] [0] definitionBody (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem surplus_valid_definition_hints_accept :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jDefStmt (encSym controlTheory.sig binder) (encSymList controlTheory.sig [parameter])
        (encNatList [0, 0]) (encTerm controlTheory.sig definitionBody)
        (encTerm controlTheory.sig
          (definitionStatement controlTheory.sig binder [parameter] definitionBody))) article =
      true := by
  apply accepted_of_derivation
  exact complete_defStmt fixed_in admitted_in controlTheory_hosted
    binder [parameter] [0, 0] definitionBody (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem missing_definition_hint_no_derivation (result : Pattern) :
    ¬ FODerivable controlRules
      (jDefStmt (encSym controlTheory.sig binder) (encSymList controlTheory.sig [parameter])
        (encNatList []) (encTerm controlTheory.sig definitionBody) result) :=
  no_defStmt_of_refused controlTheory_hosted binder [parameter] [] definitionBody
    (by decide +kernel) result

theorem out_of_range_definition_hint_no_derivation (result : Pattern) :
    ¬ FODerivable controlRules
      (jDefStmt (encSym controlTheory.sig binder) (encSymList controlTheory.sig [parameter])
        (encNatList [1]) (encTerm controlTheory.sig definitionBody) result) :=
  no_defStmt_of_refused controlTheory_hosted binder [parameter] [1] definitionBody
    (by decide +kernel) result

theorem wrong_definition_parameter_hint_no_derivation (result : Pattern) :
    ¬ FODerivable controlRules
      (jDefStmt (encSym controlTheory.sig binder)
        (encSymList controlTheory.sig [.fresh 0, parameter]) (encNatList [0])
        (encTerm controlTheory.sig definitionBody) result) :=
  no_defStmt_of_refused controlTheory_hosted binder [.fresh 0, parameter] [0] definitionBody
    (by decide +kernel) result

theorem open_definition_body_no_derivation (result : Pattern) :
    ¬ FODerivable controlRules
      (jDefStmt (encSym controlTheory.sig binder) (encSymList controlTheory.sig [parameter])
        (encNatList []) (encTerm controlTheory.sig (.bvar 0)) result) :=
  no_defStmt_of_refused controlTheory_hosted binder [parameter] [] (.bvar 0)
    (by decide +kernel) result

theorem definition_equation_leaf_accepts :
    checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig
        (definitionStatement controlTheory.sig binder [parameter] definitionBody)))
      (.node ⟨⟨definitionRuleId 1⟩, []⟩ []) = true := by decide +kernel

/-! ## Literal encodings, wraparound and bounds -/

theorem number_literal_boundary_encoding :
    natLiteral 255 = [255] ∧ natLiteral 256 = [0, 1, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem literal_is_nat_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig (litIsNatStatement 256))) article = true := by
  apply accepted_of_derivation
  exact complete_litIsNat fixed_in controlTheory controlTheory_hosted.builtin 256
    (by decide +kernel)

theorem literal_less_than_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig (litLtStatement 255 256))) article = true := by
  apply accepted_of_derivation
  exact complete_litLt fixed_in controlTheory controlTheory_hosted.builtin 255 256
    (by decide +kernel) (by decide +kernel)

theorem literal_addition_wraps :
    litAddStatement (wordBound - 1) 1 =
      .eq (.app (.builtin .litAdd) [.natLit (wordBound - 1), .natLit 1]) (.natLit 0) := by
  decide +kernel

theorem literal_addition_wraparound_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig
        (.eq (.app (.builtin .litAdd) [.natLit (wordBound - 1), .natLit 1]) (.natLit 0))))
      article = true := by
  rw [← literal_addition_wraps]
  apply accepted_of_derivation
  exact complete_litAdd fixed_in controlTheory controlTheory_hosted.builtin
    (wordBound - 1) 1 (by decide +kernel) (by decide +kernel)

theorem literal_multiplication_wraps :
    litMulStatement (wordBound - 1) 2 =
      .eq (.app (.builtin .litMul) [.natLit (wordBound - 1), .natLit 2])
        (.natLit (wordBound - 2)) := by decide +kernel

theorem literal_multiplication_wraparound_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig
        (.eq (.app (.builtin .litMul) [.natLit (wordBound - 1), .natLit 2])
          (.natLit (wordBound - 2))))) article = true := by
  rw [← literal_multiplication_wraps]
  apply accepted_of_derivation
  exact complete_litMul fixed_in controlTheory controlTheory_hosted.builtin
    (wordBound - 1) 2 (by decide +kernel) (by decide +kernel)

theorem literal_nonzero_division_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig (litDivStatement 5 2))) article = true := by
  apply accepted_of_derivation
  exact complete_litDiv fixed_in controlTheory controlTheory_hosted.builtin 5 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem division_zero_no_operation_derivation (a : Nat) (q r : Pattern) :
    ¬ FODerivable controlRules (jNDivMod (encNat a) (encNat 0) q r) := by
  intro d
  have hm : NDivModM (encNat a) (encNat 0) q r :=
    meaning_of_foDerivable controlTheory_hosted d
  obtain ⟨_, v, _, _, _, hv⟩ := hm a 0 (decNat_encNat a) (decNat_encNat 0)
  exact Nat.not_lt_zero v hv

theorem division_zero_rejects (a : Nat) (q r : Pattern) (article : RawProof) :
    checkRaw (kernelValidated controlTheory 4)
      (jNDivMod (encNat a) (encNat 0) q r) article = false :=
  rejects_of_nonderivability (division_zero_no_operation_derivation a q r) article

theorem literal_byte_length_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig (litLengthStatement [7, 8]))) article = true := by
  apply accepted_of_derivation
  exact complete_litLength fixed_in controlTheory controlTheory_hosted.builtin [7, 8]
    (by decide +kernel)

theorem literal_byte_in_range_accepts :
    ∃ article, checkRaw (kernelValidated controlTheory 4)
      (jThm (encTerm controlTheory.sig (litGetStatement [7, 8] 1))) article = true := by
  apply accepted_of_derivation
  exact complete_litGet fixed_in controlTheory controlTheory_hosted.builtin [7, 8] 1
    (by decide +kernel) (by decide +kernel)

theorem byte_index_bounds_no_operation_derivation (bytes : List UInt8) (index : Nat)
    (hbound : bytes.length ≤ index) (result : Pattern) :
    ¬ FODerivable controlRules (jNth (encBytes bytes) (encNat index) result) := by
  intro d
  have hm : NthM (encBytes bytes) (encNat index) result :=
    meaning_of_foDerivable controlTheory_hosted d
  obtain ⟨k, hk, hget⟩ := hm (bytes.map fun b => encNat b.toNat) (decList_encBytes bytes)
  have heq : index = k := by simpa only [decNat_encNat, Option.some.injEq] using hk
  subst k
  have hnone : (bytes.map fun b => encNat b.toNat)[index]? = none :=
    List.getElem?_eq_none (by simpa using hbound)
  rw [hnone] at hget
  contradiction

theorem byte_index_bounds_rejects (bytes : List UInt8) (index : Nat)
    (hbound : bytes.length ≤ index) (result : Pattern) (article : RawProof) :
    checkRaw (kernelValidated controlTheory 4)
      (jNth (encBytes bytes) (encNat index) result) article = false :=
  rejects_of_nonderivability
    (byte_index_bounds_no_operation_derivation bytes index hbound result) article

theorem byte_index_at_length_rejects (result : Pattern) (article : RawProof) :
    checkRaw (kernelValidated controlTheory 4)
      (jNth (encBytes [7, 8]) (encNat 2) result) article = false :=
  byte_index_bounds_rejects [7, 8] 2 (by decide +kernel) result article

/-! ## Uniform qualification of every stored rule -/

/-- Exact stored-rule lookup ensures rejection occurs at positional argument
validation, independently of the goal and children of the article. -/
theorem wrong_argument_arity_rejects {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules)
    (r : FORule) (hr : r ∈ rules) (args : List Pattern)
    (hlen : args.length ≠ r.vars.length) (goal : Pattern) (children : List RawProof) :
    checkRaw definition goal (.node ⟨⟨r.id⟩, args⟩ children) = false := by
  have hlookup := presents.lookup hr
  have hargs : argumentsValidAt r.toSchema.metavariables args = false := by
    cases ha : argumentsValidAt r.toSchema.metavariables args with
    | false => rfl
    | true =>
        have heq := argumentsValidAt_length ha
        have heq' : args.length = r.vars.length := by
          simpa only [FORule.toSchema, FORule.formals, List.length_map] using heq.symm
        exact False.elim (hlen heq')
  simp [checkRaw, instantiateRule?, hlookup, hargs]

def tooManyArguments (r : FORule) : List Pattern := List.replicate (r.vars.length + 1) cN0

def argumentArityArticle (r : FORule) : RawProof :=
  .node ⟨⟨r.id⟩, tooManyArguments r⟩ []

theorem tooManyArguments_length (r : FORule) :
    (tooManyArguments r).length = r.vars.length + 1 := by simp [tooManyArguments]

theorem tooManyArguments_valid (r : FORule) :
    ∀ arg ∈ tooManyArguments r, argumentValidAt 0 arg = true := by
  intro arg harg
  have heq : arg = cN0 := List.eq_of_mem_replicate harg
  subst arg
  rfl

/-- All 123 fixed rules, including the eleven built-in declarations, have a
concrete raw article with individually valid data arguments that is refused
because it has one extra positional argument. -/
theorem fixed_rule_argument_count_rejects (r : FORule) (hr : r ∈ kernelRules) :
    checkRaw kernelFixedValidated (r.instConclusion (tooManyArguments r))
      (argumentArityArticle r) = false := by
  apply wrong_argument_arity_rejects kernelFixedValidated_presents r hr
  simp [tooManyArguments]

theorem fixed_rule_argument_count_controls :
    ∀ r ∈ kernelRules,
      (∀ arg ∈ tooManyArguments r, argumentValidAt 0 arg = true) ∧
      checkRaw kernelFixedValidated (r.instConclusion (tooManyArguments r))
        (argumentArityArticle r) = false := by
  intro r hr
  exact ⟨tooManyArguments_valid r, fixed_rule_argument_count_rejects r hr⟩

/-- The same qualification uses exact lookup in every actual theory-extended
package; structural validation needs no mathematical assumption about axioms. -/
theorem admitted_rule_argument_count_rejects (T : Theory) (allocated : Nat)
    (r : FORule) (hr : r ∈ theoryRules T allocated) :
    checkRaw (kernelValidated T allocated) (r.instConclusion (tooManyArguments r))
      (argumentArityArticle r) = false := by
  apply wrong_argument_arity_rejects (kernelValidated_presents T allocated) r
    (List.mem_append.mpr (Or.inr hr))
  simp [tooManyArguments]

theorem admitted_rule_argument_count_controls (T : Theory) (allocated : Nat) :
    ∀ r ∈ theoryRules T allocated,
      (∀ arg ∈ tooManyArguments r, argumentValidAt 0 arg = true) ∧
      checkRaw (kernelValidated T allocated) (r.instConclusion (tooManyArguments r))
        (argumentArityArticle r) = false := by
  intro r hr
  exact ⟨tooManyArguments_valid r, admitted_rule_argument_count_rejects T allocated r hr⟩

theorem symbol_rule_argument_count_rejects (T : Theory) (allocated k : Nat)
    (hk : k < allocated) :
    checkRaw (kernelValidated T allocated)
      ((symbolRule T.sig k).instConclusion (tooManyArguments (symbolRule T.sig k)))
      (argumentArityArticle (symbolRule T.sig k)) = false := by
  apply admitted_rule_argument_count_rejects
  have hmem : symbolRule T.sig k ∈ (List.range allocated).map (symbolRule T.sig) :=
    List.mem_map_of_mem (List.mem_range.mpr hk)
  simp [theoryRules, hmem]

theorem axiom_rule_argument_count_rejects (T : Theory) (allocated : Nat)
    (r : FORule) (hr : r ∈ axiomRules T.sig 1 T.axioms) :
    checkRaw (kernelValidated T allocated) (r.instConclusion (tooManyArguments r))
      (argumentArityArticle r) = false := by
  apply admitted_rule_argument_count_rejects
  simp [theoryRules, hr]

theorem definition_rule_argument_count_rejects (T : Theory) (allocated : Nat)
    (r : FORule) (hr : r ∈ theoryDefinitionRules T.sig 1 T.definitions) :
    checkRaw (kernelValidated T allocated) (r.instConclusion (tooManyArguments r))
      (argumentArityArticle r) = false := by
  apply admitted_rule_argument_count_rejects
  simp [theoryRules, hr]

end Mettapedia.Languages.VibeITP.Presentation.KernelControls
