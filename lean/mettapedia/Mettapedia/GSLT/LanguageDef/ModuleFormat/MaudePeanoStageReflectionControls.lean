import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoStageReflection
import Mettapedia.Languages.Maude.PeanoArithmetic

/-! Whole-stage coverage and separating negatives for nested symbolic
terms and arbitrary numeral multiplication. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoReflectionControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Maude.PeanoEquationRules Maude.PeanoNormalization
open PeanoSimulation PeanoReflection

def context : Maude.VariableContext := [("N", "Nat"), ("M", "Nat")]
def nested : Maude.Term := .app "peano.succ" [.app "peano.add" [.app "peano.zero" [], .var "N"]]
def rightVariable : Maude.Term := .app "peano.succ" [.var "N"]
def wrongVariable : Maude.Term := .app "peano.succ" [.var "M"]

theorem nested_typed : Maude.HasSort Maude.Examples.peano.signature context nested "Nat" :=
  successor_typed (addition_typed (zero_typed context) (.var (by decide_cbv)))

theorem nested_covered :
    Relation.ReflTransGen (ReferenceStep.Step Engine.RelationEnv.empty (language peano))
      (encode nested) (encode rightVariable) := by
  have reached := normalizer_reached Engine.RelationEnv.empty context nested nested_typed
  have computed : reduce nested = rightVariable := by cbv
  rw [computed] at reached
  exact reached

theorem wrong_variable_refused :
    ¬ Relation.ReflTransGen (ReferenceStep.Step Engine.RelationEnv.empty (language peano))
      (encode nested) (encode wrongVariable) := by
  intro path
  have sourcePath := (reference_path_iff Engine.RelationEnv.empty nested_typed).mp path
  have same := path_same_reduce nested_typed sourcePath
  have first : reduce nested = rightVariable := by cbv
  have second : reduce wrongVariable = wrongVariable := by cbv
  rw [first, second] at same
  change Maude.Term.app "peano.succ" [.var "N"] = Maude.Term.app "peano.succ" [.var "M"] at same
  have names := Maude.Term.var.inj (List.cons.inj (Maude.Term.app.inj same).2).1
  exact (by decide : ("N" : String) ≠ "M") names

theorem wrong_product_refused (left right wrong : Nat) (different : left * right ≠ wrong) :
    ¬ Relation.ReflTransGen (ReferenceStep.Step Engine.RelationEnv.empty (language peano))
      (encode (.app "peano.mul" [Maude.Examples.numeral "peano" left, Maude.Examples.numeral "peano" right]))
      (encode (Maude.Examples.numeral "peano" wrong)) := by
  intro path
  have typed := multiplication_typed (numeral_typed [] left) (numeral_typed [] right)
  have sourcePath := (reference_path_iff Engine.RelationEnv.empty typed).mp path
  have same := path_same_reduce typed sourcePath
  rw [reduce_multiply_numerals, reduce_numeral] at same
  have read := congrArg numeralValue? same
  exact different (by simpa only [numeralValue?_numeral, Option.some.injEq] using read)

theorem product_normal (left right : Nat) :
    ∀ target, ¬ ReferenceStep.Step Engine.RelationEnv.empty (language peano)
      (encode (Maude.Examples.numeral "peano" (left * right))) target := by
  have noStep := normalizer_no_step Engine.RelationEnv.empty
    (multiplication_typed (numeral_typed [] left) (numeral_typed [] right))
  rw [reduce_multiply_numerals] at noStep
  exact noStep

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoReflectionControls
