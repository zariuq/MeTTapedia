import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplates

/-!
# Row-local equations in the existing constructed-template grammar

The value grammar is reused unchanged. A schema output carries its own
finite equation list over private holes and actor captures. Ordinary and
shared outputs have no additional template-condition payload. Lowering uses
the existing rule; schema conditions are published as data, not asserted
as requirements on the caller's global information.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSource

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualTemplateSource

variable {S : Signature} {Local Inner Shared O : Type}
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S) (captures : Shared → MetaArity S)

def Conditions {Γ : Ctx S} {sort : S.Srt} : Production locals inners captures Γ sort → Type
  | .schema _ => ContextualResidual.Problem (Blueprint locals inners captures)
  | .ordinary _ | .shared _ => PUnit

abbrev Description (context : Ctx S) (sort : S.Srt) :=
  (production : Production locals inners captures context sort) × Conditions locals inners captures production

structure Rule (context : Ctx S) (sort : S.Srt) where
  code : ContextualTemplateSource.Rule locals inners captures context sort
  conditions : (port : Fin code.produce.length) → Conditions locals inners captures (code.produce.get port)

namespace Rule

variable {locals inners captures} {Γ : Ctx S} {sort : S.Srt}

def descriptions (rule : Rule locals inners captures Γ sort) :
    List (Nat × Description locals inners captures Γ sort) :=
  List.ofFn fun port : Fin rule.code.produce.length =>
    (port.val, ⟨rule.code.produce.get port, rule.conditions port⟩)

def outputsFor [DecidableEq O] (rule : Rule locals inners captures Γ sort) (made : List O) :
    O → Option (Nat × Description locals inners captures Γ sort) :=
  ContextualTemplateSource.assign made rule.descriptions

def eraseDescription (entry : Nat × Description locals inners captures Γ sort) := (entry.1, entry.2.1)

theorem descriptions_erase (rule : Rule locals inners captures Γ sort) :
    rule.descriptions.map eraseDescription = rule.code.descriptors locals inners captures := by
  rw [descriptions, List.map_ofFn]
  rfl

theorem outputs_erase [DecidableEq O] (rule : Rule locals inners captures Γ sort) (made : List O) (occurrence : O) :
    (rule.outputsFor made occurrence).map eraseDescription = rule.code.outputsFor locals inners captures made occurrence := by
  rw [outputsFor, ContextualTemplateSource.assign_values_map, descriptions_erase]
  rfl

def ordinaryFlags [DecidableEq O] (rule : Rule locals inners captures Γ sort) (made : List O) (occurrence : O) : Bool :=
  match rule.code.outputsFor locals inners captures made occurrence with
  | some (_, .ordinary _) => true
  | _ => false

theorem output_at_port [DecidableEq O] (rule : Rule locals inners captures Γ sort) (made : List O)
    (unique : made.Nodup) (sameLength : made.length = rule.code.produce.length) (port : Fin made.length) :
    rule.outputsFor made (made.get port) =
      some (port.val, ⟨rule.code.produce.get ⟨port.val, by omega⟩, rule.conditions ⟨port.val, by omega⟩⟩) := by
  have length : made.length = rule.descriptions.length := sameLength.trans (List.length_ofFn).symm
  exact (ContextualTemplateSource.assign_get made rule.descriptions unique length port).trans
    (congrArg some (List.get_ofFn _ _))

theorem output_origin [DecidableEq O] (rule : Rule locals inners captures Γ sort) (made : List O)
    (unique : made.Nodup) (sameLength : made.length = rule.code.produce.length)
    (occurrence : O) (origin : Nat) (description : Description locals inners captures Γ sort)
    (selected : rule.outputsFor made occurrence = some (origin, description)) :
    ∃ port : Fin rule.code.produce.length, port.val = origin ∧
      (⟨rule.code.produce.get port, rule.conditions port⟩ : Description locals inners captures Γ sort) = description := by
  have member := ContextualTemplateSource.assign_mem made rule.descriptions occurrence (origin, description) selected
  obtain ⟨position, same⟩ := List.mem_iff_get.mp member
  have atPort := rule.output_at_port made unique sameLength position
  rw [same] at atPort
  have pairEq := Option.some.inj (atPort.symm.trans selected)
  exact ⟨⟨position.val, by omega⟩, congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩

end Rule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSource
