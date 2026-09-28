import Mettapedia.Languages.Agda.Native.JudgmentCodec

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec.SyntaxControls
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural Mettapedia.OSLF.Binding

def varWire (i : Nat) : Data := .pair (.atom 0) (.atom i)
def node (op args : Data) : Data := .pair (.atom 1) (.pair op args)
def unary (op : Nat) (arg : Data) : Data := node (.atom op) (.pair arg (.atom 0))

theorem unknown_operator : getOperator (.atom 23) = none := rfl
theorem unknown_term_tag : (rawTerm 1 .term).get (.pair (.atom 2) (.atom 0)) = none := rfl
theorem escaped_variable : (rawTerm 0 .term).get (varWire 0) = none := rfl
theorem wrong_variable_sort : (rawTerm 1 .type).get (varWire 0) = none := rfl
theorem wrong_operator_sort : (rawTerm 0 .term).get (node (.atom 20) (.atom 0)) = none := rfl
theorem missing_argument : (rawTerm 0 .term).get (node (.atom 0) (.atom 0)) = none := rfl
theorem extra_argument :
    (rawTerm 1 .term).get (node (.pair (.atom 7) (.atom 0)) (.pair (varWire 0) (.atom 0))) = none := rfl

theorem binding_scope : (rawTerm 0 .term).get (unary 0 (varWire 0)) = some (lam (.var .zero)) := rfl
theorem nonbinding_scope : (rawTerm 0 .term).get (unary 1 (varWire 0)) = none := rfl
theorem nested_scope_escape : (rawTerm 0 .term).get (unary 0 (unary 0 (varWire 2))) = none := rfl
theorem nested_ambient_variable : (rawTerm 1 .term).get (unary 0 (unary 0 (varWire 2))) =
    some (lam (lam (.var (.succ (.succ .zero))))) := rfl
theorem nested_bound_variable : (rawTerm 1 .term).get (unary 0 (unary 0 (varWire 1))) =
    some (lam (lam (.var (.succ .zero)))) := rfl

theorem nested_capture_excluded :
    (rawTerm 1 .term).get (unary 0 (unary 0 (varWire 2))) ≠ some (lam (lam (.var (.succ .zero)))) := by
  rw [nested_ambient_variable]
  intro same
  cases same

theorem natural_payload : getOperator (.pair (.atom 13) (.atom 149)) = some ⟨_, .setOmega 149⟩ := rfl
theorem name_bytes :
    getOperator (.pair (.atom 5) (.pair (.atom 206) (.pair (.atom 187) (.atom 0)))) =
      some ⟨_, .defined "λ"⟩ := rfl
theorem invalid_name_bytes : getOperator (.pair (.atom 19) (.pair (.atom 255) (.atom 0))) = none := rfl
theorem overlong_name :
    getOperator (.pair (.atom 6) (.pair (.atom 192) (.pair (.atom 128) (.atom 0)))) = none := rfl
theorem surrogate_name : Utf8.read [237, 160, 128] = none := rfl
theorem four_byte_name : Utf8.read [240, 159, 140, 187] = some "🌻" := rfl

def dependentContext : ContextGeometry.RawContext 2 :=
  .snoc (.snoc .nil (Statics.universeType 0 0).code)
    (el (set (levelClosed 1)) (.var .zero))

theorem dependent_context_roundtrip :
    context.get (context.put ⟨2, dependentContext⟩) = some ⟨2, dependentContext⟩ := context.get_put _
theorem malformed_context_scope : context.get (.pair (.atom 0) (varWire 0)) = none := rfl
theorem context_length_checked : (rawContext 1).get (context.put ⟨2, dependentContext⟩) = none := rfl

def twoImages : ContextGeometry.RawSub 2 1 :=
  Telescope.pair (Telescope.pair (Telescope.emptySub (S := sig) .term 1) (.var .zero))
    (lam (.var (.succ .zero)))

theorem substitution_roundtrip :
    (rawSub 2 1).get ((rawSub 2 1).put twoImages) = some twoImages := (rawSub 2 1).get_put _

theorem substitution_missing_image : (rawSub 2 1).get (.pair (.atom 0) (varWire 0)) = none := rfl
theorem substitution_extra_image : (rawSub 0 1).get (.pair (.atom 0) (varWire 0)) = none := rfl

def substitutionJudgment : Statics.Judgment :=
  .substitution ⟨1, .snoc .nil (Statics.universeType 0 0).code⟩ ⟨2, dependentContext⟩ twoImages

theorem substitution_judgment_roundtrip :
    coreJudgment.get (coreJudgment.put substitutionJudgment) = some substitutionJudgment := coreJudgment.get_put _

theorem substitution_judgment_is_not_admission :
    coreJudgment.put substitutionJudgment ≠ coreJudgment.put (Statics.context dependentContext) := by
  intro same
  have equal := coreJudgment.put_injective same
  cases equal

end Mettapedia.Languages.Agda.Native.Codec.SyntaxControls
