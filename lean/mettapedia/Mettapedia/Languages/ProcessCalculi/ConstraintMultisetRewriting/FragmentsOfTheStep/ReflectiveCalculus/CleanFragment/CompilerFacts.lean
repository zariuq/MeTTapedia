import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Readback

/-!
# A structural property of the literal compiler image

The initial compiler writes no target knowledge. Intermediate and otherwise
clean states can retain information, so raw onto-ness is different from the
equational onto theorem. This property is proved by the compiler's actual
recursive decomposition, not assumed as a property of a translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open ByInstantiation (sig G)

theorem rowAt_knowledge_empty {context : Ctx sig} {sort : ByInstantiation.Srt} (term : G context sort) :
    (Encodings.rowAt term).knowledge = [] := by
  cases context <;> cases sort <;> rfl

theorem tensor_knowledge_empty {first second : RawState}
    (left : first.knowledge = []) (right : second.knowledge = []) :
    (Encodings.tensor first second).knowledge = [] := by
  change ByInstantiation.knowledge.applyStore _ first.knowledge ++
    ByInstantiation.knowledge.applyStore _ second.knowledge = []
  rw [left, right]
  rfl

theorem encodeAt_knowledge_empty : {context : Ctx sig} → {sort : ByInstantiation.Srt} →
    (term : G context sort) → (Encodings.encodeAt term).knowledge = []
  | _, _, .var bound => rowAt_knowledge_empty (.var bound)
  | _, _, .op (.inr operation) _ => operation.key.elim
  | _, _, .op (.inl .zero) .nil => rfl
  | _, _, .op (.inl .bag) (.cons elements .nil) => encodeAt_knowledge_empty elements
  | _, _, .op (.inl .pnil) .nil => rfl
  | _, _, .op (.inl .pcons) (.cons first (.cons rest .nil)) => by
      have firstKnown := encodeAt_knowledge_empty first
      have restKnown := encodeAt_knowledge_empty rest
      cases rest with
      | var bound =>
          exact tensor_knowledge_empty firstKnown restKnown
      | op operation arguments =>
          cases operation with
          | inr operation => exact operation.key.elim
          | inl operation =>
              cases operation with
              | pnil => cases arguments; exact firstKnown
              | pcons =>
                  exact tensor_knowledge_empty firstKnown restKnown
  | _, _, .op (.inl .input) arguments => rowAt_knowledge_empty (.op (.inl .input) arguments)
  | _, _, .op (.inl .output) arguments => rowAt_knowledge_empty (.op (.inl .output) arguments)
  | _, _, .op (.inl .dropq) arguments => rowAt_knowledge_empty (.op (.inl .dropq) arguments)
  | _, _, .op (.inl .quote) arguments => rowAt_knowledge_empty (.op (.inl .quote) arguments)
termination_by _ _ term => termSize term
decreasing_by all_goals (simp only [termSize, argsSize]; omega)

theorem compile_knowledge_empty (process : RhoProcess) : (compile process).val.knowledge = [] :=
  encodeAt_knowledge_empty (Encodings.twin process)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment
