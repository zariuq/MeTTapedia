import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-! # Reindexing the family of candidates

A map into a step's firing family pulls back its effects and admission.
Restriction to a program is a special case. No guard, literal-store or
exactness profile is required; each such certificate is inherited separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

universe uO uT uH uOcc uS uF uG

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF} {Candidate : State → Type uG}
  (P : Step X O State Firing) (select : ∀ {s : State}, Candidate s → Firing s)

def reindex : Step X O State Candidate where
  frame := P.frame
  knowledge := P.knowledge
  present := P.present
  selection f := P.selection (select f)
  target f := P.target (select f)
  extension f := P.extension (select f)
  information f := P.information (select f)
  information_refines f := P.information_refines (select f)
  Shapes f := P.Shapes (select f)
  preparedResult f := P.preparedResult (select f)
  present_preparedResult f := P.present_preparedResult (select f)
  preparedSettle f := P.preparedSettle (select f)
  result_refines f := P.result_refines (select f)
  Admits f := P.Admits (select f)
  admitted_prepares _ admitted := P.prepares admitted

theorem reindex_admits_iff {s : State} (f : Candidate s) :
    (P.reindex select).Admits f ↔ P.Admits (select f) := Iff.rfl

theorem reindex_prepares_iff {s : State} (f : Candidate s) :
    (P.reindex select).Prepares f ↔ P.Prepares (select f) := Iff.rfl

instance reindex_guarded [P.Guarded] : (P.reindex select).Guarded where
  holds f := P.Holds (select f)
  admission f := P.admits_iff_prepares (select f)

instance reindex_literalInformation [P.LiteralInformation] : (P.reindex select).LiteralInformation :=
  ⟨fun f => P.transported (select f)⟩

instance reindex_literalKnowledge [P.LiteralKnowledge] : (P.reindex select).LiteralKnowledge :=
  ⟨fun f => P.knowledge_preparedResult (select f)⟩

instance reindex_exact [P.Exact] : (P.reindex select).Exact :=
  ⟨fun f => Exact.exactness (P := P) (select f)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step
