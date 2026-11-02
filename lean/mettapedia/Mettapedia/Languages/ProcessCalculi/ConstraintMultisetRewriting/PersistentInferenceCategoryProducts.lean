import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategory

/-!
# Cartesian structure of persistent proof observation

The empty and concatenated supported contexts are concrete objects. Terminal
maps, projections and the diagonal are represented by zero-step executions
with structural selections of existing theorem occurrences. Pairing uses the
actual proof-realization construction. Product laws hold at the declared proof
observation; no physical theorem occurrence is consumed by weakening or copied
by contraction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceJudgmentBoards
open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {definition : ValidatedCalculusLanguageDef}

namespace PersistentContext

def empty (definition : ValidatedCalculusLanguageDef) : PersistentContext definition :=
  ⟨[], by intro pattern member; cases member⟩

noncomputable def toEmptyRepresentative (source : PersistentContext definition) :
    Representative source (empty definition) :=
  identityExecution source.board ⟨Fin.elim0, fun index => Fin.elim0 index⟩

noncomputable def toEmpty (source : PersistentContext definition) : source ⟶ empty definition :=
  Quotient.mk _ source.toEmptyRepresentative

theorem terminal_map_has_no_steps (source : PersistentContext definition) :
    source.toEmptyRepresentative.actors = [] := rfl

theorem toEmpty_unique {source : PersistentContext definition} (morphism : source ⟶ empty definition) :
    morphism = source.toEmpty := by
  apply readout_injective
  exact ClassifyingContext.OpenDerivationList.eq_nil (readout morphism)

noncomputable def emptyIsTerminal (definition : ValidatedCalculusLanguageDef) :
    IsTerminal (empty definition) :=
  IsTerminal.ofUniqueHom toEmpty (fun _ morphism => toEmpty_unique morphism)

noncomputable instance hasTerminal (definition : ValidatedCalculusLanguageDef) :
    HasTerminal (PersistentContext definition) := (emptyIsTerminal definition).hasTerminal

noncomputable def product (first second : PersistentContext definition) : PersistentContext definition :=
  ⟨first.board.judgments ++ second.board.judgments, by
    intro pattern member
    rcases List.mem_append.mp member with left | right
    · exact first.supported pattern (first.board_judgments ▸ left)
    · exact second.supported pattern (second.board_judgments ▸ right)⟩

theorem product_context (first second : PersistentContext definition) :
    (product first second).board.context definition =
      ClassifyingContext.concat (first.board.context definition) (second.board.context definition) :=
  congrArg ClassifyingContext.mk (product first second).board_judgments

noncomputable def firstSelection (first second : PersistentContext definition) :
    ContextMap (product first second).board.judgments first.board.judgments :=
  (ContextMap.left first.board.judgments second.board.judgments).transport
    (product first second).board_judgments.symm rfl

noncomputable def secondSelection (first second : PersistentContext definition) :
    ContextMap (product first second).board.judgments second.board.judgments :=
  (ContextMap.right first.board.judgments second.board.judgments).transport
    (product first second).board_judgments.symm rfl

noncomputable def firstRepresentative (first second : PersistentContext definition) :
    Representative (product first second) first :=
  identityExecution (product first second).board (firstSelection first second)

noncomputable def secondRepresentative (first second : PersistentContext definition) :
    Representative (product first second) second :=
  identityExecution (product first second).board (secondSelection first second)

noncomputable def firstProjection (first second : PersistentContext definition) :
    product first second ⟶ first := Quotient.mk _ (firstRepresentative first second)

noncomputable def secondProjection (first second : PersistentContext definition) :
    product first second ⟶ second := Quotient.mk _ (secondRepresentative first second)

theorem projections_have_no_steps (first second : PersistentContext definition) :
    (firstRepresentative first second).actors = [] ∧ (secondRepresentative first second).actors = [] :=
  ⟨rfl, rfl⟩

theorem readout_first (first second : PersistentContext definition) :
    readout (firstProjection first second) = eqToHom (product_context first second) ≫
      ClassifyingContext.fstProjection (first.board.context definition) (second.board.context definition) := by
  change (identityExecution _ (firstSelection first second)).observe = _
  rw [identityExecution_observe]
  dsimp only [Board.context]
  rw [firstSelection, ContextMap.interpret_transport, ContextMap.interpret_left]
  simp only [eqToHom_refl]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

theorem readout_second (first second : PersistentContext definition) :
    readout (secondProjection first second) = eqToHom (product_context first second) ≫
      ClassifyingContext.sndProjection (first.board.context definition) (second.board.context definition) := by
  change (identityExecution _ (secondSelection first second)).observe = _
  rw [identityExecution_observe]
  dsimp only [Board.context]
  rw [secondSelection, ContextMap.interpret_transport, ContextMap.interpret_right]
  simp only [eqToHom_refl]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

noncomputable def pair {source first second : PersistentContext definition}
    (left : source ⟶ first) (right : source ⟶ second) : source ⟶ product first second :=
  Quotient.mk _ (compile source.consistent
    (ClassifyingContext.pair (readout left) (readout right) ≫ eqToHom (product_context first second).symm))

theorem readout_pair {source first second : PersistentContext definition}
    (left : source ⟶ first) (right : source ⟶ second) :
    readout (pair left right) =
      ClassifyingContext.pair (readout left) (readout right) ≫ eqToHom (product_context first second).symm :=
  compile_observe source.consistent _

theorem readout_composition {source middle target : PersistentContext definition}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    readout (first ≫ second) =
      @CategoryStruct.comp (ClassifyingContext definition) _
        (source.board.context definition) (middle.board.context definition) (target.board.context definition)
        (readout first) (readout second) :=
  readout_compose first second

private theorem cancel_transport {C : Type*} [Category* C] {a b c d : C}
    (same : b = c) (first : a ⟶ c) (second : c ⟶ d) :
    (first ≫ eqToHom same.symm) ≫ (eqToHom same ≫ second) = first ≫ second := by
  cases same
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

private theorem cancel_right_transport {C : Type*} [Category* C] {a b c : C}
    (same : b = c) (first : a ⟶ b) :
    (first ≫ eqToHom same) ≫ eqToHom same.symm = first := by
  cases same
  simp only [eqToHom_refl, Category.comp_id]

theorem pair_first {source first second : PersistentContext definition}
    (left : source ⟶ first) (right : source ⟶ second) :
    pair left right ≫ firstProjection first second = left := by
  apply readout_injective
  rw [readout_composition, readout_pair, readout_first]
  exact (cancel_transport _ _ _).trans (ClassifyingContext.pair_fst _ _)

theorem pair_second {source first second : PersistentContext definition}
    (left : source ⟶ first) (right : source ⟶ second) :
    pair left right ≫ secondProjection first second = right := by
  apply readout_injective
  rw [readout_composition, readout_pair, readout_second]
  exact (cancel_transport _ _ _).trans (ClassifyingContext.pair_snd _ _)

theorem pair_unique {source first second : PersistentContext definition}
    (left : source ⟶ first) (right : source ⟶ second) (morphism : source ⟶ product first second)
    (leftEq : morphism ≫ firstProjection first second = left)
    (rightEq : morphism ≫ secondProjection first second = right) : morphism = pair left right := by
  apply readout_injective
  rw [readout_pair]
  have leftRead := congrArg readout leftEq
  have rightRead := congrArg readout rightEq
  rw [readout_composition, readout_first] at leftRead
  rw [readout_composition, readout_second] at rightRead
  have joined : readout morphism ≫ eqToHom (product_context first second) =
      ClassifyingContext.pair (readout left) (readout right) :=
    ClassifyingContext.pair_unique _ _ _
      ((Category.assoc _ _ _).trans leftRead)
      ((Category.assoc _ _ _).trans rightRead)
  exact (cancel_right_transport _ _).symm.trans
    (congrArg (fun selected => selected ≫ eqToHom (product_context first second).symm) joined)

noncomputable def productIsLimit (first second : PersistentContext definition) :
    IsLimit (BinaryFan.mk (firstProjection first second) (secondProjection first second)) :=
  BinaryFan.IsLimit.mk _ (fun left right => pair left right)
    (fun left right => pair_first left right)
    (fun left right => pair_second left right)
    (fun left right morphism leftEq rightEq => pair_unique left right morphism leftEq rightEq)

noncomputable instance hasProduct (first second : PersistentContext definition) :
    HasLimit (Limits.pair first second) :=
  ⟨⟨BinaryFan.mk (firstProjection first second) (secondProjection first second), productIsLimit first second⟩⟩

noncomputable instance hasBinaryProducts (definition : ValidatedCalculusLanguageDef) :
    HasBinaryProducts (PersistentContext definition) :=
  hasBinaryProducts_of_hasLimit_pair (PersistentContext definition)

noncomputable def diagonalSelection (context : PersistentContext definition) :
    ContextMap context.board.judgments (product context context).board.judgments :=
  (ContextMap.pair (ContextMap.id _) (ContextMap.id _)).transport rfl
    (product context context).board_judgments.symm

noncomputable def diagonalRepresentative (context : PersistentContext definition) :
    Representative context (product context context) :=
  identityExecution context.board context.diagonalSelection

noncomputable def diagonal (context : PersistentContext definition) : context ⟶ product context context :=
  Quotient.mk _ context.diagonalRepresentative

theorem diagonal_has_no_steps (context : PersistentContext definition) :
    context.diagonalRepresentative.actors = [] := rfl

theorem diagonal_is_pair (context : PersistentContext definition) :
    context.diagonal = pair (𝟙 context) (𝟙 context) := by
  apply readout_injective
  rw [readout_pair]
  rw [show readout (𝟙 context) = assumptionEnvironment definition context.board.judgments
    from readout_identity context]
  change (identityExecution context.board context.diagonalSelection).observe = _
  rw [identityExecution_observe, diagonalSelection, ContextMap.interpret_transport,
    ContextMap.interpret_pair, ContextMap.interpret_id]
  simp only [eqToHom_refl]
  exact @Category.id_comp (ClassifyingContext definition) _ _ _ _

theorem diagonal_first (context : PersistentContext definition) :
    context.diagonal ≫ firstProjection context context = 𝟙 context := by
  rw [diagonal_is_pair, pair_first]

theorem diagonal_second (context : PersistentContext definition) :
    context.diagonal ≫ secondProjection context context = 𝟙 context := by
  rw [diagonal_is_pair, pair_second]

end PersistentContext

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
