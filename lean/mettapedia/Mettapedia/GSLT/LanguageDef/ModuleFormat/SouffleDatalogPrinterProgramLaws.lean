import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterClauseLaws
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterDeclarationLaws

/-! Universal readback of every successfully constructed source program.
This theorem concerns the authored syntax tree, projection and independent
program IR. Packed parsing of its printed text remains a separate boundary. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open ProgramProjection

theorem relations_tail (source : Pattern) (attributes tail : List Pattern) :
    Reference.relationsInto? source attributes tail =
      (Reference.relationsInto? source attributes []).map (· ++ tail) := by
  unfold Reference.relationsInto?
  split
  · rfl
  · rename_i identifier before after rest
    rw [relations_tail rest attributes tail]
    cases Reference.relationsInto? rest attributes [] <;> rfl
  · rfl
termination_by sizeOf source
decreasing_by all_goals subst_vars; simp_wf; omega

theorem item_tail (source : Pattern) (tail : List Pattern) :
    Reference.itemInto? source tail = (Reference.itemInto? source []).map (· ++ tail) := by
  unfold Reference.itemInto?
  split
  · rename_i space relations before start attributes
    cases read : Reference.attributes? attributes with
    | none => rfl
    | some fields => exact relations_tail relations fields tail
  · rename_i fact
    cases Reference.fact? fact <;> rfl
  · rename_i rule
    cases Reference.rule? rule <;> rfl
  · rfl
  · rfl
  · rfl

theorem statement_read (statement : Statement) (source : Pattern)
    (built : statement? statement = .ok source) :
    ∃ code, Reference.itemInto? source [] = some [code] ∧
      Frontend.normalize? code = some (IRCodec.statement statement) := by
  cases statement with
  | declaration declaration =>
      cases read : declaration? declaration with
      | error reason => simp only [statement?, read] at built; cases built
      | ok declarationSource =>
          have same : node "item-declaration" [declarationSource] = source := by simpa [statement?, read] using built
          subst source
          exact declaration_read declaration declarationSource read
  | fact fact =>
      cases read : fact? fact with
      | error reason => simp only [statement?, read] at built; cases built
      | ok factSource =>
          have same : node "item-fact" [factSource] = source := by simpa [statement?, read] using built
          subst source
          have normalized := fact_read fact factSource read
          cases projected : Reference.fact? factSource with
          | none => simp [projected] at normalized
          | some code =>
              refine ⟨code, ?_, ?_⟩
              · change (Reference.fact? factSource).map (· :: []) = _
                rw [projected]
                rfl
              · simpa only [projected, Option.bind_some, IRCodec.statement] using normalized
  | rule clause =>
      cases read : clause? clause with
      | error reason => simp only [statement?, read] at built; cases built
      | ok clauseSource =>
          have same : node "item-rule" [clauseSource] = source := by simpa [statement?, read] using built
          subst source
          have normalized := clause_read clause clauseSource read
          cases projected : Reference.rule? clauseSource with
          | none => simp [projected] at normalized
          | some code =>
              refine ⟨code, ?_, ?_⟩
              · change (Reference.rule? clauseSource).map (· :: []) = _
                rw [projected]
                rfl
              · simpa only [projected, Option.bind_some, IRCodec.statement] using normalized
  | input names =>
      cases read : qualifiedName? names with
      | error reason => simp only [statement?, read] at built; cases built
      | ok name =>
          have same : node "item-input" [node "input" [directiveSpace,name]] = source := by
            simpa [statement?, read] using built
          subst source
          refine ⟨.apply "InputRelation" [Reference.relation name], rfl, ?_⟩
          apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
          simp only [Frontend.normalizeChildren?, relation_normalize _ _ read, Option.bind_eq_bind, Option.bind_some]
          rfl
  | output names =>
      cases read : qualifiedName? names with
      | error reason => simp only [statement?, read] at built; cases built
      | ok name =>
          have same : node "item-output" [node "output" [directiveSpace,name]] = source := by
            simpa [statement?, read] using built
          subst source
          refine ⟨.apply "OutputRelation" [Reference.relation name], rfl, ?_⟩
          apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
          simp only [Frontend.normalizeChildren?, relation_normalize _ _ read, Option.bind_eq_bind, Option.bind_some]
          rfl

theorem items_read (statements : List Statement) (sources : List Pattern)
    (built : statements.mapM statement? = .ok sources) :
    ∃ codes, Reference.itemsInto? (items sources) [] = some codes ∧
      Frontend.normalizeChildren? codes = some (statements.map IRCodec.statement) := by
  induction statements generalizing sources with
  | nil => cases Except.ok.inj built; exact ⟨[],rfl,rfl⟩
  | cons statement rest ih =>
      cases head : statement? statement with
      | error reason => rw [List.mapM_cons, head] at built; cases built
      | ok source =>
          cases tail : rest.mapM statement? with
          | error reason => rw [List.mapM_cons, head, tail] at built; cases built
          | ok remaining =>
              rw [List.mapM_cons, head, tail] at built
              cases Except.ok.inj built
              obtain ⟨code,projected,normalized⟩ := statement_read statement source head
              obtain ⟨codes,restProjected,restNormalized⟩ := ih remaining tail
              refine ⟨code :: codes, ?_, ?_⟩
              · change ((Reference.itemsInto? (items remaining) []).bind fun rest => Reference.itemInto? source rest) = _
                rw [restProjected]
                change Reference.itemInto? source codes = _
                rw [item_tail, projected]
                rfl
              · simp only [Frontend.normalizeChildren?, normalized, restNormalized, Option.bind_eq_bind, Option.bind_some]
                rfl

theorem program_tree_readback (program : Program) (source : Pattern)
    (built : programTree? program = .ok source) :
    (Reference.projectProgram? source).bind Frontend.normalize? = some (IRCodec.program program) := by
  cases statementsRead : program.statements.mapM statement? with
  | error reason => simp only [programTree?, statementsRead] at built; cases built
  | ok statements =>
      have same : node "program" [empty,items statements] = source := by simpa [programTree?, statementsRead] using built
      subst source
      obtain ⟨codes,projected,normalized⟩ := items_read program.statements statements statementsRead
      change ((Reference.itemsInto? (items statements) []).map Reference.program).bind Frontend.normalize? = _
      rw [projected]
      change Frontend.normalize? (Reference.program codes) = _
      apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
      simp only [Frontend.normalizeChildren?, normalize_vector _ _ normalized, Option.bind_eq_bind, Option.bind_some]
      rfl

theorem program_tree_roundtrip (program : Program) (source : Pattern)
    (built : programTree? program = .ok source) :
    ((Reference.projectProgram? source).bind Frontend.normalize?).bind IRCodec.program? = some program := by
  rw [program_tree_readback program source built, Option.bind_some, IRCodec.program_roundtrip]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
