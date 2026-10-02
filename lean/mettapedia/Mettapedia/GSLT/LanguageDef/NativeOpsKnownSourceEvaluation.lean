import Mettapedia.GSLT.LanguageDef.NativeOpsSourceComposition

/-!
# Composing independently established source evaluations

These inversion laws consume exact evaluations of the actual operands. They
retain the existing finite execution relations and introduce no evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

theorem source_known_arguments_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (state : SourceState World) {expressions : List Expr} {values : List SourceValue}
    (known : List.Forall₂ (fun expression value => ∀ out,
      SourceExprEval interface heap calls frame expression state out ↔
        out = ⟨.ok value, state⟩) expressions values)
    (out : SourceArgumentsOutcome World) :
    SourceArgumentsEval interface heap calls frame expressions state out ↔
      out = ⟨.ok values, state⟩ := by
  induction known generalizing out with
  | nil => exact source_arguments_nil_exact state out
  | @cons expression value expressions values head tail ih =>
      rw [source_arguments_cons_exact]
      constructor
      · rintro (⟨first, middle, rest, ran, remaining, same⟩ | ⟨fault, after, ran, same⟩)
        · cases (head _).mp ran
          cases (ih _).mp remaining
          exact same
        · cases (head _).mp ran
      · intro same
        exact .inl ⟨value, state, ⟨.ok values, state⟩, (head _).mpr rfl,
          (ih _).mpr rfl, same⟩

theorem source_known_strict_expression_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (expression : Expr) (state : SourceState World)
    {expressions : List Expr} {values : List SourceValue}
    (operands : sourceStrictOperands? expression = some expressions)
    (known : List.Forall₂ (fun child value => ∀ out,
      SourceExprEval interface heap calls frame child state out ↔
        out = ⟨.ok value, state⟩) expressions values)
    (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame expression state out ↔
      sourcePrimitive interface heap calls frame expression values state out := by
  rw [source_strict_expression_exact expression expressions operands]
  constructor
  · rintro (⟨actual, middle, ran, primitive⟩ | ⟨fault, after, ran, same⟩)
    · cases (source_known_arguments_exact state known _).mp ran
      exact primitive
    · cases (source_known_arguments_exact state known _).mp ran
  · intro primitive
    exact .inl ⟨values, state, (source_known_arguments_exact state known _).mpr rfl, primitive⟩

theorem source_known_reference_field_location_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (base : Expr) (member record : String) (pointer : Option Address) (state : SourceState World)
    (type : inferExpr interface (sourceFrameScope frame) base = some (.ref (.named record)))
    (known : ∀ out, SourceExprEval interface heap calls frame base state out ↔
      out = ⟨.ok (.reference pointer), state⟩)
    (out : SourceLocationOutcome World) :
    SourceLocationEval interface heap calls frame (.field base member) state out ↔
      sourcePrimitiveLocation interface heap frame (.field base member) [.reference pointer] state out := by
  have operands : sourceStrictLocationOperands? interface frame (.field base member) = some [base] := by
    simp [sourceStrictLocationOperands?, type]
  have children : List.Forall₂ (fun child value => ∀ out,
      SourceExprEval interface heap calls frame child state out ↔ out = ⟨.ok value, state⟩)
      [base] [.reference pointer] := .cons known .nil
  constructor
  · intro ran
    cases ran with
    | strict other evaluated primitive =>
        cases Option.some.inj (operands.symm.trans other)
        cases (source_known_arguments_exact state children _).mp evaluated
        exact primitive
    | strictFault other evaluated =>
        cases Option.some.inj (operands.symm.trans other)
        cases (source_known_arguments_exact state children _).mp evaluated
    | fieldValue other _ _ | fieldValueFault other _ =>
        rw [type] at other
        cases other
  · intro primitive
    exact .strict operands ((source_known_arguments_exact state children _).mpr rfl) primitive

end Mettapedia.GSLT.LanguageDef.NativeOps
