import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPreservation

/-! Scope preservation for the actual independent source transitions. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

theorem transition_wellScoped {registry : SpaceSemantics.Program} {source target : Configuration}
    (edge : Transition registry source target) (well : WellScoped source) : WellScoped target := by
  have ordered := ScopedSource.transition_uses_mono edge
  have original : ConfigurationSupported (Mettapedia.ScopedString.Before source.uses) source := well
  have promoted := original.mono (fun _ old => Mettapedia.ScopedString.before_mono ordered old)
  obtain ⟨controlGood,framesGood,cellsGood,outputGood⟩ := promoted
  cases edge
  all_goals dsimp only at controlGood framesGood cellsGood outputGood ⊢
  all_goals try solve |
    simp_all [WellScoped,ConfigurationSupported,ControlSupported,FrameSupported,AnswerSupported,
      supported_expression,Effects.boolean]
  case native_query bindings index held answers used control queried =>
    exact (native_query_scoped_step registry source bindings held index answers used well control queried).2
  case primitive bindings head index held answers after control ordinary notRemove notMatch native returned =>
    exact (primitive_scoped_step registry source bindings head held answers index after well control
      ordinary notRemove notMatch native returned).2
  case equations bindings head index held selected used control ordinary notRemove notNative chosen =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    exact application_supported _ _ _ _ _ _ _ _ _ good.1
      (resolved_values_supported _ _ _ good.1 good.2.2) (Nat.le_refl _) chosen
  case dynamic_equations bindings callee supplied head selected used control resolved notNative registered chosen =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,invocationFrames_supported _ selected _ framesGood,cellsGood,outputGood⟩
    exact application_supported _ _ _ _ _ _ _ _ _ good.1
      (resolved_values_supported _ _ _ good.1 good.2.2) (Nat.le_refl _) chosen
  case dynamic_native bindings callee supplied head control resolved native =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,?_,cellsGood,outputGood⟩
    · simp only [ControlSupported,List.not_mem_nil,false_implies,implies_true,true_and]
      exact ⟨good.1,resolved_values_supported _ _ _ good.1 good.2.2⟩
    · simpa only [List.mem_cons,forall_eq_or_imp,FrameSupported,true_and] using framesGood
  case dynamic_partial bindings callee supplied captured head control recognized =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported,supported_symbol,true_and]
    refine ⟨good.1,?_⟩
    intro value member
    rcases List.mem_append.mp member with present | present
    · exact partial_captures_supported _ _ _ _ (supported_resolve good.1 callee good.2.1)
        recognized value present
    · exact resolved_values_supported _ _ _ good.1 good.2.2 value present
  case dynamic_data bindings callee supplied control notPartial notCallable =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported,List.mem_singleton,forall_eq,AnswerSupported]
    refine ⟨(supported_expression _ _).mpr ?_,good.1⟩
    simp only [List.mem_cons,forall_eq_or_imp]
    exact ⟨supported_resolve good.1 callee good.2.1,resolved_values_supported _ _ _ good.1 good.2.2⟩
  case construct bindings held index control =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported,List.mem_singleton,forall_eq,AnswerSupported,supported_expression]
    exact ⟨resolved_values_supported _ _ _ good.1 good.2.2,good.1⟩
  case value_variable bindings name control =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported,List.mem_singleton,forall_eq,AnswerSupported]
    exact ⟨supported_resolve good.1 _ good.2,good.1⟩
  case quote_enter bindings expression control =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    have held : Supported (Mettapedia.ScopedString.Before source.uses) expression := by
      simpa [supported_expression] using good.2
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported,List.mem_singleton,forall_eq,AnswerSupported]
    exact ⟨supported_resolve good.1 expression held,good.1⟩
  case partial_value bindings head captured control =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported,List.mem_singleton,forall_eq,AnswerSupported]
    exact ⟨supported_resolve good.1 _ good.2,good.1⟩
  case evaluate_code bindings index held control =>
    have good := controlGood
    simp only [control,ControlSupported,List.mem_singleton,forall_eq] at good
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported]
    exact ⟨good.1,supported_resolve good.1 held good.2.2⟩
  case raw_argument bindings target first rest values index control raw =>
    have good := controlGood
    simp only [control,ControlSupported,List.mem_cons,forall_eq_or_imp] at good
    refine ⟨?_,?_,cellsGood,outputGood⟩
    · simp only [ControlSupported,List.mem_singleton,forall_eq,AnswerSupported]
      exact ⟨supported_resolve good.1 first good.2.1.1,good.1⟩
    · simpa only [List.mem_cons,forall_eq_or_imp,FrameSupported] using And.intro
        (And.intro good.2.1.2 good.2.2) framesGood
  case read_line bindings index first rest control input =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported,List.mem_singleton,forall_eq,AnswerSupported]
    exact ⟨renamed_supported_before _ source.uses (by omega) first,good.1⟩
  case print bindings index held control =>
    have good := controlGood
    simp only [control,ControlSupported,List.mem_singleton,forall_eq] at good
    have resolvedGood := supported_resolve good.1 held good.2.2
    refine ⟨?_,framesGood,cellsGood,?_⟩
    · simpa [ControlSupported,AnswerSupported,Effects.boolean] using good.1
    · intro output member
      rcases List.mem_append.mp member with present | present
      · exact outputGood output present
      · simp only [List.mem_singleton] at present
        subst output
        exact resolvedGood
  case remove bindings index location pattern after answers used control removed =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    obtain ⟨same,answersGood⟩ := removeRows_supported (Mettapedia.ScopedString.Before (source.uses + used))
      _ _ _ _ _ _ _ removed
    refine ⟨?_,framesGood,?_,outputGood⟩
    · simp only [ControlSupported]
      intro answer member
      obtain ⟨value,present,rfl⟩ := List.mem_map.mp member
      exact ⟨answersGood value present,good.1⟩
    · intro name value stored
      exact cellsGood name value (by rw [← same]; exact stored)
  case let_star bindings pairs body nested control expanded =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    have parts : (∀ pair ∈ pairs, Supported (Mettapedia.ScopedString.Before source.uses) pair) ∧
        Supported (Mettapedia.ScopedString.Before source.uses) body := by
      simpa [supported_expression] using good.2
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported]
    exact ⟨good.1,nestedLets_supported _ body parts.2 _ _ parts.1 expanded⟩
  case case_enter bindings value rows cases control parsed =>
    have good := controlGood
    simp only [control,ControlSupported] at good
    have parts : Supported (Mettapedia.ScopedString.Before source.uses) value ∧
        ∀ row ∈ rows, Supported (Mettapedia.ScopedString.Before source.uses) row := by
      simpa [supported_expression] using good.2
    refine ⟨?_,?_,cellsGood,outputGood⟩
    · simpa only [ControlSupported] using And.intro good.1 parts.1
    · simpa only [List.mem_cons,forall_eq_or_imp,FrameSupported] using And.intro
        (readCases_supported _ _ _ parts.2 parsed) framesGood
  case fault_caught reason earned rest control recovered =>
    have recoveredGood := recoverDynamic_supported _ source.frames [] earned rest (by simp) framesGood recovered
    refine ⟨?_,recoveredGood.2,cellsGood,outputGood⟩
    simpa only [ControlSupported] using recoveredGood.1
  case dispatch_return answers rest control frames =>
    simp only [control,ControlSupported] at controlGood
    simp only [frames,List.mem_cons,forall_eq_or_imp,FrameSupported,true_and] at framesGood
    refine ⟨?_,framesGood,cellsGood,outputGood⟩
    simp only [ControlSupported,List.not_mem_nil,false_implies,implies_true,and_true]
    intro selected member
    obtain ⟨answer,present,rfl⟩ := List.mem_map.mp member
    exact dispatchAnswer_supported _ answer (controlGood answer present)
  case collapse_return answers outer rest control frames =>
    simp only [frames,List.mem_cons,forall_eq_or_imp,FrameSupported] at framesGood
    refine ⟨?_,framesGood.2,cellsGood,outputGood⟩
    simp only [ControlSupported,List.mem_singleton,forall_eq,AnswerSupported]
    exact ⟨(supported_expression _ _).mpr (copies_supported _ _ _ (Nat.le_refl _)),framesGood.1⟩
  case sequence_return answers collected pending rest control frames =>
    simp only [control,ControlSupported] at controlGood
    simp only [frames,List.mem_cons,forall_eq_or_imp,FrameSupported] at framesGood
    refine ⟨?_,framesGood.2,cellsGood,outputGood⟩
    simp only [ControlSupported]
    refine ⟨framesGood.1.1,?_⟩
    intro answer member
    rcases List.mem_append.mp member with present | present
    · exact framesGood.1.2 answer present
    · exact controlGood answer present
  case argument_return answers values pending destination index rest control frames =>
    simp only [control,ControlSupported] at controlGood
    simp only [frames,List.mem_cons,forall_eq_or_imp,FrameSupported] at framesGood
    refine ⟨?_,framesGood.2,cellsGood,outputGood⟩
    simp only [ControlSupported,List.not_mem_nil,false_implies,implies_true,and_true]
    intro selected member
    obtain ⟨answer,present,rfl⟩ := List.mem_map.mp member
    have good := controlGood answer present
    simp only [ControlSupported]
    refine ⟨good.2,framesGood.1.1,?_⟩
    intro value member
    rcases List.mem_append.mp member with old | last
    · exact framesGood.1.2 value old
    · simp only [List.mem_singleton] at last
      subst value
      exact good.1
  case binding_return answers pattern body rest continued control frames bound =>
    simp only [control,ControlSupported] at controlGood
    simp only [frames,List.mem_cons,forall_eq_or_imp,FrameSupported] at framesGood
    refine ⟨?_,framesGood.2,cellsGood,outputGood⟩
    simp only [ControlSupported,List.not_mem_nil,false_implies,implies_true,and_true]
    exact bindAnswers_supported _ pattern body framesGood.1.1 framesGood.1.2 _ _ controlGood bound
  case case_return answers cases rest continued control frames selected =>
    simp only [control,ControlSupported] at controlGood
    simp only [frames,List.mem_cons,forall_eq_or_imp,FrameSupported] at framesGood
    refine ⟨?_,framesGood.2,cellsGood,outputGood⟩
    simp only [ControlSupported,List.not_mem_nil,false_implies,implies_true,and_true]
    exact selectAnswers_supported _ cases framesGood.1 _ _ controlGood selected
  case if_return answers yes no rest control frames =>
    simp only [control,ControlSupported] at controlGood
    simp only [frames,List.mem_cons,forall_eq_or_imp,FrameSupported] at framesGood
    refine ⟨?_,framesGood.2,cellsGood,outputGood⟩
    simp only [ControlSupported,List.not_mem_nil,false_implies,implies_true,and_true]
    intro selected member
    obtain ⟨answer,present,rfl⟩ := List.mem_map.mp member
    simp only [ControlSupported]
    refine ⟨(controlGood answer present).2,?_⟩
    split
    · exact framesGood.1.1
    · exact framesGood.1.2
  case query_return answers pattern body rest continued used control frames queried =>
    simp only [control,ControlSupported] at controlGood
    simp only [frames,List.mem_cons,forall_eq_or_imp,FrameSupported] at framesGood
    refine ⟨?_,framesGood.2,cellsGood,outputGood⟩
    simp only [ControlSupported,List.not_mem_nil,false_implies,implies_true,and_true]
    exact queries_supported _ source.state pattern body framesGood.1.1 framesGood.1.2 _ _ _ _
      controlGood (Nat.le_refl _) queried

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
