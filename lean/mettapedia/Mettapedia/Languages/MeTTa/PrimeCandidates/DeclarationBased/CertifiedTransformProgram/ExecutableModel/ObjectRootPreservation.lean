import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectTemplates

/-!
# Preservation of typing by the annotated root steps of the object package

Every rewrite schema of the object package (`objectSchemas`) has an elaborated
right side that is typed where the typing of its left side puts it:

* the identity eliminator's rule `J A x P d y (refl a) ⟶ d` under the equations
  of its reflexivity position, `a = x` and `a = y` at `A`
  (`j_templateTypedEq`); without them the method's type `P x (refl x)` is not the
  left side's type `P y (refl a)`;
* every other schema without equations: the computation rules of `num-rec`, the
  equations of addition, of the iterated power set and of the iterator, the
  definitions by one equation, and the decoding of implication and of every
  quantifier and equation instance.

So every schema has a typed template (`objectSchemas_template`), and the
annotated root steps of the object package preserve typing in formed contexts,
given the injectivity and no-confusion of the annotated type formers
(`objectChurch_rootPreserving`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName)

namespace CodeModel

/-! ## The identity eliminator -/

/-- The context of the identity eliminator's rule, annotated: the carrier, the
base point, the motive, the method, the endpoint and the point of reflexivity. -/
abbrev cJTele : CCtx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.var 0))
    (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0)))
    (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))) (.var 3)) (.var 4)

/-- The positions of the eliminator's left side type its metavariables by the
eliminator's context. -/
theorem j_knowledge : ∀ i, patternKnowledge objectDecls none
    (eliminatorLeft (Head := Tower.Head) jName) i = some (cJTele.lookup i) := by
  decide

/-- The eliminator's left side synthesizes `P y (refl a)`. -/
theorem j_leftType : leftType objectDecls (eliminatorLeft (Head := Tower.Head) jName) =
    some (.app (.app (.var 3) (.var 1)) (.refl (.var 0))) := by
  decide

/-- The equations of the eliminator's reflexivity position: its point `a` equals
the base point `x` and the endpoint `y` at the carrier `A`. -/
theorem j_equations : patternEquations objectDecls none
    (eliminatorLeft (Head := Tower.Head) jName) =
      [(.var 0, .var 4, .var 5), (.var 0, .var 1, .var 5)] := by
  decide

/-- The eliminator's right side, the method, has no abstraction to annotate. -/
theorem j_elabRight : elabRight objectDecls (eliminatorLeft (Head := Tower.Head) jName) (.var 2) =
    .var 2 := by
  decide

/-- **The identity eliminator's rule is typed under its endpoint equations**: at an
instance `J A x P d y (refl a)` whose point `a` equals the base point `x` and the
endpoint `y`, the method `d : P x (refl x)` has the left side's type
`P y (refl a)`. -/
theorem j_templateTypedEq :
    TemplateTypedEq objectChurch objectDecls (eliminatorLeft jName) (.var 2) := by
  refine ⟨cJTele, .app (.app (.var 3) (.var 1)) (.refl (.var 0)), j_knowledge, j_leftType, ?_⟩
  intro n Γ σ _ mor eqs
  rw [j_equations] at eqs
  have toPoint : CEqual objectChurch Γ (σ 0) (σ 4) (σ 5) := eqs _ List.mem_cons_self
  have toEnd : CEqual objectChurch Γ (σ 0) (σ 1) (σ 5) :=
    eqs _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have motive : CTyped objectChurch Γ (σ 3)
      (.pi (σ 5) (.pi (.id ((σ 5).rename wk) ((σ 4).rename wk) (.var 0)) cU0)) := mor 3
  have method : CTyped objectChurch Γ (σ 2) (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) := mor 2
  have family : CTm.inst0 (σ 4) (.pi (.id ((σ 5).rename wk) ((σ 4).rename wk) (.var 0)) cU0) =
      (.pi (.id (σ 5) (σ 4) (σ 4)) cU0 : CTm Tower.Head n) := by
    change CTm.pi (.id (CTm.inst0 (σ 4) ((σ 5).rename wk)) (CTm.inst0 (σ 4) ((σ 4).rename wk))
      (σ 4)) cU0 = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]
  have atEnd := CDerivable.appCong (.refl motive) (.trans (.symm toPoint) toEnd)
  rw [family] at atEnd
  have atPoint : CEqual objectChurch Γ (.app (.app (σ 3) (σ 4)) (.refl (σ 4)))
      (.app (.app (σ 3) (σ 1)) (.refl (σ 0))) cU0 :=
    CDerivable.appCong atEnd (.reflCong (.symm toPoint))
  rw [j_elabRight]
  exact .conv method atPoint (.sort _)

/-! ## Every schema -/

/-- **Every schema of the object package has a typed template**: its left side is
not a reflexivity proof, and its elaborated right side is typed at the instances
that satisfy the equations of its reflexivity positions. -/
theorem objectSchemas_template {k : Nat} {L R : Tm Tower.Head k} (rule : objectSchemas L R) :
    (∀ a, L ≠ .refl a) ∧ TemplateTypedEq objectChurch objectDecls L R := by
  rcases rule with rule | rule
  · obtain ⟨p, mem, rule⟩ := DeclaredComputation.mem_of_schemaUnionAll rule
    simp only [computationSpecs, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨i, k', fields, hi, rule⟩ := rule
      rcases i with _ | _ | i
      · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        cases rule
        exact ⟨(fun _ h => nomatch h), numRecZero_template.templateTypedEq⟩
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        cases rule
        exact ⟨(fun _ h => nomatch h), numRecSuc_template.templateTypedEq⟩
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hi
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact ⟨(fun _ h => nomatch h), addZero_template.templateTypedEq⟩
      · exact ⟨(fun _ h => nomatch h), addSuc_template.templateTypedEq⟩
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact ⟨(fun _ h => nomatch h), powZero_template.templateTypedEq⟩
      · exact ⟨(fun _ h => nomatch h), powSuc_template.templateTypedEq⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), j_templateTypedEq⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), eqAt_template.templateTypedEq⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), sucMove_template.templateTypedEq⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), keep_template.templateTypedEq⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), transport_template.templateTypedEq⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), compose_template.templateTypedEq⟩
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact ⟨(fun _ h => nomatch h), iterZero_template.templateTypedEq⟩
      · exact ⟨(fun _ h => nomatch h), iterSuc_template.templateTypedEq⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), returnIter_template.templateTypedEq⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), sucStep_template.templateTypedEq⟩
  · rcases rule with rule | ⟨a, A, carrier, rule⟩ | ⟨e, A, carrier, rule⟩
    · cases rule
      exact ⟨(fun _ h => nomatch h), imp_templateTyped.templateTypedEq⟩
    · change (SetProfile.allInstance? a).map typeTerm = some A at carrier
      cases found : SetProfile.allInstance? a with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          obtain rfl := SetProfile.allInstance?_eq_some found
          cases rule
          exact ⟨(fun _ h => nomatch h), (all_templateTyped type).templateTypedEq⟩
    · change (if true = true then (SetProfile.eqInstance? e).map typeTerm else none) = some A
        at carrier
      rw [if_pos rfl] at carrier
      cases found : SetProfile.eqInstance? e with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          obtain rfl := SetProfile.eqInstance?_eq_some found
          cases rule
          exact ⟨(fun _ h => nomatch h), (eq_templateTyped type).templateTypedEq⟩

/-! ## Preservation -/

/-- **The annotated root steps of the object package preserve typing** in formed
contexts, given the injectivity and no-confusion of the annotated type formers. -/
theorem objectChurch_rootPreserving (facts : CFormerFacts objectChurch) :
    CRootPreserving objectChurch :=
  ChurchRules.ofSchemas_rootPreserving objectSchemas objectRules_presents fun rule =>
    SchemaPreserving.of_templateTypedEq facts ConvRules.objectLevels
      (objectSchemas_firstOrder rule).1 (objectSchemas_template rule).1
      (objectSchemas_template rule).2

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
