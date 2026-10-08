import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualSemanticSubstitution
import Mettapedia.TypeTheory.ContextualCwfUniverseLift
import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism
import Mettapedia.GSLT.Core.ContextualPseudoCwfMorphism

/-!
# The generated refinement dependent-model morphism

Mixed contextual evaluation and typed equation descent define the context
and family components. Successful telescope extension evaluation earns the
chosen comprehension comparison. Both models use the checked common-level
carrier lift, so mixed native size presentations retain all values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Refinement.Abstract

universe u c s t m p z
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}

noncomputable abbrev SourceModel (D : Signature S) :=
  commonLiftWithTerminal.{u, u, u, u, z} (QuotientCwf.withTerminal D)

abbrev TargetModel (C : CwfWithTerminal.{c, s, t, m}) :=
  commonLiftWithTerminal.{c, s, t, m, u} C

variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

noncomputable def liftedBase : (SourceModel.{u, max c s t m} D).toCwf.base.Context ⥤
    (TargetModel.{u, c, s, t, m} C).toCwf.base.Context where
  obj context := ⟨⟨(contextValue model context.val.down.as).1⟩⟩
  map morphism := ⟨(quotientFunctor model).map morphism.down⟩
  map_id context := congrArg ULift.up ((quotientFunctor model).map_id context.val.down)
  map_comp earlier later := congrArg ULift.up ((quotientFunctor model).map_comp earlier.down later.down)

noncomputable def familyMorphism : CwfFamilyMorphism
    (SourceModel.{u, max c s t m} D).toCwf (TargetModel.{u, c, s, t, m} C).toCwf where
  base := liftedBase model
  family :=
    { app := fun context =>
        { onIndex := fun type => ⟨typeValue model type.down⟩
          onFibre := fun _ term => ⟨termValue model term.down⟩ }
      naturality := by
        intro source target morphism
        apply IndexedFamily.Hom.ext
        · funext type
          exact congrArg ULift.up (type_substitution model type.down morphism.unop.down)
        · intro type term
          exact up_heq (term_substitution model term.down morphism.unop.down) }

@[simp] theorem familyMorphism_type_readout {context : (SourceModel.{u, max c s t m} D).toCwf.Ctx}
    (type : (SourceModel.{u, max c s t m} D).toCwf.Ty context) :
    ((familyMorphism model).mapType type).down = typeValue model type.down := rfl

@[simp] theorem familyMorphism_term_readout {context : (SourceModel.{u, max c s t m} D).toCwf.Ctx}
    {type : (SourceModel.{u, max c s t m} D).toCwf.Ty context}
    (term : (SourceModel.{u, max c s t m} D).toCwf.Tm context type) :
    ((familyMorphism model).mapTerm term).down = termValue model term.down := rfl

theorem context_empty : contextValue model (Contextual.empty D) = Mettapedia.TypeTheory.ContextualPredicateModelScopes.Scope.nil C
    model.localModel.doctrine model.localModel.assumptions :=
  Abstract.Derivation.contextValue_unique model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice (Contextual.empty D).formed.judgment) _ rfl

theorem context_extension (context : Context D) (type : TypeOver context) :
    contextValue model (Contextual.extend context type) =
      (contextValue model context).snoc (rawType model type) :=
  Abstract.Derivation.contextValue_unique model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice (Contextual.extend context type).formed.judgment) _
      (model.data.evaluateContext_snoc context.raw type.code _ _
        (context_readout model context) (type_readout model type))

theorem empty_preserved :
    (familyMorphism model).base.obj ⟨(SourceModel.{u, max c s t m} D).empty⟩ =
      ⟨(TargetModel.{u, c, s, t, m} C).empty⟩ := by
  apply ContextualBase.Context.ext
  apply congrArg ULift.up
  exact congrArg Sigma.fst (context_empty model)

theorem extension_preserved (context : (SourceModel.{u, max c s t m} D).toCwf.Ctx)
    (type : (SourceModel.{u, max c s t m} D).toCwf.Ty context) :
    (familyMorphism model).base.obj ⟨(SourceModel.{u, max c s t m} D).toCwf.ext context type⟩ =
      ⟨(TargetModel.{u, c, s, t, m} C).toCwf.ext
        ((familyMorphism model).base.obj ⟨context⟩).val ((familyMorphism model).mapType type)⟩ := by
  apply ContextualBase.Context.ext
  apply congrArg ULift.up
  have representative : rawType model (QuotientCwf.typeRepresentative type.down) =
      typeValue model type.down :=
    congrArg (typeValue model) (QuotientCwf.typeRepresentative_class type.down)
  exact (congrArg Sigma.fst (context_extension model context.down.as
    (QuotientCwf.typeRepresentative type.down))).trans
      (congrArg (C.toCwf.ext (contextValue model context.down.as).1) representative)


theorem evaluated_arrows_heq {n k : Nat}
    {first second : Abstract.ModelScope C model.localModel n}
    {target : Abstract.ModelScope C model.localModel k}
    (contexts : first = second) (substitution : Substitution S k n)
    {left : C.toCwf.Sub first.1 target.1} {right : C.toCwf.Sub second.1 target.1}
    (leftRead : model.data.evaluateSubstitution first target substitution = some left)
    (rightRead : model.data.evaluateSubstitution second target substitution = some right) : HEq left right := by
  cases contexts
  exact heq_of_eq (Option.some.inj (leftRead.symm.trans rightRead))

theorem lookup_sections_heq {n : Nat} {first second : Abstract.ModelScope C model.localModel n}
    (contexts : first = second) (index : Fin n) :
    HEq (first.2.lookup index).2 (second.2.lookup index).2 := by
  cases contexts
  rfl

theorem raw_projection_heq (context : Context D) (type : TypeOver context) :
    HEq (rawArrow model (projectionHom context type)) (C.toCwf.wk (rawType model type)) := by
  apply evaluated_arrows_heq model (context_extension model context type)
    (fun index => .var index.succ) (arrow_readout model (projectionHom context type))
  exact (model.data.evaluateSubstitution_eq_some_iff _ _ _ _).mpr (fun _ => rfl)

theorem raw_variable_heq (context : Context D) (type : TypeOver context) :
    HEq (rawTerm model (newest context type)) (C.toCwf.vz (rawType model type)) := by
  have read := term_readout model (newest context type)
  have variableRead : model.data.evaluateTerm (contextValue model (extend context type)) (.var 0) =
      some ((contextValue model (extend context type)).2.lookup 0) := rfl
  have value := Option.some.inj (read.symm.trans variableRead)
  exact (Sigma.mk.inj value).2.trans
    (lookup_sections_heq model (context_extension model context type) 0)

theorem wk_type_heq {context : C.toCwf.Ctx} {first second : C.toCwf.Ty context}
    (types : first = second) : HEq (C.toCwf.wk first) (C.toCwf.wk second) := by
  cases types
  rfl

theorem vz_type_heq {context : C.toCwf.Ctx} {first second : C.toCwf.Ty context}
    (types : first = second) : HEq (C.toCwf.vz first) (C.toCwf.vz second) := by
  cases types
  rfl

theorem hom_eq_of_source_heq {T : CwfWithTerminal.{c, s, t, m}}
    {first second target : T.toCwf.base.Context} (contexts : first = second)
    (left : first ⟶ target) (right : second ⟶ target) (same : HEq left right) :
    left = eqToHom contexts ≫ right := by
  cases contexts
  exact (eq_of_heq same).trans (Category.id_comp right).symm

theorem term_eqToHom_heq {T : CwfWithTerminal.{c, s, t, m}}
    {source target : T.toCwf.base.Context} (contexts : source = target)
    {type : T.toCwf.Ty target.val} (term : T.toCwf.Tm target.val type) :
    HEq (T.toCwf.tmSub term (show T.toCwf.Sub source.val target.val from eqToHom contexts)) term := by
  cases contexts
  exact (heq_of_eq (T.toCwf.tmSub_id term)).trans (cast_heq _ _)

set_option backward.isDefEq.respectTransparency false in
theorem projection_preserved (context : (SourceModel.{u, max c s t m} D).toCwf.Ctx)
    (type : (SourceModel.{u, max c s t m} D).toCwf.Ty context) :
    (familyMorphism model).base.map
      (show (⟨(SourceModel.{u, max c s t m} D).toCwf.ext context type⟩ :
        (SourceModel.{u, max c s t m} D).toCwf.base.Context) ⟶ ⟨context⟩ from
          (SourceModel.{u, max c s t m} D).toCwf.wk type) =
      eqToHom (extension_preserved model context type) ≫
        (show (⟨(TargetModel.{u, c, s, t, m} C).toCwf.ext
          ((familyMorphism model).base.obj ⟨context⟩).val ((familyMorphism model).mapType type)⟩ :
          (TargetModel.{u, c, s, t, m} C).toCwf.base.Context) ⟶
          (familyMorphism model).base.obj ⟨context⟩ from
            (TargetModel.{u, c, s, t, m} C).toCwf.wk ((familyMorphism model).mapType type)) := by
  apply hom_eq_of_source_heq (extension_preserved model context type)
  exact up_heq ((raw_projection_heq model context.down.as (QuotientCwf.typeRepresentative type.down)).trans
    (wk_type_heq (congrArg (typeValue model) (QuotientCwf.typeRepresentative_class type.down))))

set_option backward.isDefEq.respectTransparency false in
theorem variable_preserved (context : (SourceModel.{u, max c s t m} D).toCwf.Ctx)
    (type : (SourceModel.{u, max c s t m} D).toCwf.Ty context) :
    HEq ((familyMorphism model).mapTerm ((SourceModel.{u, max c s t m} D).toCwf.vz type))
      ((TargetModel.{u, c, s, t, m} C).toCwf.tmSub
        ((TargetModel.{u, c, s, t, m} C).toCwf.vz ((familyMorphism model).mapType type))
        (show (TargetModel.{u, c, s, t, m} C).toCwf.Sub
          ((familyMorphism model).base.obj ⟨(SourceModel.{u, max c s t m} D).toCwf.ext context type⟩).val
          ((TargetModel.{u, c, s, t, m} C).toCwf.ext
            ((familyMorphism model).base.obj ⟨context⟩).val ((familyMorphism model).mapType type)) from
              eqToHom (extension_preserved model context type))) := by
  have representative : rawType model (QuotientCwf.typeRepresentative type.down) =
      typeValue model type.down :=
    congrArg (typeValue model) (QuotientCwf.typeRepresentative_class type.down)
  exact (up_heq ((termValue_retains_section model (QuotientCwf.vz type.down)).trans
    ((raw_variable_heq model context.down.as (QuotientCwf.typeRepresentative type.down)).trans
      (vz_type_heq representative)))).trans
      (term_eqToHom_heq (extension_preserved model context type) _).symm

/-- The generated contextual interpretation satisfies the existing complete
strict terminal/comprehension contract. -/
noncomputable def strictMorphism : StrictCwfMorphism
    (SourceModel.{u, max c s t m} D) (TargetModel.{u, c, s, t, m} C) where
  toFamilyMorphism := familyMorphism model
  empty_preserved := empty_preserved model
  extension_preserved := extension_preserved model
  projection_preserved := projection_preserved model
  variable_preserved := variable_preserved model

noncomputable def pseudoMorphism : PseudoCwfMorphism
    (SourceModel.{u, max c s t m} D) (TargetModel.{u, c, s, t, m} C) :=
  (strictMorphism model).toPseudo

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
