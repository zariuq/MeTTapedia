import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedModels

/-! # The loaded solvability definition quantifies over future frames

Exact readback checks the actual tc_solvable equation. Its body calls the
already identified tc_models symbol, retaining both the target-frame and
morphism quantifiers instead of restricting solutions to endomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedSolvable

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody
open StandardTheoryInterpretation.Interpretation

abbrev solvableType : HOL.Ty AtomicTy :=
  .arr homType (.arr equalType (.arr actionType (.arr objectType (.arr storeType .prop))))

abbrev arguments : HOL.Ctx AtomicTy := [storeType, objectType, actionType, equalType, homType]

def modelsApplication : HOL.Term Symbol (mapType :: objectType :: arguments) .prop :=
  .app (.app (.app (.app (.app (.app (.app (.const HOLLoadedModels.symbol)
    (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
    (.var (.vs (.vs (.vs (.vs (.vs .vz)))))))
    (.var (.vs (.vs (.vs (.vs .vz))))))
    (.var (.vs (.vs (.vs .vz))))) (.var (.vs .vz))) (.var .vz)) (.var (.vs (.vs .vz)))

def body : HOL.ClosedTerm Symbol solvableType :=
  .lam (.lam (.lam (.lam (.lam
    (.app (.const (Symbols.existential objectType))
      (.lam (.app (.const (Symbols.existential mapType)) (.lam modelsApplication))))))))

theorem constant_available :
    (List.lookup "tc_solvable" HOLSemanticDefinitions.received.symbols.constants).isSome = true := by
  decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_solvable" HOLSemanticDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol solvableType :=
  .constant constant (Ty.fromHOL solvableType) (Ty.toHOL_fromHOL solvableType)

def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 12 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 12 definition).get definition_readable

universe w

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (hom : HOL.Ty.denote model.Carrier homType) (equal : HOL.Ty.denote model.Carrier equalType)
    (act : HOL.Ty.denote model.Carrier actionType) (a : HOL.Ty.denote model.Carrier objectType)
    (store : HOL.Ty.denote model.Carrier storeType) :
    model.denote body (fun index => nomatch index) hom equal act a store =
      ULift.up (∃ b map, (model.constDen HOLLoadedModels.symbol hom equal act a b map store).down) := by
  have existsObject : model.constDen (Symbols.existential objectType) =
      (fun predicate => ULift.up (∃ value, model.adm objectType value ∧ (predicate value).down)) :=
    funext (booleans.existential objectType)
  have existsMap : model.constDen (Symbols.existential mapType) =
      (fun predicate => ULift.up (∃ value, model.adm mapType value ∧ (predicate value).down)) :=
    funext (booleans.existential mapType)
  change model.constDen (Symbols.existential objectType) (fun b =>
    model.constDen (Symbols.existential mapType) (fun map =>
      model.constDen HOLLoadedModels.symbol hom equal act a b map store)) = _
  rw [existsObject, existsMap]
  apply ULift.ext
  apply propext
  constructor
  · rintro ⟨b, _, map, _, solves⟩
    exact ⟨b, map, solves⟩
  · rintro ⟨b, map, solves⟩
    exact ⟨b, full _ _, map, full _ _, solves⟩

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem constant_value : model.constDen symbol = model.denote body (fun index => nomatch index) :=
  HOLLoadedReadback.definition_value model full equations symbol body readDefinition

include full equations in
theorem operational_meaning
    (hom : HOL.Ty.denote model.Carrier homType) (equal : HOL.Ty.denote model.Carrier equalType)
    (act : HOL.Ty.denote model.Carrier actionType) (a : HOL.Ty.denote model.Carrier objectType)
    (store : HOL.Ty.denote model.Carrier storeType) :
    model.constDen symbol hom equal act a store =
      ULift.up (∃ b map, (model.constDen HOLLoadedModels.symbol hom equal act a b map store).down) := by
  rw [constant_value model full equations]
  exact denote_body model full (HOLLoadedBooleans.meanings_of_cache model equations full) hom equal act a store

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedSolvable
