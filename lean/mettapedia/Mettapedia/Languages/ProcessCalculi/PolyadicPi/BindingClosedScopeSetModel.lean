import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedStaticInterpretation
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# A nonconstant set-valued model of the complete structural schemas

Parallel composition observes set union and private binding observes every
supplied name. Every input arity retains its full function domain, while
outputs retain their ordered vectors. The seven independently declared
structural schemas are verified on arbitrary metadata and environments.

This is a static observation model. It forgets multiplicity and does not
interpret operational evidence generators or count communications.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedScopeSetModel

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel

abbrev Token := Nat × List Nat

abbrev sort : Srt → Type
  | .nm => Nat
  | .pr => Set Token

def nameDomain (arity : Nat) : Type := contextOf (S := AllArity.sig) sort (AllArity.names arity)
def argumentDomain (arity : Nat) : Type := familyOf (S := AllArity.sig)
  (fun context result => contextOf sort context ⟶[Type] sort result) (AllArity.nameArguments arity)

def argumentValues : (arity : Nat) → argumentDomain arity → List Nat
  | 0, _ => []
  | arity + 1, supplied =>
      (show PUnit ⟶ Nat from supplied.1) PUnit.unit :: argumentValues arity supplied.2

def operations : ClosedPresentation.Operations AllArity.sig (Type) where
  sort := sort
  operation
    | .nil => ↾fun _ => ∅
    | .par => ↾fun supplied =>
        ((show PUnit ⟶ Set Token from supplied.1) PUnit.unit) ∪
          ((show PUnit ⟶ Set Token from supplied.2.1) PUnit.unit)
    | .out arity => ↾fun supplied =>
        {((show PUnit ⟶ Nat from supplied.1) PUnit.unit, argumentValues arity supplied.2)}
    | .inp arity => ↾fun supplied =>
        {((show PUnit ⟶ Nat from supplied.1) PUnit.unit, [])} ∪
          {token | ∃ names : nameDomain arity,
            token ∈ (show nameDomain arity ⟶ Set Token from supplied.2.1) names}
    | .nu => ↾fun supplied =>
        {token | ∃ name : Nat,
          token ∈ (show nameDomain 1 ⟶ Set Token from supplied.1) (name, PUnit.unit)}
    | .rep => ↾fun supplied => (show PUnit ⟶ Set Token from supplied.1) PUnit.unit

def processValue {context : Ctx AllArity.sig} {Z : Type}
    (environment : operations.model.Env Z context) (position : Var context .pr) (point : Z) : Set Token :=
  environment .pr position point

theorem structural_schemas : operations.model.SchemaFamilySatisfaction AllArity.equations := by
  intro origin
  rcases origin with ⟨index, bound⟩
  cases index with
  | zero =>
      apply Model.ElemOver.ext
      funext Z parameters environment
      apply ConcreteCategory.hom_ext
      intro point
      change (processValue environment .zero point ∪ processValue environment (.succ .zero) point) =
        processValue environment (.succ .zero) point ∪ processValue environment .zero point
      exact Set.union_comm _ _
  | succ index =>
      cases index with
      | zero =>
          apply Model.ElemOver.ext
          funext Z parameters environment
          apply ConcreteCategory.hom_ext
          intro point
          change (processValue environment .zero point ∪ processValue environment (.succ .zero) point) ∪
            processValue environment (.succ (.succ .zero)) point =
              processValue environment .zero point ∪ (processValue environment (.succ .zero) point ∪
                processValue environment (.succ (.succ .zero)) point)
          exact Set.union_assoc _ _ _
      | succ index =>
          cases index with
          | zero =>
              apply Model.ElemOver.ext
              funext Z parameters environment
              apply ConcreteCategory.hom_ext
              intro point
              change processValue environment .zero point ∪ ∅ = processValue environment .zero point
              exact Set.union_empty _
          | succ index =>
              cases index with
              | zero =>
                  apply Model.ElemOver.ext
                  funext Z parameters environment
                  apply ConcreteCategory.hom_ext
                  intro point
                  change {token | ∃ _ : Nat, token ∈ processValue environment .zero point} =
                    processValue environment .zero point
                  ext token
                  exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨0, member⟩⟩
              | succ index =>
                  cases index with
                  | zero =>
                      apply Model.ElemOver.ext
                      funext Z parameters environment
                      apply ConcreteCategory.hom_ext
                      intro point
                      change ({token | ∃ name : Nat,
                          token ∈ (show nameDomain 1 ⟶ Set Token from (parameters point).1)
                            (name, PUnit.unit)} ∪ processValue environment .zero point) =
                        {token | ∃ name : Nat,
                          token ∈ (show nameDomain 1 ⟶ Set Token from (parameters point).1)
                            (name, PUnit.unit) ∪ processValue environment .zero point}
                      ext token
                      constructor
                      · rintro (⟨name, member⟩ | member)
                        · exact ⟨name, Or.inl member⟩
                        · exact ⟨0, Or.inr member⟩
                      · rintro ⟨name, member | member⟩
                        · exact Or.inl ⟨name, member⟩
                        · exact Or.inr member
                  | succ index =>
                      cases index with
                      | zero =>
                          apply Model.ElemOver.ext
                          funext Z parameters environment
                          apply ConcreteCategory.hom_ext
                          intro point
                          change {token | ∃ first second : Nat,
                              token ∈ (show nameDomain 2 ⟶ Set Token from (parameters point).2.1)
                                (second, first, PUnit.unit)} =
                            {token | ∃ first second : Nat,
                              token ∈ (show nameDomain 2 ⟶ Set Token from (parameters point).2.1)
                                (first, second, PUnit.unit)}
                          ext token
                          exact ⟨fun ⟨first, second, member⟩ => ⟨second, first, member⟩,
                            fun ⟨first, second, member⟩ => ⟨second, first, member⟩⟩
                      | succ index =>
                          cases index with
                          | zero =>
                              apply Model.ElemOver.ext
                              funext Z parameters environment
                              apply ConcreteCategory.hom_ext
                              intro point
                              change processValue environment .zero point =
                                processValue environment .zero point ∪ processValue environment .zero point
                              exact (Set.union_self _).symm
                          | succ index =>
                              simp [AllArity.equations, PolyadicPi.equations] at bound
                              omega

def sourceCompiler := Bridges.NamePassingGeneratedStatic.interpretation operations structural_schemas

theorem source_schemas :
    (Bridges.NamePassingGeneratedStatic.operations operations).model.SchemaFamilySatisfaction
      Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredEquations.equations :=
  Bridges.NamePassingGeneratedStatic.schema_family_satisfied operations structural_schemas

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedScopeSetModel
