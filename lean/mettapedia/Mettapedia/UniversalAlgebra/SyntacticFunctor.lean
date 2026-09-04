import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mettapedia.UniversalAlgebra.EquationSystemInterpretation
import Mettapedia.UniversalAlgebra.SyntacticFiniteProducts

/-!
# Syntactic functors induced by algebraic interpretations

An interpretation of equation systems translates bounded term tuples and
therefore induces a functor between their finite-context syntactic categories.
The functor is identity-on-contexts and preserves the selected terminal and
binary-product structure.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open CategoryTheory

universe u v w

variable {S : Signature.{u}} {T : Signature.{v}} {U : Signature.{w}}

namespace BoundedTermTuple

/-- Translate every component of a bounded term tuple. -/
def translate (symbols : Signature.Interpretation S T)
    {input output : Nat} (tuple : BoundedTermTuple S input output) :
    BoundedTermTuple T input output where
  component position :=
    ⟨(tuple.component position).1.translate symbols,
      Term.variablesBelow_translate symbols (tuple.component position).2⟩

/-- Tuple translation preserves pointwise generated consequence. -/
theorem translate_equivalent
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : EquationSystem.Interpretation source target)
    {input output : Nat}
    {left right : BoundedTermTuple S input output}
    (equivalent : Equivalent source left right) :
    Equivalent target
      (translate interpretation.symbols left)
      (translate interpretation.symbols right) := by
  intro position
  exact interpretation.mapConsequence (equivalent position)

/-- Translation along the identity interpretation fixes every tuple. -/
theorem translate_id {input output : Nat}
    (tuple : BoundedTermTuple S input output) :
    translate (Signature.Interpretation.id S) tuple = tuple := by
  ext position
  exact Term.translate_id (tuple.component position).1

/-- Tuple translation composes with signature interpretation. -/
theorem translate_comp (first : Signature.Interpretation S T)
    (second : Signature.Interpretation T U) {input output : Nat}
    (tuple : BoundedTermTuple S input output) :
    translate (first.comp second) tuple =
      translate second (translate first tuple) := by
  ext position
  exact Term.translate_comp first second (tuple.component position).1

/-- Translation commutes with tuple substitution. -/
theorem translate_comp_tuple (symbols : Signature.Interpretation S T)
    {first second third : Nat}
    (earlier : BoundedTermTuple S first second)
    (later : BoundedTermTuple S second third) :
    translate symbols (comp earlier later) =
      comp (translate symbols earlier) (translate symbols later) := by
  ext position
  change
    ((later.component position).1.subst (substitution earlier)).translate
        symbols =
      ((later.component position).1.translate symbols).subst
        (substitution (translate symbols earlier))
  rw [Term.translate_subst]
  apply Term.subst_eq_of_variablesBelow
    (Term.variablesBelow_translate symbols (later.component position).2)
  intro index below
  simp only [substitution, Term.finSubstitution, below, dite_true, translate]

/-- Translation fixes the raw identity tuple. -/
theorem translate_identity (symbols : Signature.Interpretation S T)
    (size : Nat) :
    translate symbols (identity size) = identity size := by
  ext position
  rfl

/-- Translation commutes with raw pairing. -/
theorem translate_pair (symbols : Signature.Interpretation S T)
    {input left right : Nat}
    (first : BoundedTermTuple S input left)
    (second : BoundedTermTuple S input right) :
    translate symbols (pair first second) =
      pair (translate symbols first) (translate symbols second) := by
  ext position
  refine Fin.addCases ?_ ?_ position
  · intro firstPosition
    simp only [translate, pair, Fin.addCases_left]
  · intro secondPosition
    simp only [translate, pair, Fin.addCases_right]

end BoundedTermTuple

namespace EquationSystem.Interpretation

/-- Translate a quotient arrow along an equation-system interpretation. -/
def mapSyntacticHom {source : EquationSystem S}
    {target : EquationSystem T}
    (interpretation : Interpretation source target)
    {input output : Nat} :
    SyntacticCategory.Hom source input output →
      SyntacticCategory.Hom target input output :=
  Quotient.lift
    (fun tuple => SyntacticCategory.mk target
      (BoundedTermTuple.translate interpretation.symbols tuple))
    (by
      intro left right equivalent
      apply (SyntacticCategory.mk_eq_iff target _ _).mpr
      exact BoundedTermTuple.translate_equivalent interpretation equivalent)

@[simp] theorem mapSyntacticHom_mk {source : EquationSystem S}
    {target : EquationSystem T}
    (interpretation : Interpretation source target)
    {input output : Nat} (tuple : BoundedTermTuple S input output) :
    interpretation.mapSyntacticHom (SyntacticCategory.mk source tuple) =
      SyntacticCategory.mk target
        (BoundedTermTuple.translate interpretation.symbols tuple) := rfl

/-- An algebraic interpretation induces an identity-on-contexts syntactic
functor. -/
def syntacticFunctor {source : EquationSystem S}
    {target : EquationSystem T}
    (interpretation : Interpretation source target) :
    SyntacticCategory source ⥤ SyntacticCategory target where
  obj context := SyntacticCategory.object target
    (SyntacticCategory.objectSize source context)
  map arrow := interpretation.mapSyntacticHom arrow
  map_id context := by
    apply (SyntacticCategory.mk_eq_iff target _ _).mpr
    rw [BoundedTermTuple.translate_identity]
    exact (BoundedTermTuple.consequenceSetoid target _ _).refl _
  map_comp first second := by
    induction first using Quotient.inductionOn with
    | _ first =>
      induction second using Quotient.inductionOn with
      | _ second =>
        apply (SyntacticCategory.mk_eq_iff target _ _).mpr
        rw [BoundedTermTuple.translate_comp_tuple]
        exact (BoundedTermTuple.consequenceSetoid target _ _).refl _

/-- Identity interpretation acts identically on every quotient arrow. -/
theorem mapSyntacticHom_id {system : EquationSystem S}
    {input output : Nat}
    (arrow : SyntacticCategory.Hom system input output) :
    (id system).mapSyntacticHom arrow = arrow := by
  induction arrow using Quotient.inductionOn with
  | _ tuple =>
      apply (SyntacticCategory.mk_eq_iff system _ _).mpr
      change BoundedTermTuple.Equivalent system
        (BoundedTermTuple.translate (Signature.Interpretation.id S) tuple)
        tuple
      rw [BoundedTermTuple.translate_id]
      exact (BoundedTermTuple.consequenceSetoid system _ _).refl tuple

/-- Mapping along a composite interpretation equals successive arrow maps. -/
theorem mapSyntacticHom_comp
    {firstSystem : EquationSystem S}
    {secondSystem : EquationSystem T}
    {thirdSystem : EquationSystem U}
    (first : Interpretation firstSystem secondSystem)
    (second : Interpretation secondSystem thirdSystem)
    {input output : Nat}
    (arrow : SyntacticCategory.Hom firstSystem input output) :
    (first.comp second).mapSyntacticHom arrow =
      second.mapSyntacticHom (first.mapSyntacticHom arrow) := by
  induction arrow using Quotient.inductionOn with
  | _ tuple =>
      apply (SyntacticCategory.mk_eq_iff thirdSystem _ _).mpr
      change BoundedTermTuple.Equivalent thirdSystem
        (BoundedTermTuple.translate (first.symbols.comp second.symbols) tuple)
        (BoundedTermTuple.translate second.symbols
          (BoundedTermTuple.translate first.symbols tuple))
      rw [BoundedTermTuple.translate_comp]
      exact (BoundedTermTuple.consequenceSetoid thirdSystem _ _).refl _

/-- The syntactic functor sends a displayed term arrow to the arrow of its
translated bounded term. -/
theorem syntacticFunctor_map_termArrow
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : Interpretation source target)
    {input : Nat} (term : Term.Bounded S input) :
    interpretation.syntacticFunctor.map
        (SyntacticCategory.termArrow source term) =
      SyntacticCategory.termArrow target
        ⟨term.1.translate interpretation.symbols,
          Term.variablesBelow_translate interpretation.symbols term.2⟩ := rfl

/-- The syntactic functor preserves the selected first projection. -/
theorem syntacticFunctor_map_firstProjection
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : Interpretation source target)
    (left right : Nat) :
    interpretation.syntacticFunctor.map
        (SyntacticCategory.firstProjection source left right) =
      SyntacticCategory.firstProjection target left right := by
  apply (SyntacticCategory.mk_eq_iff target _ _).mpr
  intro position
  exact EquationalConsequence.refl target _

/-- The syntactic functor preserves the selected second projection. -/
theorem syntacticFunctor_map_secondProjection
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : Interpretation source target)
    (left right : Nat) :
    interpretation.syntacticFunctor.map
        (SyntacticCategory.secondProjection source left right) =
      SyntacticCategory.secondProjection target left right := by
  apply (SyntacticCategory.mk_eq_iff target _ _).mpr
  intro position
  exact EquationalConsequence.refl target _

/-- The syntactic functor preserves the selected pairing operation. -/
theorem syntacticFunctor_map_pair
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : Interpretation source target)
    {input left right : Nat}
    (first : SyntacticCategory.object source input ⟶
      SyntacticCategory.object source left)
    (second : SyntacticCategory.object source input ⟶
      SyntacticCategory.object source right) :
    interpretation.syntacticFunctor.map
        (SyntacticCategory.pair source first second) =
      SyntacticCategory.pair target
        (interpretation.syntacticFunctor.map first)
        (interpretation.syntacticFunctor.map second) := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      apply (SyntacticCategory.mk_eq_iff target _ _).mpr
      rw [BoundedTermTuple.translate_pair]
      exact (BoundedTermTuple.consequenceSetoid target _ _).refl _

/-- An interpretation reflects generated consequence when no new equality is
created between translations of source terms. -/
def ConsequenceReflecting
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : Interpretation source target) : Prop :=
  ∀ equation,
    EquationalConsequence target
      (equation.translate interpretation.symbols) →
    EquationalConsequence source equation

/-- Consequence reflection makes the induced syntactic functor faithful. -/
theorem syntacticFunctor_faithful_of_consequenceReflecting
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : Interpretation source target)
    (reflecting : interpretation.ConsequenceReflecting) :
    interpretation.syntacticFunctor.Faithful := by
  constructor
  intro input output first second mappedEqual
  change interpretation.mapSyntacticHom first =
    interpretation.mapSyntacticHom second at mappedEqual
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      apply (SyntacticCategory.mk_eq_iff source _ _).mpr
      have translatedEquivalent : BoundedTermTuple.Equivalent target
          (BoundedTermTuple.translate interpretation.symbols first)
          (BoundedTermTuple.translate interpretation.symbols second) :=
        (SyntacticCategory.mk_eq_iff target _ _).mp mappedEqual
      intro position
      apply reflecting
      simpa only [Equation.translate, BoundedTermTuple.translate] using
        translatedEquivalent position

/-- Faithfulness of the induced syntactic functor reflects every generated
source equation.  The proof uses the computed finite bound of each term. -/
theorem consequenceReflecting_of_syntacticFunctor_faithful
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : Interpretation source target)
    (faithful : interpretation.syntacticFunctor.Faithful) :
    interpretation.ConsequenceReflecting := by
  rintro ⟨left, right⟩ translatedConsequence
  let bound := max left.variableBound right.variableBound
  let boundedLeft : Term.Bounded S bound :=
    ⟨left, (Term.variablesBelow_variableBound left).mono
      (Nat.le_max_left _ _)⟩
  let boundedRight : Term.Bounded S bound :=
    ⟨right, (Term.variablesBelow_variableBound right).mono
      (Nat.le_max_right _ _)⟩
  let translatedLeft : Term.Bounded T bound :=
    ⟨left.translate interpretation.symbols,
      Term.variablesBelow_translate interpretation.symbols boundedLeft.2⟩
  let translatedRight : Term.Bounded T bound :=
    ⟨right.translate interpretation.symbols,
      Term.variablesBelow_translate interpretation.symbols boundedRight.2⟩
  have targetArrowEquality :
      SyntacticCategory.termArrow target translatedLeft =
        SyntacticCategory.termArrow target translatedRight :=
    (SyntacticCategory.termArrow_eq_iff target _ _).mpr
      translatedConsequence
  have mappedEquality :
      interpretation.syntacticFunctor.map
          (SyntacticCategory.termArrow source boundedLeft) =
        interpretation.syntacticFunctor.map
          (SyntacticCategory.termArrow source boundedRight) := by
    rw [syntacticFunctor_map_termArrow,
      syntacticFunctor_map_termArrow]
    exact targetArrowEquality
  have sourceArrowEquality := faithful.map_injective mappedEquality
  exact (SyntacticCategory.termArrow_eq_iff source _ _).mp
    sourceArrowEquality

/-- Consequence reflection is exactly faithfulness of the induced
finite-product syntactic functor. -/
theorem consequenceReflecting_iff_syntacticFunctor_faithful
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : Interpretation source target) :
    interpretation.ConsequenceReflecting ↔
      interpretation.syntacticFunctor.Faithful :=
  ⟨syntacticFunctor_faithful_of_consequenceReflecting interpretation,
    consequenceReflecting_of_syntacticFunctor_faithful interpretation⟩

end EquationSystem.Interpretation

end Mettapedia.UniversalAlgebra
