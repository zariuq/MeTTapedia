import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ContextualLadderBridge

/-!
# Raw unityped syntax and declaration-aware typed erasure

The cumulative presentation already has one intrinsically scoped raw term
grammar and a simultaneous substitution action.  This module packages that
existing algebra as a unityped category with families.  It then proves that
the declaration-aware dependent syntax erases to the unityped structure by a
strict CwF morphism.

This is a concrete candidate instance of Prime's typed-over-raw architecture,
not a declaration that the cumulative grammar is the final raw Prime syntax.
In particular, it does not identify this grammar with the richer MeTTaIL
`Pattern` syntax.  That comparison requires its own conservative embedding.

The erasure has the following exact boundary:

* contexts retain their arity but forget the telescope entries;
* substitutions and terms retain their raw syntax exactly;
* every formed type maps to the unique external unityped index;
* terminal context and context comprehension are preserved on the nose.

Thus the unityped index is structural metadata of the formal interface.  It
is not an internal self-containing universe or a runtime type tag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace RawUnitypedErasure

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open SyntacticContextual

/-! ## The existing raw syntax is a unityped CwF -/

/-- The raw term and simultaneous-substitution algebra of a presentation,
packaged without adding a typing judgment or another term grammar.

`Sub Γ Δ` assigns a raw term in `Γ` to every variable of `Δ`, so the
orientation agrees with the contravariant reindexing convention of a CwF. -/
@[reducible] def rawUcwf (Head : Type) : Ucwf where
  Ctx := Nat
  Sub := fun source target => Sub Head target source
  idS := fun _ => ids
  compS := fun earlier later => subComp later earlier
  id_comp := by
    intro _ _ substitution
    exact subComp_ids_right substitution
  comp_id := by
    intro _ _ substitution
    exact subComp_ids_left substitution
  comp_assoc := by
    intro _ _ _ _ latest middle earliest
    exact subComp_assoc earliest middle latest
  Tm := Tm Head
  tmSub := fun term substitution => subst substitution term
  tmSub_id := subst_ids
  tmSub_comp := by
    intro _ _ _ term earlier later
    exact (subst_subComp later earlier term).symm
  ext := fun context => context + 1
  wk := projection
  vz := .var 0
  pair := fun substitution term => consSub term substitution
  wk_pair := by
    intro _ _ substitution term
    exact subComp_consSub_projection term substitution
  vz_pair := by
    intro _ _ substitution term
    exact subst_consSub_var_zero term substitution
  pair_eta := by
    intro _ _ substitution
    exact consSub_eta substitution

/-- The empty raw context is arity zero.  Its incoming substitution is the
unique function out of `Fin 0`. -/
@[reducible] def rawUcwfWithTerminal (Head : Type) : UcwfWithTerminal where
  toUcwf := rawUcwf Head
  empty := 0
  toEmpty := fun _ => Fin.elim0
  toEmpty_unique := by
    intro _ substitution
    funext index
    exact Fin.elim0 index

/-- The raw unityped syntax viewed through the two canonical ladder
inclusions as a dependent CwF with one constant external type index. -/
abbrev rawCwfWithTerminal (Head : Type) : CwfWithTerminal :=
  (rawUcwfWithTerminal Head).toScwfWithTerminal.toCwfWithTerminal

/-! ## Forgetting formed telescopes and typing evidence -/

/-- Erase a formed telescope to its raw arity. -/
def eraseContext {Head : Type} {rules : Rules Head}
    (context : FormedContext rules) : Nat :=
  context.arity

/-- The context functor retains the exact raw simultaneous substitution and
forgets only the formation evidence and telescope entries. -/
def erasureBaseFunctor {Head : Type} (rules : Rules Head) :
    (asCwf rules).base.Context ⥤
      (rawCwfWithTerminal Head).toCwf.base.Context where
  obj context := ⟨eraseContext context.val⟩
  map substitution := substitution.substitution
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Erasing a typed substitution is faithful on every hom-set: typing proofs
and telescope entries can be forgotten without identifying distinct raw
substitution arrays. -/
@[reducible] def erasureBaseFunctorFaithful {Head : Type} (rules : Rules Head) :
    (erasureBaseFunctor rules).Faithful where
  map_injective := by
    intro source target left right equality
    apply ContextHom.ext
    exact equality

/-- The family part of erasure sends every formed type to the unique
unityped index and every typed term to its retained raw term code. -/
def erasureFamilyMorphism {Head : Type} (rules : Rules Head) :
    CwfFamilyMorphism (asCwf rules) (rawCwfWithTerminal Head).toCwf where
  base := erasureBaseFunctor rules
  family :=
    { app := fun _ =>
        { onIndex := fun _ => PUnit.unit
          onFibre := fun _ term => term.code }
      naturality := by
        intro source target substitution
        apply IndexedFamily.Hom.ext
        · rfl
        · intro type term
          rfl }

/-- Declaration-aware dependent syntax erases to its raw unityped
substitution/binding structure by a strict CwF morphism.

This is stronger than a term-level commuting square: the selected terminal
context, context extension, weakening projection, and newest variable are all
preserved on the nose. -/
def strictErasure {Head : Type} (rules : Rules Head) :
    StrictCwfMorphism (asCwfWithTerminal rules) (rawCwfWithTerminal Head) where
  toFamilyMorphism := erasureFamilyMorphism rules
  empty_preserved := rfl
  extension_preserved := by
    intro _ _
    rfl
  projection_preserved := by
    intro _ _
    rfl
  variable_preserved := by
    intro _ _
    rfl

/-! ## Strongest true reflection and strict non-collapse -/

/-- Term erasure is injective inside one fixed typing fibre.  The erasure
forgets the derivation proof but not the raw term syntax. -/
theorem mapTerm_injective_at_fixed_type {Head : Type} (rules : Rules Head)
    {context : FormedContext rules} {type : TypeOver context} :
    Function.Injective
      (fun term : Term context type =>
        (erasureFamilyMorphism rules).mapTerm term) := by
  intro left right equalRawTerms
  exact Term.ext equalRawTerms

/-- Substitution before erasure is literally raw simultaneous substitution
after erasure. -/
theorem mapTerm_reindex {Head : Type} (rules : Rules Head)
    {source target : FormedContext rules} {type : TypeOver target}
    (term : Term target type) (substitution : ContextHom source target) :
    (erasureFamilyMorphism rules).mapTerm (term.reindex substitution) =
      (rawUcwf Head).tmSub
        ((erasureFamilyMorphism rules).mapTerm term)
        substitution.substitution :=
  rfl

/-- The unique target type index carries no object-language universe data. -/
theorem raw_type_index_unique {Head : Type} (context : Nat)
    (left right : (rawCwfWithTerminal Head).toCwf.Ty context) :
    left = right := by
  cases left
  cases right
  rfl

namespace TowerCanary

abbrev empty : FormedContext Tower.rules :=
  SyntacticContextual.TowerExamples.empty

/-- `U₀` as a formed type over the empty telescope. -/
def universeZeroType : TypeOver empty where
  code := sortTm Tower.zero
  level := .sort (.succ Tower.zero)
  isUniverse := .sort (.succ Tower.zero)
  formed := .headType (.sort Tower.zero)

/-- `U₀` and `U₁` are genuinely different formed type objects before
erasure. -/
theorem universeZeroType_ne_universeOne :
    universeZeroType ≠ SyntacticContextual.TowerExamples.universeOne := by
  intro equality
  have equalCodes := congrArg TypeOver.code equality
  have equalHeads :
      Tower.Head.sort Tower.zero = Tower.Head.sort (.succ Tower.zero) :=
    Tm.head.inj equalCodes
  have equalLevels : Tower.zero = .succ Tower.zero :=
    Tower.Head.sort.inj equalHeads
  change LevelExpr.const 0 = LevelExpr.succ (LevelExpr.const 0) at equalLevels
  cases equalLevels

/-- Negative control: the type action of raw erasure is not injective.  It
forgets the distinction between two genuinely different universe types. -/
theorem strictErasure_type_map_not_injective :
    ¬ Function.Injective
      (fun type : TypeOver empty =>
        (erasureFamilyMorphism Tower.rules).mapType type) := by
  intro injective
  exact universeZeroType_ne_universeOne
    (injective (by rfl))

/-- Positive control: despite type collapse, two distinct raw terms in a
fixed type fibre cannot be identified by the erasure. -/
theorem universe_terms_reflect_raw_equality
    (left right : Term empty SyntacticContextual.TowerExamples.universeOne)
    (equalErasures :
      (erasureFamilyMorphism Tower.rules).mapTerm left =
        (erasureFamilyMorphism Tower.rules).mapTerm right) :
    left = right :=
  mapTerm_injective_at_fixed_type Tower.rules equalErasures

end TowerCanary

#print axioms rawUcwf
#print axioms rawUcwfWithTerminal
#print axioms erasureBaseFunctorFaithful
#print axioms erasureFamilyMorphism
#print axioms strictErasure
#print axioms mapTerm_injective_at_fixed_type
#print axioms mapTerm_reindex
#print axioms raw_type_index_unique
#print axioms TowerCanary.universeZeroType_ne_universeOne
#print axioms TowerCanary.strictErasure_type_map_not_injective
#print axioms TowerCanary.universe_terms_reflect_raw_equality

end RawUnitypedErasure
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
