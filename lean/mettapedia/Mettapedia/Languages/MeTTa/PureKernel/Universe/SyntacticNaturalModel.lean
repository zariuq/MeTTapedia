import Mettapedia.GSLT.Core.LooseRelationCompanions
import Mettapedia.Languages.MeTTa.PureKernel.Universe.SyntacticContextualCategory

/-!
# The declaration-aware syntactic natural model

The declaration-aware presentation already supplies the strict substitution
and comprehension operations of a category with families.  This module states
their representability theorem directly, before choosing any quotient of
terms by conversion.

For a formed type `A` over `Gamma`, a generalized element over `Delta` is a
substitution `sigma : Delta -> Gamma` together with a term of `A[sigma]`.
Pairing gives an exact equivalence between those generalized elements and
substitutions `Delta -> Gamma.A`.  This is the Yoneda form of the
representable-natural-transformation characterization of a natural model.

An iterated `ComprehensionSpine` is deliberately proof relevant.  Its index is
the already-existing `FormedContext`, so it is not a second context calculus;
it records how that context was natively constructed.  In particular, it
retains the universe level selected at each extension even when the raw
telescope does not.  Variables are then generated only by the newest-variable
and weakening constructions.  Their ordinary de Bruijn lookup typings are
theorems, not side conditions.

Dependent products are added in a later module.  Raw syntax satisfies beta by
Prime conversion evidence rather than Lean equality, so it would be incorrect
to claim an ordinary extensional CwF at this layer.

The representability formulation follows the categories-with-families and
natural-model presentations of Dybjer and Awodey.  The retained construction
fibre is also the form needed by the proof-relevant route equipment: the tight
pairing map has a companion, while no quotient of construction witnesses is
imposed here.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
namespace SyntacticNaturalModel

open CategoryTheory
open SyntacticContextual

/-! ## Generalized elements and comprehension representability -/

/-- A generalized element of `type` at `source`: a base substitution together
with a term in the reindexed fibre. -/
structure GeneralizedElement {rules : Rules Head}
    (source target : FormedContext rules) (type : TypeOver target) where
  base : source ⟶ target
  term : Term source (type.reindex base)

/-- Generalized elements are determined by their base substitution and the
retained raw code of their term.  Typing derivations remain attached but live
in `Prop`, so no proof-irrelevance assumption is added by this extensionality
principle. -/
@[ext] theorem GeneralizedElement.ext {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    {left right : GeneralizedElement source target type}
    (equalBases : left.base = right.base)
    (equalCodes : left.term.code = right.term.code) :
    left = right := by
  cases left with
  | mk leftBase leftTerm =>
      cases right with
      | mk rightBase rightTerm =>
          dsimp at equalBases equalCodes
          cases equalBases
          have equalTerms : leftTerm = rightTerm := Term.ext equalCodes
          cases equalTerms
          rfl

/-- Pair a generalized element into the corresponding context extension. -/
def toComprehension {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (element : GeneralizedElement source target type) :
    source ⟶ extendContext target type :=
  extendHom element.base element.term

/-- Read an arrow into a context extension as its projected base substitution
and newest term. -/
def fromComprehension {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (morphism : source ⟶ extendContext target type) :
    GeneralizedElement source target type where
  base := morphism ≫ projectionHom target type
  term := pulledNewest morphism

/-- Reading a paired generalized element recovers both its base substitution
and its exact term code. -/
theorem fromComprehension_toComprehension {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (element : GeneralizedElement source target type) :
    fromComprehension (toComprehension element) = element := by
  apply GeneralizedElement.ext
  · exact extendHom_projection element.base element.term
  · simp only [fromComprehension, toComprehension, pulledNewest,
      Term.cast_code, Term.reindex, extendHom, newestVariable,
      Presentation.subst]
    rw [show newestIndex target type = (0 : Fin (target.arity + 1)) by
      apply Fin.ext
      rfl]
    exact consSub_zero element.term.code element.base.substitution

/-- Pairing the projected base and newest term recovers the original arrow. -/
theorem toComprehension_fromComprehension {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (morphism : source ⟶ extendContext target type) :
    toComprehension (fromComprehension morphism) = morphism :=
  extendHom_eta morphism

/-- Context comprehension represents the family of generalized elements.
This is the pointwise Yoneda form of the natural-model pullback square. -/
def comprehensionEquiv {rules : Rules Head}
    (source target : FormedContext rules) (type : TypeOver target) :
    GeneralizedElement source target type ≃
      (source ⟶ extendContext target type) where
  toFun := toComprehension
  invFun := fromComprehension
  left_inv := fromComprehension_toComprehension
  right_inv := toComprehension_fromComprehension

/-! ## Naturality in the generalized context -/

/-- Reindex a generalized element by precomposition. -/
def GeneralizedElement.precompose {rules : Rules Head}
    {first source target : FormedContext rules} {type : TypeOver target}
    (element : GeneralizedElement source target type)
    (earlier : first ⟶ source) : GeneralizedElement first target type where
  base := earlier ≫ element.base
  term := Term.cast
    (TypeOver.reindex_comp type earlier element.base).symm
    (element.term.reindex earlier)

/-- Pairing is natural in the generalized context.  The proof is exactly the
existing substitution-composition law for context extension. -/
theorem toComprehension_precompose {rules : Rules Head}
    {first source target : FormedContext rules} {type : TypeOver target}
    (element : GeneralizedElement source target type)
    (earlier : first ⟶ source) :
    earlier ≫ toComprehension element =
      toComprehension (element.precompose earlier) := by
  apply ContextHom.ext
  simp only [toComprehension, GeneralizedElement.precompose, extendHom,
    Term.cast_code]
  change
    subComp earlier.substitution
        (consSub element.term.code element.base.substitution) =
      consSub (subst earlier.substitution element.term.code)
        (subComp earlier.substitution element.base.substitution)
  exact subComp_consSub earlier.substitution element.term.code
    element.base.substitution

/-! ## The represented route into comprehension -/

/-- The proof-relevant loose graph of context pairing. -/
abbrev ComprehensionRoute {rules : Rules Head}
    (source target : FormedContext rules) (type : TypeOver target) :=
  Mettapedia.GSLT.LooseRelationEquipment.companion
    (toComprehension : GeneralizedElement source target type →
      (source ⟶ extendContext target type))

/-- Context pairing is a represented GSLT-IL route.  Direct construction and
its loose relational graph therefore agree exactly, including the equality
witness fibre selected by the equipment. -/
def comprehensionRepresentation {rules : Rules Head}
    (source target : FormedContext rules) (type : TypeOver target) :
    Mettapedia.GSLT.LooseRelationEquipment.Representation
      (ComprehensionRoute source target type) :=
  Mettapedia.GSLT.LooseRelationEquipment.Representation.companionSelf _

/-! ## Iterated comprehension as retained construction data -/

/-- Evidence that a formed telescope was constructed by iterated native
context comprehension.  The `FormedContext` index is the erasure; constructor
arguments retain the formation level and derivation chosen at every step. -/
inductive ComprehensionSpine {rules : Rules Head} :
    FormedContext rules → Type where
  | empty : ComprehensionSpine (emptyContext rules)
  | snoc {context : FormedContext rules} :
      ComprehensionSpine context →
      (type : TypeOver context) →
      ComprehensionSpine (extendContext context type)

/-- A variable in a comprehension spine.  Its formed type is an index of the
constructor: an ill-typed variable is not a value of this family. -/
inductive Variable {rules : Rules Head} :
    {context : FormedContext rules} →
    ComprehensionSpine context → TypeOver context → Type where
  | newest {context : FormedContext rules}
      (spine : ComprehensionSpine context) (type : TypeOver context) :
      Variable (.snoc spine type)
        (type.reindex (projectionHom context type))
  | weaken {context : FormedContext rules}
      {spine : ComprehensionSpine context} {priorType : TypeOver context}
      (prior : Variable spine priorType) (type : TypeOver context) :
      Variable (.snoc spine type)
        (priorType.reindex (projectionHom context type))

namespace Variable

/-- Every intrinsic variable constructs a typed term directly. -/
def term {rules : Rules Head} :
    {context : FormedContext rules} →
    {spine : ComprehensionSpine context} → {type : TypeOver context} →
    Variable spine type → Term context type
  | _, _, _, .newest spine type => newestVariable _ type
  | _, _, _, .weaken prior type =>
      prior.term.reindex (projectionHom _ type)

/-- The ordinary de Bruijn index obtained by erasing a native variable. -/
def index {rules : Rules Head} :
    {context : FormedContext rules} →
    {spine : ComprehensionSpine context} → {type : TypeOver context} →
    Variable spine type → Fin context.arity
  | _, _, _, .newest (context := context) _ type =>
      newestIndex context type
  | _, _, _, .weaken prior _ => prior.index.succ

/-- Erasure of a native variable is exactly the corresponding raw de Bruijn
term. -/
theorem term_code {rules : Rules Head}
    {context : FormedContext rules} {spine : ComprehensionSpine context}
    {type : TypeOver context} (nativeVar : Variable spine type) :
    nativeVar.term.code = .var nativeVar.index := by
  induction nativeVar with
  | newest => rfl
  | weaken prior type ih =>
      change subst projection prior.term.code = .var prior.index.succ
      rw [subst_projection, ih]
      rfl

/-- The type index carried by a native variable agrees exactly with ordinary
context lookup at its erased de Bruijn index.  Lookup is therefore a theorem
about intrinsic construction, not a post-hoc premise of variable admission. -/
theorem type_code_eq_lookup {rules : Rules Head}
    {context : FormedContext rules} {spine : ComprehensionSpine context}
    {type : TypeOver context} (nativeVar : Variable spine type) :
    type.code = Ctx.lookup context.context nativeVar.index := by
  induction nativeVar with
  | newest spine type =>
      change subst projection type.code = rename wk type.code
      exact subst_projection type.code
  | weaken prior type ih =>
      change subst projection _ = rename wk (Ctx.lookup _ prior.index)
      rw [subst_projection, ih]

/-- The intrinsic variable carries precisely the standard declarative
variable judgment after erasure. -/
theorem term_has_lookup_type {rules : Rules Head}
    {context : FormedContext rules} {spine : ComprehensionSpine context}
    {type : TypeOver context} (nativeVar : Variable spine type) :
    HasType rules context.context nativeVar.term.code
      (Ctx.lookup context.context nativeVar.index) := by
  simpa only [nativeVar.type_code_eq_lookup] using nativeVar.term.typed

end Variable

/-! ## Positive and negative controls -/

namespace TowerExamples

open SyntacticContextual.TowerExamples

/-- The empty Tower context has its canonical native construction spine. -/
def emptySpine : ComprehensionSpine empty := .empty

/-- Extending by `U₁` constructs its newest variable without any lookup or
typing side condition. -/
def universeOneVariable :
    Variable (.snoc emptySpine universeOne)
      (universeOne.reindex (projectionHom empty universeOne)) :=
  .newest emptySpine universeOne

@[simp] theorem universeOneVariable_code :
    universeOneVariable.term.code = (.var 0 : Tower.Tm 1) :=
  universeOneVariable.term_code

/-- Negative control: an empty comprehension spine has no variable at any
formed type.  This is constructor-level impossibility, not failed lookup. -/
theorem no_variable_in_empty (type : TypeOver empty) :
    IsEmpty (Variable emptySpine type) := by
  constructor
  intro nativeVar
  cases nativeVar

end TowerExamples

/-! ## Axiom audit -/

#print axioms comprehensionEquiv
#print axioms toComprehension_precompose
#print axioms comprehensionRepresentation
#print axioms Variable.term_code
#print axioms Variable.type_code_eq_lookup
#print axioms Variable.term_has_lookup_type
#print axioms TowerExamples.no_variable_in_empty

end SyntacticNaturalModel
end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
