import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Form
import Mettapedia.GSLT.LanguageDef.BagNormalForm
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ParallelBag

/-!
# The laws of restriction, over any calculus

A calculus with restriction declares three laws over its restriction constructor `ν`, besides the laws of its
parallel bag:

- `(νx) 0 = 0` (`restrictionNilOf`);
- `(νx)(νy) P = (νy)(νx) P`, the body taking the two names in the other order (`restrictionExchangeOf`);
- `{(νx) P | rest} = (νx) {P | rest}`, the rest not using `x` (`scopeExtrusionOf`).

`BlockSignature` says what the restriction-block theory reads of a language: a bare parallel bag over its process
sort with the block's unit, a restriction binding one name over a process, constructors taking terms of a sort or
abstractions of one sort over a bound name of another, and these laws among its declared laws. Soundness needs no
more, so it holds for a calculus that declares further laws, as one with replication does. `BlockLanguage` adds
that these laws are exactly the declared ones, which completeness needs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.BagNormalForm (BareBagPresentation)
open Mettapedia.GSLT.LanguageDef.WellSorted (parameterType? UsesBareCollection)

/-- `(νx) 0 = 0` -/
def restrictionNilOf (block : Block) : Equation where
  name := "RestrictionNil"
  typeContext := []
  premises := []
  left := .apply block.restrict [.lambda none (.apply block.unit [])]
  right := .apply block.unit []

/-- `(νx)(νy) P = (νy)(νx) P` -/
def restrictionExchangeOf (block : Block) : Equation where
  name := "RestrictionExchange"
  typeContext := [("P", .base block.proc)]
  premises := []
  left := .apply block.restrict [.lambda none (.apply block.restrict [.lambda none (.fvar "P")])]
  right := .apply block.restrict [.lambda none (.apply block.restrict [.lambda none (.fvar "P")])]
  bindings := some
    { dependencies := [("P", [.base block.name, .base block.name])]
      occurrences :=
        [{ name := "P", site := .left, path := [0, 0, 0, 0], arguments := [.bvar 0, .bvar 1] },
         { name := "P", site := .right, path := [0, 0, 0, 0], arguments := [.bvar 1, .bvar 0] }] }

/-- `{(νx) P | rest} = (νx) {P | rest}`, the rest not using `x` -/
def scopeExtrusionOf (block : Block) : Equation where
  name := "ScopeExtrusion"
  typeContext := [("P", .base block.proc), ("rest", .collection .hashBag (.base block.proc))]
  premises := []
  left := .collection .hashBag [.apply block.restrict [.lambda none (.fvar "P")]] (some "rest")
  right := .apply block.restrict [.lambda none (.collection .hashBag [.fvar "P"] (some "rest"))]
  bindings := some
    { dependencies := [("P", [.base block.name]), ("rest", [])]
      occurrences :=
        [{ name := "P", site := .left, path := [0, 0, 0], arguments := [.bvar 0] },
         { name := "rest", site := .left, path := [1], arguments := [] },
         { name := "P", site := .right, path := [0, 0, 0], arguments := [.bvar 0] },
         { name := "rest", site := .right, path := [0, 0, 1], arguments := [] }] }

/-- `m{} = (νx) 0`: an empty named multiset is inaction, as CCS's empty sum is, with `(νx) 0 = 0`. Stated over
the restriction, the law is read by the scope-aware matcher, which relates closed collections only. -/
def emptyUnitOf (block : Block) (label : String) : Equation where
  name := "EmptyUnit"
  typeContext := []
  premises := []
  left := .apply label [.collection .hashBag [] none]
  right := .apply block.restrict [.lambda none (.apply block.unit [])]
  bindings := some { dependencies := [], occurrences := [] }

/-- The laws of a calculus with restriction, in the order it declares them: those of restriction, then the empty
instances of its named multisets. -/
def blockLaws (block : Block) : List Equation :=
  [restrictionNilOf block, restrictionExchangeOf block, scopeExtrusionOf block] ++
    block.emptyUnits.map (emptyUnitOf block)

/-- **The signature the restriction-block theory reads**: a bare parallel bag over the process sort with the block's
unit, a restriction binding one name over a process, constructors taking terms of a sort or abstractions of one sort
over a bound name of another, and the laws of restriction and of the empty named multisets among the declared laws.
A calculus may declare further laws, as a calculus with replication does. -/
class BlockSignature (language : LanguageDef) (block : Block) : Prop where
  /-- Its parallel composition is a bare bag over the process sort, with the block's unit, beside its named
  multisets. -/
  bag : ∃ bag, ParallelBag language bag block.unit block.multisets ∧ bag.category = block.proc
  /-- The laws of restriction and of its empty named multisets are declared. -/
  lawsDeclared : ∀ law ∈ blockLaws block, law ∈ language.equations
  /-- The restriction is declared. -/
  restrictAuthored : ∃ rule ∈ language.terms, rule.label = block.restrict
  /-- A restriction binds a name over a process, and is a process. -/
  restrictShape : ∀ rule ∈ language.terms, rule.label = block.restrict → rule.category = block.proc ∧
    ∃ body, rule.params = [.abstraction body (.arrow (.base block.name) (.base block.proc))]
  /-- The unit is a process. -/
  unitShape : ∀ rule ∈ language.terms, rule.label = block.unit → rule.category = block.proc
  /-- A constructor named as a multiset is a named multiset operator. -/
  multisetShape : ∀ rule ∈ language.terms, rule.label ∈ block.multisets → NamedMultiset rule block.proc
  /-- A multiset whose empty instance is the unit is named as a multiset, and makes processes. -/
  emptyUnitShape : ∀ label ∈ block.emptyUnits, label ∈ block.multisets ∧
    ∀ rule ∈ language.terms, rule.label = label → rule.category = block.proc
  /-- A multiset whose empty instance is the unit is declared. -/
  emptyUnitAuthored : ∀ label ∈ block.emptyUnits, ∃ rule ∈ language.terms, rule.label = label
  /-- Each constructor has its own label. -/
  labelsUnique : (language.terms.map GrammarRule.label).Nodup
  /-- Every other constructor takes terms of a sort, or abstractions of one sort over a bound variable of another. -/
  params : ∀ rule ∈ language.terms, ¬ UsesBareCollection rule → rule.label ∉ block.multisets →
    ∀ parameter ∈ rule.params,
      (∃ sort, parameterType? parameter = some (.base sort)) ∨
        ∃ domain sort, parameterType? parameter = some (.arrow (.base domain) (.base sort))
  /-- A parameter of the type of abstractions is an abstraction. -/
  arrowsAbstract : ∀ rule ∈ language.terms, ¬ UsesBareCollection rule → rule.label ∉ block.multisets →
    ∀ parameter ∈ rule.params,
    ∀ domain sort, parameterType? parameter = some (.arrow (.base domain) (.base sort)) →
      ∃ binder body, parameter = .abstractionNamed binder body (.arrow (.base domain) (.base sort))

/-- **What the restriction-block theory needs of a language**: its signature, with exactly the laws of restriction
and of its empty named multisets declared, so that they generate its static theory. -/
class BlockLanguage (language : LanguageDef) (block : Block) : Prop extends BlockSignature language block where
  /-- Its declared laws are exactly those of restriction and of its empty named multisets. -/
  equations : language.equations = blockLaws block
  lawsDeclared := fun _ member => by rw [equations]; exact member

open Mettapedia.GSLT.LanguageDef.EquationSemantics (readsRaw)

/-- Restriction of inaction binds no metavariable, and is read raw. -/
theorem nil_raw (block : Block) : readsRaw (restrictionNilOf block) = true := rfl

/-- Exchange declares its bindings. -/
theorem exchange_raw (block : Block) : readsRaw (restrictionExchangeOf block) = false := rfl

/-- Extrusion declares its bindings. -/
theorem extrusion_raw (block : Block) : readsRaw (scopeExtrusionOf block) = false := rfl

/-- An empty multiset's law declares its bindings. -/
theorem emptyUnit_raw (block : Block) (label : String) : readsRaw (emptyUnitOf block label) = false := rfl

namespace BlockSignature

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext ElementsHaveType hasType_apply_inversion
  MatchesParameterRepresentation)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance AlgebraRule)

variable {language : LanguageDef} {block : Block}

theorem nil_mem (laws : BlockSignature language block) : List.Mem (restrictionNilOf block) language.equations :=
  laws.lawsDeclared _ (by simp [blockLaws])

theorem exchange_mem (laws : BlockSignature language block) :
    List.Mem (restrictionExchangeOf block) language.equations :=
  laws.lawsDeclared _ (by simp [blockLaws])

theorem extrusion_mem (laws : BlockSignature language block) : List.Mem (scopeExtrusionOf block) language.equations :=
  laws.lawsDeclared _ (by simp [blockLaws])

theorem emptyUnit_mem (laws : BlockSignature language block) {label : String} (listed : label ∈ block.emptyUnits) :
    List.Mem (emptyUnitOf block label) language.equations :=
  laws.lawsDeclared _ (List.mem_append_right _ (List.mem_map_of_mem listed))

/-- **The bag's laws**, at the process sort. -/
theorem algebra (laws : BlockSignature language block) :
    ∃ rule, AlgebraRule language rule .hashBag { flatten := true, unit := some block.unit } ∧
      rule.category = block.proc := by
  obtain ⟨bag, presented, category⟩ := laws.bag
  exact ⟨bag, presented.bagAlgebraRule, category⟩

/-- The unit is a process. -/
theorem unit_typed (laws : BlockSignature language block) {free : FreeTypeContext} {bound : List TypeExpr} :
    HasType language free bound (.apply block.unit []) (.base block.proc) := by
  obtain ⟨bag, presented, category⟩ := laws.bag
  obtain ⟨unitRule, member, labelIs, unitCategory, params⟩ := presented.unitAuthored
  have typed : HasType language free bound (.apply unitRule.label []) (.base unitRule.category) :=
    .constructor member (by
        simp only [UsesBareCollection, GrammarRule.bareParams, params]
        split <;> simp) (by rw [params]; exact .nil)
  rwa [labelIs, unitCategory, category] at typed

/-- **A restriction of a process is a process.** -/
theorem restrict_typed (laws : BlockSignature language block) {free : FreeTypeContext} {bound : List TypeExpr}
    {body : Pattern} (typed : HasType language free (.base block.name :: bound) body (.base block.proc)) :
    HasType language free bound (.apply block.restrict [.lambda none body]) (.base block.proc) := by
  obtain ⟨rule, member, labelIs⟩ := laws.restrictAuthored
  obtain ⟨category, parameterName, params⟩ := laws.restrictShape rule member labelIs
  have built : HasType language free bound (.apply rule.label [.lambda none body]) (.base rule.category) :=
    .constructor member (by
        simp only [UsesBareCollection, GrammarRule.bareParams, params]
        split <;> simp)
      (by rw [params]; exact .cons trivial rfl (.lambda typed) .nil)
  rwa [labelIs, category] at built

/-- **A typed restriction binds a name over a process, without a display name**, and is a process. -/
theorem restriction_typed (laws : BlockSignature language block) {free : FreeTypeContext} {bound : List TypeExpr}
    {binder : Option String} {body : Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.apply block.restrict [.lambda binder body]) type) :
    HasType language free (.base block.name :: bound) body (.base block.proc) ∧ type = .base block.proc ∧
      binder = none := by
  obtain ⟨rule, member, labelIs, -, typeIs, arguments⟩ := hasType_apply_inversion typed
  obtain ⟨category, parameterName, params⟩ := laws.restrictShape rule member labelIs.symm
  rw [params] at arguments
  cases arguments with
  | cons representation bodyType bodyTyped _ =>
    simp only [parameterType?, Option.some.injEq] at bodyType
    subst bodyType
    cases bodyTyped with
    | lambda inner =>
        refine ⟨inner, by rw [typeIs, category], ?_⟩
        cases binder with
        | none => rfl
        | some name => simp [MatchesParameterRepresentation] at representation

/-- A bag of processes is a process. -/
theorem bag_typed (laws : BlockSignature language block) {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {rest : Option String}
    (typed : ElementsHaveType language free bound elements (.base block.proc)) :
    HasType language free bound (.collection .hashBag elements rest) (.base block.proc) := by
  obtain ⟨bag, presented, category⟩ := laws.bag
  rw [← category]
  exact presented.bag_hasType (by rwa [category])

/-- **A typed bag is a process of processes.** -/
theorem bag_members (laws : BlockSignature language block) {free : FreeTypeContext} {bound : List TypeExpr}
    {kind : CollType} {elements : List Pattern} {rest : Option String} {sort : String}
    (typed : HasType language free bound (.collection kind elements rest) (.base sort)) :
    kind = .hashBag ∧ sort = block.proc ∧ ElementsHaveType language free bound elements (.base block.proc) := by
  obtain ⟨bag, presented, category⟩ := laws.bag
  obtain ⟨kindIs, typeIs, members⟩ := presented.bag_typing typed rfl
  rw [category] at typeIs members
  exact ⟨kindIs, by simpa using typeIs, members⟩

/-- The empty bag is the unit. -/
theorem emptyUnit (laws : BlockSignature language block) :
    DerivedInstance language (.collection .hashBag [] none) (.apply block.unit []) := by
  obtain ⟨rule, algebraRule, category⟩ := laws.algebra
  exact .emptyUnit algebraRule rfl ⟨fun _ => none, [], by
    rw [category]; exact laws.bag_typed (Mettapedia.GSLT.LanguageDef.BagNormalForm.elementsHaveType_iff.mpr (by simp))⟩

/-- A one-member bag is its member. -/
theorem singleton (laws : BlockSignature language block) {free : FreeTypeContext} {bound : List TypeExpr}
    {element : Pattern} (typed : HasType language free bound element (.base block.proc)) :
    DerivedInstance language (.collection .hashBag [element] none) element := by
  obtain ⟨rule, algebraRule, category⟩ := laws.algebra
  exact .singleton algebraRule rfl ⟨free, bound, by
    rw [category]; exact laws.bag_typed (Mettapedia.GSLT.LanguageDef.BagNormalForm.elementsHaveType_iff.mpr
      (by simpa using typed))⟩

/-- The unit inside a bag is dropped. -/
theorem unitElim (laws : BlockSignature language block) {free : FreeTypeContext} {bound : List TypeExpr}
    {pre post : List Pattern}
    (typed : HasType language free bound (.collection .hashBag (pre ++ .apply block.unit [] :: post) none)
      (.base block.proc)) :
    DerivedInstance language (.collection .hashBag (pre ++ .apply block.unit [] :: post) none)
      (.collection .hashBag (pre ++ post) none) := by
  obtain ⟨rule, algebraRule, category⟩ := laws.algebra
  exact .unitElim algebraRule rfl ⟨free, bound, by rw [category]; exact typed⟩

/-- A bag inside a bag is flattened. -/
theorem flatten (laws : BlockSignature language block) {free : FreeTypeContext} {bound : List TypeExpr}
    {pre inner post : List Pattern}
    (typed : HasType language free bound (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none)
      (.base block.proc)) :
    DerivedInstance language (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none)
      (.collection .hashBag (pre ++ inner ++ post) none) := by
  obtain ⟨rule, algebraRule, category⟩ := laws.algebra
  exact .flatten algebraRule rfl ⟨free, bound, by rw [category]; exact typed⟩

/-- **The bag is the only bare collection constructor**: a bag of processes, which is a process. -/
theorem bare_shape (laws : BlockSignature language block) {rule : GrammarRule} (member : rule ∈ language.terms)
    {parameterName : String} {kind : CollType} {element : TypeExpr}
    (shape : rule.bareParams = [.simple parameterName (.collection kind element)]) :
    kind = .hashBag ∧ element = .base block.proc ∧ rule.category = block.proc := by
  obtain ⟨bag, presented, category⟩ := laws.bag
  obtain ⟨rfl, kindIs, elementIs⟩ := presented.eq_bag_of_bareShape member shape
  exact ⟨kindIs, by rw [elementIs, category], category⟩


/-- **No set constructor.** -/
theorem no_set_rule (laws : BlockSignature language block) {rule : GrammarRule} (member : rule ∈ language.terms)
    {elements : List Pattern} : ¬ Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule .hashSet elements := by
  obtain ⟨bag, presented, -⟩ := laws.bag
  exact presented.no_set member

/-- **The only collection algebra is the bag, with the block's unit.** -/
theorem algebra_shape (laws : BlockSignature language block) {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} (algebraRule : AlgebraRule language rule kind algebra) :
    kind = .hashBag ∧ algebra.unit = some block.unit := by
  obtain ⟨bag, presented, -⟩ := laws.bag
  obtain ⟨-, kindIs, rfl⟩ := presented.algebra_rule algebraRule
  exact ⟨kindIs, rfl⟩

/-- **An empty multiset whose empty instance is the unit is a process.** -/
theorem emptyMultiset_typed (laws : BlockSignature language block) {label : String} (listed : label ∈ block.emptyUnits)
    {free : FreeTypeContext} {bound : List TypeExpr} :
    HasType language free bound (.apply label [.collection .hashBag [] none]) (.base block.proc) := by
  obtain ⟨rule, member, labelIs⟩ := laws.emptyUnitAuthored label listed
  obtain ⟨wrapped, -, parameterName, sort, params, -⟩ :=
    laws.multisetShape rule member (labelIs ▸ (laws.emptyUnitShape label listed).1)
  have notBare : ¬ UsesBareCollection rule := by
    rintro ⟨_, _, _, shape⟩
    rw [GrammarRule.bareParams_of_wrapped _ wrapped] at shape
    cases shape
  have built : HasType language free bound (.apply rule.label [.collection .hashBag [] none]) (.base rule.category) :=
    .constructor member notBare (by
      rw [params]
      exact .cons trivial rfl (.collection (Mettapedia.GSLT.LanguageDef.BagNormalForm.elementsHaveType_iff.mpr
        (by simp))) .nil)
  rwa [labelIs, (laws.emptyUnitShape label listed).2 rule member labelIs] at built

/-- **A label names one constructor.** -/
theorem rule_eq_of_label (laws : BlockSignature language block) {first second : GrammarRule}
    (firstMember : first ∈ language.terms) (secondMember : second ∈ language.terms) (same : first.label = second.label) :
    first = second :=
  List.inj_on_of_nodup_map laws.labelsUnique firstMember secondMember same

/-- **The restriction is no multiset whose empty instance is the unit.** -/
theorem restrict_not_emptyUnit (laws : BlockSignature language block) : block.restrict ∉ block.emptyUnits := by
  intro listed
  obtain ⟨rule, member, labelIs⟩ := laws.restrictAuthored
  obtain ⟨-, parameterName, params⟩ := laws.restrictShape rule member labelIs
  obtain ⟨name, sort, shape, -⟩ :=
    (laws.multisetShape rule member (labelIs ▸ (laws.emptyUnitShape _ listed).1)).shape
  rw [params] at shape
  simp at shape

/-- **A constructor named as a multiset is no restriction**, since a restriction takes an abstraction. -/
theorem restrict_not_multiset (laws : BlockSignature language block) {rule : GrammarRule}
    (member : rule ∈ language.terms) (labelIs : rule.label = block.restrict) : rule.label ∉ block.multisets := by
  intro listed
  obtain ⟨-, parameterName, params⟩ := laws.restrictShape rule member labelIs
  obtain ⟨name, sort, shape, -⟩ := (laws.multisetShape rule member listed).shape
  rw [params] at shape
  simp at shape

end BlockSignature

/-- **The laws of the blocks**: ν of inaction, exchange, extrusion and the empty named multisets. -/
theorem mem_blockLaws {block : Block} {equation : Equation} :
    equation ∈ blockLaws block ↔
      equation = restrictionNilOf block ∨ equation = restrictionExchangeOf block ∨ equation = scopeExtrusionOf block ∨
        ∃ label ∈ block.emptyUnits, equation = emptyUnitOf block label := by
  simp only [blockLaws, List.cons_append, List.nil_append, List.mem_cons, List.mem_map]
  constructor
  · rintro (rfl | rfl | rfl | ⟨label, listed, rfl⟩)
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr ⟨label, listed, rfl⟩))
  · rintro (rfl | rfl | rfl | ⟨label, listed, rfl⟩)
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr ⟨label, listed, rfl⟩))

namespace BlockLanguage

variable {language : LanguageDef} {block : Block}

/-- **The language's equations are the laws of restriction and of its empty named multisets.** -/
theorem equations_mem (laws : BlockLanguage language block) {equation : Equation}
    (member : List.Mem equation language.equations) :
    equation = restrictionNilOf block ∨ equation = restrictionExchangeOf block ∨ equation = scopeExtrusionOf block ∨
      ∃ label ∈ block.emptyUnits, equation = emptyUnitOf block label := by
  have inLaws : equation ∈ blockLaws block := laws.equations ▸ member
  simp only [blockLaws, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at inLaws
  rcases inLaws with rfl | rfl | rfl | ⟨label, listed, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr ⟨label, listed, rfl⟩))

end BlockLanguage

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
