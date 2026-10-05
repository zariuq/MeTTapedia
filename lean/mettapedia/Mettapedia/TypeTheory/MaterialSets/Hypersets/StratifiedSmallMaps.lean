import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedSubtypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.StratifiedCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.LocallyPresentedCoalgebras
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseSizeObstructions

/-!
# Constructed small fibres and stratified collection

A uniform fibre presentation supplies its small carrier and both directions
of its comparison with the actual fibre. Reindexing, composition and dependent
products construct new carriers from that data. Pointwise existential
smallness is not used to choose a uniform presentation.

Presented material types also construct the complete relation-witness object,
including its decoder and its covering projection. Arbitrary larger witness
types give a quasi-pullback at their displayed bound. This is different from
the fixed-bound covering axiom for algebraic set theory.

The comparison is with van den Berg and De Marchi, Models of Non-Well-Founded
Sets via an Indexed Final Coalgebra Theorem, sections 3.2 and 4. The results
below establish concrete fibre, collection and decoration constructions;
they do not assert all small-map axioms for a Heyting pretopos or a fixed-level
CZF or IZF model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.StratifiedSmallMaps

open AccessiblePointedGraph

universe u v w z

abbrev Fibre {E : Type v} {B : Type w} (map : E → B) (base : B) :=
  {element : E // map element = base}

/-- Uniform presentation data, rather than a choice from smallness proofs. -/
structure PresentedMap {E : Type v} {B : Type w} (map : E → B) where
  Code : B → Type u
  fibreEquiv : (base : B) → Code base ≃ Fibre map base

namespace PresentedMap

variable {E : Type v} {B : Type w} {map : E → B}
variable (presentation : PresentedMap.{u} map)

def element (base : B) (code : presentation.Code base) : E :=
  (presentation.fibreEquiv base code).val

theorem element_fibre (base : B) (code : presentation.Code base) :
    map (presentation.element base code) = base :=
  (presentation.fibreEquiv base code).property

/-- The whole domain is reconstructed with its actual projection. -/
def totalEquiv : (Σ base, presentation.Code base) ≃ E :=
  ({ toFun := fun point => ⟨point.1, presentation.fibreEquiv point.1 point.2⟩
     invFun := fun point => ⟨point.1, (presentation.fibreEquiv point.1).symm point.2⟩
     left_inv := fun point => congrArg (Sigma.mk point.1)
       ((presentation.fibreEquiv point.1).symm_apply_apply point.2)
     right_inv := fun point => congrArg (Sigma.mk point.1)
       ((presentation.fibreEquiv point.1).apply_symm_apply point.2) } :
    Sigma presentation.Code ≃ Σ base, Fibre map base).trans {
      toFun := fun point => point.2.val
      invFun := fun element => ⟨map element, ⟨element, rfl⟩⟩
      left_inv := by
        rintro ⟨base, element, same⟩
        cases same
        rfl
      right_inv := fun _ => rfl }

theorem totalEquiv_projection (point : Sigma presentation.Code) :
    map (presentation.totalEquiv point) = point.1 :=
  presentation.element_fibre point.1 point.2

/-- The pullback is an actual pair type with its commuting equation. -/
abbrev Pullback {A : Type z} (restriction : A → B) :=
  {point : A × E // map point.2 = restriction point.1}

def pullback {A : Type z} (restriction : A → B) :
    PresentedMap.{u} (fun point : Pullback (map := map) restriction => point.val.1) where
  Code base := presentation.Code (restriction base)
  fibreEquiv base := {
    toFun := fun code => ⟨⟨⟨base, presentation.element (restriction base) code⟩,
      presentation.element_fibre (restriction base) code⟩, rfl⟩
    invFun := fun point => (presentation.fibreEquiv (restriction base)).symm
      ⟨point.val.val.2, point.val.property.trans (congrArg restriction point.property)⟩
    left_inv code := (presentation.fibreEquiv (restriction base)).symm_apply_apply code
    right_inv point := by
      rcases point with ⟨⟨⟨other, element⟩, same⟩, baseSame⟩
      cases baseSame
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun value => (other, value.val))
        ((presentation.fibreEquiv (restriction other)).apply_symm_apply ⟨element, same⟩) }

end PresentedMap

/-- The projection of an actual small family has its supplied fibres. -/
def familyProjection {B : Type v} (family : B → Type u) :
    PresentedMap.{u} (fun point : Sigma family => point.1) where
  Code := family
  fibreEquiv base := {
    toFun := fun code => ⟨⟨base, code⟩, rfl⟩
    invFun := fun point => point.property ▸ point.val.2
    left_inv _ := rfl
    right_inv point := by
      rcases point with ⟨⟨other, code⟩, same⟩
      cases same
      rfl }

private def sigmaFibreEquiv {A : Type v} {first : A → Type w} {second : A → Type z}
    (equivalence : ∀ a, first a ≃ second a) : Sigma first ≃ Sigma second where
  toFun point := ⟨point.1, equivalence point.1 point.2⟩
  invFun point := ⟨point.1, (equivalence point.1).symm point.2⟩
  left_inv point := congrArg (Sigma.mk point.1) ((equivalence point.1).symm_apply_apply point.2)
  right_inv point := congrArg (Sigma.mk point.1) ((equivalence point.1).apply_symm_apply point.2)

private def sigmaBaseEquiv {A : Type v} {B : Type w} (equivalence : A ≃ B)
    (family : B → Type z) : (Σ a, family (equivalence a)) ≃ Sigma family where
  toFun point := ⟨equivalence point.1, point.2⟩
  invFun point := ⟨equivalence.symm point.1,
    cast (congrArg family (equivalence.apply_symm_apply point.1).symm) point.2⟩
  left_inv point := Sigma.ext (equivalence.symm_apply_apply point.1) (cast_heq _ _)
  right_inv point := Sigma.ext (equivalence.apply_symm_apply point.1) (cast_heq _ _)

private def compositionFibreEquiv {E : Type v} {B : Type w} {A : Type z}
    (first : E → B) (second : B → A) (base : A) :
    (Σ middle : Fibre second base, Fibre first middle.val) ≃ Fibre (second ∘ first) base where
  toFun point := ⟨point.2.val, (congrArg second point.2.property).trans point.1.property⟩
  invFun point := ⟨⟨first point.val, point.property⟩, ⟨point.val, rfl⟩⟩
  left_inv point := by
    rcases point with ⟨⟨middle, outer⟩, ⟨element, inner⟩⟩
    cases inner
    rfl
  right_inv _ := rfl

namespace PresentedMap

variable {E : Type v} {B : Type w} {A : Type z} {first : E → B} {second : B → A}

/-- Composition constructs dependent sums of the two authored small carriers. -/
def compose (inner : PresentedMap.{u} first) (outer : PresentedMap.{u} second) :
    PresentedMap.{u} (second ∘ first) where
  Code base := Σ middle : outer.Code base, inner.Code (outer.element base middle)
  fibreEquiv base :=
    (sigmaFibreEquiv fun middle => inner.fibreEquiv (outer.element base middle)).trans
      ((sigmaBaseEquiv (outer.fibreEquiv base) (fun middle => Fibre first middle.val)).trans
        (compositionFibreEquiv first second base))

end PresentedMap

private def piBaseEquiv {A : Type v} {B : Type w} (equivalence : A ≃ B)
    (family : B → Type z) : ((a : A) → family (equivalence a)) ≃ ((b : B) → family b) where
  toFun term base := cast (congrArg family (equivalence.apply_symm_apply base))
    (term (equivalence.symm base))
  invFun term code := term (equivalence code)
  left_inv term := by
    funext code
    exact eq_of_heq ((cast_heq _ _).trans
      (congr_arg_heq term (equivalence.symm_apply_apply code)))
  right_inv term := by
    funext base
    exact eq_of_heq ((cast_heq _ _).trans
      (congr_arg_heq term (equivalence.apply_symm_apply base)))

namespace PresentedMap

variable {E : Type v} {B : Type w} {W : Type z} {first : E → B} {second : W → E}
variable (domain : PresentedMap.{u} first) (codomain : PresentedMap.{u} second)

/-- All dependent functions on an actual fibre, including the codomain's
actual equation at every argument. -/
abbrev ProductFibre (base : B) := (element : Fibre first base) → Fibre second element.val

def productFibreEquiv (base : B) :
    ((code : domain.Code base) → codomain.Code (domain.element base code)) ≃
      ProductFibre (first := first) (second := second) base :=
  (Equiv.piCongrRight fun code => codomain.fibreEquiv (domain.element base code)).trans
    (piBaseEquiv (domain.fibreEquiv base) (fun element => Fibre second element.val))

/-- The dependent product's small carrier is constructed by Pi, rather than
deduced from a family of existential smallness statements. -/
def product : PresentedMap.{u}
    (fun point : Σ base : B, ProductFibre (first := first) (second := second) base => point.1) where
  Code base := (code : domain.Code base) → codomain.Code (domain.element base code)
  fibreEquiv base := (productFibreEquiv domain codomain base).trans
    ((familyProjection (ProductFibre (first := first) (second := second))).fibreEquiv base)

/-- Application retains the actual result and its authored fibre equation. -/
theorem product_application (base : B)
    (function : (code : domain.Code base) → codomain.Code (domain.element base code))
    (argument : domain.Code base) :
    productFibreEquiv domain codomain base function (domain.fibreEquiv base argument) =
      codomain.fibreEquiv (domain.element base argument) (function argument) := by
  change piBaseEquiv (domain.fibreEquiv base) (fun element => Fibre second element.val)
    (fun code => codomain.fibreEquiv (domain.element base code) (function code))
      (domain.fibreEquiv base argument) = _
  exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq
    (fun code => codomain.fibreEquiv (domain.element base code) (function code))
      ((domain.fibreEquiv base).symm_apply_apply argument)))

end PresentedMap

namespace Classification

def universeProjection (point : Σ carrier : Type u, carrier) : Type u := point.1

/-- The generic projection lives one level above its supplied fibre codes. -/
def universePresentation : PresentedMap.{u} universeProjection.{u} :=
  familyProjection (id : Type u → Type u)

private def familyPullbackEquiv {B : Type v} (family : B → Type u) :
    Sigma family ≃ PresentedMap.Pullback (map := universeProjection) family where
  toFun point := ⟨⟨point.1, ⟨family point.1, point.2⟩⟩, rfl⟩
  invFun point := ⟨point.val.1, cast point.property point.val.2.2⟩
  left_inv _ := rfl
  right_inv point := by
    rcases point with ⟨⟨base, carrier, code⟩, same⟩
    change carrier = family base at same
    cases same
    rfl

variable {E : Type v} {B : Type w} {map : E → B}
variable (presentation : PresentedMap.{u} map)

/-- Classification uses the actual supplied family. It is not a selector
obtained from pointwise existential smallness. -/
def equivalence : E ≃ PresentedMap.Pullback (map := universeProjection) presentation.Code :=
  presentation.totalEquiv.symm.trans (familyPullbackEquiv presentation.Code)

theorem projection (element : E) : (equivalence presentation element).val.1 = map element := by
  change (presentation.totalEquiv.symm element).1 = map element
  exact (presentation.totalEquiv_projection (presentation.totalEquiv.symm element)).symm.trans
    (congrArg map (presentation.totalEquiv.apply_symm_apply element))

end Classification

namespace MaterialRelations

variable {A : Type u} {B : A → Type u}
variable (domain : PresentedType A) (fibres : (a : A) → PresentedType (B a))
variable (relation : (a : A) → B a → Prop)

/-- The entire witness object has an actual graph and a member decoder. -/
def witnessModel : PresentedType (Σ a : A, {b : B a // relation a b}) :=
  PresentedType.sum domain (fun a => PresentedType.restrict (fibres a) (relation a))

theorem witnessModel_carrier : (witnessModel domain fibres relation).carrier =
    PresentedCollection.rows domain fibres relation := by
  apply HSet.ext
  intro value
  change value ∈ HSet.mk (PresentedType.sumGraph domain
    (fun a => PresentedType.restrict (fibres a) (relation a))) ↔ _
  rw [PresentedType.mem_sumGraph_iff, PresentedCollection.mem_rows]
  constructor
  · rintro ⟨⟨a, b, related⟩, same⟩
    exact ⟨a, b, related, same⟩
  · rintro ⟨a, b, related, same⟩
    exact ⟨⟨a, b, related⟩, same⟩

theorem witnessModel_value (witness : Σ a : A, {b : B a // relation a b}) :
    (witnessModel domain fibres relation).value witness =
      HSet.kpair (domain.value witness.1) ((fibres witness.1).value witness.2.val) :=
  PresentedType.sum_value _ _ witness

/-- Actual rows are equivalent to complete dependent relation witnesses. -/
def rowWitnessEquiv :
    {value : HSet.{u} // value ∈ PresentedCollection.rows domain fibres relation} ≃
      (Σ a : A, {b : B a // relation a b}) :=
  ({ toFun := fun member => ⟨member.val, (witnessModel_carrier domain fibres relation).symm ▸ member.property⟩
     invFun := fun member => ⟨member.val, (witnessModel_carrier domain fibres relation) ▸ member.property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
    {value : HSet.{u} // value ∈ PresentedCollection.rows domain fibres relation} ≃
      {value : HSet.{u} // value ∈ (witnessModel domain fibres relation).carrier}).trans
    (witnessModel domain fibres relation).decode

def projection (row : {value : HSet.{u} // value ∈ PresentedCollection.rows domain fibres relation}) : A :=
  (rowWitnessEquiv domain fibres relation row).1

def projectionPresentation : PresentedMap.{u} (projection domain fibres relation) where
  Code a := {b : B a // relation a b}
  fibreEquiv a := {
    toFun := fun b => ⟨(rowWitnessEquiv domain fibres relation).symm ⟨a, b⟩,
      congrArg Sigma.fst ((rowWitnessEquiv domain fibres relation).apply_symm_apply ⟨a, b⟩)⟩
    invFun := fun row =>
      cast (congrArg (fun index => {b : B index // relation index b}) row.property)
        (rowWitnessEquiv domain fibres relation row.val).2
    left_inv b := by
      change cast _ ((rowWitnessEquiv domain fibres relation
        ((rowWitnessEquiv domain fibres relation).symm ⟨a, b⟩)).2) = b
      exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq Sigma.snd
        ((rowWitnessEquiv domain fibres relation).apply_symm_apply ⟨a, b⟩)))
    right_inv row := by
      apply Subtype.ext
      apply (rowWitnessEquiv domain fibres relation).injective
      rw [(rowWitnessEquiv domain fibres relation).apply_symm_apply]
      exact Sigma.ext row.property.symm (cast_heq _ _ ) }

theorem projection_surjective (total : ∀ a, ∃ b, relation a b) :
    Function.Surjective (projection domain fibres relation) := by
  intro a
  obtain ⟨b, related⟩ := total a
  refine ⟨(rowWitnessEquiv domain fibres relation).symm ⟨a, b, related⟩, ?_⟩
  exact congrArg Sigma.fst ((rowWitnessEquiv domain fibres relation).apply_symm_apply ⟨a, b, related⟩)

theorem projection_total_iff : Function.Surjective (projection domain fibres relation) ↔
    ∀ a, ∃ b, relation a b := by
  constructor
  · intro surjective a
    obtain ⟨row, same⟩ := surjective a
    let witness := rowWitnessEquiv domain fibres relation row
    have index : witness.1 = a := same
    cases index
    exact ⟨witness.2.val, witness.2.property⟩
  · exact projection_surjective domain fibres relation

end MaterialRelations

namespace Covering

variable {E : Type v} {B : Type w} {Y : Type z} {map : E → B}
variable (presentation : PresentedMap.{u} map) (coverMap : Y → E)

/-- Every cover witness is retained, at the displayed witness universe. -/
def Witness (base : B) : Type (max u z) :=
  Σ code : presentation.Code base,
    {witness : Y // coverMap witness = presentation.element base code}

abbrev Object := Sigma (Witness presentation coverMap)

def toWitness (point : Object presentation coverMap) : Y := point.2.2.val

theorem square (point : Object presentation coverMap) :
    map (coverMap (toWitness presentation coverMap point)) = point.1 :=
  (congrArg map point.2.2.property).trans (presentation.element_fibre point.1 point.2.1)

/-- The left vertical map is presented at the witness bound. This bound may
be larger than that of the original right vertical map. -/
def projectionPresentation :
    PresentedMap.{max u z} (fun point : Object presentation coverMap => point.1) :=
  familyProjection (Witness presentation coverMap)

def comparison : Object presentation coverMap → PresentedMap.Pullback (map := map) (id : B → B) :=
  fun point => ⟨⟨point.1, coverMap (toWitness presentation coverMap point)⟩,
    square presentation coverMap point⟩

/-- Surjectivity is the quasi-pullback condition on the constructed square.
Cover witnesses are eliminated only while proving this proposition. -/
theorem comparison_surjective (cover : Function.Surjective coverMap) :
    Function.Surjective (comparison presentation coverMap) := by
  rintro ⟨⟨base, element⟩, same⟩
  obtain ⟨witness, covered⟩ := cover element
  let code := (presentation.fibreEquiv base).symm ⟨element, same⟩
  have codeValue : presentation.element base code = element :=
    congrArg Subtype.val ((presentation.fibreEquiv base).apply_symm_apply ⟨element, same⟩)
  refine ⟨⟨base, code, witness, covered.trans codeValue.symm⟩, ?_⟩
  exact Subtype.ext (congrArg (Prod.mk base) covered)

/-- When the witness type really has the original bound, the very same
construction is a same-bound covering square. -/
def sameBoundProjection {Y : Type u} (coverMap : Y → E) :
    PresentedMap.{u} (fun point : Object presentation coverMap => point.1) :=
  projectionPresentation presentation coverMap

end Covering

namespace Decoration

variable {E : Type v} {State : Type w} {source : E → State}
variable (presentation : PresentedMap.{u} source) (target : E → State)

/-- Actual authored events supply the positions of the small coalgebra. -/
def coalgebra : LocallyPresentedCoalgebras.Coalgebra.{u, w} State where
  Branch := presentation.Code
  next state code := target (presentation.element state code)

def transition (first second : State) : Prop :=
  ∃ event : E, source event = first ∧ target event = second

theorem transition_iff (first second : State) :
    LocallyPresentedCoalgebras.transition (coalgebra presentation target) first second ↔
      transition (source := source) target first second := by
  constructor
  · rintro ⟨code, same⟩
    exact ⟨presentation.element first code, presentation.element_fibre first code, same⟩
  · rintro ⟨event, available, same⟩
    refine ⟨(presentation.fibreEquiv first).symm ⟨event, available⟩, ?_⟩
    exact (congrArg target (congrArg Subtype.val
      ((presentation.fibreEquiv first).apply_symm_apply ⟨event, available⟩))).trans same

def value : State → HSet.{u} := LocallyPresentedCoalgebras.behaviour (coalgebra presentation target)

/-- The material value is constructed by finite branch paths. Every event
contributes its actual successor value; repeated events remain positions. -/
theorem mem_value_iff (state : State) (member : HSet.{u}) :
    member ∈ value presentation target state ↔
      ∃ event : E, source event = state ∧ value presentation target (target event) = member := by
  rw [value, LocallyPresentedCoalgebras.mem_behaviour]
  constructor
  · rintro ⟨code, same⟩
    exact ⟨presentation.element state code, presentation.element_fibre state code, same⟩
  · rintro ⟨event, available, same⟩
    refine ⟨(presentation.fibreEquiv state).symm ⟨event, available⟩, ?_⟩
    change value presentation target
      (target (presentation.element state ((presentation.fibreEquiv state).symm ⟨event, available⟩))) = member
    rw [show presentation.element state ((presentation.fibreEquiv state).symm ⟨event, available⟩) = event from
      congrArg Subtype.val ((presentation.fibreEquiv state).apply_symm_apply ⟨event, available⟩)]
    exact same

include presentation in
/-- The unique decoration has been constructed from the actual small event
fibres, independently of the size of the state type. -/
theorem existsUnique_value : ∃! decoration : State → HSet.{u},
    ∀ state member, member ∈ decoration state ↔
      ∃ event : E, source event = state ∧ decoration (target event) = member := by
  refine ⟨value presentation target, mem_value_iff presentation target, ?_⟩
  intro decoration lawful
  apply LocallyPresentedCoalgebras.IsDecoration.eq_behaviour
    (system := coalgebra presentation target)
  intro state member
  rw [lawful state member]
  constructor
  · rintro ⟨event, available, same⟩
    refine ⟨(presentation.fibreEquiv state).symm ⟨event, available⟩, ?_⟩
    exact (congrArg (fun element => decoration (target element))
      (congrArg Subtype.val ((presentation.fibreEquiv state).apply_symm_apply ⟨event, available⟩))).trans same
  · rintro ⟨code, same⟩
    exact ⟨presentation.element state code, presentation.element_fibre state code, same⟩

/-- Reading a root occurrence recovers its complete original event, not just
an erased proof that some transition occurred. -/
def occurrenceEventEquiv (state : State) :
    Occurrence (LocallyPresentedCoalgebras.graph (coalgebra presentation target) state) ≃
      Fibre source state :=
  (LocallyPresentedCoalgebras.occurrenceEquiv (coalgebra presentation target) state).trans
    (presentation.fibreEquiv state)

end Decoration

namespace MaterialRelations

variable {A : Type u} {B : A → Type u}
variable (domain : PresentedType A) (fibres : (a : A) → PresentedType (B a))
variable (relation : (a : A) → B a → Prop) (next : (a : A) → B a → A)

def target (row : {value : HSet.{u} // value ∈ PresentedCollection.rows domain fibres relation}) : A :=
  let witness := rowWitnessEquiv domain fibres relation row
  next witness.1 witness.2.val

theorem target_fibre_code (a : A) (b : {b : B a // relation a b}) :
    target domain fibres relation next
      ((projectionPresentation domain fibres relation).element a b) = next a b.val :=
  congrArg (fun witness : Σ a : A, {b : B a // relation a b} => next witness.1 witness.2.val)
    ((rowWitnessEquiv domain fibres relation).apply_symm_apply ⟨a, b⟩)

/-- Relation witnesses are genuine event positions; their material decoder
supplies the endpoint map to the independently constructed coalgebra. -/
def value : A → HSet.{u} :=
  Decoration.value (projectionPresentation domain fibres relation) (target domain fibres relation next)

theorem mem_value_iff (a : A) (member : HSet.{u}) :
    member ∈ value domain fibres relation next a ↔
      ∃ b : B a, relation a b ∧ value domain fibres relation next (next a b) = member := by
  change member ∈ LocallyPresentedCoalgebras.behaviour
    (Decoration.coalgebra (projectionPresentation domain fibres relation) (target domain fibres relation next)) a ↔ _
  rw [LocallyPresentedCoalgebras.mem_behaviour]
  constructor
  · rintro ⟨b, same⟩
    refine ⟨b.val, b.property, ?_⟩
    have endpoint := target_fibre_code domain fibres relation next a b
    exact (congrArg (value domain fibres relation next) endpoint).symm.trans same
  · rintro ⟨b, related, same⟩
    refine ⟨⟨b, related⟩, ?_⟩
    exact (congrArg (value domain fibres relation next)
      (target_fibre_code domain fibres relation next a ⟨b, related⟩)).trans same

end MaterialRelations

namespace FixedBound

variable {I : Type (u + 1)} (relation : I → HSet.{u} → Prop)

/-- Fixed-level strong collection is exactly the existence of a material
bound reaching at least one witness per argument. Separation removes every
extraneous member of that bound. It need not bound all possible witnesses. -/
theorem strong_collection_iff_bounded_witnesses :
    (∃ collected : HSet.{u},
      (∀ index, ∃ y, relation index y ∧ y ∈ collected) ∧
      (∀ y ∈ collected, ∃ index, relation index y)) ↔
    ∃ bound : HSet.{u}, ∀ index, ∃ y ∈ bound, relation index y := by
  constructor
  · rintro ⟨collected, covers, _⟩
    refine ⟨collected, fun index => ?_⟩
    obtain ⟨y, related, member⟩ := covers index
    exact ⟨y, member, related⟩
  · rintro ⟨bound, total⟩
    exact ⟨HSet.boundedCollection bound relation,
      HSet.strong_bounded_collection bound relation total⟩

/-- A small material witness cover is precisely such a bound. The graph
existence is eliminated into a proposition; no uniform graph is selected. -/
theorem bounded_witnesses_iff_small_cover :
    (∃ bound : HSet.{u}, ∀ index, ∃ y ∈ bound, relation index y) ↔
    ∃ graph : AccessiblePointedGraph.{u}, ∀ index,
      ∃ code : PowerMemberClass graph, relation index (classMember graph code).val := by
  constructor
  · rintro ⟨bound, covers⟩
    obtain ⟨graph, same⟩ := HSet.exists_mk bound
    refine ⟨graph, fun index => ?_⟩
    obtain ⟨y, member, related⟩ := covers index
    have pictured : y ∈ picture graph := by rw [picture_eq_mk, same]; exact member
    refine ⟨classOfMember graph ⟨y, pictured⟩, ?_⟩
    exact (congrArg Subtype.val (classMember_classOfMember graph ⟨y, pictured⟩)).symm ▸ related
  · rintro ⟨graph, covers⟩
    refine ⟨HSet.mk graph, fun index => ?_⟩
    obtain ⟨code, related⟩ := covers index
    exact ⟨(classMember graph code).val, picture_eq_mk graph ▸ (classMember graph code).property, related⟩

/-- To promote totality to original-level strong collection, one must obtain
this small witness cover. The typed and raised constructions below supply
their respective covers; this equivalence does not posit the missing one. -/
theorem strong_collection_iff_small_cover :
    (∃ collected : HSet.{u},
      (∀ index, ∃ y, relation index y ∧ y ∈ collected) ∧
      (∀ y ∈ collected, ∃ index, relation index y)) ↔
    ∃ graph : AccessiblePointedGraph.{u}, ∀ index,
      ∃ code : PowerMemberClass graph, relation index (classMember graph code).val :=
  (strong_collection_iff_bounded_witnesses relation).trans (bounded_witnesses_iff_small_cover relation)

/-- Descending the complete raised witness collection is a stronger property:
it requires a bound on every witness, rather than one witness per argument. -/
theorem collectionUp_descends_iff_all_witnesses_bounded :
    (∃ collected : HSet.{u}, HSet.lift collected = HSet.collectionUp relation) ↔
      ∃ bound : HSet.{u}, ∀ index y, relation index y → y ∈ bound := by
  constructor
  · rintro ⟨collected, same⟩
    refine ⟨collected, fun index y related => ?_⟩
    apply HSet.lift_mem_lift_iff.mp
    rw [same]
    exact HSet.lift_mem_collectionUp_iff.mpr ⟨index, related⟩
  · rintro ⟨bound, bounded⟩
    exact ⟨HSet.boundedCollection bound relation,
      HSet.lift_boundedCollection_eq_collectionUp bound relation bounded⟩

/-- For the actual set-theoretic schema the arguments are members of a set,
not an arbitrary large index type. This identifies the missing fixed-level
implication from totality to a small witness cover. -/
theorem fixed_level_schema_iff_small_witness_covers :
    (∀ X : HSet.{u}, ∀ relation : LiftedFamilyModel.Elements X → HSet.{u} → Prop,
      (∀ index, ∃ y, relation index y) →
      ∃ collected : HSet.{u},
        (∀ index, ∃ y, relation index y ∧ y ∈ collected) ∧
        (∀ y ∈ collected, ∃ index, relation index y)) ↔
    (∀ X : HSet.{u}, ∀ relation : LiftedFamilyModel.Elements X → HSet.{u} → Prop,
      (∀ index, ∃ y, relation index y) →
      ∃ graph : AccessiblePointedGraph.{u}, ∀ index,
        ∃ code : PowerMemberClass graph, relation index (classMember graph code).val) := by
  constructor
  · intro collection X relation total
    exact (strong_collection_iff_small_cover relation).mp (collection X relation total)
  · intro covers X relation total
    exact (strong_collection_iff_small_cover relation).mpr (covers X relation total)

end FixedBound

namespace Generated

open GeneratedMaterialDecoder LiftedFamilyModel

variable {X : HSet.{u}} {Family : Elements X → HSet.{u}}
variable {S : Type (u + 1)} {T : S → Type (u + 1)}
variable (sourceCode : CoreGeneration (Elements X) (fun a => Elements (Family a)) S)
variable (targetCode : (source : S) → CoreGeneration (Elements X) (fun a => Elements (Family a)) (T source))
variable (relation : (source : S) → T source → Prop)

/-- Arbitrarily nested Pi/Sigma/Id/W codes discharge every model parameter
of the witness decoder at the one common generated bound. -/
def witnessModel : PresentedType (Σ source : S, {result : T source // relation source result}) :=
  MaterialRelations.witnessModel (interpretFamily X Family sourceCode)
    (fun source => interpretFamily X Family (targetCode source)) relation

theorem witnessModel_carrier : (witnessModel sourceCode targetCode relation).carrier =
    PresentedCollection.generatedRows sourceCode targetCode relation :=
  MaterialRelations.witnessModel_carrier _ _ _

def projectionPresentation : PresentedMap.{u + 1}
    (MaterialRelations.projection (interpretFamily X Family sourceCode)
      (fun source => interpretFamily X Family (targetCode source)) relation) :=
  MaterialRelations.projectionPresentation _ _ _

/-- This is an actual small covering projection in the interpreted model. -/
theorem projection_surjective (total : ∀ source, ∃ result, relation source result) :
    Function.Surjective (MaterialRelations.projection (interpretFamily X Family sourceCode)
      (fun source => interpretFamily X Family (targetCode source)) relation) :=
  MaterialRelations.projection_surjective _ _ _ total

def value (next : (source : S) → T source → S) : S → HSet.{u + 1} :=
  MaterialRelations.value (interpretFamily X Family sourceCode)
    (fun source => interpretFamily X Family (targetCode source)) relation next

theorem mem_value_iff (next : (source : S) → T source → S) (source : S) (member : HSet.{u + 1}) :
    member ∈ value sourceCode targetCode relation next source ↔
      ∃ result, relation source result ∧ value sourceCode targetCode relation next (next source result) = member :=
  MaterialRelations.mem_value_iff _ _ _ _ _ _

end Generated

namespace MaterialMaps

variable {E W : Type u} {B : Type v}
variable (domain : PresentedType E) (result : PresentedType W)
variable (source : E → B) (endpoint : W → E)

/-- Every fibre of an actual presented domain has a constructed graph and
decoder at that original graph bound. -/
def fibreModel (base : B) : PresentedType (Fibre source base) :=
  PresentedType.restrict domain (fun element => source element = base)

def productModel (base : B) :
    PresentedType (PresentedMap.ProductFibre (first := source) (second := endpoint) base) :=
  PresentedType.product (fibreModel domain source base)
    (fun element => fibreModel result endpoint element.val)

/-- Pi-closure constructs material function graphs over the complete actual
input fibre. Argument and result values retain their original encodings. -/
theorem product_entry (base : B)
    (function : PresentedMap.ProductFibre (first := source) (second := endpoint) base)
    (argument : Fibre source base) :
    HSet.kpair (domain.value argument.val) (result.value (function argument).val) ∈
      (productModel domain result source endpoint base).value function :=
  PresentedType.product_entry (fibreModel domain source base)
    (fun element => fibreModel result endpoint element.val) function argument

/-- Application is computed by bounded separation and union of the actual
function graph, rather than by choosing a function witness. -/
theorem product_evaluation (base : B)
    (function : PresentedMap.ProductFibre (first := source) (second := endpoint) base)
    (argument : Fibre source base) :
    PresentedType.evalValue (fibreModel domain source base)
      (fun element => fibreModel result endpoint element.val)
      ((productModel domain result source endpoint base).value function) argument =
      result.value (function argument).val :=
  PresentedType.evalValue_functionGraph (fibreModel domain source base)
    (fun element => fibreModel result endpoint element.val) function argument

end MaterialMaps

namespace Controls

/-- Strong collection can stay at the original bound even when collecting
every possible witness requires a larger set. These properties are distinct. -/
theorem true_relation_strong_collection :
    ∃ collected : HSet.{u},
      (∀ _index : ULift.{u + 1, 0} PUnit, ∃ y : HSet.{u}, True ∧ y ∈ collected) ∧
      (∀ y ∈ collected, ∃ _index : ULift.{u + 1, 0} PUnit, True) := by
  refine ⟨{∅}, ?_, ?_⟩
  · intro _index
    exact ⟨∅, trivial, HSet.mem_singleton_self ∅⟩
  · intro _y _member
    exact ⟨ULift.up PUnit.unit, trivial⟩

theorem true_relation_all_witnesses_do_not_descend :
    ¬ ∃ collected : HSet.{u}, HSet.lift collected =
      HSet.collectionUp (fun (_index : ULift.{u + 1, 0} PUnit) (_value : HSet.{u}) => True) :=
  HSet.CollectionControls.true_relation_collection_not_lifted

open GeneratedMaterialDecoder LiftedFamilyModel

def quineSeed : HSet.{u} := {HSet.quineAtom}

def quineFamily (_source : Elements quineSeed.{u}) : HSet.{u} := {HSet.quineAtom}

def quineValue : Elements quineSeed.{u} → HSet.{u + 1} :=
  Generated.value (.base : CoreGeneration (Elements quineSeed.{u})
      (fun source => Elements (quineFamily source)) (Elements quineSeed))
    (fun source => .fibre source) (fun _ _ => True) (fun source _ => source)

theorem generated_quine_value (source : Elements quineSeed.{u}) :
    quineValue source = HSet.quineAtom := by
  apply HSet.eq_quineAtom_of_eq_singleton
  apply HSet.ext
  intro member
  rw [HSet.mem_singleton]
  constructor
  · intro available
    obtain ⟨_result, _, same⟩ := (Generated.mem_value_iff _ _ _ _ source member).mp available
    exact same.symm
  · intro same
    apply (Generated.mem_value_iff _ _ _ _ source member).mpr
    exact ⟨⟨HSet.quineAtom, HSet.mem_singleton_self _⟩, trivial, same.symm⟩

def deadValue : Elements quineSeed.{u} → HSet.{u + 1} :=
  Generated.value (.base : CoreGeneration (Elements quineSeed.{u})
      (fun source => Elements (quineFamily source)) (Elements quineSeed))
    (fun source => .fibre source) (fun _ _ => False) (fun source _ => source)

theorem generated_dead_value (source : Elements quineSeed.{u}) : deadValue source = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro member available
  obtain ⟨_result, impossible, _⟩ := (Generated.mem_value_iff _ _ _ _ source member).mp available
  exact impossible

theorem generated_cyclic_and_dead_distinct (source : Elements quineSeed.{u}) :
    quineValue source ≠ deadValue source := by
  rw [generated_quine_value, generated_dead_value]
  exact HSet.empty_ne_quineAtom.symm

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.StratifiedSmallMaps
