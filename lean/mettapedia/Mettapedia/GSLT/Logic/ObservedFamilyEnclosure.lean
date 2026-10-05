import Mettapedia.GSLT.Logic.ObservedMaterialization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GeneratedFamilyEnclosure

/-!
# Material dependent families over observed GSLT values

The range of the system's explicitly generated value graphs is an actual
material base. Its member carrier is equivalent to the small, represented
observation classes. Invariant source graph families descend to this base;
material product decoding then recovers exactly the compatible source
sections, including their original member values and complete graph rows.

The generated enclosure supplies semantic codes for this actual material
family. Its discrete identity over readout values compares the declared
observed behaviour, while the source equations retain their own meaning.
Actual action occurrences remain a separate event carrier over the material
base. Full subset carriers, material union and the stated raised universe
bounds belong to this construction's mathematical scope.

Source classes and the constructed fibre models live in `Type u`; their
generated code carrier lives in `Type (u + 1)`. Original material sets have
graph bound `u`. The independently constructed material products and sums
have graph bound `u + 1`, but their member carriers are equivalent to the
small generated decodings. The general enclosure on literal material-member
types remains available at code level `u + 2`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedFamilyEnclosure

open Mettapedia.TypeTheory.MaterialSets Mettapedia.TypeTheory.MaterialSets.Hypersets
open ObservedMaterialization HennessyMilner


universe u

variable {S : GSLT.{u}} {M : System.{u, u} S}

/-- The reachable graph of the actual observation/action encoding at a state. -/
def valueGraph (readings : LabelReadings M) (source : S.Term) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.generated
    (readings.taggedPresentation.edge (encodedStep M)) (HSet.LabelCarrier.atom (some source))

theorem mk_valueGraph (readings : LabelReadings M) (source : S.Term) :
    HSet.mk (valueGraph readings source) = readings.value source := rfl

/-- All values represented by the source System form an actual material set. -/
def valueRange (readings : LabelReadings M) : HSet.{u} := HSet.range (valueGraph readings)

theorem mem_valueRange_iff (readings : LabelReadings M) (value : HSet.{u}) :
    value ∈ valueRange readings ↔ ∃ source, readings.value source = value := by
  rw [valueRange, HSet.mem_range]
  simp only [mk_valueGraph]

def valueMember (readings : LabelReadings M) (source : S.Term) : LiftedFamilyModel.Elements (valueRange readings) :=
  ⟨readings.value source, (mem_valueRange_iff readings _).mpr ⟨source, rfl⟩⟩

theorem valueMember_eq_iff (readings : LabelReadings M) (faithful : readings.Faithful)
    (left right : S.Term) :
    valueMember readings left = valueMember readings right ↔ M.Bisimilar left right :=
  ⟨fun same => (readings.value_eq_iff_bisimilar faithful left right).mp (congrArg PSigma.fst same),
    fun related => El.ext HSet.propositional (readings.value_eq_of_bisimilar related)⟩

abbrev Classes (readings : LabelReadings M) := PowerClassFamilyDescent.ObservationClass readings.value

private theorem valueGraphs_invariant (readings : LabelReadings M) :
    PowerClassFamilyDescent.FamilyInvariant readings.value (valueGraph readings) := by
  intro left right same
  simpa only [mk_valueGraph] using same

/-- Decode a class by range and union of all its value graphs. -/
def classDecode (readings : LabelReadings M) (observed : Classes readings) :
    LiftedFamilyModel.Elements (valueRange readings) :=
  ⟨PowerClassFamilyDescent.decodedFamily (valueGraph readings) observed, by
    obtain ⟨source, same⟩ := PowerClassFamilyDescent.classOf_surjective readings.value observed
    rw [← same, PowerClassFamilyDescent.family_beta readings.value (valueGraph readings)
      (valueGraphs_invariant readings), mk_valueGraph]
    exact (valueMember readings source).2⟩

theorem classDecode_classOf (readings : LabelReadings M) (source : S.Term) :
    classDecode readings (PowerClassFamilyDescent.classOf readings.value source) = valueMember readings source :=
  El.ext HSet.propositional
    ((PowerClassFamilyDescent.family_beta readings.value (valueGraph readings) (valueGraphs_invariant readings) source).trans
      (mk_valueGraph readings source))

/-- Encode a material value by its entire source fibre. An existential source
witness establishes membership of the subset in the class carrier only. -/
def classEncode (readings : LabelReadings M) (member : LiftedFamilyModel.Elements (valueRange readings)) :
    Classes readings :=
  ⟨{source | readings.value source = member.1}, by
    obtain ⟨source, same⟩ := (mem_valueRange_iff readings member.1).mp member.2
    exact ⟨source, congrArg (fun value => {other | readings.value other = value}) same.symm⟩⟩

theorem classEncode_valueMember (readings : LabelReadings M) (source : S.Term) :
    classEncode readings (valueMember readings source) = PowerClassFamilyDescent.classOf readings.value source :=
  Subtype.ext rfl

theorem classEncode_classDecode (readings : LabelReadings M) (observed : Classes readings) :
    classEncode readings (classDecode readings observed) = observed := by
  obtain ⟨source, rfl⟩ := PowerClassFamilyDescent.classOf_surjective readings.value observed
  rw [classDecode_classOf, classEncode_valueMember]

theorem classDecode_classEncode (readings : LabelReadings M)
    (member : LiftedFamilyModel.Elements (valueRange readings)) : classDecode readings (classEncode readings member) = member := by
  obtain ⟨source, same⟩ := (mem_valueRange_iff readings member.1).mp member.2
  have memberEq : member = valueMember readings source := El.ext HSet.propositional same.symm
  rw [memberEq, classEncode_valueMember, classDecode_classOf]

/-- The actual material base and the explicitly small class carrier have
constructed inverse functions, without a representative selector. -/
def classMemberEquiv (readings : LabelReadings M) :
    Classes readings ≃ LiftedFamilyModel.Elements (valueRange readings) where
  toFun := classDecode readings
  invFun := classEncode readings
  left_inv := classEncode_classDecode readings
  right_inv := classDecode_classEncode readings

theorem classMemberEquiv_classOf (readings : LabelReadings M) (source : S.Term) :
    classMemberEquiv readings (PowerClassFamilyDescent.classOf readings.value source) = valueMember readings source :=
  classDecode_classOf readings source

theorem classMemberEquiv_symm_valueMember (readings : LabelReadings M) (source : S.Term) :
    (classMemberEquiv readings).symm (valueMember readings source) =
      PowerClassFamilyDescent.classOf readings.value source := classEncode_valueMember readings source

theorem value_members_small (readings : LabelReadings M) :
    Small.{u} (LiftedFamilyModel.Elements (valueRange readings)) := Small.mk' (classMemberEquiv readings).symm

/-- Descended fibres indexed by actual material members of the value range. -/
def materialFamily (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u})
    (member : LiftedFamilyModel.Elements (valueRange readings)) : HSet.{u} :=
  PowerClassFamilyDescent.decodedFamily graphs ((classMemberEquiv readings).symm member)

theorem materialFamily_valueMember (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) (source : S.Term) :
    materialFamily readings graphs (valueMember readings source) = HSet.mk (graphs source) := by
  rw [materialFamily, classMemberEquiv_symm_valueMember]
  exact PowerClassFamilyDescent.family_beta readings.value graphs invariant source

private def memberCast {X Y : HSet.{u}} (same : X = Y) : LiftedFamilyModel.Elements X ≃ LiftedFamilyModel.Elements Y where
  toFun member := ⟨member.1, same ▸ member.2⟩
  invFun member := ⟨member.1, same.symm ▸ member.2⟩
  left_inv _member := El.ext HSet.propositional rfl
  right_inv _member := El.ext HSet.propositional rfl

/-- Reindexing across the constructed base comparison preserves the full
member value despite the dependent fibre equality. -/
private def sectionBaseEquiv {A C : Type*} (base : A ≃ C) (family : A → HSet.{u}) :
    ((c : C) → LiftedFamilyModel.Elements (family (base.symm c))) ≃ ((a : A) → LiftedFamilyModel.Elements (family a)) where
  toFun term a := memberCast (congrArg family (base.symm_apply_apply a)) (term (base a))
  invFun term c := term (base.symm c)
  left_inv term := by
    funext c
    apply El.ext HSet.propositional
    exact congrArg (fun c => (term c).1) (base.apply_symm_apply c)
  right_inv term := by
    funext a
    apply El.ext HSet.propositional
    exact congrArg (fun a => (term a).1) (base.symm_apply_apply a)

abbrev CompatibleSections (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u}) :=
  {term : PowerClassFamilyDescent.SourceSection graphs // PowerClassFamilyDescent.TermCompatible readings.value graphs term}

def sectionCode (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u}) :=
  GeneratedFamilyEnclosure.productCode (valueRange readings) (materialFamily readings graphs)

def enclosure (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u}) :=
  GeneratedFamilyEnclosure.enclosure (valueRange readings) (materialFamily readings graphs)

/-- The generated product code decodes to precisely the source sections that
agree in full member value on each observation fibre. -/
def sourceSectionCodeEquiv (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) :
    (sectionCode readings graphs).El ≃ CompatibleSections readings graphs :=
  (sectionBaseEquiv (classMemberEquiv readings) (PowerClassFamilyDescent.decodedFamily graphs)).trans
    (PowerClassFamilyDescent.materialSectionEquiv readings.value graphs invariant)

def productSourceEquiv (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) :
    LiftedFamilyModel.Elements (LiftedFamilyModel.productUp (valueRange readings) (materialFamily readings graphs)) ≃
      CompatibleSections readings graphs :=
  (GeneratedFamilyEnclosure.productDecode (valueRange readings) (materialFamily readings graphs)).trans
    (sourceSectionCodeEquiv readings graphs invariant)

theorem productSourceEquiv_application (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs)
    (graph : LiftedFamilyModel.Elements (LiftedFamilyModel.productUp (valueRange readings) (materialFamily readings graphs)))
    (source : S.Term) :
    ((productSourceEquiv readings graphs invariant graph).1 source).1 =
      (LiftedFamilyModel.evaluate graph (valueMember readings source)).1 := by
  change (PowerClassFamilyDescent.pullSection readings.value graphs invariant
    (sectionBaseEquiv (classMemberEquiv readings) (PowerClassFamilyDescent.decodedFamily graphs)
      (LiftedFamilyModel.evaluate graph)) source).1 = _
  rw [PowerClassFamilyDescent.pullSection_value]
  change (LiftedFamilyModel.evaluate graph (classMemberEquiv readings (PowerClassFamilyDescent.classOf readings.value source))).1 = _
  rw [classMemberEquiv_classOf]

/-- Material rows identify exactly the original source-section result. -/
theorem product_row_iff (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs)
    (graph : LiftedFamilyModel.Elements (LiftedFamilyModel.productUp (valueRange readings) (materialFamily readings graphs)))
    (source : S.Term) (value : HSet.{u}) :
    HSet.lift (HSet.kpair (readings.value source) value) ∈ graph.1 ↔
      value = ((productSourceEquiv readings graphs invariant graph).1 source).1 := by
  rw [← LiftedFamilyModel.graph_evaluate graph]
  exact (LiftedFamilyModel.liftedPair_mem_sectionGraph_iff (LiftedFamilyModel.evaluate graph) (valueMember readings source) value).trans
    (by rw [productSourceEquiv_application])

def encodeSection (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) (term : CompatibleSections readings graphs) :
    LiftedFamilyModel.Elements (LiftedFamilyModel.productUp (valueRange readings) (materialFamily readings graphs)) :=
  (productSourceEquiv readings graphs invariant).symm term

theorem encodeSection_beta_value (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) (term : CompatibleSections readings graphs)
    (source : S.Term) :
    (LiftedFamilyModel.evaluate (encodeSection readings graphs invariant term) (valueMember readings source)).1 =
      (term.1 source).1 := by
  rw [← productSourceEquiv_application readings graphs invariant]
  exact congrArg (fun term : CompatibleSections readings graphs => (term.1 source).1)
    ((productSourceEquiv readings graphs invariant).apply_symm_apply term)

theorem encodeSection_eta (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs)
    (graph : LiftedFamilyModel.Elements (LiftedFamilyModel.productUp (valueRange readings) (materialFamily readings graphs))) :
    (encodeSection readings graphs invariant (productSourceEquiv readings graphs invariant graph)).1 =
      graph.1 := congrArg PSigma.fst ((productSourceEquiv readings graphs invariant).symm_apply_apply graph)

def sourceMember (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) (source : S.Term)
    (member : LiftedFamilyModel.Elements (HSet.mk (graphs source))) :
    LiftedFamilyModel.Elements (materialFamily readings graphs (valueMember readings source)) :=
  memberCast (materialFamily_valueMember readings graphs invariant source).symm member

/-- The actual material sum has exactly the source value/member pairs.
No source witness is selected to define its material decoder. -/
theorem mem_sum_iff_source_pair (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) (pair : HSet.{u + 1}) :
    pair ∈ LiftedFamilyModel.sumUp (valueRange readings) (materialFamily readings graphs) ↔
      ∃ source, ∃ member : LiftedFamilyModel.Elements (HSet.mk (graphs source)),
        HSet.lift (HSet.kpair (readings.value source) member.1) = pair := by
  rw [LiftedFamilyModel.mem_sumUp_iff]
  constructor
  · rintro ⟨index, member, same⟩
    obtain ⟨source, valueEq⟩ := (mem_valueRange_iff readings index.1).mp index.2
    have indexEq : index = valueMember readings source := El.ext HSet.propositional valueEq.symm
    subst index
    refine ⟨source, memberCast (materialFamily_valueMember readings graphs invariant source) member, same⟩
  · rintro ⟨source, member, same⟩
    exact ⟨valueMember readings source, sourceMember readings graphs invariant source member, same⟩

theorem sumDecode_source_first (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) (source : S.Term)
    (member : LiftedFamilyModel.Elements (HSet.mk (graphs source))) :
    (GeneratedFamilyEnclosure.sumDecode (valueRange readings) (materialFamily readings graphs)
      (LiftedFamilyModel.sumPair (valueMember readings source) (sourceMember readings graphs invariant source member))).1 =
      valueMember readings source := GeneratedFamilyEnclosure.sumDecode_first _ _

theorem sumDecode_source_second_value (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) (source : S.Term)
    (member : LiftedFamilyModel.Elements (HSet.mk (graphs source))) :
    (GeneratedFamilyEnclosure.sumDecode (valueRange readings) (materialFamily readings graphs)
      (LiftedFamilyModel.sumPair (valueMember readings source) (sourceMember readings graphs invariant source member))).2.1 =
      member.1 := GeneratedFamilyEnclosure.sumDecode_second_value _ _

/-- Identity in this discrete generated model is equality of the observed
material values; it is not the source equation theory or a higher native Id. -/
def identityCode (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u})
    (left right : S.Term) :=
  GeneratedFamilyEnclosure.identityCode (valueRange readings) (materialFamily readings graphs)
    (valueMember readings left) (valueMember readings right)

theorem identityCode_iff_bisimilar (readings : LabelReadings M) (faithful : readings.Faithful)
    (graphs : S.Term → AccessiblePointedGraph.{u}) (left right : S.Term) :
    Nonempty (GeneratedFamilyEnclosure.identityCode (valueRange readings) (materialFamily readings graphs)
      (valueMember readings left) (valueMember readings right)).El ↔ M.Bisimilar left right :=
  (GeneratedFamilyEnclosure.identityCode_inhabited_iff_values _ _).trans (readings.value_eq_iff_bisimilar faithful left right)

abbrev SmallCodes (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u}) :=
  Mettapedia.TypeTheory.GeneratedFamilyUniverse.Code (Classes readings)
    (fun observed => PowerClassFamilyDescent.FamilyMemberModel graphs observed)

/-- The small class and fibre carriers generate an enclosure at the lower
code level, with actual full material-value decoding comparisons below. -/
def smallEnclosure (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u}) :
    Mettapedia.TypeTheory.FamilyEnclosingUniverse.ClosedTarskiUniverseOver.{u + 1, u}
      (Classes readings) (fun observed => PowerClassFamilyDescent.FamilyMemberModel graphs observed) :=
  Mettapedia.TypeTheory.GeneratedFamilyUniverse.envelope (Classes readings)
    (fun observed => PowerClassFamilyDescent.FamilyMemberModel graphs observed)

def smallSectionCode (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u}) :
    SmallCodes readings graphs :=
  Mettapedia.TypeTheory.GeneratedFamilyUniverse.Code.pi
    Mettapedia.TypeTheory.GeneratedFamilyUniverse.Code.base
    (fun observed => Mettapedia.TypeTheory.GeneratedFamilyUniverse.Code.fibre observed)

def smallSumCode (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u}) :
    SmallCodes readings graphs :=
  Mettapedia.TypeTheory.GeneratedFamilyUniverse.Code.sigma
    Mettapedia.TypeTheory.GeneratedFamilyUniverse.Code.base
    (fun observed => Mettapedia.TypeTheory.GeneratedFamilyUniverse.Code.fibre observed)

def smallSourceSectionEquiv (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) :
    (smallSectionCode readings graphs).El ≃ CompatibleSections readings graphs :=
  PowerClassFamilyDescent.compatibleSectionEquiv readings.value graphs invariant

/-- The independently constructed material product decodes to the lower
generated product code, through its actual compatible source sections. -/
def productSmallCodeDecode (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) :
    LiftedFamilyModel.Elements (LiftedFamilyModel.productUp
      (valueRange readings) (materialFamily readings graphs)) ≃ (smallSectionCode readings graphs).El :=
  (productSourceEquiv readings graphs invariant).trans (smallSourceSectionEquiv readings graphs invariant).symm

theorem productSmallCodeDecode_application (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs)
    (graph : LiftedFamilyModel.Elements (LiftedFamilyModel.productUp
      (valueRange readings) (materialFamily readings graphs))) (source : S.Term) :
    AccessiblePointedGraph.classValue
      (PowerClassFamilyDescent.familyGraph graphs (PowerClassFamilyDescent.classOf readings.value source))
      (productSmallCodeDecode readings graphs invariant graph
        (PowerClassFamilyDescent.classOf readings.value source)).1 =
      (LiftedFamilyModel.evaluate graph (valueMember readings source)).1 := by
  have decodes := PowerClassFamilyDescent.compatibleSectionEquiv_value readings.value graphs invariant
    (productSmallCodeDecode readings graphs invariant graph) source
  have inverse : smallSourceSectionEquiv readings graphs invariant
      (productSmallCodeDecode readings graphs invariant graph) =
      productSourceEquiv readings graphs invariant graph :=
    (smallSourceSectionEquiv readings graphs invariant).apply_symm_apply _
  exact decodes.symm.trans
    ((congrArg (fun term : CompatibleSections readings graphs => (term.1 source).1) inverse).trans
      (productSourceEquiv_application readings graphs invariant graph source))

private def sumBaseEquiv {A C : Type*} (base : A ≃ C) (family : A → HSet.{u}) :
    (Σ c : C, LiftedFamilyModel.Elements (family (base.symm c))) ≃
      (Σ a : A, LiftedFamilyModel.Elements (family a)) where
  toFun member := ⟨base.symm member.1, member.2⟩
  invFun member := ⟨base member.1,
    memberCast (congrArg family (base.symm_apply_apply member.1)).symm member.2⟩
  left_inv member :=
    (PowerClassFamilyDescent.totalElPair_eq_iff (fun c => family (base.symm c)) _ _).mpr
      ⟨base.apply_symm_apply member.1, rfl⟩
  right_inv member := (PowerClassFamilyDescent.totalElPair_eq_iff family _ _).mpr
    ⟨base.symm_apply_apply member.1, rfl⟩

def sumSmallCodeDecode (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u}) :
    LiftedFamilyModel.Elements (LiftedFamilyModel.sumUp
      (valueRange readings) (materialFamily readings graphs)) ≃ (smallSumCode readings graphs).El :=
  ((GeneratedFamilyEnclosure.sumDecode (valueRange readings) (materialFamily readings graphs)).trans
    (sumBaseEquiv (classMemberEquiv readings) (PowerClassFamilyDescent.decodedFamily graphs))).trans
      (PowerClassFamilyDescent.observedComprehensionEquiv readings.value graphs).symm

theorem sumSmallCodeDecode_base (readings : LabelReadings M) (graphs : S.Term → AccessiblePointedGraph.{u})
    (pair : LiftedFamilyModel.Elements (LiftedFamilyModel.sumUp
      (valueRange readings) (materialFamily readings graphs))) :
    classMemberEquiv readings (sumSmallCodeDecode readings graphs pair).1 =
      (GeneratedFamilyEnclosure.sumDecode (valueRange readings) (materialFamily readings graphs) pair).1 :=
  (classMemberEquiv readings).apply_symm_apply _

theorem sumSmallCodeDecode_member_value (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (pair : LiftedFamilyModel.Elements (LiftedFamilyModel.sumUp
      (valueRange readings) (materialFamily readings graphs))) :
    (PowerClassFamilyDescent.familyMemberEquiv graphs (sumSmallCodeDecode readings graphs pair).1
      (sumSmallCodeDecode readings graphs pair).2).1 =
      (GeneratedFamilyEnclosure.sumDecode (valueRange readings) (materialFamily readings graphs) pair).2.1 :=
  congrArg PSigma.fst (PowerClassFamilyDescent.familyMemberEquiv graphs _ |>.apply_symm_apply _)

/-- The explicit class/fibre constructions exhibit both material member
carriers at the original source bound, despite the raised graph encoding. -/
theorem material_members_small (readings : LabelReadings M)
    (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs) :
    Small.{u} (LiftedFamilyModel.Elements (LiftedFamilyModel.productUp
      (valueRange readings) (materialFamily readings graphs))) ∧
    Small.{u} (LiftedFamilyModel.Elements (LiftedFamilyModel.sumUp
      (valueRange readings) (materialFamily readings graphs))) :=
  ⟨Small.mk' (productSmallCodeDecode readings graphs invariant),
    Small.mk' (sumSmallCodeDecode readings graphs)⟩

namespace Reindex

variable {S' : GSLT.{u}} {M' : System.{u, u} S'}
variable (readings : LabelReadings M) (readings' : LabelReadings M')
variable (sourceMap : S'.Term → S.Term) (targetMap : HSet.{u} → HSet.{u})
variable (commutes : ∀ source, readings.value (sourceMap source) = targetMap (readings'.value source))

/-- A commuting raw square induces an actual map of the two material bases.
Only its membership proof uses the source witness of an input member. -/
def baseMap (member : LiftedFamilyModel.Elements (valueRange readings')) :
    LiftedFamilyModel.Elements (valueRange readings) :=
  ⟨targetMap member.1, by
    obtain ⟨source, same⟩ := (mem_valueRange_iff readings' member.1).mp member.2
    exact (mem_valueRange_iff readings _).mpr
      ⟨sourceMap source, (commutes source).trans (congrArg targetMap same)⟩⟩

theorem baseMap_valueMember (source : S'.Term) :
    baseMap readings readings' sourceMap targetMap commutes (valueMember readings' source) =
      valueMember readings (sourceMap source) := El.ext HSet.propositional (commutes source).symm

theorem baseMap_classDecode (observed : Classes readings') :
    baseMap readings readings' sourceMap targetMap commutes (classDecode readings' observed) =
      classDecode readings
        (PowerClassFamilyDescent.classMap readings.value readings'.value sourceMap targetMap commutes observed) := by
  obtain ⟨source, rfl⟩ := PowerClassFamilyDescent.classOf_surjective readings'.value observed
  rw [classDecode_classOf, PowerClassFamilyDescent.classMap_beta,
    classDecode_classOf, baseMap_valueMember]

/-- Reindexing the source graph family and decoding its represented classes
commutes with the actual material-base map. -/
theorem family_reindex (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs)
    (member : LiftedFamilyModel.Elements (valueRange readings')) :
    materialFamily readings' (graphs ∘ sourceMap) member =
      materialFamily readings graphs (baseMap readings readings' sourceMap targetMap commutes member) := by
  obtain ⟨source, same⟩ := (mem_valueRange_iff readings' member.1).mp member.2
  have memberEq : member = valueMember readings' source := El.ext HSet.propositional same.symm
  subst member
  rw [baseMap_valueMember]
  exact (materialFamily_valueMember readings' (graphs ∘ sourceMap)
    (PowerClassFamilyDescent.reindexInvariant readings.value readings'.value sourceMap targetMap
      commutes graphs invariant) source).trans
    (materialFamily_valueMember readings graphs invariant (sourceMap source)).symm

private theorem evaluate_memberCast_value {X : HSet.{u}} {first second : LiftedFamilyModel.Elements X → HSet.{u}}
    (same : first = second)
    (graph : LiftedFamilyModel.Elements (LiftedFamilyModel.productUp X first))
    (argument : LiftedFamilyModel.Elements X) :
    (LiftedFamilyModel.evaluate (memberCast (congrArg (LiftedFamilyModel.productUp X) same) graph) argument).1 =
      (LiftedFamilyModel.evaluate graph argument).1 := by
  cases same
  rfl

/-- Evaluate the original graph at the actual base substitution, construct
the substituted graph, and explicitly transport its fibre formation. -/
def pullProduct (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs)
    (graph : LiftedFamilyModel.Elements (LiftedFamilyModel.productUp
      (valueRange readings) (materialFamily readings graphs))) :
    LiftedFamilyModel.Elements (LiftedFamilyModel.productUp
      (valueRange readings') (materialFamily readings' (graphs ∘ sourceMap))) :=
  memberCast (congrArg (LiftedFamilyModel.productUp (valueRange readings'))
    (funext (family_reindex readings readings' sourceMap targetMap commutes graphs invariant)).symm)
      (LiftedFamilyModel.pullGraph (baseMap readings readings' sourceMap targetMap commutes) graph)

theorem pullProduct_application (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs)
    (graph : LiftedFamilyModel.Elements (LiftedFamilyModel.productUp
      (valueRange readings) (materialFamily readings graphs)))
    (argument : LiftedFamilyModel.Elements (valueRange readings')) :
    (LiftedFamilyModel.evaluate (pullProduct readings readings' sourceMap targetMap commutes graphs invariant graph)
      argument).1 =
      (LiftedFamilyModel.evaluate graph (baseMap readings readings' sourceMap targetMap commutes argument)).1 := by
  exact (evaluate_memberCast_value
    (funext (family_reindex readings readings' sourceMap targetMap commutes graphs invariant)).symm
    (LiftedFamilyModel.pullGraph (baseMap readings readings' sourceMap targetMap commutes) graph) argument).trans
      (congrArg (fun term => (term argument).1)
        (LiftedFamilyModel.evaluate_pullGraph (baseMap readings readings' sourceMap targetMap commutes) graph))

/-- The substituted material graph decodes to the substituted SOURCE section
with exactly the original member values at every argument. -/
theorem pullProduct_source_value (graphs : S.Term → AccessiblePointedGraph.{u})
    (invariant : PowerClassFamilyDescent.FamilyInvariant readings.value graphs)
    (graph : LiftedFamilyModel.Elements (LiftedFamilyModel.productUp
      (valueRange readings) (materialFamily readings graphs))) (source : S'.Term) :
    ((productSourceEquiv readings' (graphs ∘ sourceMap)
      (PowerClassFamilyDescent.reindexInvariant readings.value readings'.value sourceMap targetMap
        commutes graphs invariant)
      (pullProduct readings readings' sourceMap targetMap commutes graphs invariant graph)).1 source).1 =
      ((productSourceEquiv readings graphs invariant graph).1 (sourceMap source)).1 := by
  rw [productSourceEquiv_application, pullProduct_application, baseMap_valueMember]
  exact (productSourceEquiv_application readings graphs invariant graph (sourceMap source)).symm

end Reindex

namespace Events

open Mettapedia.OSLF.Framework.DerivedModalities ObservationSpans

/-- The actual source event carrier is retained over the actual material base. -/
def memberSpan (readings : LabelReadings M) (occurrences : ActionOccurrences M) :
    ReductionSpan (LiftedFamilyModel.Elements (valueRange readings)) where
  Edge := ActionOccurrences.Event occurrences
  source event := valueMember readings event.source
  target event := valueMember readings event.target

def observation (readings : LabelReadings M) (occurrences : ActionOccurrences M) :
    SpanMap occurrences.sourceSpan (memberSpan readings occurrences) where
  states := valueMember readings
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

def values (readings : LabelReadings M) (occurrences : ActionOccurrences M) :
    SpanMap (memberSpan readings occurrences) (occurrences.materialSpan readings) where
  states := PSigma.fst
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

theorem observation_square (readings : LabelReadings M) (occurrences : ActionOccurrences M) :
    SpanMap.comp (values readings occurrences) (observation readings occurrences) =
      occurrences.observation readings := rfl

theorem events_injective (readings : LabelReadings M) (occurrences : ActionOccurrences M) :
    Function.Injective (observation readings occurrences).events := fun _ _ same => same

theorem sourceLifts (readings : LabelReadings M) (faithful : readings.Faithful)
    (occurrences : ActionOccurrences M) : (observation readings occurrences).SourceLifts := by
  intro source event same
  obtain ⟨matched, starts, targets⟩ := (occurrences.sourceLifts readings faithful)
    source event (congrArg PSigma.fst same)
  exact ⟨matched, starts, El.ext HSet.propositional targets⟩

theorem diamond (readings : LabelReadings M) (faithful : readings.Faithful)
    (occurrences : ActionOccurrences M) (predicate : LiftedFamilyModel.Elements (valueRange readings) → Prop)
    (source : S.Term) :
    derivedDiamond (memberSpan readings occurrences) predicate (valueMember readings source) ↔
      derivedDiamond occurrences.sourceSpan (predicate ∘ valueMember readings) source :=
  (observation readings occurrences).diamond_pullback (sourceLifts readings faithful occurrences) predicate source

/-- An actual event map with commuting authored endpoints induces the
corresponding span map over the two material bases. Event data is mapped by
the supplied function, independently of endpoint behavioural identification. -/
def reindexSpanMap {S' : GSLT.{u}} {M' : System.{u, u} S'}
    (readings : LabelReadings M) (readings' : LabelReadings M')
    (sourceMap : S'.Term → S.Term) (targetMap : HSet.{u} → HSet.{u})
    (commutes : ∀ source, readings.value (sourceMap source) = targetMap (readings'.value source))
    (occurrences : ActionOccurrences M) (occurrences' : ActionOccurrences M')
    (events : ActionOccurrences.Event occurrences' → ActionOccurrences.Event occurrences)
    (sourceSquare : ∀ event, (events event).source = sourceMap event.source)
    (targetSquare : ∀ event, (events event).target = sourceMap event.target) :
    SpanMap (memberSpan readings' occurrences') (memberSpan readings occurrences) where
  states := Reindex.baseMap readings readings' sourceMap targetMap commutes
  events := events
  source_comm event := (congrArg (valueMember readings) (sourceSquare event)).trans
    (Reindex.baseMap_valueMember readings readings' sourceMap targetMap commutes event.source).symm
  target_comm event := (congrArg (valueMember readings) (targetSquare event)).trans
    (Reindex.baseMap_valueMember readings readings' sourceMap targetMap commutes event.target).symm

theorem reindex_events_injective {S' : GSLT.{u}} {M' : System.{u, u} S'}
    (readings : LabelReadings M) (readings' : LabelReadings M')
    (sourceMap : S'.Term → S.Term) (targetMap : HSet.{u} → HSet.{u})
    (commutes : ∀ source, readings.value (sourceMap source) = targetMap (readings'.value source))
    (occurrences : ActionOccurrences M) (occurrences' : ActionOccurrences M')
    (events : ActionOccurrences.Event occurrences' → ActionOccurrences.Event occurrences)
    (sourceSquare : ∀ event, (events event).source = sourceMap event.source)
    (targetSquare : ∀ event, (events event).target = sourceMap event.target)
    (retains : Function.Injective events) :
    Function.Injective (reindexSpanMap readings readings' sourceMap targetMap commutes
      occurrences occurrences' events sourceSquare targetSquare).events := retains

end Events

namespace Controls

open ObservedMaterialization.Controls
open OutcomeLabels

/-- Fibres are the actual observable entries at each source state. -/
def familyGraphs : State.{u} → AccessiblePointedGraph.{u} := valueGraph readings

theorem familyInvariant : PowerClassFamilyDescent.FamilyInvariant readings.{u}.value familyGraphs :=
  valueGraphs_invariant readings

/-- Choose the declared result/fault observation, with actual material
membership at every terminal and cyclic source state. -/
def atomSection (source : State.{u}) : LiftedFamilyModel.Elements (HSet.mk (familyGraphs source)) :=
  ⟨HSet.kpair (readings.taggedReading (.inl (outcome source))) ∅, by
    change HSet.kpair (readings.taggedReading (.inl (outcome source))) ∅ ∈ readings.value source
    exact (readings.observation_iff faithful source (outcome source)).mpr rfl⟩

theorem atomCompatible : PowerClassFamilyDescent.TermCompatible readings.{u}.value familyGraphs atomSection := by
  intro left right same
  have results : outcome left = outcome right :=
    ((readings.kernel_isBisimulation faithful).2.2 same (outcome left)).mp rfl
  exact congrArg (fun result => HSet.kpair (readings.taggedReading (.inl result)) ∅) results

def encodedAtomSection :=
  encodeSection readings.{u} familyGraphs familyInvariant ⟨atomSection, atomCompatible⟩

theorem atomSection_beta (source : State.{u}) :
    (LiftedFamilyModel.evaluate encodedAtomSection (valueMember readings source)).1 =
      HSet.kpair (readings.taggedReading (.inl (outcome source))) ∅ :=
  encodeSection_beta_value readings familyGraphs familyInvariant ⟨atomSection, atomCompatible⟩ source

theorem atomSection_rows (source : State.{u}) (value : HSet.{u}) :
    HSet.lift (HSet.kpair (readings.value source) value) ∈ encodedAtomSection.1 ↔
      value = HSet.kpair (readings.taggedReading (.inl (outcome source))) ∅ := by
  rw [← LiftedFamilyModel.graph_evaluate encodedAtomSection]
  exact (LiftedFamilyModel.liftedPair_mem_sectionGraph_iff
    (LiftedFamilyModel.evaluate encodedAtomSection) (valueMember readings source) value).trans
      (by rw [atomSection_beta])

theorem material_family_nonconstant (result : Outcome.{u}) :
    materialFamily readings familyGraphs (valueMember readings (State.terminal result)) ≠
      materialFamily readings familyGraphs (valueMember readings (State.cycle result false)) := by
  intro same
  have terminal := materialFamily_valueMember readings familyGraphs familyInvariant (State.terminal result)
  have cycle := materialFamily_valueMember readings familyGraphs familyInvariant (State.cycle result false)
  exact terminal_ne_cycle result false (terminal.symm.trans (same.trans cycle))

theorem base_not_wf : ¬ (valueRange readings.{u}).WF :=
  HSet.not_wf_of_mem (valueMember readings (State.cycle (Outcome.result 0) false)).2
    (cycle_not_wf (Outcome.result 0) false)

theorem actual_product_nonempty :
    LiftedFamilyModel.productUp (valueRange readings.{u}) (materialFamily readings familyGraphs) ≠ ∅ := by
  intro same
  have member := encodedAtomSection.{u}.2
  exact HSet.notMem_empty _
    (Eq.mp (congrArg (fun bound : HSet.{u + 1} => encodedAtomSection.1 ∈ bound) same) member)

/-- The alternate source section retains the phase-sensitive decision to
take a cyclic continuation rather than read the atomic result. -/
def phaseSection : PowerClassFamilyDescent.SourceSection familyGraphs.{u}
  | .terminal result => atomSection (.terminal result)
  | .cycle result false => atomSection (.cycle result false)
  | .cycle result true =>
      ⟨HSet.kpair (readings.taggedReading (.inr PUnit.unit))
        (readings.value (.cycle result false)), by
        change HSet.kpair (readings.taggedReading (.inr PUnit.unit))
          (readings.value (.cycle result false)) ∈ readings.value (.cycle result true)
        exact (readings.action_iff faithful (.cycle result true) PUnit.unit _).mpr
          ⟨State.cycle result false, ⟨rfl, rfl⟩, rfl⟩⟩

/-- Fibre invariance does not make every selected source term compatible. -/
theorem phaseSection_incompatible :
    ¬ PowerClassFamilyDescent.TermCompatible readings.{u}.value familyGraphs phaseSection := by
  intro compatible
  have selected := compatible (cycle_values_eq (Outcome.result 0) false true)
  change HSet.kpair (readings.taggedReading (.inl (Outcome.result 0))) ∅ =
    HSet.kpair (readings.taggedReading (.inr PUnit.unit))
      (readings.value (.cycle (Outcome.result 0) false)) at selected
  exact HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp (HSet.kpair_inj.mp selected).1).1

theorem no_product_reifies_phase :
    ¬ ∃ graph : LiftedFamilyModel.Elements
        (LiftedFamilyModel.productUp (valueRange readings.{u}) (materialFamily readings familyGraphs)),
      ∀ source, ((productSourceEquiv readings familyGraphs familyInvariant graph).1 source).1 =
        (phaseSection source).1 := by
  rintro ⟨graph, agrees⟩
  have terms : (productSourceEquiv readings familyGraphs familyInvariant graph).1 = phaseSection := by
    funext source
    exact El.ext HSet.propositional (agrees source)
  have compatible := (productSourceEquiv readings familyGraphs familyInvariant graph).2
  rw [terms] at compatible
  exact phaseSection_incompatible compatible

/-- A nonidentity source substitution really advances each cycle phase. -/
def advance : State.{u} → State.{u}
  | .terminal result => .terminal result
  | .cycle result phase => .cycle result (!phase)

theorem advance_square (source : State.{u}) : readings.value (advance source) = id (readings.value source) := by
  cases source with
  | terminal _ => rfl
  | cycle result phase => exact cycle_values_eq result (!phase) phase

theorem outcome_advance (source : State.{u}) : outcome (advance source) = outcome source := by
  cases source <;> rfl

theorem advance_nonidentity (result : Outcome.{u}) :
    advance (State.cycle result false) ≠ State.cycle result false := by
  intro same
  exact Bool.noConfusion (State.cycle.inj same).2

/-- The material substitution rebuilds a graph over the independently
reindexed source family and preserves its actual atomic member values. -/
theorem advance_product_application (source : State.{u}) :
    (LiftedFamilyModel.evaluate
      (Reindex.pullProduct readings readings advance id advance_square familyGraphs familyInvariant encodedAtomSection)
      (valueMember readings source)).1 =
      HSet.kpair (readings.taggedReading (.inl (outcome source))) ∅ := by
  have application := Reindex.pullProduct_application readings readings advance id advance_square
    familyGraphs familyInvariant encodedAtomSection (valueMember readings source)
  have arguments := Reindex.baseMap_valueMember readings readings advance id advance_square source
  exact application.trans
    ((congrArg (fun argument => (LiftedFamilyModel.evaluate encodedAtomSection argument).1) arguments).trans
      ((atomSection_beta (advance source)).trans
        (congrArg (fun result => HSet.kpair (readings.taggedReading (.inl result)) ∅) (outcome_advance source))))

theorem cycle_identity_inhabited (result : Outcome.{u}) :
    Nonempty (identityCode readings familyGraphs (.cycle result false) (.cycle result true)).El :=
  (GeneratedFamilyEnclosure.identityCode_inhabited_iff_values _ _).mpr
    (cycle_values_eq result false true)

theorem model_identity_not_source_equation (result : Outcome.{u}) :
    Nonempty (identityCode readings familyGraphs (.cycle result false) (.cycle result true)).El ∧
      ¬ theory.Equiv (.cycle result false) (.cycle result true) := by
  refine ⟨cycle_identity_inhabited result, ?_⟩
  intro same
  exact Bool.noConfusion (State.cycle.inj same).2

/-- The two observation profiles induce different discrete model identities
on the same source states and preserve their authored event data separately. -/
theorem provenance_identity_depends_on_profile (result : Outcome.{u}) :
    Nonempty (identityCode (ProvenanceControls.plainReadings result)
        (valueGraph (ProvenanceControls.plainReadings result))
        ProvenanceControls.State.single ProvenanceControls.State.double).El ∧
      ¬ Nonempty (identityCode (ProvenanceControls.richReadings result)
        (valueGraph (ProvenanceControls.richReadings result))
        ProvenanceControls.State.single ProvenanceControls.State.double).El := by
  constructor
  · exact (GeneratedFamilyEnclosure.identityCode_inhabited_iff_values _ _).mpr
      (ProvenanceControls.plain_values_eq result)
  · exact fun inhabited => ProvenanceControls.rich_values_ne result
      ((GeneratedFamilyEnclosure.identityCode_inhabited_iff_values _ _).mp inhabited)

theorem provenance_events_remain_distinct (result : Outcome.{u}) :
    (Events.observation (ProvenanceControls.plainReadings result)
      (ProvenanceControls.occurrences result)).events (ProvenanceControls.doubleEvent result false) ≠
    (Events.observation (ProvenanceControls.plainReadings result)
      (ProvenanceControls.occurrences result)).events (ProvenanceControls.doubleEvent result true) := by
  intro same
  exact ProvenanceControls.double_events_distinct result
    (Events.events_injective (ProvenanceControls.plainReadings result)
      (ProvenanceControls.occurrences result) same)

end Controls

end Mettapedia.GSLT.ObservedFamilyEnclosure
