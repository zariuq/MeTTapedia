import Mettapedia.TypeTheory.ContextualSmallFamilyUniverseCoherence
import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions

/-!
# Small dependent families over wider contextual parameters

The parameter presheaf may live above the context universe. Dependent sums
are constructed from their actual fibre pairs. Dependent products use the
small category of future context arrows, carrying the root parameter along
each arrow, and retain every compatible future argument and result.

The resulting fibres remain in the original context universe. This is
closure of authored coherent small families, not a selection of coherent
presentations from pointwise smallness or a native universe axiom.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers

open CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w z

variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

def argumentStep {first second : base.Elements} (step : first ⟶ second)
    (argument : domain.obj first) :
    domain.elementsMk first argument ⟶ domain.elementsMk second (domain.map step argument) :=
  CategoryOfElements.homMk _ _ step rfl

theorem elementArrow_heq {E : Type w} [Category.{u} E] {family : E ⥤ Type z}
    {first otherFirst second otherSecond : family.Elements}
    (source : first = otherFirst) (target : second = otherSecond)
    (left : first ⟶ second) (right : otherFirst ⟶ otherSecond)
    (same : HEq left.val right.val) : HEq left right := by
  cases source
  cases target
  exact heq_of_eq (Subtype.ext (eq_of_heq same))

abbrev SumAt (point : base.Elements) : Type u :=
  Σ argument : domain.obj point, body.obj ⟨point, argument⟩

def sumMap {first second : base.Elements} (step : first ⟶ second)
    (term : SumAt domain body first) : SumAt domain body second :=
  ⟨domain.map step term.1, body.map (argumentStep domain step term.1) term.2⟩

theorem sumMap_id (point : base.Elements) (term : SumAt domain body point) :
    sumMap domain body (𝟙 point) term = term := by
  rcases term with ⟨argument, value⟩
  apply Sigma.ext (domain.map_id_apply point argument)
  have target : (⟨point, domain.map (𝟙 point) argument⟩ : domain.Elements) = ⟨point, argument⟩ :=
    congrArg (fun member => (⟨point, member⟩ : domain.Elements)) (domain.map_id_apply point argument)
  exact (ContextualSmallFamilyUniverse.familyMap_heq body rfl target _ (𝟙 (domain.elementsMk point argument))
    (elementArrow_heq rfl target _ _ HEq.rfl) value value HEq.rfl).trans
      (heq_of_eq (body.map_id_apply _ value))

theorem sumMap_comp {first middle last : base.Elements}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (term : SumAt domain body first) :
    sumMap domain body (earlier ≫ later) term =
      sumMap domain body later (sumMap domain body earlier term) := by
  rcases term with ⟨argument, value⟩
  apply Sigma.ext (domain.map_comp_apply earlier later argument)
  have target : (⟨last, domain.map (earlier ≫ later) argument⟩ : domain.Elements) =
      ⟨last, domain.map later (domain.map earlier argument)⟩ :=
    congrArg (fun member => (⟨last, member⟩ : domain.Elements))
      (domain.map_comp_apply earlier later argument)
  exact (ContextualSmallFamilyUniverse.familyMap_heq body rfl target _
    (argumentStep domain earlier argument ≫ argumentStep domain later (domain.map earlier argument))
    (elementArrow_heq rfl target _ _ HEq.rfl) value value HEq.rfl).trans
      (heq_of_eq (body.map_comp_apply _ _ value))

def sigma : base.Elements ⥤ Type u where
  obj := SumAt domain body
  map step := TypeCat.ofHom (sumMap domain body step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact sumMap_id domain body point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact sumMap_comp domain body earlier later

def overArguments (result : base.Elements ⥤ Type u) : domain.Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.restrict (CategoryOfElements.π domain) result

def sigmaCurry {result : base.Elements ⥤ Type u} (operation : NatTrans (sigma domain body) result) :
    NatTrans body (overArguments domain result) where
  app point := TypeCat.ofHom fun value => operation.app point.1 ⟨point.2, value⟩
  naturality first second step := by
    rcases first with ⟨first, argument⟩
    rcases second with ⟨second, nextArgument⟩
    rcases step with ⟨step, follows⟩
    change first ⟶ second at step
    change domain.map step argument = nextArgument at follows
    subst nextArgument
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg (fun map => map (⟨argument, value⟩ : SumAt domain body first))
      (operation.naturality step)

def sigmaUncurry {result : base.Elements ⥤ Type u} (operation : NatTrans body (overArguments domain result)) :
    NatTrans (sigma domain body) result where
  app point := TypeCat.ofHom fun term => operation.app ⟨point, term.1⟩ term.2
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, value⟩
    exact congrArg (fun map => map value) (operation.naturality (argumentStep domain step argument))

theorem sigma_uncurry_curry {result : base.Elements ⥤ Type u}
    (operation : NatTrans (sigma domain body) result) :
    sigmaUncurry domain body (sigmaCurry domain body operation) = operation := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  rintro ⟨_, _⟩
  rfl

theorem sigma_curry_uncurry {result : base.Elements ⥤ Type u}
    (operation : NatTrans body (overArguments domain result)) :
    sigmaCurry domain body (sigmaUncurry domain body operation) = operation := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro _
  rfl

def sigmaHomEquiv (result : base.Elements ⥤ Type u) :
    NatTrans (sigma domain body) result ≃ NatTrans body (overArguments domain result) where
  toFun := sigmaCurry domain body
  invFun := sigmaUncurry domain body
  left_inv := sigma_uncurry_curry domain body
  right_inv := sigma_curry_uncurry domain body

/-! ## Small complete future argument categories -/

abbrev futureDomain (point : base.Elements) :
    ContextualSmallFamilyUniverse.Code point.1 := ContextualSmallFamilyUniverse.familyCode domain point.1 point.2

def futureArguments (point : base.Elements) :
    (futureDomain domain point).Elements ⥤ domain.Elements where
  obj argument := ⟨(ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj argument.1, argument.2⟩
  map step := CategoryOfElements.homMk (F := domain) _ _
    ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step.1) step.2
  map_id _ := rfl
  map_comp _ _ := rfl

def futureBody (point : base.Elements) :
    (futureDomain domain point).Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.restrict (futureArguments domain point) body

abbrev ProductAt (point : base.Elements) : Type u :=
  (futureBody domain body point).sections

theorem futureDomain_prefix {first second : base.Elements} (step : first ⟶ second) :
    ContextualSmallFamilyUniverse.codeMap step.1 (futureDomain domain first) = futureDomain domain second := by
  have same := ContextualSmallFamilyUniverse.familyCode_naturality domain step.1 first.2
  rw [step.2] at same
  exact same

def prefixArguments {first second : base.Elements} (step : first ⟶ second) :
    (futureDomain domain second).Elements ⥤ (futureDomain domain first).Elements :=
  MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.compose
    (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.elementsTransport
      (futureDomain_prefix domain step).symm)
    (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.elementsMap
      (ContextualSmallFamilyUniverse.futurePrefix step.1) (futureDomain domain first))

theorem prefixArguments_context {first second : base.Elements} (step : first ⟶ second)
    (argument : (futureDomain domain second).Elements) :
    ((prefixArguments domain step).obj argument).1 =
      (ContextualSmallFamilyUniverse.futurePrefix step.1).obj argument.1 :=
  congrArg (ContextualSmallFamilyUniverse.futurePrefix step.1).obj
    (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.elementsTransport_context
      (futureDomain_prefix domain step).symm argument)

theorem prefixArguments_value {first second : base.Elements} (step : first ⟶ second)
    (argument : (futureDomain domain second).Elements) :
    HEq ((prefixArguments domain step).obj argument).2 argument.2 :=
  MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.elementsTransport_value
    (futureDomain_prefix domain step).symm argument

theorem prefixPoint_eq {first second : base.Elements} (step : first ⟶ second)
    (future : MaterialSets.Hypersets.PowerClassPresheafBaseChange.Future.Objects second.1) :
    (ContextualSmallFamilyUniverse.futureElement first.1 first.2).obj
        ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) =
      (ContextualSmallFamilyUniverse.futureElement second.1 second.2).obj future := by
  exact congrArg (fun value : base.obj future.1 => (⟨future.1, value⟩ : base.Elements))
    ((base.map_comp_apply step.1 future.2 first.2).trans (congrArg (base.map future.2) step.2))

theorem prefixArguments_embedding {first second : base.Elements} (step : first ⟶ second)
    (argument : (futureDomain domain second).Elements) :
    (futureArguments domain first).obj ((prefixArguments domain step).obj argument) =
      (futureArguments domain second).obj argument := by
  apply Sigma.ext
    ((congrArg (ContextualSmallFamilyUniverse.futureElement first.1 first.2).obj
      (prefixArguments_context domain step argument)).trans (prefixPoint_eq step argument.1))
  exact prefixArguments_value domain step argument

theorem futureArrow_value_heq {point : D}
    {first otherFirst second otherSecond : MaterialSets.Hypersets.PowerClassPresheafBaseChange.Future.Objects point}
    (source : first = otherFirst) (target : second = otherSecond)
    (left : first ⟶ second) (right : otherFirst ⟶ otherSecond) (same : HEq left right) :
    HEq left.val right.val := by
  cases source
  cases target
  cases eq_of_heq same
  rfl

theorem prefixArguments_arrow {first second : base.Elements} (step : first ⟶ second)
    {source target : (futureDomain domain second).Elements} (arrow : source ⟶ target) :
    HEq (((prefixArguments domain step).map arrow).1.1) arrow.1.1 := by
  exact futureArrow_value_heq
    (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.elementsTransport_context
      (futureDomain_prefix domain step).symm source)
    (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.elementsTransport_context
      (futureDomain_prefix domain step).symm target)
    _ _ (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.elementsTransport_arrow
      (futureDomain_prefix domain step).symm arrow)

theorem prefixArguments_embedding_arrow {first second : base.Elements} (step : first ⟶ second)
    {source target : (futureDomain domain second).Elements} (arrow : source ⟶ target) :
    HEq ((futureArguments domain first).map ((prefixArguments domain step).map arrow))
      ((futureArguments domain second).map arrow) := by
  apply elementArrow_heq (prefixArguments_embedding domain step source)
    (prefixArguments_embedding domain step target)
  exact ContextualSmallFamilyUniverse.elementsArrow_heq
    (congrArg Sigma.fst (prefixArguments_embedding domain step source))
    (congrArg Sigma.fst (prefixArguments_embedding domain step target))
    _ _ (prefixArguments_arrow domain step arrow)

theorem futureBody_prefix {first second : base.Elements} (step : first ⟶ second) :
    ContextualSmallFamilyUniverse.restrict (prefixArguments domain step) (futureBody domain body first) =
      futureBody domain body second := by
  refine Functor.hext (fun argument => congrArg body.obj (prefixArguments_embedding domain step argument)) ?_
  intro source target arrow
  exact ContextualSmallFamilyUniverse.familyArrow_heq body
    (prefixArguments_embedding domain step source) (prefixArguments_embedding domain step target)
    _ _ (prefixArguments_embedding_arrow domain step arrow)

theorem prefixArguments_id (point : base.Elements) (argument : (futureDomain domain point).Elements) :
    (prefixArguments domain (𝟙 point)).obj argument = argument := by
  have context : ((prefixArguments domain (𝟙 point)).obj argument).1 = argument.1 :=
    (prefixArguments_context domain (𝟙 point) argument).trans
      (congrArg (fun change => change.obj argument.1) (ContextualSmallFamilyUniverse.prefix_id point.1))
  exact Sigma.ext context (prefixArguments_value domain (𝟙 point) argument)

theorem prefixArguments_comp {first middle last : base.Elements}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (argument : (futureDomain domain last).Elements) :
    (prefixArguments domain (earlier ≫ later)).obj argument =
      (prefixArguments domain earlier).obj ((prefixArguments domain later).obj argument) := by
  have context : ((prefixArguments domain (earlier ≫ later)).obj argument).1 =
      ((prefixArguments domain earlier).obj ((prefixArguments domain later).obj argument)).1 :=
    (prefixArguments_context domain (earlier ≫ later) argument).trans
      ((congrArg (fun change => change.obj argument.1)
          (ContextualSmallFamilyUniverse.prefix_comp earlier.1 later.1)).trans
        ((congrArg (ContextualSmallFamilyUniverse.futurePrefix earlier.1).obj
          (prefixArguments_context domain later argument)).symm.trans
          (prefixArguments_context domain earlier ((prefixArguments domain later).obj argument)).symm))
  exact Sigma.ext context ((prefixArguments_value domain (earlier ≫ later) argument).trans
    ((prefixArguments_value domain earlier ((prefixArguments domain later).obj argument)).trans
      (prefixArguments_value domain later argument)).symm)

def productMap {first second : base.Elements} (step : first ⟶ second)
    (term : ProductAt domain body first) : ProductAt domain body second :=
  MaterialSets.Hypersets.PowerClassPresheafProducts.CP.castSection (futureBody_prefix domain body step)
    (MaterialSets.Hypersets.PowerClassPresheafProducts.CP.restrictSection
      (prefixArguments domain step) (futureBody domain body first) term)

theorem productMap_value {first second : base.Elements} (step : first ⟶ second)
    (term : ProductAt domain body first) (argument : (futureDomain domain second).Elements) :
    HEq ((productMap domain body step term).val argument)
      (term.val ((prefixArguments domain step).obj argument)) :=
  MaterialSets.Hypersets.PowerClassPresheafProducts.CP.castSection_value _ _ argument

theorem productMap_id (point : base.Elements) (term : ProductAt domain body point) :
    productMap domain body (𝟙 point) term = term := by
  apply Subtype.ext
  funext argument
  exact eq_of_heq ((productMap_value domain body (𝟙 point) term argument).trans
    (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.dependentValue_heq term.val
      (prefixArguments_id domain point argument)))

theorem productMap_comp {first middle last : base.Elements}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (term : ProductAt domain body first) :
    productMap domain body (earlier ≫ later) term =
      productMap domain body later (productMap domain body earlier term) := by
  apply Subtype.ext
  funext argument
  exact eq_of_heq ((productMap_value domain body (earlier ≫ later) term argument).trans
    ((MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.dependentValue_heq term.val
        (prefixArguments_comp domain earlier later argument)).trans
      ((productMap_value domain body earlier term ((prefixArguments domain later).obj argument)).symm.trans
        (productMap_value domain body later (productMap domain body earlier term) argument).symm)))

def pi : base.Elements ⥤ Type u where
  obj := ProductAt domain body
  map step := TypeCat.ofHom (productMap domain body step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact productMap_id domain body point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact productMap_comp domain body earlier later

/-! ## The dependent-product adjunction -/

def futureRootArrow (point : base.Elements) (argument : (futureDomain domain point).Elements) :
    point ⟶ ((futureArguments domain point).obj argument).1 :=
  CategoryOfElements.homMk (F := base) _ _ argument.1.2 rfl

theorem futureRootArrow_triangle (point : base.Elements)
    {source target : (futureDomain domain point).Elements} (arrow : source ⟶ target) :
    futureRootArrow domain point source ≫ ((futureArguments domain point).map arrow).1 =
      futureRootArrow domain point target := by
  apply CategoryOfElements.ext base
  exact arrow.1.2

theorem futureSecond_heq {point : D}
    {first second : MaterialSets.Hypersets.PowerClassPresheafBaseChange.Future.Objects point}
    (same : first = second) : HEq first.2 second.2 := by
  cases same
  rfl

theorem prefixRootArrow_heq {first second : base.Elements} (step : first ⟶ second)
    (argument : (futureDomain domain second).Elements) :
    HEq (futureRootArrow domain first ((prefixArguments domain step).obj argument))
      (step ≫ futureRootArrow domain second argument) :=
  ContextualSmallFamilyUniverse.elementsArrow_heq rfl
    (congrArg Sigma.fst (prefixArguments_embedding domain step argument)) _ _
    (futureSecond_heq (prefixArguments_context domain step argument))

theorem naturalApplication_heq {E : Type w} [Category.{u} E]
    {source target : E ⥤ Type z} (operation : NatTrans source target)
    {first second : E} (same : first = second)
    (value : source.obj first) (other : source.obj second) (values : HEq value other) :
    HEq (operation.app first value) (operation.app second other) := by
  cases same
  cases eq_of_heq values
  rfl

def piCurryValue {parameters : base.Elements ⥤ Type u}
    (operation : NatTrans (overArguments domain parameters) body)
    (point : base.Elements) (parameter : parameters.obj point) : ProductAt domain body point :=
  ⟨fun argument => operation.app ((futureArguments domain point).obj argument)
      (parameters.map (futureRootArrow domain point argument) parameter), by
    intro source target arrow
    have natural := congrArg
      (fun map => map (parameters.map (futureRootArrow domain point source) parameter))
      (operation.naturality ((futureArguments domain point).map arrow))
    change operation.app ((futureArguments domain point).obj target)
        (parameters.map ((futureArguments domain point).map arrow).1
          (parameters.map (futureRootArrow domain point source) parameter)) =
      body.map ((futureArguments domain point).map arrow)
        (operation.app ((futureArguments domain point).obj source)
          (parameters.map (futureRootArrow domain point source) parameter)) at natural
    exact natural.symm.trans
      (congrArg (operation.app ((futureArguments domain point).obj target))
        ((parameters.map_comp_apply _ _ parameter).symm.trans
          (congrArg (fun step => parameters.map step parameter)
            (futureRootArrow_triangle domain point arrow))))⟩

def piCurry {parameters : base.Elements ⥤ Type u}
    (operation : NatTrans (overArguments domain parameters) body) :
    NatTrans parameters (pi domain body) where
  app point := TypeCat.ofHom (piCurryValue domain body operation point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro parameter
    apply Subtype.ext
    funext argument
    apply eq_of_heq
    have parameterEq := ContextualSmallFamilyUniverse.familyMap_heq parameters rfl
      (congrArg Sigma.fst (prefixArguments_embedding domain step argument))
      (futureRootArrow domain first ((prefixArguments domain step).obj argument))
      (step ≫ futureRootArrow domain second argument) (prefixRootArrow_heq domain step argument)
      parameter parameter HEq.rfl
    have resultEq := naturalApplication_heq operation
      (prefixArguments_embedding domain step argument)
      (parameters.map (futureRootArrow domain first ((prefixArguments domain step).obj argument)) parameter)
      (parameters.map (futureRootArrow domain second argument) (parameters.map step parameter))
      (parameterEq.trans (heq_of_eq (parameters.map_comp_apply _ _ parameter)))
    exact resultEq.symm.trans
      (productMap_value domain body step (piCurryValue domain body operation first parameter) argument).symm

def currentArgument (point : base.Elements) (argument : domain.obj point) :
    (futureDomain domain point).Elements :=
  ⟨ContextualSmallFamilyUniverse.root point.1,
    (ContextualSmallFamilyUniverse.evaluationEquiv domain point.1 point.2).symm argument⟩

theorem currentArgument_value (point : base.Elements) (argument : domain.obj point) :
    HEq (currentArgument domain point argument).2 argument :=
  ContextualSmallFamilyUniverse.cast_heq _ _

theorem currentArgument_embedding (point : base.Elements) (argument : domain.obj point) :
    (futureArguments domain point).obj (currentArgument domain point argument) = ⟨point, argument⟩ :=
  Sigma.ext (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2)
    (currentArgument_value domain point argument)

theorem futureRootArrow_current (point : base.Elements) (argument : domain.obj point) :
    HEq (futureRootArrow domain point (currentArgument domain point argument)) (𝟙 point) :=
  ContextualSmallFamilyUniverse.elementsArrow_heq rfl
    (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2) _ _ HEq.rfl

def evaluateValue (point : base.Elements) (term : ProductAt domain body point)
    (argument : domain.obj point) : body.obj ⟨point, argument⟩ :=
  cast (congrArg body.obj (currentArgument_embedding domain point argument))
    (term.val (currentArgument domain point argument))

theorem evaluateValue_heq (point : base.Elements) (term : ProductAt domain body point)
    (argument : domain.obj point) : HEq (evaluateValue domain body point term argument)
      (term.val (currentArgument domain point argument)) :=
  ContextualSmallFamilyUniverse.cast_heq _ _

def currentFutureArrow {first second : base.Elements} (step : first ⟶ second)
    (argument : domain.obj first) :
    (currentArgument domain first argument).1 ⟶
      ((prefixArguments domain step).obj (currentArgument domain second (domain.map step argument))).1 :=
  cast (congrArg (fun target => ContextualSmallFamilyUniverse.root first.1 ⟶ target)
    (prefixArguments_context domain step (currentArgument domain second (domain.map step argument))).symm)
    (ContextualSmallFamilyUniverse.rootArrow step.1)

theorem currentFutureArrow_value {first second : base.Elements} (step : first ⟶ second)
    (argument : domain.obj first) : HEq (currentFutureArrow domain step argument).val step.val :=
  futureArrow_value_heq rfl
    (prefixArguments_context domain step (currentArgument domain second (domain.map step argument)))
    _ _ (ContextualSmallFamilyUniverse.cast_heq _ _)

theorem prefixCurrent_embedding {first second : base.Elements} (step : first ⟶ second)
    (argument : domain.obj first) :
    (futureArguments domain first).obj
      ((prefixArguments domain step).obj (currentArgument domain second (domain.map step argument))) =
      domain.elementsMk second (domain.map step argument) :=
  (prefixArguments_embedding domain step _).trans (currentArgument_embedding domain second _)

def currentArgumentStep {first second : base.Elements} (step : first ⟶ second)
    (argument : domain.obj first) :
    currentArgument domain first argument ⟶
      (prefixArguments domain step).obj (currentArgument domain second (domain.map step argument)) :=
  CategoryOfElements.homMk (F := futureDomain domain first) _ _
    (currentFutureArrow domain step argument) (by
      apply eq_of_heq
      exact (ContextualSmallFamilyUniverse.familyMap_heq domain
        (congrArg Sigma.fst (currentArgument_embedding domain first argument))
        (congrArg Sigma.fst (prefixCurrent_embedding domain step argument))
        ((ContextualSmallFamilyUniverse.futureElement first.1 first.2).map
          (currentFutureArrow domain step argument)) step
        (ContextualSmallFamilyUniverse.elementsArrow_heq
          (congrArg Sigma.fst (currentArgument_embedding domain first argument))
          (congrArg Sigma.fst (prefixCurrent_embedding domain step argument)) _ _
          (currentFutureArrow_value domain step argument))
        (currentArgument domain first argument).2 argument (currentArgument_value domain first argument)).trans
          ((prefixArguments_value domain step (currentArgument domain second (domain.map step argument))).trans
            (currentArgument_value domain second (domain.map step argument))).symm)

theorem currentArgumentStep_embedding {first second : base.Elements} (step : first ⟶ second)
    (argument : domain.obj first) :
    HEq ((futureArguments domain first).map (currentArgumentStep domain step argument))
      (argumentStep domain step argument) :=
  elementArrow_heq (currentArgument_embedding domain first argument)
    (prefixCurrent_embedding domain step argument) _ _
    (ContextualSmallFamilyUniverse.elementsArrow_heq
      (congrArg Sigma.fst (currentArgument_embedding domain first argument))
      (congrArg Sigma.fst (prefixCurrent_embedding domain step argument)) _ _
      (currentFutureArrow_value domain step argument))

theorem evaluateValue_natural {first second : base.Elements} (step : first ⟶ second)
    (term : ProductAt domain body first) (argument : domain.obj first) :
    body.map (argumentStep domain step argument) (evaluateValue domain body first term argument) =
      evaluateValue domain body second (productMap domain body step term) (domain.map step argument) := by
  have mapped := ContextualSmallFamilyUniverse.familyMap_heq body
    (currentArgument_embedding domain first argument) (prefixCurrent_embedding domain step argument)
    ((futureArguments domain first).map (currentArgumentStep domain step argument))
    (argumentStep domain step argument) (currentArgumentStep_embedding domain step argument)
    (term.val (currentArgument domain first argument)) (evaluateValue domain body first term argument)
    (evaluateValue_heq domain body first term argument).symm
  exact eq_of_heq (mapped.symm.trans
    ((heq_of_eq (term.property (currentArgumentStep domain step argument))).trans
      ((productMap_value domain body step term
          (currentArgument domain second (domain.map step argument))).symm.trans
        (evaluateValue_heq domain body second (productMap domain body step term)
          (domain.map step argument)).symm)))

def piUncurry {parameters : base.Elements ⥤ Type u} (operation : NatTrans parameters (pi domain body)) :
    NatTrans (overArguments domain parameters) body where
  app point := TypeCat.ofHom fun parameter => evaluateValue domain body point.1 (operation.app point.1 parameter) point.2
  naturality first second step := by
    rcases first with ⟨first, argument⟩
    rcases second with ⟨second, nextArgument⟩
    rcases step with ⟨step, follows⟩
    change first ⟶ second at step
    change domain.map step argument = nextArgument at follows
    subst nextArgument
    apply ConcreteCategory.hom_ext
    intro parameter
    have natural := (congrArg (fun map => map parameter) (operation.naturality step))
    change operation.app second (parameters.map step parameter) =
      productMap domain body step (operation.app first parameter) at natural
    exact (congrArg (fun term => evaluateValue domain body second term (domain.map step argument)) natural).trans
      (evaluateValue_natural domain body step (operation.app first parameter) argument).symm

theorem pi_uncurry_curry {parameters : base.Elements ⥤ Type u}
    (operation : NatTrans (overArguments domain parameters) body) :
    piUncurry domain body (piCurry domain body operation) = operation := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro parameter
  have parameterEq := ContextualSmallFamilyUniverse.familyMap_heq parameters rfl
    (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1.1 point.1.2)
    (futureRootArrow domain point.1 (currentArgument domain point.1 point.2)) (𝟙 point.1)
    (futureRootArrow_current domain point.1 point.2) parameter parameter HEq.rfl
  exact eq_of_heq ((evaluateValue_heq domain body point.1
    (piCurryValue domain body operation point.1 parameter) point.2).trans
    (naturalApplication_heq operation (currentArgument_embedding domain point.1 point.2)
      (parameters.map (futureRootArrow domain point.1 (currentArgument domain point.1 point.2)) parameter)
      parameter (parameterEq.trans (heq_of_eq (parameters.map_id_apply point.1 parameter)))))

theorem prefixCurrent_returns (point : base.Elements) (argument : (futureDomain domain point).Elements) :
    (prefixArguments domain (futureRootArrow domain point argument)).obj
      (currentArgument domain ((futureArguments domain point).obj argument).1 argument.2) = argument := by
  have context :
      ((prefixArguments domain (futureRootArrow domain point argument)).obj
        (currentArgument domain ((futureArguments domain point).obj argument).1 argument.2)).1 = argument.1 :=
    (prefixArguments_context domain (futureRootArrow domain point argument) _).trans
      (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Future.objects_ext rfl
        (heq_of_eq (Category.comp_id argument.1.2)))
  exact Sigma.ext context
    ((prefixArguments_value domain (futureRootArrow domain point argument) _).trans
      (currentArgument_value domain ((futureArguments domain point).obj argument).1 argument.2))

theorem pi_curry_uncurry {parameters : base.Elements ⥤ Type u}
    (operation : NatTrans parameters (pi domain body)) :
    piCurry domain body (piUncurry domain body operation) = operation := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro parameter
  apply Subtype.ext
  funext argument
  have natural := congrArg (fun map => map parameter)
    (operation.naturality (futureRootArrow domain point argument))
  change operation.app ((futureArguments domain point).obj argument).1
      (parameters.map (futureRootArrow domain point argument) parameter) =
    productMap domain body (futureRootArrow domain point argument) (operation.app point parameter) at natural
  have evaluationEq := congrArg (fun term =>
    evaluateValue domain body ((futureArguments domain point).obj argument).1 term argument.2) natural
  exact eq_of_heq ((heq_of_eq evaluationEq).trans
    ((evaluateValue_heq domain body ((futureArguments domain point).obj argument).1
        (productMap domain body (futureRootArrow domain point argument) (operation.app point parameter)) argument.2).trans
      ((productMap_value domain body (futureRootArrow domain point argument) (operation.app point parameter)
          (currentArgument domain ((futureArguments domain point).obj argument).1 argument.2)).trans
        (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.dependentValue_heq
          (operation.app point parameter).val (prefixCurrent_returns domain point argument)))))

def piHomEquiv (parameters : base.Elements ⥤ Type u) :
    NatTrans (overArguments domain parameters) body ≃ NatTrans parameters (pi domain body) where
  toFun := piCurry domain body
  invFun := piUncurry domain body
  left_inv := pi_uncurry_curry domain body
  right_inv := pi_curry_uncurry domain body

def identityNat {E : Type w} [Category.{u} E] (family : E ⥤ Type z) : NatTrans family family where
  app _ := TypeCat.ofHom id
  naturality _ _ _ := rfl

def evaluate : NatTrans (overArguments domain (pi domain body)) body :=
  piUncurry domain body (identityNat (pi domain body))

def unit (parameters : base.Elements ⥤ Type u) :
    NatTrans parameters (pi domain (overArguments domain parameters)) :=
  piCurry domain (overArguments domain parameters) (identityNat (overArguments domain parameters))

theorem evaluate_value (point : domain.Elements) (term : ProductAt domain body point.1) :
    (evaluate domain body).app point term = evaluateValue domain body point.1 term point.2 := rfl

theorem curry_evaluate : piCurry domain body (evaluate domain body) = identityNat (pi domain body) :=
  pi_curry_uncurry domain body (identityNat (pi domain body))

theorem uncurry_unit (parameters : base.Elements ⥤ Type u) :
    piUncurry domain (overArguments domain parameters) (unit domain parameters) =
      identityNat (overArguments domain parameters) :=
  pi_uncurry_curry domain (overArguments domain parameters) (identityNat (overArguments domain parameters))

def composeNat {E : Type w} [Category.{u} E] {first middle last : E ⥤ Type z}
    (earlier : NatTrans first middle) (later : NatTrans middle last) : NatTrans first last where
  app point := TypeCat.ofHom fun value => later.app point (earlier.app point value)
  naturality firstPoint lastPoint step := by
    apply ConcreteCategory.hom_ext
    intro value
    have left := congrArg (fun map => map value) (earlier.naturality step)
    have right := congrArg (fun map => map (earlier.app firstPoint value)) (later.naturality step)
    exact (congrArg (later.app lastPoint) left).trans right

def overMap {first second : base.Elements ⥤ Type u} (operation : NatTrans first second) :
    NatTrans (overArguments domain first) (overArguments domain second) where
  app point := operation.app point.1
  naturality _ _ step := operation.naturality step.1

theorem piCurry_natural_parameters {first second : base.Elements ⥤ Type u}
    (earlier : NatTrans first second) (operation : NatTrans (overArguments domain second) body) :
    piCurry domain body (composeNat (overMap domain earlier) operation) =
      composeNat earlier (piCurry domain body operation) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro parameter
  apply Subtype.ext
  funext argument
  exact congrArg (operation.app ((futureArguments domain point).obj argument))
    (congrArg (fun map => map parameter) (earlier.naturality (futureRootArrow domain point argument)))

theorem evaluate_future (point : base.Elements) (term : ProductAt domain body point)
    (argument : (futureDomain domain point).Elements) :
    evaluateValue domain body ((futureArguments domain point).obj argument).1
        (productMap domain body (futureRootArrow domain point argument) term) argument.2 =
      term.val argument :=
  eq_of_heq ((evaluateValue_heq domain body ((futureArguments domain point).obj argument).1
      (productMap domain body (futureRootArrow domain point argument) term) argument.2).trans
    ((productMap_value domain body (futureRootArrow domain point argument) term
        (currentArgument domain ((futureArguments domain point).obj argument).1 argument.2)).trans
      (MaterialSets.Hypersets.PowerClassPresheafBaseChange.Cat.dependentValue_heq term.val
        (prefixCurrent_returns domain point argument))))

def piMap {other : domain.Elements ⥤ Type u} (operation : NatTrans body other) :
    NatTrans (pi domain body) (pi domain other) :=
  piCurry domain other (composeNat (evaluate domain body) operation)

theorem piMap_value {other : domain.Elements ⥤ Type u} (operation : NatTrans body other)
    (point : base.Elements) (term : ProductAt domain body point) (argument : (futureDomain domain point).Elements) :
    ((piMap domain body operation).app point term).val argument =
      operation.app ((futureArguments domain point).obj argument) (term.val argument) :=
  congrArg (operation.app ((futureArguments domain point).obj argument)) (evaluate_future domain body point term argument)

theorem piCurry_natural_body {parameters : base.Elements ⥤ Type u}
    {other : domain.Elements ⥤ Type u} (operation : NatTrans (overArguments domain parameters) body)
    (later : NatTrans body other) :
    piCurry domain other (composeNat operation later) =
      composeNat (piCurry domain body operation) (piMap domain body later) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro parameter
  apply Subtype.ext
  funext argument
  exact (piMap_value domain body later point (piCurryValue domain body operation point parameter) argument).symm

theorem piMap_id : piMap domain body (identityNat body) = identityNat (pi domain body) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro term
  apply Subtype.ext
  funext argument
  exact piMap_value domain body (identityNat body) point term argument

theorem piMap_comp {middle last : domain.Elements ⥤ Type u}
    (earlier : NatTrans body middle) (later : NatTrans middle last) :
    piMap domain body (composeNat earlier later) =
      composeNat (piMap domain body earlier) (piMap domain middle later) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro term
  apply Subtype.ext
  funext argument
  exact (piMap_value domain body (composeNat earlier later) point term argument).trans
    ((congrArg (later.app ((futureArguments domain point).obj argument))
      (piMap_value domain body earlier point term argument)).symm.trans
        (piMap_value domain middle later point ((piMap domain body earlier).app point term) argument).symm)

theorem unit_counit_left (parameters : base.Elements ⥤ Type u) :
    composeNat (overMap domain (unit domain parameters))
        (evaluate domain (overArguments domain parameters)) = identityNat (overArguments domain parameters) :=
  uncurry_unit domain parameters

theorem unit_counit_right :
    composeNat (unit domain (pi domain body)) (piMap domain (overArguments domain (pi domain body))
      (evaluate domain body)) = identityNat (pi domain body) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro term
  apply Subtype.ext
  funext argument
  exact (piMap_value domain (overArguments domain (pi domain body)) (evaluate domain body) point
      ((unit domain (pi domain body)).app point term) argument).trans (evaluate_future domain body point term argument)

end Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers
