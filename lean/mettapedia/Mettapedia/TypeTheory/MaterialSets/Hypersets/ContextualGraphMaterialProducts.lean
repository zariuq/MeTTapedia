import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyComparison
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyProducts

/-!
# Material dependent products of actual contextual element denotations

The native product consists of all naturally compatible future sections,
at the original universe bound. Each product term denotes its
actual graph of ordered argument/result pairs. Those pairs retain the
declared material bodies of both components, and the enclosing product
set attaches the resulting full graphs rather than terminal receipt tags.
Single-valued material application additionally requires compatibility of
argument and output readings; that refinement is constructed separately.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialProducts

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : Family base) (body : Family (total domain.native))

abbrev nativeProduct : base.Elements ⥤ Type u := piDisplayed domain.native body.native

/-- Arguments remain original-small, including above a parameter that
carries a complete future section. -/
def arguments : (total (nativeProduct domain body)).Elements ⥤ Type u :=
  restrict (elementMap (projection (nativeProduct domain body))) domain.native

def argumentTarget : NaturalHom (total (arguments domain body)) (total domain.native) where
  app _ receipt := ⟨receipt.1.1, receipt.2⟩
  naturality _ _ := rfl

def evaluated (point : base.Elements) (function : (nativeProduct domain body).obj point)
    (argument : domain.native.obj point) :
    body.native.obj ((flatten domain.native).obj ⟨point, argument⟩) :=
  ContextualSmallFamilyTypeFormers.evaluateValue domain.native (indexedBody domain.native body.native)
    point function argument

theorem evaluated_natural {first second : base.Elements} (step : first ⟶ second)
    (function : (nativeProduct domain body).obj first) (argument : domain.native.obj first) :
    body.native.map ((flatten domain.native).map
      (ContextualSmallFamilyTypeFormers.argumentStep domain.native step argument))
      (evaluated domain body first function argument) =
    evaluated domain body second ((nativeProduct domain body).map step function)
      (domain.native.map step argument) :=
  ContextualSmallFamilyTypeFormers.evaluateValue_natural domain.native
    (indexedBody domain.native body.native) step function argument

def resultTarget : NaturalHom (total (arguments domain body)) (total body.native) where
  app point receipt :=
    ⟨⟨receipt.1.1, receipt.2⟩, evaluated domain body ⟨point, receipt.1.1⟩ receipt.1.2 receipt.2⟩
  naturality {first second} arrival receipt := by
    let step := CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1⟩
      ⟨second, base.map arrival receipt.1.1⟩ arrival rfl
    change (⟨⟨base.map arrival receipt.1.1, domain.native.map step receipt.2⟩,
      body.native.map ((flatten domain.native).map
        (ContextualSmallFamilyTypeFormers.argumentStep domain.native step receipt.2))
        (evaluated domain body ⟨first, receipt.1.1⟩ receipt.1.2 receipt.2)⟩ :
        (total body.native).obj second) =
      ⟨⟨base.map arrival receipt.1.1, domain.native.map step receipt.2⟩,
        evaluated domain body ⟨second, base.map arrival receipt.1.1⟩
          ((nativeProduct domain body).map step receipt.1.2) (domain.native.map step receipt.2)⟩
    exact congrArg (fun value =>
      (⟨⟨base.map arrival receipt.1.1, domain.native.map step receipt.2⟩, value⟩ :
        (total body.native).obj second)) (evaluated_natural domain body step receipt.1.2 receipt.2)

def applicationReading : NaturalHom (total (arguments domain body)) (values D) :=
  ContextualGraphOrderedPairs.orderedReading
    ((argumentTarget domain body).comp domain.reading)
    ((resultTarget domain body).comp body.reading)

def functionReading : NaturalHom (total (nativeProduct domain body)) (values D) :=
  ContextualGraphFamilyBodies.parent (arguments domain body) (applicationReading domain body)

/-- A product term denotes the set of its actual ordered applications,
using the constructed complete future section carrier. -/
def pi : Family base where
  native := nativeProduct domain body
  reading := functionReading domain body

def literal (family : Family base) : base.Elements ⥤ Type u :=
  ContextualGraphFamilyBodies.literal family.native family.reading

def carrier (family : Family base) : NaturalHom base (values D) :=
  ContextualGraphFamilyBodies.parent family.native family.reading

def sectionDecoder (family : Family base) : (literal family).sections ≃ family.native.sections :=
  ContextualGraphFamilyBodies.sectionDecoder family.native family.reading

def productElement (point : base.Elements) (function : (nativeProduct domain body).obj point) :
    Value D point.1 := termValue (pi domain body) point function

theorem application_value (point : base.Elements) (function : (nativeProduct domain body).obj point)
    (argument : domain.native.obj point) :
    (applicationReading domain body).app point.1 ⟨⟨point.2, function⟩, argument⟩ =
      ContextualGraphOrderedPairs.orderedPair (termValue domain point argument)
        (termValue body ((flatten domain.native).obj ⟨point, argument⟩)
          (evaluated domain body point function argument)) := rfl

def applicationMember (point : base.Elements) (function : (nativeProduct domain body).obj point)
    (argument : domain.native.obj point) :
    Member (ContextualGraphOrderedPairs.orderedPair (termValue domain point argument)
      (termValue body ((flatten domain.native).obj ⟨point, argument⟩)
        (evaluated domain body point function argument))) (productElement domain body point function) :=
  ContextualGraphFamilyBodyComparison.memberIntro (arguments domain body) (applicationReading domain body)
    ⟨point.1, ⟨point.2, function⟩⟩ _ argument (Equal.refl _)

def applicationDecode (point : base.Elements) (function : (nativeProduct domain body).obj point)
    (element : Value D point.1) (membership : Member element (productElement domain body point function)) :
    Σ argument : domain.native.obj point,
      Equal element (ContextualGraphOrderedPairs.orderedPair (termValue domain point argument)
        (termValue body ((flatten domain.native).obj ⟨point, argument⟩)
          (evaluated domain body point function argument))) :=
  ContextualGraphFamilyBodyComparison.memberDecode (arguments domain body) (applicationReading domain body)
    ⟨point.1, ⟨point.2, function⟩⟩ element membership

def futurePoint (point : base.Elements) (future : ContextualGraphRealizers.Future point.1) : base.Elements :=
  ⟨future.1, base.map future.2 point.2⟩

def futureStep (point : base.Elements) (future : ContextualGraphRealizers.Future point.1) :
    point ⟶ futurePoint point future := CategoryOfElements.homMk _ _ future.2 rfl

def resultValue (point : base.Elements) (function : (nativeProduct domain body).obj point)
    (argument : domain.native.obj point) : Value D point.1 :=
  termValue body ((flatten domain.native).obj ⟨point, argument⟩)
    (evaluated domain body point function argument)

/-- Every future application is matched by an actual argument receipt,
with both component readings retained. -/
abbrev ApplicationMatching (point : base.Elements)
    (first second : (nativeProduct domain body).obj point) : Type u :=
  ∀ (future : ContextualGraphRealizers.Future point.1)
    (argument : domain.native.obj (futurePoint point future)),
    Σ matched : domain.native.obj (futurePoint point future),
      Equal (termValue domain (futurePoint point future) argument)
        (termValue domain (futurePoint point future) matched) ×
      Equal (resultValue domain body (futurePoint point future)
        ((nativeProduct domain body).map (futureStep point future) first) argument)
        (resultValue domain body (futurePoint point future)
          ((nativeProduct domain body).map (futureStep point future) second) matched)

def applicationMatching (point : base.Elements) (first second : (nativeProduct domain body).obj point)
    (same : Equal (productElement domain body point first) (productElement domain body point second)) :
    ApplicationMatching domain body point first second := by
  intro future argument
  let step := futureStep point future
  let next := futurePoint point future
  let left := (nativeProduct domain body).map step first
  let right := (nativeProduct domain body).map step second
  have futureSame : Equal (productElement domain body next left) (productElement domain body next right) :=
    (Equal.ofEq (termValue_move (pi domain body) step first)).symm.trans
      ((Equal.restrict future.2 same).trans (Equal.ofEq (termValue_move (pi domain body) step second)))
  let matched := applicationDecode domain body next right _
    (Member.transportParent futureSame (applicationMember domain body next left argument))
  exact ⟨matched.1, ContextualGraphOrderedPairs.orderedPairReflectFirst matched.2,
    ContextualGraphOrderedPairs.orderedPairReflectSecond matched.2⟩

def applicationMembers (point : base.Elements) (first second : (nativeProduct domain body).obj point)
    (matching : ApplicationMatching domain body point first second)
    (target : D) (arrival : point.1 ⟶ target) (element : Value D target)
    (membership : Member element (move D arrival (productElement domain body point first))) :
    Member element (move D arrival (productElement domain body point second)) := by
  let future : ContextualGraphRealizers.Future point.1 := ⟨target, arrival⟩
  let step := futureStep point future
  let next := futurePoint point future
  let left := (nativeProduct domain body).map step first
  let right := (nativeProduct domain body).map step second
  let original := applicationDecode domain body next left element
    (Member.transportParent (Equal.ofEq (termValue_move (pi domain body) step first)) membership)
  let response := matching future original.1
  exact Member.transportParent (Equal.ofEq (termValue_move (pi domain body) step second)).symm
    (Member.transportChild
      (original.2.trans (ContextualGraphOrderedPairs.orderedPairCongr response.2.1 response.2.2)).symm
      (applicationMember domain body next right response.1))

def productEquality (point : base.Elements) (first second : (nativeProduct domain body).obj point)
    (forth : ApplicationMatching domain body point first second)
    (back : ApplicationMatching domain body point second first) :
    Equal (productElement domain body point first) (productElement domain body point second) :=
  extensionality (applicationMembers domain body point first second forth)
    (applicationMembers domain body point second first back)

theorem product_kernel (point : base.Elements) (first second : (nativeProduct domain body).obj point) :
    Nonempty (Equal (productElement domain body point first) (productElement domain body point second)) ↔
      Nonempty (ApplicationMatching domain body point first second ×
        ApplicationMatching domain body point second first) :=
  ⟨fun ⟨same⟩ => ⟨applicationMatching domain body point first second same,
      applicationMatching domain body point second first same.symm⟩,
    fun ⟨matching⟩ => ⟨productEquality domain body point first second matching.1 matching.2⟩⟩

/-- A native section descends to a single-valued material operation only
when equal argument readings have equal result readings. -/
abbrev ApplicationCompatible (point : base.Elements) (function : (nativeProduct domain body).obj point) : Type u :=
  ∀ (first second : domain.native.obj point),
    Equal (termValue domain point first) (termValue domain point second) →
      Equal (resultValue domain body point function first) (resultValue domain body point function second)

def applicationCongr (point : base.Elements) (first second : (nativeProduct domain body).obj point)
    (firstArgument secondArgument : domain.native.obj point)
    (sameFunction : Equal (productElement domain body point first) (productElement domain body point second))
    (sameArgument : Equal (termValue domain point firstArgument) (termValue domain point secondArgument))
    (compatible : ApplicationCompatible domain body point second) :
    Equal (resultValue domain body point first firstArgument) (resultValue domain body point second secondArgument) := by
  let response := applicationDecode domain body point second _
    (Member.transportParent sameFunction (applicationMember domain body point first firstArgument))
  exact (ContextualGraphOrderedPairs.orderedPairReflectSecond response.2).trans
    (compatible response.1 secondArgument
      ((ContextualGraphOrderedPairs.orderedPairReflectFirst response.2).symm.trans sameArgument))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialProducts
