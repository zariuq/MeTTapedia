import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetConstructors
import Mettapedia.TypeTheory.ContextualProductComparison
import Mettapedia.TypeTheory.ContextualSumComparison

/-!
# Actual small dependent receipt families in the realized graph model

The children of a constructed disjoint union decode bijectively to its
retained index. Dependent sums and products are constructed from genuine
small pair and function carriers. Product presentations contain the full
graphs of their sections. Their root receipts, unlike bare membership,
retain which section was authored.

The decoders compare these actual carriers and their whole sections with
the existing native dependent-family CwF. Abstraction, application,
beta/eta and parameter substitution follow through the inverse decoders.
They concern retained receipts; material equality does not identify an
arbitrary native family or erase its argument occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedReceiptFamilies

open GraphBisimulationRealizers GraphSetRealization GraphSetOperations GraphRealizedSetConstructors
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison

universe u

abbrev Receipts (graph : Graph.{u}) : Type u := Child graph.edge graph.point

/-- Literal root children retain the family index even when the material
values at two indices have equal extensions. -/
def supDecode {Index : Type u} (graphs : Index → Graph.{u}) :
    Receipts (AccessiblePointedGraph.sup graphs) ≃ Index where
  toFun := Sup.index graphs
  invFun := Sup.child graphs
  left_inv receipt := Subtype.ext (Sup.node graphs receipt).symm
  right_inv _ := rfl

def orderedPair (first second : Graph.{u}) : Graph.{u} :=
  pair (singleton first) (pair first second)

variable (domain : Graph.{u}) (body : Receipts domain → Graph.{u})

abbrev SumCarrier : Type u := Σ argument : Receipts domain, Receipts (body argument)
abbrev ProductCarrier : Type u := (argument : Receipts domain) → Receipts (body argument)

def sigmaGraph : Graph.{u} :=
  AccessiblePointedGraph.sup (fun value : SumCarrier domain body =>
    orderedPair (domain.repoint value.1.val) ((body value.1).repoint value.2.val))

def sigmaDecode : Receipts (sigmaGraph domain body) ≃ SumCarrier domain body :=
  supDecode _

def sectionGraph (sectionValue : ProductCarrier domain body) : Graph.{u} :=
  AccessiblePointedGraph.sup (fun argument : Receipts domain =>
    orderedPair (domain.repoint argument.val) ((body argument).repoint (sectionValue argument).val))

/-- The function carrier is constructed at the original universe; no
externally supplied small section carrier is assumed. -/
def piGraph : Graph.{u} := AccessiblePointedGraph.sup (sectionGraph domain body)

def piDecode : Receipts (piGraph domain body) ≃ ProductCarrier domain body := supDecode _

def abstraction (sectionValue : ProductCarrier domain body) : Receipts (piGraph domain body) :=
  (piDecode domain body).symm sectionValue

def application (function : Receipts (piGraph domain body)) (argument : Receipts domain) :
    Receipts (body argument) := piDecode domain body function argument

theorem application_abstraction (sectionValue : ProductCarrier domain body) (argument : Receipts domain) :
    application domain body (abstraction domain body sectionValue) argument = sectionValue argument :=
  congrFun ((piDecode domain body).apply_symm_apply sectionValue) argument

theorem abstraction_application (function : Receipts (piGraph domain body)) :
    abstraction domain body (application domain body function) = function :=
  (piDecode domain body).symm_apply_apply function

def pairReceipts (argument : Receipts domain) (value : Receipts (body argument)) :
    Receipts (sigmaGraph domain body) := (sigmaDecode domain body).symm ⟨argument, value⟩

theorem sigma_pair_decode (argument : Receipts domain) (value : Receipts (body argument)) :
    sigmaDecode domain body (pairReceipts domain body argument value) = ⟨argument, value⟩ :=
  (sigmaDecode domain body).apply_symm_apply _

theorem sigma_eta (receipt : Receipts (sigmaGraph domain body)) :
    pairReceipts domain body (sigmaDecode domain body receipt).1 (sigmaDecode domain body receipt).2 = receipt :=
  (sigmaDecode domain body).symm_apply_apply receipt

section Contexts

variable {Context Other Third : Type u}
variable (domains : Context → Graph.{u})
variable (bodies : (context : Context) → Receipts (domains context) → Graph.{u})

def nativeDomain : familiesCwf.Ty Context := fun context => Receipts (domains context)

def nativeBody : familiesCwf.Ty (familiesCwf.ext Context (nativeDomain domains)) :=
  fun point => Receipts (bodies point.1 point.2)

def nativeProductComparison (context : Context) :
    Receipts (piGraph (domains context) (bodies context)) ≃
      (familiesProducts.pi (nativeDomain domains) (nativeBody domains bodies)) context :=
  piDecode _ _

def nativeSumComparison (context : Context) :
    Receipts (sigmaGraph (domains context) (bodies context)) ≃
      (familiesSums.sigma (nativeDomain domains) (nativeBody domains bodies)) context :=
  sigmaDecode _ _

def lambdaSections (bodySection : (context : Context) → ProductCarrier (domains context) (bodies context)) :
    (context : Context) → Receipts (piGraph (domains context) (bodies context)) :=
  fun context => abstraction _ _ (bodySection context)

def applySections (function : (context : Context) → Receipts (piGraph (domains context) (bodies context)))
    (argument : (context : Context) → Receipts (domains context)) :
    (context : Context) → Receipts (bodies context (argument context)) :=
  fun context => application _ _ (function context) (argument context)

theorem sections_beta (bodySection : (context : Context) → ProductCarrier (domains context) (bodies context))
    (argument : (context : Context) → Receipts (domains context)) :
    applySections domains bodies (lambdaSections domains bodies bodySection) argument =
      fun context => bodySection context (argument context) := by
  funext context
  exact application_abstraction _ _ _ _

theorem sections_eta (function : (context : Context) → Receipts (piGraph (domains context) (bodies context))) :
    lambdaSections domains bodies (fun context => application _ _ (function context)) = function := by
  funext context
  exact abstraction_application _ _ _

def productSectionsEquiv :
    ((context : Context) → Receipts (piGraph (domains context) (bodies context))) ≃
      familiesCwf.Tm Context (familiesProducts.pi (nativeDomain domains) (nativeBody domains bodies)) where
  toFun function context := nativeProductComparison domains bodies context (function context)
  invFun function context := (nativeProductComparison domains bodies context).symm (function context)
  left_inv function := funext fun context => (nativeProductComparison domains bodies context).symm_apply_apply (function context)
  right_inv function := funext fun context => (nativeProductComparison domains bodies context).apply_symm_apply (function context)

def sumSectionsEquiv :
    ((context : Context) → Receipts (sigmaGraph (domains context) (bodies context))) ≃
      familiesCwf.Tm Context (familiesSums.sigma (nativeDomain domains) (nativeBody domains bodies)) where
  toFun term context := nativeSumComparison domains bodies context (term context)
  invFun term context := (nativeSumComparison domains bodies context).symm (term context)
  left_inv term := funext fun context => (nativeSumComparison domains bodies context).symm_apply_apply (term context)
  right_inv term := funext fun context => (nativeSumComparison domains bodies context).apply_symm_apply (term context)

theorem product_decode_substitution (change : Other → Context) (point : Other)
    (receipt : Receipts (piGraph (domains (change point)) (bodies (change point)))) :
    nativeProductComparison (domains ∘ change) (fun point => bodies (change point)) point receipt =
      nativeProductComparison domains bodies (change point) receipt := rfl

theorem sum_decode_substitution (change : Other → Context) (point : Other)
    (receipt : Receipts (sigmaGraph (domains (change point)) (bodies (change point)))) :
    nativeSumComparison (domains ∘ change) (fun point => bodies (change point)) point receipt =
      nativeSumComparison domains bodies (change point) receipt := rfl

theorem lambda_substitution (change : Other → Context)
    (bodySection : (context : Context) → ProductCarrier (domains context) (bodies context)) :
    lambdaSections (domains ∘ change) (fun point => bodies (change point)) (fun point => bodySection (change point)) =
      (fun point => lambdaSections domains bodies bodySection (change point)) := rfl

theorem substitution_composition (first : Other → Context) (second : Third → Other) :
    (domains ∘ first) ∘ second = domains ∘ (first ∘ second) := rfl

end Contexts

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedReceiptFamilies
