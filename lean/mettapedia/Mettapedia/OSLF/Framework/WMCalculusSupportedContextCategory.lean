import Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
import Mettapedia.OSLF.Syntax.SyntacticCategory
import Mathlib.CategoryTheory.Widesubcategory

/-!
# Supported WM substitutions and their model-environment functor

The combined reading interprets a constructor fragment, not every term of
the generated binding signature. Its supported substitutions form a wide
subcategory of the existing syntactic context category. Interpretation is
an actual functor on that subcategory, independent of support certificates.

The inclusion forgets only the support condition; it does not quotient
terms by their observations. This is not a classifying completion or an
interpretation of the signature's uninterpreted binders and collections.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusSupportedContextCategory

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.Syntactic
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics

/-- A syntactic context map is interpretable precisely when all its
variable images have constructor-fragment certificates. -/
def supportedMaps : MorphismProperty (Ctxt CombinedSignature) :=
  fun _ _ sigma => ∀ sort position, Nonempty (FirstOrder (sigma sort position))

instance : supportedMaps.IsMultiplicative where
  id_mem _ := fun _ position => ⟨.variable position⟩
  comp_mem sigma tau hs ht := by
    intro sort position
    obtain ⟨fragment⟩ := ht sort position
    exact ⟨FirstOrder.substitute sigma
      (fun imageSort imagePosition => Classical.choice (hs imageSort imagePosition))
      fragment⟩

abbrev SupportedContext := WideSubcategory supportedMaps

/-- The ordinary generated context, with only its maps restricted. -/
def context (entries : Ctx CombinedSignature) : SupportedContext :=
  ⟨⟨entries⟩⟩

/-- The original syntax is retained by the faithful wide inclusion. -/
def inclusion : SupportedContext ⥤ Ctxt CombinedSignature :=
  wideSubcategoryInclusion supportedMaps

instance : inclusion.Faithful := inferInstanceAs
  (wideSubcategoryInclusion supportedMaps).Faithful

/-- Package an existing substitution without replacing its computed images. -/
def supportedMap {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort position, FirstOrder (sigma sort position)) :
    context Δ ⟶ context Γ :=
  ⟨sigma, fun sort position => ⟨supported sort position⟩⟩

@[simp] theorem supportedMap_hom {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort position, FirstOrder (sigma sort position)) :
    (supportedMap sigma supported).hom = sigma := rfl

noncomputable def certificates {Γ Δ : SupportedContext} (sigma : Γ ⟶ Δ) :
    ∀ sort position, FirstOrder (sigma.hom sort position) :=
  fun sort position => Classical.choice (sigma.property sort position)

/-- Support proofs do not introduce an extra semantic authority. -/
theorem reindexEnvironment_certificate_independent
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature} (sigma : Sub CombinedSignature Γ Δ)
    (first second : ∀ sort position, FirstOrder (sigma sort position)) :
    reindexEnvironment reading sigma first =
      reindexEnvironment reading sigma second := by
  funext environment sort position
  exact (denote_heq_of_erase_eq reading environment
    (first sort position) (second sort position) rfl).eq

/-- Environments are covariant on the context category: a map `Delta -> Gamma`
is syntactically a substitution of Gamma's variables by Delta terms. -/
noncomputable def environmentFunctor {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope) :
    SupportedContext ⥤ Type where
  obj Γ := Environment (State := State) (Query := Query)
    (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ.obj.vars
  map sigma := TypeCat.ofHom
    (reindexEnvironment reading sigma.hom (certificates sigma))
  map_id Γ := by
    apply ConcreteCategory.hom_ext
    intro environment
    change reindexEnvironment reading _ _ environment = environment
    rw [reindexEnvironment_certificate_independent reading _
      (certificates (𝟙 Γ)) (fun _ position => .variable position)]
    exact reindexEnvironment_id reading environment
  map_comp sigma tau := by
    apply ConcreteCategory.hom_ext
    intro environment
    change reindexEnvironment reading (sigma ≫ tau).hom _ environment =
      reindexEnvironment reading tau.hom (certificates tau)
        (reindexEnvironment reading sigma.hom (certificates sigma) environment)
    rw [reindexEnvironment_comp]
    exact congrFun (reindexEnvironment_certificate_independent reading _ _ _) environment

/-- The categorical map of an explicitly computed substitution is exactly
the already-proved environment reindexing, with its supplied certificates. -/
theorem environmentFunctor_map_supportedMap
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature} (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort position, FirstOrder (sigma sort position))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ) :
    (environmentFunctor reading).map (supportedMap sigma supported) environment =
      reindexEnvironment reading sigma supported environment :=
  congrFun (reindexEnvironment_certificate_independent reading sigma _ supported)
    environment

/-- Interpreting a substituted term commutes with the actual categorical
action, not only with a separately supplied environment function. -/
theorem denote_supportedMap
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature} (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ sort position, FirstOrder (sigma sort position))
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ) :
    FirstOrder.denote reading environment
        (FirstOrder.substitute sigma supported fragment) =
      FirstOrder.denote reading
        ((environmentFunctor reading).map (supportedMap sigma supported) environment)
        fragment := by
  rw [environmentFunctor_map_supportedMap]
  exact denote_substitute reading sigma supported environment fragment

private abbrev Evidence := TypeExpr.base "BinaryEvidence"

def duplicateEvidence : context [Evidence] ⟶ context [Evidence] :=
  supportedMap (fun _ position =>
    match position with
    | .zero => combine (.var .zero) (.var .zero)
    | .succ impossible => nomatch impossible)
    (fun _ position => by
      cases position with
      | zero => exact .combine (.variable .zero) (.variable .zero)
      | succ impossible => cases impossible)

def singleEvidenceEnvironment (count : Nat) :
    Environment (State := CountState) (Query := String) (Ev := Nat)
      (Ov := Nat) (Scope := CountScope) [Evidence] := by
  intro sort position
  cases position with
  | zero => exact count
  | succ impossible => cases impossible

/-- Substitution really changes the model environment; the functor is not
a constant or identity interpretation disguised as a context action. -/
theorem duplicateEvidence_denotes (count : Nat) :
    (environmentFunctor countingCombined).map duplicateEvidence
      (singleEvidenceEnvironment count) Evidence .zero = count + count := by
  unfold duplicateEvidence
  rw [environmentFunctor_map_supportedMap]
  rfl

/-- The support restriction rejects a generic intrinsic substitution form
which the combined reading does not interpret. -/
def unsupportedEvidenceMap :
    (context []).obj ⟶ (context [Evidence]).obj :=
  fun _ position =>
    match position with
    | .zero => genericEvidenceSubst
    | .succ impossible => nomatch impossible

theorem unsupportedEvidenceMap_rejected : ¬ supportedMaps unsupportedEvidenceMap := by
  intro supported
  exact genericEvidenceSubst_not_FirstOrder (supported Evidence .zero)

#print axioms environmentFunctor
#print axioms denote_supportedMap
#print axioms duplicateEvidence_denotes
#print axioms unsupportedEvidenceMap_rejected

end Mettapedia.OSLF.Framework.WMCalculusSupportedContextCategory
