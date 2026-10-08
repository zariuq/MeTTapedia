import Mettapedia.TypeTheory.ContextualComprehensionMorphism
import Mettapedia.TypeTheory.ContextualPiEta

/-!
# Local logical preservation by contextual morphisms

The underlying map is an actual strict morphism of categories with families.
The extra capabilities below concern individual dependent-product and
dependent-sum constructors. Supplied image presentations retain their
context, domain and codomain comparisons explicitly. They do not assume an
action on all syntax, any judgment interpretation, or sum elimination.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualLogicalMorphism

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u v w w'

variable {C D : CwfWithTerminal.{u, v, w, w'}}

/-- Local product constructors at explicitly compared image presentations. -/
structure PiPreservation (F : StrictCwfMorphism C D)
    (source : PiOperations C.toCwf) (target : PiOperations D.toCwf) : Prop where
  formation : ∀ {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (_contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (_domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (_codomains : HEq (F.toFamilyMorphism.mapType B) B'),
    HEq (F.toFamilyMorphism.mapType (source.pi A B)) (target.pi A' B')
  abstraction : ∀ {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (_contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (_domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (_codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (body : C.toCwf.Tm (C.toCwf.ext Γ A) B)
    (body' : D.toCwf.Tm (D.toCwf.ext Γ' A') B'),
    HEq (F.toFamilyMorphism.mapTerm body) body' →
    HEq (F.toFamilyMorphism.mapTerm (source.lam body)) (target.lam body')
  application : ∀ {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (_contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (_domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (_codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (function : C.toCwf.Tm Γ (source.pi A B))
    (function' : D.toCwf.Tm Γ' (target.pi A' B'))
    (argument : C.toCwf.Tm Γ A) (argument' : D.toCwf.Tm Γ' A'),
    HEq (F.toFamilyMorphism.mapTerm function) function' →
    HEq (F.toFamilyMorphism.mapTerm argument) argument' →
    HEq (F.toFamilyMorphism.mapTerm (source.app function argument))
      (target.app function' argument')

/-- Local sum constructors; the full-motive eliminator is not a field. -/
structure SigmaPreservation (F : StrictCwfMorphism C D)
    (source : SigmaOperations C.toCwf) (target : SigmaOperations D.toCwf) : Prop where
  formation : ∀ {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (_contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (_domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (_codomains : HEq (F.toFamilyMorphism.mapType B) B'),
    HEq (F.toFamilyMorphism.mapType (source.sigma A B)) (target.sigma A' B')
  pairing : ∀ {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (_contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (_domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (_codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (first : C.toCwf.Tm Γ A) (first' : D.toCwf.Tm Γ' A')
    (second : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf first)))
    (second' : D.toCwf.Tm Γ' (D.toCwf.tySub B' (selfExtend D.toCwf first'))),
    HEq (F.toFamilyMorphism.mapTerm first) first' →
    HEq (F.toFamilyMorphism.mapTerm second) second' →
    HEq (F.toFamilyMorphism.mapTerm (source.pair first second)) (target.pair first' second')
  firstProjection : ∀ {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (_contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (_domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (_codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (pair : C.toCwf.Tm Γ (source.sigma A B))
    (pair' : D.toCwf.Tm Γ' (target.sigma A' B')),
    HEq (F.toFamilyMorphism.mapTerm pair) pair' →
    HEq (F.toFamilyMorphism.mapTerm (source.fst pair)) (target.fst pair')
  secondProjection : ∀ {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (_contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (_domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (_codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (pair : C.toCwf.Tm Γ (source.sigma A B))
    (pair' : D.toCwf.Tm Γ' (target.sigma A' B')),
    HEq (F.toFamilyMorphism.mapTerm pair) pair' →
    HEq (F.toFamilyMorphism.mapTerm (source.snd pair)) (target.snd pair')

/-- Logical structure sits over the supplied complete contextual morphism. -/
structure LogicalPreservation (F : StrictCwfMorphism C D)
    (sourcePi : PiOperations C.toCwf) (targetPi : PiOperations D.toCwf)
    (sourceSigma : SigmaOperations C.toCwf) (targetSigma : SigmaOperations D.toCwf) : Prop where
  products : PiPreservation F sourcePi targetPi
  sums : SigmaPreservation F sourceSigma targetSigma

theorem tuple_contexts (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    context F (tupleContext A B) = tupleContext A' B' :=
  extension_images F (extension_images F contexts domains) codomains

theorem tuple_base_heq (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    HEq (F.toFamilyMorphism.base.map (C.toCwf.compS (C.toCwf.wk A) (C.toCwf.wk B)))
      (D.toCwf.compS (D.toCwf.wk A') (D.toCwf.wk B')) :=
  (heq_of_eq (F.toFamilyMorphism.base.map_comp (C.toCwf.wk B) (C.toCwf.wk A))).trans
    (comp_heq (tuple_contexts F contexts domains codomains)
      (extension_images F contexts domains) contexts
      ((projection_heq F Γ A).trans (wk_heq contexts domains))
      ((projection_heq F _ B).trans (wk_heq (extension_images F contexts domains) codomains)))

theorem generic_first_heq (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    HEq (F.toFamilyMorphism.mapTerm (genericFirst A B)) (genericFirst A' B') := by
  have weakeningA := (projection_heq F Γ A).trans (wk_heq contexts domains)
  have weakeningB := (projection_heq F _ B).trans
    (wk_heq (extension_images F contexts domains) codomains)
  have variableReadout := (variable_heq F Γ A).trans (vz_heq contexts domains)
  have variableType := substituted_type_heq F (extension_images F contexts domains)
    contexts domains weakeningA
  have read := substituted_term_heq F (tuple_contexts F contexts domains codomains)
    (extension_images F contexts domains) variableType variableReadout weakeningB
  exact (F.mapTerm_heq (C.toCwf.tySub_comp A (C.toCwf.wk A) (C.toCwf.wk B))
    (genericFirst_heq A B)).trans (read.trans (genericFirst_heq A' B').symm)

theorem generic_second_heq (F : StrictCwfMorphism C D)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    HEq (F.toFamilyMorphism.mapTerm (genericSecond A B)) (genericSecond A' B') :=
  (F.mapTerm_heq (genericSecond_type A B).symm (genericSecond_heq A B)).trans
    ((variable_heq F _ B).trans ((vz_heq (extension_images F contexts domains) codomains).trans
      (genericSecond_heq A' B').symm))

/-- The exact pairing of the two generic witnesses is preserved using the
local sum constructor and the independently earned lifted-substitution law. -/
theorem packed_variable_heq (F : StrictCwfMorphism C D)
    (source : StableSums C.toCwf) (target : StableSums D.toCwf)
    (preserves : SigmaPreservation F source.operations target.operations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    HEq (F.toFamilyMorphism.mapTerm
      (C.toCwf.tmSub (C.toCwf.vz (source.operations.sigma A B)) (pack source A B)))
      (D.toCwf.tmSub (D.toCwf.vz (target.operations.sigma A' B')) (pack target A' B')) := by
  let σ := C.toCwf.compS (C.toCwf.wk A) (C.toCwf.wk B)
  let σ' := D.toCwf.compS (D.toCwf.wk A') (D.toCwf.wk B')
  have tuples := tuple_contexts F contexts domains codomains
  have bases := tuple_base_heq F contexts domains codomains
  have domainsAt := substituted_type_heq F tuples contexts domains bases
  have lifts := lifted_substitution_heq F tuples contexts domains σ σ' bases
  have codomainsAt := substituted_type_heq F
    (extension_images F tuples domainsAt) (extension_images F contexts domains) codomains lifts
  have pairingRead := preserves.pairing tuples domainsAt codomainsAt
    (genericFirst A B) (genericFirst A' B') (genericSecond A B) (genericSecond A' B')
    (generic_first_heq F contexts domains codomains) (generic_second_heq F contexts domains codomains)
  have sourceReadTypes :
      C.toCwf.tySub (C.toCwf.tySub (source.operations.sigma A B)
        (C.toCwf.wk (source.operations.sigma A B))) (pack source A B) =
      source.operations.sigma (C.toCwf.tySub A σ)
        (C.toCwf.tySub B (TypeOver.extensionSubstitution σ A)) := by
    rw [← C.toCwf.tySub_comp, pack_over, source.substitution.1]
  exact (F.mapTerm_heq sourceReadTypes (pack_variable source A B)).trans
    (pairingRead.trans (pack_variable target A' B').symm)

end Mettapedia.TypeTheory.ContextualLogicalMorphism
