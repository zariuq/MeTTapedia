import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mettapedia.GSLT.Core.ContextualTypeReindexing

/-!
# Coherence of contextual type reindexing

The fibre functor selected by a CwF is contravariantly functorial in the
context substitution.  Its object action preserves identity and composition
through the stated `tySub_id` and `tySub_comp` equalities, rather than by
definitional equality.  Consequently the standard categorical packaging is
pseudo-functorial: identity and composition are witnessed by coherent
natural isomorphisms.

This file constructs that packaging with the canonical equality
isomorphisms, relates its comparisons to the cartesian comprehension lifts,
and proves the triangle and pentagon coherence laws.  The comparisons are
not chosen independently of reindexing; their naturality is the cartesian
square already proved for `reindexFunctor`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

namespace TypeOver

/-- Component bridge from the `Cat` wrapper back to an ordinary natural
isomorphism. -/
@[simp]
theorem catIsoMk_hom_app
    {Source Target : Type w} [Category.{v} Source]
    [Category.{v} Target] {F G : Source ⥤ Target}
    (comparison : F ≅ G) (X : Source) :
    (Cat.Hom.isoMk comparison).hom.toNatTrans.app X =
      comparison.hom.app X := rfl

/-- Inverse-component bridge from the `Cat` wrapper. -/
@[simp]
theorem catIsoMk_inv_app
    {Source Target : Type w} [Category.{v} Source]
    [Category.{v} Target] {F G : Source ⥤ Target}
    (comparison : F ≅ G) (X : Source) :
    (Cat.Hom.isoMk comparison).inv.toNatTrans.app X =
      comparison.inv.app X := rfl

/-- Equality of the underlying types induces an isomorphism in the category
of types over a fixed context. -/
def isoOfValEq {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ} (equalValues : A.val = B.val) : A ≅ B :=
  eqToIso (TypeOver.ext equalValues)

/-- Equal base substitutions induce objectwise isomorphic reindexed types. -/
def substitutionEqualityObjectIso
    {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    {left right : C.Sub Γ Δ} (equalSubstitutions : left = right)
    (A : TypeOver C Δ) :
    reindexObject left A ≅ reindexObject right A :=
  isoOfValEq (congrArg (fun substitution => C.tySub A.val substitution)
    equalSubstitutions)

/-- Reindexing respects equality of base substitutions by a natural
isomorphism.  This is the locally-discrete 2-cell action required by the
unit and associativity coherence laws. -/
def substitutionEqualityReindexIso
    {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    {left right : C.Sub Γ Δ} (equalSubstitutions : left = right) :
    reindexFunctor left ≅ reindexFunctor right := by
  cases equalSubstitutions
  exact NatIso.ofComponents
    (fun A => substitutionEqualityObjectIso rfl A)
    (fun morphism => by
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The equality comparison is the unique display arrow relating the
cartesian lifts selected by the equal base substitutions. -/
theorem substitutionEqualityObjectIso_hom_lift
    {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    {left right : C.Sub Γ Δ} (equalSubstitutions : left = right)
    (A : TypeOver C Δ) :
    C.compS (extensionSubstitution right A.val)
        (substitutionEqualityObjectIso equalSubstitutions A).hom.substitution =
      extensionSubstitution left A.val := by
  cases equalSubstitutions
  change C.compS (extensionSubstitution left A.val)
      (C.idS (C.ext Γ (C.tySub A.val left))) =
    extensionSubstitution left A.val
  exact C.comp_id _

/-- The equality-induced display arrow carries the target generic variable
back to the source generic variable. -/
theorem isoOfValEq_hom_reads_vz
    {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ} (equalValues : A.val = B.val) :
    HEq
      (C.tmSub (C.vz B.val) (isoOfValEq equalValues).hom.substitution)
      (C.vz A.val) := by
  rcases A with ⟨sourceType⟩
  rcases B with ⟨targetType⟩
  dsimp at equalValues
  cases equalValues
  change HEq
    (C.tmSub (C.vz sourceType) (C.idS (C.ext Γ sourceType)))
    (C.vz sourceType)
  exact (heq_of_eq (C.tmSub_id (C.vz sourceType))).trans
    (cast_heq _ _)

/-- Reindexing a type along the identity substitution returns an isomorphic
type. -/
def identityObjectIso {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    (A : TypeOver C Γ) :
    reindexObject (C.idS Γ) A ≅ A :=
  isoOfValEq (C.tySub_id A.val)

/-- The hom of the identity comparison is exactly the selected cartesian
lift of the identity substitution. -/
theorem identityObjectIso_hom_substitution
    {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    (A : TypeOver C Γ) :
    (identityObjectIso A).hom.substitution =
      extensionSubstitution (C.idS Γ) A.val := by
  apply TypeOver.substitution_ext
  · calc
      C.compS (C.wk A.val) (identityObjectIso A).hom.substitution =
          C.wk (C.tySub A.val (C.idS Γ)) :=
        (identityObjectIso A).hom.over
      _ = C.compS (C.idS Γ)
          (C.wk (C.tySub A.val (C.idS Γ))) :=
        (C.id_comp _).symm
      _ = C.compS (C.wk A.val)
          (extensionSubstitution (C.idS Γ) A.val) :=
        (wk_extensionSubstitution (C.idS Γ) A.val).symm
  · exact
      (isoOfValEq_hom_reads_vz (C.tySub_id A.val)).trans
        (vz_extensionSubstitution (C.idS Γ) A.val).symm

/-- The unit comparison for contextual reindexing.  Its naturality square is
exactly the cartesian square for the selected comprehension lift. -/
def identityReindexIso {C : Cwf.{u, v, w, w'}} (Γ : C.Ctx) :
    reindexFunctor (C.idS Γ) ≅ 𝟭 (TypeOver C Γ) :=
  NatIso.ofComponents identityObjectIso (fun {A B} morphism => by
    apply Hom.ext
    change C.compS (identityObjectIso B).hom.substitution
        (reindexArrow (C.idS Γ) morphism).substitution =
      C.compS morphism.substitution
        (identityObjectIso A).hom.substitution
    rw [identityObjectIso_hom_substitution,
      identityObjectIso_hom_substitution]
    exact extensionSubstitution_naturality (C.idS Γ) morphism)

/-! ## Composition comparison -/

/-- The two-stage comprehension lift selected by consecutive context
substitutions. -/
def composedExtensionSubstitution
    {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    (first : C.Sub Δ Θ) (second : C.Sub Γ Δ) (A : C.Ty Θ) :
    C.Sub
      (C.ext Γ (C.tySub (C.tySub A first) second))
      (C.ext Θ A) :=
  C.compS (extensionSubstitution first A)
    (extensionSubstitution second (C.tySub A first))

/-- The two-stage lift lies over the composite base substitution. -/
theorem wk_composedExtensionSubstitution
    {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    (first : C.Sub Δ Θ) (second : C.Sub Γ Δ) (A : C.Ty Θ) :
    C.compS (C.wk A)
        (composedExtensionSubstitution first second A) =
      C.compS (C.compS first second)
        (C.wk (C.tySub (C.tySub A first) second)) := by
  calc
    C.compS (C.wk A)
        (C.compS (extensionSubstitution first A)
          (extensionSubstitution second (C.tySub A first))) =
        C.compS
          (C.compS (C.wk A) (extensionSubstitution first A))
          (extensionSubstitution second (C.tySub A first)) :=
      (C.comp_assoc _ _ _).symm
    _ = C.compS
          (C.compS first (C.wk (C.tySub A first)))
          (extensionSubstitution second (C.tySub A first)) := by
      rw [wk_extensionSubstitution]
    _ = C.compS first
          (C.compS (C.wk (C.tySub A first))
            (extensionSubstitution second (C.tySub A first))) :=
      C.comp_assoc _ _ _
    _ = C.compS first
          (C.compS second
            (C.wk (C.tySub (C.tySub A first) second))) := by
      rw [wk_extensionSubstitution]
    _ = C.compS (C.compS first second)
          (C.wk (C.tySub (C.tySub A first) second)) :=
      (C.comp_assoc _ _ _).symm

/-- Reading the original generic variable along the two-stage lift gives the
generic variable of the twice-substituted type. -/
theorem vz_composedExtensionSubstitution
    {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    (first : C.Sub Δ Θ) (second : C.Sub Γ Δ) (A : C.Ty Θ) :
    HEq
      (C.tmSub (C.vz A)
        (composedExtensionSubstitution first second A))
      (C.vz (C.tySub (C.tySub A first) second)) := by
  have firstVariableTypes :
      C.tySub (C.tySub A (C.wk A))
          (extensionSubstitution first A) =
        C.tySub (C.tySub A first) (C.wk (C.tySub A first)) := by
    rw [← C.tySub_comp, wk_extensionSubstitution, C.tySub_comp]
  exact
    (tmSub_comp_heq (C.vz A) (extensionSubstitution first A)
      (extensionSubstitution second (C.tySub A first))).trans
    ((tmSub_heq firstVariableTypes
      (vz_extensionSubstitution first A)
      (extensionSubstitution second (C.tySub A first))).trans
      (vz_extensionSubstitution second (C.tySub A first)))

/-- Reindexing once along a composite and reindexing in two stages give
canonically isomorphic type objects. -/
def compositionObjectIso
    {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    (first : C.Sub Δ Θ) (second : C.Sub Γ Δ)
    (A : TypeOver C Θ) :
    reindexObject (C.compS first second) A ≅
      reindexObject second (reindexObject first A) :=
  isoOfValEq (C.tySub_comp A.val first second)

/-- The composition comparison is precisely the unique arrow equating the
one-stage lift with the two-stage lift. -/
theorem compositionObjectIso_hom_lift
    {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    (first : C.Sub Δ Θ) (second : C.Sub Γ Δ)
    (A : TypeOver C Θ) :
    C.compS (composedExtensionSubstitution first second A.val)
        (compositionObjectIso first second A).hom.substitution =
      extensionSubstitution (C.compS first second) A.val := by
  apply TypeOver.substitution_ext
  · have comparisonOver := (compositionObjectIso first second A).hom.over
    change C.compS
        (C.wk (C.tySub (C.tySub A.val first) second))
        (compositionObjectIso first second A).hom.substitution =
      C.wk (C.tySub A.val (C.compS first second)) at comparisonOver
    calc
      C.compS (C.wk A.val)
          (C.compS (composedExtensionSubstitution first second A.val)
            (compositionObjectIso first second A).hom.substitution) =
          C.compS
            (C.compS (C.wk A.val)
              (composedExtensionSubstitution first second A.val))
            (compositionObjectIso first second A).hom.substitution :=
        (C.comp_assoc _ _ _).symm
      _ = C.compS
            (C.compS (C.compS first second)
              (C.wk (C.tySub (C.tySub A.val first) second)))
            (compositionObjectIso first second A).hom.substitution := by
        rw [wk_composedExtensionSubstitution]
      _ = C.compS (C.compS first second)
            (C.compS
              (C.wk (C.tySub (C.tySub A.val first) second))
              (compositionObjectIso first second A).hom.substitution) :=
        C.comp_assoc _ _ _
      _ = C.compS (C.compS first second)
            (C.wk (C.tySub A.val (C.compS first second))) := by
        exact congrArg
          (fun base => C.compS (C.compS first second) base)
          comparisonOver
      _ = C.compS (C.wk A.val)
          (extensionSubstitution (C.compS first second) A.val) :=
        (wk_extensionSubstitution (C.compS first second) A.val).symm
  · have composedVariableTypes :
        C.tySub (C.tySub A.val (C.wk A.val))
            (composedExtensionSubstitution first second A.val) =
          C.tySub (C.tySub (C.tySub A.val first) second)
            (C.wk (C.tySub (C.tySub A.val first) second)) := by
      calc
        C.tySub (C.tySub A.val (C.wk A.val))
            (composedExtensionSubstitution first second A.val) =
            C.tySub A.val
              (C.compS (C.wk A.val)
                (composedExtensionSubstitution first second A.val)) :=
          (C.tySub_comp A.val (C.wk A.val)
            (composedExtensionSubstitution first second A.val)).symm
        _ = C.tySub A.val
              (C.compS (C.compS first second)
                (C.wk (C.tySub (C.tySub A.val first) second))) :=
          congrArg (fun base => C.tySub A.val base)
            (wk_composedExtensionSubstitution first second A.val)
        _ = C.tySub (C.tySub A.val (C.compS first second))
              (C.wk (C.tySub (C.tySub A.val first) second)) :=
          C.tySub_comp A.val (C.compS first second)
            (C.wk (C.tySub (C.tySub A.val first) second))
        _ = C.tySub (C.tySub (C.tySub A.val first) second)
              (C.wk (C.tySub (C.tySub A.val first) second)) :=
          congrArg
            (fun type => C.tySub type
              (C.wk (C.tySub (C.tySub A.val first) second)))
            (C.tySub_comp A.val first second)
    exact
      (tmSub_comp_heq (C.vz A.val)
        (composedExtensionSubstitution first second A.val)
        (compositionObjectIso first second A).hom.substitution).trans
      ((tmSub_heq composedVariableTypes
        (vz_composedExtensionSubstitution first second A.val)
        (compositionObjectIso first second A).hom.substitution).trans
      ((isoOfValEq_hom_reads_vz
        (C.tySub_comp A.val first second)).trans
        (vz_extensionSubstitution (C.compS first second) A.val).symm))

/-- The two-stage lift is left-cancellable on display arrows lying over the
reindexed base. -/
theorem composedExtensionSubstitution_cancel
    {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    (first : C.Sub Δ Θ) (second : C.Sub Γ Δ)
    {source : TypeOver C Γ} {B : TypeOver C Θ}
    {left right : source ⟶
      reindexObject second (reindexObject first B)}
    (compositesEqual :
      C.compS (composedExtensionSubstitution first second B.val)
          left.substitution =
        C.compS (composedExtensionSubstitution first second B.val)
          right.substitution) :
    left = right := by
  apply Hom.ext
  apply TypeOver.substitution_ext
  · have leftOver := left.over
    have rightOver := right.over
    change C.compS
        (C.wk (C.tySub (C.tySub B.val first) second))
        left.substitution = C.wk source.val at leftOver
    change C.compS
        (C.wk (C.tySub (C.tySub B.val first) second))
        right.substitution = C.wk source.val at rightOver
    exact leftOver.trans rightOver.symm
  · have composedVariableTypes :
        C.tySub (C.tySub B.val (C.wk B.val))
            (composedExtensionSubstitution first second B.val) =
          C.tySub (C.tySub (C.tySub B.val first) second)
            (C.wk (C.tySub (C.tySub B.val first) second)) := by
      calc
        C.tySub (C.tySub B.val (C.wk B.val))
            (composedExtensionSubstitution first second B.val) =
            C.tySub B.val
              (C.compS (C.wk B.val)
                (composedExtensionSubstitution first second B.val)) :=
          (C.tySub_comp B.val (C.wk B.val)
            (composedExtensionSubstitution first second B.val)).symm
        _ = C.tySub B.val
              (C.compS (C.compS first second)
                (C.wk (C.tySub (C.tySub B.val first) second))) :=
          congrArg (fun base => C.tySub B.val base)
            (wk_composedExtensionSubstitution first second B.val)
        _ = C.tySub (C.tySub B.val (C.compS first second))
              (C.wk (C.tySub (C.tySub B.val first) second)) :=
          C.tySub_comp B.val (C.compS first second)
            (C.wk (C.tySub (C.tySub B.val first) second))
        _ = C.tySub (C.tySub (C.tySub B.val first) second)
              (C.wk (C.tySub (C.tySub B.val first) second)) :=
          congrArg
            (fun type => C.tySub type
              (C.wk (C.tySub (C.tySub B.val first) second)))
            (C.tySub_comp B.val first second)
    have composedReadEquality :
        HEq
          (C.tmSub (C.vz B.val)
            (C.compS
              (composedExtensionSubstitution first second B.val)
              left.substitution))
          (C.tmSub (C.vz B.val)
            (C.compS
              (composedExtensionSubstitution first second B.val)
              right.substitution)) := by
      rw [compositesEqual]
    exact
      (tmSub_heq composedVariableTypes
        (vz_composedExtensionSubstitution first second B.val)
        left.substitution).symm.trans
      ((tmSub_comp_heq (C.vz B.val)
        (composedExtensionSubstitution first second B.val)
        left.substitution).symm.trans
      (composedReadEquality.trans
      ((tmSub_comp_heq (C.vz B.val)
        (composedExtensionSubstitution first second B.val)
        right.substitution).trans
      (tmSub_heq composedVariableTypes
        (vz_composedExtensionSubstitution first second B.val)
        right.substitution))))

/-- The two-stage comprehension lift is natural in display maps. -/
theorem composedExtensionSubstitution_naturality
    {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    (first : C.Sub Δ Θ) (second : C.Sub Γ Δ)
    {A B : TypeOver C Θ} (morphism : A ⟶ B) :
    C.compS (composedExtensionSubstitution first second B.val)
        (reindexArrow second
          (reindexArrow first morphism)).substitution =
      C.compS morphism.substitution
        (composedExtensionSubstitution first second A.val) := by
  have firstNaturality :=
    extensionSubstitution_naturality first morphism
  change C.compS (extensionSubstitution first B.val)
      (reindexArrow first morphism).substitution =
    C.compS morphism.substitution
      (extensionSubstitution first A.val) at firstNaturality
  have secondNaturality := extensionSubstitution_naturality second
    (reindexArrow first morphism)
  change C.compS
      (extensionSubstitution second (C.tySub B.val first))
      (reindexArrow second (reindexArrow first morphism)).substitution =
    C.compS (reindexArrow first morphism).substitution
      (extensionSubstitution second (C.tySub A.val first))
    at secondNaturality
  calc
    C.compS
        (C.compS (extensionSubstitution first B.val)
          (extensionSubstitution second (C.tySub B.val first)))
        (reindexArrow second
          (reindexArrow first morphism)).substitution =
        C.compS (extensionSubstitution first B.val)
          (C.compS
            (extensionSubstitution second (C.tySub B.val first))
            (reindexArrow second
              (reindexArrow first morphism)).substitution) :=
      C.comp_assoc _ _ _
    _ = C.compS (extensionSubstitution first B.val)
          (C.compS (reindexArrow first morphism).substitution
            (extensionSubstitution second
              (C.tySub A.val first))) := by
      exact congrArg
        (fun inner => C.compS (extensionSubstitution first B.val) inner)
        secondNaturality
    _ = C.compS
          (C.compS (extensionSubstitution first B.val)
            (reindexArrow first morphism).substitution)
          (extensionSubstitution second (C.tySub A.val first)) :=
      (C.comp_assoc _ _ _).symm
    _ = C.compS
          (C.compS morphism.substitution
            (extensionSubstitution first A.val))
          (extensionSubstitution second (C.tySub A.val first)) := by
      exact congrArg
        (fun outer => C.compS outer
          (extensionSubstitution second (C.tySub A.val first)))
        firstNaturality
    _ = C.compS morphism.substitution
          (C.compS (extensionSubstitution first A.val)
            (extensionSubstitution second (C.tySub A.val first))) :=
      C.comp_assoc _ _ _

/-- The compositor comparison for contextual reindexing. -/
def compositionReindexIso
    {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    (first : C.Sub Δ Θ) (second : C.Sub Γ Δ) :
    reindexFunctor (C.compS first second) ≅
      reindexFunctor first ⋙ reindexFunctor second :=
  NatIso.ofComponents (compositionObjectIso first second)
    (fun {A B} morphism => by
      apply composedExtensionSubstitution_cancel first second
      have directNaturality := extensionSubstitution_naturality
        (C.compS first second) morphism
      change C.compS
          (extensionSubstitution (C.compS first second) B.val)
          (reindexArrow (C.compS first second) morphism).substitution =
        C.compS morphism.substitution
          (extensionSubstitution (C.compS first second) A.val)
        at directNaturality
      have stagedNaturality :=
        composedExtensionSubstitution_naturality first second morphism
      change C.compS (composedExtensionSubstitution first second B.val)
          (reindexArrow second
            (reindexArrow first morphism)).substitution =
        C.compS morphism.substitution
          (composedExtensionSubstitution first second A.val)
        at stagedNaturality
      have comparisonA :=
        compositionObjectIso_hom_lift first second A
      have comparisonB :=
        compositionObjectIso_hom_lift first second B
      have comparisonBWhiskered := congrArg
        (fun outer => C.compS outer
          (reindexArrow (C.compS first second) morphism).substitution)
        comparisonB
      have comparisonAWhiskered := congrArg
        (fun inner => C.compS morphism.substitution inner)
        comparisonA.symm
      have stagedWhiskered := congrArg
        (fun outer => C.compS outer
          (compositionObjectIso first second A).hom.substitution)
        stagedNaturality.symm
      have reassociateA :=
        (C.comp_assoc morphism.substitution
          (composedExtensionSubstitution first second A.val)
          (compositionObjectIso first second A).hom.substitution).symm
      have reassociateFinal :=
        C.comp_assoc (composedExtensionSubstitution first second B.val)
          (reindexArrow second
            (reindexArrow first morphism)).substitution
          (compositionObjectIso first second A).hom.substitution
      have comparisonTail :
          C.compS morphism.substitution
              (extensionSubstitution (C.compS first second) A.val) =
            C.compS (composedExtensionSubstitution first second B.val)
              (C.compS
                (reindexArrow second
                  (reindexArrow first morphism)).substitution
                (compositionObjectIso first second A).hom.substitution) :=
        comparisonAWhiskered.trans
          (reassociateA.trans (stagedWhiskered.trans reassociateFinal))
      have reassociateStart :=
        (C.comp_assoc (composedExtensionSubstitution first second B.val)
          (compositionObjectIso first second B).hom.substitution
          (reindexArrow (C.compS first second) morphism).substitution).symm
      change C.compS
          (composedExtensionSubstitution first second B.val)
          (C.compS
            (compositionObjectIso first second B).hom.substitution
            (reindexArrow (C.compS first second) morphism).substitution) =
        C.compS
          (composedExtensionSubstitution first second B.val)
          (C.compS
            (reindexArrow second
              (reindexArrow first morphism)).substitution
            (compositionObjectIso first second A).hom.substitution)
      exact reassociateStart.trans
        (comparisonBWhiskered.trans
          (directNaturality.trans comparisonTail)))

/-! ## Unit coherence at the display-map boundary -/

/-- Left-unit coherence: composing the compositor with the reindexed unit
comparison is exactly the equality comparison induced by `id_comp`. -/
theorem leftUnitComparison_hom
    {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) (A : TypeOver C Δ) :
    (compositionObjectIso (C.idS Δ) substitution A).hom ≫
        reindexArrow substitution (identityObjectIso A).hom =
      (substitutionEqualityObjectIso (C.id_comp substitution) A).hom := by
  apply extensionSubstitution_cancel
    (source := reindexObject (C.compS (C.idS Δ) substitution) A)
    (B := A) substitution
  change C.compS (extensionSubstitution substitution A.val)
      (C.compS
        (reindexArrow substitution
          (identityObjectIso A).hom).substitution
        (compositionObjectIso (C.idS Δ) substitution A).hom.substitution) =
    C.compS (extensionSubstitution substitution A.val)
      (substitutionEqualityObjectIso
        (C.id_comp substitution) A).hom.substitution
  have equalityLift :
      C.compS (extensionSubstitution substitution A.val)
          (substitutionEqualityObjectIso
            (C.id_comp substitution) A).hom.substitution =
        extensionSubstitution
          (C.compS (C.idS Δ) substitution) A.val :=
    substitutionEqualityObjectIso_hom_lift
      (C.id_comp substitution) A
  have unitNaturality := extensionSubstitution_naturality substitution
    (identityObjectIso A).hom
  change C.compS (extensionSubstitution substitution A.val)
      (reindexArrow substitution
        (identityObjectIso A).hom).substitution =
    C.compS (identityObjectIso A).hom.substitution
      (extensionSubstitution substitution
        (C.tySub A.val (C.idS Δ))) at unitNaturality
  have compositeLift :
      C.compS (extensionSubstitution substitution A.val)
          (C.compS
            (reindexArrow substitution
              (identityObjectIso A).hom).substitution
            (compositionObjectIso
              (C.idS Δ) substitution A).hom.substitution) =
        extensionSubstitution
          (C.compS (C.idS Δ) substitution) A.val := by
    calc
    C.compS (extensionSubstitution substitution A.val)
        (C.compS
          (reindexArrow substitution
            (identityObjectIso A).hom).substitution
          (compositionObjectIso (C.idS Δ) substitution A).hom.substitution) =
        C.compS
          (C.compS (extensionSubstitution substitution A.val)
            (reindexArrow substitution
              (identityObjectIso A).hom).substitution)
          (compositionObjectIso (C.idS Δ) substitution A).hom.substitution :=
      (C.comp_assoc _ _ _).symm
    _ = C.compS
          (C.compS (identityObjectIso A).hom.substitution
            (extensionSubstitution substitution
              (C.tySub A.val (C.idS Δ))))
          (compositionObjectIso (C.idS Δ) substitution A).hom.substitution := by
      exact congrArg
        (fun outer => C.compS outer
          (compositionObjectIso (C.idS Δ) substitution A).hom.substitution)
        unitNaturality
    _ = C.compS
          (composedExtensionSubstitution (C.idS Δ) substitution A.val)
          (compositionObjectIso (C.idS Δ) substitution A).hom.substitution := by
      rw [identityObjectIso_hom_substitution]
      rfl
    _ = extensionSubstitution
          (C.compS (C.idS Δ) substitution) A.val :=
      compositionObjectIso_hom_lift (C.idS Δ) substitution A
  exact compositeLift.trans equalityLift.symm

/-- Right-unit coherence: composing the compositor with the unit comparison
at the reindexed object is exactly the equality comparison induced by
`comp_id`. -/
theorem rightUnitComparison_hom
    {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    (substitution : C.Sub Γ Δ) (A : TypeOver C Δ) :
    (compositionObjectIso substitution (C.idS Γ) A).hom ≫
        (identityObjectIso (reindexObject substitution A)).hom =
      (substitutionEqualityObjectIso (C.comp_id substitution) A).hom := by
  apply extensionSubstitution_cancel
    (source := reindexObject (C.compS substitution (C.idS Γ)) A)
    (B := A) substitution
  change C.compS (extensionSubstitution substitution A.val)
      (C.compS
        (identityObjectIso (reindexObject substitution A)).hom.substitution
        (compositionObjectIso substitution (C.idS Γ) A).hom.substitution) =
    C.compS (extensionSubstitution substitution A.val)
      (substitutionEqualityObjectIso
        (C.comp_id substitution) A).hom.substitution
  have equalityLift :
      C.compS (extensionSubstitution substitution A.val)
          (substitutionEqualityObjectIso
            (C.comp_id substitution) A).hom.substitution =
        extensionSubstitution
          (C.compS substitution (C.idS Γ)) A.val :=
    substitutionEqualityObjectIso_hom_lift
      (C.comp_id substitution) A
  have compositeLift :
      C.compS (extensionSubstitution substitution A.val)
          (C.compS
            (identityObjectIso
              (reindexObject substitution A)).hom.substitution
            (compositionObjectIso substitution
              (C.idS Γ) A).hom.substitution) =
        extensionSubstitution
          (C.compS substitution (C.idS Γ)) A.val := by
    calc
    C.compS (extensionSubstitution substitution A.val)
        (C.compS
          (identityObjectIso
            (reindexObject substitution A)).hom.substitution
          (compositionObjectIso substitution
            (C.idS Γ) A).hom.substitution) =
        C.compS
          (C.compS (extensionSubstitution substitution A.val)
            (identityObjectIso
              (reindexObject substitution A)).hom.substitution)
          (compositionObjectIso substitution
            (C.idS Γ) A).hom.substitution :=
      (C.comp_assoc _ _ _).symm
    _ = C.compS
          (composedExtensionSubstitution substitution (C.idS Γ) A.val)
          (compositionObjectIso substitution
            (C.idS Γ) A).hom.substitution := by
      rw [identityObjectIso_hom_substitution]
      rfl
    _ = extensionSubstitution
          (C.compS substitution (C.idS Γ)) A.val :=
      compositionObjectIso_hom_lift substitution (C.idS Γ) A
  exact compositeLift.trans equalityLift.symm

/-! ## Pseudofunctorial packaging -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Contextual types and display maps form the canonical contravariant
pseudofunctor from the context category to `Cat`.  The unit and compositor
are the cartesian comparisons constructed above; the remaining fields state
their triangle and pentagon coherence. -/
def reindexingPseudofunctor (C : Cwf.{u, v, w, w'}) :
    Pseudofunctor (LocallyDiscrete ((C.base.Context)ᵒᵖ)) Cat.{v, w} :=
  LocallyDiscrete.mkPseudofunctor
    (obj := fun Γ =>
      (Cat.of (TypeOver C Γ.unop.val) : Cat.{v, w}))
    (map := fun substitution =>
      (reindexFunctor (C := C) substitution.unop).toCatHom)
    (mapId := fun Γ =>
      Cat.Hom.isoMk (identityReindexIso (C := C) Γ.unop.val))
    (mapComp := fun first second =>
      Cat.Hom.isoMk
        (compositionReindexIso (C := C) first.unop second.unop))
    (map₂_associator := by
      intro Γ Δ Θ Ξ first second third
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply Hom.ext
      simp [compositionReindexIso, compositionObjectIso, isoOfValEq,
        eqToHom_map, eqToHom_trans])
    (map₂_left_unitor := by
      intro Γ Δ substitution
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply Hom.ext
      simpa [compositionReindexIso, identityReindexIso,
        substitutionEqualityObjectIso, isoOfValEq,
        reindexFunctor, reindexObject] using congrArg Hom.substitution
          (leftUnitComparison_hom (C := C) substitution.unop A))
    (map₂_right_unitor := by
      intro Γ Δ substitution
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply Hom.ext
      simpa [compositionReindexIso, identityReindexIso,
        substitutionEqualityObjectIso, isoOfValEq,
        reindexFunctor, reindexObject] using congrArg Hom.substitution
          (rightUnitComparison_hom (C := C) substitution.unop A))

/-! ## Executable controls -/

/-- The one-point context, bundled as an object of the families CwF base
category. -/
def familiesUnitBaseContext : familiesCwf.base.Context :=
  ⟨PUnit⟩

/-- The one-point context as an object of the locally discrete opposite base
bicategory used by the reindexing pseudofunctor. -/
def familiesUnitPseudofunctorObject :
    LocallyDiscrete ((familiesCwf.base.Context)ᵒᵖ) :=
  LocallyDiscrete.mk (Opposite.op familiesUnitBaseContext)

/-- The packaged pseudofunctor acts on a fibre arrow by the explicitly
constructed reindexing operation. -/
theorem families_pseudofunctor_identity_map_boolNegation :
    ((reindexingPseudofunctor familiesCwf).map
      (𝟙 familiesUnitPseudofunctorObject)).toFunctor.map
        boolNegationDisplay =
      reindexArrow (fun pointUnit : PUnit => pointUnit)
        boolNegationDisplay := by
  rfl

/-- In the families CwF, the identity comparison really is the identity on
displayed values. -/
theorem families_identityObjectIso_hom_apply
    (point : Σ _ : PUnit, Bool) :
    (identityObjectIso unitBoolType).hom.substitution point = point :=
  rfl

/-- In the families CwF, the composition comparison also preserves the
displayed value exactly. -/
theorem families_compositionObjectIso_hom_apply
    (point : Σ _ : Bool, Bool) :
    (compositionObjectIso (C := familiesCwf)
      (fun pointUnit : PUnit => pointUnit)
      (fun _ : Bool => PUnit.unit)
      unitBoolType).hom.substitution point = point :=
  rfl

/-- Negative control: the unit comparison does not collapse non-identity
fibre maps.  Boolean negation remains distinct from the identity after
reindexing along the identity context substitution. -/
theorem identity_reindexed_boolNegation_ne_identity :
    reindexArrow (C := familiesCwf)
        (fun pointUnit : PUnit => pointUnit)
        boolNegationDisplay ≠
      𝟙 (reindexObject (C := familiesCwf)
        (fun pointUnit : PUnit => pointUnit) unitBoolType) := by
  intro equalArrows
  have equalSubstitutions := congrArg Hom.substitution equalArrows
  have atTrue := congrFun equalSubstitutions
    (⟨PUnit.unit, true⟩ : Σ _ : PUnit, Bool)
  have valuesEqual := congrArg (fun point => point.2) atTrue
  change false = true at valuesEqual
  cases valuesEqual

/-- Negative package-level control: the pseudofunctor retains the genuine
Boolean-negation display map; its fibre action is neither discrete nor
constant. -/
theorem families_pseudofunctor_identity_map_boolNegation_ne_identity :
    ((reindexingPseudofunctor familiesCwf).map
      (𝟙 familiesUnitPseudofunctorObject)).toFunctor.map
        boolNegationDisplay ≠
      𝟙 (((reindexingPseudofunctor familiesCwf).map
        (𝟙 familiesUnitPseudofunctorObject)).toFunctor.obj
          unitBoolType) := by
  change reindexArrow (C := familiesCwf)
      (fun pointUnit : PUnit => pointUnit) boolNegationDisplay ≠
    𝟙 (reindexObject (C := familiesCwf)
      (fun pointUnit : PUnit => pointUnit) unitBoolType)
  exact identity_reindexed_boolNegation_ne_identity

#print axioms TypeOver.isoOfValEq
#print axioms TypeOver.isoOfValEq_hom_reads_vz
#print axioms TypeOver.identityObjectIso
#print axioms TypeOver.identityObjectIso_hom_substitution
#print axioms TypeOver.identityReindexIso
#print axioms TypeOver.composedExtensionSubstitution
#print axioms TypeOver.wk_composedExtensionSubstitution
#print axioms TypeOver.vz_composedExtensionSubstitution
#print axioms TypeOver.compositionObjectIso
#print axioms TypeOver.compositionObjectIso_hom_lift
#print axioms TypeOver.substitutionEqualityObjectIso_hom_lift
#print axioms TypeOver.composedExtensionSubstitution_cancel
#print axioms TypeOver.composedExtensionSubstitution_naturality
#print axioms TypeOver.compositionReindexIso
#print axioms TypeOver.leftUnitComparison_hom
#print axioms TypeOver.rightUnitComparison_hom
#print axioms TypeOver.reindexingPseudofunctor
#print axioms TypeOver.families_pseudofunctor_identity_map_boolNegation
#print axioms TypeOver.families_identityObjectIso_hom_apply
#print axioms TypeOver.families_compositionObjectIso_hom_apply
#print axioms TypeOver.identity_reindexed_boolNegation_ne_identity
#print axioms TypeOver.families_pseudofunctor_identity_map_boolNegation_ne_identity

end TypeOver

end Mettapedia.GSLT.Core.ContextualLadder
