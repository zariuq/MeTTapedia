import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialFamilies
import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.TypeTheory.ContextualIdentityTypes
import Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction
import Mettapedia.TypeTheory.ContextualSumComparison

/-!
# The constructive authored material CwF

Contexts are actual presheaves with potentially wider parameter fibres.
Types retain small native families and their constructed material decoders.
Terms are full compatible sections. Actual natural substitutions and
material-member decoding commute with comprehension and term restriction.
The common CwF interface receives proved projection, variable and pairing
laws; its terminal context has the genuine universal property.

Discrete identity and arbitrary dependent J act in this interpreted model.
They are not native higher identity or equality-reflection rules. The graph
bound for each authored type is the original small receipt bound, while
contexts, global sections and formation codes may be wider.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialCwf

open CategoryTheory Mettapedia.TypeTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualAuthoredMaterialFamilies

universe u v w
variable {D : Type u} [Category.{u} D]

variable {base other : D ⥤ Type (max u v)}

def pair (change : NaturalHom other base) (domain : Family base)
    (term : (domain.reindex change).native.sections) : NaturalHom other domain.extension where
  app point value := ⟨change.app point value, term.val ⟨point, value⟩⟩
  naturality {first second} step value := by
    apply Sigma.ext (change.naturality step value)
    let original : other.Elements := ⟨first, value⟩
    let next : other.Elements := ⟨second, other.map step value⟩
    let contextual : original ⟶ next := CategoryOfElements.homMk _ _ step rfl
    have target : (⟨second, base.map step (change.app first value)⟩ : base.Elements) =
        (elementMap change).obj next :=
      Sigma.ext rfl (heq_of_eq (change.naturality step value))
    have arrows := elementsArrow_heq rfl target
      (CategoryOfElements.homMk (F := base) ⟨first, change.app first value⟩
        ⟨second, base.map step (change.app first value)⟩ step rfl)
      ((elementMap change).map contextual) HEq.rfl
    exact (familyMap_heq domain.native rfl target _ _ arrows
      (term.val original) (term.val original) HEq.rfl).trans
      (heq_of_eq (term.property contextual))

/-- The wider context universe absorbs every genuine small comprehension.
Each type field retains its authored dictionary under actual substitution. -/
abbrev cwf (D : Type u) [Category.{u} D] :
    Cwf.{max u v + 1, max u v, max (u + 1) v, max u v} where
  Ctx := D ⥤ Type (max u v)
  Sub := NaturalHom
  idS := ContextualSmallMapConstructions.identity
  compS later earlier := earlier.comp later
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty := Family
  tySub domain change := domain.reindex change
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm _ domain := domain.native.sections
  tmSub term change := ContextualSmallFamilyIdentity.reindexSection change _ term
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext _ domain := domain.extension
  wk domain := projection domain.native
  vz domain := ContextualSmallFamilyIdentity.lastVariable domain.native
  pair := pair
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := rfl
  pair_eta _ _ := rfl

def terminalBase (D : Type u) [Category.{u} D] : D ⥤ Type (max u v) where
  obj _ := PUnit.{max u v + 1}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def toTerminal (base : D ⥤ Type (max u v)) : NaturalHom base (terminalBase D) where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

def withTerminal (D : Type u) [Category.{u} D] :
    CwfWithTerminal.{max u v + 1, max u v, max (u + 1) v, max u v} where
  toCwf := cwf D
  empty := terminalBase D
  toEmpty := toTerminal
  toEmpty_unique base operation := by
    apply NaturalHom.ext
    intro point value
    exact Subsingleton.elim (show PUnit.{max u v + 1} from operation.app point value) PUnit.unit

def identityFormation (D : Type u) [Category.{u} D] : ContextualIdentityTypes.IdentityFormation (cwf.{u,v} D) where
  idTy := Family.identity
  idTy_sub _ _ _ _ := rfl

def identityIntroduction (D : Type u) [Category.{u} D] :
    ContextualIdentityTypes.IdentityReflexivity (cwf.{u,v} D) (identityFormation.{u,v} D) where
  refl term := ContextualSmallFamilyIdentity.reflexivity _ term
  refl_sub := by
    intro source target change domain term
    exact HEq.rfl

def identityElimination (D : Type u) [Category.{u} D] :
    ContextualIdentityTypes.IdentityEliminationBeta (cwf.{u,v} D)
      (identityFormation.{u,v} D) (identityIntroduction.{u,v} D) where
  reflexivitySubstitution domain := ContextualSmallFamilyIdentity.diagonal domain.native
  over_diagonal _ := rfl
  witness_is_refl _ := HEq.rfl
  j motive method := ContextualSmallFamilyIdentity.J _ motive.native method
  beta motive method := ContextualSmallFamilyIdentity.J_beta _ motive.native method

theorem identityContext_native (domain : Family base) :
    ContextualIdentityTypes.identityContext (cwf.{u,v} D) (identityFormation.{u,v} D) domain =
      ContextualSmallFamilyIdentity.identityContext domain.native := rfl

theorem termRestriction_member (domain : Family base) (change : NaturalHom other base)
    (term : domain.native.sections) (point : other.Elements) :
    (((domain.reindex change).sectionDecoder
      (ContextualSmallFamilyIdentity.reindexSection change domain.native term)).val point).val =
      ((domain.sectionDecoder term).val ((elementMap change).obj point)).val := rfl

/-! ## Full future products, sections and material application -/

def unitNative (E : Type w) [Category.{u} E] : E ⥤ Type u where
  obj _ := ULift.{u,0} PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def sectionHomEquiv {E : Type w} [Category.{u} E] (family : E ⥤ Type u) :
    family.sections ≃ WiderPresheafDependentFunctions.Hom (unitNative E) family where
  toFun term := { app point _ := term.val point, naturality step _ := term.property step }
  invFun operation := ⟨fun point => operation.app point ⟨PUnit.unit⟩,
    fun {_ _} step => operation.naturality step ⟨PUnit.unit⟩⟩
  left_inv _ := rfl
  right_inv operation := by
    apply WiderPresheafDependentFunctions.Hom.ext
    intro point argument
    rcases argument with ⟨argument⟩
    cases argument
    rfl

def lambdaEquiv (domain : Family base) (body : Family domain.extension)
    (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second)) :
    body.native.sections ≃ (domain.pi body worlds arrows).native.sections :=
  (bodySectionEquiv domain.native body.native).trans
    ((sectionHomEquiv (domain.bodyNative body)).trans
      ((ContextualSmallFamilyNativeAdjunction.smallHomEquiv domain.native
        (domain.bodyNative body) (unitNative base.Elements)).trans
        (sectionHomEquiv (domain.pi body worlds arrows).native).symm))

def applyTerm (domain : Family base) (body : Family domain.extension)
    (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
    (function : (domain.pi body worlds arrows).native.sections) (argument : domain.native.sections) :
    (body.reindex (pair (ContextualSmallMapConstructions.identity base) domain argument)).native.sections :=
  ContextualSmallFamilyIdentity.reindexSection
    (pair (ContextualSmallMapConstructions.identity base) domain argument) body.native
    ((lambdaEquiv domain body worlds arrows).symm function)

theorem lambda_value (domain : Family base) (body : Family domain.extension)
    (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
    (term : body.native.sections) (point : base.Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain.native point).Elements) :
    ((lambdaEquiv domain body worlds arrows term).val point).val argument =
      term.val ((flatten domain.native).obj
        ((ContextualSmallFamilyTypeFormers.futureArguments domain.native point).obj argument)) := rfl

theorem lambda_material_entry (domain : Family base) (body : Family domain.extension)
    (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
    (term : body.native.sections) (point : base.Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain.native point).Elements) :
    HSet.kpair ((ContextualReceiptFamilyModels.futureCoding domain.native domain.models worlds arrows point).reading argument)
        ((body.models ((flatten domain.native).obj
          ((ContextualSmallFamilyTypeFormers.futureArguments domain.native point).obj argument))).value
            (term.val ((flatten domain.native).obj
              ((ContextualSmallFamilyTypeFormers.futureArguments domain.native point).obj argument)))) ∈
      ((domain.pi body worlds arrows).models point).value
        ((lambdaEquiv domain body worlds arrows term).val point) :=
  ContextualReceiptFamilyModels.pi_entry domain.native domain.models (domain.bodyNative body)
    (domain.bodyModels body) worlds arrows point ((lambdaEquiv domain body worlds arrows term).val point) argument

theorem apply_lambda (domain : Family base) (body : Family domain.extension)
    (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
    (term : body.native.sections) (argument : domain.native.sections) :
    applyTerm domain body worlds arrows (lambdaEquiv domain body worlds arrows term) argument =
      ContextualSmallFamilyIdentity.reindexSection
        (pair (ContextualSmallMapConstructions.identity base) domain argument) body.native term := by
  unfold applyTerm
  rw [Equiv.symm_apply_apply]

theorem lambda_eta (domain : Family base) (body : Family domain.extension)
    (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
    (function : (domain.pi body worlds arrows).native.sections) :
    lambdaEquiv domain body worlds arrows ((lambdaEquiv domain body worlds arrows).symm function) = function := by
  exact Equiv.apply_symm_apply _ function

def products (D : Type u) [Category.{u} D] (worlds : ArgumentCoding D)
    (arrows : (first second : D) → ArgumentCoding (first ⟶ second)) :
    ContextualProductComparison.DependentProductBeta (cwf.{u,v} D) where
  pi domain body := domain.pi body worlds arrows
  lam := lambdaEquiv _ _ worlds arrows
  app := applyTerm _ _ worlds arrows
  beta term argument := apply_lambda _ _ worlds arrows term argument

/-! ## Dependent sums retain both complete section coordinates -/

def sigmaFirst (domain : Family base) (body : Family domain.extension)
    (term : (domain.sigma body).native.sections) : domain.native.sections :=
  ⟨fun point => (term.val point).1,
    fun {_ _} step => congrArg Sigma.fst (term.property step)⟩

def sigmaSecond (domain : Family base) (body : Family domain.extension)
    (term : (domain.sigma body).native.sections) :
    (body.reindex (pair (ContextualSmallMapConstructions.identity base) domain (sigmaFirst domain body term))).native.sections :=
  ⟨fun point => (term.val point).2, by
    intro first second step
    have coordinates := term.property step
    have firstSame : domain.native.map step (term.val first).1 = (term.val second).1 :=
      congrArg Sigma.fst coordinates
    have target : (flatten domain.native).obj
        ⟨second, domain.native.map step (term.val first).1⟩ =
      (elementMap (pair (ContextualSmallMapConstructions.identity base) domain (sigmaFirst domain body term))).obj second :=
      congrArg (fun argument => (⟨second.1, ⟨second.2, argument⟩⟩ : domain.extension.Elements)) firstSame
    have arrows := elementsArrow_heq rfl target
      ((flatten domain.native).map (ContextualSmallFamilyTypeFormers.argumentStep domain.native step (term.val first).1))
      ((elementMap (pair (ContextualSmallMapConstructions.identity base) domain (sigmaFirst domain body term))).map step) HEq.rfl
    have values := familyMap_heq body.native rfl target _ _ arrows
      (term.val first).2 (term.val first).2 HEq.rfl
    exact eq_of_heq (values.symm.trans (Sigma.mk.inj_iff.mp coordinates).2)⟩

def sigmaPair (domain : Family base) (body : Family domain.extension)
    (firstTerm : domain.native.sections)
    (secondTerm : (body.reindex (pair (ContextualSmallMapConstructions.identity base) domain firstTerm)).native.sections) :
    (domain.sigma body).native.sections :=
  ⟨fun point => ⟨firstTerm.val point, secondTerm.val point⟩, by
    intro first second step
    apply Sigma.ext (firstTerm.property step)
    have target : (flatten domain.native).obj
        ⟨second, domain.native.map step (firstTerm.val first)⟩ =
      (elementMap (pair (ContextualSmallMapConstructions.identity base) domain firstTerm)).obj second :=
      congrArg (fun argument => (⟨second.1, ⟨second.2, argument⟩⟩ : domain.extension.Elements)) (firstTerm.property step)
    have arrows := elementsArrow_heq rfl target
      ((flatten domain.native).map (ContextualSmallFamilyTypeFormers.argumentStep domain.native step (firstTerm.val first)))
      ((elementMap (pair (ContextualSmallMapConstructions.identity base) domain firstTerm)).map step) HEq.rfl
    exact (familyMap_heq body.native rfl target _ _ arrows
      (secondTerm.val first) (secondTerm.val first) HEq.rfl).trans
      (heq_of_eq (secondTerm.property step))⟩

def sums (D : Type u) [Category.{u} D] : ContextualSumComparison.DependentSumBeta (cwf.{u,v} D) where
  sigma := Family.sigma
  pair := sigmaPair _ _
  fst := sigmaFirst _ _
  snd := sigmaSecond _ _
  fst_pair _ _ := rfl
  snd_pair _ _ := HEq.rfl

theorem sigma_eta (domain : Family base) (body : Family domain.extension)
    (term : (domain.sigma body).native.sections) :
    sigmaPair domain body (sigmaFirst domain body term) (sigmaSecond domain body term) = term := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialCwf
