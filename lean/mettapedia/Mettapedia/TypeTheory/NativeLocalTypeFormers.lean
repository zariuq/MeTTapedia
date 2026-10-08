import Mettapedia.TypeTheory.NativeLocalFunctionParameters
import Mettapedia.TypeTheory.DisplayedPresheafSigma

/-!
# Dependent formers over native local family presentations

The parameter space records the original domain parameters and a natural
choice of codomain parameters at every dependent argument. The supplied
codomain name determines the context's map into that space. Native products
and sums are then formed once over the parameter space and pulled back along
the supplied name. Substitution retains the parameter families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalTypeFormers

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafPi DisplayedPresheafPiSubstitution
open DisplayedPresheafSigma ContextualLocalUniverses

universe u
variable {C : Type u} [Category.{u} C]
variable {X Y : Face.{u, u, u} C}

abbrev NativeType (X : Face.{u, u, u} C) := LocalType (presheafCwf C) X

noncomputable def formerParameters (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) : Face.{u, u, u} C :=
  NativeLocalFunctionParameters.parameters A.family B.parameters

noncomputable def parameterDomain (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    DisplayedFamily.{u, u, u, u} (formerParameters A B) :=
  NativeLocalFunctionParameters.argumentFamily A.family B.parameters

noncomputable def parameterBody (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    DisplayedFamily.{u, u, u, u} (totalSpace (parameterDomain A B)) :=
  reindexDisplayed (NativeLocalFunctionParameters.evaluation A.family B.parameters) B.family

noncomputable def formerName (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) : X ⟶ formerParameters A B :=
  NativeLocalFunctionParameters.name A.name A.family B.parameters B.name

noncomputable def pi (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) : NativeType X :=
  ⟨formerParameters A B, piDisplayed (parameterDomain A B) (parameterBody A B),
    formerName A B⟩

noncomputable def sigma (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) : NativeType X :=
  ⟨formerParameters A B, sigmaDisplayed (parameterDomain A B) (parameterBody A B),
    formerName A B⟩

theorem parameterDomain_decode (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    reindexDisplayed (formerName A B) (parameterDomain A B) = A.decoded := by
  change reindexDisplayed
    (NativeLocalFunctionParameters.name A.name A.family B.parameters B.name)
    (reindexDisplayed (totalProjection
      (NativeLocalFunctionParameters.choices A.family B.parameters)) A.family) = _
  exact congrArg (fun map => reindexDisplayed map A.family)
    (NativeLocalFunctionParameters.name_projection A.name A.family B.parameters B.name)

theorem parameterBody_decode (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    reindexDisplayed (totalReindexMap (formerName A B) (parameterDomain A B))
      (parameterBody A B) = B.decoded := by
  change reindexDisplayed
    (NativeLocalFunctionParameters.argumentName A.name A.family B.parameters B.name)
    (reindexDisplayed (NativeLocalFunctionParameters.evaluation A.family B.parameters)
      B.family) = _
  exact congrArg (fun map => reindexDisplayed map B.family)
    (NativeLocalFunctionParameters.name_evaluation A.name A.family B.parameters B.name)

noncomputable def piDecodeIso (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (show DisplayedFamily.{u, u, u, u} X from (pi A B).decoded) ≅
      piDisplayed A.decoded B.decoded :=
  (piSubstitutionIso (formerName A B) (parameterDomain A B) (parameterBody A B)).symm ≪≫
    eqToIso (congrArg (piDisplayed A.decoded) (parameterBody_decode A B))

theorem sigmaDecode (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (sigma A B).decoded = sigmaDisplayed A.decoded B.decoded := by
  change reindexDisplayed (formerName A B)
    (sigmaDisplayed (parameterDomain A B) (parameterBody A B)) = _
  rw [sigmaDisplayed_reindex, parameterBody_decode]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pi_reindex (s : Y ⟶ X) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (pi A B).reindex s =
      pi (A.reindex s) (B.reindex (totalReindexMap s A.decoded)) := by
  exact congrArg (fun map => (⟨formerParameters A B,
      piDisplayed (parameterDomain A B) (parameterBody A B), map⟩ : NativeType Y))
    (NativeLocalFunctionParameters.name_substitution s A.name A.family
      B.parameters B.name).symm

set_option backward.isDefEq.respectTransparency false in
theorem sigma_reindex (s : Y ⟶ X) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    (sigma A B).reindex s =
      sigma (A.reindex s) (B.reindex (totalReindexMap s A.decoded)) := by
  exact congrArg (fun map => (⟨formerParameters A B,
      sigmaDisplayed (parameterDomain A B) (parameterBody A B), map⟩ : NativeType Y))
    (NativeLocalFunctionParameters.name_substitution s A.name A.family
      B.parameters B.name).symm

end Mettapedia.TypeTheory.NativeLocalTypeFormers
