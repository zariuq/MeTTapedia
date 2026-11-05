import Mettapedia.Logic.HOL.SetFamilyUnionProofs

/-!
# Retained proofs from primitive universe closure

Transitivity, union, powerset and bounded replacement are explicit formulas.
Subset and separation closure are derived from them and the ordinary set
laws. No closure rule for a derived type former is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetUniverseProofs
open SetComprehensionProofs SetMembershipProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (set mapping powerLaw emptyLaw separationLaw)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

def mapsInto (universeSet domain : Term Const Γ set) (function : Term Const Γ mapping) : Formula Const Γ :=
  .all (.imp (member core (.var .vz) (HOL.weaken domain))
    (member core (.app (HOL.weaken function) (.var .vz)) (HOL.weaken universeSet)))

def transitive (universeSet : Term Const Γ set) : Formula Const Γ :=
  .all (.imp (member core (.var .vz) (HOL.weaken universeSet))
    (included core (.var .vz) (HOL.weaken universeSet)))

def unaryClosed (universeSet : Term Const Γ set) (operation : Term Const Γ mapping) : Formula Const Γ :=
  .all (.imp (member core (.var .vz) (HOL.weaken universeSet))
    (member core (.app (HOL.weaken operation) (.var .vz)) (HOL.weaken universeSet)))

def replacementClosed (universeSet : Term Const Γ set) : Formula Const Γ :=
  .all (σ := set) (.imp (member core (.var .vz) (HOL.weaken universeSet))
    (.all (σ := mapping) (.imp
      (mapsInto core (HOL.weaken (HOL.weaken universeSet)) (.var (.vs .vz)) (.var .vz))
      (member core (image core (.var (.vs .vz)) (.var .vz)) (HOL.weaken (HOL.weaken universeSet))))))

@[simp] theorem subst_included (theta : Subst Const Γ Ξ) (left right : Term Const Γ set) :
    HOL.subst theta (included core left right) = included core (HOL.subst theta left) (HOL.subst theta right) := by
  simp only [included,member,HOL.subst,HOL.subst_weaken,Subst.lift]

@[simp] theorem subst_mapsInto (theta : Subst Const Γ Ξ) (universeSet domain : Term Const Γ set)
    (function : Term Const Γ mapping) : HOL.subst theta (mapsInto core universeSet domain function) =
      mapsInto core (HOL.subst theta universeSet) (HOL.subst theta domain) (HOL.subst theta function) := by
  simp only [mapsInto,member,HOL.subst,HOL.subst_weaken,Subst.lift]

@[simp] theorem subst_transitive (theta : Subst Const Γ Ξ) (universeSet : Term Const Γ set) :
    HOL.subst theta (transitive core universeSet) = transitive core (HOL.subst theta universeSet) := by
  simp only [transitive,member,HOL.subst,subst_included,HOL.subst_weaken,Subst.lift]

@[simp] theorem subst_unaryClosed (theta : Subst Const Γ Ξ) (universeSet : Term Const Γ set)
    (operation : Term Const Γ mapping) : HOL.subst theta (unaryClosed core universeSet operation) =
      unaryClosed core (HOL.subst theta universeSet) (HOL.subst theta operation) := by
  simp only [unaryClosed,member,HOL.subst,HOL.subst_weaken,Subst.lift]

@[simp] theorem subst_replacementClosed (theta : Subst Const Γ Ξ) (universeSet : Term Const Γ set) :
    HOL.subst theta (replacementClosed core universeSet) = replacementClosed core (HOL.subst theta universeSet) := by
  simp only [replacementClosed,member,image,HOL.subst,subst_mapsInto,HOL.subst_weaken,Subst.lift]
  rfl

theorem rename_mapsInto (rho : Rename Unit Γ Ξ) (universeSet domain : Term Const Γ set)
    (function : Term Const Γ mapping) : HOL.rename rho (mapsInto core universeSet domain function) =
      mapsInto core (HOL.rename rho universeSet) (HOL.rename rho domain) (HOL.rename rho function) := by
  simpa only [HOL.subst_ofRename] using subst_mapsInto core (Subst.ofRename rho) universeSet domain function

theorem rename_transitive (rho : Rename Unit Γ Ξ) (universeSet : Term Const Γ set) :
    HOL.rename rho (transitive core universeSet) = transitive core (HOL.rename rho universeSet) := by
  simpa only [HOL.subst_ofRename] using subst_transitive core (Subst.ofRename rho) universeSet

theorem rename_unaryClosed (rho : Rename Unit Γ Ξ) (universeSet : Term Const Γ set) (operation : Term Const Γ mapping) :
    HOL.rename rho (unaryClosed core universeSet operation) =
      unaryClosed core (HOL.rename rho universeSet) (HOL.rename rho operation) := by
  simpa only [HOL.subst_ofRename] using subst_unaryClosed core (Subst.ofRename rho) universeSet operation

theorem rename_replacementClosed (rho : Rename Unit Γ Ξ) (universeSet : Term Const Γ set) :
    HOL.rename rho (replacementClosed core universeSet) = replacementClosed core (HOL.rename rho universeSet) := by
  simpa only [HOL.subst_ofRename] using subst_replacementClosed core (Subst.ofRename rho) universeSet

structure Laws (universeSet : Term Const Γ set) (assumptions : List (Formula Const Γ)) where
  transitive : ProofSyntax Const assumptions (transitive core universeSet)
  union : ProofSyntax Const assumptions (unaryClosed core universeSet (.const (core .union)))
  power : ProofSyntax Const assumptions (unaryClosed core universeSet (.const (core .power)))
  replacement : ProofSyntax Const assumptions (replacementClosed core universeSet)

def Laws.prepend {core : Core Const} {universeSet : Term Const Γ set} (laws : Laws core universeSet Δ)
    (formula : Formula Const Γ) : Laws core universeSet (formula :: Δ) where
  transitive := laws.transitive.prepend formula
  union := laws.union.prepend formula
  power := laws.power.prepend formula
  replacement := laws.replacement.prepend formula

def Laws.weaken {core : Core Const} {universeSet : Term Const Γ set} (laws : Laws core universeSet Δ)
    (added : Ty Unit) : Laws core (HOL.weaken (σ := added) universeSet) (weakenHyps (σ := added) Δ) where
  transitive := by
    apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof laws.transitive)
    simp only [HOL.weaken,rename_transitive]
  union := by
    apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof laws.union)
    simp only [HOL.weaken,rename_unaryClosed,HOL.rename]
  power := by
    apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof laws.power)
    simp only [HOL.weaken,rename_unaryClosed,HOL.rename]
  replacement := by
    apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof laws.replacement)
    simp only [HOL.weaken,rename_replacementClosed]

private theorem substituteWeak {type added : Ty Unit} (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

def mapsIntoAt (universeSet domain : Term Const Γ set) (function : Term Const Γ mapping) (point : Term Const Γ set)
    (body : ProofSyntax Const Δ (mapsInto core universeSet domain function))
    (inDomain : ProofSyntax Const Δ (member core point domain)) :
    ProofSyntax Const Δ (member core (.app function point) universeSet) := by
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ (.allE point body)) inDomain
  simp only [instantiate,member,HOL.subst,Subst.single,substituteWeak]

def transitiveAt (universeSet bound point : Term Const Γ set) (laws : Laws core universeSet Δ)
    (inUniverse : ProofSyntax Const Δ (member core bound universeSet))
    (inBound : ProofSyntax Const Δ (member core point bound)) :
    ProofSyntax Const Δ (member core point universeSet) := by
  have rule : ProofSyntax Const Δ (.imp (member core bound universeSet) (included core bound universeSet)) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE bound laws.transitive)
    simp only [instantiate,member,HOL.subst,subst_included,Subst.single,substituteWeak]
  exact subsetElim core bound universeSet point (.impE rule inUniverse) inBound

def unaryAt (universeSet : Term Const Γ set) (operation : Term Const Γ mapping) (point : Term Const Γ set)
    (closed : ProofSyntax Const Δ (unaryClosed core universeSet operation))
    (inUniverse : ProofSyntax Const Δ (member core point universeSet)) :
    ProofSyntax Const Δ (member core (.app operation point) universeSet) := by
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ (.allE point closed)) inUniverse
  simp only [instantiate,member,HOL.subst,Subst.single,substituteWeak]

def replacementAt (universeSet domain : Term Const Γ set) (function : Term Const Γ mapping)
    (laws : Laws core universeSet Δ) (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (body : ProofSyntax Const Δ (mapsInto core universeSet domain function)) :
    ProofSyntax Const Δ (member core (image core domain function) universeSet) := by
  have first : ProofSyntax Const Δ (.imp (member core domain universeSet)
      (.all (.imp (mapsInto core (HOL.weaken universeSet) (HOL.weaken domain) (.var .vz))
        (member core (image core (HOL.weaken domain) (.var .vz)) (HOL.weaken universeSet))))) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE domain laws.replacement)
    simp only [instantiate,member,image,HOL.subst,subst_mapsInto,Subst.single,Subst.lift,HOL.subst_weaken,substituteWeak]
    rfl
  have second := ProofSyntax.allE function (.impE first domainMember)
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ second) body
  simp only [instantiate,member,image,HOL.subst,subst_mapsInto,Subst.single,substituteWeak]

def subsetClosed (universeSet bound value : Term Const Γ set) (laws : Laws core universeSet Δ)
    (powerProof : ProofSyntax Const Δ (lawAt core powerLaw))
    (inUniverse : ProofSyntax Const Δ (member core bound universeSet))
    (inclusion : ProofSyntax Const Δ (included core value bound)) :
    ProofSyntax Const Δ (member core value universeSet) :=
  transitiveAt core universeSet (power core bound) value laws
    (unaryAt core universeSet (.const (core .power)) bound laws.power inUniverse)
    (.impE (.andER (powerset core bound value powerProof)) inclusion)

def emptyClosed (universeSet anchor : Term Const Γ set) (laws : Laws core universeSet Δ)
    (emptyProof : ProofSyntax Const Δ (lawAt core emptyLaw))
    (powerProof : ProofSyntax Const Δ (lawAt core powerLaw))
    (anchorMember : ProofSyntax Const Δ (member core anchor universeSet)) :
    ProofSyntax Const Δ (member core (.const (core .empty)) universeSet) := by
  apply subsetClosed core universeSet anchor _ laws powerProof anchorMember
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.botE
  exact .notE ((emptyElim core (.var .vz) (weakenLaw core _ emptyProof)).prepend _) (.hyp 0)

def separationClosed (universeSet bound : Term Const Γ set)
    (predicate : Term Const Γ Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.predicate)
    (laws : Laws core universeSet Δ) (powerProof : ProofSyntax Const Δ (lawAt core powerLaw))
    (separationProof : ProofSyntax Const Δ (lawAt core separationLaw))
    (inUniverse : ProofSyntax Const Δ (member core bound universeSet)) :
    ProofSyntax Const Δ (member core (separate core bound predicate) universeSet) := by
  apply subsetClosed core universeSet bound _ laws powerProof inUniverse
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  exact .andEL (.impE (.andEL (SetComprehensionProofs.separation core (HOL.weaken bound)
    (HOL.weaken predicate) (.var .vz) ((weakenLaw core _ separationProof).prepend _))) (.hyp 0))

def weakenMapsInto (universeSet domain : Term Const Γ set) (function : Term Const Γ mapping)
    (body : ProofSyntax Const Δ (mapsInto core universeSet domain function)) :
    ProofSyntax Const (weakenHyps (σ := set) Δ)
      (mapsInto core (HOL.weaken universeSet) (HOL.weaken domain) (HOL.weaken function)) := by
  apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof body)
  simp only [HOL.weaken,rename_mapsInto]

structure Laws.Free {core : Core Const} {universeSet : Term Const Γ set} (laws : Laws core universeSet Δ) : Prop where
  transitive : laws.transitive.FunctionExtensionalityFree
  union : laws.union.FunctionExtensionalityFree
  power : laws.power.FunctionExtensionalityFree
  replacement : laws.replacement.FunctionExtensionalityFree

theorem Laws.prepend_free {core : Core Const} {universeSet : Term Const Γ set} (laws : Laws core universeSet Δ)
    (formula : Formula Const Γ) (free : laws.Free) : (laws.prepend formula).Free where
  transitive := by simpa [Laws.prepend,ProofSyntax.prepend] using free.transitive
  union := by simpa [Laws.prepend,ProofSyntax.prepend] using free.union
  power := by simpa [Laws.prepend,ProofSyntax.prepend] using free.power
  replacement := by simpa [Laws.prepend,ProofSyntax.prepend] using free.replacement

theorem Laws.weaken_free {core : Core Const} {universeSet : Term Const Γ set} (laws : Laws core universeSet Δ)
    (added : Ty Unit) (free : laws.Free) : (laws.weaken added).Free where
  transitive := by simpa [Laws.weaken,PredicateFixedPoint.weakenProof] using free.transitive
  union := by simpa [Laws.weaken,PredicateFixedPoint.weakenProof] using free.union
  power := by simpa [Laws.weaken,PredicateFixedPoint.weakenProof] using free.power
  replacement := by simpa [Laws.weaken,PredicateFixedPoint.weakenProof] using free.replacement

theorem mapsIntoAt_free (universeSet domain : Term Const Γ set) (function : Term Const Γ mapping) (point : Term Const Γ set)
    (body : ProofSyntax Const Δ (mapsInto core universeSet domain function))
    (inDomain : ProofSyntax Const Δ (member core point domain))
    (bodyFree : body.FunctionExtensionalityFree) (domainFree : inDomain.FunctionExtensionalityFree) :
    (mapsIntoAt core universeSet domain function point body inDomain).FunctionExtensionalityFree := by
  simp [mapsIntoAt,ProofSyntax.FunctionExtensionalityFree,bodyFree,domainFree]

theorem transitiveAt_free (universeSet bound point : Term Const Γ set) (laws : Laws core universeSet Δ)
    (inUniverse : ProofSyntax Const Δ (member core bound universeSet))
    (inBound : ProofSyntax Const Δ (member core point bound))
    (lawsFree : laws.Free) (universeFree : inUniverse.FunctionExtensionalityFree) (boundFree : inBound.FunctionExtensionalityFree) :
    (transitiveAt core universeSet bound point laws inUniverse inBound).FunctionExtensionalityFree := by
  simp [transitiveAt,subsetElim,ProofSyntax.FunctionExtensionalityFree,lawsFree.transitive,universeFree,boundFree]

theorem unaryAt_free (universeSet : Term Const Γ set) (operation : Term Const Γ mapping) (point : Term Const Γ set)
    (closed : ProofSyntax Const Δ (unaryClosed core universeSet operation))
    (inUniverse : ProofSyntax Const Δ (member core point universeSet))
    (closedFree : closed.FunctionExtensionalityFree) (universeFree : inUniverse.FunctionExtensionalityFree) :
    (unaryAt core universeSet operation point closed inUniverse).FunctionExtensionalityFree := by
  simp [unaryAt,ProofSyntax.FunctionExtensionalityFree,closedFree,universeFree]

theorem replacementAt_free (universeSet domain : Term Const Γ set) (function : Term Const Γ mapping)
    (laws : Laws core universeSet Δ) (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (body : ProofSyntax Const Δ (mapsInto core universeSet domain function))
    (lawsFree : laws.Free) (domainFree : domainMember.FunctionExtensionalityFree) (bodyFree : body.FunctionExtensionalityFree) :
    (replacementAt core universeSet domain function laws domainMember body).FunctionExtensionalityFree := by
  simp [replacementAt,ProofSyntax.FunctionExtensionalityFree,lawsFree.replacement,domainFree,bodyFree]

theorem subsetClosed_free (universeSet bound value : Term Const Γ set) (laws : Laws core universeSet Δ)
    (powerProof : ProofSyntax Const Δ (lawAt core powerLaw))
    (inUniverse : ProofSyntax Const Δ (member core bound universeSet))
    (inclusion : ProofSyntax Const Δ (included core value bound))
    (lawsFree : laws.Free) (powerFree : powerProof.FunctionExtensionalityFree)
    (universeFree : inUniverse.FunctionExtensionalityFree) (inclusionFree : inclusion.FunctionExtensionalityFree) :
    (subsetClosed core universeSet bound value laws powerProof inUniverse inclusion).FunctionExtensionalityFree :=
  transitiveAt_free core universeSet (power core bound) value laws _ _ lawsFree
    (unaryAt_free core universeSet _ bound laws.power inUniverse lawsFree.power universeFree)
    ⟨(powerset_free core bound value powerProof).mpr powerFree,inclusionFree⟩

theorem emptyClosed_free (universeSet anchor : Term Const Γ set) (laws : Laws core universeSet Δ)
    (emptyProof : ProofSyntax Const Δ (lawAt core emptyLaw))
    (powerProof : ProofSyntax Const Δ (lawAt core powerLaw))
    (anchorMember : ProofSyntax Const Δ (member core anchor universeSet))
    (lawsFree : laws.Free) (emptyFree : emptyProof.FunctionExtensionalityFree)
    (powerFree : powerProof.FunctionExtensionalityFree) (anchorFree : anchorMember.FunctionExtensionalityFree) :
    (emptyClosed core universeSet anchor laws emptyProof powerProof anchorMember).FunctionExtensionalityFree := by
  apply subsetClosed_free
  · exact lawsFree
  · exact powerFree
  · exact anchorFree
  · change ((emptyElim core (.var .vz) (weakenLaw (added := set) core _ emptyProof)).prepend _).FunctionExtensionalityFree ∧ True
    constructor
    · simpa [ProofSyntax.prepend] using (emptyElim_free core _ _).mpr
        (weakenLaw_free (added := set) core _ emptyProof emptyFree)
    · trivial

theorem separationClosed_free (universeSet bound : Term Const Γ set)
    (predicate : Term Const Γ Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.predicate)
    (laws : Laws core universeSet Δ) (powerProof : ProofSyntax Const Δ (lawAt core powerLaw))
    (separationProof : ProofSyntax Const Δ (lawAt core separationLaw))
    (inUniverse : ProofSyntax Const Δ (member core bound universeSet))
    (lawsFree : laws.Free) (powerFree : powerProof.FunctionExtensionalityFree)
    (separationFree : separationProof.FunctionExtensionalityFree) (universeFree : inUniverse.FunctionExtensionalityFree) :
    (separationClosed core universeSet bound predicate laws powerProof separationProof inUniverse).FunctionExtensionalityFree := by
  apply subsetClosed_free
  · exact lawsFree
  · exact powerFree
  · exact universeFree
  · change (SetComprehensionProofs.separation core (HOL.weaken bound) (HOL.weaken predicate) (.var .vz)
      ((weakenLaw (added := set) core _ separationProof).prepend _)).FunctionExtensionalityFree ∧ True
    constructor
    · apply (separation_free core _ _ _ _).mpr
      simpa [ProofSyntax.prepend] using weakenLaw_free (added := set) core _ separationProof separationFree
    · trivial

theorem weakenMapsInto_free (universeSet domain : Term Const Γ set) (function : Term Const Γ mapping)
    (body : ProofSyntax Const Δ (mapsInto core universeSet domain function)) (free : body.FunctionExtensionalityFree) :
    (weakenMapsInto core universeSet domain function body).FunctionExtensionalityFree := by
  simpa [weakenMapsInto,PredicateFixedPoint.weakenProof] using free

end Mettapedia.Logic.HOL.SetUniverseProofs
