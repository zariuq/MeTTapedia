import Mettapedia.Logic.HOL.SetPairingProofs
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Retained graph construction over the material-set profile

Graphs are functional images of the declared domain under the ordered-pair
mapping. Membership and functionality are derived from replacement and the
existing pairing construction, with actual source binders and hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetGraphProofs
open SetComprehensionProofs SetMembershipProofs SetPairingProofs ContextualTrinity
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

def mapping (function : Term Const Γ (object ⇒ object)) : Term Const Γ (object ⇒ object) :=
  .lam (ordered core epsilon (.var .vz) (.app (HOL.weaken function) (.var .vz)))

def graph (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object)) : Term Const Γ object :=
  image core domain (mapping core epsilon function)

@[simp] theorem subst_mapping (theta : Subst Const Γ Ξ) (function : Term Const Γ (object ⇒ object)) :
    HOL.subst theta (mapping core epsilon function) = mapping core epsilon (HOL.subst theta function) := by
  simp only [mapping,HOL.subst,subst_ordered,HOL.subst_weaken,Subst.lift]

@[simp] theorem subst_graph (theta : Subst Const Γ Ξ) (domain : Term Const Γ object)
    (function : Term Const Γ (object ⇒ object)) :
    HOL.subst theta (graph core epsilon domain function) =
      graph core epsilon (HOL.subst theta domain) (HOL.subst theta function) := by
  simp only [graph,image,HOL.subst,subst_mapping]

theorem rename_mapping (rho : Rename Unit Γ Ξ) (function : Term Const Γ (object ⇒ object)) :
    HOL.rename rho (mapping core epsilon function) = mapping core epsilon (HOL.rename rho function) := by
  simpa only [HOL.subst_ofRename] using subst_mapping core epsilon (Subst.ofRename rho) function

theorem rename_graph (rho : Rename Unit Γ Ξ) (domain : Term Const Γ object)
    (function : Term Const Γ (object ⇒ object)) :
    HOL.rename rho (graph core epsilon domain function) =
      graph core epsilon (HOL.rename rho domain) (HOL.rename rho function) := by
  simpa only [HOL.subst_ofRename] using subst_graph core epsilon (Subst.ofRename rho) domain function

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

def mappingBeta (function : Term Const Γ (object ⇒ object)) (point : Term Const Γ object) :
    ProofSyntax Const Δ (.eq (.app (mapping core epsilon function) point)
      (ordered core epsilon point (.app function point))) := by
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta point
    (ordered core epsilon (.var .vz) (.app (HOL.weaken function) (.var .vz))))
  simp only [mapping,instantiate,subst_ordered,HOL.subst,Subst.single,substituteWeak]

def orderedCongrSecond (point : Term Const Γ object) {left right : Term Const Γ object}
    (equal : ProofSyntax Const Δ (.eq left right)) :
    ProofSyntax Const Δ (.eq (ordered core epsilon point left) (ordered core epsilon point right)) := by
  apply ProofSyntax.castIndices rfl ?_
    (holeCongr (ordered core epsilon (HOL.weaken point) (.var .vz)) equal)
  simp only [instantiate,subst_ordered,HOL.subst,Subst.single,substituteWeak]

def graphIntro (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point : Term Const Γ object)
    (replacement : ProofSyntax Const Δ (lawAt core Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.replacementLaw))
    (admitted : ProofSyntax Const Δ (member core point domain)) :
    ProofSyntax Const Δ (member core (ordered core epsilon point (.app function point))
      (graph core epsilon domain function)) :=
  transportValue core _ (mappingBeta core epsilon function point)
    (imageIntro core domain (mapping core epsilon function) point replacement admitted)

def graphElim (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core (ordered core epsilon point value)
      (graph core epsilon domain function))) :
    ProofSyntax Const Δ (.and (member core point domain) (.eq (.app function point) value)) := by
  have imageWitness := ProofSyntax.impE
    (.andEL (SetComprehensionProofs.replacement core domain (mapping core epsilon function)
      (ordered core epsilon point value) laws.replacement)) admitted
  refine ProofSyntax.exE imageWitness ?_
  let body : Formula Const (object :: Γ) :=
    .and (member core (.var .vz) (HOL.weaken domain))
      (.eq (.app (HOL.weaken (mapping core epsilon function)) (.var .vz))
        (HOL.weaken (ordered core epsilon point value)))
  let assumptions := body :: weakenHyps (σ := object) Δ
  let raised := (laws.weaken object).prepend body
  have witness : ProofSyntax Const assumptions body := .hyp 0
  have pairEqual : ProofSyntax Const assumptions
      (.eq (ordered core epsilon (.var .vz) (.app (HOL.weaken function) (.var .vz)))
        (ordered core epsilon (HOL.weaken point) (HOL.weaken value))) := by
    apply ProofSyntax.eqTrans (ProofSyntax.eqSymm (mappingBeta core epsilon (HOL.weaken function) (.var .vz)))
    apply ProofSyntax.castIndices rfl ?_ (.andER witness)
    simp only [HOL.weaken,rename_mapping,rename_ordered]
  have fields := orderedInjective core epsilon (.var .vz) (.app (HOL.weaken function) (.var .vz))
    (HOL.weaken point) (HOL.weaken value) raised pairEqual
  change ProofSyntax Const assumptions
    (.and (member core (HOL.weaken point) (HOL.weaken domain))
      (.eq (.app (HOL.weaken function) (HOL.weaken point)) (HOL.weaken value)))
  exact .andI (transportValue core _ (.andEL fields) (.andEL witness))
    (.eqTrans (.eqSymm (.eqAppArg (HOL.weaken function) (.andEL fields))) (.andER fields))

def membership (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ) :
    ProofSyntax Const Δ (.and
      (.imp (member core (ordered core epsilon point value) (graph core epsilon domain function))
        (.and (member core point domain) (.eq (.app function point) value)))
      (.imp (.and (member core point domain) (.eq (.app function point) value))
        (member core (ordered core epsilon point value) (graph core epsilon domain function)))) :=
  .andI (.impI (graphElim core epsilon domain function point value (laws.prepend _) (.hyp 0)))
    (.impI (transportValue core _ (orderedCongrSecond core epsilon point (.andER (.hyp 0)))
      (graphIntro core epsilon domain function point ((laws.prepend _).replacement) (.andEL (.hyp 0)))))

def functional (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point left right : Term Const Γ object) (laws : Laws core epsilon Δ)
    (first : ProofSyntax Const Δ (member core (ordered core epsilon point left) (graph core epsilon domain function)))
    (second : ProofSyntax Const Δ (member core (ordered core epsilon point right) (graph core epsilon domain function))) :
    ProofSyntax Const Δ (.eq left right) :=
  .eqTrans (.eqSymm (.andER (graphElim core epsilon domain function point left laws first)))
    (.andER (graphElim core epsilon domain function point right laws second))

def outside (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (absent : ProofSyntax Const Δ (.not (member core point domain))) :
    ProofSyntax Const Δ (.not (member core (ordered core epsilon point value) (graph core epsilon domain function))) :=
  .notI (.notE (absent.prepend _) (.andEL
    (graphElim core epsilon domain function point value (laws.prepend _) (.hyp 0))))

theorem mappingBeta_free (function : Term Const Γ (object ⇒ object)) (point : Term Const Γ object) :
    (mappingBeta (Δ := Δ) core epsilon function point).FunctionExtensionalityFree := by
  simp [mappingBeta,ProofSyntax.FunctionExtensionalityFree]

theorem orderedCongrSecond_free (point : Term Const Γ object) {left right : Term Const Γ object}
    (equal : ProofSyntax Const Δ (.eq left right)) (free : equal.FunctionExtensionalityFree) :
    (orderedCongrSecond core epsilon point equal).FunctionExtensionalityFree := by
  simpa [orderedCongrSecond] using free

theorem graphIntro_free (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point : Term Const Γ object)
    (replacement : ProofSyntax Const Δ (lawAt core Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.replacementLaw))
    (admitted : ProofSyntax Const Δ (member core point domain))
    (lawFree : replacement.FunctionExtensionalityFree) (admittedFree : admitted.FunctionExtensionalityFree) :
    (graphIntro core epsilon domain function point replacement admitted).FunctionExtensionalityFree :=
  ⟨mappingBeta_free core epsilon _ _,imageIntro_free core _ _ _ _ _ lawFree admittedFree⟩

theorem graphElim_free (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core (ordered core epsilon point value)
      (graph core epsilon domain function)))
    (lawsFree : laws.Free) (admittedFree : admitted.FunctionExtensionalityFree) :
    (graphElim core epsilon domain function point value laws admitted).FunctionExtensionalityFree := by
  simp [graphElim,ProofSyntax.FunctionExtensionalityFree,SetComprehensionProofs.replacement,
    transportValue,valueCongr,mappingBeta,lawsFree.replacement,admittedFree]
  apply orderedInjective_free
  · exact (laws.weaken object).prepend_free _ (laws.weaken_free object lawsFree)
  · simp [ProofSyntax.FunctionExtensionalityFree]

theorem membership_free (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ) (free : laws.Free) :
    (membership core epsilon domain function point value laws).FunctionExtensionalityFree := by
  simp only [membership,ProofSyntax.FunctionExtensionalityFree]
  refine ⟨graphElim_free core epsilon _ _ _ _ _ _ (laws.prepend_free _ free) trivial,?_⟩
  exact ⟨orderedCongrSecond_free core epsilon _ _ trivial,
    graphIntro_free core epsilon _ _ _ _ _ (by simpa [Laws.prepend,ProofSyntax.prepend] using free.replacement) trivial⟩

theorem functional_free (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point left right : Term Const Γ object) (laws : Laws core epsilon Δ)
    (first : ProofSyntax Const Δ (member core (ordered core epsilon point left) (graph core epsilon domain function)))
    (second : ProofSyntax Const Δ (member core (ordered core epsilon point right) (graph core epsilon domain function)))
    (lawsFree : laws.Free) (firstFree : first.FunctionExtensionalityFree) (secondFree : second.FunctionExtensionalityFree) :
    (functional core epsilon domain function point left right laws first second).FunctionExtensionalityFree :=
  ⟨graphElim_free core epsilon _ _ _ _ _ _ lawsFree firstFree,
    graphElim_free core epsilon _ _ _ _ _ _ lawsFree secondFree⟩

theorem outside_free (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (absent : ProofSyntax Const Δ (.not (member core point domain)))
    (lawsFree : laws.Free) (absentFree : absent.FunctionExtensionalityFree) :
    (outside core epsilon domain function point value laws absent).FunctionExtensionalityFree :=
  ⟨by simpa [ProofSyntax.prepend] using absentFree,
   graphElim_free core epsilon _ _ _ _ _ _ (laws.prepend_free _ lawsFree) trivial⟩

def resultOutside (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (apart : ProofSyntax Const Δ (.not (.eq (.app function point) value))) :
    ProofSyntax Const Δ (.not (member core (ordered core epsilon point value) (graph core epsilon domain function))) :=
  .notI (.notE (apart.prepend _) (.andER
    (graphElim core epsilon domain function point value (laws.prepend _) (.hyp 0))))

theorem resultOutside_free (domain : Term Const Γ object) (function : Term Const Γ (object ⇒ object))
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (apart : ProofSyntax Const Δ (.not (.eq (.app function point) value)))
    (lawsFree : laws.Free) (apartFree : apart.FunctionExtensionalityFree) :
    (resultOutside core epsilon domain function point value laws apart).FunctionExtensionalityFree :=
  ⟨by simpa [ProofSyntax.prepend] using apartFree,
   graphElim_free core epsilon _ _ _ _ _ _ (laws.prepend_free _ lawsFree) trivial⟩

end Mettapedia.Logic.HOL.SetGraphProofs

