import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchWords
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricPrincipalResults
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MatchIdentityOrder

/-!
# Principal result naming for complete symmetric CMR bags

Profile: one first-order occurrence-bag store, ambient rules, jointly fresh
finite bags, own-information guards after tells. After aligning member classes,
one pair of inverse-on-support variable maps acts on the whole source/output
interface. Correlations across different members are not forgotten.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

noncomputable def batchReadout (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) (answer : Subst signature) :
    List (Term signature) :=
  (sourceTerms s).map answer.applyTerm ++ (bag.produce (frames (FirstOrder.action signature))).map answer.applyTerm

omit [DecidableEq O] in
theorem outputWords_flatten {a : PUnit} {x : (ext (FirstOrder.action signature)).Ext a}
    (members : List (Member O (ext (FirstOrder.action signature)) P x)) (assignment : Subst signature) :
    (outputWords members assignment).flatten =
      (members.flatMap fun m => (m.firing.opened (frames (FirstOrder.action signature))).produce).map
        assignment.applyTerm := by
  induction members with
  | nil => rfl
  | cons m rest ih =>
    change ((m.firing.opened (frames (FirstOrder.action signature))).produce.map assignment.applyTerm) ++
      (outputWords rest assignment).flatten = _
    rw [ih]
    exact List.map_append.symm

omit [DecidableEq O] in
theorem batchReadout_factor (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) (answer candidate residual : Subst signature)
    (factors : ∀ term, candidate.applyTerm term = residual.applyTerm (answer.applyTerm term)) :
    (batchReadout s bag answer).map residual.applyTerm = batchReadout s bag candidate := by
  simp only [batchReadout, List.map_append, List.map_map]
  exact congrArg₂ List.append (List.map_congr_left fun term _ => (factors term).symm)
    (List.map_congr_left fun term _ => (factors term).symm)

theorem principal_batch_instance (s : State (Terms (Term signature)) O)
    (first : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (second : Bag O (ext (FirstOrder.action signature)) P' s.frame)
    (firstOwn : first.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (secondOwn : second.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (keys : first.keysBy identity = second.keysBy identity) (firstAnswer secondAnswer : Subst signature)
    (firstPrincipal : (FirstOrder.action signature).Principal
      (first.information (frames (FirstOrder.action signature)) s) firstAnswer)
    (secondPrincipal : (FirstOrder.action signature).Principal
      (second.information (frames (FirstOrder.action signature)) s) secondAnswer) :
    ∃ residual : Subst signature,
      (batchReadout s second secondAnswer).map residual.applyTerm = batchReadout s first firstAnswer := by
  have model : WordResultModel s first firstAnswer (outputWords first.members firstAnswer) :=
    ⟨firstAnswer, firstPrincipal.sound, fun _ _ => rfl, rfl⟩
  obtain ⟨candidate, solves, source, output⟩ :=
    (same_keys_word_models s first second firstOwn secondOwn keys _ _).mp model
  obtain ⟨residual, factors⟩ := secondPrincipal.factors candidate solves
  have through : ∀ term, candidate.applyTerm term = residual.applyTerm (secondAnswer.applyTerm term) := by
    intro term
    simpa only [FirstOrder.action, Subst.applyTerm_comp] using factors term
  refine ⟨residual, ?_⟩
  rw [batchReadout_factor s second secondAnswer candidate residual through]
  unfold batchReadout
  apply congrArg₂ List.append
  · exact List.map_congr_left fun term member => source term (sourceTerms_mentioned s term member)
  · have flat := congrArg List.flatten output
    simpa only [outputWords_flatten, Bag.produce] using flat.symm

variable [DecidableEq signature.vars]

theorem principal_batch_variants (s : State (Terms (Term signature)) O)
    (first : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (second : Bag O (ext (FirstOrder.action signature)) P' s.frame)
    (firstOwn : first.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (secondOwn : second.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (keys : first.keysBy identity = second.keysBy identity) (firstAnswer secondAnswer : Subst signature)
    (firstPrincipal : (FirstOrder.action signature).Principal
      (first.information (frames (FirstOrder.action signature)) s) firstAnswer)
    (secondPrincipal : (FirstOrder.action signature).Principal
      (second.information (frames (FirstOrder.action signature)) s) secondAnswer) :
    ∃ names inverse : signature.vars → signature.vars,
      (batchReadout s first firstAnswer).map (UnificationRenaming.rename names) = batchReadout s second secondAnswer ∧
      (batchReadout s second secondAnswer).map (UnificationRenaming.rename inverse) = batchReadout s first firstAnswer ∧
      (∀ term ∈ batchReadout s first firstAnswer, ∀ name ∈ term.freeVars, inverse (names name) = name) ∧
      (∀ term ∈ batchReadout s second secondAnswer, ∀ name ∈ term.freeVars, names (inverse name) = name) := by
  obtain ⟨backward, recovered⟩ := principal_batch_instance s first second firstOwn secondOwn keys
    firstAnswer secondAnswer firstPrincipal secondPrincipal
  obtain ⟨forward, advanced⟩ := principal_batch_instance s second first secondOwn firstOwn keys.symm
    secondAnswer firstAnswer secondPrincipal firstPrincipal
  exact MutualListInstantiation.variants_of_mutual_instances _ _ forward backward advanced recovered

omit [DecidableEq O] [DecidableEq signature.vars] in
theorem align_key_order (s : State (Terms (Term signature)) O)
    (first : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (second : Bag O (ext (FirstOrder.action signature)) P' s.frame)
    (keys : (first.keysBy identity).Perm (second.keysBy identity)) :
    ∃ members : List (Member O (ext (FirstOrder.action signature)) P' second.ext),
      members.Perm second.members ∧
        first.keysBy identity = (⟨second.ext, members⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).keysBy identity := by
  change (first.keysBy identity).Perm (second.members.map
    (fun m : Member O (ext (FirstOrder.action signature)) P' second.ext => (presentation m.firing).key)) at keys
  have lift := congrFun (congrFun
    (List.eq_map_comp_perm (fun m : Member O (ext (FirstOrder.action signature)) P' second.ext =>
      (presentation m.firing).key)) (first.keysBy identity)) second.members
  obtain ⟨members, same, perm⟩ := Eq.mpr lift keys
  exact ⟨members, perm, same⟩

variable [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

theorem complete_principal_batch_variants (s : State (Terms (Term signature)) O)
    (region : Class signature O → Prop)
    (first second : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (firstComplete : first.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (secondComplete : second.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (firstAnswer secondAnswer : Subst signature)
    (firstAccepted : unifyTotal (first.information (frames (FirstOrder.action signature)) s) = some firstAnswer)
    (secondAccepted : unifyTotal (second.information (frames (FirstOrder.action signature)) s) = some secondAnswer) :
    ∃ members : List (Member O (ext (FirstOrder.action signature)) P second.ext),
      members.Perm second.members ∧ ∃ names inverse : signature.vars → signature.vars,
      (batchReadout s first firstAnswer).map (UnificationRenaming.rename names) =
        batchReadout s (⟨second.ext, members⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame) secondAnswer ∧
      (batchReadout s (⟨second.ext, members⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame) secondAnswer).map
        (UnificationRenaming.rename inverse) = batchReadout s first firstAnswer ∧
      (∀ term ∈ batchReadout s first firstAnswer, ∀ name ∈ term.freeVars, inverse (names name) = name) ∧
      (∀ term ∈ batchReadout s (⟨second.ext, members⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame) secondAnswer,
        ∀ name ∈ term.freeVars, names (inverse name) = name) := by
  obtain ⟨members, perm, keys⟩ := align_key_order s first second
    (firstComplete.keys_perm (fun _ _ => ⟨Subst.id signature⟩) secondComplete)
  have own := Bag.admitsOwn_perm (frames (FirstOrder.action signature)) perm.symm secondComplete.1
  have infoPerm := (Bag.result_perm (frames (FirstOrder.action signature)) perm.symm secondComplete.1.1).2.2
  have principal := FirstOrder.accepted_principal _ secondAnswer secondAccepted
  have alignedPrincipal : (FirstOrder.action signature).Principal
      ((⟨second.ext, members⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).information
        (frames (FirstOrder.action signature)) s) secondAnswer := by
    refine ⟨fun e member => principal.sound e (infoPerm.mem_iff.mp member), ?_⟩
    intro candidate solved
    exact principal.factors candidate (fun e member => solved e (infoPerm.mem_iff.mpr member))
  exact ⟨members, perm, principal_batch_variants s first _ firstComplete.1 own keys firstAnswer secondAnswer
    (FirstOrder.accepted_principal _ firstAnswer firstAccepted) alignedPrincipal⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
