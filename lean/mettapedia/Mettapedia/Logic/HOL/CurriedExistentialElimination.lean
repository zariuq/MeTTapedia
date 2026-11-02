import Mettapedia.Logic.HOL.CurriedExistentialProofs
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Opening an actual retained existential field query

The original field arguments stay fixed while one result witness is opened
for a continuation. The continuation's goal is independent of that witness.
This is an explicit proof program using existential elimination, not a
witness-selection operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.CurriedPredicates

open FiniteConstructorEncoding
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {bound : Ty Base}

def existsValue_elim {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (predicate : Term Const Γ (bound ⇒ handlerType fields))
    (arguments : Arguments Const Γ fields) (goal : Formula Const Γ)
    (present : ProofSyntax Const assumptions (applyArguments fields (existsValue fields predicate) arguments))
    (continuation : ProofSyntax Const
      (applyArguments fields (.app (weaken predicate) (.var .vz)) (weakenArguments bound fields arguments) ::
        weakenHyps assumptions) (weaken goal)) :
    ProofSyntax Const assumptions goal :=
  .exE (.impE (.eqPropEL (existsValue_beta fields predicate arguments)) present) continuation

theorem existsValue_elim_free {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (predicate : Term Const Γ (bound ⇒ handlerType fields))
    (arguments : Arguments Const Γ fields) (goal : Formula Const Γ)
    (present : ProofSyntax Const assumptions (applyArguments fields (existsValue fields predicate) arguments))
    (continuation : ProofSyntax Const
      (applyArguments fields (.app (weaken predicate) (.var .vz)) (weakenArguments bound fields arguments) ::
        weakenHyps assumptions) (weaken goal))
    (presentFree : present.FunctionExtensionalityFree) (continuationFree : continuation.FunctionExtensionalityFree) :
    (existsValue_elim fields predicate arguments goal present continuation).FunctionExtensionalityFree := by
  exact ⟨⟨existsValue_beta_free fields predicate arguments, presentFree⟩, continuationFree⟩

theorem rename_existsValue {Ξ : Ctx Base} (rho : Rename Base Γ Ξ) (fields : List (Ty Base))
    (predicate : Term Const Γ (bound ⇒ handlerType fields)) :
    rename rho (existsValue fields predicate) = existsValue fields (rename rho predicate) := by
  simpa only [subst_ofRename] using existsValue_subst (Subst.ofRename rho) fields predicate

theorem existsValue_nil (predicate : Term Const Γ (bound ⇒ .prop)) :
    existsValue [] predicate = .ex (.app (weaken predicate) (.var .vz)) := by
  have identity : subst (fun index => Term.var index) predicate = predicate :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) predicate
  simp only [existsValue, abstractArguments, applyArguments, identity]

def existsValue_nil_congr {assumptions : List (Formula Const Γ)}
    (first second : Term Const Γ (bound ⇒ .prop)) (equal : ProofSyntax Const assumptions (.eq first second)) :
    ProofSyntax Const assumptions (.eq (existsValue [] first) (existsValue [] second)) :=
  ProofSyntax.castIndices rfl (congrArg₂ Term.eq (existsValue_nil first).symm (existsValue_nil second).symm)
    (ContextualTrinity.exCongr (.eqApp (.var .vz) (equal.rename Rename.weaken)))

theorem existsValue_nil_congr_free {assumptions : List (Formula Const Γ)}
    (first second : Term Const Γ (bound ⇒ .prop)) (equal : ProofSyntax Const assumptions (.eq first second))
    (free : equal.FunctionExtensionalityFree) :
    (existsValue_nil_congr first second equal).FunctionExtensionalityFree := by
  simpa only [existsValue_nil_congr, ProofSyntax.functionExtensionalityFree_castIndices,
    ContextualTrinity.exCongr_free, ProofSyntax.FunctionExtensionalityFree,
    ProofSyntax.functionExtensionalityFree_rename] using free

theorem existsValue_nil_denote (model : HenkinModel.{u,v,w} Base Const) (values : model.Valuation Γ)
    (predicate : Term Const Γ (bound ⇒ .prop)) :
    (model.denote (existsValue [] predicate) values).down ↔
      ∃ point, model.adm bound point ∧ (model.denote predicate values point).down := by
  rw [existsValue_nil]
  simp only [HenkinModel.denote, PreModel.denote, Soundness.denote_weaken]
  rfl

#print axioms existsValue_elim_free

end Mettapedia.Logic.HOL.CurriedPredicates
