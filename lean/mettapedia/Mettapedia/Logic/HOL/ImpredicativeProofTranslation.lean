import Mettapedia.Logic.HOL.ImpredicativeProofCore

/-!
# Retained proofs for the impredicative connective encodings

The derived logical rules are implemented using the existing retained HOL
calculus. Beta equalities connect the exact operator applications used by
`ImpredicativeConnectives.expand` to their quantified bodies. These are
constructed proof trees, not proofs recovered from semantic validity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ImpredicativeConnectives

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

private theorem substVariables {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ)
    {τ : Ty Base} (term : Term Const Γ τ) :
    subst (fun i => Term.var (ρ i)) term = rename ρ term :=
  subst_ofRename ρ term

private theorem substIdentity {τ : Ty Base} (term : Term Const Γ τ) :
    subst (fun i => Term.var i) term = term := subst_id term

private def convert {p q : Formula Const Γ}
    (equality : ProofSyntax Const Δ (.eq p q))
    (proof : ProofSyntax Const Δ p) : ProofSyntax Const Δ q :=
  .impE (.eqPropEL equality) proof

private def weakenProof {p : Formula Const Γ} {σ : Ty Base}
    (proof : ProofSyntax Const Δ p) :
    ProofSyntax Const (weakenHyps (σ := σ) Δ) (weaken (σ := σ) p) :=
  proof.rename Rename.weaken

def conjunctionFormula (p q : Formula Const Γ) : Formula Const Γ :=
  .all (.imp (.imp (weaken p) (.imp (weaken q) (.var .vz))) (.var .vz))

def disjunctionFormula (p q : Formula Const Γ) : Formula Const Γ :=
  .all (.imp (.imp (weaken p) (.var .vz))
    (.imp (.imp (weaken q) (.var .vz)) (.var .vz)))

def conjunctionBeta (p q : Formula Const Γ) :
    ProofSyntax Const Δ (.eq (.app (.app conjunction p) q) (conjunctionFormula p q)) := by
  apply ProofSyntax.eqTrans (ProofSyntax.eqApp q (ProofSyntax.beta p _))
  refine ProofSyntax.castIndices rfl ?_
    (ProofSyntax.beta q (.all (.imp
      (.imp (weaken (weaken p)) (.imp (.var (.vs .vz)) (.var .vz)))
      (.var .vz))))
  simp [conjunctionFormula, instantiate, subst, Subst.single,
    Subst.lift, Rename.weaken, weaken, subst_rename,
    substVariables]
  rfl

def disjunctionBeta (p q : Formula Const Γ) :
    ProofSyntax Const Δ (.eq (.app (.app disjunction p) q) (disjunctionFormula p q)) := by
  apply ProofSyntax.eqTrans (ProofSyntax.eqApp q (ProofSyntax.beta p _))
  refine ProofSyntax.castIndices rfl ?_
    (ProofSyntax.beta q (.all (.imp (.imp (weaken (weaken p)) (.var .vz))
      (.imp (.imp (.var (.vs .vz)) (.var .vz)) (.var .vz)))))
  simp [disjunctionFormula, instantiate, subst, Subst.single,
    Subst.lift, Rename.weaken, weaken, subst_rename,
    substVariables]
  rfl

def truthIntro : ProofSyntax Const Δ truth := .allI (.impI (.hyp 0))

def falsityElim (p : Formula Const Γ) (proof : ProofSyntax Const Δ falsity) :
    ProofSyntax Const Δ p := .allE p proof

def conjunctionIntro {p q : Formula Const Γ}
    (left : ProofSyntax Const Δ p) (right : ProofSyntax Const Δ q) :
    ProofSyntax Const Δ (.app (.app conjunction p) q) :=
  convert (.eqSymm (conjunctionBeta p q))
    (.allI (.impI (.impE (.impE (.hyp 0)
      ((weakenProof left).prepend _)) ((weakenProof right).prepend _))))

def conjunctionLeft {p q : Formula Const Γ}
    (proof : ProofSyntax Const Δ (.app (.app conjunction p) q)) :
    ProofSyntax Const Δ p := by
  have selected := ProofSyntax.allE p (convert (conjunctionBeta p q) proof)
  have selected' : ProofSyntax Const Δ (.imp (.imp p (.imp q p)) p) := by
    exact ProofSyntax.castIndices rfl (by simp [instantiate,
      subst, Subst.single, weaken, subst_rename, Rename.weaken,
      substIdentity]) selected
  exact .impE selected' (.impI (.impI (.hyp 1)))

def conjunctionRight {p q : Formula Const Γ}
    (proof : ProofSyntax Const Δ (.app (.app conjunction p) q)) :
    ProofSyntax Const Δ q := by
  have selected := ProofSyntax.allE q (convert (conjunctionBeta p q) proof)
  have selected' : ProofSyntax Const Δ (.imp (.imp p (.imp q q)) q) := by
    exact ProofSyntax.castIndices rfl (by simp [instantiate,
      subst, Subst.single, weaken, subst_rename, Rename.weaken,
      substIdentity]) selected
  exact .impE selected' (.impI (.impI (.hyp 0)))

def disjunctionLeft {p q : Formula Const Γ} (proof : ProofSyntax Const Δ p) :
    ProofSyntax Const Δ (.app (.app disjunction p) q) :=
  convert (.eqSymm (disjunctionBeta p q))
    (.allI (.impI (.impI (.impE (.hyp 1)
      (((weakenProof proof).prepend _).prepend _)))))

def disjunctionRight {p q : Formula Const Γ} (proof : ProofSyntax Const Δ q) :
    ProofSyntax Const Δ (.app (.app disjunction p) q) :=
  convert (.eqSymm (disjunctionBeta p q))
    (.allI (.impI (.impI (.impE (.hyp 0)
      (((weakenProof proof).prepend _).prepend _)))))

def disjunctionElim {p q r : Formula Const Γ}
    (cases : ProofSyntax Const Δ (.app (.app disjunction p) q))
    (left : ProofSyntax Const (p :: Δ) r) (right : ProofSyntax Const (q :: Δ) r) :
    ProofSyntax Const Δ r := by
  have selected := ProofSyntax.allE r (convert (disjunctionBeta p q) cases)
  have selected' : ProofSyntax Const Δ (.imp (.imp p r) (.imp (.imp q r) r)) := by
    exact ProofSyntax.castIndices rfl (by simp [instantiate,
      subst, Subst.single, weaken, subst_rename, Rename.weaken,
      substIdentity]) selected
  exact .impE (.impE selected' (.impI left)) (.impI right)

def existentialFormula {σ : Ty Base} (predicate : Term Const Γ (σ ⇒ .prop)) :
    Formula Const Γ :=
  .all (.imp (.all (.imp (.app (weaken (weaken predicate)) (.var .vz))
    (.var (.vs .vz)))) (.var .vz))

def existentialBeta {σ : Ty Base} (predicate : Term Const Γ (σ ⇒ .prop)) :
    ProofSyntax Const Δ (.eq (.app (existential σ) predicate)
      (existentialFormula predicate)) := by
  refine ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta predicate
    (.all (.imp (.all (.imp (.app (.var (.vs (.vs .vz))) (.var .vz))
      (.var (.vs .vz)))) (.var .vz))))
  simp [existential, existentialFormula, instantiate, subst, Subst.single,
    Subst.lift, weaken]
  rfl

def existentialIntro {σ : Ty Base} (predicate : Term Const Γ (σ ⇒ .prop))
    (witness : Term Const Γ σ) (proof : ProofSyntax Const Δ (.app predicate witness)) :
    ProofSyntax Const Δ (.app (existential σ) predicate) := by
  apply convert (.eqSymm (existentialBeta predicate))
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  have selected := ProofSyntax.allE (weaken (σ := .prop) witness)
    (ProofSyntax.hyp (Const := Const)
      (Δ := Term.all (Term.imp (Term.app (weaken (weaken predicate)) (.var .vz))
        (.var (.vs .vz))) :: weakenHyps (σ := .prop) Δ) 0)
  have selected' : ProofSyntax Const
      (Term.all (Term.imp (Term.app (weaken (weaken predicate)) (.var .vz))
        (.var (.vs .vz))) :: weakenHyps (σ := .prop) Δ)
      (.imp (.app (weaken predicate) (weaken witness)) (.var .vz)) := by
    refine ProofSyntax.castIndices rfl ?_ selected
    simp [instantiate, subst, Subst.single, weaken, subst_rename, Rename.weaken,
      substVariables]
    rfl
  exact .impE selected' ((weakenProof proof).prepend _)

def existentialElim {σ : Ty Base} {predicate : Term Const Γ (σ ⇒ .prop)}
    {result : Formula Const Γ}
    (existsProof : ProofSyntax Const Δ (.app (existential σ) predicate))
    (body : ProofSyntax Const
      (.app (weaken predicate) (.var .vz) :: weakenHyps (σ := σ) Δ)
      (weaken (σ := σ) result)) : ProofSyntax Const Δ result := by
  have selected := ProofSyntax.allE result (convert (existentialBeta predicate) existsProof)
  have selected' : ProofSyntax Const Δ
      (.imp (.all (.imp (.app (weaken predicate) (.var .vz)) (weaken result))) result) := by
    refine ProofSyntax.castIndices rfl ?_ selected
    simp [instantiate, subst, Subst.single, Subst.lift,
      weaken, subst_rename, Rename.weaken, substVariables]
    rfl
  exact .impE selected' (.allI (.impI body))

theorem expand_instantiate {σ τ : Ty Base}
    (term : Term Const Γ σ) (body : Term Const (σ :: Γ) τ) :
    expand (instantiate term body) = instantiate (expand term) (expand body) := by
  unfold instantiate
  rw [expand_subst]
  apply subst_ext
  intro _ index
  cases index <;> rfl

@[simp] theorem isCore_expanded_instantiation {σ τ : Ty Base}
    (term : Term Const Γ σ) (body : Term Const (σ :: Γ) τ) :
    IsCore (subst (Subst.single (expand term)) (expand body)) := by
  change IsCore (instantiate (expand term) (expand body))
  rw [← expand_instantiate]
  exact expand_isCore _

private theorem instantiateLiftWeaken {σ τ : Ty Base}
    (body : Term Const (σ :: Γ) τ) :
    instantiate (Term.var (Var.vz : Var (σ :: Γ) σ))
      (rename (Rename.lift Rename.weaken) body) = body := by
  unfold instantiate
  rw [subst_rename]
  calc
    _ = subst Subst.id body := by
      apply subst_ext
      intro _ index
      cases index <;> rfl
    _ = body := subst_id body

private def lambdaVariableBeta {σ τ : Ty Base}
    (body : Term Const (σ :: Γ) τ)
    {assumptions : List (Formula Const (σ :: Γ))} :
    ProofSyntax Const assumptions
      (.eq (.app (weaken (.lam body)) (.var .vz)) body) := by
  exact ProofSyntax.castIndices rfl (by simp only [weaken, rename, instantiateLiftWeaken])
    (ProofSyntax.beta (.var .vz) (rename (Rename.lift Rename.weaken) body) :
      ProofSyntax Const assumptions _)

/-- Expand every source proof rule using the same connective translation as
the term semantics. Premises are transformed from the supplied proof tree;
neither derivability nor semantic truth is used to choose a replacement. -/
def expandProof {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ProofSyntax Const Δ φ → ProofSyntax Const (Δ.map expand) (expand φ)
  | .hyp occurrence => by
      exact ProofSyntax.castIndices rfl (by simp)
        (ProofSyntax.hyp (Const := Const) (Δ := Δ.map expand)
          ⟨occurrence.val, by simp⟩)
  | .topI => truthIntro
  | .botE proof => falsityElim _ (expandProof proof)
  | .andI left right => conjunctionIntro (expandProof left) (expandProof right)
  | .andEL proof => conjunctionLeft (expandProof proof)
  | .andER proof => conjunctionRight (expandProof proof)
  | .orIL proof => disjunctionLeft (expandProof proof)
  | .orIR proof => disjunctionRight (expandProof proof)
  | .orE cases left right => disjunctionElim
      (expandProof cases) (expandProof left) (expandProof right)
  | .impI proof => .impI (expandProof proof)
  | .impE function argument => .impE (expandProof function) (expandProof argument)
  | .notI proof => .impI (expandProof proof)
  | .notE negative positive => .impE (expandProof negative) (expandProof positive)
  | .allI proof => by
      exact .allI (ProofSyntax.castIndices (by
        simp [weakenHyps, List.map_map, Function.comp_def, weaken, expand_rename])
        rfl (expandProof proof))
  | .allE term proof => by
      exact ProofSyntax.castIndices rfl (by simp only [expand_instantiate])
        (.allE (expand term) (expandProof proof))
  | @ProofSyntax.exI _ _ _ _ _ body term proof => by
      apply existentialIntro (.lam (expand body)) (expand term)
      apply convert (.eqSymm (.beta (expand term) (expand body)))
      exact ProofSyntax.castIndices rfl (expand_instantiate term body) (expandProof proof)
  | @ProofSyntax.exE _ _ _ _ _ body result existsProof bodyProof => by
      apply existentialElim (expandProof existsProof)
      have translated : ProofSyntax Const
          (expand body :: weakenHyps (Δ.map expand)) (weaken (expand result)) :=
        ProofSyntax.castIndices (by
          simp [weakenHyps, List.map_map, Function.comp_def, weaken, expand_rename])
          (by simp [weaken, expand_rename]) (expandProof bodyProof)
      exact .impE ((ProofSyntax.impI translated).prepend _)
        (convert (lambdaVariableBeta (expand body)) (.hyp 0))
  | .eqRefl term => .eqRefl (expand term)
  | .eqSymm proof => .eqSymm (expandProof proof)
  | .eqTrans left right => .eqTrans (expandProof left) (expandProof right)
  | .eqPropI forward backward => .eqPropI (expandProof forward) (expandProof backward)
  | .eqPropEL proof => .eqPropEL (expandProof proof)
  | .eqPropER proof => .eqPropER (expandProof proof)
  | .eqApp term proof => .eqApp (expand term) (expandProof proof)
  | .eqAppArg term proof => .eqAppArg (expand term) (expandProof proof)
  | .eqLam proof => by
      exact .eqLam (ProofSyntax.castIndices (by
        simp [weakenHyps, List.map_map, Function.comp_def, weaken, expand_rename])
        rfl (expandProof proof))
  | .funExt proof => by
      apply ProofSyntax.funExt
      exact ProofSyntax.castIndices rfl (by simp [expand, weaken, expand_rename])
        (expandProof proof)
  | .beta term body => by
      exact ProofSyntax.castIndices rfl (by simp only [expand, expand_instantiate])
        (ProofSyntax.beta (expand term) (expand body))
  | .eta term => by
      exact ProofSyntax.castIndices rfl (by simp [expand, weaken, expand_rename])
        (ProofSyntax.eta (expand term))

theorem expandProof_derivable {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) :
    ExtDerivation Const (Δ.map expand) (expand φ) := (expandProof proof).erase

theorem expandProof_isCore {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) :
    IsCoreProof (expandProof proof) := by
  induction proof with
  | _ => simp_all [expandProof, convert, truthIntro, falsityElim,
      conjunctionIntro, conjunctionLeft, conjunctionRight, conjunctionBeta,
      disjunctionLeft, disjunctionRight, disjunctionElim, disjunctionBeta,
      existentialIntro, existentialElim, existentialBeta, lambdaVariableBeta,
      weakenProof, ProofSyntax.prepend, IsCoreProof, expand_isCore,
      conjunctionFormula, disjunctionFormula, existentialFormula,
      falsity, conjunction, disjunction, existential, IsCore,
      weaken, rename, subst, instantiate, Subst.single, Subst.lift, Rename.weaken]

set_option maxHeartbeats 800000 in
/-- Fixed-size derived-rule expansions give a linear bound on rule nodes.
This does not bound the size of repeated term annotations or compilation time. -/
theorem nodeCount_expandProof_le {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) :
    (expandProof proof).nodeCount ≤ 32 * proof.nodeCount := by
  have count_cast {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} (assumptions : Δ = Δ') (conclusion : φ = ψ)
      (proof : ProofSyntax Const Δ φ) :
      (proof.castIndices assumptions conclusion).observe.nodeCount = proof.observe.nodeCount :=
    ProofSyntax.nodeCount_castIndices assumptions conclusion proof
  have count_mono {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ : Formula Const Γ}
      (transport : ProofSyntax.OccurrenceMap Δ Δ') (proof : ProofSyntax Const Δ φ) :
      (proof.mono transport).observe.nodeCount = proof.observe.nodeCount :=
    ProofSyntax.mono_nodeCount transport proof
  have count_rename {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
      (ρ : Rename Base Γ Ξ) (proof : ProofSyntax Const Δ φ) :
      (proof.rename ρ).observe.nodeCount = proof.observe.nodeCount :=
    ProofSyntax.rename_nodeCount ρ proof
  induction proof with
  | _ =>
      simp_all [expandProof, convert, truthIntro, falsityElim,
        conjunctionIntro, conjunctionLeft, conjunctionRight, conjunctionBeta,
        disjunctionLeft, disjunctionRight, disjunctionElim, disjunctionBeta,
        existentialIntro, existentialElim, existentialBeta, lambdaVariableBeta,
        weakenProof, ProofSyntax.prepend, ProofSyntax.nodeCount,
        ProofSyntax.observe, Fin.sum_univ_succ] <;> omega

namespace ProofControls

/-- Existential elimination retains one witness while projecting both pieces
of evidence; both conclusions rebind that witness independently. -/
def splitExistential {σ : Ty Base} (p q : Formula Const (σ :: Γ)) :
    ProofSyntax Const [] (.imp (.ex (.and p q)) (.and (.ex p) (.ex q))) := by
  apply ProofSyntax.impI
  apply ProofSyntax.exE (ProofSyntax.hyp 0)
  apply ProofSyntax.andI
  · apply ProofSyntax.exI (.var .vz)
    exact ProofSyntax.castIndices rfl (instantiateLiftWeaken p).symm
      (.andEL (.hyp 0))
  · apply ProofSyntax.exI (.var .vz)
    exact ProofSyntax.castIndices rfl (instantiateLiftWeaken q).symm
      (.andER (.hyp 0))

/-- A false encoded conclusion cannot acquire a retained proof in an
extensional Henkin model merely by going through the expansion. -/
theorem expandedFalse_empty (model : HenkinModel.{u, v, w} Base Const)
    (extensional : HenkinModel.FunctionsRespectEqv model) :
    ¬ Nonempty (ProofSyntax Const (Γ := []) [] (expand (.and .top .bot))) := by
  rintro ⟨proof⟩
  exact not_models_expanded_false model
    (Soundness.extTheorem_sound proof.erase model extensional)

end ProofControls

#print axioms expandProof
#print axioms expandProof_derivable
#print axioms expandProof_isCore
#print axioms nodeCount_expandProof_le
#print axioms ProofControls.splitExistential
#print axioms ProofControls.expandedFalse_empty

end Mettapedia.Logic.HOL.ImpredicativeConnectives
