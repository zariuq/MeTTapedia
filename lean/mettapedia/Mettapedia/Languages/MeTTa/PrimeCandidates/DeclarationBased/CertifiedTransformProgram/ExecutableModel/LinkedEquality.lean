import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LinkedConnectives
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LinkedControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingIdentity

/-!
# Linked equality proofs in the object package

The object package has the identity reading and the eliminator `id:eliminate`
at the lowest universe. It transports every code family along identity
evidence (`setTransport`), so the equality algebra of the identity reading is
lawful for the set reading (`setIdentityOps`). No extensionality is tracked:
the package declares no function- or propositional-extensionality constant.

**Positive controls.** Each retained proof compiles by `rfl` to the displayed
term, which is a closed term of the object package at the decoding of the
code of its statement, strongly normalizing, and not refuted by the package:

* symmetry: `∀k. k = add zero k` from the linked `zero-add` proof
  (`converseTerm`, transport of `λy. y = add zero k` along `zero-add k`);
* congruence: `∀a b. a = b → suc a = suc b` (`sucCongTerm`);
* β: `∀n. (λx. suc x) n = suc n` (`betaTerm`, reflexivity at the redex);
* η: `∀f. (λx. f x) = f` (`etaTerm`, reflexivity at the η-expansion, with no
  function extensionality).

**Negative controls.**

* Without the identity reading the equality steps are declined, although the
  proofs are still read (`converse_noIdentity`, `sucCong_noIdentity`,
  `beta_noIdentity`, `eta_noIdentity`), and the typing theorem is not
  available (`noIdentity_not_lawful`).
* Untracked extensionality is declined: propositional extensionality,
  function extensionality, η proved through function extensionality, and
  equality under a binder (`propext_untracked`, `funext_untracked`,
  `etaByFunext_untracked`, `xi_untracked`); the ξ statement itself compiles by
  reflexivity (`xiRefl_compiled`).
* Reflexivity at a point is sound only for equal endpoints: `zero` and
  `suc zero` are not equal (`zero_suc_not_equal`), and `refl zero` is not a
  proof of `zero = suc zero` (`refl_wrong_endpoint`).

**The declared signature.** Over the constants the package declares, a proof
compiles exactly when it is a core proof with no extensionality step
(`object_compileP_isSome_iff`), and closed theorems compile to closed, strongly
normalizing terms (`object_closed_compileP_sn`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open SetProfile (SetBase SetConst numTy zeroT sucT addT zeroNative sucNative addNative)
open IdentityEquality.Translation (linkedZeroAdd)
open Package (jName jApp numT)

namespace CodeModel

/-! ## Transport at code motives -/

/-- **Identity elimination at code motives** in the object package. -/
theorem setTransport : setReading.CodeTransport jName where
  typed := by
    intro n Γ A x y d e C hA hx hy hC hd he
    have L := setReading_laws
    have formed₂ : Typed objectRules (.snoc Γ A)
        (.pi (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0)) Package.U0) U1 :=
      piO (raiseO (.idForm hA.weaken (.sort _) hx.weaken (.var 0))) U0_typedO
    have formed : Typed objectRules Γ
        (.pi A (.pi (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0)) Package.U0))
        U1 :=
      piO (raiseO hA) formed₂
    have motiveBody : Typed objectRules
        (.snoc (.snoc Γ A) (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0)))
        (programCodes.holdsOf (Presentation.rename wk C)) Package.U0 :=
      L.holdsOf_typed hC.weaken
    have motive : Typed objectRules Γ (.lam (.lam (programCodes.holdsOf (Presentation.rename wk C))))
        (.pi A (.pi (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0)) Package.U0)) :=
      .lamIntro formed (.sort _) (.lamIntro formed₂ (.sort _) motiveBody)
    have opened : ∀ {a b : Tower.Tm n},
        inst0 b (Presentation.subst (liftSub (subst0 a))
          (programCodes.holdsOf (Presentation.rename wk C))) = programCodes.holdsOf (inst0 a C) := by
      intro a b
      change programCodes.holdsOf (inst0 b (Presentation.subst (liftSub (subst0 a))
        (Presentation.rename wk C))) = _
      rw [subst_liftSub_wk, inst0_rename_wk]
      rfl
    have atPoint : ∀ {a : Tower.Tm n},
        inst0 a (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0)) = .id A x a := by
      intro a
      change Tm.id (inst0 a (Presentation.rename wk A)) (inst0 a (Presentation.rename wk x)) a = _
      rw [inst0_rename_wk, inst0_rename_wk]
    have reflAt : Typed objectRules Γ (.refl x)
        (inst0 x (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0))) := by
      rw [atPoint]
      exact .reflIntro hx
    have pathAt : Typed objectRules Γ e
        (inst0 y (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0))) := by
      rw [atPoint]
      exact he
    have base : Typed objectRules Γ d
        (.app (.app (.lam (.lam (programCodes.holdsOf (Presentation.rename wk C)))) x) (.refl x)) := by
      have beta := betaTwoT formed (.sort _) formed₂ motiveBody hx reflAt
      rw [opened] at beta
      exact .conv hd (.symm beta) (.sort _)
    have eliminated := j_typedO hA hx motive base hy he
    have beta := betaTwoT formed (.sort _) formed₂ motiveBody hy pathAt
    rw [opened] at beta
    exact .conv eliminated beta (.sort _)

/-- The equality algebra of the identity reading at the set reading, with no
extensionality tracked. -/
def setIdentityOps : PointedOperations setReading :=
  identityEqOperations setReading_laws setTransport (TrackedEquality.untracked setReading)

/-! ## Symmetry: the converse of `zero-add` -/

/-- `∀k. k = add zero k`, the converse of `zero-add`. -/
def converseStatement : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.eq (.var .vz) (addT zeroT (.var .vz)))

/-- The converse from `zero-add`, by symmetry. -/
def converseProof : HOL.ProofSyntax SetConst [SetProfile.zeroAddStatement] converseStatement :=
  .allI (.eqSymm (.allE (φ := .eq (addT zeroT (.var .vz)) (.var .vz)) (.var .vz)
    (.hyp ⟨0, by decide⟩)))

/-- Its code, `∀k. eq@num k (add zero k)`. -/
def converseCode : Tower.Tm 0 :=
  setReading.allOf numTy (.lam (setReading.eqOf numTy (.var 0) (addNative zeroNative (.var 0))))

/-- The linked term: at `k`, transport of `λy. y = add zero k` along the linked
`zero-add` evidence at `k`, from `refl (add zero k)`. -/
def converseTerm : Tower.Tm 0 :=
  .lam (setReading.transport jName numT (addNative zeroNative (.var 0))
    (setReading.eqOf numTy (.var 0) (addNative zeroNative (.var 1)))
    (.refl (addNative zeroNative (.var 0))) (.var 0)
    (.app (Presentation.rename wk linkedZeroAdd) (.var 0)))

theorem converse_compiled :
    setReading.compileP setIdentityOps.raw converseProof Fin.elim0 ![linkedZeroAdd] =
      some converseTerm :=
  rfl

theorem converseStatement_read : setReading.term converseStatement = some converseCode := rfl

theorem converseTerm_typedO :
    Typed objectRules .nil converseTerm (programCodes.holdsOf converseCode) := by
  obtain ⟨code, read, typed⟩ := setReading_laws.compileP_typedO setIdentityOps.lawful
    converseProof (target := .nil) (fun i => Fin.elim0 i)
    (fun i => match i with
      | ⟨0, _⟩ => ⟨SetProfile.zeroAddCode, rfl, by
          rw [SetProfile.subst_elim0]
          exact linkedZeroAdd_typedO⟩)
    converse_compiled
  rw [converseStatement_read] at read
  cases read
  rwa [SetProfile.subst_elim0] at typed

theorem converseTerm_sn : StrongNormalization.SN objectRules converseTerm :=
  (objectRules_sn .nil converseTerm_typedO).1

/-- The package does not refute the converse. -/
theorem converse_not_refuted (f : Tower.Tm 0) :
    ¬ Typed objectRules .nil f (programCodes.holdsOf (programCodes.impOf converseCode botCode)) :=
  fun refutation => consistent_bot (.app f converseTerm) (setReading_laws.impElim
    (setReading_laws.term_typed converseStatement_read) botCode_typed refutation
    converseTerm_typedO)

/-! ## Congruence: `a = b → suc a = suc b` -/

/-- `∀a b. a = b → suc a = suc b`. -/
def sucCongStatement : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.all (σ := numTy) (.imp (.eq (.var (.vs .vz)) (.var .vz))
    (.eq (sucT (.var (.vs .vz))) (sucT (.var .vz)))))

/-- Congruence of the successor, by the argument-congruence rule. -/
def sucCongProof : HOL.ProofSyntax SetConst [] sucCongStatement :=
  .allI (.allI (.impI (.eqAppArg (.const SetConst.suc) (.hyp ⟨0, by decide⟩))))

def sucCongCode : Tower.Tm 0 :=
  setReading.allOf numTy (.lam (setReading.allOf numTy (.lam (programCodes.impOf
    (setReading.eqOf numTy (.var 1) (.var 0))
    (setReading.eqOf numTy (sucNative (.var 1)) (sucNative (.var 0)))))))

/-- The linked term: transport of `λy. suc a = suc y` along the evidence for
`a = b`, from `refl (suc a)`. -/
def sucCongTerm : Tower.Tm 0 :=
  .lam (.lam (.lam (setReading.transport jName numT (.var 2)
    (setReading.eqOf numTy (sucNative (.var 3)) (sucNative (.var 0)))
    (.refl (sucNative (.var 2))) (.var 1) (.var 0))))

theorem sucCong_compiled :
    setReading.compileP setIdentityOps.raw sucCongProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = some sucCongTerm :=
  rfl

theorem sucCongStatement_read : setReading.term sucCongStatement = some sucCongCode := rfl

theorem sucCongTerm_typedO :
    Typed objectRules .nil sucCongTerm (programCodes.holdsOf sucCongCode) := by
  obtain ⟨code, read, typed⟩ := setReading_laws.compileP_typedO setIdentityOps.lawful
    sucCongProof (target := .nil) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) sucCong_compiled
  rw [sucCongStatement_read] at read
  cases read
  rwa [SetProfile.subst_elim0] at typed

theorem sucCongTerm_sn : StrongNormalization.SN objectRules sucCongTerm :=
  (objectRules_sn .nil sucCongTerm_typedO).1

theorem sucCong_not_refuted (f : Tower.Tm 0) :
    ¬ Typed objectRules .nil f (programCodes.holdsOf (programCodes.impOf sucCongCode botCode)) :=
  fun refutation => consistent_bot (.app f sucCongTerm) (setReading_laws.impElim
    (setReading_laws.term_typed sucCongStatement_read) botCode_typed refutation
    sucCongTerm_typedO)

/-! ## β and η, realized by reflexivity at a point -/

/-- `∀n. (λx. suc x) n = suc n`. -/
def betaStatement : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.eq (.app (.lam (sucT (.var .vz))) (.var .vz)) (sucT (.var .vz)))

/-- The β rule. -/
def betaProof : HOL.ProofSyntax SetConst [] betaStatement :=
  .allI (.beta (.var .vz) (sucT (.var .vz)))

def betaCode : Tower.Tm 0 :=
  setReading.allOf numTy (.lam (setReading.eqOf numTy
    (.app (.lam (sucNative (.var 0))) (.var 0)) (sucNative (.var 0))))

/-- The linked term: reflexivity at the redex. -/
def betaTerm : Tower.Tm 0 := .lam (.refl (.app (.lam (sucNative (.var 0))) (.var 0)))

theorem beta_compiled :
    setReading.compileP setIdentityOps.raw betaProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = some betaTerm :=
  rfl

theorem betaStatement_read : setReading.term betaStatement = some betaCode := rfl

theorem betaTerm_typedO : Typed objectRules .nil betaTerm (programCodes.holdsOf betaCode) := by
  obtain ⟨code, read, typed⟩ := setReading_laws.compileP_typedO setIdentityOps.lawful
    betaProof (target := .nil) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) beta_compiled
  rw [betaStatement_read] at read
  cases read
  rwa [SetProfile.subst_elim0] at typed

theorem betaTerm_sn : StrongNormalization.SN objectRules betaTerm :=
  (objectRules_sn .nil betaTerm_typedO).1

theorem beta_not_refuted (f : Tower.Tm 0) :
    ¬ Typed objectRules .nil f (programCodes.holdsOf (programCodes.impOf betaCode botCode)) :=
  fun refutation => consistent_bot (.app f betaTerm) (setReading_laws.impElim
    (setReading_laws.term_typed betaStatement_read) botCode_typed refutation betaTerm_typedO)

/-- The code of η at `num → num`: `∀f. eq (λx. f x) f`. -/
def etaCode : Tower.Tm 0 :=
  setReading.allOf (.arr numTy numTy) (.lam (setReading.eqOf (.arr numTy numTy)
    (.lam (.app (.var 1) (.var 0))) (.var 0)))

/-- The linked term of η: reflexivity at the η-expansion. No function
extensionality is used. -/
def etaTerm : Tower.Tm 0 := .lam (.refl (.lam (.app (.var 1) (.var 0))))

theorem eta_compiled :
    setReading.compileP setIdentityOps.raw etaProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = some etaTerm :=
  rfl

theorem etaStatement_read : setReading.term etaStatement = some etaCode := rfl

theorem etaTerm_typedO : Typed objectRules .nil etaTerm (programCodes.holdsOf etaCode) := by
  obtain ⟨code, read, typed⟩ := setReading_laws.compileP_typedO setIdentityOps.lawful
    etaProof (target := .nil) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) eta_compiled
  rw [etaStatement_read] at read
  cases read
  rwa [SetProfile.subst_elim0] at typed

theorem etaTerm_sn : StrongNormalization.SN objectRules etaTerm :=
  (objectRules_sn .nil etaTerm_typedO).1

theorem eta_not_refuted (f : Tower.Tm 0) :
    ¬ Typed objectRules .nil f (programCodes.holdsOf (programCodes.impOf etaCode botCode)) :=
  fun refutation => consistent_bot (.app f etaTerm) (setReading_laws.impElim
    (setReading_laws.term_typed etaStatement_read) botCode_typed refutation etaTerm_typedO)

/-! ## Negative controls -/

/-! ### Without the identity reading -/

/-- The set reading with the identity reading switched off. -/
def noIdentityReading : HOLReading Tower.Head SetBase SetConst :=
  { setReading with codes := { programCodes with identity := false } }

/-- The identity algebra built for that reading. -/
abbrev noIdentityOps : PointedRaw Tower.Head SetBase :=
  noIdentityReading.identityRaw jName (fun _ _ => none) none

/-- The typing theorem is not available there: the laws of a reading require
the identity reading. -/
theorem noIdentity_not_lawful : ¬ noIdentityReading.Laws :=
  fun L => absurd L.identity (by decide)

/-- The proofs are still read. -/
theorem converse_read_noIdentity : noIdentityReading.ReadProof converseProof :=
  ⟨rfl, rfl, rfl, trivial⟩

theorem converse_noIdentity :
    noIdentityReading.compileP noIdentityOps converseProof Fin.elim0 ![linkedZeroAdd] = none :=
  rfl

theorem sucCong_noIdentity :
    noIdentityReading.compileP noIdentityOps sucCongProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = none :=
  rfl

theorem beta_noIdentity :
    noIdentityReading.compileP noIdentityOps betaProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = none :=
  rfl

theorem eta_noIdentity :
    noIdentityReading.compileP noIdentityOps etaProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = none :=
  rfl

/-! ### Untracked extensionality -/

/-- Propositional extensionality is declined. -/
theorem propext_untracked :
    setReading.compileP setIdentityOps.raw propextProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = none :=
  rfl

/-- `∀f g : num → num. (∀x. f x = g x) → f = g`. -/
def funextStatement : HOL.Formula SetConst [] := HOLReading.funextFormula numTy numTy

def funextProof : HOL.ProofSyntax SetConst [] funextStatement :=
  .allI (.allI (.impI (.funExt (.hyp ⟨0, by decide⟩))))

/-- Function extensionality is declined. -/
theorem funext_untracked :
    setReading.compileP setIdentityOps.raw funextProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = none :=
  rfl

/-- η proved through function extensionality, from β pointwise. -/
def etaByFunextProof : HOL.ProofSyntax SetConst [] etaStatement :=
  .allI (.funExt (.allI (.beta (.var .vz) (.app (.var (.vs (.vs .vz))) (.var .vz)))))

/-- η through function extensionality is declined, while the η rule compiles
by reflexivity (`eta_compiled`). -/
theorem etaByFunext_untracked :
    setReading.compileP setIdentityOps.raw etaByFunextProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = none :=
  rfl

/-- `∀f : num → num. (λx. f x) = (λx. f x)`. -/
def xiStatement : HOL.Formula SetConst [] :=
  .all (σ := .arr numTy numTy) (.eq (.lam (.app (HOL.weaken (.var .vz)) (.var .vz)))
    (.lam (.app (HOL.weaken (.var .vz)) (.var .vz))))

/-- The ξ rule (equality under a binder) is function extensionality. -/
def xiProof : HOL.ProofSyntax SetConst [] xiStatement :=
  .allI (.eqLam (.eqRefl (.app (HOL.weaken (.var .vz)) (.var .vz))))

/-- The same statement by reflexivity. -/
def xiReflProof : HOL.ProofSyntax SetConst [] xiStatement :=
  .allI (.eqRefl (.lam (.app (HOL.weaken (.var .vz)) (.var .vz))))

theorem xi_untracked :
    setReading.compileP setIdentityOps.raw xiProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = none :=
  rfl

theorem xiRefl_compiled :
    setReading.compileP setIdentityOps.raw xiReflProof (Fin.elim0 : Sub Tower.Head 0 0)
      Fin.elim0 = some (.lam (.refl (.lam (.app (.var 1) (.var 0))))) :=
  rfl

/-! ### Reflexivity at endpoints that are not equal -/

/-- The algebra offers `refl zero` at the point `zero`. -/
theorem pointed_zero :
    setIdentityOps.raw.pointed numTy (zeroNative : Tower.Tm 0) = some (.refl zeroNative) :=
  rfl

/-- `zero` and `suc zero` are not equal in the object package. -/
theorem zero_suc_not_equal : ¬ Equal objectRules .nil zeroNative (sucNative zeroNative) numT :=
  fun equal => numeral_identity_apart (j := 0) (k := 1) (by decide) (.refl zeroNative)
    (.conv (.reflIntro zero_typedO)
      (.idCong (.refl num_typedO) (.sort _) (.refl zero_typedO) equal) (.sort _))

/-- **A pointed node at endpoints that are not equal is untypable**: `refl zero`
is not a proof of `zero = suc zero`. -/
theorem refl_wrong_endpoint :
    ¬ Typed objectRules .nil (.refl zeroNative)
      (programCodes.holdsOf (setReading.eqOf numTy zeroNative (sucNative zeroNative))) :=
  fun typed => numeral_identity_apart (j := 0) (k := 1) (by decide) (.refl zeroNative)
    (.conv typed (setReading_laws.equal_holds_eq (τ := numTy) zero_typedO (numeral_typedO 1))
      (.sort _))

/-! ## The declared signature: exact totality -/

theorem objectTransport : objectReading.CodeTransport jName :=
  ⟨setTransport.typed⟩

/-- The equality algebra of the identity reading over the declared signature. -/
def objectIdentityOps : PointedOperations objectReading :=
  identityEqOperations objectReading_laws objectTransport (TrackedEquality.untracked objectReading)

/-- **Exact totality in the object package.** A proof over the declared
constants compiles exactly when it is a core proof with no extensionality
step. -/
theorem object_compileP_isSome_iff {Γ : HOL.Ctx SetBase} {Δ : List (HOL.Formula ObjectConst Γ)}
    {φ : HOL.Formula ObjectConst Γ} (d : HOL.ProofSyntax ObjectConst Δ φ) {n : Nat}
    (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    (objectReading.compileP objectIdentityOps.raw d objects hyps).isSome ↔
      HOL.ImpredicativeConnectives.IsCoreProof d ∧
        Request.propositionExtensionality ∉ requests d ∧
        ∀ σ τ, Request.functionExtensionality σ τ ∉ requests d := by
  have h := identityEqOperations_isSome_iff objectReading_laws objectTransport
    (TrackedEquality.untracked objectReading) d objects hyps
  rw [HOLReading.readProof_iff_isCoreProof objectReading_total] at h
  refine h.trans ?_
  simp [TrackedEquality.untracked]

/-- **Closed theorems** over the declared constants whose proofs are core and
use no extensionality compile to closed, strongly normalizing terms of the
object package at the decoding of their statements. -/
theorem object_closed_compileP_sn {φ : HOL.Formula ObjectConst []}
    (d : HOL.ProofSyntax ObjectConst [] φ) (core : HOL.ImpredicativeConnectives.IsCoreProof d)
    (noPropext : Request.propositionExtensionality ∉ requests d)
    (noFunext : ∀ σ τ, Request.functionExtensionality σ τ ∉ requests d) :
    ∃ out code, objectReading.compileP objectIdentityOps.raw d Fin.elim0 Fin.elim0 = some out ∧
      objectReading.term φ = some code ∧ Typed objectRules .nil out (programCodes.holdsOf code) ∧
      StrongNormalization.SN objectRules out := by
  obtain ⟨out, compiled⟩ := Option.isSome_iff_exists.mp
    ((object_compileP_isSome_iff d (n := 0) Fin.elim0 Fin.elim0).mpr ⟨core, noPropext, noFunext⟩)
  obtain ⟨code, read, typed⟩ := objectReading_laws.compileP_typedO objectIdentityOps.lawful d
    (target := .nil) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) compiled
  rw [SetProfile.subst_elim0] at typed
  exact ⟨out, code, compiled, read, typed, (objectRules_sn .nil typed).1⟩

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
