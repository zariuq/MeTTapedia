import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofCompilerCompleteness
import Mettapedia.Logic.HOL.ProofSyntaxModuloStructural
import Mettapedia.Logic.HOL.ImpredicativeProofModulo
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion

/-!
# The laws of the generic proof compiler modulo conversion

The generic compiler `Modulo.compileModulo` links a proof of
`HOL.ProofSyntaxModulo` against terms for its object variables and its
hypotheses. Its laws, for every declared logical signature:

* **exact totality** (`compileModulo_isSome_iff`): a proof compiles exactly
  when it is core;
* **context extension**: hypothesis transport is reindexing of the hypothesis
  terms (`compileModulo_mono`), source renaming is reindexing of the object
  terms (`compileModulo_rename`), and source weakening commutes with target
  renaming (`compileModulo_weaken`);
* **source substitution** (`compileModulo_sourceSubst`): substituting core
  terms in the proof is substituting their representations in the object
  terms;
* **specialization** (`compileModulo_instantiate`,
  `compileModulo_allE_allI_step`): the linked term of an instance is the
  instance of the linked term, and eliminating a generalization at a term is
  one β-step from it;
* **declaration compatibility** (`compileModulo_mapConst`): along a signature
  embedding, the image of a proof links to the same term;
* **dependency**: the linked term reads only the hypotheses the proof uses
  (`compileModulo_frame`); its constants are the signature's symbols, the
  object terms' constants and the used hypotheses' constants
  (`constantNames_compileModulo`); every used hypothesis occurs in it
  (`constantNames_hyp_compileModulo`), so the frame is tight
  (`compileModulo_frame_tight`);
* **residual list** (`assumed_link`, `assumed_eq_residual`): when each
  published assumption is linked to its realization and every other one to its
  assumption constant, the assumption constants of the linked term are
  exactly the used assumptions that are not published.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Mettapedia.Logic FormationSensitiveHOLInterface
open HOL.ImpredicativeConnectives (IsCoreProofModulo IsCore isCore_eq_true_iff)
open Presentation.ConstantExpansion (constantNames constantNames_rename)

universe u v w

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

namespace Modulo

/-! ## Representation is defined exactly on the core terms -/

theorem represent_isSome_eq (signature : LogicalSignature Base Const) :
    ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ),
      (represent signature t).isSome = t.isCore
  | _, _, .var _ => rfl
  | _, _, .const _ => rfl
  | _, _, .app f a => by
      have hf := represent_isSome_eq signature f
      have ha := represent_isSome_eq signature a
      simp only [HOL.Term.isCore]
      cases rf : represent signature f <;> cases ra : represent signature a <;>
        simp only [rf, ra, Option.isSome_none, Option.isSome_some] at hf ha <;>
        simp only [represent, rf, ra, ← hf, ← ha] <;> rfl
  | _, _, .lam b => by
      have hb := represent_isSome_eq signature b
      simp only [represent, HOL.Term.isCore, Option.isSome_map, hb]
  | _, _, .imp p q => by
      have hp := represent_isSome_eq signature p
      have hq := represent_isSome_eq signature q
      simp only [HOL.Term.isCore]
      cases rp : represent signature p <;> cases rq : represent signature q <;>
        simp only [rp, rq, Option.isSome_none, Option.isSome_some] at hp hq <;>
        simp only [represent, rp, rq, ← hp, ← hq] <;> rfl
  | _, _, .all b => by
      have hb := represent_isSome_eq signature b
      simp only [HOL.Term.isCore]
      cases rb : represent signature b <;>
        simp only [rb, Option.isSome_none, Option.isSome_some] at hb <;>
        simp only [represent, rb, ← hb, Option.map_none, Option.map_some] <;> rfl
  | _, _, .eq l r => by
      have hl := represent_isSome_eq signature l
      have hr := represent_isSome_eq signature r
      simp only [HOL.Term.isCore]
      cases rl : represent signature l <;> cases rr : represent signature r <;>
        simp only [rl, rr, Option.isSome_none, Option.isSome_some] at hl hr <;>
        simp only [represent, rl, rr, ← hl, ← hr] <;> rfl
  | _, _, .top | _, _, .bot | _, _, .and _ _ | _, _, .or _ _ | _, _, .not _
  | _, _, .ex _ => rfl

theorem isCore_of_represent (signature : LogicalSignature Base Const) {Γ : HOL.Ctx Base}
    {τ : HOL.Ty Base} {t : HOL.Term Const Γ τ} {out : Tower.Tm Γ.length}
    (h : represent signature t = some out) : IsCore t := by
  rw [← isCore_eq_true_iff, ← represent_isSome_eq signature t, h]
  rfl

/-! ## Inversion of representation -/

theorem represent_app_inv (signature : LogicalSignature Base Const) {Γ : HOL.Ctx Base}
    {σ τ : HOL.Ty Base} {f : HOL.Term Const Γ (.arr σ τ)} {a : HOL.Term Const Γ σ}
    {out : Tower.Tm Γ.length} (h : represent signature (.app f a) = some out) :
    ∃ f' a', represent signature f = some f' ∧ represent signature a = some a' ∧
      out = .app f' a' := by
  have core := represent_isSome_eq signature (.app f a)
  rw [h] at core
  simp only [Option.isSome_some, HOL.Term.isCore] at core
  obtain ⟨f', hf⟩ := Option.isSome_iff_exists.mp
    ((represent_isSome_eq signature f).trans (Bool.and_eq_true_iff.mp core.symm).1)
  obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp
    ((represent_isSome_eq signature a).trans (Bool.and_eq_true_iff.mp core.symm).2)
  rw [represent_app signature f a hf ha, Option.some.injEq] at h
  exact ⟨f', a', hf, ha, h.symm⟩

theorem represent_imp_inv (signature : LogicalSignature Base Const) {Γ : HOL.Ctx Base}
    {p q : HOL.Formula Const Γ} {out : Tower.Tm Γ.length}
    (h : represent signature (.imp p q) = some out) :
    ∃ p' q', represent signature p = some p' ∧ represent signature q = some q' ∧
      out = .app (.app (liftClosed signature.implication) p') q' := by
  have core := represent_isSome_eq signature (.imp p q)
  rw [h] at core
  simp only [Option.isSome_some, HOL.Term.isCore] at core
  obtain ⟨p', hp⟩ := Option.isSome_iff_exists.mp
    ((represent_isSome_eq signature p).trans (Bool.and_eq_true_iff.mp core.symm).1)
  obtain ⟨q', hq⟩ := Option.isSome_iff_exists.mp
    ((represent_isSome_eq signature q).trans (Bool.and_eq_true_iff.mp core.symm).2)
  rw [represent_imp, hp, hq] at h
  exact ⟨p', q', hp, hq, (Option.some.inj h).symm⟩

theorem represent_eq_inv (signature : LogicalSignature Base Const) {Γ : HOL.Ctx Base}
    {τ : HOL.Ty Base} {l r : HOL.Term Const Γ τ} {out : Tower.Tm Γ.length}
    (h : represent signature (.eq l r) = some out) :
    ∃ l' r', represent signature l = some l' ∧ represent signature r = some r' ∧
      out = .app (.app (liftClosed (signature.equality τ)) l') r' := by
  have core := represent_isSome_eq signature (.eq l r)
  rw [h] at core
  simp only [Option.isSome_some, HOL.Term.isCore] at core
  obtain ⟨l', hl⟩ := Option.isSome_iff_exists.mp
    ((represent_isSome_eq signature l).trans (Bool.and_eq_true_iff.mp core.symm).1)
  obtain ⟨r', hr⟩ := Option.isSome_iff_exists.mp
    ((represent_isSome_eq signature r).trans (Bool.and_eq_true_iff.mp core.symm).2)
  rw [represent_eq signature l r hl hr, Option.some.injEq] at h
  exact ⟨l', r', hl, hr, h.symm⟩

/-! ## The compiler, rule by rule -/

section Unfolding

variable (signature : LogicalSignature Base Const) {equations : List (HOL.DefiningEquation Const)}

theorem compileModulo_impI {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {p q : HOL.Formula Const Γ} (body : HOL.ProofSyntaxModulo equations (p :: Δ) q)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    compileModulo signature (.impI body) objects hyps =
      (represent signature p).bind fun _ =>
        (compileModulo signature body (fun i => rename wk (objects i))
          (Fin.cases (.var 0) (fun i => rename wk (hyps i)))).map .lam := by
  simp only [compileModulo]
  cases represent signature p with
  | none => rfl
  | some _ =>
      cases compileModulo signature body (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hyps i))) <;> rfl

theorem compileModulo_impE {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {p q : HOL.Formula Const Γ} (function : HOL.ProofSyntaxModulo equations Δ (.imp p q))
    (argument : HOL.ProofSyntaxModulo equations Δ p)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    compileModulo signature (.impE function argument) objects hyps =
      (compileModulo signature function objects hyps).bind fun f =>
        (compileModulo signature argument objects hyps).map (.app f) := by
  simp only [compileModulo]
  cases compileModulo signature function objects hyps with
  | none => rfl
  | some _ => cases compileModulo signature argument objects hyps <;> rfl

theorem compileModulo_allI {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {σ : HOL.Ty Base}
    {φ : HOL.Formula Const (σ :: Γ)}
    (body : HOL.ProofSyntaxModulo equations (HOL.weakenHyps (σ := σ) Δ) φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    compileModulo signature (.allI body) objects hyps =
      (compileModulo signature body (liftSub objects)
        (fun i => rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))).map .lam := by
  simp only [compileModulo]
  cases compileModulo signature body (liftSub objects)
    (fun i => rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) <;> rfl

theorem compileModulo_allE {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {σ : HOL.Ty Base}
    {φ : HOL.Formula Const (σ :: Γ)} (t : HOL.Term Const Γ σ)
    (function : HOL.ProofSyntaxModulo equations Δ (.all φ))
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    compileModulo signature (.allE t function) objects hyps =
      (represent signature t).bind fun t' =>
        (compileModulo signature function objects hyps).map fun f => .app f (subst objects t') := by
  simp only [compileModulo]
  cases represent signature t with
  | none => rfl
  | some _ => cases compileModulo signature function objects hyps <;> rfl

theorem compileModulo_congr {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}
    {φ : HOL.Formula Const Γ} (d : HOL.ProofSyntaxModulo equations Δ φ) {n : Nat}
    {objects objects' : Sub Tower.Head Γ.length n} {hyps hyps' : Fin Δ.length → Tower.Tm n}
    (sameObjects : ∀ i, objects i = objects' i) (sameHyps : ∀ i, hyps i = hyps' i) :
    compileModulo signature d objects hyps = compileModulo signature d objects' hyps' := by
  rw [funext sameObjects, funext sameHyps]

end Unfolding

/-! ## Exact totality -/

/-- **Exact totality.** A proof modulo conversion compiles exactly when it is
core, for every signature, object terms and hypothesis terms. -/
theorem compileModulo_isSome_iff (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hyps : Fin Δ.length → Tower.Tm n) :
    (compileModulo signature d objects hyps).isSome ↔ IsCoreProofModulo d := by
  refine ⟨fun success => ?_, fun core => compileModulo_core_isSome signature d core objects hyps⟩
  induction d generalizing n with
  | hyp => trivial
  | @impI Γ Δ p q body ih =>
      rw [compileModulo_impI] at success
      cases hp : represent signature p with
      | none => rw [hp] at success; cases success
      | some _ =>
          rw [hp, Option.bind_some, Option.isSome_map] at success
          exact ⟨isCore_of_represent signature hp, ih _ _ success⟩
  | impE function argument ihf iha =>
      rw [compileModulo_impE] at success
      cases hf : compileModulo signature function objects hyps with
      | none => rw [hf] at success; cases success
      | some _ =>
          rw [hf, Option.bind_some, Option.isSome_map] at success
          exact ⟨ihf _ _ (by rw [hf]; rfl), iha _ _ success⟩
  | allI body ih =>
      rw [compileModulo_allI, Option.isSome_map] at success
      exact ih _ _ success
  | allE t function ih =>
      rw [compileModulo_allE] at success
      cases ht : represent signature t with
      | none => rw [ht] at success; cases success
      | some _ =>
          rw [ht, Option.bind_some, Option.isSome_map] at success
          exact ⟨isCore_of_represent signature ht, ih _ _ success⟩
  | convert _ inner ih => exact ih objects hyps success

/-! ## Changing only the indices of a proof -/

theorem compileModulo_castIndices (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ Δ' : List (HOL.Formula Const Γ)} {φ ψ : HOL.Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ) (d : HOL.ProofSyntaxModulo equations Δ φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ'.length → Tower.Tm n) :
    compileModulo signature (d.castIndices assumptions conclusion) objects hyps =
      compileModulo signature d objects (fun i => hyps (i.cast (congrArg List.length assumptions))) := by
  subst assumptions conclusion
  rfl

theorem compileModulo_cast_conclusion (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ ψ : HOL.Formula Const Γ} (conclusion : φ = ψ)
    (d : HOL.ProofSyntaxModulo equations Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hyps : Fin Δ.length → Tower.Tm n) :
    compileModulo signature (conclusion ▸ d) objects hyps = compileModulo signature d objects hyps := by
  subst conclusion
  rfl

/-! ## Context extension -/

/-- **Hypothesis extension.** Transporting the assumptions along an occurrence
map reindexes the hypothesis terms. -/
theorem compileModulo_mono (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ Δ' : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (transport : HOL.ProofSyntax.OccurrenceMap Δ Δ') (d : HOL.ProofSyntaxModulo equations Δ φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ'.length → Tower.Tm n) :
    compileModulo signature (d.mono transport) objects hyps =
      compileModulo signature d objects (fun i => hyps (transport.index i)) := by
  induction d generalizing n with
  | hyp i =>
      simp only [HOL.ProofSyntaxModulo.mono]
      rw [compileModulo_cast_conclusion]
      rfl
  | @impI Γ Δ p q body ih =>
      simp only [HOL.ProofSyntaxModulo.mono]
      erw [compileModulo_impI, compileModulo_impI]
      congr 1
      funext _
      congr 1
      refine (ih _ _ _).trans (compileModulo_congr signature body (fun _ => rfl) fun i => ?_)
      exact Fin.cases rfl (fun j => rfl) i
  | impE function argument ihf iha =>
      simp only [HOL.ProofSyntaxModulo.mono]
      erw [compileModulo_impE, compileModulo_impE]
      exact congrArg₂ (fun x (y : Tower.Tm n → Option (Tower.Tm n)) => x.bind y) (ihf _ _ _)
        (funext fun _ => congrArg _ (iha _ _ _))
  | allI body ih =>
      simp only [HOL.ProofSyntaxModulo.mono]
      erw [compileModulo_allI, compileModulo_allI]
      exact congrArg _ ((ih _ _ _).trans
        (compileModulo_congr signature body (fun _ => rfl) fun _ => rfl))
  | allE t function ih =>
      simp only [HOL.ProofSyntaxModulo.mono]
      erw [compileModulo_allE, compileModulo_allE]
      exact congrArg _ (funext fun _ => congrArg _ (ih _ _ _))
  | convert _ inner ih =>
      simp only [HOL.ProofSyntaxModulo.mono, compileModulo]
      exact ih _ _ _

/-- **Source renaming.** Renaming the object variables of a proof reindexes the
object terms along any native renaming compatible with it. -/
theorem compileModulo_rename (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) :
    ∀ {Γ' : HOL.Ctx Base} (ρ : HOL.Rename Base Γ Γ') (raw : Ren Γ.length Γ'.length)
      (_compatible : ∀ {τ : HOL.Ty Base} (i : HOL.Var Γ τ), variableIndex (ρ i) = raw (variableIndex i))
      {n : Nat} (objects : Sub Tower.Head Γ'.length n)
      (hyps : Fin (Δ.map (HOL.rename ρ)).length → Tower.Tm n),
      compileModulo signature (d.rename ρ) objects hyps =
        compileModulo signature d (fun i => objects (raw i)) (fun i => hyps (i.cast (by simp))) := by
  induction d with
  | hyp i =>
      intro Γ' ρ raw _ n objects hyps
      simp only [HOL.ProofSyntaxModulo.rename]
      rw [compileModulo_castIndices]
      rfl
  | @impI Γ Δ p q body ih =>
      intro Γ' ρ raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.rename]
      erw [compileModulo_impI, compileModulo_impI, represent_rename signature ρ raw compatible p]
      cases represent signature p with
      | none => rfl
      | some _ =>
          simp only [Option.map_some, Option.bind_some]
          congr 1
          refine (ih ρ raw compatible _ _).trans
            (compileModulo_congr signature body (fun _ => rfl) fun i => ?_)
          exact Fin.cases rfl (fun j => rfl) i
  | impE function argument ihf iha =>
      intro Γ' ρ raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.rename]
      erw [compileModulo_impE, compileModulo_impE]
      exact congrArg₂ (fun x (y : Tower.Tm n → Option (Tower.Tm n)) => x.bind y)
        (ihf ρ raw compatible _ _) (funext fun _ => congrArg _ (iha ρ raw compatible _ _))
  | @allI Γ Δ σ φ body ih =>
      intro Γ' ρ raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.rename]
      erw [compileModulo_allI, compileModulo_allI, compileModulo_castIndices]
      have lifted : ∀ {τ : HOL.Ty Base} (i : HOL.Var (σ :: Γ) τ),
          variableIndex (HOL.Rename.lift ρ i) = liftRen raw (variableIndex i) := by
        intro τ i
        cases i with
        | vz => rfl
        | vs i => exact congrArg Fin.succ (compatible i)
      refine congrArg _ ((ih (HOL.Rename.lift ρ) (liftRen raw) lifted _ _).trans
        (compileModulo_congr signature body (fun i => ?_) fun _ => rfl))
      exact Fin.cases rfl (fun j => rfl) i
  | allE t function ih =>
      intro Γ' ρ raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.rename]
      erw [compileModulo_castIndices, compileModulo_allE, compileModulo_allE,
        represent_rename signature ρ raw compatible t]
      cases represent signature t with
      | none => rfl
      | some t' =>
          simp only [Option.map_some, Option.bind_some, subst_rename]
          exact congrArg _ (ih ρ raw compatible _ _)
  | convert _ inner ih =>
      intro Γ' ρ raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.rename, compileModulo]
      exact ih ρ raw compatible objects hyps

/-- **Source weakening commutes with target renaming.** The proof weakened by a
new object variable, linked with the object terms lifted past a binder and the
hypothesis terms weakened, is the weakening of the linked proof. -/
theorem compileModulo_weaken (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ} {σ : HOL.Ty Base}
    (d : HOL.ProofSyntaxModulo equations Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hyps : Fin Δ.length → Tower.Tm n) :
    compileModulo signature (d.weaken (σ := σ)) (liftSub objects)
        (fun i => rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) =
      (compileModulo signature d objects hyps).map (rename wk) := by
  have renamed := compileModulo_rename signature d (Γ' := σ :: Γ) HOL.Rename.weaken wk
    (fun _ => rfl) (liftSub objects) (fun i => rename wk (hyps (i.cast (by simp))))
  have substituted := compileModulo_substitute signature d objects hyps (renSub wk)
  have renSubWk : (subst (renSub wk) : Tower.Tm n → Tower.Tm (n + 1)) = rename wk :=
    funext (subst_renSub wk)
  simp only [renSubWk] at substituted
  rw [← substituted]
  exact renamed.trans (compileModulo_congr signature d (fun _ => rfl) fun _ => rfl)

/-! ## Source substitution -/

/-- **Source substitution.** Substituting core terms for the object variables
of a proof substitutes their representations in the object terms, for any
native substitution compatible with it. -/
theorem compileModulo_sourceSubst (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) :
    ∀ {Γ' : HOL.Ctx Base} (θ : HOL.Subst Const Γ Γ') (core : HOL.CoreSubst θ)
      (raw : Sub Tower.Head Γ.length Γ'.length)
      (_compatible : ∀ {τ : HOL.Ty Base} (i : HOL.Var Γ τ),
        represent signature (θ i) = some (raw (variableIndex i)))
      {n : Nat} (objects : Sub Tower.Head Γ'.length n)
      (hyps : Fin (Δ.map (HOL.subst θ)).length → Tower.Tm n),
      compileModulo signature (d.subst θ core) objects hyps =
        compileModulo signature d (fun i => subst objects (raw i))
          (fun i => hyps (i.cast (by simp))) := by
  induction d with
  | hyp i =>
      intro Γ' θ core raw _ n objects hyps
      simp only [HOL.ProofSyntaxModulo.subst]
      rw [compileModulo_castIndices]
      rfl
  | @impI Γ Δ p q body ih =>
      intro Γ' θ core raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.subst]
      erw [compileModulo_impI, compileModulo_impI, represent_subst signature θ raw compatible p]
      cases represent signature p with
      | none => rfl
      | some _ =>
          simp only [Option.map_some, Option.bind_some]
          congr 1
          refine (ih θ core raw compatible _ _).trans
            (compileModulo_congr signature body (fun i => ?_) fun i => ?_)
          · exact (rename_subst wk objects (raw i)).symm
          · exact Fin.cases rfl (fun j => rfl) i
  | impE function argument ihf iha =>
      intro Γ' θ core raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.subst]
      erw [compileModulo_impE, compileModulo_impE]
      exact congrArg₂ (fun x (y : Tower.Tm n → Option (Tower.Tm n)) => x.bind y)
        (ihf θ core raw compatible _ _) (funext fun _ => congrArg _ (iha θ core raw compatible _ _))
  | @allI Γ Δ σ φ body ih =>
      intro Γ' θ core raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.subst]
      erw [compileModulo_allI, compileModulo_allI, compileModulo_castIndices]
      have lifted : ∀ {τ : HOL.Ty Base} (i : HOL.Var (σ :: Γ) τ),
          represent signature (HOL.Subst.lift θ i) = some (liftSub raw (variableIndex i)) := by
        intro τ i
        cases i with
        | vz => rfl
        | vs i =>
            change represent signature (HOL.rename HOL.Rename.weaken (θ i)) = _
            rw [represent_rename signature HOL.Rename.weaken wk (fun _ => rfl), compatible i]
            rfl
      refine congrArg _ ((ih (HOL.Subst.lift θ) core.lift (liftSub raw) lifted _ _).trans
        (compileModulo_congr signature body (fun i => ?_) fun _ => rfl))
      refine Fin.cases rfl (fun j => ?_) i
      exact subst_liftSub_wk objects (raw j)
  | allE t function ih =>
      intro Γ' θ core raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.subst]
      erw [compileModulo_castIndices, compileModulo_allE, compileModulo_allE,
        represent_subst signature θ raw compatible t]
      cases represent signature t with
      | none => rfl
      | some t' =>
          simp only [Option.map_some, Option.bind_some, subst_comp]
          exact congrArg _ (ih θ core raw compatible _ _)
  | convert _ inner ih =>
      intro Γ' θ core raw compatible n objects hyps
      simp only [HOL.ProofSyntaxModulo.subst, compileModulo]
      exact ih θ core raw compatible objects hyps

/-- Source substitution along the native substitution of the representations. -/
theorem compileModulo_sourceSubst_native (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ Γ' : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) (θ : HOL.Subst Const Γ Γ') (core : HOL.CoreSubst θ)
    {n : Nat} (objects : Sub Tower.Head Γ'.length n)
    (hyps : Fin (Δ.map (HOL.subst θ)).length → Tower.Tm n) :
    compileModulo signature (d.subst θ core) objects hyps =
      compileModulo signature d (fun i => subst objects (nativeSubstitution signature θ i))
        (fun i => hyps (i.cast (by simp))) :=
  compileModulo_sourceSubst signature d θ core (nativeSubstitution signature θ)
    (nativeSubstitution_compatible signature θ core) objects hyps

/-! ## Specialization -/

/-- **Specialization.** The linked term of a proof instantiated at a core term
is the instance of the linked open proof at the term's representation. -/
theorem compileModulo_instantiate (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {σ : HOL.Ty Base} {φ : HOL.Formula Const (σ :: Γ)}
    (t : HOL.Term Const Γ σ) (core : t.isCore = true) {t' : Tower.Tm Γ.length}
    (represented : represent signature t = some t')
    (d : HOL.ProofSyntaxModulo equations (HOL.weakenHyps (σ := σ) Δ) φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    compileModulo signature (d.instantiate t core) objects hyps =
      (compileModulo signature d (liftSub objects)
        (fun i => rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))).map
        (inst0 (subst objects t')) := by
  unfold HOL.ProofSyntaxModulo.instantiate
  erw [compileModulo_castIndices]
  refine (compileModulo_sourceSubst signature d (HOL.Subst.single t) (HOL.CoreSubst.single core)
    (subst0 t') (fun i => by cases i with | vz => exact represented | vs _ => rfl) objects _).trans ?_
  have substituted := compileModulo_substitute signature d (liftSub objects)
    (fun i => rename wk (hyps (i.cast (by simp [HOL.weakenHyps])))) (subst0 (subst objects t'))
  have inst : (inst0 (subst objects t') : Tower.Tm (n + 1) → Tower.Tm n) =
      subst (subst0 (subst objects t')) := rfl
  rw [inst, ← substituted]
  refine compileModulo_congr signature d (fun i => ?_) fun i => ?_
  · refine Fin.cases rfl (fun j => ?_) i
    exact (inst0_rename_wk (subst objects t') (objects j)).symm
  · exact (inst0_rename_wk (subst objects t') _).symm

/-- The linked term of a generalization eliminated at a term. -/
theorem compileModulo_allE_allI (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {σ : HOL.Ty Base} {φ : HOL.Formula Const (σ :: Γ)}
    (t : HOL.Term Const Γ σ) {t' : Tower.Tm Γ.length} (represented : represent signature t = some t')
    (d : HOL.ProofSyntaxModulo equations (HOL.weakenHyps (σ := σ) Δ) φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n) :
    compileModulo signature (.allE t (.allI d)) objects hyps =
      (compileModulo signature d (liftSub objects)
        (fun i => rename wk (hyps (i.cast (by simp [HOL.weakenHyps]))))).map
        (fun b => .app (.lam b) (subst objects t')) := by
  rw [compileModulo_allE, compileModulo_allI, represented, Option.bind_some, Option.map_map]
  rfl

/-- **Specialization as computation.** Eliminating a generalization at a core
term links to a term that β-reduces in one step to the linked instance. -/
theorem compileModulo_allE_allI_step (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {σ : HOL.Ty Base} {φ : HOL.Formula Const (σ :: Γ)}
    (t : HOL.Term Const Γ σ) (core : t.isCore = true)
    (d : HOL.ProofSyntaxModulo equations (HOL.weakenHyps (σ := σ) Δ) φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n)
    {out : Tower.Tm n} (linked : compileModulo signature (.allE t (.allI d)) objects hyps = some out) :
    ∃ out', compileModulo signature (d.instantiate t core) objects hyps = some out' ∧
      ∀ (root : RootComputation Tower.Head) (headEq : Tower.Head → Tower.Head → Prop),
        StepCore root headEq out out' := by
  obtain ⟨t', represented⟩ := Modulo.represent_isCore signature t core
  rw [compileModulo_allE_allI signature t represented] at linked
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp linked
  refine ⟨inst0 (subst objects t') b, ?_, fun root headEq => .betaPi b (subst objects t')⟩
  rw [compileModulo_instantiate signature t core represented, hb]
  rfl

/-! ## Declaration compatibility -/

/-- A signature embedding: a map of constants under which the target signature
interprets the image of each constant as the source interprets the constant,
with the same logical symbols. -/
structure SignatureEmbedding {Const' : HOL.Ty Base → Type w}
    (source : LogicalSignature Base Const) (target : LogicalSignature Base Const') where
  map : ∀ {τ : HOL.Ty Base}, Const τ → Const' τ
  constant : ∀ {τ : HOL.Ty Base} (c : Const τ), target.constant (map c) = source.constant c
  implication : target.implication = source.implication
  universal : ∀ τ, target.universal τ = source.universal τ
  equality : ∀ τ, target.equality τ = source.equality τ

namespace SignatureEmbedding

variable {Const' : HOL.Ty Base → Type w} {source : LogicalSignature Base Const}
  {target : LogicalSignature Base Const'}

theorem represent_mapConst (e : SignatureEmbedding source target) :
    ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ),
      represent target (HOL.mapConst e.map t) = represent source t
  | _, _, .var _ => rfl
  | _, _, .const c => by simp only [HOL.mapConst, represent, e.constant]
  | _, _, .app f a => by
      simp only [HOL.mapConst, represent, represent_mapConst e f, represent_mapConst e a]
  | _, _, .lam b => by simp only [HOL.mapConst, represent, represent_mapConst e b]
  | _, _, .imp p q => by
      simp only [HOL.mapConst, represent, represent_mapConst e p, represent_mapConst e q,
        e.implication]
  | _, _, .all b => by
      simp only [HOL.mapConst, represent, represent_mapConst e b, e.universal]
  | _, _, .eq l r => by
      simp only [HOL.mapConst, represent, represent_mapConst e l, represent_mapConst e r,
        e.equality]
  | _, _, .top | _, _, .bot | _, _, .and _ _ | _, _, .or _ _ | _, _, .not _
  | _, _, .ex _ => rfl

end SignatureEmbedding

/-- **Declaration compatibility.** Along a signature embedding, the image of a
proof links to the same term. -/
theorem compileModulo_mapConst {Const' : HOL.Ty Base → Type w}
    {source : LogicalSignature Base Const} {target : LogicalSignature Base Const'}
    (e : SignatureEmbedding source target)
    {equations : List (HOL.DefiningEquation Const)} {equations' : List (HOL.DefiningEquation Const')}
    (listed : ∀ equation ∈ equations, HOL.DefiningEquation.mapConst e.map equation ∈ equations')
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) :
    ∀ {n : Nat} (objects : Sub Tower.Head Γ.length n)
      (hyps : Fin (Δ.map (HOL.mapConst e.map)).length → Tower.Tm n),
      compileModulo target (d.mapConst e.map listed) objects hyps =
        compileModulo source d objects (fun i => hyps (i.cast (by simp))) := by
  induction d with
  | hyp i =>
      intro n objects hyps
      simp only [HOL.ProofSyntaxModulo.mapConst]
      rw [compileModulo_castIndices]
      rfl
  | @impI Γ Δ p q body ih =>
      intro n objects hyps
      simp only [HOL.ProofSyntaxModulo.mapConst]
      erw [compileModulo_impI, compileModulo_impI, e.represent_mapConst p]
      cases represent source p with
      | none => rfl
      | some _ =>
          simp only [Option.bind_some]
          congr 1
          refine (ih _ _).trans (compileModulo_congr source body (fun _ => rfl) fun i => ?_)
          exact Fin.cases rfl (fun j => rfl) i
  | impE function argument ihf iha =>
      intro n objects hyps
      simp only [HOL.ProofSyntaxModulo.mapConst]
      erw [compileModulo_impE, compileModulo_impE]
      exact congrArg₂ (fun x (y : Tower.Tm n → Option (Tower.Tm n)) => x.bind y) (ihf _ _)
        (funext fun _ => congrArg _ (iha _ _))
  | allI body ih =>
      intro n objects hyps
      simp only [HOL.ProofSyntaxModulo.mapConst]
      erw [compileModulo_allI, compileModulo_allI, compileModulo_castIndices]
      exact congrArg _ ((ih _ _).trans (compileModulo_congr source body (fun _ => rfl) fun _ => rfl))
  | allE t function ih =>
      intro n objects hyps
      simp only [HOL.ProofSyntaxModulo.mapConst]
      erw [compileModulo_castIndices, compileModulo_allE, compileModulo_allE, e.represent_mapConst t]
      exact congrArg _ (funext fun _ => congrArg _ (ih _ _))
  | convert _ inner ih =>
      intro n objects hyps
      simp only [HOL.ProofSyntaxModulo.mapConst, compileModulo]
      exact ih objects hyps

/-! ## Dependency -/

/-- **Frame.** A linked term reads only the hypotheses the proof uses. -/
theorem compileModulo_frame (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    {hyps hyps' : Fin Δ.length → Tower.Tm n} (agree : ∀ i, d.usesHyp i = true → hyps i = hyps' i) :
    compileModulo signature d objects hyps = compileModulo signature d objects hyps' := by
  induction d generalizing n with
  | hyp i =>
      simp only [compileModulo]
      rw [agree i (by simp [HOL.ProofSyntaxModulo.usesHyp])]
  | impI body ih =>
      rw [compileModulo_impI, compileModulo_impI]
      congr 1
      funext _
      congr 1
      refine ih _ fun i used => ?_
      refine Fin.cases (fun _ => rfl) (fun j used => ?_) i used
      exact congrArg (rename wk) (agree j used)
  | impE function argument ihf iha =>
      rw [compileModulo_impE, compileModulo_impE,
        ihf _ fun i used => agree i (by simp [HOL.ProofSyntaxModulo.usesHyp, used]),
        iha _ fun i used => agree i (by simp [HOL.ProofSyntaxModulo.usesHyp, used])]
  | allI body ih =>
      rw [compileModulo_allI, compileModulo_allI]
      refine congrArg _ (ih _ fun i used => congrArg (rename wk) (agree _ used))
  | allE t function ih =>
      rw [compileModulo_allE, compileModulo_allE, ih _ agree]
  | convert _ inner ih =>
      simp only [compileModulo]
      exact ih _ agree

/-- The constant names the signature can insert: those of its constants and
logical symbols. -/
def _root_.Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface.LogicalSignature.SymbolName
    (signature : LogicalSignature Base Const) (name : DeclName) : Prop :=
  (∃ τ : HOL.Ty Base, ∃ c : Const τ, name ∈ constantNames (signature.constant c)) ∨
    name ∈ constantNames signature.implication ∨
    (∃ τ : HOL.Ty Base, name ∈ constantNames (signature.universal τ)) ∨
    (∃ τ : HOL.Ty Base, name ∈ constantNames (signature.equality τ))

theorem mem_constantNames_subst {n m : Nat} (σ : Sub Tower.Head n m) (t : Tower.Tm n)
    {name : DeclName} (mem : name ∈ constantNames (subst σ t)) :
    name ∈ constantNames t ∨ ∃ i, name ∈ constantNames (σ i) := by
  have liftCase : ∀ {k l : Nat} (τ : Sub Tower.Head k l) (i : Fin (k + 1)),
      name ∈ constantNames (liftSub τ i) → ∃ j, name ∈ constantNames (τ j) := by
    intro k l τ i h
    refine Fin.cases (fun h => ?_) (fun j h => ?_) i h
    · simp [liftSub, constantNames] at h
    · exact ⟨j, by simpa only [liftSub, Fin.cases_succ, constantNames_rename] using h⟩
  induction t generalizing m with
  | var i => exact .inr ⟨i, mem⟩
  | const c => exact .inl mem
  | head h => exact .inl mem
  | pi A B ihA ihB | sigma A B ihA ihB =>
      simp only [subst, constantNames, List.mem_append] at mem ⊢
      rcases mem with mem | mem
      · exact (ihA σ mem).imp .inl id
      · rcases ihB (liftSub σ) mem with h | ⟨i, h⟩
        · exact .inl (.inr h)
        · exact .inr (liftCase σ i h)
  | lam b ih =>
      simp only [subst, constantNames] at mem ⊢
      rcases ih (liftSub σ) mem with h | ⟨i, h⟩
      · exact .inl h
      · exact .inr (liftCase σ i h)
  | id A a b ihA iha ihb =>
      simp only [subst, constantNames, List.mem_append] at mem ⊢
      rcases mem with (mem | mem) | mem
      · exact (ihA σ mem).imp (fun h => .inl (.inl h)) id
      · exact (iha σ mem).imp (fun h => .inl (.inr h)) id
      · exact (ihb σ mem).imp .inr id
  | app f a ihf iha | pair f a ihf iha =>
      simp only [subst, constantNames, List.mem_append] at mem ⊢
      rcases mem with mem | mem
      · exact (ihf σ mem).imp .inl id
      · exact (iha σ mem).imp .inr id
  | fst p ih | snd p ih | refl p ih =>
      simp only [subst, constantNames] at mem ⊢
      exact ih σ mem

theorem symbolName_of_represent (signature : LogicalSignature Base Const) :
    ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {t : HOL.Term Const Γ τ} {out : Tower.Tm Γ.length},
      represent signature t = some out → ∀ {name : DeclName}, name ∈ constantNames out →
        signature.SymbolName name
  | _, _, .var _, out, h, name, mem => by
      simp only [represent, Option.some.injEq] at h
      subst h
      simp [constantNames] at mem
  | _, _, .const c, out, h, name, mem => by
      simp only [represent, Option.some.injEq] at h
      subst h
      rw [ConstantExpansion.constantNames_liftClosed] at mem
      exact .inl ⟨_, c, mem⟩
  | _, _, .app f a, out, h, name, mem => by
      obtain ⟨f', a', hf, ha, rfl⟩ := represent_app_inv signature h
      simp only [constantNames, List.mem_append] at mem
      rcases mem with mem | mem
      · exact symbolName_of_represent signature hf mem
      · exact symbolName_of_represent signature ha mem
  | _, _, .lam b, out, h, name, mem => by
      simp only [represent] at h
      obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
      exact symbolName_of_represent signature hb mem
  | _, _, .imp p q, out, h, name, mem => by
      obtain ⟨p', q', hp, hq, rfl⟩ := represent_imp_inv signature h
      simp only [constantNames, List.mem_append, ConstantExpansion.constantNames_liftClosed] at mem
      rcases mem with (mem | mem) | mem
      · exact .inr (.inl mem)
      · exact symbolName_of_represent signature hp mem
      · exact symbolName_of_represent signature hq mem
  | _, _, .all b, out, h, name, mem => by
      rw [represent_all] at h
      obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [constantNames, List.mem_append, ConstantExpansion.constantNames_liftClosed] at mem
      rcases mem with mem | mem
      · exact .inr (.inr (.inl ⟨_, mem⟩))
      · exact symbolName_of_represent signature hb mem
  | _, _, .eq l r, out, h, name, mem => by
      obtain ⟨l', r', hl, hr, rfl⟩ := represent_eq_inv signature h
      simp only [constantNames, List.mem_append, ConstantExpansion.constantNames_liftClosed] at mem
      rcases mem with (mem | mem) | mem
      · exact .inr (.inr (.inr ⟨_, mem⟩))
      · exact symbolName_of_represent signature hl mem
      · exact symbolName_of_represent signature hr mem
  | _, _, .top, _, h, _, _ | _, _, .bot, _, h, _, _ | _, _, .and _ _, _, h, _, _
  | _, _, .or _ _, _, h, _, _ | _, _, .not _, _, h, _, _ | _, _, .ex _, _, h, _, _ => by
      cases h

/-- **Constants of a linked term.** Every constant of a linked term is a symbol
of the signature, a constant of an object term, or a constant of a hypothesis
term the proof uses. -/
theorem constantNames_compileModulo (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) :
    ∀ {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n)
      {out : Tower.Tm n}, compileModulo signature d objects hyps = some out →
      ∀ {name : DeclName}, name ∈ constantNames out →
        signature.SymbolName name ∨ (∃ j, name ∈ constantNames (objects j)) ∨
          ∃ i, d.usesHyp i = true ∧ name ∈ constantNames (hyps i) := by
  induction d with
  | hyp i =>
      intro n objects hyps out h name mem
      simp only [compileModulo, Option.some.injEq] at h
      subst h
      exact .inr (.inr ⟨i, by simp [HOL.ProofSyntaxModulo.usesHyp], mem⟩)
  | @impI Γ Δ p q body ih =>
      intro n objects hyps out h name mem
      rw [compileModulo_impI] at h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases ih _ _ hb mem with symbol | ⟨j, hj⟩ | ⟨i, used, hi⟩
      · exact .inl symbol
      · exact .inr (.inl ⟨j, by simpa only [constantNames_rename] using hj⟩)
      · refine Fin.cases (fun _ hi => ?_) (fun i used hi => ?_) i used hi
        · simp [constantNames] at hi
        · refine .inr (.inr ⟨i, used, ?_⟩)
          simpa only [Fin.cases_succ, constantNames_rename] using hi
  | impE function argument ihf iha =>
      intro n objects hyps out h name mem
      rw [compileModulo_impE] at h
      obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [constantNames, List.mem_append] at mem
      rcases mem with mem | mem
      · rcases ihf _ _ hf mem with symbol | objectName | ⟨i, used, hi⟩
        · exact .inl symbol
        · exact .inr (.inl objectName)
        · exact .inr (.inr ⟨i, by simp [HOL.ProofSyntaxModulo.usesHyp, used], hi⟩)
      · rcases iha _ _ ha mem with symbol | objectName | ⟨i, used, hi⟩
        · exact .inl symbol
        · exact .inr (.inl objectName)
        · exact .inr (.inr ⟨i, by simp [HOL.ProofSyntaxModulo.usesHyp, used], hi⟩)
  | allI body ih =>
      intro n objects hyps out h name mem
      rw [compileModulo_allI] at h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases ih _ _ hb mem with symbol | ⟨j, hj⟩ | ⟨i, used, hi⟩
      · exact .inl symbol
      · refine Fin.cases (fun hj => ?_) (fun j hj => ?_) j hj
        · simp [liftSub, constantNames] at hj
        · exact .inr (.inl ⟨j, by simpa only [liftSub, Fin.cases_succ, constantNames_rename]
            using hj⟩)
      · refine .inr (.inr ⟨i.cast (by simp [HOL.weakenHyps]), ?_, ?_⟩)
        · simpa [HOL.ProofSyntaxModulo.usesHyp] using used
        · simpa only [constantNames_rename] using hi
  | allE t function ih =>
      intro n objects hyps out h name mem
      rw [compileModulo_allE] at h
      obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [constantNames, List.mem_append] at mem
      rcases mem with mem | mem
      · rcases ih _ _ hf mem with symbol | objectName | ⟨i, used, hi⟩
        · exact .inl symbol
        · exact .inr (.inl objectName)
        · exact .inr (.inr ⟨i, by simpa [HOL.ProofSyntaxModulo.usesHyp] using used, hi⟩)
      · rcases mem_constantNames_subst objects t' mem with inTerm | objectName
        · exact .inl (symbolName_of_represent signature ht inTerm)
        · exact .inr (.inl objectName)
  | convert _ inner ih =>
      intro n objects hyps out h name mem
      simp only [compileModulo] at h
      rcases ih _ _ h mem with symbol | objectName | ⟨i, used, hi⟩
      · exact .inl symbol
      · exact .inr (.inl objectName)
      · exact .inr (.inr ⟨i, by simpa [HOL.ProofSyntaxModulo.usesHyp] using used, hi⟩)

/-- **Every used hypothesis occurs in the linked term.** -/
theorem constantNames_hyp_compileModulo (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) :
    ∀ {n : Nat} (objects : Sub Tower.Head Γ.length n) (hyps : Fin Δ.length → Tower.Tm n)
      {out : Tower.Tm n}, compileModulo signature d objects hyps = some out →
      ∀ (i : Fin Δ.length), d.usesHyp i = true →
        ∀ {name : DeclName}, name ∈ constantNames (hyps i) → name ∈ constantNames out := by
  induction d with
  | hyp j =>
      intro n objects hyps out h i used name mem
      simp only [compileModulo, Option.some.injEq] at h
      subst h
      simp only [HOL.ProofSyntaxModulo.usesHyp, decide_eq_true_eq] at used
      subst used
      exact mem
  | @impI Γ Δ p q body ih =>
      intro n objects hyps out h i used name mem
      rw [compileModulo_impI] at h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ih _ _ hb i.succ used (by simpa only [Fin.cases_succ, constantNames_rename] using mem)
  | impE function argument ihf iha =>
      intro n objects hyps out h i used name mem
      rw [compileModulo_impE] at h
      obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [HOL.ProofSyntaxModulo.usesHyp, Bool.or_eq_true] at used
      simp only [constantNames, List.mem_append]
      rcases used with used | used
      · exact .inl (ihf _ _ hf i used mem)
      · exact .inr (iha _ _ ha i used mem)
  | allI body ih =>
      intro n objects hyps out h i used name mem
      rw [compileModulo_allI] at h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ih _ _ hb _ used (by rw [constantNames_rename]; exact mem)
  | allE t function ih =>
      intro n objects hyps out h i used name mem
      rw [compileModulo_allE] at h
      obtain ⟨t', _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [constantNames, List.mem_append]
      exact .inl (ih _ _ hf i used mem)
  | convert _ inner ih =>
      intro n objects hyps out h i used name mem
      simp only [compileModulo] at h
      exact ih _ _ h i used mem

/-- **The frame is tight.** Replacing a used hypothesis by a constant that does
not occur in the linked term changes the linked term. -/
theorem compileModulo_frame_tight (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hyps : Fin Δ.length → Tower.Tm n) {out : Tower.Tm n}
    (linked : compileModulo signature d objects hyps = some out) (i : Fin Δ.length)
    (used : d.usesHyp i = true) {fresh : DeclName} (absent : fresh ∉ constantNames out) :
    ∃ out', compileModulo signature d objects (Function.update hyps i (.const fresh)) = some out' ∧
      out' ≠ out := by
  have core := (compileModulo_isSome_iff signature d objects hyps).mp (by rw [linked]; rfl)
  obtain ⟨out', linked'⟩ := Option.isSome_iff_exists.mp
    ((compileModulo_isSome_iff signature d objects (Function.update hyps i (.const fresh))).mpr core)
  refine ⟨out', linked', fun same => absent ?_⟩
  rw [← same]
  refine constantNames_hyp_compileModulo signature d objects _ linked' i used ?_
  simp [constantNames]

/-! ## The residual list -/

/-- The hypothesis terms of a link: the realization of each published
assumption, and the assumption constant of each other one. -/
def linkHyps {k n : Nat} (published : Fin k → Option (Tower.Tm 0)) (names : Fin k → DeclName) :
    Fin k → Tower.Tm n :=
  fun i => liftClosed ((published i).getD (.const (names i)))

/-- The used assumptions that are not published, in order. -/
def residual {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) (published : Fin Δ.length → Option (Tower.Tm 0)) :
    List (Fin Δ.length) :=
  d.usedHyps.filter fun i => (published i).isNone

/-- **Residual assumptions.** The assumption constants of a link are exactly the
used assumptions that are not published, when the assumption names are
distinct and fresh for the signature, the object terms and the realizations. -/
theorem assumed_link (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (published : Fin Δ.length → Option (Tower.Tm 0)) (names : Fin Δ.length → DeclName)
    (distinct : Function.Injective names)
    (freshSymbols : ∀ i, ¬ signature.SymbolName (names i))
    (freshObjects : ∀ i j, names i ∉ constantNames (objects j))
    (freshRealizations : ∀ i j r, published j = some r → names i ∉ constantNames r)
    {out : Tower.Tm n} (linked : compileModulo signature d objects (linkHyps published names) = some out)
    (i : Fin Δ.length) :
    names i ∈ constantNames out ↔ d.usesHyp i = true ∧ published i = none := by
  constructor
  · intro mem
    rcases constantNames_compileModulo signature d objects _ linked mem with
      symbol | ⟨j, hj⟩ | ⟨j, used, hj⟩
    · exact absurd symbol (freshSymbols i)
    · exact absurd hj (freshObjects i j)
    · simp only [linkHyps, ConstantExpansion.constantNames_liftClosed] at hj
      cases hp : published j with
      | some r =>
          rw [hp] at hj
          exact absurd hj (freshRealizations i j r hp)
      | none =>
          rw [hp] at hj
          simp only [Option.getD_none, constantNames, List.mem_singleton] at hj
          obtain rfl := distinct hj
          exact ⟨used, hp⟩
  · rintro ⟨used, unpublished⟩
    refine constantNames_hyp_compileModulo signature d objects _ linked i used ?_
    simp [linkHyps, unpublished, constantNames]

/-- The residual list, as lists: the assumptions whose constants occur in the
link, in order, are the residual assumptions. -/
theorem assumed_eq_residual (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)} {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (d : HOL.ProofSyntaxModulo equations Δ φ) {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (published : Fin Δ.length → Option (Tower.Tm 0)) (names : Fin Δ.length → DeclName)
    (distinct : Function.Injective names)
    (freshSymbols : ∀ i, ¬ signature.SymbolName (names i))
    (freshObjects : ∀ i j, names i ∉ constantNames (objects j))
    (freshRealizations : ∀ i j r, published j = some r → names i ∉ constantNames r)
    {out : Tower.Tm n} (linked : compileModulo signature d objects (linkHyps published names) = some out) :
    (List.finRange Δ.length).filter (fun i => decide (names i ∈ constantNames out)) =
      residual d published := by
  unfold residual HOL.ProofSyntaxModulo.usedHyps
  rw [List.filter_filter]
  apply List.filter_congr
  intro i _
  have iff := assumed_link signature d objects published names distinct freshSymbols freshObjects
    freshRealizations linked i
  by_cases mem : names i ∈ constantNames out
  · obtain ⟨used, unpublished⟩ := iff.mp mem
    simp [mem, used, unpublished]
  · have notBoth : ¬ (d.usesHyp i = true ∧ published i = none) := fun h => mem (iff.mpr h)
    cases hu : d.usesHyp i <;> cases hp : published i <;> simp_all

end Modulo

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
