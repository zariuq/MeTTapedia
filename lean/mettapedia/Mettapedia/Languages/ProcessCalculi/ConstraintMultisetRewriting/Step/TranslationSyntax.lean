import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFrames
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureEmbedding

/-!
# Second-order frames inside dependent frames: the syntax

A second-order frame with finitely many metavariables, in order, is a list of metavariable
arities. Its translation is a telescope in which a metavariable of arity `(Γ, s)` is a variable of
the closed type `Π Γ. s`. A second-order term at the frame, in an object context `Γ`, becomes a raw
dependent term over the scope `k + |Γ|`, where `k` is the number of metavariables:

* object variables stay variables, in the innermost `|Γ|` positions (`inner`);
* a constructor becomes its declared constant, applied to the closed bodies of its arguments, as
  in `BindingSignatureEmbedding.encode`;
* a metavariable occurrence `m(a₀, …, aₚ₋₁)` becomes the variable of `m` (`outer`) applied to the
  translated arguments, last argument first (`spine`), matching the order of `Π Γ. s`.

A contextual assignment becomes a substitution of closed abstractions (`homCode`).

**Contextual instantiation is beta on spines** (`instantiate_beta`, `action_beta`): substituting
the abstractions into the translation of a term computes, by beta steps only, to the translation of
the instantiated term. Renaming and object substitution commute with the translation
(`encode_rename`, `encode_bind`). Each law is stated for every substitution that agrees with the
expected one on the object positions and the metavariable positions, so that it lifts through
binders by a one-line lemma.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation

open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type}

/-! ## Scopes: metavariables outside, object variables inside -/

/-- The object positions of the scope `k + p`: its innermost `p` variables. -/
def inner {k : Nat} : {p : Nat} → Fin p → Fin (k + p)
  | 0, j => j.elim0
  | p + 1, j => Fin.cases (motive := fun _ => Fin (k + (p + 1))) ⟨0, by omega⟩
      (fun j => (inner j).succ) j

/-- The metavariable positions of the scope `k + p`: its outermost `k` variables. -/
def outer {k : Nat} : {p : Nat} → Fin k → Fin (k + p)
  | 0, i => i
  | _ + 1, i => (outer i).succ

/-- Substitute the object positions by `w` and the metavariable positions by `τ`. -/
def appendSub {k n : Nat} : {p : Nat} → Sub Head p n → Sub Head k n → Sub Head (k + p) n
  | 0, _, τ => τ
  | _ + 1, w, τ => consSub (w 0) (appendSub (fun j => w j.succ) τ)

theorem appendSub_inner {k n : Nat} : ∀ {p : Nat} (w : Sub Head p n) (τ : Sub Head k n)
    (j : Fin p), appendSub w τ (inner j) = w j
  | 0, _, _, j => j.elim0
  | _ + 1, w, τ, j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · exact appendSub_inner (fun j => w j.succ) τ j

theorem appendSub_outer {k n : Nat} : ∀ {p : Nat} (w : Sub Head p n) (τ : Sub Head k n)
    (i : Fin k), appendSub w τ (outer i) = τ i
  | 0, _, _, _ => rfl
  | _ + 1, w, τ, i => appendSub_outer (fun j => w j.succ) τ i

/-- The position of a variable in its context, for any sort type. -/
def vIdx {Srt : Type} : {Γ : List Srt} → {s : Srt} → Binding.Var Γ s → Fin Γ.length
  | _, _, .zero => ⟨0, Nat.succ_pos _⟩
  | _, _, .succ w => (vIdx w).succ

/-! ## Spines and abstractions -/

/-- Apply a head to `p` arguments, the last argument first: `f w(p-1) … w(0)`. -/
def spine {n : Nat} (f : Tm Head n) : {p : Nat} → Sub Head p n → Tm Head n
  | 0, _ => f
  | _ + 1, w => .app (spine f (fun j => w j.succ)) (w 0)

/-- Apply a head to `p` arguments, the first argument first: `f w(0) … w(p-1)`. -/
def applyVec {n : Nat} : Tm Head n → {p : Nat} → Sub Head p n → Tm Head n
  | f, 0, _ => f
  | f, _ + 1, w => applyVec (.app f (w 0)) (fun j => w j.succ)

/-- Close the innermost `p` positions, innermost first. -/
def abstractN {k : Nat} : (p : Nat) → Tm Head (k + p) → Tm Head k
  | 0, body => body
  | p + 1, body => abstractN p (.lam body)

variable {S : Binding.Signature}

/-- Close the binders of one constructor argument, innermost first, at an offset scope. -/
def abstractB {Srt : Type} {k : Nat} {Γ : List Srt} : (bound : List Srt) →
    Tm Head (k + (bound ++ Γ).length) → Tm Head (k + Γ.length)
  | [], body => body
  | _ :: bound, body => abstractB bound (.lam body)

/-- Lift a renaming of offset scopes under the binders of one argument. -/
def liftRenB {Srt : Type} {k k' : Nat} {Γ Δ : List Srt} (ρ : Ren (k + Γ.length) (k' + Δ.length)) :
    (bound : List Srt) → Ren (k + (bound ++ Γ).length) (k' + (bound ++ Δ).length)
  | [] => ρ
  | _ :: bound => liftRen (liftRenB ρ bound)

/-- Lift a substitution of offset scopes under the binders of one argument. -/
def liftSubB {Srt : Type} {k k' : Nat} {Γ Δ : List Srt} (σ : Sub Head (k + Γ.length) (k' + Δ.length)) :
    (bound : List Srt) → Sub Head (k + (bound ++ Γ).length) (k' + (bound ++ Δ).length)
  | [] => σ
  | _ :: bound => liftSub (liftSubB σ bound)

/-- Lift a substitution under `p` binders. -/
def liftN {k n : Nat} (σ : Sub Head k n) : (p : Nat) → Sub Head (k + p) (n + p)
  | 0 => σ
  | p + 1 => liftSub (liftN σ p)

theorem rename_spine {n m : Nat} (ρ : Ren n m) (f : Tm Head n) :
    ∀ {p : Nat} (w : Sub Head p n),
      rename ρ (spine f w) = spine (rename ρ f) (fun j => rename ρ (w j))
  | 0, _ => rfl
  | _ + 1, w => congrArg (fun g => Tm.app g (rename ρ (w 0))) (rename_spine ρ f (fun j => w j.succ))

theorem subst_spine {n m : Nat} (σ : Sub Head n m) (f : Tm Head n) :
    ∀ {p : Nat} (w : Sub Head p n),
      subst σ (spine f w) = spine (subst σ f) (fun j => subst σ (w j))
  | 0, _ => rfl
  | _ + 1, w => congrArg (fun g => Tm.app g (subst σ (w 0))) (subst_spine σ f (fun j => w j.succ))

theorem rename_applyVec {n m : Nat} (ρ : Ren n m) :
    ∀ {p : Nat} (f : Tm Head n) (w : Sub Head p n),
      rename ρ (applyVec f w) = applyVec (rename ρ f) (fun j => rename ρ (w j))
  | 0, _, _ => rfl
  | _ + 1, f, w => rename_applyVec ρ (.app f (w 0)) (fun j => w j.succ)

theorem subst_applyVec {n m : Nat} (σ : Sub Head n m) :
    ∀ {p : Nat} (f : Tm Head n) (w : Sub Head p n),
      subst σ (applyVec f w) = applyVec (subst σ f) (fun j => subst σ (w j))
  | 0, _, _ => rfl
  | _ + 1, f, w => subst_applyVec σ (.app f (w 0)) (fun j => w j.succ)

theorem rename_abstractB {Srt : Type} {k k' : Nat} {Γ Δ : List Srt}
    (ρ : Ren (k + Γ.length) (k' + Δ.length)) :
    ∀ (bound : List Srt) (body : Tm Head (k + (bound ++ Γ).length)),
      rename ρ (abstractB (Γ := Γ) bound body) =
        abstractB (Γ := Δ) bound (rename (liftRenB ρ bound) body)
  | [], _ => rfl
  | _ :: bound, body => rename_abstractB ρ bound (.lam body)

theorem subst_abstractB {Srt : Type} {k k' : Nat} {Γ Δ : List Srt}
    (σ : Sub Head (k + Γ.length) (k' + Δ.length)) :
    ∀ (bound : List Srt) (body : Tm Head (k + (bound ++ Γ).length)),
      subst σ (abstractB (Γ := Γ) bound body) =
        abstractB (Γ := Δ) bound (subst (liftSubB σ bound) body)
  | [], _ => rfl
  | _ :: bound, body => subst_abstractB σ bound (.lam body)

theorem subst_abstractN {k n : Nat} (σ : Sub Head k n) :
    ∀ (p : Nat) (body : Tm Head (k + p)),
      subst σ (abstractN p body) = abstractN p (subst (liftN σ p) body)
  | 0, _ => rfl
  | p + 1, body => subst_abstractN σ p (.lam body)

theorem liftN_inner {k n : Nat} (σ : Sub Head k n) :
    ∀ {p : Nat} (j : Fin p), liftN σ p (inner j) = .var (inner j)
  | 0, j => j.elim0
  | p + 1, j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · show rename wk (liftN σ p (inner j)) = .var (inner j).succ
        rw [liftN_inner σ j]
        rfl

theorem liftN_outer {k n : Nat} (σ : Sub Head k n) :
    ∀ {p : Nat} (i : Fin k), liftN σ p (outer i) = subst (fun i' => .var (outer i')) (σ i)
  | 0, i => (subst_ids (σ i)).symm
  | p + 1, i => by
      show rename wk (liftN σ p (outer i)) = _
      rw [liftN_outer σ i, rename_subst]
      rfl

/-! ## Conversion through spines and abstractions -/

section Conversion

variable {headEq : Head → Head → Prop} {root : RootComputation Head}

theorem conv_spine {n : Nat} {f f' : Tm Head n} (head : Conv headEq f f' root) :
    ∀ {p : Nat} {w w' : Sub Head p n}, (∀ j, Conv headEq (w j) (w' j) root) →
      Conv headEq (spine f w) (spine f' w') root
  | 0, _, _, _ => head
  | _ + 1, _, _, arguments =>
      Conv.congApp (conv_spine head (fun j => arguments j.succ)) (arguments 0)

theorem conv_applyVec {n : Nat} :
    ∀ {p : Nat} {f f' : Tm Head n} {w w' : Sub Head p n}, Conv headEq f f' root →
      (∀ j, Conv headEq (w j) (w' j) root) → Conv headEq (applyVec f w) (applyVec f' w') root
  | 0, _, _, _, _, head, _ => head
  | _ + 1, f, f', w, w', head, arguments =>
      conv_applyVec (f := .app f (w 0)) (f' := .app f' (w' 0)) (w := fun j => w j.succ)
        (w' := fun j => w' j.succ) (Conv.congApp head (arguments 0)) (fun j => arguments j.succ)

theorem conv_abstractB {Srt : Type} {k : Nat} {Γ : List Srt} :
    ∀ (bound : List Srt) {body body' : Tm Head (k + (bound ++ Γ).length)},
      Conv headEq body body' root →
        Conv headEq (abstractB (Γ := Γ) bound body) (abstractB (Γ := Γ) bound body') root
  | [], _, _, same => same
  | _ :: bound, _, _, same => conv_abstractB bound (Conv.congLam same)

theorem conv_abstractN {k : Nat} :
    ∀ (p : Nat) {body body' : Tm Head (k + p)}, Conv headEq body body' root →
      Conv headEq (abstractN p body) (abstractN p body') root
  | 0, _, _, same => same
  | p + 1, _, _, same => conv_abstractN p (Conv.congLam same)

/-- A pure beta or projection step is a step of every rule package. -/
theorem stepCore_of_beta {n : Nat} {a b : Tm Head n}
    (step : StepCore (RootComputation.empty : RootComputation Head) (fun _ _ => False) a b) :
    StepCore root headEq a b := by
  induction step with
  | betaPi body argument => exact .betaPi body argument
  | betaSigmaFst first second => exact .betaSigmaFst first second
  | betaSigmaSnd first second => exact .betaSigmaSnd first second
  | head impossible => cases impossible
  | root impossible => cases impossible
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

theorem conv_of_beta {n : Nat} {a b : Tm Head n}
    (steps : TelescopeAbstraction.BetaSteps a b) : Conv headEq a b root := by
  induction steps with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ (stepCore_of_beta step))

end Conversion

/-- **Beta on spines.** Applying a closed abstraction of `p` positions to `p` arguments computes,
by beta steps only, to the body with the arguments substituted. -/
theorem spine_beta {k n : Nat} (τ : Sub Head k n) :
    ∀ (p : Nat) (body : Tm Head (k + p)) (w : Sub Head p n),
      TelescopeAbstraction.BetaSteps (spine (subst τ (abstractN p body)) w)
        (subst (appendSub w τ) body)
  | 0, _, _ => Relation.ReflTransGen.refl
  | p + 1, body, w => by
      have earlier := spine_beta τ p (.lam body) (fun j => w j.succ)
      have underApplication := earlier.lift (fun function : Tm Head n => Tm.app function (w 0))
        (fun _ _ step => StepCore.congAppFun step)
      refine Relation.ReflTransGen.tail underApplication ?_
      have reduce := StepCore.betaPi (root := (RootComputation.empty : RootComputation Head))
        (headEq := fun _ _ => False) (subst (liftSub (appendSub (fun j => w j.succ) τ)) body) (w 0)
      have target : inst0 (w 0) (subst (liftSub (appendSub (fun j => w j.succ) τ)) body) =
          subst (appendSub w τ) body :=
        (subst_consSub (w 0) (appendSub (fun j => w j.succ) τ) body).symm
      rw [target] at reduce
      exact reduce

/-! ## The translation -/

/-- The source signature with the metavariables of the list frame `M` as operators. -/
abbrev Sig (S : Binding.Signature) (M : List (Binding.MetaArity S)) : Binding.Signature :=
  Binding.ContextualFamily.signature S M.get

section Encoding

variable (names : BindingSignatureEmbedding.Names S) (M : List (Binding.MetaArity S))

mutual

/-- **The translation of a second-order term** at the list frame `M`. -/
def encode : {Γ : Binding.Ctx S} → {s : S.Srt} → Binding.Term (Sig S M) Γ s →
    Tm Head (M.length + Γ.length)
  | _, _, .var v => .var (inner (vIdx v))
  | _, _, .op (.inl o) args => applyVec (.const (names.operator o)) (encodeArgs args)
  | _, _, .op (.inr (.mk i)) args =>
      spine (.var (outer i))
        (fun j : Fin (M.get i).1.length => encodeArgs args (Fin.cast (by simp) j))

/-- The translated arguments of one operator, each closed over its own binders. -/
def encodeArgs : {as : List (List S.Srt × S.Srt)} → {Γ : Binding.Ctx S} →
    Binding.Args (Sig S M) as Γ → Sub Head as.length (M.length + Γ.length)
  | _, _, .nil => fun j => j.elim0
  | _, _, .cons (bs := bound) body rest =>
      consSub (abstractB bound (encode body)) (encodeArgs rest)

end

/-- The arguments of a metavariable occurrence are read positionally. -/
theorem encodeArgs_argsToSub : ∀ (P : List S.Srt) {Γ : Binding.Ctx S}
    (args : Binding.Args (Sig S M) (P.map (fun sort => ([], sort))) Γ) {s : S.Srt}
    (v : Binding.Var P s) (h : P.length = (P.map (fun sort => ([], sort))).length),
    encodeArgs (Head := Head) names M args (Fin.cast h (vIdx v)) =
      encode names M (Binding.argsToSub args s v)
  | [], _, _, _, v, _ => nomatch v
  | _ :: _, _, .cons _ _, _, .zero, _ => rfl
  | _ :: P, _, .cons _ rest, _, .succ v, _ => encodeArgs_argsToSub P rest v (by simp)

/-! ## Renaming -/

/-- A scope renaming that tracks an object renaming and fixes every metavariable. -/
def RenGood {Γ Δ : Binding.Ctx S} (ρ : Binding.Ren (Sig S M) Γ Δ)
    (ρ' : Ren (M.length + Γ.length) (M.length + Δ.length)) : Prop :=
  (∀ (s : S.Srt) (v : Binding.Var Γ s),
      ρ' (inner (vIdx v)) = inner (vIdx (ρ s v))) ∧
    ∀ i : Fin M.length, ρ' (outer i) = outer i

theorem renGood_lift {Γ Δ : Binding.Ctx S} {ρ : Binding.Ren (Sig S M) Γ Δ}
    {ρ' : Ren (M.length + Γ.length) (M.length + Δ.length)} (good : RenGood M ρ ρ') :
    ∀ bound : List S.Srt, RenGood M (Binding.liftRen ρ bound) (liftRenB ρ' bound)
  | [] => good
  | _ :: bound => by
      have ih := renGood_lift good bound
      refine ⟨fun s v => ?_, fun i => congrArg Fin.succ (ih.2 i)⟩
      cases v with
      | zero => rfl
      | succ w => exact congrArg Fin.succ (ih.1 s w)

theorem renGood_weaken {Γ : Binding.Ctx S} (b : S.Srt) :
    RenGood M (Γ := Γ) (Δ := b :: Γ) (fun _ v => .succ v) wk :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

mutual

/-- **Renaming commutes with the translation.** -/
theorem encode_rename : ∀ {Γ Δ : Binding.Ctx S} {s : S.Srt}
    (t : Binding.Term (Sig S M) Γ s) (ρ : Binding.Ren (Sig S M) Γ Δ)
    (ρ' : Ren (M.length + Γ.length) (M.length + Δ.length)), RenGood M ρ ρ' →
      encode (Head := Head) names M (Binding.rename ρ t) = rename ρ' (encode names M t)
  | _, _, _, .var v, _, _, good => congrArg Tm.var (good.1 _ v).symm
  | _, _, _, .op (.inl o) args, ρ, ρ', good => by
      show applyVec (.const (names.operator o)) (encodeArgs names M (Binding.renameArgs ρ args)) =
        rename ρ' (applyVec (.const (names.operator o)) (encodeArgs names M args))
      rw [rename_applyVec]
      exact congrArg (applyVec (.const (names.operator o)))
        (funext fun j => encodeArgs_rename args ρ ρ' good j)
  | _, _, _, .op (.inr (.mk i)) args, ρ, ρ', good => by
      have castLength : (M.get i).1.length =
          ((M.get i).1.map (fun sort => (([] : List S.Srt), sort))).length := by simp
      show spine (.var (outer i))
          (fun j => encodeArgs names M (Binding.renameArgs ρ args) (Fin.cast castLength j)) =
        rename ρ' (spine (.var (outer i)) (fun j => encodeArgs names M args (Fin.cast castLength j)))
      rw [rename_spine]
      show _ = spine (.var (ρ' (outer i))) _
      rw [good.2 i]
      exact congrArg (spine (.var (outer i)))
        (funext fun j => encodeArgs_rename args ρ ρ' good (Fin.cast castLength j))

theorem encodeArgs_rename : ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ : Binding.Ctx S}
    (args : Binding.Args (Sig S M) as Γ) (ρ : Binding.Ren (Sig S M) Γ Δ)
    (ρ' : Ren (M.length + Γ.length) (M.length + Δ.length)), RenGood M ρ ρ' →
      ∀ j, encodeArgs (Head := Head) names M (Binding.renameArgs ρ args) j =
        rename ρ' (encodeArgs names M args j)
  | _, _, _, .nil, _, _, _, j => j.elim0
  | _, _, _, .cons (bs := bound) body rest, ρ, ρ', good, j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · show abstractB bound (encode names M (Binding.rename (Binding.liftRen ρ bound) body)) =
          rename ρ' (abstractB bound (encode names M body))
        rw [rename_abstractB, encode_rename body _ (liftRenB ρ' bound) (renGood_lift M good bound)]
      · exact encodeArgs_rename rest ρ ρ' good j

end

/-! ## Object substitution -/

/-- A scope substitution `σ'` that agrees with first substituting `θ` and then `σ`. -/
def SubGood {Γ Δ Ξ : Binding.Ctx S} {k : Nat} (θ : Binding.Sub (Sig S M) Γ Δ)
    (σ : Sub Head (M.length + Δ.length) (k + Ξ.length))
    (σ' : Sub Head (M.length + Γ.length) (k + Ξ.length)) : Prop :=
  (∀ (s : S.Srt) (v : Binding.Var Γ s),
      σ' (inner (vIdx v)) = subst σ (encode names M (θ s v))) ∧
    ∀ i : Fin M.length, σ' (outer i) = σ (outer i)

theorem subGood_lift {Γ Δ Ξ : Binding.Ctx S} {k : Nat} {θ : Binding.Sub (Sig S M) Γ Δ}
    {σ : Sub Head (M.length + Δ.length) (k + Ξ.length)}
    {σ' : Sub Head (M.length + Γ.length) (k + Ξ.length)} (good : SubGood names M θ σ σ') :
    ∀ bound : List S.Srt,
      SubGood names M (Binding.liftSub θ bound) (liftSubB σ bound) (liftSubB σ' bound)
  | [] => good
  | b :: bound => by
      have ih := subGood_lift good bound
      refine ⟨fun s v => ?_, fun i => ?_⟩
      · cases v with
        | zero => rfl
        | succ w =>
            have weakened :
                encode names M (Binding.weaken (S := Sig S M) (t := b) (Binding.liftSub θ bound s w)) =
                rename wk (encode (Head := Head) names M (Binding.liftSub θ bound s w)) :=
              encode_rename names M _ (fun _ v => .succ v) wk (renGood_weaken M b)
            show rename wk (liftSubB σ' bound (inner (vIdx w))) =
              subst (liftSub (liftSubB σ bound))
                (encode names M (Binding.weaken (S := Sig S M) (t := b) (Binding.liftSub θ bound s w)))
            rw [ih.1 s w, weakened, subst_rename, rename_subst]
            rfl
      · show rename wk (liftSubB σ' bound (outer i)) = rename wk (liftSubB σ bound (outer i))
        rw [ih.2 i]

mutual

/-- **Object substitution commutes with the translation.** -/
theorem encode_bind : ∀ {Γ Δ Ξ : Binding.Ctx S} {s : S.Srt} {k : Nat}
    (t : Binding.Term (Sig S M) Γ s) (θ : Binding.Sub (Sig S M) Γ Δ)
    (σ : Sub Head (M.length + Δ.length) (k + Ξ.length))
    (σ' : Sub Head (M.length + Γ.length) (k + Ξ.length)), SubGood names M θ σ σ' →
      subst σ (encode names M (Binding.bind θ t)) = subst σ' (encode names M t)
  | _, _, _, _, _, .var v, _, _, _, good => (good.1 _ v).symm
  | _, _, _, _, _, .op (.inl o) args, θ, σ, σ', good => by
      show subst σ (applyVec (.const (names.operator o))
          (encodeArgs names M (Binding.bindArgs θ args))) =
        subst σ' (applyVec (.const (names.operator o)) (encodeArgs names M args))
      rw [subst_applyVec, subst_applyVec]
      exact congrArg (applyVec (.const (names.operator o)))
        (funext fun j => encodeArgs_bind args θ σ σ' good j)
  | _, _, _, _, _, .op (.inr (.mk i)) args, θ, σ, σ', good => by
      have castLength : (M.get i).1.length =
          ((M.get i).1.map (fun sort => (([] : List S.Srt), sort))).length := by simp
      show subst σ (spine (.var (outer i))
          (fun j => encodeArgs names M (Binding.bindArgs θ args) (Fin.cast castLength j))) =
        subst σ' (spine (.var (outer i)) (fun j => encodeArgs names M args (Fin.cast castLength j)))
      rw [subst_spine, subst_spine]
      show spine (σ (outer i)) _ = spine (σ' (outer i)) _
      rw [good.2 i]
      exact congrArg (spine (σ (outer i)))
        (funext fun j => encodeArgs_bind args θ σ σ' good (Fin.cast castLength j))

theorem encodeArgs_bind : ∀ {as : List (List S.Srt × S.Srt)} {Γ Δ Ξ : Binding.Ctx S} {k : Nat}
    (args : Binding.Args (Sig S M) as Γ) (θ : Binding.Sub (Sig S M) Γ Δ)
    (σ : Sub Head (M.length + Δ.length) (k + Ξ.length))
    (σ' : Sub Head (M.length + Γ.length) (k + Ξ.length)), SubGood names M θ σ σ' →
      ∀ j, subst σ (encodeArgs names M (Binding.bindArgs θ args) j) =
        subst σ' (encodeArgs names M args j)
  | _, _, _, _, _, .nil, _, _, _, _, j => j.elim0
  | _, _, _, _, _, .cons (bs := bound) body rest, θ, σ, σ', good, j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · show subst σ (abstractB bound (encode names M (Binding.bind (Binding.liftSub θ bound) body))) =
          subst σ' (abstractB bound (encode names M body))
        rw [subst_abstractB, subst_abstractB,
          encode_bind body _ _ _ (subGood_lift names M good bound)]
      · exact encodeArgs_bind rest θ σ σ' good j

end

/-! ## Contextual instantiation is beta on spines -/

variable (N : List (Binding.MetaArity S))
  (σa : Binding.ContextualFamily.Assignment (S := S) M.get N.get)

/-- **The code of a contextual assignment**: each metavariable becomes the closed abstraction of
the translation of its image, over the image's parameters. -/
def homCode : Sub Head M.length N.length :=
  fun i => abstractN (M.get i).1.length (encode names N (σa i))

/-- `σ` substitutes the codes of `σa` for the metavariables and agrees with `σ'` on the object
positions. -/
def InstGood {Γ Ξ : Binding.Ctx S} {k : Nat} (σ : Sub Head (M.length + Γ.length) (k + Ξ.length))
    (σ' : Sub Head (N.length + Γ.length) (k + Ξ.length)) : Prop :=
  (∀ j : Fin Γ.length, σ (inner j) = σ' (inner j)) ∧
    ∀ i : Fin M.length,
      σ (outer i) = subst (fun i' => σ' (outer i')) (homCode (Head := Head) names M N σa i)

theorem instGood_lift {Γ Ξ : Binding.Ctx S} {k : Nat}
    {σ : Sub Head (M.length + Γ.length) (k + Ξ.length)}
    {σ' : Sub Head (N.length + Γ.length) (k + Ξ.length)} (good : InstGood names M N σa σ σ') :
    ∀ bound : List S.Srt, InstGood names M N σa (liftSubB σ bound) (liftSubB σ' bound)
  | [] => good
  | _ :: bound => by
      have ih := instGood_lift good bound
      refine ⟨fun j => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · show rename wk (liftSubB σ bound (inner j)) = rename wk (liftSubB σ' bound (inner j))
          rw [ih.1 j]
      · show rename wk (liftSubB σ bound (outer i)) = _
        rw [ih.2 i, rename_subst]
        rfl

theorem instGood_liftN (Γ : Binding.Ctx S) :
    InstGood (Head := Head) names M N σa (Γ := Γ) (Ξ := Γ) (k := N.length)
      (liftN (homCode names M N σa) Γ.length) ids :=
  ⟨fun j => liftN_inner _ j, fun i => liftN_outer _ i⟩

section Beta

variable {headEq : Head → Head → Prop} {root : RootComputation Head}

mutual

/-- **Contextual instantiation is beta on spines**, for every substitution of the codes. -/
theorem instantiate_beta : ∀ {Γ Ξ : Binding.Ctx S} {s : S.Srt} {k : Nat}
    (t : Binding.Term (Sig S M) Γ s) (σ : Sub Head (M.length + Γ.length) (k + Ξ.length))
    (σ' : Sub Head (N.length + Γ.length) (k + Ξ.length)), InstGood names M N σa σ σ' →
      Conv headEq (subst σ (encode names M t))
        (subst σ' (encode names N (Binding.ContextualFamily.instantiate σa t))) root
  | _, _, _, _, .var v, σ, σ', good =>
      (congrArg (fun t => Conv headEq t (σ' (inner (vIdx v))) root)
        (good.1 (vIdx v))).mpr (.refl _)
  | _, _, _, _, .op (.inl o) args, σ, σ', good => by
      show Conv headEq
        (subst σ (applyVec (.const (names.operator o)) (encodeArgs names M args)))
        (subst σ' (applyVec (.const (names.operator o))
          (encodeArgs names N (Binding.ContextualFamily.instantiateArgs σa args)))) root
      rw [subst_applyVec, subst_applyVec]
      exact conv_applyVec (.refl _) (fun j => instantiateArgs_beta args σ σ' good j)
  | Γ, _, _, _, .op (.inr (.mk i)) args, σ, σ', good => by
      have castLength : (M.get i).1.length =
          ((M.get i).1.map (fun sort => (([] : List S.Srt), sort))).length := by simp
      let instantiated : Binding.Args (Sig S N) ((M.get i).1.map (fun sort => ([], sort))) Γ :=
        Binding.ContextualFamily.instantiateArgs σa args
      let w : Sub Head (M.get i).1.length _ :=
        fun j => subst σ' (encodeArgs names N instantiated (Fin.cast castLength j))
      have arguments : ∀ j, Conv headEq (subst σ (encodeArgs names M args (Fin.cast castLength j)))
          (w j) root := fun j => instantiateArgs_beta args σ σ' good (Fin.cast castLength j)
      have headConv : Conv headEq (subst σ (.var (outer i)))
          (subst (fun i' => σ' (outer i')) (abstractN (M.get i).1.length (encode names N (σa i))))
          root :=
        (congrArg (fun t => Conv headEq t
          (subst (fun i' => σ' (outer i')) (abstractN (M.get i).1.length (encode names N (σa i))))
          root) (good.2 i)).mpr (.refl _)
      have beta := spine_beta (fun i' => σ' (outer i')) (M.get i).1.length
        (encode names N (σa i)) w
      have bound : SubGood names N (Binding.argsToSub instantiated) σ'
          (appendSub w (fun i' => σ' (outer i'))) := by
        refine ⟨fun s v => ?_, fun i' => appendSub_outer _ _ i'⟩
        rw [appendSub_inner]
        show subst σ' (encodeArgs names N instantiated (Fin.cast castLength (vIdx v))) = _
        rw [encodeArgs_argsToSub names N (M.get i).1 instantiated v castLength]
      have bindLaw := encode_bind names N (σa i) (Binding.argsToSub instantiated) σ' _ bound
      show Conv headEq
        (subst σ (spine (.var (outer i)) (fun j => encodeArgs names M args (Fin.cast castLength j))))
        (subst σ' (encode names N (Binding.bind (Binding.argsToSub instantiated) (σa i)))) root
      rw [subst_spine, bindLaw]
      exact .trans _ _ _ (conv_spine headConv arguments) (conv_of_beta beta)

theorem instantiateArgs_beta : ∀ {as : List (List S.Srt × S.Srt)} {Γ Ξ : Binding.Ctx S} {k : Nat}
    (args : Binding.Args (Sig S M) as Γ) (σ : Sub Head (M.length + Γ.length) (k + Ξ.length))
    (σ' : Sub Head (N.length + Γ.length) (k + Ξ.length)), InstGood names M N σa σ σ' →
      ∀ j, Conv headEq (subst σ (encodeArgs names M args j))
        (subst σ' (encodeArgs names N (Binding.ContextualFamily.instantiateArgs σa args) j)) root
  | _, _, _, _, .nil, _, _, _, j => j.elim0
  | _, _, _, _, .cons (bs := bound) body rest, σ, σ', good, j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · show Conv headEq (subst σ (abstractB bound (encode names M body)))
          (subst σ' (abstractB bound
            (encode names N (Binding.ContextualFamily.instantiate σa body)))) root
        rw [subst_abstractB, subst_abstractB]
        exact conv_abstractB bound
          (instantiate_beta body _ _ (instGood_lift names M N σa good bound))
      · exact instantiateArgs_beta rest σ σ' good j

end

/-- **The action law**: substituting the code of `σa` into the translation of a term converts,
by beta steps, to the translation of its instantiation. -/
theorem action_beta {Γ : Binding.Ctx S} {s : S.Srt} (t : Binding.Term (Sig S M) Γ s) :
    Conv headEq (subst (liftN (homCode names M N σa) Γ.length) (encode names M t))
      (encode names N (Binding.ContextualFamily.instantiate σa t)) root := by
  have law := instantiate_beta names M N σa (headEq := headEq) (root := root) t _ ids
    (instGood_liftN names M N σa Γ)
  rwa [subst_ids] at law

/-- The action law on closed bodies. -/
theorem action_beta_closed {Γ : Binding.Ctx S} {s : S.Srt} (t : Binding.Term (Sig S M) Γ s) :
    Conv headEq (subst (homCode names M N σa) (abstractN Γ.length (encode names M t)))
      (abstractN Γ.length (encode names N (Binding.ContextualFamily.instantiate σa t))) root := by
  rw [subst_abstractN]
  exact conv_abstractN Γ.length (action_beta names M N σa t)

end Beta

end Encoding

end Translation

#print axioms Translation.spine_beta
#print axioms Translation.encode_rename
#print axioms Translation.encode_bind
#print axioms Translation.instantiate_beta
#print axioms Translation.action_beta
#print axioms Translation.action_beta_closed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
