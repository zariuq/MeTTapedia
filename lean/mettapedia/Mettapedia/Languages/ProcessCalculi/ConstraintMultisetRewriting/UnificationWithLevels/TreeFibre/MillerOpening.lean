import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralForcing

/-!
# Miller patterns in the tree's fibre: binders, spines of locals, opening and β

An equation of a Miller pattern lives under bound locals `ȳ`, each declared at a universe: it is an equation at the
family `Π (y₁ : U_{q₁}) … (y_k : U_{q_k}). U_d`, between abstractions over the locals. An unknown applied to some of
the locals, `λ ȳ. F y_{i₁} … y_{i_m}`, is a **Miller side**.

The binders are read **outermost first**. The arity under a list of binders is defined by recursion along the list
(`arity n (q :: qs) = arity (n + 1) qs`), so that every construction below is by structural recursion with no cast of
arities.

* `ctx Γ qs`: the telescope `Γ` extended by the binders; `lams qs b`: one abstraction per binder; `apps h ts`: an
  application spine; `shift qs`: the weakening past the binders; `loc qs j`: the `j`-th local.
* `opened qs s`: a function applied to the fresh locals in order, `s y₁ … y_k`. Its abstraction is the tree's
  η-expansion (`lams_opened`), so every function of a family is equal to the abstraction of its opening
  (`eta_opened`).
* `spineRen ps ρ img`: the renaming that sends the binders of `ps` to the variables `img j` and the outer variables
  through `ρ`; `subsAt qs σ img`: the same for a substitution.
* **Opening** (`lams_equal_iff`): two abstractions are equal at the family exactly when their bodies are equal at
  `U_d` under the binders.
* **β along a spine of variables** (`beta_apps`): an abstraction over `ps`, applied to variables of the right
  universes, is equal to its body renamed by `spineRen`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Syntax under binders -/

section Syntax

/-- The arity under a list of binders. -/
def arity : Nat → List Head → Nat
  | n, [] => n
  | n, _ :: qs => arity (n + 1) qs

theorem arity_eq : ∀ (n : Nat) (qs : List Head), arity n qs = n + qs.length
  | _, [] => rfl
  | n, _ :: qs => by
      show arity (n + 1) qs = n + (qs.length + 1)
      rw [arity_eq (n + 1) qs]
      omega

/-- A telescope extended by universe binders, the outermost first. -/
def ctx : {n : Nat} → Ctx Head n → (qs : List Head) → Ctx Head (arity n qs)
  | _, Γ, [] => Γ
  | _, Γ, q :: qs => ctx (.snoc Γ (.head q)) qs

/-- One abstraction per binder. -/
def lams : {n : Nat} → (qs : List Head) → Tm Head (arity n qs) → Tm Head n
  | _, [], b => b
  | _, _ :: qs, b => .lam (lams qs b)

/-- An application spine, the first argument outermost: `apps h [t₁, …, t_k] = h t₁ … t_k`. -/
def apps {n : Nat} : Tm Head n → List (Tm Head n) → Tm Head n
  | h, [] => h
  | h, t :: ts => apps (.app h t) ts

/-- The weakening past the binders. -/
def shift : {n : Nat} → (qs : List Head) → Ren n (arity n qs)
  | _, [] => fun i => i
  | _, _ :: qs => fun i => shift qs (Fin.succ i)

/-- The local bound by the `j`-th binder. -/
def loc : {n : Nat} → (qs : List Head) → Fin qs.length → Fin (arity n qs)
  | _, [], j => j.elim0
  | _, _ :: qs, j => Fin.cases (motive := fun _ => Fin _) (shift qs 0) (fun j' => loc qs j') j

/-- A function applied to the fresh locals in order, `s y₁ … y_k`, read under the binders. -/
def opened : {n : Nat} → (qs : List Head) → Tm Head n → Tm Head (arity n qs)
  | _, [], s => s
  | _, _ :: qs, s => opened qs (.app (Presentation.rename wk s) (.var 0))

/-- A substitution lifted under the binders. -/
def liftSubs : {n m : Nat} → (qs : List Head) → Sub Head n m → Sub Head (arity n qs) (arity m qs)
  | _, _, [], σ => σ
  | _, _, _ :: qs, σ => liftSubs qs (liftSub σ)

/-- A renaming lifted under the binders. -/
def liftRens : {n m : Nat} → (qs : List Head) → Ren n m → Ren (arity n qs) (arity m qs)
  | _, _, [], ρ => ρ
  | _, _, _ :: qs, ρ => liftRens qs (liftRen ρ)

/-- The renaming sending the `j`-th binder of `ps` to `img j` and the outer variables through `ρ`. -/
def spineRen : {n m : Nat} → (ps : List Head) → Ren n m → (Fin ps.length → Fin m) → Ren (arity n ps) m
  | _, _, [], ρ, _ => ρ
  | _, m, _ :: ps, ρ, img => spineRen ps (Fin.cases (motive := fun _ => Fin m) (img 0) ρ) (fun j => img j.succ)

/-- The substitution sending the `j`-th binder of `qs` to `img j` and the outer variables through `σ`. -/
def subsAt : {n m : Nat} → (qs : List Head) → Sub Head n m → (Fin qs.length → Tm Head m) → Sub Head (arity n qs) m
  | _, _, [], σ, _ => σ
  | _, m, _ :: qs, σ, img => subsAt qs (Fin.cases (motive := fun _ => Tm Head m) (img 0) σ) (fun j => img j.succ)

/-- The spine of the locals of `ps` read through `img`: `[img 0, …, img (k - 1)]` as variables. -/
def spineArgs {m : Nat} (ps : List Head) (img : Fin ps.length → Fin m) : List (Tm Head m) :=
  (List.finRange ps.length).map fun j => .var (img j)

@[simp] theorem loc_zero {n : Nat} (q : Head) (qs : List Head) :
    loc (n := n) (q :: qs) ⟨0, Nat.succ_pos _⟩ = shift qs 0 := rfl

@[simp] theorem loc_succ {n : Nat} (q : Head) (qs : List Head) (j : Fin qs.length) :
    loc (n := n) (q :: qs) j.succ = loc qs j := rfl

theorem spineArgs_cons {m : Nat} (p : Head) (ps : List Head) (img : Fin (p :: ps).length → Fin m) :
    spineArgs (p :: ps) img = .var (img 0) :: spineArgs ps (fun j => img j.succ) := by
  unfold spineArgs
  show List.map _ (List.finRange (ps.length + 1)) = _
  rw [List.finRange_succ, List.map_cons, List.map_map]
  rfl

theorem subst_lams : ∀ {n m : Nat} (qs : List Head) (σ : Sub Head n m) (b : Tm Head (arity n qs)),
    Presentation.subst σ (lams qs b) = lams qs (Presentation.subst (liftSubs qs σ) b)
  | _, _, [], _, _ => rfl
  | _, _, _ :: qs, σ, b => by
      show Tm.lam (Presentation.subst (liftSub σ) (lams qs b)) =
        Tm.lam (lams qs (Presentation.subst (liftSubs qs (liftSub σ)) b))
      rw [subst_lams qs (liftSub σ) b]

theorem rename_lams : ∀ {n m : Nat} (qs : List Head) (ρ : Ren n m) (b : Tm Head (arity n qs)),
    Presentation.rename ρ (lams qs b) = lams qs (Presentation.rename (liftRens qs ρ) b)
  | _, _, [], _, _ => rfl
  | _, _, _ :: qs, ρ, b => by
      show Tm.lam (Presentation.rename (liftRen ρ) (lams qs b)) =
        Tm.lam (lams qs (Presentation.rename (liftRens qs (liftRen ρ)) b))
      rw [rename_lams qs (liftRen ρ) b]

theorem subst_apps {n m : Nat} (σ : Sub Head n m) : ∀ (h : Tm Head n) (ts : List (Tm Head n)),
    Presentation.subst σ (apps h ts) = apps (Presentation.subst σ h) (ts.map (Presentation.subst σ))
  | _, [] => rfl
  | h, t :: ts => by
      show Presentation.subst σ (apps (.app h t) ts) = _
      rw [subst_apps σ (.app h t) ts]
      rfl

theorem rename_apps {n m : Nat} (ρ : Ren n m) : ∀ (h : Tm Head n) (ts : List (Tm Head n)),
    Presentation.rename ρ (apps h ts) = apps (Presentation.rename ρ h) (ts.map (Presentation.rename ρ))
  | _, [] => rfl
  | h, t :: ts => by
      show Presentation.rename ρ (apps (.app h t) ts) = _
      rw [rename_apps ρ (.app h t) ts]
      rfl

theorem liftSubs_shift : ∀ {n m : Nat} (qs : List Head) (σ : Sub Head n m) (v : Fin n),
    liftSubs qs σ (shift qs v) = Presentation.rename (shift qs) (σ v)
  | _, _, [], σ, v => (rename_id (σ v)).symm
  | _, _, _ :: qs, σ, v => by
      show liftSubs qs (liftSub σ) (shift qs (Fin.succ v)) = _
      rw [liftSubs_shift qs (liftSub σ) (Fin.succ v), liftSub_succ, rename_comp]
      rfl

theorem liftSubs_loc : ∀ {n m : Nat} (qs : List Head) (σ : Sub Head n m) (j : Fin qs.length),
    liftSubs qs σ (loc qs j) = .var (loc qs j)
  | _, _, [], _, j => j.elim0
  | _, _, _ :: qs, σ, j => by
      cases j using Fin.cases with
      | zero =>
          show liftSubs qs (liftSub σ) (shift qs 0) = .var (shift qs 0)
          rw [liftSubs_shift qs (liftSub σ) 0, liftSub_zero]
          rfl
      | succ j => exact liftSubs_loc qs (liftSub σ) j

theorem liftRens_shift : ∀ {n m : Nat} (qs : List Head) (ρ : Ren n m) (v : Fin n),
    liftRens qs ρ (shift qs v) = shift qs (ρ v)
  | _, _, [], _, _ => rfl
  | _, _, _ :: qs, ρ, v => liftRens_shift qs (liftRen ρ) (Fin.succ v)

theorem liftRens_loc : ∀ {n m : Nat} (qs : List Head) (ρ : Ren n m) (j : Fin qs.length),
    liftRens qs ρ (loc qs j) = loc qs j
  | _, _, [], _, j => j.elim0
  | _, _, _ :: qs, ρ, j => by
      cases j using Fin.cases with
      | zero => exact liftRens_shift qs (liftRen ρ) 0
      | succ j => exact liftRens_loc qs (liftRen ρ) j

theorem spineRen_shift : ∀ {n m : Nat} (ps : List Head) (ρ : Ren n m) (img : Fin ps.length → Fin m) (v : Fin n),
    spineRen ps ρ img (shift ps v) = ρ v
  | _, _, [], _, _, _ => rfl
  | _, _, _ :: ps, _, img, v => spineRen_shift ps _ (fun j => img j.succ) (Fin.succ v)

theorem spineRen_loc : ∀ {n m : Nat} (ps : List Head) (ρ : Ren n m) (img : Fin ps.length → Fin m)
    (j : Fin ps.length), spineRen ps ρ img (loc ps j) = img j
  | _, _, [], _, _, j => j.elim0
  | _, _, _ :: ps, ρ, img, j => by
      cases j using Fin.cases with
      | zero => exact spineRen_shift ps _ (fun j => img j.succ) 0
      | succ j => exact spineRen_loc ps _ (fun j => img j.succ) j

theorem subsAt_shift : ∀ {n m : Nat} (qs : List Head) (σ : Sub Head n m) (img : Fin qs.length → Tm Head m)
    (v : Fin n), subsAt qs σ img (shift qs v) = σ v
  | _, _, [], _, _, _ => rfl
  | _, _, _ :: qs, _, img, v => subsAt_shift qs _ (fun j => img j.succ) (Fin.succ v)

theorem subsAt_loc : ∀ {n m : Nat} (qs : List Head) (σ : Sub Head n m) (img : Fin qs.length → Tm Head m)
    (j : Fin qs.length), subsAt qs σ img (loc qs j) = img j
  | _, _, [], _, _, j => j.elim0
  | _, _, _ :: qs, σ, img, j => by
      cases j using Fin.cases with
      | zero => exact subsAt_shift qs _ (fun j => img j.succ) 0
      | succ j => exact subsAt_loc qs _ (fun j => img j.succ) j

/-- **Every variable under the binders is an outer variable or a local.** -/
theorem index_cases : ∀ {n : Nat} (qs : List Head) (i : Fin (arity n qs)),
    (∃ v, i = shift qs v) ∨ ∃ j, i = loc qs j
  | _, [], i => .inl ⟨i, rfl⟩
  | n, _ :: qs, i => by
      rcases index_cases (n := n + 1) qs i with ⟨v, rfl⟩ | ⟨j, rfl⟩
      · cases v using Fin.cases with
        | zero => exact .inr ⟨0, rfl⟩
        | succ v => exact .inl ⟨v, rfl⟩
      · exact .inr ⟨j.succ, rfl⟩

theorem shift_injective : ∀ {n : Nat} (qs : List Head), Function.Injective (shift (n := n) qs)
  | _, [] => fun _ _ same => same
  | _, _ :: qs => fun _ _ same => Fin.succ_injective _ (shift_injective qs same)

/-- A local is never an outer variable. -/
theorem loc_ne_shift : ∀ {n : Nat} (qs : List Head) (j : Fin qs.length) (v : Fin n), loc qs j ≠ shift qs v
  | _, [], j, _ => j.elim0
  | _, _ :: qs, j, v => by
      cases j using Fin.cases with
      | zero =>
          intro same
          exact Fin.succ_ne_zero v (shift_injective qs same).symm
      | succ j => exact loc_ne_shift qs j (Fin.succ v)

theorem loc_injective : ∀ {n : Nat} (qs : List Head), Function.Injective (loc (n := n) qs)
  | _, [] => fun j => j.elim0
  | _, _ :: qs => by
      intro first second same
      cases first using Fin.cases with
      | zero =>
          cases second using Fin.cases with
          | zero => rfl
          | succ second => exact absurd same.symm (loc_ne_shift qs second 0)
      | succ first =>
          cases second using Fin.cases with
          | zero => exact absurd same (loc_ne_shift qs first 0)
          | succ second => exact congrArg Fin.succ (loc_injective qs same)

/-- The opening is the function weakened past the binders, applied to the locals in order. -/
theorem opened_eq : ∀ {n : Nat} (qs : List Head) (s : Tm Head n),
    opened qs s = apps (Presentation.rename (shift qs) s) (spineArgs qs (loc qs))
  | _, [], s => (rename_id s).symm
  | _, q :: qs, s => by
      show opened qs (.app (Presentation.rename wk s) (.var 0)) = _
      rw [opened_eq qs, spineArgs_cons]
      show apps (.app (Presentation.rename (shift qs) (Presentation.rename wk s)) (.var (shift qs 0))) _ = _
      rw [rename_comp]
      rfl

end Syntax

/-! ## Lookups and typed maps -/

section Maps

theorem lookup_shift : ∀ {n : Nat} (Γ : Ctx Head n) (qs : List Head) (v : Fin n),
    Ctx.lookup (ctx Γ qs) (shift qs v) = Presentation.rename (shift qs) (Ctx.lookup Γ v)
  | _, _, [], _ => (rename_id _).symm
  | _, Γ, q :: qs, v => by
      show Ctx.lookup (ctx (.snoc Γ (.head q)) qs) (shift qs (Fin.succ v)) = _
      rw [lookup_shift (.snoc Γ (.head q)) qs (Fin.succ v), Ctx.lookup_snoc_succ, rename_comp]
      rfl

theorem lookup_loc : ∀ {n : Nat} (Γ : Ctx Head n) (qs : List Head) (j : Fin qs.length),
    Ctx.lookup (ctx Γ qs) (loc qs j) = .head (qs.get j)
  | _, _, [], j => j.elim0
  | _, Γ, q :: qs, j => by
      cases j using Fin.cases with
      | zero =>
          show Ctx.lookup (ctx (.snoc Γ (.head q)) qs) (shift qs 0) = .head q
          rw [lookup_shift (.snoc Γ (.head q)) qs 0, Ctx.lookup_snoc_zero]
          rfl
      | succ j => exact lookup_loc (.snoc Γ (.head q)) qs j

/-- **The renaming of a spine is a typed renaming** when the variables it reaches have the binders' universes. -/
theorem spineRen_ctxRen : ∀ {n m : Nat} {Γ : Ctx Head n} {Γ' : Ctx Head m} (ps : List Head) (ρ : Ren n m)
    (img : Fin ps.length → Fin m), CtxRen Γ Γ' ρ → (∀ j, Ctx.lookup Γ' (img j) = .head (ps.get j)) →
      CtxRen (ctx Γ ps) Γ' (spineRen ps ρ img)
  | _, _, _, _, [], _, _, compatible, _ => compatible
  | _, m, Γ, Γ', p :: ps, ρ, img, compatible, typed => by
      refine spineRen_ctxRen (Γ := .snoc Γ (.head p)) ps (Fin.cases (motive := fun _ => Fin m) (img 0) ρ)
        (fun j => img j.succ) ?_ (fun j => typed j.succ)
      intro index
      cases index using Fin.cases with
      | zero =>
          show Ctx.lookup Γ' (img 0) = Presentation.rename _ (Presentation.rename wk (.head p))
          rw [typed 0]
          rfl
      | succ prior =>
          show Ctx.lookup Γ' (ρ prior) = Presentation.rename _ (Presentation.rename wk (Ctx.lookup Γ prior))
          rw [compatible prior, rename_comp]
          rfl

/-- The weakening past the binders is a typed renaming. -/
theorem shift_ctxRen {n : Nat} (Γ : Ctx Head n) (qs : List Head) : CtxRen Γ (ctx Γ qs) (shift qs) :=
  fun v => lookup_shift Γ qs v

variable {S : Setting Head L}

/-- **The substitution of a spine is typed** when its images have the binders' universes. -/
theorem subsAt_substMor : ∀ {n m : Nat} {Γ : Ctx Head n} {Γ' : Ctx Head m} (qs : List Head) (σ : Sub Head n m)
    (img : Fin qs.length → Tm Head m), SubstMor S.R Γ Γ' σ →
      (∀ j, Typed S.R Γ' (img j) (.head (qs.get j))) → SubstMor S.R (ctx Γ qs) Γ' (subsAt qs σ img)
  | _, _, _, _, [], _, _, typed, _ => typed
  | _, m, Γ, Γ', q :: qs, σ, img, typed, imgs => by
      refine subsAt_substMor (Γ := .snoc Γ (.head q)) qs (Fin.cases (motive := fun _ => Tm Head m) (img 0) σ)
        (fun j => img j.succ) ?_ (fun j => imgs j.succ)
      intro index
      cases index using Fin.cases with
      | zero =>
          show Typed S.R Γ' (img 0) (Presentation.subst _ (Presentation.rename wk (.head q)))
          exact imgs 0
      | succ prior =>
          show Typed S.R Γ' (σ prior) (Presentation.subst _ (Presentation.rename wk (Ctx.lookup Γ prior)))
          rw [subst_rename]
          exact typed prior

end Maps

/-! ## Typing under binders -/

section Typing

variable {S : Setting Head L}

theorem ctx_formed : ∀ {n : Nat} {Γ : Ctx Head n} (qs : List Head), CtxFormed S.R Γ → AllUniverses S.R qs →
    CtxFormed S.R (ctx Γ qs)
  | _, _, [], formed, _ => formed
  | _, _, _ :: qs, formed, universes =>
      ctx_formed qs (formed.snoc (IsType.head_of_universe universes.head)) universes.tail

/-- **Abstraction at a family.** -/
theorem lams_typed : ∀ {n : Nat} {Γ : Ctx Head n} (qs : List Head) {d : Head} {b : Tm Head (arity n qs)},
    CtxFormed S.R Γ → AllUniverses S.R qs → S.R.isUniverse d →
      Typed S.R (ctx Γ qs) b (.head d) → Typed S.R Γ (lams qs b) (famCode qs d)
  | _, _, [], _, _, _, _, _, typed => typed
  | _, Γ, q :: qs, d, _, formed, universes, hd, typed => by
      have inner := lams_typed qs (formed.snoc (IsType.head_of_universe universes.head)) universes.tail hd typed
      obtain ⟨u, hu, tPi⟩ := famCode_isType (q :: qs) universes hd formed
      have tPi' : Typed S.R Γ (.pi (.head q) (famCode qs d)) (.head u) := tPi
      exact Derivable.lamIntro tPi' hu inner

/-- **Opening a function of a family.** -/
theorem opened_typed : ∀ {n : Nat} {Γ : Ctx Head n} (qs : List Head) {d : Head} {s : Tm Head n},
    Typed S.R Γ s (famCode qs d) → Typed S.R (ctx Γ qs) (opened qs s) (.head d)
  | _, _, [], _, _, typed => typed
  | _, Γ, q :: qs, d, s, typed => by
      apply opened_typed qs
      have weak := typed.rename (CtxRen.wk Γ (.head q))
      rw [famCode_rename] at weak
      have step := Derivable.appElim weak (var_head_typed (S := S) Γ q)
      simpa only [famCode_cons, inst0, famCode_subst] using step

/-- The abstraction of the opening is the tree's η-expansion. -/
theorem lams_opened : ∀ {n : Nat} (qs : List Head) (t : Tm Head n), lams qs (opened qs t) = etaExp qs.length t
  | _, [], _ => rfl
  | _, _ :: qs, t => by
      show Tm.lam (lams qs (opened qs (.app (Presentation.rename wk t) (.var 0)))) = etaExp (qs.length + 1) t
      rw [lams_opened qs]
      rfl

/-- **η at a family**: a function is the abstraction of its opening. -/
theorem eta_opened {n : Nat} {Γ : Ctx Head n} (qs : List Head) {c : Head} {t : Tm Head n} (formed : CtxFormed S.R Γ)
    (typed : Typed S.R Γ t (famCode qs c)) : Equal S.R Γ (lams qs (opened qs t)) t (famCode qs c) := by
  rw [lams_opened]
  exact etaExp_equal qs formed typed

/-- **Opening an equation of abstractions**: equal at the family exactly when the bodies are equal under the
binders. -/
theorem lams_equal_iff : ∀ {n : Nat} {Γ : Ctx Head n} (qs : List Head) {d : Head} {s t : Tm Head (arity n qs)},
    CtxFormed S.R Γ → AllUniverses S.R qs → S.R.isUniverse d →
      Typed S.R (ctx Γ qs) s (.head d) → Typed S.R (ctx Γ qs) t (.head d) →
      (Equal S.R Γ (lams qs s) (lams qs t) (famCode qs d) ↔ Equal S.R (ctx Γ qs) s t (.head d))
  | _, _, [], _, _, _, _, _, _, _, _ => Iff.rfl
  | _, Γ, q :: qs, d, s, t, formed, universes, hd, ts, tt => by
      have formed' : CtxFormed S.R (.snoc Γ (.head q)) := formed.snoc (IsType.head_of_universe universes.head)
      have ih := lams_equal_iff qs formed' universes.tail hd ts tt
      obtain ⟨u, hu, tPi⟩ := famCode_isType (q :: qs) universes hd formed
      have tPi' : Typed S.R Γ (.pi (.head q) (famCode qs d)) (.head u) := tPi
      have tS := lams_typed qs formed' universes.tail hd ts
      have tT := lams_typed qs formed' universes.tail hd tt
      constructor
      · intro equal
        apply ih.mp
        have weak := equal.rename (CtxRen.wk Γ (.head q))
        rw [famCode_rename] at weak
        have step := Derivable.appCong weak (Derivable.refl (var_head_typed (S := S) Γ q))
        have applied : Equal S.R (.snoc Γ (.head q)) (.app (Presentation.rename wk (lams (q :: qs) s)) (.var 0))
            (.app (Presentation.rename wk (lams (q :: qs) t)) (.var 0)) (famCode qs d) := by
          simpa only [famCode_cons, inst0, famCode_subst] using step
        exact ((beta_open tPi' hu tS).symm.trans applied).trans (beta_open tPi' hu tT)
      · intro equal
        exact Derivable.lamCong tPi' hu (ih.mpr equal)

/-- Congruence of a spine of variables. -/
theorem apps_congr : ∀ {m : Nat} {Γ' : Ctx Head m} (ps : List Head) {d : Head} {f f' : Tm Head m}
    (img : Fin ps.length → Fin m), (∀ j, Ctx.lookup Γ' (img j) = .head (ps.get j)) →
      Equal S.R Γ' f f' (famCode ps d) → Equal S.R Γ' (apps f (spineArgs ps img)) (apps f' (spineArgs ps img)) (.head d)
  | _, _, [], _, _, _, _, _, equal => equal
  | _, Γ', p :: ps, d, f, f', img, typed, equal => by
      rw [spineArgs_cons]
      apply apps_congr ps (fun j => img j.succ) (fun j => typed j.succ)
      have tv : Typed S.R Γ' (.var (img 0)) (.head p) := by
        have v := Derivable.var (R := S.R) (Γ := Γ') (img 0)
        rw [typed 0] at v
        exact v
      have step := Derivable.appCong (equal : Equal S.R Γ' f f' (.pi (.head p) (famCode ps d))) (Derivable.refl tv)
      simpa only [inst0, famCode_subst] using step

theorem inst0_rename_liftRen {n m : Nat} (x : Fin m) (ρ : Ren n m) (Z : Tm Head (n + 1)) :
    inst0 (.var x) (Presentation.rename (liftRen ρ) Z) =
      Presentation.rename (Fin.cases (motive := fun _ => Fin m) x ρ) Z := by
  rw [inst0, subst_rename, ← subst_renSub]
  apply subst_ext
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

/-- **β along a spine of variables.** -/
theorem beta_apps : ∀ {n m : Nat} {Γ : Ctx Head n} {Γ' : Ctx Head m} (ps : List Head) {d : Head}
    {B : Tm Head (arity n ps)} (ρ : Ren n m) (img : Fin ps.length → Fin m),
    CtxFormed S.R Γ → CtxFormed S.R Γ' → AllUniverses S.R ps → S.R.isUniverse d → CtxRen Γ Γ' ρ →
      (∀ j, Ctx.lookup Γ' (img j) = .head (ps.get j)) → Typed S.R (ctx Γ ps) B (.head d) →
      Equal S.R Γ' (apps (Presentation.rename ρ (lams ps B)) (spineArgs ps img))
        (Presentation.rename (spineRen ps ρ img) B) (.head d)
  | _, _, _, _, [], _, _, _, _, _, _, _, _, compatible, _, typed => by
      have renamed := typed.rename compatible
      exact .refl renamed
  | _, m, Γ, Γ', p :: ps, d, B, ρ, img, formed, formed', universes, hd, compatible, imgs, typed => by
      have formedP : CtxFormed S.R (.snoc Γ (.head p)) := formed.snoc (IsType.head_of_universe universes.head)
      have compatible' : CtxRen (.snoc Γ (.head p)) Γ' (Fin.cases (motive := fun _ => Fin m) (img 0) ρ) := by
        intro index
        cases index using Fin.cases with
        | zero =>
            show Ctx.lookup Γ' (img 0) = Presentation.rename _ (Presentation.rename wk (.head p))
            rw [imgs 0]
            rfl
        | succ prior =>
            show Ctx.lookup Γ' (ρ prior) = Presentation.rename _ (Presentation.rename wk (Ctx.lookup Γ prior))
            rw [compatible prior, rename_comp]
            rfl
      have ih := beta_apps ps (Fin.cases (motive := fun _ => Fin m) (img 0) ρ) (fun j => img j.succ) formedP formed'
        universes.tail hd compatible' (fun j => imgs j.succ) typed
      -- The first β-step.
      have tBody := lams_typed ps formedP universes.tail hd typed
      have tLifted : Typed S.R (.snoc Γ' (.head p)) (Presentation.rename (liftRen ρ) (lams ps B)) (famCode ps d) := by
        have renamed := tBody.rename (CtxRen.snoc compatible (.head p))
        rw [famCode_rename] at renamed
        exact renamed
      obtain ⟨u, hu, tPi⟩ := famCode_isType (p :: ps) universes hd formed'
      have tPi' : Typed S.R Γ' (.pi (.head p) (famCode ps d)) (.head u) := tPi
      have tv : Typed S.R Γ' (.var (img 0)) (.head p) := by
        have v := Derivable.var (R := S.R) (Γ := Γ') (img 0)
        rw [imgs 0] at v
        exact v
      have beta := Derivable.betaPi tPi' hu tLifted tv
      rw [inst0_rename_liftRen] at beta
      have beta' : Equal S.R Γ' (.app (.lam (Presentation.rename (liftRen ρ) (lams ps B))) (.var (img 0)))
          (Presentation.rename (Fin.cases (motive := fun _ => Fin m) (img 0) ρ) (lams ps B)) (famCode ps d) := by
        simpa only [inst0, famCode_subst] using beta
      have spine := apps_congr ps (fun j => img j.succ) (fun j => imgs j.succ) beta'
      rw [spineArgs_cons]
      exact spine.trans ih

end Typing

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
