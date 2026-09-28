import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Package
import Mettapedia.Logic.HOL.ProofSyntaxModulo

/-!
# HOL signatures read inside a package of proposition codes

A *reading* of a HOL signature in a package of proposition codes over a base
package fixes

* a closed carrier for each base sort: the carrier of `prop` is the type of
  codes, and the carrier of `a ⇒ b` is the non-dependent function type;
* a closed term for each HOL constant the package interprets. The map is
  partial: a package need not interpret the whole signature;
* the instance names `all@A` and `eq@A` at every simple type.

The *fragment* of the reading is the part of the selected typed judgment built
from carriers, codes and the decoder. A HOL term is read by `term`, which is
undefined exactly on the connectives outside the core (`⊤ ⊥ ∧ ∨ ¬ ∃`) and on
the constants the reading does not interpret.

The laws of a reading (`Laws`) say that the decoder reads each quantifier and
equation instance at the carrier of its type, that the instance names are not
the names of `prop`, `holds` and `imp`, that the universe of proofs is a
universe closed under function types, and that the sorts and the interpreted
constants are typed at their carriers. Under the laws:

* every read term has its carrier as a type (`term_typed`);
* the decoder gives the codes the natural-deduction rules of implication, of
  the quantifier at every carrier and, under the identity reading, of equality
  read as identity (`impIntro`, `impElim`, `allIntro`, `allElim`,
  `equal_holds_eq`, `reflIntro`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open Mettapedia.Logic

universe u v

/-- A HOL signature read inside a code package of the selected judgment. -/
structure HOLReading (Head : Type) (Base : Type u) (Const : HOL.Ty Base → Type v) where
  /-- The codes: `prop`, `holds`, `imp`, the instance tables, the identity flag. -/
  codes : Codes Head
  /-- The base package: data, recursors, definitions, identity elimination. -/
  base : Rules Head
  /-- The closed carrier of each base sort. -/
  sort : Base → Tm Head 0
  /-- The closed term of each constant the package interprets. -/
  constant : ∀ {τ : HOL.Ty Base}, Const τ → Option (Tm Head 0)
  /-- The name of the quantifier instance `all@A`. -/
  allName : HOL.Ty Base → DeclName
  /-- The name of the equation instance `eq@A`. -/
  eqName : HOL.Ty Base → DeclName

namespace HOLReading

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-! ## Variables -/

/-- The de Bruijn index of a typed HOL variable. -/
def varIndex : {Γ : HOL.Ctx Base} → {τ : HOL.Ty Base} → HOL.Var Γ τ → Fin Γ.length
  | _, _, .vz => 0
  | _, _, .vs i => (varIndex i).succ

/-- The typed variable at a de Bruijn index. -/
def varAt : (Γ : HOL.Ctx Base) → Fin Γ.length → Σ τ : HOL.Ty Base, HOL.Var Γ τ
  | [], i => i.elim0
  | τ :: Γ, i => Fin.cases ⟨τ, .vz⟩ (fun j => ⟨(varAt Γ j).1, .vs (varAt Γ j).2⟩) i

theorem varAt_varIndex : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (i : HOL.Var Γ τ),
    varAt Γ (varIndex i) = ⟨τ, i⟩
  | _, _, .vz => rfl
  | _, _, .vs i => by
      simp only [varIndex, varAt, Fin.cases_succ]
      rw [varAt_varIndex i]

/-! ## Carriers, contexts, and the reading of terms -/

section Syntax

variable (ρ : HOLReading Head Base Const)

/-- The package of the reading: the base extended by the codes. -/
abbrev rules : Rules Head := ρ.codes.extend ρ.base

/-- The universe of proofs, where `prop` lives and `holds` lands. -/
abbrev U {n : Nat} : Tm Head n := .head ρ.codes.proofs

abbrev holdsOf {n : Nat} (c : Tm Head n) : Tm Head n := ρ.codes.holdsOf c

abbrev impOf {n : Nat} (p q : Tm Head n) : Tm Head n := ρ.codes.impOf p q

/-- `all@A f`. -/
abbrev allOf {n : Nat} (τ : HOL.Ty Base) (f : Tm Head n) : Tm Head n :=
  .app (.const (ρ.allName τ)) f

/-- `eq@A x y`. -/
abbrev eqOf {n : Nat} (τ : HOL.Ty Base) (x y : Tm Head n) : Tm Head n :=
  .app (.app (.const (ρ.eqName τ)) x) y

/-- The carrier of a simple type, at any depth: `prop ↦ prop`, a base sort to
its carrier, and `a ⇒ b ↦ Π (_ : a). b`. -/
def carrierAt : (n : Nat) → HOL.Ty Base → Tm Head n
  | _, .prop => .const ρ.codes.prop
  | _, .base b => liftClosed (ρ.sort b)
  | n, .arr a b => .pi (carrierAt n a) (carrierAt (n + 1) b)

/-- The closed carrier of a simple type. -/
abbrev carrier (τ : HOL.Ty Base) : Tm Head 0 := ρ.carrierAt 0 τ

@[simp] theorem rename_carrierAt {n m : Nat} (r : Ren n m) (τ : HOL.Ty Base) :
    Presentation.rename r (ρ.carrierAt n τ) = ρ.carrierAt m τ := by
  induction τ generalizing n m with
  | prop => rfl
  | base b => exact rename_liftClosed r (ρ.sort b)
  | arr a b ia ib => simp only [carrierAt, Presentation.rename, ia, ib]

@[simp] theorem subst_carrierAt {n m : Nat} (σ : Sub Head n m) (τ : HOL.Ty Base) :
    Presentation.subst σ (ρ.carrierAt n τ) = ρ.carrierAt m τ := by
  induction τ generalizing n m with
  | prop => rfl
  | base b => exact subst_liftClosed σ (ρ.sort b)
  | arr a b ia ib => simp only [carrierAt, Presentation.subst, ia, ib]

@[simp] theorem inst0_carrierAt {n : Nat} (a : Tm Head n) (τ : HOL.Ty Base) :
    inst0 a (ρ.carrierAt (n + 1) τ) = ρ.carrierAt n τ :=
  ρ.subst_carrierAt _ τ

theorem liftClosed_carrier {n : Nat} (τ : HOL.Ty Base) :
    (liftClosed (ρ.carrier τ) : Tm Head n) = ρ.carrierAt n τ :=
  ρ.rename_carrierAt _ τ

/-- The object context of `Γ`: one variable per variable of `Γ`, at its
carrier. -/
def objCtx : (Γ : HOL.Ctx Base) → Ctx Head Γ.length
  | [] => .nil
  | τ :: Γ => .snoc (objCtx Γ) (ρ.carrierAt Γ.length τ)

/-- Weakening past `k` binders. -/
def wkBy {n : Nat} (k : Nat) : Ren n (n + k) := fun i => Fin.castAdd k i

/-- The object context of `Γ` followed by one proof variable of type `holds c`
for each code `c` of `hyps`, the head of the list innermost. -/
def ctx (Γ : HOL.Ctx Base) :
    (hyps : List (Tm Head Γ.length)) → Ctx Head (Γ.length + hyps.length)
  | [] => ρ.objCtx Γ
  | c :: cs => .snoc (ctx Γ cs) (ρ.holdsOf (Presentation.rename (wkBy cs.length) c))

theorem ctx_nil (Γ : HOL.Ctx Base) : ρ.ctx Γ [] = ρ.objCtx Γ := rfl

theorem lookup_objCtx {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (i : HOL.Var Γ τ) :
    Ctx.lookup (ρ.objCtx Γ) (varIndex i) = ρ.carrierAt Γ.length τ := by
  induction i with
  | vz => simp only [objCtx, varIndex, Ctx.lookup_snoc_zero, rename_carrierAt, List.length_cons]
  | vs i ih =>
      simp only [objCtx, varIndex, Ctx.lookup_snoc_succ, ih, rename_carrierAt, List.length_cons]

/-- Two optional terms, combined when both are present. -/
def both {n : Nat} (g : Tm Head n → Tm Head n → Tm Head n) :
    Option (Tm Head n) → Option (Tm Head n) → Option (Tm Head n)
  | some a, some b => some (g a b)
  | _, _ => none

/-- The reading of a HOL term. Undefined on `⊤ ⊥ ∧ ∨ ¬ ∃` and on the constants
the reading does not interpret. -/
def term : {Γ : HOL.Ctx Base} → {τ : HOL.Ty Base} → HOL.Term Const Γ τ →
    Option (Tm Head Γ.length)
  | _, _, .var i => some (.var (varIndex i))
  | _, _, .const c => (ρ.constant c).map fun t => liftClosed t
  | _, _, .app f a => both .app (term f) (term a)
  | _, _, .lam b => (term b).map .lam
  | _, _, .imp p q => both ρ.impOf (term p) (term q)
  | _, _, @HOL.Term.all _ _ τ _ b => (term b).map fun b' => ρ.allOf τ (.lam b')
  | _, _, @HOL.Term.eq _ _ _ τ l r => both (ρ.eqOf τ) (term l) (term r)
  | _, _, .top | _, _, .bot | _, _, .and _ _ | _, _, .or _ _ | _, _, .not _
  | _, _, .ex _ => none

end Syntax

theorem both_eq_some {n : Nat} {g : Tm Head n → Tm Head n → Tm Head n}
    {x y : Option (Tm Head n)} {out : Tm Head n} :
    both g x y = some out ↔ ∃ a b, x = some a ∧ y = some b ∧ out = g a b := by
  cases x <;> cases y <;> simp [both, eq_comm]

/-! ## Inversion of the reading -/

section Inversion

variable {ρ : HOLReading Head Base Const} {Γ : HOL.Ctx Base}

theorem term_app {σ τ : HOL.Ty Base} {f : HOL.Term Const Γ (.arr σ τ)}
    {a : HOL.Term Const Γ σ}
    {out : Tm Head Γ.length} (h : ρ.term (.app f a) = some out) :
    ∃ f' a', ρ.term f = some f' ∧ ρ.term a = some a' ∧ out = .app f' a' :=
  both_eq_some.mp h

theorem term_lam {σ τ : HOL.Ty Base} {b : HOL.Term Const (σ :: Γ) τ} {out : Tm Head Γ.length}
    (h : ρ.term (.lam b) = some out) : ∃ b', ρ.term b = some b' ∧ out = .lam b' := by
  obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b', hb, rfl⟩

theorem term_imp {p q : HOL.Formula Const Γ} {out : Tm Head Γ.length}
    (h : ρ.term (.imp p q) = some out) :
    ∃ p' q', ρ.term p = some p' ∧ ρ.term q = some q' ∧ out = ρ.impOf p' q' :=
  both_eq_some.mp h

theorem term_all {σ : HOL.Ty Base} {b : HOL.Formula Const (σ :: Γ)} {out : Tm Head Γ.length}
    (h : ρ.term (.all b) = some out) :
    ∃ b', ρ.term b = some b' ∧ out = ρ.allOf σ (.lam b') := by
  obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b', hb, rfl⟩

theorem term_eq {τ : HOL.Ty Base} {l r : HOL.Term Const Γ τ} {out : Tm Head Γ.length}
    (h : ρ.term (.eq l r) = some out) :
    ∃ l' r', ρ.term l = some l' ∧ ρ.term r = some r' ∧ out = ρ.eqOf τ l' r' :=
  both_eq_some.mp h

/-- A read term is core. -/
theorem isCore_of_term : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {t : HOL.Term Const Γ τ}
    {out : Tm Head Γ.length}, ρ.term t = some out → t.isCore = true
  | _, _, .var _, _, _ => rfl
  | _, _, .const _, _, _ => rfl
  | _, _, .app f a, _, h => by
      obtain ⟨_, _, hf, ha, -⟩ := term_app h
      simp only [HOL.Term.isCore, isCore_of_term hf, isCore_of_term ha, Bool.and_self]
  | _, _, .lam b, _, h => by
      obtain ⟨_, hb, -⟩ := term_lam h
      simpa only [HOL.Term.isCore] using isCore_of_term hb
  | _, _, .imp p q, _, h => by
      obtain ⟨_, _, hp, hq, -⟩ := term_imp h
      simp only [HOL.Term.isCore, isCore_of_term hp, isCore_of_term hq, Bool.and_self]
  | _, _, .all b, _, h => by
      obtain ⟨_, hb, -⟩ := term_all h
      simpa only [HOL.Term.isCore] using isCore_of_term hb
  | _, _, .eq l r, _, h => by
      obtain ⟨_, _, hl, hr, -⟩ := term_eq h
      simp only [HOL.Term.isCore, isCore_of_term hl, isCore_of_term hr, Bool.and_self]
  | _, _, .top, _, h | _, _, .bot, _, h | _, _, .and _ _, _, h | _, _, .or _ _, _, h
  | _, _, .not _, _, h | _, _, .ex _, _, h => by cases h

end Inversion

/-! ## Renaming and substitution commute with the reading -/

section Binding

variable (ρ : HOLReading Head Base Const)

theorem term_rename {Γ Δ : HOL.Ctx Base} (r : HOL.Rename Base Γ Δ)
    (raw : Ren Γ.length Δ.length)
    (compatible : ∀ {τ : HOL.Ty Base} (i : HOL.Var Γ τ), varIndex (r i) = raw (varIndex i))
    {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ) :
    ρ.term (HOL.rename r t) = (ρ.term t).map (Presentation.rename raw) := by
  induction t generalizing Δ with
  | var i => simp [HOL.rename, term, compatible, Presentation.rename]
  | const c =>
      simp only [HOL.rename, term, Option.map_map]
      cases ρ.constant c <;> simp [rename_liftClosed]
  | app f a ihf iha =>
      simp only [HOL.rename, term, ihf r raw compatible, iha r raw compatible]
      cases ρ.term f <;> cases ρ.term a <;> rfl
  | @lam σ Γ τ b ih =>
      have lifted : ∀ {τ'} (i : HOL.Var (σ :: Γ) τ'),
          varIndex (HOL.Rename.lift r i) = liftRen raw (varIndex i) := by
        intro τ' i
        cases i with
        | vz => rfl
        | vs i => exact congrArg Fin.succ (compatible i)
      simp only [HOL.rename, term, ih _ _ lifted]
      cases ρ.term b <;> rfl
  | imp p q ihp ihq =>
      simp only [HOL.rename, term, ihp r raw compatible, ihq r raw compatible]
      cases ρ.term p <;> cases ρ.term q <;> rfl
  | @all σ Γ b ih =>
      have lifted : ∀ {τ'} (i : HOL.Var (σ :: Γ) τ'),
          varIndex (HOL.Rename.lift r i) = liftRen raw (varIndex i) := by
        intro τ' i
        cases i with
        | vz => rfl
        | vs i => exact congrArg Fin.succ (compatible i)
      simp only [HOL.rename, term, ih _ _ lifted]
      cases ρ.term b <;> rfl
  | eq l r' ihl ihr =>
      simp only [HOL.rename, term, ihl r raw compatible, ihr r raw compatible]
      cases ρ.term l <;> cases ρ.term r' <;> rfl
  | top | bot | and | or | not | ex => rfl

theorem term_weaken {Γ : HOL.Ctx Base} {σ τ : HOL.Ty Base} (t : HOL.Term Const Γ τ) :
    ρ.term (HOL.weaken (σ := σ) t) = (ρ.term t).map (Presentation.rename wk) :=
  ρ.term_rename HOL.Rename.weaken wk (fun _ => rfl) t

/-- Substitution commutes with the reading when every image is read. -/
theorem term_subst {Γ Δ : HOL.Ctx Base} (s : HOL.Subst Const Γ Δ)
    (raw : Sub Head Γ.length Δ.length)
    (compatible : ∀ {τ : HOL.Ty Base} (i : HOL.Var Γ τ),
      ρ.term (s i) = some (raw (varIndex i)))
    {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ) :
    ρ.term (HOL.subst s t) = (ρ.term t).map (Presentation.subst raw) := by
  induction t generalizing Δ with
  | var i => exact compatible i
  | const c =>
      simp only [HOL.subst, term, Option.map_map]
      cases ρ.constant c <;> simp [subst_liftClosed]
  | app f a ihf iha =>
      simp only [HOL.subst, term, ihf s raw compatible, iha s raw compatible]
      cases ρ.term f <;> cases ρ.term a <;> rfl
  | @lam σ Γ τ b ih =>
      have lifted : ∀ {τ'} (i : HOL.Var (σ :: Γ) τ'),
          ρ.term (HOL.Subst.lift s i) = some (liftSub raw (varIndex i)) := by
        intro τ' i
        cases i with
        | vz => rfl
        | vs i =>
            change ρ.term (HOL.rename HOL.Rename.weaken (s i)) = _
            rw [ρ.term_rename HOL.Rename.weaken wk (fun _ => rfl), compatible i]
            rfl
      simp only [HOL.subst, term, ih _ _ lifted]
      cases ρ.term b <;> rfl
  | imp p q ihp ihq =>
      simp only [HOL.subst, term, ihp s raw compatible, ihq s raw compatible]
      cases ρ.term p <;> cases ρ.term q <;> rfl
  | @all σ Γ b ih =>
      have lifted : ∀ {τ'} (i : HOL.Var (σ :: Γ) τ'),
          ρ.term (HOL.Subst.lift s i) = some (liftSub raw (varIndex i)) := by
        intro τ' i
        cases i with
        | vz => rfl
        | vs i =>
            change ρ.term (HOL.rename HOL.Rename.weaken (s i)) = _
            rw [ρ.term_rename HOL.Rename.weaken wk (fun _ => rfl), compatible i]
            rfl
      simp only [HOL.subst, term, ih _ _ lifted]
      cases ρ.term b <;> rfl
  | eq l r ihl ihr =>
      simp only [HOL.subst, term, ihl s raw compatible, ihr s raw compatible]
      cases ρ.term l <;> cases ρ.term r <;> rfl
  | top | bot | and | or | not | ex => rfl

/-- Instantiation commutes with the reading when the argument is read. -/
theorem term_instantiate {Γ : HOL.Ctx Base} {σ τ : HOL.Ty Base} {a : HOL.Term Const Γ σ}
    {a' : Tm Head Γ.length} (ha : ρ.term a = some a') (b : HOL.Term Const (σ :: Γ) τ) :
    ρ.term (HOL.instantiate a b) = (ρ.term b).map (inst0 a') := by
  apply ρ.term_subst (HOL.Subst.single a) (subst0 a')
  intro τ' i
  cases i with
  | vz => exact ha
  | vs _ => rfl

/-- The native image of a source substitution: the reading of each image, and
an inert constant where an image is not read. -/
def nativeSub {Θ Γ : HOL.Ctx Base} (s : HOL.Subst Const Θ Γ) : Sub Head Θ.length Γ.length :=
  fun i => (ρ.term (s (varAt Θ i).2)).getD (.const .anonymous)

theorem nativeSub_varIndex {Θ Γ : HOL.Ctx Base} (s : HOL.Subst Const Θ Γ) {τ : HOL.Ty Base}
    (i : HOL.Var Θ τ) {out : Tm Head Γ.length} (h : ρ.term (s i) = some out) :
    ρ.nativeSub s (varIndex i) = out := by
  have atIndex : ρ.term (s (varAt Θ (varIndex i)).2) = ρ.term (s i) :=
    congrArg (fun entry : Σ τ : HOL.Ty Base, HOL.Var Θ τ => ρ.term (s entry.2))
      (varAt_varIndex i)
  simp only [nativeSub, atIndex, h, Option.getD_some]

/-- A read instance of a term is the native instance of its read pattern. Only
the images of the variables that occur are read, so no image outside them is
assumed read. -/
theorem term_subst_inv {Θ Γ : HOL.Ctx Base} (s : HOL.Subst Const Θ Γ)
    (raw : Sub Head Θ.length Γ.length)
    (compatible : ∀ {τ : HOL.Ty Base} (i : HOL.Var Θ τ) {out : Tm Head Γ.length},
      ρ.term (s i) = some out → raw (varIndex i) = out) :
    ∀ {τ : HOL.Ty Base} (t : HOL.Term Const Θ τ) {out : Tm Head Γ.length},
      ρ.term (HOL.subst s t) = some out →
        ∃ t', ρ.term t = some t' ∧ out = Presentation.subst raw t' := by
  intro τ t
  induction t generalizing Γ with
  | var i =>
      intro out h
      exact ⟨_, rfl, (compatible i h).symm⟩
  | const c =>
      intro out h
      change (ρ.constant c).map (fun t => liftClosed t) = some out at h
      obtain ⟨t0, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨liftClosed t0, by simp [term, ht], ?_⟩
      exact (subst_liftClosed raw t0).symm
  | app f a ihf iha =>
      intro out h
      obtain ⟨f', a', hf, ha, rfl⟩ := term_app (ρ := ρ) h
      obtain ⟨f0, hf0, rfl⟩ := ihf s raw compatible hf
      obtain ⟨a0, ha0, rfl⟩ := iha s raw compatible ha
      exact ⟨.app f0 a0, by simp [term, hf0, ha0, both], rfl⟩
  | @lam σ Θ τ b ih =>
      intro out h
      obtain ⟨b', hb, rfl⟩ := term_lam (ρ := ρ) h
      have lifted : ∀ {τ'} (i : HOL.Var (σ :: Θ) τ') {out : Tm Head (Γ.length + 1)},
          ρ.term (HOL.Subst.lift s i) = some out → liftSub raw (varIndex i) = out := by
        intro τ' i out h
        cases i with
        | vz => cases h; rfl
        | vs i =>
            change ρ.term (HOL.rename HOL.Rename.weaken (s i)) = _ at h
            rw [ρ.term_rename HOL.Rename.weaken wk (fun _ => rfl)] at h
            obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
            change Presentation.rename wk (raw (varIndex i)) = _
            rw [compatible i ho]
      obtain ⟨b0, hb0, rfl⟩ := ih (HOL.Subst.lift s) (liftSub raw) lifted hb
      exact ⟨.lam b0, by simp [term, hb0], rfl⟩
  | imp p q ihp ihq =>
      intro out h
      obtain ⟨p', q', hp, hq, rfl⟩ := term_imp (ρ := ρ) h
      obtain ⟨p0, hp0, rfl⟩ := ihp s raw compatible hp
      obtain ⟨q0, hq0, rfl⟩ := ihq s raw compatible hq
      exact ⟨ρ.impOf p0 q0, by simp [term, hp0, hq0, both], rfl⟩
  | @all σ Θ b ih =>
      intro out h
      obtain ⟨b', hb, rfl⟩ := term_all (ρ := ρ) h
      have lifted : ∀ {τ'} (i : HOL.Var (σ :: Θ) τ') {out : Tm Head (Γ.length + 1)},
          ρ.term (HOL.Subst.lift s i) = some out → liftSub raw (varIndex i) = out := by
        intro τ' i out h
        cases i with
        | vz => cases h; rfl
        | vs i =>
            change ρ.term (HOL.rename HOL.Rename.weaken (s i)) = _ at h
            rw [ρ.term_rename HOL.Rename.weaken wk (fun _ => rfl)] at h
            obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
            change Presentation.rename wk (raw (varIndex i)) = _
            rw [compatible i ho]
      obtain ⟨b0, hb0, rfl⟩ := ih (HOL.Subst.lift s) (liftSub raw) lifted hb
      exact ⟨ρ.allOf σ (.lam b0), by simp [term, hb0], rfl⟩
  | eq l r ihl ihr =>
      intro out h
      obtain ⟨l', r', hl, hr, rfl⟩ := term_eq (ρ := ρ) h
      obtain ⟨l0, hl0, rfl⟩ := ihl s raw compatible hl
      obtain ⟨r0, hr0, rfl⟩ := ihr s raw compatible hr
      exact ⟨ρ.eqOf _ l0 r0, by simp only [term, hl0, hr0]; rfl, rfl⟩
  | top | bot | and | or | not | ex => intro out h; cases h

end Binding

/-! ## The laws of a reading -/

/-- The laws of a reading, all about the package itself: the decoder's tables
agree with the carriers, the instance names are apart from the fixed code
names, the universe of proofs is a universe closed under function types whose
decoder type is formed, and the sorts and interpreted constants are typed. -/
structure Laws (ρ : HOLReading Head Base Const) : Prop where
  /-- The decoder reads `all@A` at the carrier of `A`. -/
  quantifier : ∀ τ, ρ.codes.quantifiers (ρ.allName τ) = some (ρ.carrier τ)
  /-- Under the identity reading, `eq@A` decodes at the carrier of `A`. -/
  equation : ∀ τ, ρ.codes.equationCarrier (ρ.eqName τ) = some (ρ.carrier τ)
  allName_apart : ∀ τ, ρ.allName τ ≠ ρ.codes.prop ∧ ρ.allName τ ≠ ρ.codes.holds ∧
    ρ.allName τ ≠ ρ.codes.imp
  eqName_apart : ∀ τ, ρ.eqName τ ≠ ρ.codes.prop ∧ ρ.eqName τ ≠ ρ.codes.holds ∧
    ρ.eqName τ ≠ ρ.codes.imp ∧ ρ.codes.quantifiers (ρ.eqName τ) = none
  imp_apart : ρ.codes.imp ≠ ρ.codes.prop ∧ ρ.codes.imp ≠ ρ.codes.holds
  holds_apart : ρ.codes.holds ≠ ρ.codes.prop
  /-- The universe of proofs is a universe. -/
  proofs_universe : ρ.rules.isUniverse ρ.codes.proofs
  /-- It is a type of a universe. -/
  proofs_typed : ∃ w, ρ.rules.isUniverse w ∧ ρ.rules.headTyping ρ.codes.proofs w
  /-- It is closed under function types. -/
  proofs_pi : ∃ w, ρ.rules.join ρ.codes.proofs ρ.codes.proofs w ∧
    ρ.rules.cumulative w ρ.codes.proofs
  /-- The declared type of the decoder, `prop → U`, is formed. -/
  holds_formed : ∃ w, ρ.rules.isUniverse w ∧ Typed ρ.rules .nil ρ.codes.holdsType (.head w)
  sort_typed : ∀ b, Typed ρ.rules .nil (ρ.sort b) (.head ρ.codes.proofs)
  const_typed : ∀ {τ : HOL.Ty Base} (c : Const τ) {t : Tm Head 0},
    ρ.constant c = some t → Typed ρ.rules .nil t (ρ.carrier τ)

/-- A closed typing holds in every context. -/
theorem typed_closed {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {t T : Tm Head 0}
    (h : Typed R .nil t T) : Typed R Γ (liftClosed t) (liftClosed T) :=
  h.rename (fun i => Fin.elim0 i)

theorem Codes.codeType_eq (K : Codes Head) {e : DeclName} {A : Tm Head 0}
    (apart : e ≠ K.prop ∧ e ≠ K.holds ∧ e ≠ K.imp ∧ K.quantifiers e = none)
    (carrier : K.equationCarrier e = some A) : K.codeType e = some (K.eqType A) := by
  obtain ⟨hp, hh, hi, hq⟩ := apart
  simp [Codes.codeType, hp, hh, hi, hq, carrier]

theorem var_carrier (ρ : HOLReading Head Base Const) {n : Nat} {Γ : Ctx Head n}
    (τ : HOL.Ty Base) :
    Typed ρ.rules (.snoc Γ (ρ.carrierAt n τ)) (.var 0) (ρ.carrierAt (n + 1) τ) := by
  simpa only [Ctx.lookup_snoc_zero, rename_carrierAt] using
    (Derivable.var (R := ρ.rules) (Γ := .snoc Γ (ρ.carrierAt n τ)) 0)

theorem app_carrier {ρ : HOLReading Head Base Const} {n : Nat} {Γ : Ctx Head n}
    {σ τ : HOL.Ty Base} {f a : Tm Head n}
    (hf : Typed ρ.rules Γ f (ρ.carrierAt n (.arr σ τ)))
    (ha : Typed ρ.rules Γ a (ρ.carrierAt n σ)) :
    Typed ρ.rules Γ (.app f a) (ρ.carrierAt n τ) := by
  have h := Derivable.appElim hf ha
  rwa [inst0_carrierAt] at h

namespace Laws

variable {ρ : HOLReading Head Base Const} (L : ρ.Laws)
include L

/-! ### The code constants -/

theorem prop_typed {n : Nat} {Γ : Ctx Head n} : Typed ρ.rules Γ ρ.codes.propT ρ.U := by
  obtain ⟨w, hw, ht⟩ := L.proofs_typed
  exact .const (ρ.codes.extend_constantType_of_code ρ.base ρ.codes.codeType_prop)
    (.headType ht) hw

theorem holds_typed {n : Nat} {Γ : Ctx Head n} :
    Typed ρ.rules Γ (.const ρ.codes.holds) (.pi ρ.codes.propT ρ.U) := by
  obtain ⟨w, hw, ht⟩ := L.holds_formed
  exact .const
    (ρ.codes.extend_constantType_of_code ρ.base (ρ.codes.codeType_holds L.holds_apart))
    ht hw

theorem holdsOf_typed {n : Nat} {Γ : Ctx Head n} {c : Tm Head n}
    (h : Typed ρ.rules Γ c ρ.codes.propT) : Typed ρ.rules Γ (ρ.holdsOf c) ρ.U :=
  .appElim L.holds_typed h

theorem pi_typed {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (hA : Typed ρ.rules Γ A ρ.U) (hB : Typed ρ.rules (.snoc Γ A) B ρ.U) :
    Typed ρ.rules Γ (.pi A B) ρ.U := by
  obtain ⟨w, hj, hc⟩ := L.proofs_pi
  exact .cumul (.piForm hA L.proofs_universe hB L.proofs_universe hj) hc

theorem equal_pi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (dom : Equal ρ.rules Γ A A' ρ.U) (cod : Equal ρ.rules (.snoc Γ A) B B' ρ.U) :
    Equal ρ.rules Γ (.pi A B) (.pi A' B') ρ.U := by
  obtain ⟨w, hj, hc⟩ := L.proofs_pi
  exact Derivable.cumulEq (.piCong dom L.proofs_universe cod L.proofs_universe hj) hc

theorem imp_typed {n : Nat} {Γ : Ctx Head n} :
    Typed ρ.rules Γ (.const ρ.codes.imp)
      (.pi ρ.codes.propT (.pi ρ.codes.propT ρ.codes.propT)) :=
  .const (ρ.codes.extend_constantType_of_code ρ.base (ρ.codes.codeType_imp L.imp_apart))
    (L.pi_typed L.prop_typed (L.pi_typed L.prop_typed L.prop_typed)) L.proofs_universe

theorem impOf_typed {n : Nat} {Γ : Ctx Head n} {p q : Tm Head n}
    (hp : Typed ρ.rules Γ p ρ.codes.propT) (hq : Typed ρ.rules Γ q ρ.codes.propT) :
    Typed ρ.rules Γ (ρ.impOf p q) ρ.codes.propT :=
  .appElim (.appElim L.imp_typed hp) hq

theorem carrierAt_typed {n : Nat} {Γ : Ctx Head n} (τ : HOL.Ty Base) :
    Typed ρ.rules Γ (ρ.carrierAt n τ) ρ.U := by
  induction τ generalizing n with
  | prop => exact L.prop_typed
  | base b => exact typed_closed (L.sort_typed b)
  | arr a b ia ib => exact L.pi_typed ia ib

theorem all_typed {n : Nat} {Γ : Ctx Head n} (τ : HOL.Ty Base) :
    Typed ρ.rules Γ (.const (ρ.allName τ))
      (.pi (.pi (ρ.carrierAt n τ) ρ.codes.propT) ρ.codes.propT) := by
  have declared := ρ.codes.extend_constantType_of_code ρ.base
    (ρ.codes.codeType_all (L.allName_apart τ) (L.quantifier τ))
  have formed : Typed ρ.rules .nil (ρ.codes.allType (ρ.carrier τ)) ρ.U :=
    L.pi_typed (L.pi_typed (L.carrierAt_typed τ) L.prop_typed) L.prop_typed
  have h := Derivable.const (Γ := Γ) declared formed L.proofs_universe
  simpa only [Codes.allType, liftClosed, Presentation.rename, rename_carrierAt] using h

theorem eq_typed {n : Nat} {Γ : Ctx Head n} (τ : HOL.Ty Base) :
    Typed ρ.rules Γ (.const (ρ.eqName τ))
      (.pi (ρ.carrierAt n τ) (.pi (ρ.carrierAt (n + 1) τ) ρ.codes.propT)) := by
  have declared := ρ.codes.extend_constantType_of_code ρ.base
    (Codes.codeType_eq ρ.codes (L.eqName_apart τ) (L.equation τ))
  have formed : Typed ρ.rules .nil (ρ.codes.eqType (ρ.carrier τ)) ρ.U := by
    refine L.pi_typed (L.carrierAt_typed τ) ?_
    simpa only [rename_carrierAt] using
      L.pi_typed (Γ := .snoc .nil (ρ.carrier τ)) (L.carrierAt_typed τ) L.prop_typed
  have h := Derivable.const (Γ := Γ) declared formed L.proofs_universe
  simpa only [Codes.eqType, liftClosed, Presentation.rename, rename_carrierAt] using h

theorem allOf_typed {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {f : Tm Head n}
    (hf : Typed ρ.rules Γ f (.pi (ρ.carrierAt n τ) ρ.codes.propT)) :
    Typed ρ.rules Γ (ρ.allOf τ f) ρ.codes.propT :=
  .appElim (L.all_typed τ) hf

theorem eqOf_typed {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {x y : Tm Head n}
    (hx : Typed ρ.rules Γ x (ρ.carrierAt n τ)) (hy : Typed ρ.rules Γ y (ρ.carrierAt n τ)) :
    Typed ρ.rules Γ (ρ.eqOf τ x y) ρ.codes.propT := by
  have h := Derivable.appElim (L.eq_typed τ) hx
  simp only [inst0, Presentation.subst, subst_carrierAt] at h
  exact .appElim h hy

theorem lam_carrier {n : Nat} {Γ : Ctx Head n} {σ τ : HOL.Ty Base} {b : Tm Head (n + 1)}
    (hb : Typed ρ.rules (.snoc Γ (ρ.carrierAt n σ)) b (ρ.carrierAt (n + 1) τ)) :
    Typed ρ.rules Γ (.lam b) (ρ.carrierAt n (.arr σ τ)) :=
  .lamIntro (L.carrierAt_typed (.arr σ τ)) L.proofs_universe hb

/-! ### Decoding -/

/-- `holds (imp p q) ≡ Π (_ : holds p). holds q`. -/
theorem equal_holds_imp {n : Nat} {Γ : Ctx Head n} {p q : Tm Head n}
    (hp : Typed ρ.rules Γ p ρ.codes.propT) (hq : Typed ρ.rules Γ q ρ.codes.propT) :
    Equal ρ.rules Γ (ρ.holdsOf (ρ.impOf p q))
      (.pi (ρ.holdsOf p) (ρ.holdsOf (Presentation.rename wk q))) ρ.U :=
  .root (ρ.codes.extend_decoder_step ρ.base (DecoderStep.imp p q))
    (L.holdsOf_typed (L.impOf_typed hp hq))
    (L.pi_typed (L.holdsOf_typed hp) (L.holdsOf_typed hq.weaken))

/-- `holds (all@A f) ≡ Π (x : A). holds (f x)`. -/
theorem equal_holds_all {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {f : Tm Head n}
    (hf : Typed ρ.rules Γ f (.pi (ρ.carrierAt n τ) ρ.codes.propT)) :
    Equal ρ.rules Γ (ρ.holdsOf (ρ.allOf τ f))
      (.pi (ρ.carrierAt n τ) (ρ.holdsOf (.app (Presentation.rename wk f) (.var 0)))) ρ.U := by
  have step := ρ.codes.extend_decoder_step ρ.base
    (DecoderStep.all (D := ρ.codes.decoders) (L.quantifier τ) f)
  rw [ρ.liftClosed_carrier] at step
  have hf' : Typed ρ.rules (.snoc Γ (ρ.carrierAt n τ)) (Presentation.rename wk f)
      (.pi (ρ.carrierAt (n + 1) τ) ρ.codes.propT) := by
    simpa only [Presentation.rename, rename_carrierAt] using
      hf.weaken (extension := ρ.carrierAt n τ)
  exact .root step (L.holdsOf_typed (L.allOf_typed hf))
    (L.pi_typed (L.carrierAt_typed τ) (L.holdsOf_typed (.appElim hf' (ρ.var_carrier τ))))

/-- `holds (all@A (λx. B)) ≡ Π (x : A). holds B`, with the β-step under the
binder. -/
theorem equal_holds_all_lam {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {B : Tm Head (n + 1)}
    (hB : Typed ρ.rules (.snoc Γ (ρ.carrierAt n τ)) B ρ.codes.propT) :
    Equal ρ.rules Γ (ρ.holdsOf (ρ.allOf τ (.lam B))) (.pi (ρ.carrierAt n τ) (ρ.holdsOf B))
      ρ.U := by
  have family : Typed ρ.rules Γ (.lam B) (.pi (ρ.carrierAt n τ) ρ.codes.propT) :=
    .lamIntro (L.pi_typed (L.carrierAt_typed τ) L.prop_typed) L.proofs_universe hB
  refine .trans (L.equal_holds_all family)
    (L.equal_pi (.refl (L.carrierAt_typed τ)) (.appCong (.refl L.holds_typed) ?_))
  have lifted : Typed ρ.rules (.snoc (.snoc Γ (ρ.carrierAt n τ)) (ρ.carrierAt (n + 1) τ))
      (Presentation.rename (liftRen wk) B) ρ.codes.propT := by
    have h := hB.rename (CtxRen.snoc (Gamma := Γ) (Delta := .snoc Γ (ρ.carrierAt n τ))
      (rho := wk) (fun _ => rfl) (ρ.carrierAt n τ))
    simpa only [rename_carrierAt, Codes.propT, Presentation.rename] using h
  have beta := Derivable.betaPi (L.pi_typed (L.carrierAt_typed τ) L.prop_typed)
    L.proofs_universe lifted (ρ.var_carrier τ)
  rw [inst0_var_rename_liftRen_wk] at beta
  exact beta

/-- Under the identity reading, `holds (eq@A x y) ≡ Id A x y`. -/
theorem equal_holds_eq {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {x y : Tm Head n}
    (hx : Typed ρ.rules Γ x (ρ.carrierAt n τ)) (hy : Typed ρ.rules Γ y (ρ.carrierAt n τ)) :
    Equal ρ.rules Γ (ρ.holdsOf (ρ.eqOf τ x y)) (.id (ρ.carrierAt n τ) x y) ρ.U := by
  have step := ρ.codes.extend_decoder_step ρ.base
    (DecoderStep.eq (D := ρ.codes.decoders) (L.equation τ) x y)
  rw [ρ.liftClosed_carrier] at step
  exact .root step (L.holdsOf_typed (L.eqOf_typed hx hy))
    (.idForm (L.carrierAt_typed τ) L.proofs_universe hx hy)

/-- Equal codes decode to equal types. -/
theorem equal_holdsOf {n : Nat} {Γ : Ctx Head n} {c c' : Tm Head n}
    (h : Equal ρ.rules Γ c c' ρ.codes.propT) :
    Equal ρ.rules Γ (ρ.holdsOf c) (ρ.holdsOf c') ρ.U :=
  .appCong (.refl L.holds_typed) h

/-! ### Natural deduction for the codes -/

theorem impIntro {n : Nat} {Γ : Ctx Head n} {p q : Tm Head n} {b : Tm Head (n + 1)}
    (hp : Typed ρ.rules Γ p ρ.codes.propT) (hq : Typed ρ.rules Γ q ρ.codes.propT)
    (hb : Typed ρ.rules (.snoc Γ (ρ.holdsOf p)) b (ρ.holdsOf (Presentation.rename wk q))) :
    Typed ρ.rules Γ (.lam b) (ρ.holdsOf (ρ.impOf p q)) :=
  .conv (.lamIntro (L.pi_typed (L.holdsOf_typed hp) (L.holdsOf_typed hq.weaken))
      L.proofs_universe hb)
    (.symm (L.equal_holds_imp hp hq)) L.proofs_universe

theorem impElim {n : Nat} {Γ : Ctx Head n} {p q f a : Tm Head n}
    (hp : Typed ρ.rules Γ p ρ.codes.propT) (hq : Typed ρ.rules Γ q ρ.codes.propT)
    (hf : Typed ρ.rules Γ f (ρ.holdsOf (ρ.impOf p q)))
    (ha : Typed ρ.rules Γ a (ρ.holdsOf p)) :
    Typed ρ.rules Γ (.app f a) (ρ.holdsOf q) := by
  have h : Typed ρ.rules Γ (.app f a) (ρ.holdsOf (inst0 a (Presentation.rename wk q))) :=
    .appElim (.conv hf (L.equal_holds_imp hp hq) L.proofs_universe) ha
  rwa [inst0_rename_wk] at h

theorem allIntro {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {B b : Tm Head (n + 1)}
    (hB : Typed ρ.rules (.snoc Γ (ρ.carrierAt n τ)) B ρ.codes.propT)
    (hb : Typed ρ.rules (.snoc Γ (ρ.carrierAt n τ)) b (ρ.holdsOf B)) :
    Typed ρ.rules Γ (.lam b) (ρ.holdsOf (ρ.allOf τ (.lam B))) :=
  .conv (.lamIntro (L.pi_typed (L.carrierAt_typed τ) (L.holdsOf_typed hB)) L.proofs_universe hb)
    (.symm (L.equal_holds_all_lam hB)) L.proofs_universe

theorem allElim {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {B : Tm Head (n + 1)}
    {f a : Tm Head n}
    (hB : Typed ρ.rules (.snoc Γ (ρ.carrierAt n τ)) B ρ.codes.propT)
    (hf : Typed ρ.rules Γ f (ρ.holdsOf (ρ.allOf τ (.lam B))))
    (ha : Typed ρ.rules Γ a (ρ.carrierAt n τ)) :
    Typed ρ.rules Γ (.app f a) (ρ.holdsOf (inst0 a B)) :=
  .appElim (.conv hf (L.equal_holds_all_lam hB) L.proofs_universe) ha

/-- Reflexivity proves the equation code of a point with itself, through the
identity reading. -/
theorem reflIntro {n : Nat} {Γ : Ctx Head n} {τ : HOL.Ty Base} {x : Tm Head n}
    (hx : Typed ρ.rules Γ x (ρ.carrierAt n τ)) :
    Typed ρ.rules Γ (.refl x) (ρ.holdsOf (ρ.eqOf τ x x)) :=
  .conv (.reflIntro hx) (.symm (L.equal_holds_eq hx hx)) L.proofs_universe

/-- `λx. refl x` proves `∀x. x = x` at every carrier. -/
theorem refl_typed {n : Nat} {Γ : Ctx Head n} (τ : HOL.Ty Base) :
    Typed ρ.rules Γ (.lam (.refl (.var 0)))
      (ρ.holdsOf (ρ.allOf τ (.lam (ρ.eqOf τ (.var 0) (.var 0))))) :=
  L.allIntro (L.eqOf_typed (ρ.var_carrier τ) (ρ.var_carrier τ))
    (L.reflIntro (ρ.var_carrier τ))

/-! ### Terms -/

/-- **Typing of the reading.** A read HOL term has its carrier as a type in the
object context. -/
theorem term_typed : ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} {t : HOL.Term Const Γ τ}
    {out : Tm Head Γ.length}, ρ.term t = some out →
      Typed ρ.rules (ρ.objCtx Γ) out (ρ.carrierAt Γ.length τ)
  | _, _, .var i, _, h => by
      cases h
      simpa only [ρ.lookup_objCtx] using
        Derivable.var (R := ρ.rules) (Γ := ρ.objCtx _) (varIndex i)
  | _, _, .const c, _, h => by
      obtain ⟨t0, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa only [ρ.liftClosed_carrier] using typed_closed (Γ := ρ.objCtx _) (L.const_typed c ht)
  | _, _, .app f a, _, h => by
      obtain ⟨f', a', hf, ha, rfl⟩ := term_app h
      exact app_carrier (term_typed hf) (term_typed ha)
  | _, _, .lam b, _, h => by
      obtain ⟨b', hb, rfl⟩ := term_lam h
      exact L.lam_carrier (term_typed hb)
  | _, _, .imp p q, _, h => by
      obtain ⟨p', q', hp, hq, rfl⟩ := term_imp h
      exact L.impOf_typed (term_typed hp) (term_typed hq)
  | _, _, .all b, _, h => by
      obtain ⟨b', hb, rfl⟩ := term_all h
      exact L.allOf_typed (.lamIntro (L.pi_typed (L.carrierAt_typed _) L.prop_typed)
        L.proofs_universe (term_typed hb))
  | _, _, .eq l r, _, h => by
      obtain ⟨l', r', hl, hr, rfl⟩ := term_eq h
      exact L.eqOf_typed (term_typed hl) (term_typed hr)
  | _, _, .top, _, h | _, _, .bot, _, h | _, _, .and _ _, _, h | _, _, .or _ _, _, h
  | _, _, .not _, _, h | _, _, .ex _, _, h => by cases h

end Laws

end HOLReading

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
