import Mettapedia.Logic.TierZero.Adequacy.HOLPres
import Mettapedia.Languages.HOLLight.DefinitionAdapters

/-!
# Mettapedia's HOL Light terms as kernel terms

The encoding of the HOL Light specification's syntax (`Languages/HOLLight`, over OpenTheory's
de Bruijn terms) into the kernel terms that `holRules` speak about:

* `encTy`: `.var A` is `(hol:tyvar "A")`; `.op op args` is `(hol:tyapp "op" args…)`, with HOL Light's
  spelling of the operator's name (`sourceOperatorName`: the specification's `->` is HOL Light's
  `fun`);
* `encDB`: `.const c T` is `(hol:const "c" T)`, `.free x` is `(hol:var "x" T)`, `.app f x` is
  `(hol:comb F X)`, `.abs T b` is the kernel's binder `(bind T B)`, and the de Bruijn index
  `.bound i` is the kernel's bound variable `i`: both count binders from the nearest one outward, so
  the encoding moves no index;
* `EncSet S H`: the set term `S` has exactly the encodings of the hypotheses `H` as members.

Names keep only their last component, HOL Light's names being global, and constants and type
operators keep only their names, HOL Light identifying them by name; injectivity therefore holds on
terms whose names are global and whose names determine their provenance (`Ty.Coherent`).

Example: `T = ((\p. p) = (\p. p))` at `bool` encodes to
`(hol:comb (hol:comb (hol:const "=" (hol:tyapp "fun" B (hol:tyapp "fun" B B'))) (hol:const "T" B)) R)`
with `B = (hol:tyapp "bool")`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOL

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.HOLLight.DefinitionAdapters (sourceOperatorName)

/-! ## Kernel terms of the encoding -/

/-- `(hol:tyvar "A")`. -/
def tyvarT (n : String) : Tm := ex [sym "hol:tyvar", str n]
/-- `(hol:tyapp "op" T₁ … Tₖ)`. -/
def tyappT (op : String) (args : List Tm) : Tm := ex (sym "hol:tyapp" :: str op :: args)
/-- `(hol:var "x" T)`. -/
def varT (n : String) (ty : Tm) : Tm := ex [sym "hol:var", str n, ty]
/-- `(hol:const "c" T)`. -/
def constT (c : String) (ty : Tm) : Tm := ex [sym "hol:const", str c, ty]
/-- `(hol:comb F X)`. -/
def combT (f x : Tm) : Tm := ex [sym "hol:comb", f, x]
/-- `bool`. -/
def boolT : Tm := tyappT "bool" []
/-- `A → B`. -/
def funT (a b : Tm) : Tm := tyappT "fun" [a, b]
/-- `s = t` at type `A`. -/
def eqT (a s t : Tm) : Tm := combT (combT (constT "=" (funT a (funT a boolT))) s) t
/-- `(set M₁ … Mₙ)`. -/
def setT (ms : List Tm) : Tm := ex (sym "set" :: ms)

/-! ## The encoding -/

/-- HOL Light's spelling of a type operator's name. -/
def opName : TypeOp → String
  | .mk n _ => (sourceOperatorName n).component

/-- A constant's name. -/
def constName : Const → String
  | .mk n _ => n.component

mutual

/-- **A type as a kernel term.** -/
def encTy : Ty → Tm
  | .var n => tyvarT n.component
  | .op op args => tyappT (opName op) (encTys args)

/-- Types as kernel terms. -/
def encTys : List Ty → List Tm
  | [] => []
  | a :: as => encTy a :: encTys as

end

theorem encTys_eq_map : ∀ ts : List Ty, encTys ts = ts.map encTy
  | [] => rfl
  | a :: as => by simp [encTys, encTys_eq_map as]

/-- **A de Bruijn term as a kernel term**: the index `i` stays `i`. -/
def encDB : DBTerm → Tm
  | .const c ty => constT (constName c) (encTy ty)
  | .free v => varT v.name.component (encTy v.ty)
  | .bound i => .idx i
  | .app f x => combT (encDB f) (encDB x)
  | .abs ty b => bnd (encTy ty) (encDB b)

/-- A checked term as a kernel term. -/
def encCT (t : CanonicalTerm) : Tm := encDB t.term

/-- **The set term `S` stands for the hypotheses `H`**: its members are exactly their encodings, in
any order, repetitions allowed. -/
def EncSet (s : Tm) (H : Finset CanonicalTerm) : Prop :=
  ∃ ms, setMembers s = some ms ∧ ∀ x, x ∈ ms ↔ ∃ h ∈ H, encCT h = x

/-! ## The primitive types and equality -/

/-- `bool` keeps its name: the swap of `->` and `fun` leaves it. -/
theorem sourceOperatorName_bool : sourceOperatorName (Name.global "bool") = Name.global "bool" :=
  Equiv.swap_apply_of_ne_of_ne (by simp [Name.global]) (by simp [Name.global])

@[simp] theorem encTy_bool : encTy Ty.bool = boolT := by
  simp only [Ty.bool, TypeOp.bool, encTy, encTys, opName, sourceOperatorName_bool, boolT]
  rfl

@[simp] theorem encTy_function (a b : Ty) : encTy (Ty.function a b) = funT (encTy a) (encTy b) := by
  simp only [Ty.function, TypeOp.function, encTy, encTys, opName, funT]
  rw [show sourceOperatorName (Name.global "->") = Name.global "fun" from
    Mettapedia.Languages.HOLLight.DefinitionAdapters.sourceOperatorName_arrow]
  rfl

@[simp] theorem encTy_equality (a : Ty) :
    encTy (Ty.equality a) = funT (encTy a) (funT (encTy a) boolT) := by
  simp [Ty.equality]

@[simp] theorem encDB_equalityDB (a : Ty) (l r : DBTerm) :
    encDB (CanonicalTerm.equalityDB a l r) = eqT (encTy a) (encDB l) (encDB r) := by
  simp [CanonicalTerm.equalityDB, encDB, eqT, Const.equality, constName, Name.global]

/-! ## Patterns of the rules at encoded values -/

theorem boolP_inst (σ : Subst ℕ Tm) : boolP.inst σ = some boolT := rfl

theorem funP_inst (σ : Subst ℕ Tm) {a b : Pat} {av bv : Tm} (ha : a.inst σ = some av)
    (hb : b.inst σ = some bv) : (funP a b).inst σ = some (funT av bv) := by
  simp [funP, tyappP, pex, pflds, psym, pstr, TreePat.inst, TreePatFields.inst, ha, hb, funT,
    tyappT, ex, flds, sym, str]

theorem eqP_inst (σ : Subst ℕ Tm) {a s t : Pat} {av sv tv : Tm} (ha : a.inst σ = some av)
    (hs : s.inst σ = some sv) (ht : t.inst σ = some tv) :
    (eqP a s t).inst σ = some (eqT av sv tv) := by
  simp [eqP, eqTyP, combP, constP, funP, tyappP, boolP, pex, pflds, psym, pstr, TreePat.inst,
    TreePatFields.inst, ha, hs, ht, eqT, combT, constT, funT, tyappT, boolT, ex, flds, sym, str]

/-! ## Encoded checked terms are locally closed -/

mutual

/-- Types have no bound variables. -/
theorem encTy_supported (k : ℕ) : ∀ ty : Ty, Term.supportedAt k (encTy ty) = true
  | .var _ => by simp [encTy, tyvarT, ex, flds, sym, str, Term.supportedAt, Term.Fields.supportedAt]
  | .op _ args => by
      simp only [encTy, tyappT, ex, flds, sym, str, Term.supportedAt, Term.Fields.supportedAt,
        Bool.true_and]
      exact encTys_supported k args

theorem encTys_supported (k : ℕ) :
    ∀ ts : List Ty, Term.Fields.supportedAt k (flds (encTys ts)) = true
  | [] => rfl
  | a :: as => by
      simp only [encTys, flds, Term.Fields.supportedAt, Nat.add_zero, encTy_supported k a,
        encTys_supported k as, Bool.and_self]

end

/-- A term that type checks under `k` binders has its indices below `k`. -/
theorem encDB_supported : ∀ (t : DBTerm) (ctx : List Ty) (ty : Ty),
    DBTerm.inferType ctx t = some ty → Term.supportedAt ctx.length (encDB t) = true
  | .const _ _, _, _, _ => by
      simp [encDB, constT, ex, flds, sym, str, Term.supportedAt, Term.Fields.supportedAt,
        encTy_supported]
  | .free _, _, _, _ => by
      simp [encDB, varT, ex, flds, sym, str, Term.supportedAt, Term.Fields.supportedAt,
        encTy_supported]
  | .bound i, ctx, ty, h => by
      simp only [DBTerm.inferType] at h
      simp only [encDB, Term.supportedAt, decide_eq_true_eq]
      exact (List.getElem?_eq_some_iff.mp h).1
  | .app f x, ctx, ty, h => by
      simp only [DBTerm.inferType, Option.bind_eq_bind] at h
      cases hf : DBTerm.inferType ctx f with
      | none => simp [hf] at h
      | some fty =>
        cases hx : DBTerm.inferType ctx x with
        | none => simp [hf, hx] at h
        | some xty =>
          simp [encDB, combT, ex, flds, sym, Term.supportedAt, Term.Fields.supportedAt,
            encDB_supported f ctx fty hf, encDB_supported x ctx xty hx]
  | .abs a b, ctx, ty, h => by
      simp only [DBTerm.inferType, Option.bind_eq_bind] at h
      cases hb : DBTerm.inferType (a :: ctx) b with
      | none => simp [hb] at h
      | some bty =>
        have := encDB_supported b (a :: ctx) bty hb
        simp only [List.length_cons] at this
        simp [encDB, bnd, Term.supportedAt, Term.Fields.supportedAt, encTy_supported, this]
/-- A checked term's encoding is locally closed. -/
theorem encCT_supported (t : CanonicalTerm) : Term.supportedAt 0 (encCT t) = true :=
  encDB_supported t.term [] t.ty t.checked

/-! ## Injectivity over a signature

HOL Light's names are global, and it identifies a type operator by its name. Over a signature
`opOf`, which gives the operator of each name, the encoding of types is injective
(`encTy_inj`). Example: two operators that differ only in provenance are one name, so they are not
both in one signature. -/

/-- A name without namespace, as HOL Light's names are. -/
def NameGlobal (n : Name) : Prop := n.namespaceComponents = []

theorem name_eq_of_global {m n : Name} (hm : NameGlobal m) (hn : NameGlobal n)
    (h : m.component = n.component) : m = n := by
  cases m; cases n
  simp only [NameGlobal] at hm hn
  simp_all

mutual

/-- **A type over the signature `opOf`**: its type variables have global names, and each of its
operators is the signature's operator of its HOL Light name. -/
def TyOverSig (opOf : String → TypeOp) : Ty → Prop
  | .var n => NameGlobal n
  | .op op args => op = opOf (opName op) ∧ TysOverSig opOf args

/-- Every type of the list is over the signature. -/
def TysOverSig (opOf : String → TypeOp) : List Ty → Prop
  | [] => True
  | a :: as => TyOverSig opOf a ∧ TysOverSig opOf as

end

theorem flds_inj : ∀ {xs ys : List Tm}, flds xs = flds ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [flds] at h
  | _ :: _, [], h => by simp [flds] at h
  | x :: xs, y :: ys, h => by
      simp only [flds, Fields.cons.injEq, true_and] at h
      rw [h.1, flds_inj h.2]

mutual

/-- **The encoding of types is injective over a signature.** -/
theorem encTy_inj (opOf : String → TypeOp) :
    ∀ {a b : Ty}, TyOverSig opOf a → TyOverSig opOf b → encTy a = encTy b → a = b
  | .var m, .var n, hm, hn, h => by
      simp only [encTy, tyvarT, ex, flds, sym, str, Term.node.injEq, Fields.cons.injEq,
        Head.str.injEq, true_and, and_true] at h
      rw [name_eq_of_global (by simpa [TyOverSig] using hm) (by simpa [TyOverSig] using hn) h]
  | .op o as, .op p bs, ⟨ho, has⟩, ⟨hp, hbs⟩, h => by
      simp only [encTy, tyappT, ex, flds, sym, str, Term.node.injEq, Fields.cons.injEq,
        Head.str.injEq, true_and, and_true] at h
      have hop : o = p := by rw [ho, hp, h.1]
      rw [hop, encTys_inj opOf has hbs (flds_inj h.2)]
  | .var _, .op _ _, _, _, h => by
      simp [encTy, tyvarT, tyappT, ex, flds, sym, str] at h
  | .op _ _, .var _, _, _, h => by
      simp [encTy, tyvarT, tyappT, ex, flds, sym, str] at h

theorem encTys_inj (opOf : String → TypeOp) :
    ∀ {as bs : List Ty}, TysOverSig opOf as → TysOverSig opOf bs → encTys as = encTys bs → as = bs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [encTys] at h
  | _ :: _, [], _, _, h => by simp [encTys] at h
  | a :: as, b :: bs, ⟨ha, has⟩, ⟨hb, hbs⟩, h => by
      simp only [encTys, List.cons.injEq] at h
      rw [encTy_inj opOf ha hb h.1, encTys_inj opOf has hbs h.2]

end

end Mettapedia.Logic.TierZero.Adequacy.HOL
