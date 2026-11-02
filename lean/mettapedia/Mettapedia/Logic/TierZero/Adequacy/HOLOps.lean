import Mettapedia.Logic.TierZero.Adequacy.HOLEnc

/-!
# The kernel's binder operations on encoded HOL terms

The kernel computes `open`, `abstract` and `subst` on kernel terms; the HOL Light specification
computes beta instantiation, abstraction and substitution on de Bruijn terms. On encoded terms they
agree:

* `encDB_instantiateAt`, `openT_encDB`: opening an encoded body with an encoded closed argument is
  the encoding of the specification's `DBTerm.instantiateAt` (the beta reduct of
  `BetaReductionSemantics`). Example: the body `(hol:comb F (bv 0))` opened with `(hol:var "y" T)` is
  `(hol:comb F (hol:var "y" T))`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOL

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Languages.OpenTheory

/-! ## Opening -/

mutual

/-- Instantiation leaves a type unchanged: types have no bound variables. -/
theorem encTy_instantiateAt (d : ℕ) (v : Tm) : ∀ ty : Ty, Term.instantiateAt d v (encTy ty) = encTy ty
  | .var _ => by
      simp [encTy, tyvarT, ex, flds, sym, str, Term.instantiateAt, Term.Fields.instantiateAt]
  | .op _ args => by
      simp only [encTy, tyappT, ex, flds, sym, str, Term.instantiateAt, Term.Fields.instantiateAt,
        encTys_instantiateAt d v args]

theorem encTys_instantiateAt (d : ℕ) (v : Tm) :
    ∀ ts : List Ty, Term.Fields.instantiateAt d v (flds (encTys ts)) = flds (encTys ts)
  | [] => rfl
  | a :: as => by
      simp only [encTys, flds, Term.Fields.instantiateAt, Nat.add_zero, encTy_instantiateAt d v a,
        encTys_instantiateAt d v as]

end

/-- **Opening commutes with the encoding**: for a closed argument `r` and a body without indices
above `d`, the kernel's instantiation at `d` is the specification's. -/
theorem encDB_instantiateAt (r : DBTerm) (hr : Term.supportedAt 0 (encDB r) = true) :
    ∀ (t : DBTerm) (d : ℕ), Term.supportedAt (d + 1) (encDB t) = true →
      encDB (DBTerm.instantiateAt r d t) = Term.instantiateAt d (encDB r) (encDB t)
  | .const c ty, d, _ => by
      simp [DBTerm.instantiateAt, encDB, constT, ex, flds, sym, str, Term.instantiateAt,
        Term.Fields.instantiateAt, encTy_instantiateAt]
  | .free x, d, _ => by
      simp [DBTerm.instantiateAt, encDB, varT, ex, flds, sym, str, Term.instantiateAt,
        Term.Fields.instantiateAt, encTy_instantiateAt]
  | .bound i, d, h => by
      simp only [encDB, Term.supportedAt, decide_eq_true_eq] at h
      by_cases hi : i = d
      · subst hi
        simp [encDB, Term.instantiateAt, Term.lift_of_supported 0 i (encDB r) hr]
      · have hlt : i < d := by omega
        simp [DBTerm.instantiateAt, encDB, Term.instantiateAt, hi, hlt]
  | .app f x, d, h => by
      simp only [encDB, combT, ex, flds, sym, Term.supportedAt, Term.Fields.supportedAt,
        Nat.add_zero, Bool.and_eq_true] at h
      simp only [DBTerm.instantiateAt, encDB, combT, ex, flds, sym, Term.instantiateAt,
        Term.Fields.instantiateAt, Nat.add_zero, encDB_instantiateAt r hr f d h.2.1,
        encDB_instantiateAt r hr x d h.2.2.1]
  | .abs ty b, d, h => by
      simp only [encDB, bnd, Term.supportedAt, Term.Fields.supportedAt, Nat.add_zero,
        Bool.and_eq_true] at h
      simp only [DBTerm.instantiateAt, encDB, bnd, Term.instantiateAt, Term.Fields.instantiateAt,
        Nat.add_zero, encTy_instantiateAt, encDB_instantiateAt r hr b (d + 1) h.2.1]

/-- **The kernel's `open` is the specification's beta instantiation** on encoded terms. -/
theorem openT_encDB (b r : DBTerm) (hb : Term.supportedAt 1 (encDB b) = true)
    (hr : Term.supportedAt 0 (encDB r) = true) :
    openT (encDB b) (encDB r) = encDB (DBTerm.instantiateAt r 0 b) :=
  (encDB_instantiateAt r hr b 0 hb).symm

/-! ## Abstraction

The kernel abstracts a variable by comparing subterms with its encoding; the specification by
`sourceVarSame`. They agree on variables over a signature (`encVar_eq_iff`), and no subterm of an
encoded type is a variable, so annotations stay as they are (`abstractAt_encTy`). -/

/-- A variable over the signature: a global name and a type over the signature. -/
def VarOverSig (opOf : String → TypeOp) (v : SourceVar) : Prop :=
  NameGlobal v.name ∧ TyOverSig opOf v.ty

/-- The encoding of a variable. -/
def encVar (v : SourceVar) : Tm := varT v.name.component (encTy v.ty)

theorem encDB_free (v : SourceVar) : encDB (.free v) = encVar v := rfl

/-- **Two variables over a signature have one encoding exactly when the specification identifies
them.** -/
theorem encVar_eq_iff (opOf : String → TypeOp) {v w : SourceVar} (hv : VarOverSig opOf v)
    (hw : VarOverSig opOf w) : encVar v = encVar w ↔ sourceVarSame v w = true := by
  constructor
  · intro h
    simp only [encVar, varT, ex, flds, sym, str, Term.node.injEq, Fields.cons.injEq, Head.str.injEq,
      true_and, and_true] at h
    have hn : v.name = w.name := name_eq_of_global hv.1 hw.1 h.1
    have ht : v.ty = w.ty := encTy_inj opOf hv.2 hw.2 h.2
    simp [sourceVarSame, hn, ht]
  · intro h
    simp only [sourceVarSame, Bool.and_eq_true, decide_eq_true_eq, Ty.same_eq_true_iff] at h
    simp [encVar, h.1, h.2]

theorem encVar_supported (v : SourceVar) (k : ℕ) : Term.supportedAt k (encVar v) = true := by
  simp [encVar, varT, ex, flds, sym, str, Term.supportedAt, Term.Fields.supportedAt,
    encTy_supported]

theorem lift_encVar (v : SourceVar) (d : ℕ) : Term.lift 0 d (encVar v) = encVar v :=
  Term.lift_of_supported 0 d _ (encVar_supported v 0)

mutual

/-- No subterm of an encoded type is an encoded variable, so abstracting one leaves a type. -/
theorem abstractAt_encTy (v : SourceVar) (d : ℕ) :
    ∀ ty : Ty, abstractAt (encVar v) d (encTy ty) = encTy ty
  | .var _ => by
      simp only [encTy, tyvarT, ex, flds, sym, str, abstractAt, abstractFields, lift_encVar]
      simp [encVar, varT, ex, flds, sym, str]
  | .op _ args => by
      simp only [encTy, tyappT, ex, flds, sym, str, abstractAt, abstractFields, lift_encVar,
        Nat.add_zero, encTys_abstract v d args]
      simp [encVar, varT, ex, flds, sym, str]

theorem encTys_abstract (v : SourceVar) (d : ℕ) :
    ∀ ts : List Ty, abstractFields (encVar v) d (flds (encTys ts)) = flds (encTys ts)
  | [] => rfl
  | a :: as => by
      simp only [encTys, flds, abstractFields, Nat.add_zero, abstractAt_encTy v d a,
        encTys_abstract v d as]

end

/-- Every free variable of a term is over the signature. -/
def FreeOverSig (opOf : String → TypeOp) : DBTerm → Prop
  | .const _ _ => True
  | .free w => VarOverSig opOf w
  | .bound _ => True
  | .app f x => FreeOverSig opOf f ∧ FreeOverSig opOf x
  | .abs _ b => FreeOverSig opOf b

theorem abstractAt_node_eq (x : Tm) (h : Head) (fs : Fields Head) (d : ℕ)
    (heq : Term.lift 0 d x = .node h fs) : abstractAt x d (.node h fs) = .idx d := by
  simp [abstractAt, heq]

theorem abstractAt_node_ne (x : Tm) (h : Head) (fs : Fields Head) (d : ℕ)
    (hne : Term.lift 0 d x ≠ .node h fs) :
    abstractAt x d (.node h fs) = .node h (abstractFields x d fs) := by
  simp [abstractAt, hne]

theorem abstractAt_encVar_sym (v : SourceVar) (d : ℕ) (s : String) :
    abstractAt (encVar v) d (sym s) = sym s := by
  rw [sym, abstractAt_node_ne _ _ _ _ (by rw [lift_encVar]; simp [encVar, varT, ex, flds])]
  rfl

theorem abstractAt_encVar_str (v : SourceVar) (d : ℕ) (s : String) :
    abstractAt (encVar v) d (str s) = str s := by
  rw [str, abstractAt_node_ne _ _ _ _ (by rw [lift_encVar]; simp [encVar, varT, ex, flds])]
  rfl

/-- **Abstraction commutes with the encoding**: for a variable and a term over the signature, with
no index at or above `d`, the kernel's `abstract` is the specification's `closeFreeAt`. -/
theorem encDB_closeFreeAt (opOf : String → TypeOp) (v : SourceVar) (hv : VarOverSig opOf v) :
    ∀ (t : DBTerm) (d : ℕ), FreeOverSig opOf t → Term.supportedAt d (encDB t) = true →
      encDB (DBTerm.closeFreeAt v d t) = abstractAt (encVar v) d (encDB t)
  | .const c ty, d, _, _ => by
      simp only [DBTerm.closeFreeAt, encDB, constT, ex]
      rw [abstractAt_node_ne _ _ _ _ (by rw [lift_encVar]; simp [encVar, varT, ex, flds, sym, str])]
      simp only [flds, abstractFields, Nat.add_zero, abstractAt_encVar_sym, abstractAt_encVar_str,
        abstractAt_encTy]
  | .free w, d, hw, _ => by
      by_cases h : sourceVarSame v w = true
      · have e : encVar v = encVar w := (encVar_eq_iff opOf hv hw).mpr h
        simp only [DBTerm.closeFreeAt, h, if_true]
        rw [encDB_free, ← e]
        exact (abstractAt_node_eq (encVar v) .expr
          (flds [sym "hol:var", str v.name.component, encTy v.ty]) d (lift_encVar v d)).symm
      · have e : encVar v ≠ encVar w := fun e => h ((encVar_eq_iff opOf hv hw).mp e)
        simp only [DBTerm.closeFreeAt, h, Bool.false_eq_true, if_false]
        rw [encDB_free, show encVar w = Term.node .expr
          (flds [sym "hol:var", str w.name.component, encTy w.ty]) from rfl]
        rw [abstractAt_node_ne _ _ _ _ (by rw [lift_encVar]; exact e)]
        simp only [flds, abstractFields, Nat.add_zero, abstractAt_encVar_sym, abstractAt_encVar_str,
          abstractAt_encTy]
  | .bound i, d, _, hs => by
      simp only [encDB, Term.supportedAt, decide_eq_true_eq] at hs
      simp only [DBTerm.closeFreeAt, encDB, abstractAt, lift_encVar]
      simp [encVar, varT, ex, hs]
  | .app f x, d, ⟨hf, hx⟩, hs => by
      simp only [encDB, combT, ex, flds, sym, Term.supportedAt, Term.Fields.supportedAt,
        Nat.add_zero, Bool.and_eq_true] at hs
      simp only [DBTerm.closeFreeAt, encDB, combT, ex]
      rw [abstractAt_node_ne _ _ _ _ (by rw [lift_encVar]; simp [encVar, varT, ex, flds, sym, str])]
      simp only [flds, abstractFields, Nat.add_zero, abstractAt_encVar_sym,
        ← encDB_closeFreeAt opOf v hv f d hf hs.2.1, ← encDB_closeFreeAt opOf v hv x d hx hs.2.2.1]
  | .abs ty b, d, hb, hs => by
      simp only [encDB, bnd, Term.supportedAt, Term.Fields.supportedAt, Nat.add_zero,
        Bool.and_eq_true] at hs
      simp only [DBTerm.closeFreeAt, encDB, bnd]
      rw [abstractAt_node_ne _ _ _ _ (by rw [lift_encVar]; simp [encVar, varT, ex, flds, sym, str])]
      simp only [abstractFields, Nat.add_zero, abstractAt_encTy,
        ← encDB_closeFreeAt opOf v hv b (d + 1) hb hs.2.1]

/-! ## Free occurrence -/

theorem occursAt_encVar_sym (v : SourceVar) (d : ℕ) (s : String) :
    occursAt (encVar v) d (sym s) = false := by
  simp only [sym, occursAt, occursFields, lift_encVar, Bool.or_false]
  simp [encVar, varT, ex, flds]

theorem occursAt_encVar_str (v : SourceVar) (d : ℕ) (s : String) :
    occursAt (encVar v) d (str s) = false := by
  simp only [str, occursAt, occursFields, lift_encVar, Bool.or_false]
  simp [encVar, varT, ex, flds]

/-- An encoded variable is no other expression headed by a symbol. -/
theorem encVar_ne_sym_head (v : SourceVar) (s : String) (hs : s ≠ "hol:var") (rest : Fields Head) :
    encVar v ≠ Term.node .expr (Fields.cons 0 (sym s) rest) := by
  intro h
  simp only [encVar, varT, ex, flds, sym, Term.node.injEq, Fields.cons.injEq, Head.sym.injEq,
    true_and] at h
  exact hs h.1.1.symm

mutual

/-- An encoded variable occurs in no encoded type. -/
theorem occursAt_encTy (v : SourceVar) (d : ℕ) : ∀ ty : Ty, occursAt (encVar v) d (encTy ty) = false
  | .var _ => by
      simp only [encTy, tyvarT, ex, flds, occursAt, occursFields, lift_encVar, Nat.add_zero,
        occursAt_encVar_sym, occursAt_encVar_str, Bool.or_false,
        decide_eq_false (encVar_ne_sym_head v "hol:tyvar" (by decide) _)]
  | .op _ args => by
      simp only [encTy, tyappT, ex, flds, occursAt, occursFields, lift_encVar, Nat.add_zero,
        occursAt_encVar_sym, occursAt_encVar_str, Bool.false_or, occursTys_encTy v d args,
        decide_eq_false (encVar_ne_sym_head v "hol:tyapp" (by decide) _)]

theorem occursTys_encTy (v : SourceVar) (d : ℕ) :
    ∀ ts : List Ty, occursFields (encVar v) d (flds (encTys ts)) = false
  | [] => rfl
  | a :: as => by
      simp only [encTys, flds, occursFields, Nat.add_zero, occursAt_encTy v d a,
        occursTys_encTy v d as, Bool.or_self]

end

theorem occursAt_encVar_encVar (v w : SourceVar) (d : ℕ) :
    occursAt (encVar v) d (encVar w) = decide (encVar v = encVar w) := by
  have hw : encVar w = Term.node .expr (flds [sym "hol:var", str w.name.component, encTy w.ty]) :=
    rfl
  rw [hw]
  simp only [flds, occursAt, occursFields, lift_encVar, Nat.add_zero, occursAt_encVar_sym,
    occursAt_encVar_str, occursAt_encTy, Bool.or_false]
  exact decide_eq_decide.mpr Iff.rfl

/-- **The kernel's occurrence test is the specification's free occurrence** on encoded terms over
the signature. -/
theorem occursAt_encDB_iff (opOf : String → TypeOp) (v : SourceVar) (hv : VarOverSig opOf v) :
    ∀ (t : DBTerm) (d : ℕ), FreeOverSig opOf t →
      (occursAt (encVar v) d (encDB t) = true ↔ DBTerm.FreeOccurrence v t)
  | .const c ty, d, _ => by
      simp only [encDB, constT, ex, flds, occursAt, occursFields, lift_encVar, Nat.add_zero,
        occursAt_encVar_sym, occursAt_encVar_str, occursAt_encTy, Bool.or_false,
        decide_eq_false (encVar_ne_sym_head v "hol:const" (by decide) _), Bool.false_eq_true,
        false_iff]
      intro h; cases h
  | .free w, d, hw => by
      rw [encDB_free, occursAt_encVar_encVar, decide_eq_true_iff, encVar_eq_iff opOf hv hw]
      constructor
      · intro hs
        simp only [sourceVarSame, Bool.and_eq_true, decide_eq_true_eq, Ty.same_eq_true_iff] at hs
        have : v = w := by cases v; cases w; simp_all
        subst this
        exact .here
      · intro h
        cases h
        simp [sourceVarSame]
  | .bound i, d, _ => by
      simp only [encDB, occursAt, lift_encVar, decide_eq_true_eq]
      constructor
      · intro h; simp [encVar, varT, ex] at h
      · intro h; cases h
  | .app f x, d, ⟨hf, hx⟩ => by
      simp only [encDB, combT, ex, flds, occursAt, occursFields, lift_encVar, Nat.add_zero,
        occursAt_encVar_sym, Bool.false_or, Bool.or_false,
        decide_eq_false (encVar_ne_sym_head v "hol:comb" (by decide) _), Bool.or_eq_true,
        occursAt_encDB_iff opOf v hv f d hf, occursAt_encDB_iff opOf v hv x d hx]
      constructor
      · rintro (h | h)
        · exact .appFunction h
        · exact .appArgument h
      · intro h
        cases h with
        | appFunction h => exact Or.inl h
        | appArgument h => exact Or.inr h
  | .abs ty b, d, hb => by
      have hne : encVar v ≠ Term.node .bind
          (Fields.cons 0 (encTy ty) (Fields.cons 1 (encDB b) Fields.nil)) := by
        simp [encVar, varT, ex, flds]
      simp only [encDB, bnd, occursAt, occursFields, lift_encVar, Nat.add_zero, occursAt_encTy,
        Bool.false_or, Bool.or_false, decide_eq_false hne, occursAt_encDB_iff opOf v hv b (d + 1) hb]
      constructor
      · exact .absBody
      · intro h; cases h with | absBody h => exact h

/-! ## Type substitution

INST_TYPE's substitution `S` (type variable names to types) as kernel pairs: the key of `A ↦ T` is
`(hol:tyvar "A")`, its value the encoding of `T`. The kernel replaces whole subterms, the first key
winning, as `TypeSubst.lookup` does. -/

/-- The kernel pairs of a type substitution. -/
def encTypeSubst (S : TypeSubst) : List (Tm × Tm) :=
  S.entries.map fun e => (tyvarT e.1.component, encTy e.2)

/-- Every key of the substitution is a global name. -/
def TypeSubstGlobal (S : TypeSubst) : Prop := ∀ e ∈ S.entries, NameGlobal e.1

theorem lift_tyvarT (c : String) (d : ℕ) : Term.lift 0 d (tyvarT c) = tyvarT c :=
  Term.lift_of_supported 0 d _ (by simp [tyvarT, ex, flds, sym, str, Term.supportedAt,
    Term.Fields.supportedAt])

theorem lift_encTy (ty : Ty) (d : ℕ) : Term.lift 0 d (encTy ty) = encTy ty :=
  Term.lift_of_supported 0 d _ (encTy_supported 0 ty)

theorem tyvarT_inj {m n : Name} (hm : NameGlobal m) (hn : NameGlobal n) :
    tyvarT m.component = tyvarT n.component ↔ m = n := by
  constructor
  · intro h
    simp only [tyvarT, ex, flds, sym, str, Term.node.injEq, Fields.cons.injEq, Head.str.injEq,
      true_and, and_true] at h
    exact name_eq_of_global hm hn h
  · rintro rfl; rfl

/-- The kernel's lookup of a type variable is the substitution's lookup. -/
theorem lookupAt_encTypeSubst (es : List (Name × Ty)) (hes : ∀ e ∈ es, NameGlobal e.1)
    {n : Name} (hn : NameGlobal n) (d : ℕ) :
    lookupAt (es.map fun e => (tyvarT e.1.component, encTy e.2)) d (tyvarT n.component) =
      (es.lookup n).map encTy := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      have he : NameGlobal e.1 := hes e (by simp)
      have ih' := ih (fun x hx => hes x (by simp [hx]))
      simp only [lookupAt, List.map_cons, List.find?_cons, lift_tyvarT] at ih' ⊢
      by_cases h : e.1 = n
      · subst h
        simp [lift_encTy, List.lookup]
      · have : ¬ tyvarT e.1.component = tyvarT n.component := fun e' => h ((tyvarT_inj he hn).mp e')
        have hb : (n == e.1) = false := by
          rw [beq_eq_false_iff_ne]; exact fun h' => h h'.symm
        simp only [this, decide_false]
        rw [ih']
        simp only [List.lookup, hb]
/-- A term that is no key's lift is not found. -/
theorem lookupAt_none_of (s : List (Tm × Tm)) (d : ℕ) (t : Tm)
    (h : ∀ p ∈ s, Term.lift 0 d p.1 ≠ t) : lookupAt s d t = none := by
  simp only [lookupAt, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  exact h

theorem tyvarT_ne_sym (c s : String) : tyvarT c ≠ sym s := by simp [tyvarT, ex, flds, sym]
theorem tyvarT_ne_str (c s : String) : tyvarT c ≠ str s := by simp [tyvarT, ex, flds, str]
theorem tyvarT_ne_tyappT (c op : String) (args : List Tm) : tyvarT c ≠ tyappT op args := by
  simp [tyvarT, tyappT, ex, flds, sym]

theorem substAt_typeSubst_leaf (S : TypeSubst) (d : ℕ) (t : Tm) (ht : ∀ c, tyvarT c ≠ t)
    (hleaf : ∃ h, t = Term.node h .nil) : substAt (encTypeSubst S) d t = t := by
  obtain ⟨h, rfl⟩ := hleaf
  have hn : lookupAt (encTypeSubst S) d (Term.node h .nil) = none := by
    apply lookupAt_none_of
    intro p hp
    simp only [encTypeSubst, List.mem_map] at hp
    obtain ⟨e, -, rfl⟩ := hp
    rw [lift_tyvarT]; exact ht _
  simp [substAt, hn, substFields]

mutual

/-- **Type substitution commutes with the encoding**: the kernel's `subst` with the pairs of `S`
is `S.apply`, on types whose type variables have global names. -/
theorem substAt_encTy (opOf : String → TypeOp) (S : TypeSubst) (hS : TypeSubstGlobal S) (d : ℕ) :
    ∀ ty : Ty, TyOverSig opOf ty → substAt (encTypeSubst S) d (encTy ty) = encTy (S.apply ty)
  | .var n, hn => by
      have hn' : NameGlobal n := by simpa [TyOverSig] using hn
      have hl := lookupAt_encTypeSubst S.entries hS hn' d
      simp only [encTy]
      rw [show tyvarT n.component = Term.node .expr (flds [sym "hol:tyvar", str n.component]) from rfl]
      simp only [substAt]
      rw [show Term.node .expr (flds [sym "hol:tyvar", str n.component]) = tyvarT n.component
        from rfl, show encTypeSubst S = S.entries.map (fun e => (tyvarT e.1.component, encTy e.2))
        from rfl, hl]
      cases hT : S.entries.lookup n with
      | some T => simp [TypeSubst.lookup, hT]
      | none =>
          simp only [Option.map_none, TypeSubst.apply, TypeSubst.lookup, hT, Option.getD_none,
            encTy, flds, substFields, Nat.add_zero]
          rw [← encTypeSubst, substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_sym c _) ⟨_, rfl⟩,
            substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_str c _) ⟨_, rfl⟩]
          rfl
  | .op op args, ⟨_, hargs⟩ => by
      have hn : lookupAt (encTypeSubst S) d (tyappT (opName op) (encTys args)) = none := by
        apply lookupAt_none_of
        intro p hp
        simp only [encTypeSubst, List.mem_map] at hp
        obtain ⟨e, -, rfl⟩ := hp
        rw [lift_tyvarT]; exact tyvarT_ne_tyappT _ _ _
      simp only [encTy]
      rw [show tyappT (opName op) (encTys args) = Term.node .expr
        (flds (sym "hol:tyapp" :: str (opName op) :: encTys args)) from rfl] at hn ⊢
      simp only [flds] at hn
      simp only [substAt, flds, hn, substFields, Nat.add_zero]
      rw [substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_sym c _) ⟨_, rfl⟩,
        substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_str c _) ⟨_, rfl⟩,
        substTys_encTy opOf S hS d args hargs, TypeSubst.apply]
      rfl

theorem substTys_encTy (opOf : String → TypeOp) (S : TypeSubst) (hS : TypeSubstGlobal S) (d : ℕ) :
    ∀ ts : List Ty, TysOverSig opOf ts →
      substFields (encTypeSubst S) d (flds (encTys ts)) = flds (encTys (ts.map S.apply))
  | [], _ => rfl
  | a :: as, ⟨ha, has⟩ => by
      simp only [encTys, List.map_cons, flds, substFields, Nat.add_zero,
        substAt_encTy opOf S hS d a ha, substTys_encTy opOf S hS d as has]

end

/-- Type substitution on an encoded variable instantiates its type annotation. -/
theorem substAt_encVar_types (opOf : String → TypeOp) (S : TypeSubst) (hS : TypeSubstGlobal S)
    (d : ℕ) (x : SourceVar) (hx : TyOverSig opOf x.ty) :
    substAt (encTypeSubst S) d (encVar x) = encVar (S.applyVar x) := by
  have hn : lookupAt (encTypeSubst S) d (encVar x) = none := by
    apply lookupAt_none_of
    intro p hp
    simp only [encTypeSubst, List.mem_map] at hp
    obtain ⟨e, -, rfl⟩ := hp
    rw [lift_tyvarT]
    simp [tyvarT, encVar, varT, ex, flds, sym]
  rw [show encVar x = Term.node .expr (flds [sym "hol:var", str x.name.component, encTy x.ty])
    from rfl] at hn ⊢
  simp only [flds] at hn
  simp only [substAt, flds, hn, substFields, Nat.add_zero]
  rw [substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_sym c _) ⟨_, rfl⟩,
    substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_str c _) ⟨_, rfl⟩,
    substAt_encTy opOf S hS d x.ty hx]
  rfl

/-- Every type annotation of a term (constants, variables, binders) is over the signature. -/
def AnnotOverSig (opOf : String → TypeOp) : DBTerm → Prop
  | .const _ ty => TyOverSig opOf ty
  | .free x => TyOverSig opOf x.ty
  | .bound _ => True
  | .app f x => AnnotOverSig opOf f ∧ AnnotOverSig opOf x
  | .abs ty b => TyOverSig opOf ty ∧ AnnotOverSig opOf b

/-- **INST_TYPE's action commutes with the encoding**: the kernel's `subst` with the pairs of `S`
is the specification's `applyDB` of the type-only substitution `⟨S, []⟩`. -/
theorem substAt_encDB_types (opOf : String → TypeOp) (S : TypeSubst) (hS : TypeSubstGlobal S) :
    ∀ (t : DBTerm) (d : ℕ), AnnotOverSig opOf t →
      substAt (encTypeSubst S) d (encDB t) = encDB (TermSubst.applyDB ⟨S, []⟩ t)
  | .const c ty, d, hty => by
      have hn : lookupAt (encTypeSubst S) d (encDB (.const c ty)) = none := by
        apply lookupAt_none_of
        intro p hp
        simp only [encTypeSubst, List.mem_map] at hp
        obtain ⟨e, -, rfl⟩ := hp
        rw [lift_tyvarT]; simp [tyvarT, encDB, constT, ex, flds, sym]
      simp only [encDB, constT, ex] at hn ⊢
      simp only [flds] at hn ⊢
      simp only [substAt, hn, substFields, Nat.add_zero]
      rw [substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_sym c _) ⟨_, rfl⟩,
        substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_str c _) ⟨_, rfl⟩,
        substAt_encTy opOf S hS d ty hty]
      simp [encDB, constT, ex, flds]
  | .free x, d, hx => by
      rw [encDB_free, substAt_encVar_types opOf S hS d x hx]
      simp [TermSubst.applyDB, TermSubst.lookup, encDB_free]
  | .bound i, d, _ => by
      have hn : lookupAt (encTypeSubst S) d (.idx i) = none := by
        apply lookupAt_none_of
        intro p hp
        simp only [encTypeSubst, List.mem_map] at hp
        obtain ⟨e, -, rfl⟩ := hp
        rw [lift_tyvarT]; simp [tyvarT, ex]
      simp [encDB, substAt, hn]
  | .app f x, d, ⟨hf, hx⟩ => by
      have hn : lookupAt (encTypeSubst S) d (encDB (.app f x)) = none := by
        apply lookupAt_none_of
        intro p hp
        simp only [encTypeSubst, List.mem_map] at hp
        obtain ⟨e, -, rfl⟩ := hp
        rw [lift_tyvarT]; simp [tyvarT, encDB, combT, ex, flds, sym]
      simp only [encDB, combT, ex] at hn ⊢
      simp only [flds] at hn ⊢
      simp only [substAt, hn, substFields, Nat.add_zero]
      rw [substAt_typeSubst_leaf S d _ (fun c => tyvarT_ne_sym c _) ⟨_, rfl⟩,
        substAt_encDB_types opOf S hS f d hf, substAt_encDB_types opOf S hS x d hx]
      simp [encDB, combT, ex, flds]
  | .abs ty b, d, ⟨hty, hb⟩ => by
      have hn : lookupAt (encTypeSubst S) d (encDB (.abs ty b)) = none := by
        apply lookupAt_none_of
        intro p hp
        simp only [encTypeSubst, List.mem_map] at hp
        obtain ⟨e, -, rfl⟩ := hp
        rw [lift_tyvarT]; simp [tyvarT, encDB, bnd, ex, flds]
      simp only [encDB, bnd] at hn ⊢
      simp only [substAt, hn, substFields, Nat.add_zero, substAt_encTy opOf S hS d ty hty,
        substAt_encDB_types opOf S hS b (d + 1) hb]
      simp [encDB, bnd]

end Mettapedia.Logic.TierZero.Adequacy.HOL
