import Mathlib.Data.List.Forall2

/-!
# Contract typing for PeTTa: values, types and the static rules

Values are terms with unbound logic variables; bindings only extend. An alias is expanded when
declared (`type_normalize/2`), so it is no type here. `Fits` is `typecheck_ok/2`: an unbound
value fits every type; a literal tag, an atom no declaration mentions, has the symbol itself as
its one value; a newtype is checked as its representation; a check cannot inspect a type
variable, rigid or not, so what a function returns at a rigid type is trusted. `inst` and
`compat` are the two strengths of evidence, and a static type `S` is the evidence `Has v S`.
`Est` is `est/2` on an instantiated static type, `Establishes` (`established/2`) chooses the
instance. `Conflict` is `conflict/2`, the static conventions of `consistent/2`, each with its
guarantee: atoms are disjoint; a union conflicts through a branch, which surely fails when atomic;
lists of conflicting atoms share only `()`; arrows conflict in a component (and raise at runtime,
`Checker.arrow_conflict_raises`); a rigid type meets only itself; a newtype is nominal.

Not modelled: intersections from occurrence typing, partial applications as values, foreign
values, metatypes, and `get-type` rules of the program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping

/-! ## Values -/

/-- Literals of the representation types. -/
inductive Lit where
  | num (n : Int)
  | str (s : String)
  | bool (b : Bool)
  deriving DecidableEq

/-- The representation types `Number`, `String` and `Bool`. -/
inductive Prim where
  | number | string | bool
  deriving DecidableEq

def Lit.prim : Lit → Prim
  | .num _ => .number
  | .str _ => .string
  | .bool _ => .bool

/-- Values. `app []` is `()`; a constructor application is `app (sym c :: fields)`. -/
inductive Term where
  | var (x : Nat)
  | lit (l : Lit)
  | sym (s : String)
  | app (xs : List Term)

namespace Term

mutual
/-- Extending the bindings: each unbound variable `x` becomes `θ x`. -/
def subst (θ : Nat → Term) : Term → Term
  | .var x => θ x
  | .lit l => .lit l
  | .sym s => .sym s
  | .app xs => .app (substList θ xs)
def substList (θ : Nat → Term) : List Term → List Term
  | [] => []
  | x :: xs => subst θ x :: substList θ xs
end

theorem substList_eq_map (θ : Nat → Term) : ∀ xs, substList θ xs = xs.map (subst θ)
  | [] => rfl
  | x :: xs => by rw [substList, substList_eq_map θ xs, List.map_cons]

@[simp] theorem subst_var (θ : Nat → Term) (x : Nat) : (var x).subst θ = θ x := rfl
@[simp] theorem subst_lit (θ : Nat → Term) (l : Lit) : (lit l).subst θ = lit l := rfl
@[simp] theorem subst_sym (θ : Nat → Term) (s : String) : (sym s).subst θ = sym s := rfl
@[simp] theorem subst_app (θ : Nat → Term) (xs : List Term) :
    (app xs).subst θ = app (xs.map (subst θ)) := by rw [subst, substList_eq_map]

theorem subst_id : ∀ v : Term, v.subst .var = v
  | .var _ | .lit _ | .sym _ => by simp
  | .app xs => by
      rw [subst_app]
      exact congrArg app ((List.map_congr_left fun x _ => subst_id x).trans (List.map_id xs))

theorem subst_subst (θ δ : Nat → Term) : ∀ v : Term,
    (v.subst θ).subst δ = v.subst (fun x => (θ x).subst δ)
  | .var _ | .lit _ | .sym _ => by simp
  | .app xs => by
      simp only [subst_app, List.map_map]
      exact congrArg app (List.map_congr_left fun x _ => subst_subst θ δ x)

/-- A ground value: no unbound variable. -/
inductive Closed : Term → Prop
  | lit (l : Lit) : Closed (.lit l)
  | sym (s : String) : Closed (.sym s)
  | app {xs : List Term} : (∀ x ∈ xs, Closed x) → Closed (.app xs)

theorem closed_subst {θ : Nat → Term} (hθ : ∀ x, (θ x).Closed) : ∀ v : Term, (v.subst θ).Closed
  | .var x => by simpa using hθ x
  | .lit l => .lit l
  | .sym s => .sym s
  | .app xs => by
      rw [subst_app]
      exact .app fun y hy => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy
        exact closed_subst hθ x

end Term

/-! ## Types and the value relation -/

inductive Ty where
  | prim (p : Prim)
  /-- A declared name, or a literal tag: an atom that no declaration mentions. -/
  | name (n : String)
  /-- A type variable. As a required type it is unknown; in a static type it ranges over
  every type. -/
  | var (a : Nat)
  /-- A type variable of a body's own declaration that the caller chooses (`body_contract/4`). -/
  | rigid (a : Nat)
  /-- `(: N (Newtype R))`. -/
  | newtype (n : String)
  /-- `%Undefined%`, and the wildcards `Atom` and `Expression`. -/
  | unknown
  | list (elem : Ty)
  | tuple (elems : List Ty)
  | arrow (args : List Ty) (res : Ty)
  | union (alts : List Ty)

namespace Ty

mutual
/-- Instantiating type variables. -/
def subst (σ : Nat → Ty) : Ty → Ty
  | .prim p => .prim p
  | .name n => .name n
  | .var a => σ a
  | .rigid a => .rigid a
  | .newtype n => .newtype n
  | .unknown => .unknown
  | .list T => .list (T.subst σ)
  | .tuple Ts => .tuple (substList σ Ts)
  | .arrow As R => .arrow (substList σ As) (R.subst σ)
  | .union Ts => .union (substList σ Ts)
def substList (σ : Nat → Ty) : List Ty → List Ty
  | [] => []
  | T :: Ts => subst σ T :: substList σ Ts
end

theorem substList_eq_map (σ : Nat → Ty) : ∀ Ts, substList σ Ts = Ts.map (subst σ)
  | [] => rfl
  | T :: Ts => by rw [substList, substList_eq_map σ Ts, List.map_cons]

mutual
theorem subst_id : ∀ T : Ty, T.subst .var = T
  | .prim _ | .name _ | .var _ | .rigid _ | .newtype _ | .unknown => rfl
  | .list T => by rw [subst, subst_id T]
  | .tuple Ts => by rw [subst, substList_id Ts]
  | .arrow As R => by rw [subst, substList_id As, subst_id R]
  | .union Ts => by rw [subst, substList_id Ts]
theorem substList_id : ∀ Ts : List Ty, substList .var Ts = Ts
  | [] => rfl
  | T :: Ts => by rw [substList, subst_id T, substList_id Ts]
end

/-- Neither a variable nor the unknown type. -/
def Known : Ty → Prop
  | .unknown | .var _ => False
  | _ => True

/-- Known, and not a union. -/
def Plain : Ty → Prop
  | .unknown | .var _ | .union _ => False
  | _ => True

/-- An atom of a type: a representation type, a name or a tag. -/
def Atom : Ty → Prop
  | .prim _ | .name _ => True
  | _ => False

def Compound : Ty → Prop
  | .list _ | .tuple _ | .arrow _ _ => True
  | _ => False

theorem not_atom_of_compound {T : Ty} (h : T.Compound) : ¬ T.Atom := by
  cases T <;> simp_all [Compound, Atom]

/-- `Number`, `String`, `Bool` and `(List _)`: types whose values are fixed by their
representation, whatever the program declares. -/
def Representation : Ty → Prop
  | .prim _ | .list _ => True
  | _ => False

mutual
/-- `nominal/1`: a newtype occurs in the type. -/
def nominal : Ty → Bool
  | .newtype _ => true
  | .list T => T.nominal
  | .tuple Ts | .union Ts => nominalList Ts
  | .arrow As R => nominalList As || R.nominal
  | _ => false
def nominalList : List Ty → Bool
  | [] => false
  | T :: Ts => T.nominal || nominalList Ts
end

end Ty

/-- The declarations a run consults. A declaration `(: s T)` at a representation type is
rejected (`representation_declaration_conflict`), so symbols are declared at names. -/
structure Sig where
  /-- `(: s N)` (`symbol_type/2`). -/
  symbols : List (String × String)
  /-- `(: c (-> A₁ .. Aₙ N))` for a constructor `c`, a declared function without equations. -/
  ctors : List (String × List Ty × String)
  /-- Functions and constructors with an arity they accept (`arity/2`). -/
  arities : List (String × Nat)
  /-- `(: N (Newtype R))`. -/
  newtypes : String → Option Ty

/-- `literal_tag/1`: no symbol or constructor is declared with `N`, and `N` is no newtype. -/
def Sig.tag (sig : Sig) (N : String) : Bool :=
  sig.symbols.all (·.2 != N) && sig.ctors.all (·.2.2 != N) && (sig.newtypes N).isNone

variable (sig : Sig)

/-- The value relation, `typecheck_ok/2`. Componentwise conditions are stated by position, so
that induction applies. -/
inductive Fits : Term → Ty → Prop
  | var (x : Nat) (T : Ty) : Fits (.var x) T
  | unknown (v : Term) : Fits v .unknown
  | tvar (v : Term) (a : Nat) : Fits v (.var a)
  | rigid (v : Term) (a : Nat) : Fits v (.rigid a)
  | lit (l : Lit) : Fits (.lit l) (.prim l.prim)
  | sym {s N : String} : (s, N) ∈ sig.symbols → Fits (.sym s) (.name N)
  | tag {N : String} : sig.tag N = true → Fits (.sym N) (.name N)
  | ctor {c N : String} {fs : List Term} {As : List Ty} : (c, As, N) ∈ sig.ctors →
      fs.length = As.length → (∀ i (h₁ : i < fs.length) (h₂ : i < As.length), Fits fs[i] As[i]) →
      Fits (.app (.sym c :: fs)) (.name N)
  | newtype {v : Term} {N : String} {R : Ty} : sig.newtypes N = some R → Fits v R →
      Fits v (.newtype N)
  | list {xs : List Term} {E : Ty} : (∀ x ∈ xs, Fits x E) → Fits (.app xs) (.list E)
  | tuple {xs : List Term} {Ts : List Ty} : xs.length = Ts.length →
      (∀ i (h₁ : i < xs.length) (h₂ : i < Ts.length), Fits xs[i] Ts[i]) →
      Fits (.app xs) (.tuple Ts)
  | arrow {f : String} {As : List Ty} {R : Ty} : (f, As.length) ∈ sig.arities →
      Fits (.sym f) (.arrow As R)
  | union {v : Term} {T : Ty} {Ts : List Ty} : T ∈ Ts → Fits v T → Fits v (.union Ts)

/-- A vector of values fits a vector of types. -/
def FitsAll (vs : List Term) (Ts : List Ty) : Prop := List.Forall₂ (Fits sig) vs Ts

theorem fitsAll_iff (vs : List Term) (Ts : List Ty) : FitsAll sig vs Ts ↔
    vs.length = Ts.length ∧ ∀ i (h₁ : i < vs.length) (h₂ : i < Ts.length), Fits sig vs[i] Ts[i] := by
  simp [FitsAll, List.forall₂_iff_get]

/-- At runtime a newtype is its representation. -/
theorem fits_newtype {N : String} {R : Ty} (hN : sig.newtypes N = some R) (v : Term) :
    Fits sig v (.newtype N) ↔ Fits sig v R := by
  refine ⟨fun h => ?_, .newtype hN⟩
  cases h with
  | var => exact .var _ _
  | newtype h' hv => exact (Option.some.inj (h'.symm.trans hN)) ▸ hv

/-- The test of a value against the declared type, whose variables are unknown, accepts every
value that the test against an instance accepts. -/
theorem Fits.of_subst {σ : Nat → Ty} {v : Term} {U : Ty} (h : Fits sig v U) :
    ∀ T : Ty, U = T.subst σ → Fits sig v T := by
  induction h with
  | var x _ => exact fun T _ => .var x T
  | unknown v => intro T hT; cases T <;> simp [Ty.subst] at hT <;> first | exact .unknown v | exact .tvar v _
  | tvar v b => intro T hT; cases T <;> simp [Ty.subst] at hT; exact .tvar v _
  | rigid v b => intro T hT; cases T <;> simp [Ty.subst] at hT <;> first | exact .tvar v _ | (subst hT; exact .rigid v _)
  | lit l => intro T hT; cases T <;> simp [Ty.subst] at hT <;> first | exact .tvar _ _ | (subst hT; exact .lit l)
  | sym hs => intro T hT; cases T <;> simp [Ty.subst] at hT <;> first | exact .tvar _ _ | (subst hT; exact .sym hs)
  | tag ht => intro T hT; cases T <;> simp [Ty.subst] at hT <;> first | exact .tvar _ _ | (subst hT; exact .tag ht)
  | ctor hc len h => intro T hT; cases T <;> simp [Ty.subst] at hT <;> first | exact .tvar _ _ | (subst hT; exact .ctor hc len h)
  | newtype hN hv => intro T hT; cases T <;> simp [Ty.subst] at hT <;> first | exact .tvar _ _ | (subst hT; exact .newtype hN hv)
  | list _ ih =>
      intro T hT; cases T <;> simp [Ty.subst] at hT
      · exact .tvar _ _
      · exact .list fun x hx => ih x hx _ hT
  | tuple len _ ih =>
      intro T hT; cases T <;> simp [Ty.subst, Ty.substList_eq_map] at hT
      · exact .tvar _ _
      · subst hT
        exact .tuple (by simpa using len) fun i h₁ h₂ =>
          ih i h₁ (by simpa using h₂) _ (List.getElem_map ..)
  | arrow hf =>
      intro T hT; cases T <;> simp [Ty.subst, Ty.substList_eq_map] at hT
      · exact .tvar _ _
      · obtain ⟨rfl, -⟩ := hT; exact .arrow (by simpa using hf)
  | union hT' _ ih =>
      intro T hT; cases T <;> simp [Ty.subst, Ty.substList_eq_map] at hT
      · exact .tvar _ _
      · subst hT
        obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT'
        exact .union hT₀ (ih _ rfl)

/-- The inline test of a representation type (`fast_test/3`): an unbound value or a literal of
that type. -/
def primTest (p : Prim) : Term → Bool
  | .var _ => true
  | .lit l => decide (l.prim = p)
  | _ => false

theorem primTest_iff (p : Prim) (v : Term) : primTest p v = true ↔ Fits sig v (.prim p) := by
  cases v with
  | var x => exact ⟨fun _ => .var x _, fun _ => rfl⟩
  | lit l =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [primTest, decide_eq_true_eq] at h; exact h ▸ .lit l
      · cases h; simp [primTest]
  | sym s => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | app xs => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-! ## Evidence -/

/-- Every instance of `v`, under every extension of the bindings, fits `T`. -/
def inst (v : Term) (T : Ty) : Prop := ∀ θ, Fits sig (v.subst θ) T

/-- Some instance of `v` fits `T`: what a passed check on an open value shows. -/
def compat (v : Term) (T : Ty) : Prop := ∃ θ, Fits sig (v.subst θ) T

/-- `v` has the static type `S`: every instance of `v` fits every instance of `S`. -/
def Has (v : Term) (S : Ty) : Prop := ∀ σ, inst sig v (S.subst σ)

variable {sig}

theorem inst.fits {v : Term} {T : Ty} (h : inst sig v T) : Fits sig v T := by
  simpa [Term.subst_id] using h .var

theorem Has.inst {v : Term} {S : Ty} (h : Has sig v S) : inst sig v S := by
  simpa [Ty.subst_id] using h .var

/-- Inst evidence survives every later binding. -/
theorem inst_evidence_stable {v : Term} {T : Ty} (h : inst sig v T) (θ : Nat → Term) :
    inst sig (v.subst θ) T := fun δ => by
  rw [Term.subst_subst]; exact h _

/-- Compat evidence does not: an unbound variable passes a `Number` check, and after it is
bound to a string no instance fits. Erasing a later check on such evidence is the open-alias
bug. -/
theorem compat_evidence_unstable :
    compat sig (.var 0) (.prim .number) ∧
      ¬ compat sig ((Term.var 0).subst fun _ => .lit (.str "s")) (.prim .number) := by
  refine ⟨⟨.var, by simpa using Fits.var 0 _⟩, ?_⟩
  rintro ⟨θ, h⟩
  simp only [Term.subst_var, Term.subst_lit] at h
  exact absurd ((primTest_iff sig _ _).2 h) (by decide)

/-! ## Establishment -/

variable (sig) in
/-- `est/2` on a static type whose variables are already instantiated. -/
inductive Est : Ty → Ty → Prop
  | unknown (S : Ty) : Est S .unknown
  | var (S : Ty) (a : Nat) : Est S (.var a)
  | prim (p : Prim) : Est (.prim p) (.prim p)
  | name (n : String) : Est (.name n) (.name n)
  | rigid (a : Nat) : Est (.rigid a) (.rigid a)
  | newtype (N : String) : Est (.newtype N) (.newtype N)
  /-- A newtype establishes what its representation does, unless that is a wildcard. -/
  | newtypeRep {N : String} {R T : Ty} : sig.newtypes N = some R → R ≠ .unknown → Est R T →
      Est (.newtype N) T
  | unionL {Ss : List Ty} {T : Ty} : (∀ S ∈ Ss, Est S T) → Est (.union Ss) T
  | unionR {S T : Ty} {Ts : List Ty} : T ∈ Ts → Est S T → Est S (.union Ts)
  | list {S T : Ty} : Est S T → Est (.list S) (.list T)
  | tupleList {Ss : List Ty} {T : Ty} : (∀ S ∈ Ss, Est S T) → Est (.tuple Ss) (.list T)
  | tuple {Ss Ts : List Ty} : Ss.length = Ts.length →
      (∀ i (h₁ : i < Ss.length) (h₂ : i < Ts.length), Est Ss[i] Ts[i]) → Est (.tuple Ss) (.tuple Ts)
  | arrow {As Bs : List Ty} {R R' : Ty} : As.length = Bs.length →
      (∀ i (h₁ : i < As.length) (h₂ : i < Bs.length), Est As[i] Bs[i]) → Est R R' →
      Est (.arrow As R) (.arrow Bs R')

variable (sig) in
/-- `S ⊑ T` (`established/2`): some instance of the variables of `S` establishes `T`. -/
def Establishes (S T : Ty) : Prop := ∃ σ, Est sig (S.subst σ) T

theorem Est.refl : ∀ T : Ty, Est sig T T
  | .prim p => .prim p
  | .name n => .name n
  | .var a => .var _ a
  | .rigid a => .rigid a
  | .newtype N => .newtype N
  | .unknown => .unknown _
  | .list T => .list (Est.refl T)
  | .tuple Ts => .tuple rfl fun i _ _ => Est.refl Ts[i]
  | .arrow As R => .arrow rfl (fun i _ _ => Est.refl As[i]) (Est.refl R)
  | .union Ts => .unionL fun T hT => .unionR hT (Est.refl T)
termination_by T => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have := List.sizeOf_lt_of_mem (List.getElem_mem ‹_›); omega
    | have := List.sizeOf_lt_of_mem ‹_›; omega

/-- A type variable establishes every type: the value fits each instance. -/
theorem establishes_var (a : Nat) (T : Ty) : Establishes sig (.var a) T :=
  ⟨fun _ => T, by simpa [Ty.subst] using Est.refl T⟩

/-- Establishment is pointwise sound against the value relation, tags and newtypes included. -/
theorem Est.sound {S T : Ty} (h : Est sig S T) : ∀ {v : Term}, Fits sig v S → Fits sig v T := by
  induction h with
  | unknown => exact fun _ => .unknown _
  | var => exact fun _ => .tvar _ _
  | prim | name | rigid | newtype => exact id
  | newtypeRep hN _ _ ih => exact fun hv => ih ((fits_newtype sig hN _).1 hv)
  | unionL _ ih =>
      intro v hv; cases hv with
      | var => exact .var _ _
      | union hT hvT => exact ih _ hT hvT
  | unionR hT _ ih => exact fun hv => .union hT (ih hv)
  | list _ ih =>
      intro v hv; cases hv with
      | var => exact .var _ _
      | list h => exact .list fun x hx => ih (h x hx)
  | tupleList _ ih =>
      intro v hv; cases hv with
      | var => exact .var _ _
      | tuple len h =>
          refine .list fun x hx => ?_
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
          exact ih _ (List.getElem_mem (len ▸ hi)) (h i hi (len ▸ hi))
  | tuple len _ ih =>
      intro v hv; cases hv with
      | var => exact .var _ _
      | tuple len' h =>
          exact .tuple (len'.trans len) fun i h₁ h₂ =>
            ih i (len' ▸ h₁) h₂ (h i h₁ (len' ▸ h₁))
  | arrow len _ _ _ _ =>
      intro v hv; cases hv with
      | var => exact .var _ _
      | arrow hf => exact .arrow (len ▸ hf)

/-- `establishes_sound`: a value with static type `S ⊑ T` has inst evidence at `T`. -/
theorem establishes_sound {S T : Ty} (h : Establishes sig S T) {v : Term} (hv : Has sig v S) :
    inst sig v T := by
  obtain ⟨σ, hσ⟩ := h
  exact fun θ => hσ.sound (hv σ θ)

/-- A rigid type establishes no known type but itself. -/
theorem rigid_establishes_only_itself {a : Nat} {T : Ty} (h : Est sig (.rigid a) T)
    (hT : T.Plain) : T = .rigid a := by
  cases h <;> simp_all [Ty.Plain]

/-! ## Conflict -/

variable (sig) in
/-- `may_share_values/2`: two names may share a value when they are equal, a symbol is declared
with both, one is a literal tag declared as a value of the other, or a constructor of one arity
is declared with both. -/
def MayShare (N M : String) : Prop :=
  N = M ∨ (∃ s, (s, N) ∈ sig.symbols ∧ (s, M) ∈ sig.symbols) ∨
    (sig.tag N = true ∧ (N, M) ∈ sig.symbols) ∨ (sig.tag M = true ∧ (M, N) ∈ sig.symbols) ∨
    ∃ c As Bs, (c, As, N) ∈ sig.ctors ∧ (c, Bs, M) ∈ sig.ctors ∧ As.length = Bs.length

variable (sig) in
/-- `constructed/2`: a tuple type may type an application of one of `N`'s constructors: its head
is unknown, or such a constructor with as many fields as follow it. -/
def Constructed (A C : Ty) : Prop :=
  ∃ N H Fs, A = .name N ∧ C = .tuple (H :: Fs) ∧ (H = .unknown ∨ (∃ a, H = .var a) ∨
    ∃ c As, H = .name c ∧ (c, As, N) ∈ sig.ctors ∧ As.length = Fs.length)

variable (sig) in
/-- `conflict/2`: `S`, the static type of a value, is not consistent with the required `T`
(Siek and Taha). The clauses of `consistent/2` are tried in order, and a variable or an unknown
type on either side is consistent; the side conditions below keep that order. -/
inductive Conflict : Ty → Ty → Prop
  /-- Some alternative of a union fails: a branch that surely fails. -/
  | unionL {Ss : List Ty} {S T : Ty} : T.Known → S ∈ Ss → Conflict S T → Conflict (.union Ss) T
  /-- Every alternative of a required union fails. -/
  | unionR {S : Ty} {Ts : List Ty} : S.Plain → (∀ T ∈ Ts, Conflict S T) → Conflict S (.union Ts)
  /-- A rigid type is consistent only with itself. -/
  | rigid {a : Nat} {T : Ty} : T.Plain → T ≠ .rigid a → Conflict (.rigid a) T
  /-- Only `N` is consistent with a newtype `N`: its values are made by `brand`. -/
  | newtypeR {S : Ty} {N : String} : S.Plain → (∀ a, S ≠ .rigid a) → S ≠ .newtype N →
      Conflict S (.newtype N)
  /-- A newtype is used as its representation, which must not be a wildcard. -/
  | newtypeL {N : String} {R T : Ty} : sig.newtypes N = some R → T.Plain → (∀ a, T ≠ .rigid a) →
      (∀ M, T ≠ .newtype M) → Conflict R T → Conflict (.newtype N) T
  | newtypeWild {N : String} {T : Ty} : sig.newtypes N = some .unknown → T.Plain →
      (∀ a, T ≠ .rigid a) → (∀ M, T ≠ .newtype M) → Conflict (.newtype N) T
  | prim {p q : Prim} : p ≠ q → Conflict (.prim p) (.prim q)
  | primName (p : Prim) (N : String) : Conflict (.prim p) (.name N)
  | namePrim (N : String) (p : Prim) : Conflict (.name N) (.prim p)
  | name {N M : String} : ¬ MayShare sig N M → Conflict (.name N) (.name M)
  /-- An atom against a list, tuple or arrow type (`constructed/2`). -/
  | atomCompound {A C : Ty} : A.Atom → C.Compound → ¬ Constructed sig A C → Conflict A C
  | compoundAtom {C A : Ty} : C.Compound → A.Atom → ¬ Constructed sig A C → Conflict C A
  | listTuple {E T : Ty} {Ts : List Ty} : T ∈ Ts → Conflict E T → Conflict (.list E) (.tuple Ts)
  | tupleList {S E : Ty} {Ss : List Ty} : S ∈ Ss → Conflict S E → Conflict (.tuple Ss) (.list E)
  /-- Lists of conflicting elements: they share only `()` when the elements are atoms. -/
  | list {A B : Ty} : Conflict A B → Conflict (.list A) (.list B)
  | tupleLength {Ss Ts : List Ty} : Ss.length ≠ Ts.length → Conflict (.tuple Ss) (.tuple Ts)
  | tuple {Ss Ts : List Ty} {i : Nat} (h₁ : i < Ss.length) (h₂ : i < Ts.length) :
      Conflict Ss[i] Ts[i] → Conflict (.tuple Ss) (.tuple Ts)
  /-- Arrows conflict component-wise, with no regard to variance. -/
  | arrowLength {As Bs : List Ty} {R R' : Ty} : As.length ≠ Bs.length →
      Conflict (.arrow As R) (.arrow Bs R')
  | arrowArg {As Bs : List Ty} {R R' : Ty} {i : Nat} (h₁ : i < As.length) (h₂ : i < Bs.length) :
      Conflict As[i] Bs[i] → Conflict (.arrow As R) (.arrow Bs R')
  | arrowRes {As Bs : List Ty} {R R' : Ty} : Conflict R R' → Conflict (.arrow As R) (.arrow Bs R')
  | listArrow (E : Ty) (As : List Ty) (R : Ty) : Conflict (.list E) (.arrow As R)
  | arrowList (As : List Ty) (R E : Ty) : Conflict (.arrow As R) (.list E)

/-- Conflicting atoms share no ground value. -/
theorem Conflict.atomic_apart {S T : Ty} (h : Conflict sig S T) (hS : S.Atom) (hT : T.Atom)
    {v : Term} (hc : v.Closed) (h₁ : Fits sig v S) (h₂ : Fits sig v T) : False := by
  cases h with
  | prim hpq => cases h₁ with | var => cases hc | lit l => cases h₂; exact hpq rfl
  | primName => cases h₁ with | var => cases hc | lit => cases h₂
  | namePrim => cases h₂ with | var => cases hc | lit => cases h₁
  | name hN =>
      apply hN
      cases h₁ with
      | var => cases hc
      | sym hs =>
          cases h₂ with
          | sym ht => exact .inr (.inl ⟨_, hs, ht⟩)
          | tag ht => exact .inr (.inr (.inr (.inl ⟨ht, hs⟩)))
      | tag hs =>
          cases h₂ with
          | sym ht => exact .inr (.inr (.inl ⟨hs, ht⟩))
          | tag => exact .inl rfl
      | ctor hc₁ len₁ _ =>
          cases h₂ with
          | ctor hc₂ len₂ _ => exact .inr (.inr (.inr (.inr ⟨_, _, _, hc₁, hc₂, len₁.symm.trans len₂⟩)))
  | atomCompound _ hC => exact Ty.not_atom_of_compound hC hT
  | compoundAtom hC => exact Ty.not_atom_of_compound hC hS
  | unionL | rigid | newtypeL | newtypeWild | listTuple | tupleList | list | tupleLength | tuple
    | arrowLength | arrowArg | arrowRes | listArrow | arrowList => simp [Ty.Atom] at hS
  | unionR | newtypeR => simp [Ty.Atom] at hT

/-- `(a)`: a union conflicts only through one of its alternatives. -/
theorem union_conflict_branch {Ss : List Ty} {T : Ty} (h : Conflict sig (.union Ss) T) :
    ∃ S ∈ Ss, Conflict sig S T := by
  cases h with
  | unionL _ hS h => exact ⟨_, hS, h⟩
  | unionR hS | newtypeR hS => simp [Ty.Plain] at hS
  | atomCompound hA => simp [Ty.Atom] at hA
  | compoundAtom hC => simp [Ty.Compound] at hC

/-- `(a)` for atoms: some branch surely fails, on every ground value. -/
theorem union_branch_fails {Ss : List Ty} {T : Ty} (h : Conflict sig (.union Ss) T)
    (hS : ∀ S ∈ Ss, S.Atom) (hT : T.Atom) :
    ∃ S ∈ Ss, ∀ v, v.Closed → Fits sig v S → ¬ Fits sig v T := by
  obtain ⟨S, hm, h⟩ := union_conflict_branch h
  exact ⟨S, hm, fun _ hc h₁ h₂ => h.atomic_apart (hS S hm) hT hc h₁ h₂⟩

/-- `(b)`: lists conflict through their elements; for atoms they share only `()`. -/
theorem list_conflict_nil {A B : Ty} (h : Conflict sig (.list A) (.list B)) :
    Conflict sig A B ∧ (A.Atom → B.Atom →
      ∀ v, v.Closed → Fits sig v (.list A) → Fits sig v (.list B) → v = .app []) := by
  have hAB : Conflict sig A B := by
    cases h with
    | list h => exact h
    | atomCompound hA | compoundAtom _ hA => simp [Ty.Atom] at hA
  refine ⟨hAB, fun hA hB v hc h₁ h₂ => ?_⟩
  cases h₁ with
  | var => cases hc
  | list hx =>
      cases h₂ with
      | list hy =>
          cases hc with
          | app hcs =>
              cases xs : ‹List Term› with
              | nil => rfl
              | cons x rest =>
                  subst xs
                  exact (hAB.atomic_apart hA hB (hcs x (by simp)) (hx x (by simp))
                    (hy x (by simp))).elim

/-- `(c)`: arrows conflict in their arity, in a parameter, or in the result. -/
theorem arrow_conflict_component {As Bs : List Ty} {R R' : Ty}
    (h : Conflict sig (.arrow As R) (.arrow Bs R')) :
    As.length ≠ Bs.length ∨ (∃ i, ∃ (h₁ : i < As.length) (h₂ : i < Bs.length),
      Conflict sig As[i] Bs[i]) ∨ Conflict sig R R' := by
  cases h with
  | arrowLength h => exact .inl h
  | arrowArg h₁ h₂ h => exact .inr (.inl ⟨_, h₁, h₂, h⟩)
  | arrowRes h => exact .inr (.inr h)
  | atomCompound hA | compoundAtom _ hA => simp [Ty.Atom] at hA

/-- A rigid type meets only itself, and every type but another rigid one meets a rigid type. -/
theorem rigid_conflict {a : Nat} {T : Ty} (hT : T.Plain) :
    (Conflict sig (.rigid a) T ↔ T ≠ .rigid a) ∧
      ((∀ b, T ≠ .rigid b) → ¬ Conflict sig T (.rigid a)) := by
  refine ⟨⟨fun h => ?_, fun h => .rigid hT h⟩, fun hn h => ?_⟩
  · cases h with
    | rigid _ h => exact h
    | unionR => simp [Ty.Plain] at hT
    | newtypeR _ h => exact absurd rfl (h a)
    | atomCompound hA => simp [Ty.Atom] at hA
    | compoundAtom hC => simp [Ty.Compound] at hC
  · cases h with
    | unionL => simp [Ty.Plain] at hT
    | rigid => exact hn _ rfl
    | newtypeL _ _ h | newtypeWild _ _ h => exact h a rfl
    | atomCompound _ hC => simp [Ty.Compound] at hC
    | compoundAtom _ hA => simp [Ty.Atom] at hA

/-- Only `N` itself, or an unknown, meets a newtype `N`. -/
theorem newtype_conflict {S : Ty} {N : String} (hS : S.Plain) (hr : ∀ a, S ≠ .rigid a) :
    Conflict sig S (.newtype N) ↔ S ≠ .newtype N := by
  refine ⟨fun h hSN => ?_, fun h => .newtypeR hS hr h⟩
  subst hSN
  cases h with
  | newtypeR _ _ h => exact h rfl
  | newtypeL _ _ _ h | newtypeWild _ _ _ h => exact h N rfl
  | atomCompound hA | compoundAtom _ hA => simp [Ty.Atom] at hA

/-! ## The three outcomes of a boundary -/

inductive Outcome where
  /-- `S ⊑ T`: no code. -/
  | exact
  /-- A type error at compile time. -/
  | conflict
  /-- A check at runtime. -/
  | check
  deriving DecidableEq

variable (sig) in
open Classical in
/-- How a value of static type `S` meets the required type `T`. -/
noncomputable def classify (S T : Ty) : Outcome :=
  if Establishes sig S T then .exact else if Conflict sig S T then .conflict else .check

variable (sig) in
open Classical in
/-- `type_boundary/4`: a ground value is decided at compile time by the value relation
(`value_established/2`, else `literal_type_mismatch`), unless the required type is nominal: a
value is made a newtype's only by `brand`. Other values are decided by their static type. -/
noncomputable def boundary (v : Term) (S T : Ty) : Outcome :=
  if v.Closed ∧ T.nominal = false then (if Fits sig v T then .exact else .conflict)
  else classify sig S T

/-- An exact boundary needs no check: the value has inst evidence at the required type. -/
theorem classify_exact_sound {S T : Ty} (h : classify sig S T = .exact) {v : Term}
    (hv : Has sig v S) : inst sig v T := by
  unfold classify at h
  split_ifs at h with hE
  exact establishes_sound hE hv

/-- A conflict is one of the conventions above; between atoms it rejects only values that
cannot pass. -/
theorem classify_conflict_sound {S T : Ty} (h : classify sig S T = .conflict) :
    Conflict sig S T ∧ (S.Atom → T.Atom → ∀ v, v.Closed → Fits sig v S → ¬ Fits sig v T) := by
  unfold classify at h
  split_ifs at h with hE hC
  exact ⟨hC, fun hS hT _ hc h₁ h₂ => hC.atomic_apart hS hT hc h₁ h₂⟩

/-- A symbol never fits a representation type, whatever is declared: a declaration
`(: s Number)` or `(: s (List T))` would give `s` a static type under which every boundary is
exact, so `representation_declaration/2` rejects it. -/
theorem representation_declaration_conflict (s : String) {T : Ty} (hT : T.Representation) :
    ¬ Fits sig (.sym s) T ∧ classify sig T T = .exact ∧ ¬ Has sig (.sym s) T := by
  have hfit : ¬ Fits sig (.sym s) T := by
    cases T <;> simp only [Ty.Representation] at hT <;> intro h <;> cases h
  exact ⟨hfit, if_pos ⟨.var, (Ty.subst_id T).symm ▸ Est.refl T⟩, fun h => hfit h.inst.fits⟩

/-- Other names admit the symbols declared with them. -/
theorem declared_symbol_admitted {s N : String} (h : (s, N) ∈ sig.symbols) :
    Has sig (.sym s) (.name N) ∧ boundary sig (.sym s) (.name N) (.name N) = .exact := by
  have hfit : Fits sig (.sym s) (.name N) := .sym h
  exact ⟨fun _ _ => by simpa [Ty.subst] using hfit,
    by simp [boundary, hfit, Term.Closed.sym, Ty.nominal]⟩

/-! ## Rigid type variables -/

/-- `body_contract/4`: the variables that are a parameter's whole type, or the element type of
a list parameter. -/
def rigidVars : List Ty → List Nat
  | [] => []
  | .var a :: Ts | .list (.var a) :: Ts => a :: rigidVars Ts
  | _ :: Ts => rigidVars Ts

/-- A declaration seen from its body: those variables are rigid, every other one unknown. -/
def bodyView (params : List Ty) : Ty → Ty :=
  Ty.subst fun a => if a ∈ rigidVars params then .rigid a else .unknown

/-! ## Examples -/

namespace Examples

/-- `(: Z Nat) (: succ (-> Nat Nat)) (: Meters (Newtype Number))`; `STV` is a tag. -/
def nat : Sig where
  symbols := [("Z", "Nat")]
  ctors := [("succ", [.name "Nat"], "Nat")]
  arities := [("succ", 1)]
  newtypes := fun N => if N = "Meters" then some (.prim .number) else none

/-- `(succ Z)` fits `Nat`; `(succ 1)` does not. -/
theorem succ_fits :
    Fits nat (.app [.sym "succ", .sym "Z"]) (.name "Nat") ∧
      ¬ Fits nat (.app [.sym "succ", .lit (.num 1)]) (.name "Nat") := by
  refine ⟨.ctor (As := [.name "Nat"]) (by simp [nat]) rfl fun i h₁ _ => ?_, fun h => ?_⟩
  · have : i = 0 := by simpa using h₁
    subst this; exact .sym (by simp [nat])
  · cases h with
    | ctor hc _ h =>
        obtain rfl : _ = [Ty.name "Nat"] := by simpa [nat] using hc
        have := h 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at this
        cases this

/-- A tag is its own value in every position: `(STV Number) ⊑ (List (| STV Number))`, and
`(STV 1)` fits both. -/
theorem tag_in_list :
    Est nat (.tuple [.name "STV", .prim .number]) (.list (.union [.name "STV", .prim .number])) ∧
      Fits nat (.app [.sym "STV", .lit (.num 1)]) (.list (.union [.name "STV", .prim .number])) := by
  have hE : Est nat (.tuple [.name "STV", .prim .number])
      (.list (.union [.name "STV", .prim .number])) :=
    .tupleList fun S hS => .unionR hS (Est.refl S)
  refine ⟨hE, hE.sound (.tuple rfl fun i h₁ _ => ?_)⟩
  match i, h₁ with
  | 0, _ => exact .tag (by decide)
  | 1, _ => exact .lit (.num 1)

/-- `(| Number String)` against `Number` is a conflict: its `String` branch surely fails. -/
theorem union_some_branch :
    Conflict nat (.union [.prim .number, .prim .string]) (.prim .number) :=
  .unionL (S := .prim .string) trivial (by simp) (.prim (by decide))

/-- Lists of lists conflict, yet share `(())`: `(b)` needs atomic elements. -/
theorem nested_lists_share :
    Conflict nat (.list (.list (.prim .number))) (.list (.list (.prim .string))) ∧
      Fits nat (.app [.app []]) (.list (.list (.prim .number))) ∧
      Fits nat (.app [.app []]) (.list (.list (.prim .string))) :=
  ⟨.list (.list (.prim (by decide))), .list (by simp; exact .list (by simp)),
    .list (by simp; exact .list (by simp))⟩

/-- A newtype is nominal: `5` fits `Meters` at runtime, yet `Number` conflicts with it and a
ground `5` is not established by inspection. -/
theorem newtype_is_nominal :
    Fits nat (.lit (.num 5)) (.newtype "Meters") ∧
      boundary nat (.lit (.num 5)) (.prim .number) (.newtype "Meters") = .conflict := by
  refine ⟨.newtype (R := .prim .number) (by simp [nat]) (.lit (.num 5)), ?_⟩
  have hC : Conflict nat (.prim .number) (.newtype "Meters") :=
    .newtypeR trivial (fun _ h => nomatch h) (fun h => nomatch h)
  have hE : ¬ Establishes nat (.prim .number) (.newtype "Meters") := by
    rintro ⟨σ, h⟩; cases h
  simp [boundary, classify, Ty.nominal, hE, hC]

/-- In `(-> $a (List $b) (Pair $c) $d)` seen from the body, `$a` and `$b` are rigid, `$c` and
`$d` unknown. -/
theorem body_view :
    let ps := [Ty.var 0, .list (.var 1), .tuple [.name "Pair", .var 2]]
    bodyView ps (.var 0) = .rigid 0 ∧ bodyView ps (.list (.var 1)) = .list (.rigid 1) ∧
      bodyView ps (.var 2) = .unknown ∧ bodyView ps (.var 3) = .unknown :=
  ⟨rfl, rfl, rfl, rfl⟩

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping
