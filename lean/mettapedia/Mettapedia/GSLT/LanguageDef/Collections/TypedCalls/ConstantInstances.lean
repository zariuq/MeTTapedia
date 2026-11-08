import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TwoWayTypedVersions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationSolver

/-!
# Constant parameters: the instance a constant's declaration fixes

A parameter whose formal is an arrow with type variables, to which every call to
itself passes one function name, is a CONSTANT parameter. The C derives an
instance from the name's one declaration (`contract_entry_facts`):
`match_atoms` of the formal against a fresh copy of the declaration, a most
general unifier, accepted when it gives each variable of the formal a closed type
or a variable the declaration names once (`contract_fixes_closed`); the other
formals are then read under it.

* **The derivation** (`derive`): the total first-order unifier on the formal and
  the declaration, their variables apart, through the codec of
  `TypeEquationSolver`; `FixesClosed` is `contract_fixes_closed`.
* **The derived instance is the one the protocol's check selects**: a closed
  instance of the formal is a type of the declaration exactly when it is an
  instance of the derivation (`derive_selects`, by soundness and most-generality
  of the unifier); with no derivation there is none (`derive_none`, by its
  completeness). The guard at the formal on the constant adds one equation
  (`constant_guard`), after which the store allows exactly the instances it
  allowed whose restriction to the formal is the derivation's
  (`constant_check_selects`). A derivation closing the formal fixes one instance
  (`selects_closed`), at which the constant meets the INSTANCE entry fact
  (`constant_entry`).
* **Controls**: `inc` fixes `$a := Number` at `(-> $a $a)`; `hop`'s `upd`,
  declared `(-> $a Nat Nat)`, fixes `$ct := Nat` at `(-> $a $ct $ct)` and leaves `$a`
  free, and the check selects exactly that (`upd_selects`); `(-> $c $c $c)` couples
  the formal's variables and fails `contract_fixes_closed`; `keep`, at the
  instance `inc` derives, is the protocol of
  `(-> (-> $a $a) (List $a) (List $a))` at every fuel (`keep_version`), and `dblS`
  derives `$a := String` and does not meet that instance's entry fact.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ConstantInstances

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions UnifyingFrames
open Mettapedia.Logic.LP (Term Subst unifyTotal Unifies)
open TypeEquationSolver (signature encode decode decode_encode encode_decode decode_apply encode_bind)

/-! ## The C's derivation -/

/-- The formal's type variables (`inl`) and those of a fresh copy of the
constant's declaration (`inr`), apart (`petta_type_call_instantiate`). -/
abbrev Side := String ⊕ String

/-- **The derivation** (`contract_entry_facts` at a constant parameter):
`match_atoms` of the formal against the fresh declaration, a most general unifier. -/
def derive (F D : Ty String) : Option (Subst (signature Side)) :=
  unifyTotal [(encode (F.map Sum.inl), encode (D.map Sum.inr))]

/-- What the derivation gives a variable, as a type. -/
def readTy (θ : Subst (signature Side)) (v : Side) : Ty Side := decode (θ v)

/-- **`contract_fixes_closed`**: each variable of the formal is given a closed type,
or a variable the fresh declaration names at most once. -/
def FixesClosed (θ : Subst (signature Side)) (F D : Ty String) : Prop :=
  ∀ x ∈ F.vars, (readTy θ (.inl x)).vars = [] ∨
    ∃ w, readTy θ (.inl x) = .var w ∧ (D.map Sum.inr).vars.count w ≤ 1

theorem bind_lift_comp {V : Type} (σ : V → Ty Empty) (t : Ty V) :
    t.bind (fun x => ((σ x).lift : Ty Side)) = ((t.bind σ).lift : Ty Side) := by
  unfold Ty.lift Ty.map
  rw [Ty.bind_bind]

/-- The derivation unifies the formal with the declaration. -/
theorem derive_unifies {F D : Ty String} {θ : Subst (signature Side)} (derived : derive F D = some θ) :
    (F.map Sum.inl).bind (readTy θ) = (D.map Sum.inr).bind (readTy θ) := by
  have sound := Mettapedia.Logic.LP.unifyTotal_sound _ θ derived
    (encode (F.map Sum.inl), encode (D.map Sum.inr)) (by simp)
  have decoded := congrArg decode sound
  rw [decode_apply, decode_apply] at decoded
  exact decoded

/-- **The instances the constant's declaration allows are the derivation's**: a closed
instance of the formal is a type of the declaration exactly when it is an instance of
the most general unifier `match_atoms` computes. -/
theorem derive_selects {F D : Ty String} {θ : Subst (signature Side)} (derived : derive F D = some θ)
    (σ : String → Ty Empty) :
    (∃ ρ : String → Ty Empty, D.bind ρ = F.bind σ) ↔
      ∃ μ : Side → Ty Empty, ∀ x ∈ F.vars, σ x = (readTy θ (.inl x)).bind μ := by
  constructor
  · rintro ⟨ρ, same⟩
    let δ : Side → Ty Side := fun v => Sum.elim (fun x => ((σ x).lift : Ty Side)) (fun y => (ρ y).lift) v
    have unified : Unifies (fun v => encode (δ v) : Subst (signature Side))
        [(encode (F.map Sum.inl), encode (D.map Sum.inr))] := by
      intro p member
      simp only [List.mem_singleton] at member
      subst member
      simp only
      rw [← encode_bind, ← encode_bind, Ty.bind_map, Ty.bind_map]
      congr 1
      change F.bind (fun x => ((σ x).lift : Ty Side)) = D.bind (fun y => ((ρ y).lift : Ty Side))
      rw [bind_lift_comp, bind_lift_comp, same]
    obtain ⟨ν, factor⟩ := Mettapedia.Logic.LP.unifyTotal_mgu _ θ derived _ unified
    refine ⟨fun v => (decode (ν v)).bind (fun _ => (default : Ty Empty)), fun x _ => ?_⟩
    have decoded := congrArg decode (factor (.inl x))
    rw [decode_encode, ← encode_decode (θ (Sum.inl x)), decode_apply] at decoded
    have grounded := congrArg (fun t : Ty Side => t.bind (fun _ => (default : Ty Empty))) decoded
    simp only [δ, Sum.elim_inl, Ty.lift_bind_ground, Ty.bind_bind] at grounded
    exact grounded
  · rintro ⟨μ, factor⟩
    refine ⟨fun y => (readTy θ (.inr y)).bind μ, ?_⟩
    have instanced := congrArg (fun t : Ty Side => t.bind μ) (derive_unifies derived)
    simp only [Ty.bind_bind, Ty.bind_map] at instanced
    change F.bind (fun x => (readTy θ (.inl x)).bind μ) = D.bind (fun y => (readTy θ (.inr y)).bind μ)
      at instanced
    rw [← instanced]
    exact Ty.bind_congr F fun x member => (factor x member).symm

/-- **No derivation, no instance**: where `match_atoms` fails, no instance of the
formal is a type of the declaration. -/
theorem derive_none {F D : Ty String} (failed : derive F D = none) :
    ¬ ∃ (σ : String → Ty Empty) (ρ : String → Ty Empty), D.bind ρ = F.bind σ := by
  rintro ⟨σ, ρ, same⟩
  let δ : Side → Ty Side := fun v => Sum.elim (fun x => ((σ x).lift : Ty Side)) (fun y => (ρ y).lift) v
  have unified : Unifies (fun v => encode (δ v) : Subst (signature Side))
      [(encode (F.map Sum.inl), encode (D.map Sum.inr))] := by
    intro p member
    simp only [List.mem_singleton] at member
    subst member
    simp only
    rw [← encode_bind, ← encode_bind, Ty.bind_map, Ty.bind_map]
    congr 1
    change F.bind (fun x => ((σ x).lift : Ty Side)) = D.bind (fun y => ((ρ y).lift : Ty Side))
    rw [bind_lift_comp, bind_lift_comp, same]
  obtain ⟨θ, found⟩ := Mettapedia.Logic.LP.unifyTotal_complete ⟨_, unified⟩
  unfold derive at failed
  rw [failed] at found
  cases found

/-! ## The protocol's check at a constant parameter -/

section Check

variable {Γ : Decls}

theorem sat_row_iff (D : Ty String) (T : Ty Empty) :
    Sat ([((D.map DVar.own : Ty DVar), (T.lift : Ty DVar))] : List (Eqn DVar)) ↔
      ∃ ρ : String → Ty Empty, D.bind ρ = T := by
  constructor
  · rintro ⟨ρ, solved⟩
    rw [solves_singleton, Ty.bind_map, Ty.lift_bind_ground] at solved
    exact ⟨ρ ∘ DVar.own, solved⟩
  · rintro ⟨ρ, same⟩
    refine ⟨fun d => match d.2 with
      | some x => ρ x
      | none => default, ?_⟩
    rw [solves_singleton, Ty.bind_map, Ty.lift_bind_ground]
    exact same

theorem eff_constant {f : String} {D : Ty String} (row : Γ f = [D]) :
    eff (info Γ (.symbol f)) = {⟨D.map DVar.own, []⟩} := by
  rw [info_symbol, row]
  unfold eff
  simp

/-- **The guard at a constant parameter's formal adds one equation**, the constant's
declaration met with the formal; its store allows exactly the instances the store
allowed that make the formal a type of the declaration. -/
theorem constant_allows {D F : Ty String} (k : ℕ) (S : List (Eqn CallVar))
    (fresh : ∀ d, atGuard k d ∉ eqnVars S) (σ : String → Ty Empty) :
    Allows (S ++ [(((D.map DVar.own).map (atGuard k) : Ty CallVar), F.map Sum.inl)]) σ ↔
      Allows S σ ∧ ∃ ρ : String → Ty Empty, D.bind ρ = F.bind σ := by
  have extend := allows_extend k S fresh ⟨D.map DVar.own, []⟩ F σ
  simp only [List.map_nil, List.append_nil, List.nil_append] at extend
  rw [extend, sat_row_iff]

/-- **The derived instance is the one the protocol's check selects**: after the guard
at the formal on the constant, the store allows exactly the instances the store
allowed whose restriction to the formal's variables is an instance of the
derivation. -/
theorem constant_check_selects {D F : Ty String} {θ : Subst (signature Side)}
    (derived : derive F D = some θ) (k : ℕ) (S : List (Eqn CallVar))
    (fresh : ∀ d, atGuard k d ∉ eqnVars S) (σ : String → Ty Empty) :
    Allows (S ++ [(((D.map DVar.own).map (atGuard k) : Ty CallVar), F.map Sum.inl)]) σ ↔
      Allows S σ ∧ ∃ μ : Side → Ty Empty, ∀ x ∈ F.vars, σ x = (readTy θ (.inl x)).bind μ :=
  (constant_allows k S fresh σ).trans (and_congr_right fun _ => derive_selects derived σ)

open Classical in
/-- **The guard at the formal on the constant** continues once, with that one equation,
when some allowed instance makes the formal a type of the declaration, and not at
all otherwise. -/
theorem constant_guard {f : String} {D F : Ty String} (row : Γ f = [D]) (noMeta : NoMeta F)
    (grounded : String → Bool) (k : ℕ) (S : List (Eqn CallVar))
    (fresh : ∀ d, atGuard k d ∉ eqnVars S) :
    guard (atGuard k) S (F.map Sum.inl) (info Γ (.symbol f)) (metatype grounded (.symbol f)) =
      if ∃ σ, Allows S σ ∧ ∃ ρ : String → Ty Empty, D.bind ρ = F.bind σ then
        {S ++ [(((D.map DVar.own).map (atGuard k) : Ty CallVar), F.map Sum.inl)]}
      else 0 := by
  have gt := getType_of_eff (atGuard k) S (F.map Sum.inl) (eff_constant row)
  simp only [List.map_nil, List.append_nil] at gt
  have iff : Sat (S ++ [(((D.map DVar.own).map (atGuard k) : Ty CallVar), F.map Sum.inl)]) ↔
      ∃ σ, Allows S σ ∧ ∃ ρ : String → Ty Empty, D.bind ρ = F.bind σ := by
    rw [sat_iff_allows]
    exact exists_congr fun σ => constant_allows k S fresh σ
  by_cases h : ∃ σ, Allows S σ ∧ ∃ ρ : String → Ty Empty, D.bind ρ = F.bind σ
  · rw [if_pos (iff.mpr h)] at gt
    rw [if_pos h, guard_of_getType _ _ _ _ _ (by rw [gt]; exact Multiset.singleton_ne_zero _), gt]
  · rw [if_neg (fun hs => h (iff.mp hs))] at gt
    rw [if_neg h]
    unfold guard
    rw [gt, Multiset.card_zero, if_pos rfl, Multiset.filter_singleton,
      if_neg (not_sat_meta noMeta grounded _)]
    rfl

end Check

/-! ## A closed derivation -/

/-- The closed instance a derivation that closes every variable fixes. -/
def closedInstance (θ : Subst (signature Side)) (x : String) : Ty Empty :=
  (readTy θ (.inl x)).bind fun _ => default

/-- **A derivation closing the formal fixes one instance**: the instances the check
selects are exactly those agreeing with it on the formal's variables. -/
theorem selects_closed {F D : Ty String} {θ : Subst (signature Side)} (derived : derive F D = some θ)
    (closed : ∀ x ∈ F.vars, (readTy θ (.inl x)).vars = []) (σ : String → Ty Empty) :
    (∃ ρ : String → Ty Empty, D.bind ρ = F.bind σ) ↔ ∀ x ∈ F.vars, σ x = closedInstance θ x := by
  rw [derive_selects derived]
  constructor
  · rintro ⟨μ, factor⟩ x member
    rw [factor x member]
    exact Ty.bind_congr _ fun v occurs => by simp [closed x member] at occurs
  · intro agree
    exact ⟨fun _ => default, agree⟩

open Classical in
theorem count_constant {Γ : Decls} {f : String} {D : Ty String} (row : Γ f = [D]) (T : Ty Empty) :
    count (info Γ (.symbol f)) T = if ∃ ρ : String → Ty Empty, D.bind ρ = T then 1 else 0 := by
  classical
  unfold count
  rw [eff_constant row, Multiset.filter_singleton]
  simp only [List.nil_append]
  by_cases h : ∃ ρ : String → Ty Empty, D.bind ρ = T
  · rw [if_pos ((sat_row_iff D T).mpr h), if_pos h]
    rfl
  · rw [if_neg (fun hs => h ((sat_row_iff D T).mp hs)), if_neg h]
    rfl

/-- **The constant meets the entry fact of the derived instance** (CONSTANT as
INSTANCE): ground, and typed once at the formal under the closed instance the
derivation fixes. -/
theorem constant_entry {Γ : Decls} (grounded : String → Bool) {f : String} {D F : Ty String}
    (row : Γ f = [D]) {θ : Subst (signature Side)} (derived : derive F D = some θ)
    (closed : ∀ x ∈ F.vars, (readTy θ (.inl x)).vars = []) {σ : String → Ty Empty}
    (agree : ∀ x ∈ F.vars, σ x = closedInstance θ x) :
    support (Atom.symbol f) = ∅ ∧ Holds Γ grounded (.symbol f) (F.bind σ) := by
  refine ⟨by simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars], ?_⟩
  apply Holds.of_count
  rw [count_constant row, if_pos ((selects_closed derived closed σ).mpr agree)]

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (decls decls_functional sym num app listOf listNumber cons_row
  cons_constructor count_nil listA atNumber)
open TwoWayTypedVersions GroundUninterpretedVersions
open TwoWayTypedVersions.Controls (number holds_num num_ground noEnter)

/-- `(-> $a $a)`, a constant parameter's formal. -/
abbrev arrowA : Ty String := arrow [.var "a"] (.var "a")

/-- `(-> Number Number)`, the declaration of `inc`. -/
abbrev arrowNumberRow : Ty String := arrow [.sym "Number"] (.sym "Number")

/-- **`inc` fixes `$a` at `Number`**: the derivation closes the formal. -/
theorem inc_derived : (derive arrowA arrowNumberRow).map (fun θ => readTy θ (.inl "a")) =
    some (.sym "Number") := by
  cbv

/-- `(-> $a $ct $ct)` and `upd`'s `(-> $a Nat Nat)` (the higher-order chainer `hop`). -/
abbrev hopFormal : Ty String := arrow [.var "a", .var "ct"] (.var "ct")
abbrev updRow : Ty String := arrow [.var "a", .sym "Nat"] (.sym "Nat")

/-- **A polymorphic declaration**: `$ct` is fixed at `Nat`; `$a` is given the
declaration's own variable, named once there. -/
theorem upd_derived : (derive hopFormal updRow).map
    (fun θ => (readTy θ (.inl "a"), readTy θ (.inl "ct"))) = some (.var (.inr "a"), .sym "Nat") := by
  cbv

theorem upd_fixes_closed : ∃ θ, derive hopFormal updRow = some θ ∧ FixesClosed θ hopFormal updRow := by
  obtain ⟨θ, found, read⟩ := Option.map_eq_some_iff.mp upd_derived
  simp only [Prod.mk.injEq] at read
  refine ⟨θ, found, fun x member => ?_⟩
  simp [hopFormal, arrow] at member
  rcases member with rfl | rfl
  · exact .inr ⟨.inr "a", read.1, by decide⟩
  · exact .inl (by rw [read.2]; rfl)

/-- **The check selects `$ct := Nat` and leaves `$a` free**: a closed instance of
`(-> $a $ct $ct)` is a type of `upd` exactly when it sends `$ct` to `Nat`. -/
theorem upd_selects (σ : String → Ty Empty) :
    (∃ ρ : String → Ty Empty, updRow.bind ρ = hopFormal.bind σ) ↔ σ "ct" = .sym "Nat" := by
  obtain ⟨θ, found, read⟩ := Option.map_eq_some_iff.mp upd_derived
  simp only [Prod.mk.injEq] at read
  rw [derive_selects found]
  constructor
  · rintro ⟨μ, factor⟩
    rw [factor "ct" (by simp [hopFormal, arrow]), read.2]
    rfl
  · intro ct
    refine ⟨fun v => if v = .inr "a" then σ "a" else default, fun x member => ?_⟩
    simp [hopFormal, arrow] at member
    rcases member with rfl | rfl
    · rw [read.1]
      simp
    · rw [read.2, ct]
      rfl

/-- `(-> $c $c $c)`: a declaration whose variable couples the formal's two. -/
abbrev coupledRow : Ty String := arrow [.var "c", .var "c"] (.var "c")

/-- **A coupling declaration fixes nothing** (`contract_fixes_closed` fails): `$a` and
`$ct` are both given the declaration's variable, which it names three times. -/
theorem coupled_not_fixed : ∃ θ, derive hopFormal coupledRow = some θ ∧ ¬ FixesClosed θ hopFormal coupledRow := by
  have read : (derive hopFormal coupledRow).map (fun θ => readTy θ (.inl "a")) = some (.var (.inr "c")) := by
    cbv
  obtain ⟨θ, found, readA⟩ := Option.map_eq_some_iff.mp read
  refine ⟨θ, found, fun fixes => ?_⟩
  rcases fixes "a" (by simp [hopFormal, arrow]) with closed | ⟨w, same, count⟩
  · rw [readA] at closed
    cases closed
  · rw [readA] at same
    cases same
    revert count
    decide

/-! ### A constant parameter's instance in a version -/

/-- `(= (keep $f Nil) Nil)`. -/
def keepNil : Equation := ⟨[.var "f", .const (sym "Nil")], .const (sym "Nil")⟩

/-- `(= (keep $f (Cons $h $t)) (Cons $h (keep $f $t)))` at
`(: keep (-> (-> $a $a) (List $a) (List $a)))`, read at the instance `inc` fixes. -/
def keepCons : Equation :=
  ⟨[.var "f", .ctor "Cons" [.var "h", .var "t"]], .ctor "Cons" [.var "h", .self [.var "f", .var "t"]]⟩

abbrev arrowNumber : Ty Empty := arrow [.sym "Number"] (.sym "Number")

def keepProgram : TProgram :=
  ⟨[.ground arrowNumber, .ground listNumber], .closed listNumber, fun _ => none, fun _ _ => none, []⟩

theorem cons_fact (x : String) (B : Ty String) (U : Ty Empty) (p : Pat)
    (field : (B, p) ∈ List.zip [Ty.var "a", listOf (Ty.var "a")] [.var "h", .var "t"])
    (fixed : ¬ FreeField (listOf (Ty.var "a")) B) (inner : PatFact decls p (B.bind atNumber) x U) :
    PatFact decls (.ctor "Cons" [.var "h", .var "t"]) listNumber x U := by
  have inst : ((listOf (Ty.var "a") : Ty String).bind atNumber) = listNumber := by
    simp [listOf, listNumber, atNumber]
  exact PatFact.ctor (σ := atNumber) cons_row cons_constructor rfl
    (by simp [MetaName, listNumber, listOf]) (by simp [Named, listNumber, listOf]) inst field fixed inner

theorem keep_accepted (grounded : String → Bool) :
    ∀ eq ∈ [keepNil, keepCons], TAccepted decls grounded keepProgram eq := by
  intro eq member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨rfl, _, _, .const _ _ (some listNumber) (fun T h => by
      cases h
      exact ⟨by simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars],
        Holds.of_count (count_nil _)⟩), Or.inr ⟨by decide +kernel, rfl⟩⟩
  · have factF : eqTypes decls keepProgram.positions keepCons.pats "f" arrowNumber :=
      ⟨arrowNumber, .var "f", by simp [keepProgram, keepCons], .var _ _⟩
    have factH : eqTypes decls keepProgram.positions keepCons.pats "h" number :=
      ⟨listNumber, .ctor "Cons" [.var "h", .var "t"], by simp [keepProgram, keepCons],
        cons_fact "h" (.var "a") number (.var "h") (by simp) (by simp [FreeField, listOf])
          (.var _ _)⟩
    have factT : eqTypes decls keepProgram.positions keepCons.pats "t" listNumber :=
      ⟨listNumber, .ctor "Cons" [.var "h", .var "t"], by simp [keepProgram, keepCons],
        cons_fact "t" (listOf (.var "a")) listNumber (.var "t") (by simp) (by simp [FreeField, listOf])
          (by simpa [listOf, listNumber, atNumber] using PatFact.var (Γ := decls) "t" listNumber)⟩
    refine ⟨rfl, _, _, .ctor (t := some listNumber) (.cons (.var _ "h" (some number) fun _ h => by
        cases h
        exact factH)
      (.cons (.self (.cons (.var _ "f" (some arrowNumber) fun _ h => by
          cases h
          exact factF) (.cons (.var _ "t" (some listNumber) fun _ h => by
          cases h
          exact factT) (.nil _)))
        (Or.inr (.cons ⟨by decide +kernel, rfl⟩ (.cons ⟨by decide +kernel, rfl⟩ .nil)))) (.nil _)))
      (fun T h => ?_), Or.inr ⟨by decide +kernel, rfl⟩⟩
    cases h
    exact ⟨[.var "a", listOf (.var "a")], listOf (.var "a"), atNumber, cons_row, cons_constructor,
      .cons (fun _ => ⟨by decide, rfl⟩) (.cons (fun _ => ⟨by decide, rfl⟩) .nil), rfl⟩

theorem keep_hyps (grounded : String → Bool) :
    TVersionHyps decls grounded (fun _ => False) keepProgram TypedCalls.Controls.env
      TypedCalls.Controls.env [keepNil, keepCons] noEnter noEnter where
  functional := decls_functional
  accepted := keep_accepted grounded
  enterAgree _ _ _ offered := by cases offered
  enterAnswers _ _ _ offered := by cases offered
  prim _ _ _ known := by cases known
  primSame := rfl
  keptSame := rfl
  rows _ _ := rfl
  named _ member := by cases member

/-- **The instance a constant derives is the version's**: `inc`'s declaration fixes
`$a := Number` (`inc_derived`), the instance the protocol's check selects
(`selects_closed`), at which `inc` meets its entry fact (`constant_entry`); the version
analysed there is the protocol of `(-> (-> $a $a) (List $a) (List $a))` at every fuel,
multiplicity included, on `inc` and a ground list of numbers. -/
theorem keep_version (grounded : String → Bool) (n : ℕ) (xs : Atom) (xsGround : support xs = ∅)
    (xsTyped : Holds decls grounded xs listNumber) :
    protocolRun decls grounded (relBody TypedCalls.Controls.env noEnter [keepNil, keepCons])
        (arrow [arrowA, listA] listA) n [sym "inc", xs] =
      versionRun (relBody TypedCalls.Controls.env noEnter [keepNil, keepCons]) n [sym "inc", xs] := by
  obtain ⟨θ, found, read⟩ := Option.map_eq_some_iff.mp inc_derived
  have closed : ∀ x ∈ arrowA.vars, (readTy θ (.inl x)).vars = [] := by
    intro x member
    simp [arrowA, arrow] at member
    subst member
    rw [read]
    rfl
  have agree : ∀ x ∈ arrowA.vars, atNumber x = closedInstance θ x := by
    intro x member
    simp [arrowA, arrow] at member
    subst member
    simp [closedInstance, read, atNumber]
  have incEntry := constant_entry grounded (Γ := decls) (f := "inc") (by simp [decls]) found closed agree
  exact instance_typed_version_eq_protocol (keep_hyps grounded) (Fs := [arrowA, listA]) (R := listA)
    atNumber rfl rfl (fun F member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨by decide, noMeta_app _⟩
      · exact ⟨by decide, noMeta_app _⟩) (by decide) (noMeta_app _) n [sym "inc", xs]
    (.cons ⟨incEntry.1, by simpa [arrowA, arrow, atNumber] using incEntry.2⟩
      (.cons ⟨xsGround, xsTyped⟩ .nil))

/-- `(keep inc (Cons 1 Nil))` is `(Cons 1 Nil)`, once. -/
theorem keep_answers :
    versionRun (relBody TypedCalls.Controls.env noEnter [keepNil, keepCons]) 3
        [sym "inc", app "Cons" [num 1, sym "Nil"]] = {app "Cons" [num 1, sym "Nil"]} := by
  cbv

/-- **Off the derived instance the constant may not enter**: `dblS`'s declaration
fixes `$a := String`, and `dblS` is not typed at `(-> Number Number)`, so the entry fact
of `inc`'s instance refuses it (the C's CONSTANT test names `inc`). -/
theorem dblS_off_instance :
    (derive arrowA (arrow [.sym "String"] (.sym "String"))).map (fun θ => readTy θ (.inl "a")) =
        some (.sym "String") ∧
      count (info decls (sym "dblS")) arrowNumber = 0 := by
  refine ⟨by cbv, ?_⟩
  rw [count_constant (D := arrow [.sym "String"] (.sym "String")) (by simp [decls]), if_neg]
  rintro ⟨ρ, same⟩
  simp [arrow, arrowNumber, Ty.bind_app] at same

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ConstantInstances
