import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNeedSource

/-!
# The nested-calls core: its embedding, and the first lemmas of its correspondence

The nested-calls core (`ProgramNested`) has first-order rows (`Tm`: numerals, one binary cell,
variables `(scope, name)`), expressions `val t` (held data), `pair a b` (both evaluated, then the cell
built) and `call a` (evaluated, then answered by the installed version's equations), equations
`(= lhs rhs)` with a data pattern and an expression pattern, and a reference semantics in evaluation
contexts (`CStep`) where answering a call applies a most general unifier to every row.

**The embedding.**
* Rows are data of the signature `RSig` (numerals and the cell); the core's variable `(s, x)`, used by
  equation `j` at scope `s`, is the name `⟨[s], var j x⟩` (`trTm`), so a copy of equation `j` at scope
  `s` is exactly the core's renaming of its pattern into scope `s` (`trPat_at`).
* `val t` is `ret`; `pair a b` is two arrows and a `ret` of the cell; `call a` is an arrow and an
  `apply` (`trEx`, `trEPat`). Equation `j` is the core equation at site `j` (`trEquation`).

**What is proved here.** Substitutions of the core are assignments of the language
(`instantiate_assignOf`), the translation is injective (`trTm_injective`), and a substitution unifies
a problem of the core exactly when its assignment solves the translated store
(`unifies_iff_models`).

**What the correspondence still needs** (not proved here): the solved-form relation between a
configuration of the core (rows with the most general unifiers applied) and a configuration of the
language (stores), with the two facts that make it a simulation: a most general unifier of the core
gives an idempotent most general solution of the translated store (`IsMGU` to `Principal`, using
`exists_isMGU`), and the core's evaluation contexts are the language's frames (`ECtx.fill` against
`bindTo` frames). The core's versions and redefinition (`ver`, `redefTo`) have no counterpart: the
language's programs are static, so the embedding covers the programs of one version.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NestedCore

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP
open ProgramRows ProgramEquations ProgramNested

/-! ## Rows as data -/

/-- Operators of rows: numerals and the binary cell. -/
inductive ROp : Unit → Type where
  | const (k : ℕ) : ROp ()
  | cell : ROp ()

def ROp.arity : {s : Unit} → ROp s → List (List Unit × Unit)
  | _, .const _ => []
  | _, .cell => [([], ()), ([], ())]

/-- **The signature of rows.** -/
abbrev RSig : Signature := ⟨Unit, ROp, ROp.arity⟩

/-- Keys: the variable `x` of equation `j`, the slot of the translation at a path, or the shared
cell of heap location `ℓ` (for the call-by-need core). -/
inductive RKey where
  | var (j x : ℕ)
  | slot (path : List ℕ)
  | cell (location : ℕ)
  deriving DecidableEq

/-- Equation `j` owns its variables; each slot is its own arrow; each location its own cell. -/
def RKey.site : RKey → ℕ ⊕ (List ℕ ⊕ ℕ)
  | .var j _ => .inl j
  | .slot path => .inr (.inl path)
  | .cell location => .inr (.inr location)

abbrev rkeys : Keys RSig := ⟨RKey, ℕ ⊕ (List ℕ ⊕ ℕ), RKey.site, fun _ => ([], ()), inferInstance⟩

abbrev RData := Data rkeys [] ()

/-- A name of the language as a datum. -/
def nameD (x : Name rkeys) : RData := .op (.inr (.mk x)) .nil

def constD (k : ℕ) : RData := .op (.inl (.const k)) .nil
def cellD (a b : RData) : RData := .op (.inl .cell) (.cons a (.cons b .nil))

/-- **Rows as data**: the core's variable `(s, x)` is the name of variable `x` of the equation used
at scope `s`, at scope `s`. -/
def trTm (eqAt : ℕ → ℕ) : Tm → RData
  | .var (s, x) => nameD ⟨[s], .var (eqAt s) x⟩
  | .const k => constD k
  | .app () ts => cellD (trTm eqAt (ts 0)) (trTm eqAt (ts 1))

/-- **Patterns as data** of equation `j`, unopened. -/
def trPat (j : ℕ) : Pat → RData
  | .var x => nameD ⟨[], .var j x⟩
  | .sym k => constD k
  | .cell a b => cellD (trPat j a) (trPat j b)

/-- A copy at scope `n` of equation `j`'s pattern is the core's renaming of it into scope `n`. -/
theorem trPat_at (eqAt : ℕ → ℕ) (n j : ℕ) (same : eqAt n = j) :
    ∀ p : Pat, instantiate (copyAt rkeys n) (trPat j p) = trTm eqAt (p.at n)
  | .var x => by
      subst same
      show bind (argsToSub _) _ = _
      rfl
  | .sym k => rfl
  | .cell a b => by
      show cellD (instantiate (copyAt rkeys n) (trPat j a)) (instantiate (copyAt rkeys n) (trPat j b)) =
        cellD (trTm eqAt (a.at n)) (trTm eqAt (b.at n))
      rw [trPat_at eqAt n j same a, trPat_at eqAt n j same b]

/-! ## Expressions and equations -/

/-- The slot of the translation at a path, unopened. -/
def slotD (path : List ℕ) : RData := nameD ⟨[], .slot path⟩

variable {Ty : Type}

/-- **Expression patterns** of equation `j` at a path: `val` holds, `pair` evaluates both sides and
builds the cell, `call` evaluates and calls. -/
def trEPat (j : ℕ) : List ℕ → EPat → Comp rkeys [] () Ty
  | _, .val p => .ret (trPat j p)
  | path, .pair a b =>
      .let_ (.inr (.inl (path ++ [0]))) (slotD (path ++ [0])) (trEPat j (path ++ [0]) a)
        (.let_ (.inr (.inl (path ++ [1]))) (slotD (path ++ [1])) (trEPat j (path ++ [1]) b)
          (.ret (cellD (slotD (path ++ [0])) (slotD (path ++ [1])))))
  | path, .call a =>
      .let_ (.inr (.inl (path ++ [0]))) (slotD (path ++ [0])) (trEPat j (path ++ [0]) a)
        (.apply (slotD (path ++ [0])))

/-- **Expressions** at a path (the query). -/
def trEx (eqAt : ℕ → ℕ) : List ℕ → Ex → Comp rkeys [] () Ty
  | _, .val t => .ret (trTm eqAt t)
  | path, .pair a b =>
      .let_ (.inr (.inl (path ++ [0]))) (slotD (path ++ [0])) (trEx eqAt (path ++ [0]) a)
        (.let_ (.inr (.inl (path ++ [1]))) (slotD (path ++ [1])) (trEx eqAt (path ++ [1]) b)
          (.ret (cellD (slotD (path ++ [0])) (slotD (path ++ [1])))))
  | path, .call a =>
      .let_ (.inr (.inl (path ++ [0]))) (slotD (path ++ [0])) (trEx eqAt (path ++ [0]) a)
        (.apply (slotD (path ++ [0])))

/-- **Equation `j`** as a core equation at site `j`. -/
def trEquation (j : ℕ) (e : NEquation) : Equation rkeys [] () Ty :=
  ⟨.inl j, trPat j e.lhs, trEPat j [j] e.rhs⟩

/-- **The program of one version**: its equations in order, text read as a root call. -/
def program (eqs : List NEquation) : Program rkeys [] () Ty :=
  ⟨eqs.zipIdx.map fun p => trEquation p.2 p.1, fun t => .apply t⟩

/-- An equation whose left-hand side is a name of its own site and whose right-hand side fails. -/
def failing (J : ℕ) : Equation rkeys [] () Ty := ⟨.inl J, nameD ⟨[], .var J 0⟩, .fail⟩

/-- **The program of one version, with the core's rule for a call that no equation answers.** In the
core such a call has no step; in the language a call that no equation answers is returned as data.
The core's rule is the language's with `failing` added last: its alternative fails, so it adds no
answer. -/
def programStrict (eqs : List NEquation) : Program rkeys [] () Ty :=
  ⟨eqs.zipIdx.map (fun p => trEquation p.2 p.1) ++ [failing eqs.length], fun t => .apply t⟩

/-! ## The first-order equation core and the call-by-need core: their embeddings -/

/-- **First-order pattern equations** (`ProgramEquations`): the right-hand side is data that is
called again at its root, as the core's threads rewrite again. -/
def trEquationFO (j : ℕ) (e : ProgramEquations.Equation) : Equation rkeys [] () Ty :=
  ⟨.inl j, trPat j e.lhs, .apply (trPat j e.rhs)⟩

def programFO (eqs : ProgramEquations.Program) : Program rkeys [] () Ty :=
  ⟨eqs.zipIdx.map fun p => trEquationFO p.2 p.1, fun t => .apply t⟩

/-- Closed rows. -/
def trSx : Sx → RData
  | .sym k => constD k
  | .cell a b => cellD (trSx a) (trSx b)

/-- The shared cell of heap location `ℓ`, unopened. -/
def cellName (location : ℕ) : RData := nameD ⟨[], .cell location⟩

/-- **Call by need** (`ProgramNeed`): binding a location delays its thunk in a shared cell; reading
the location forces the cell. -/
def trNEx : List ℕ → ProgramNeed.NEx → Comp rkeys [] () Ty
  | _, .val t => .ret (trSx t)
  | _, .loc ℓ => .force (cellName ℓ)
  | path, .pair a b =>
      .let_ (.inr (.inl (path ++ [0]))) (slotD (path ++ [0])) (trNEx (path ++ [0]) a)
        (.let_ (.inr (.inl (path ++ [1]))) (slotD (path ++ [1])) (trNEx (path ++ [1]) b)
          (.ret (cellD (slotD (path ++ [0])) (slotD (path ++ [1])))))
  | path, .call a =>
      .let_ (.inr (.inl (path ++ [0]))) (slotD (path ++ [0])) (trNEx (path ++ [0]) a)
        (.apply (slotD (path ++ [0])))
  | path, .bind ℓ a b => .delay (.inr (.inr ℓ)) (cellName ℓ) (trNEx (path ++ [0]) a) (trNEx (path ++ [1]) b)

/-! ## Substitutions of the core are assignments -/

/-- The assignment of a substitution of the core: each name `⟨[s], var j x⟩` reads as the image of
`(s, x)`; every other name is kept. -/
def assignOf (eqAt : ℕ → ℕ) (δ : Subst rows) : Assignment (fam rkeys) (fam rkeys) := fun x =>
  match x with
  | ⟨[s], .var j v⟩ => if j = eqAt s then trTm eqAt (δ (s, v)) else generator (fam rkeys) ⟨[s], .var j v⟩
  | x => generator (fam rkeys) x

theorem argsToSub_nil {X : Type} {target : X → MetaArity RSig} :
    (argsToSub (S := signature RSig target) (bs := []) (Γ := []) .nil) = fun _ v => .var v := by
  funext s v
  cases v

@[simp] theorem instantiate_nameD {X : Type} {target : X → MetaArity RSig}
    (σ : Assignment (fam rkeys) target) (x : Name rkeys) : instantiate σ (nameD x) = σ x := by
  change bind (argsToSub (S := signature RSig target) (bs := []) (Γ := []) .nil) (σ x) = _
  rw [argsToSub_nil, bind_id]

/-- **A substitution acts on translated rows as its assignment does.** -/
theorem instantiate_assignOf (eqAt : ℕ → ℕ) (δ : Subst rows) :
    ∀ t : Tm, instantiate (assignOf eqAt δ) (trTm eqAt t) = trTm eqAt (δ.applyTerm t)
  | .var (s, x) => by
      rw [trTm, instantiate_nameD]
      simp [assignOf, Subst.applyTerm]
  | .const k => rfl
  | .app () ts => by
      have zero := instantiate_assignOf eqAt δ (ts 0)
      have one := instantiate_assignOf eqAt δ (ts 1)
      show cellD (instantiate (assignOf eqAt δ) (trTm eqAt (ts 0))) (instantiate (assignOf eqAt δ) (trTm eqAt (ts 1))) =
        trTm eqAt (δ.applyTerm (.app () ts))
      rw [zero, one, Subst.applyTerm_app]
      rfl

/-- **The translation is injective.** -/
theorem trTm_injective (eqAt : ℕ → ℕ) : ∀ t u : Tm, trTm eqAt t = trTm eqAt u → t = u
  | .var (s, x), .var (s', x'), same => by
      simp only [trTm, nameD] at same
      injection same with _ _ hop _
      simp only [Sum.inr.injEq] at hop
      injection hop with hname
      simp only [Name.mk.injEq, List.cons.injEq, and_true, RKey.var.injEq] at hname
      obtain ⟨rfl, _, rfl⟩ := hname
      rfl
  | .var _, .const _, same => by injection same with _ _ hop _; simp at hop
  | .var _, .app () _, same => by injection same with _ _ hop _; simp at hop
  | .const _, .var _, same => by injection same with _ _ hop _; simp at hop
  | .const k, .const k', same => by
      simp only [trTm, constD] at same
      injection same with _ _ hop _
      simp only [Sum.inl.injEq, ROp.const.injEq] at hop
      rw [hop]
  | .const _, .app () _, same => by injection same with _ _ hop _; simp at hop
  | .app () _, .var _, same => by injection same with _ _ hop _; simp at hop
  | .app () _, .const _, same => by injection same with _ _ hop _; simp at hop
  | .app () ts, .app () us, same => by
      simp only [trTm, cellD] at same
      injection same with _ _ _ hargs
      obtain ⟨zero, rest⟩ := Args.cons.inj hargs
      obtain ⟨one, _⟩ := Args.cons.inj rest
      have h0 := trTm_injective eqAt (ts 0) (us 0) zero
      have h1 := trTm_injective eqAt (ts 1) (us 1) one
      have : ts = us := by
        funext i
        match i with
        | ⟨0, _⟩ => exact h0
        | ⟨1, _⟩ => exact h1
      rw [this]

/-- **A substitution unifies a problem of the core exactly when its assignment solves the translated
store.** -/
theorem unifies_iff_models (eqAt : ℕ → ℕ) (δ : Subst rows) (P : List (Tm × Tm)) :
    Unifies δ P ↔ Models (assignOf eqAt δ) (P.map fun e => (trTm eqAt e.1, trTm eqAt e.2)) := by
  constructor
  · intro unified e member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    rw [instantiate_assignOf, instantiate_assignOf, unified original inside]
  · intro solved e member
    have := solved _ (List.mem_map.mpr ⟨e, member, rfl⟩)
    rw [instantiate_assignOf, instantiate_assignOf] at this
    exact trTm_injective eqAt _ _ this

/-! ## Copies of right-hand sides, and arrows that leave other arrows' names alone -/

/-- **Expressions at a path, with their arrows' names at scopes `pre`**: the query has `pre = []`, the
copy of an equation's right-hand side at scope `n` has `pre = [n]`. -/
def trX (eqAt : ℕ → ℕ) (pre : List ℕ) : List ℕ → Ex → Comp rkeys [] () Ty
  | _, .val t => .ret (trTm eqAt t)
  | path, .pair a b =>
      .let_ (.inr (.inl (path ++ [0]))) (nameD ⟨pre, .slot (path ++ [0])⟩) (trX eqAt pre (path ++ [0]) a)
        (.let_ (.inr (.inl (path ++ [1]))) (nameD ⟨pre, .slot (path ++ [1])⟩) (trX eqAt pre (path ++ [1]) b)
          (.ret (cellD (nameD ⟨pre, .slot (path ++ [0])⟩) (nameD ⟨pre, .slot (path ++ [1])⟩))))
  | path, .call a =>
      .let_ (.inr (.inl (path ++ [0]))) (nameD ⟨pre, .slot (path ++ [0])⟩) (trX eqAt pre (path ++ [0]) a)
        (.apply (nameD ⟨pre, .slot (path ++ [0])⟩))

theorem trEx_eq_trX (eqAt : ℕ → ℕ) :
    ∀ (path : List ℕ) (e : Ex), (trEx eqAt path e : Comp rkeys [] () Ty) = trX eqAt [] path e
  | _, .val _ => rfl
  | path, .pair a b => by
      simp only [trEx, trX, slotD, trEx_eq_trX eqAt (path ++ [0]) a, trEx_eq_trX eqAt (path ++ [1]) b]
  | path, .call a => by
      simp only [trEx, trX, slotD, trEx_eq_trX eqAt (path ++ [0]) a]

/-- **The copy at scope `n` of equation `j`'s right-hand side is the translation of the core's
renaming of it into scope `n`**, with the arrows' names at `[n]`. -/
theorem trEPat_at (eqAt : ℕ → ℕ) (n j : ℕ) (same : eqAt n = j) :
    ∀ (path : List ℕ) (e : EPat),
      ((trEPat j path e : Comp rkeys [] () Ty).inst (copyAt rkeys n)) = trX eqAt [n] path (e.at n)
  | _, .val p => by
      show Comp.ret (instantiate (copyAt rkeys n) (trPat j p)) = Comp.ret (trTm eqAt (p.at n))
      rw [trPat_at eqAt n j same p]
  | path, .pair a b => by
      have ha := trEPat_at eqAt n j same (path ++ [0]) a
      have hb := trEPat_at eqAt n j same (path ++ [1]) b
      show Comp.let_ (κ := rkeys) (.inr (.inl (path ++ [0]))) (instantiate (copyAt rkeys n) (slotD (path ++ [0])))
          ((trEPat j (path ++ [0]) a : Comp rkeys [] () Ty).inst (copyAt rkeys n))
          (Comp.let_ (.inr (.inl (path ++ [1]))) (instantiate (copyAt rkeys n) (slotD (path ++ [1])))
            ((trEPat j (path ++ [1]) b : Comp rkeys [] () Ty).inst (copyAt rkeys n))
            (Comp.ret (instantiate (copyAt rkeys n) (cellD (slotD (path ++ [0])) (slotD (path ++ [1])))))) = _
      rw [ha, hb]
      rfl
  | path, .call a => by
      have ha := trEPat_at eqAt n j same (path ++ [0]) a
      show Comp.let_ (κ := rkeys) (.inr (.inl (path ++ [0]))) (instantiate (copyAt rkeys n) (slotD (path ++ [0])))
          ((trEPat j (path ++ [0]) a : Comp rkeys [] () Ty).inst (copyAt rkeys n))
          (Comp.apply (instantiate (copyAt rkeys n) (slotD (path ++ [0])))) = _
      rw [ha]
      rfl

/-- Opening an arrow's site leaves translated rows alone: their names belong to equations. -/
theorem trTm_open (eqAt : ℕ → ℕ) (q : List ℕ ⊕ ℕ) (m : ℕ) :
    ∀ t : Tm, instantiate (openAt rkeys (.inr q) m) (trTm eqAt t) = trTm eqAt t
  | .var (s, x) => by
      rw [trTm, instantiate_nameD]
      rfl
  | .const _ => rfl
  | .app () ts => by
      have zero := trTm_open eqAt q m (ts 0)
      have one := trTm_open eqAt q m (ts 1)
      show cellD (instantiate (openAt rkeys (.inr q) m) (trTm eqAt (ts 0)))
          (instantiate (openAt rkeys (.inr q) m) (trTm eqAt (ts 1))) = trTm eqAt (.app () ts)
      rw [zero, one]
      rfl

/-- An arrow's name is left alone by opening another arrow's site. -/
theorem slot_open (pre r q : List ℕ) (m : ℕ) (different : r ≠ q) :
    instantiate (openAt rkeys (.inr (.inl q)) m) (nameD ⟨pre, .slot r⟩) = nameD ⟨pre, .slot r⟩ := by
  rw [instantiate_nameD]
  show generator (fam rkeys) ⟨if (Sum.inr (Sum.inl r) : ℕ ⊕ (List ℕ ⊕ ℕ)) = .inr (.inl q) then m :: pre else pre,
    .slot r⟩ = _
  rw [if_neg (fun h => different (by simpa using h))]
  rfl

/-- **Opening a site that is not strictly below `path` leaves the translation at `path` alone**: the
arrows of an expression's translation are at sites strictly below its path. -/
theorem trX_open (eqAt : ℕ → ℕ) (pre q : List ℕ) (m : ℕ) :
    ∀ (path : List ℕ) (e : Ex), (∀ r, q = path ++ r → r = []) →
      ((trX eqAt pre path e : Comp rkeys [] () Ty).inst (openAt rkeys (.inr (.inl q)) m)) = trX eqAt pre path e
  | _, .val t, _ => by
      show Comp.ret (instantiate (openAt rkeys (.inr (.inl q)) m) (trTm eqAt t)) = _
      rw [trTm_open]
      rfl
  | path, .pair a b, away => by
      have below : ∀ i, ∀ r, q = (path ++ [i]) ++ r → r = [] := fun i r h => by
        have := away ([i] ++ r) (by rw [h, List.append_assoc])
        simp at this
      have zero : path ++ [0] ≠ q := fun h => by
        have := away [0] (by rw [h])
        simp at this
      have one : path ++ [1] ≠ q := fun h => by
        have := away [1] (by rw [h])
        simp at this
      have ha := trX_open eqAt pre q m (path ++ [0]) a (below 0)
      have hb := trX_open eqAt pre q m (path ++ [1]) b (below 1)
      show Comp.let_ (κ := rkeys) (.inr (.inl (path ++ [0])))
          (instantiate (openAt rkeys (.inr (.inl q)) m) (nameD ⟨pre, .slot (path ++ [0])⟩))
          ((trX eqAt pre (path ++ [0]) a : Comp rkeys [] () Ty).inst (openAt rkeys (.inr (.inl q)) m))
          (Comp.let_ (.inr (.inl (path ++ [1])))
            (instantiate (openAt rkeys (.inr (.inl q)) m) (nameD ⟨pre, .slot (path ++ [1])⟩))
            ((trX eqAt pre (path ++ [1]) b : Comp rkeys [] () Ty).inst (openAt rkeys (.inr (.inl q)) m))
            (Comp.ret (cellD (instantiate (openAt rkeys (.inr (.inl q)) m) (nameD ⟨pre, .slot (path ++ [0])⟩))
              (instantiate (openAt rkeys (.inr (.inl q)) m) (nameD ⟨pre, .slot (path ++ [1])⟩))))) = _
      rw [ha, hb, slot_open pre _ q m zero, slot_open pre _ q m one]
      rfl
  | path, .call a, away => by
      have below : ∀ r, q = (path ++ [0]) ++ r → r = [] := fun r h => by
        have := away ([0] ++ r) (by rw [h, List.append_assoc])
        simp at this
      have zero : path ++ [0] ≠ q := fun h => by
        have := away [0] (by rw [h])
        simp at this
      have ha := trX_open eqAt pre q m (path ++ [0]) a below
      show Comp.let_ (κ := rkeys) (.inr (.inl (path ++ [0])))
          (instantiate (openAt rkeys (.inr (.inl q)) m) (nameD ⟨pre, .slot (path ++ [0])⟩))
          ((trX eqAt pre (path ++ [0]) a : Comp rkeys [] () Ty).inst (openAt rkeys (.inr (.inl q)) m))
          (Comp.apply (instantiate (openAt rkeys (.inr (.inl q)) m) (nameD ⟨pre, .slot (path ++ [0])⟩))) = _
      rw [ha, slot_open pre _ q m zero]
      rfl

/-! ## Solutions over any family read back as unifiers -/

/-- **Rows read back from data over any family.** A cell reads as the node of its parts, a numeral as
itself; a variable or an unknown reads as `0` (the reading is used on translated rows only, where
neither occurs). -/
def readRow {X : Type} {target : X → MetaArity RSig} {Γ : Ctx RSig} {s : Unit} :
    Term (signature RSig target) Γ s → Tm
  | .op (.inl (.const k)) _ => .const k
  | .op (.inl .cell) (.cons a (.cons b .nil)) => node (readRow a) (readRow b)
  | _ => .const 0

theorem readRow_cell {X : Type} {target : X → MetaArity RSig} (a b : Term (signature RSig target) [] ()) :
    readRow (.op (.inl ROp.cell) (.cons a (.cons b .nil)) : Term (signature RSig target) [] ()) =
      node (readRow a) (readRow b) := rfl

theorem readRow_const {X : Type} {target : X → MetaArity RSig} (k : ℕ) :
    readRow (.op (.inl (ROp.const k)) .nil : Term (signature RSig target) [] ()) = .const k := rfl

/-- The core substitution a solution reads back as. -/
def readSubst {X : Type} {target : X → MetaArity RSig} (eqAt : ℕ → ℕ) (σ : Assignment (fam rkeys) target) :
    Subst rows := fun x => readRow (σ ⟨[x.1], .var (eqAt x.1) x.2⟩)

/-- **Reading back is a homomorphism on translated rows.** -/
theorem readRow_trTm {X : Type} {target : X → MetaArity RSig} (eqAt : ℕ → ℕ) (σ : Assignment (fam rkeys) target) :
    ∀ u : Tm, readRow (instantiate σ (trTm eqAt u)) = (readSubst eqAt σ).applyTerm u
  | .var (s, x) => by
      rw [trTm, instantiate_nameD]
      rfl
  | .const k => by
      show readRow (.op (.inl (ROp.const k)) .nil : Term (signature RSig target) [] ()) = _
      rw [readRow_const]
      rfl
  | .app () ts => by
      have zero := readRow_trTm eqAt σ (ts 0)
      have one := readRow_trTm eqAt σ (ts 1)
      show readRow (.op (.inl ROp.cell) (.cons (instantiate σ (trTm eqAt (ts 0)))
        (.cons (instantiate σ (trTm eqAt (ts 1))) .nil)) : Term (signature RSig target) [] ()) = _
      rw [readRow_cell, zero, one, Subst.applyTerm_app]
      show node _ _ = Term.app () _
      unfold node
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl

/-- **A solution of a translated problem, over any family, reads back as a unifier of the problem.** -/
theorem unifies_of_models {X : Type} {target : X → MetaArity RSig} (eqAt : ℕ → ℕ)
    (σ : Assignment (fam rkeys) target) (P : List (Tm × Tm))
    (solved : Models σ (P.map fun e => (trTm eqAt e.1, trTm eqAt e.2))) :
    Unifies (readSubst eqAt σ) P := by
  intro e member
  have same := congrArg readRow (solved _ (List.mem_map.mpr ⟨e, member, rfl⟩))
  rwa [readRow_trTm, readRow_trTm] at same

/-- **The language's knowledge and the core's unification agree on translated problems**: a
translated problem has a solution, over some family, exactly when the core problem has a unifier,
exactly when it has a most general unifier. -/
theorem solvable_iff_unifiable (eqAt : ℕ → ℕ) (P : List (Tm × Tm)) :
    Solvable (P.map fun e => (trTm eqAt e.1, trTm eqAt e.2)) ↔ ∃ δ : Subst rows, Unifies δ P := by
  constructor
  · rintro ⟨X, target, σ, solved⟩
    exact ⟨readSubst eqAt σ, unifies_of_models eqAt σ P solved⟩
  · rintro ⟨δ, unified⟩
    exact ⟨Name rkeys, fam rkeys, assignOf eqAt δ, (unifies_iff_models eqAt δ P).mp unified⟩

theorem solvable_iff_mgu (eqAt : ℕ → ℕ) (P : List (Tm × Tm)) :
    Solvable (P.map fun e => (trTm eqAt e.1, trTm eqAt e.2)) ↔ ∃ θ, ProgramEquationsOpen.IsMGU P θ := by
  rw [solvable_iff_unifiable]
  constructor
  · exact ProgramEquationsOpen.exists_isMGU
  · rintro ⟨θ, mgu⟩
    exact ⟨θ, mgu.unifies⟩

#print axioms trPat_at
#print axioms instantiate_assignOf
#print axioms trTm_injective
#print axioms unifies_iff_models
#print axioms readRow_trTm
#print axioms unifies_of_models
#print axioms solvable_iff_unifiable
#print axioms solvable_iff_mgu
#print axioms trEx_eq_trX
#print axioms trEPat_at
#print axioms trTm_open
#print axioms trX_open

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NestedCore
