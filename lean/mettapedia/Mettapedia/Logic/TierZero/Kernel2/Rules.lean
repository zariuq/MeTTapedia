import Mettapedia.Logic.TierZero.ChildBound
import Mettapedia.Logic.TierZero.Kernel2.Syntax

/-!
# Rules as data, the presentation they define, and the kernel's matching

A **rule** is data, as in the MeTTa kernel's `(admit-rule ID FORMALS PREMISES CONCLUSION)`: a number
of formals, a list of premises and a conclusion pattern. A premise is

* `judg p`: a judgment, discharged by the next child's theorem (matching binds formals);
* `given p`: a term the claim cites by id from its term store (the child `(term TID)`); its
  judgment is `(given T)`;
* a **side condition**, decided by the kernel and consuming no child: `differ`, `absent`, `dv`,
  the relations between sets a claim supplies `union-of`, `remove-of`, `singleton-of`, `image-of`,
  and `atom-kind` (checks), and `isOpen`, `isAbstract`, `isSubst` (a value computed from earlier formals and
  matched against a result pattern, which may bind formals). The computed ones ask their inputs to
  be locally closed, as the MeTTa kernel-v2 does; under that condition its unshifted `open`,
  `abstract` and `subst` are the binder-correct functions of `Syntax`.

Example (`Controls`): `ax-mp` has formals `ph, ps` and premises `(wff ph) (wff ps) (|- ph)
(|- (wi ph ps))`; its conclusion is `(|- ps)`.

## The declarative presentation

`presOf env fr` is the tier-0 presentation of a rule table `env` (rule names of any type `R`) in a
claim's frame `fr`: its judgments are trees, an instance of rule `r` is the list of values of its
formals, and that instance exists exactly when every side condition holds there
(`Rule.instance`). Side conditions are part of instance existence, and `side` is constantly
`false`: no premise of an instance is discharged without a child.

## The kernel's matching

`Rule.solve` is what kernel version 2 does at a node: walk the premises **in order**, matching each
judgment premise against the next child's judgment (`matchT`), checking each side condition on
values already bound, and matching each computed value against its result pattern. A rule is
**determined** (`Rule.determinedB`, checked at admission) when, walking its premises in order,
every side condition's inputs are bound by earlier premises and every formal is bound at the end.

* `solve_sound`: what `solve` returns is an instance whose judgment premises are the children's
  judgments;
* `solve_instance`: for a determined rule, `solve` applied to an instance's judgment premises
  returns exactly that instance's values;
* `matcherOf`: so `solve` is a `ChildBound.Matcher` for `presOf env fr`, and
  `ChildBound.checkCB_iff_derivable` and `Kernel.check_iff_derivable` apply
  (`accepts_iff_derivable`).

Negative example: a rule `(differ a b)` before the premises that bind `a` and `b` is not
determined, so it is refused at admission (`Controls.late_inputs_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero

/-! ## Frames: the claim's names and declared distinct pairs -/

/-- A claim's frame: its names `fv 0 … fv (nvars - 1)` and its declared distinct pairs. -/
structure Frame where
  nvars : ℕ
  dvs : List (Tm × Tm)

/-- The pair `(a, b)` is declared distinct, in either orientation. -/
def Frame.declared (fr : Frame) (a b : ℕ) : Bool :=
  decide ((fvar a, fvar b) ∈ fr.dvs) || decide ((fvar b, fvar a) ∈ fr.dvs)

/-- **Distinctness** (Metamath's `$d`): every frame name of `x` and every frame name of `y` are
different and declared distinct. -/
def Frame.dvOk (fr : Frame) (x y : Tm) : Bool :=
  (fvsOf x).all fun a => (fvsOf y).all fun b =>
    !(decide (a < fr.nvars) && decide (b < fr.nvars)) || (decide (a ≠ b) && fr.declared a b)

/-! ## Premises and rules -/

/-- A premise of a rule. -/
inductive Premise where
  | judg (p : Pat)
  | given (p : Pat)
  | differ (a b : Pat)
  | absent (x b : Pat)
  | dv (x y : Pat)
  | isOpen (r b v : Pat)
  | isAbstract (r x b : Pat)
  | isSubst (r s b : Pat)
  | unionOf (u g d : Pat)
  | removeOf (r x g : Pat)
  | singletonOf (s x : Pat)
  | imageOf (h' s h : Pat)
  | atomKind (x k : Pat)
  | each (x : ℕ) (l p : Pat)

/-- The judgment a `given` premise asks of a cited term. -/
def givenPat (p : Pat) : Pat := pjd "given" [p]

/-- The judgment of a cited term. -/
def givenTm (t : Tm) : Tm := jd "given" [t]

/-- Every key and value of a substitution is locally closed. -/
def pairsClosed (pairs : List (Tm × Tm)) : Bool :=
  pairs.all fun p => Term.supportedAt 0 p.1 && Term.supportedAt 0 p.2

/-- The checks of the side conditions on values. -/
def differOk (x y : Tm) : Bool := decide (x ≠ y)

def absentOk (x b : Tm) : Bool := !occursIn x b

/-- The computed side conditions on values: `none` when the condition fails. -/
def openVal (b v : Tm) : Option Tm :=
  if Term.supportedAt 1 b && Term.supportedAt 0 v then some (openT b v) else none

def abstractVal (x b : Tm) : Option Tm :=
  if Term.supportedAt 0 x && Term.supportedAt 0 b then some (abstractT x b) else none

def substVal (s b : Tm) : Option Tm :=
  match decodePairs s with
  | some pairs => if pairsClosed pairs && Term.supportedAt 0 b then some (substT pairs b) else none
  | none => none

/-! ### Sets and atom kinds

A **set** is the value `(set M₁ … Mₙ)`: its members are `M₁ … Mₙ`, in any order, duplicates allowed;
`(set a b)`, `(set b a)` and `(set a b a)` are one set. Sets are values a claim supplies (cited from
its term store); the kernel checks relations between them and never computes a set, so no order of
terms is involved. -/

/-- The fields of a node, all at depth `0`. -/
def fieldsAtZero : Fields Head → Option (List Tm)
  | .nil => some []
  | .cons 0 t rest => (fieldsAtZero rest).map (t :: ·)
  | .cons (_ + 1) _ _ => none

/-- The members of a set `(set M₁ … Mₙ)`. -/
def setMembers : Tm → Option (List Tm)
  | .node .expr (.cons 0 (.node (.sym "set") .nil) rest) => fieldsAtZero rest
  | _ => none

/-- `(union-of U G D)`: every member of `U` is a member of `G` or of `D`, and every member of `G` and
of `D` is a member of `U`. -/
def unionOfOk (u g d : Tm) : Bool :=
  match setMembers u, setMembers g, setMembers d with
  | some us, some gs, some ds =>
      us.all (fun m => decide (m ∈ gs) || decide (m ∈ ds)) && gs.all (fun m => decide (m ∈ us)) &&
        ds.all (fun m => decide (m ∈ us))
  | _, _, _ => false

/-- `(remove-of R X G)`: every member of `R` is a member of `G` other than `X`, and every member of
`G` is `X` or a member of `R`. -/
def removeOfOk (r x g : Tm) : Bool :=
  match setMembers r, setMembers g with
  | some rs, some gs =>
      rs.all (fun m => decide (m ∈ gs) && decide (m ≠ x)) && gs.all (fun m => decide (m = x) || decide (m ∈ rs))
  | _, _ => false

/-- `(singleton-of S X)`: `S` has the member `X` and no other. -/
def singletonOfOk (s x : Tm) : Bool :=
  match setMembers s with
  | some ms => !ms.isEmpty && ms.all (fun m => decide (m = x))
  | none => false

/-- `(image-of H' S H)`: the members of `H'` are exactly the substitution `S` applied to the
members of `H` (as `subst` does it; members may merge). -/
def imageOfOk (h' s h : Tm) : Bool :=
  match setMembers h', decodePairs s, setMembers h with
  | some hs', some pairs, some hs =>
      pairsClosed pairs && hs.all (Term.supportedAt 0) &&
        ((hs.map (substT pairs)).all (fun m => decide (m ∈ hs')) &&
          hs'.all (fun m => decide (m ∈ hs.map (substT pairs))))
  | _, _, _ => false

/-- A symbol, a number, a string, a claim's fresh name. -/
def isSymAtom : Tm → Bool
  | .node (.sym _) .nil => true
  | _ => false

def isNumAtom : Tm → Bool
  | .node (.num _) .nil => true
  | _ => false

def isStrAtom : Tm → Bool
  | .node (.str _) .nil => true
  | _ => false

def isNameAtom : Tm → Bool
  | .node (.fv _) .nil => true
  | _ => false

/-- `(atom-kind X K)`: `X` is an atom of kind `K`: `symbol`, `number`, `string`, or `name` (a
claim's fresh name). Example: `(atom-kind "x" string)` holds, `(atom-kind x string)` does not. -/
def atomKindOk (x k : Tm) : Bool :=
  (decide (k = sym "symbol") && isSymAtom x) || (decide (k = sym "number") && isNumAtom x) ||
    (decide (k = sym "string") && isStrAtom x) || (decide (k = sym "name") && isNameAtom x)

/-! ### List premises

A **list premise** `(each x L P)` asks, for every element `E` of the list `L = (E₁ … Eₙ)`, in order,
one child proving `P` with `x := E`. Its `x` is local to the premise: a pattern variable numbered past
the rule's formals, so it occurs in no other premise and not in the conclusion. Example: INST's
`(each e S (typed-pair e))` asks one child `(typed-pair (V T))` per pair of the substitution `S`. -/

/-- The elements of a list `(E₁ … Eₙ)`. -/
def listElems : Tm → Option (List Tm)
  | .node .expr fs => fieldsAtZero fs
  | _ => none

/-- A substitution with `x` set to `e`. -/
def updS (σ : Subst ℕ Tm) (x : ℕ) (e : Tm) : Subst ℕ Tm := fun v => if v = x then some e else σ v

/-- **The judgments a list premise asks** of the list value `lv`: `P` with `x := E` for each element
`E`, in order. -/
def eachJudgments (lv : Tm) (x : ℕ) (p : Pat) (σ : Subst ℕ Tm) : Option (List Tm) :=
  (listElems lv).bind fun es => es.mapM fun e => p.inst (updS σ x e)

/-- What a premise does: consume a child's judgment, check its inputs, compute a value and match
it, or consume one child per element of a list. -/
inductive Kind where
  | consume (q : Pat)
  | check (ins : List Pat) (ok : Frame → List Tm → Bool)
  | compute (r : Pat) (ins : List Pat) (f : List Tm → Option Tm)
  | each (l : Pat) (x : ℕ) (p : Pat)

/-- The kind of each premise. -/
def Premise.kind : Premise → Kind
  | .judg p => .consume p
  | .given p => .consume (givenPat p)
  | .differ a b => .check [a, b] fun _ vs => match vs with
      | [x, y] => differOk x y
      | _ => false
  | .absent x b => .check [x, b] fun _ vs => match vs with
      | [xv, bv] => absentOk xv bv
      | _ => false
  | .dv x y => .check [x, y] fun fr vs => match vs with
      | [xv, yv] => fr.dvOk xv yv
      | _ => false
  | .isOpen r b v => .compute r [b, v] fun vs => match vs with
      | [bb, vv] => openVal bb vv
      | _ => none
  | .isAbstract r x b => .compute r [x, b] fun vs => match vs with
      | [xv, bv] => abstractVal xv bv
      | _ => none
  | .isSubst r s b => .compute r [s, b] fun vs => match vs with
      | [sv, bv] => substVal sv bv
      | _ => none
  | .unionOf u g d => .check [u, g, d] fun _ vs => match vs with
      | [uv, gv, dset] => unionOfOk uv gv dset
      | _ => false
  | .removeOf r x g => .check [r, x, g] fun _ vs => match vs with
      | [rv, xv, gv] => removeOfOk rv xv gv
      | _ => false
  | .singletonOf s x => .check [s, x] fun _ vs => match vs with
      | [sv, xv] => singletonOfOk sv xv
      | _ => false
  | .imageOf h' s h => .check [h', s, h] fun _ vs => match vs with
      | [hv', sv, hv] => imageOfOk hv' sv hv
      | _ => false
  | .atomKind x k => .check [x, k] fun _ vs => match vs with
      | [xv, kv] => atomKindOk xv kv
      | _ => false
  | .each x l p => .each l x p

/-- A rule: its formals `0 … nformals - 1`, its premises in order, its conclusion. -/
structure Rule where
  nformals : ℕ
  prems : List Premise
  concl : Pat

/-- The kinds of a rule's premises. -/
def Rule.kinds (ru : Rule) : List Kind := ru.prems.map Premise.kind

/-! ## Instances: the declarative reading -/

/-- Instantiate a list of patterns. -/
def instAll (σ : Subst ℕ Tm) : List Pat → Option (List Tm)
  | [] => some []
  | p :: ps =>
      match p.inst σ, instAll σ ps with
      | some t, some ts => some (t :: ts)
      | _, _ => none

/-- The judgment premises of an instance, when every side condition holds there. -/
def instKinds (fr : Frame) (σ : Subst ℕ Tm) : List Kind → Option (List Tm)
  | [] => some []
  | .consume q :: ks =>
      match q.inst σ, instKinds fr σ ks with
      | some j, some js => some (j :: js)
      | _, _ => none
  | .check ins ok :: ks =>
      match instAll σ ins with
      | some vs => if ok fr vs then instKinds fr σ ks else none
      | none => none
  | .compute r ins f :: ks =>
      match instAll σ ins, r.inst σ with
      | some vs, some rv => if f vs = some rv then instKinds fr σ ks else none
      | _, _ => none
  | .each l x p :: ks =>
      match (l.inst σ).bind (fun lv => eachJudgments lv x p σ), instKinds fr σ ks with
      | some js, some rest => some (js ++ rest)
      | _, _ => none

/-- The substitution of a list of values: formal `v` is the `v`-th value. -/
def substOf (a : List Tm) : Subst ℕ Tm := fun v => a[v]?

/-- **A rule instance**: the values of the formals give the judgment premises and the conclusion,
when every side condition holds. -/
def Rule.instance (fr : Frame) (ru : Rule) (a : List Tm) : Option (List Tm × Tm) :=
  if a.length = ru.nformals then
    match instKinds fr (substOf a) ru.kinds, ru.concl.inst (substOf a) with
    | some ps, some c => some (ps, c)
    | _, _ => none
  else none

/-- A rule table over rule names `R`. -/
abbrev Env (R : Type) := R → Option Rule

/-- **The presentation of a rule table in a frame.** -/
abbrev presOf {R : Type} (env : Env R) (fr : Frame) : Presentation.{0} where
  J := Tm
  R := R
  A := List Tm
  inst r a :=
    match env r with
    | some ru => ru.instance fr a
    | none => none
  side _ := false

instance {R : Type} (env : Env R) (fr : Frame) : DecidableEq (presOf env fr).J :=
  inferInstanceAs (DecidableEq Tm)

/-! ## The kernel's matching -/

/-- Walk the premises in order: match judgment premises against the children's judgments, check
side conditions, match computed values. -/
def solveKinds (fr : Frame) : List Kind → Subst ℕ Tm → List Tm → Option (Subst ℕ Tm)
  | [], σ, js => if js = [] then some σ else none
  | .consume q :: ks, σ, js =>
      match js with
      | [] => none
      | j :: rest =>
          match matchT q σ j with
          | some τ => solveKinds fr ks τ rest
          | none => none
  | .check ins ok :: ks, σ, js =>
      match instAll σ ins with
      | some vs => if ok fr vs then solveKinds fr ks σ js else none
      | none => none
  | .compute r ins f :: ks, σ, js =>
      match instAll σ ins with
      | some vs =>
          match f vs with
          | some v =>
              match matchT r σ v with
              | some τ => solveKinds fr ks τ js
              | none => none
          | none => none
      | none => none
  | .each l x p :: ks, σ, js =>
      match (l.inst σ).bind (fun lv => eachJudgments lv x p σ) with
      | some es => if js.take es.length = es then solveKinds fr ks σ (js.drop es.length) else none
      | none => none

/-- The empty substitution. -/
def emptySubst : Subst ℕ Tm := fun _ => none

/-- **The kernel's matching at a node**: the values of the formals from the children's
judgments. -/
def Rule.solve (fr : Frame) (ru : Rule) (js : List Tm) : Option (List Tm) :=
  match solveKinds fr ru.kinds emptySubst js with
  | some τ => (List.range ru.nformals).mapM τ
  | none => none

/-! ## Determined rules -/

/-- The variables of a list of patterns. -/
def patsVars (ps : List Pat) : Finset ℕ := ps.foldr (fun p acc => p.vars ∪ acc) ∅

/-- The variables of a premise kind. -/
def Kind.vars : Kind → Finset ℕ
  | .consume q => q.vars
  | .check ins _ => patsVars ins
  | .compute r ins _ => r.vars ∪ patsVars ins
  | .each l x p => l.vars ∪ p.vars.erase x

/-- The variables of a list of kinds. -/
def kindsVars (ks : List Kind) : Finset ℕ := ks.foldr (fun k acc => k.vars ∪ acc) ∅

/-- Walk the premises in order with the set of bound formals: side-condition inputs must be bound
already; consumed and computed patterns bind their variables. -/
def detKinds : List Kind → Finset ℕ → Option (Finset ℕ)
  | [], D => some D
  | .consume q :: ks, D => detKinds ks (D ∪ q.vars)
  | .check ins _ :: ks, D => if patsVars ins ⊆ D then detKinds ks D else none
  | .compute r ins _ :: ks, D => if patsVars ins ⊆ D then detKinds ks (D ∪ r.vars) else none
  | .each l x p :: ks, D => if l.vars ∪ p.vars.erase x ⊆ D then detKinds ks D else none

/-- A list premise's variable is past the formals `0 … n-1`. -/
def Kind.localPast (n : ℕ) : Kind → Bool
  | .each _ x _ => decide (n ≤ x)
  | _ => true

/-- **A determined rule**: every variable is a formal; in order, every side condition's inputs are
bound by earlier premises; every formal is bound at the end. -/
def Rule.determinedB (ru : Rule) : Bool :=
  decide (kindsVars ru.kinds ⊆ Finset.range ru.nformals) &&
    decide (ru.concl.vars ⊆ Finset.range ru.nformals) &&
    ru.kinds.all (Kind.localPast ru.nformals) &&
    match detKinds ru.kinds ∅ with
    | some D => decide (Finset.range ru.nformals ⊆ D)
    | none => false

/-! ## Laws of instantiation -/

theorem instAll_extends {σ τ : Subst ℕ Tm} (grow : Extends σ τ) :
    ∀ {ps : List Pat} {vs : List Tm}, instAll σ ps = some vs → instAll τ ps = some vs
  | [], vs, h => h
  | p :: ps, vs, h => by
      simp only [instAll] at h ⊢
      cases hp : p.inst σ with
      | none => rw [hp] at h; simp at h
      | some t =>
          cases hs : instAll σ ps with
          | none => rw [hp, hs] at h; simp at h
          | some ts =>
              rw [hp, hs] at h
              rw [inst_extends hp grow, instAll_extends grow hs]
              exact h

theorem patsVars_cons (p : Pat) (ps : List Pat) : patsVars (p :: ps) = p.vars ∪ patsVars ps := rfl

theorem instAll_local {σ τ : Subst ℕ Tm} :
    ∀ (ps : List Pat), (∀ v ∈ patsVars ps, σ v = τ v) → instAll σ ps = instAll τ ps
  | [], _ => rfl
  | p :: ps, same => by
      simp only [instAll]
      rw [TreePat.inst_local σ τ p (fun v m => same v (by rw [patsVars_cons]; exact Finset.mem_union_left _ m)),
        instAll_local ps (fun v m => same v (by rw [patsVars_cons]; exact Finset.mem_union_right _ m))]

theorem kindsVars_cons (k : Kind) (ks : List Kind) : kindsVars (k :: ks) = k.vars ∪ kindsVars ks := rfl

theorem updS_extends {σ τ : Subst ℕ Tm} (grow : Extends σ τ) (x : ℕ) (e : Tm) :
    Extends (updS σ x e) (updS τ x e) := by
  intro v t h
  simp only [updS] at h ⊢
  split_ifs at h ⊢
  · exact h
  · exact grow v t h

/-- The list premise's judgments depend only on its list's and its pattern's variables. -/
theorem eachAt_local {σ τ : Subst ℕ Tm} {l p : Pat} {x : ℕ}
    (same : ∀ v ∈ (Kind.each l x p).vars, σ v = τ v) :
    (l.inst σ).bind (fun lv => eachJudgments lv x p σ) = (l.inst τ).bind (fun lv => eachJudgments lv x p τ) := by
  simp only [Kind.vars] at same
  rw [TreePat.inst_local σ τ l (fun v m => same v (Finset.mem_union_left _ m))]
  cases l.inst τ with
  | none => rfl
  | some lv =>
      simp only [Option.bind_some, eachJudgments]
      cases listElems lv with
      | none => rfl
      | some es =>
          simp only [Option.bind_some]
          congr 1
          funext e
          apply TreePat.inst_local
          intro v mv
          simp only [updS]
          split_ifs with hv
          · rfl
          · exact same v (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hv, mv⟩))

/-- A list premise's judgments survive extending the substitution. -/
theorem eachAt_extends {σ τ : Subst ℕ Tm} (grow : Extends σ τ) {l p : Pat} {x : ℕ} {es : List Tm}
    (h : (l.inst σ).bind (fun lv => eachJudgments lv x p σ) = some es) :
    (l.inst τ).bind (fun lv => eachJudgments lv x p τ) = some es := by
  cases hl : l.inst σ with
  | none => rw [hl] at h; cases h
  | some lv =>
      rw [hl] at h
      rw [inst_extends hl grow]
      simp only [Option.bind_some, eachJudgments] at h ⊢
      cases hle : listElems lv with
      | none => rw [hle] at h; cases h
      | some ls =>
          rw [hle] at h
          simp only [Option.bind_some] at h ⊢
          clear hle hl
          induction ls generalizing es with
          | nil => exact h
          | cons e ls ih =>
              simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h ⊢
              cases hp : p.inst (updS σ x e) with
              | none => rw [hp] at h; simp at h
              | some j =>
                  rw [hp] at h
                  rw [inst_extends hp (updS_extends grow x e)]
                  cases hr : ls.mapM (fun e => p.inst (updS σ x e)) with
                  | none => rw [hr] at h; simp at h
                  | some js =>
                      rw [hr] at h
                      rw [ih hr]
                      exact h

theorem instKinds_local (fr : Frame) {σ τ : Subst ℕ Tm} :
    ∀ (ks : List Kind), (∀ v ∈ kindsVars ks, σ v = τ v) → instKinds fr σ ks = instKinds fr τ ks
  | [], _ => rfl
  | k :: ks, same => by
      have here : ∀ v ∈ k.vars, σ v = τ v := fun v m => same v (by
        rw [kindsVars_cons]; exact Finset.mem_union_left _ m)
      have rest : ∀ v ∈ kindsVars ks, σ v = τ v := fun v m => same v (by
        rw [kindsVars_cons]; exact Finset.mem_union_right _ m)
      cases k with
      | consume q =>
          simp only [instKinds]
          rw [TreePat.inst_local σ τ q here, instKinds_local fr ks rest]
      | check ins ok =>
          simp only [instKinds]
          rw [instAll_local ins here, instKinds_local fr ks rest]
      | compute r ins f =>
          simp only [Kind.vars] at here
          simp only [instKinds]
          rw [instAll_local ins (fun v m => here v (Finset.mem_union_right _ m)),
            TreePat.inst_local σ τ r (fun v m => here v (Finset.mem_union_left _ m)),
            instKinds_local fr ks rest]
      | each l x p =>
          simp only [instKinds]
          rw [eachAt_local here, instKinds_local fr ks rest]

/-! ## Soundness of the matching -/

/-- **What the walk binds is an instance**: the judgment premises are the children's
judgments. -/
theorem solveKinds_sound (fr : Frame) :
    ∀ (ks : List Kind) (σ τ : Subst ℕ Tm) (js : List Tm), solveKinds fr ks σ js = some τ →
      Extends σ τ ∧ instKinds fr τ ks = some js
  | [], σ, τ, js, h => by
      simp only [solveKinds] at h
      by_cases e : js = []
      · rw [if_pos e] at h; cases h; subst e
        exact ⟨Extends.refl _, rfl⟩
      · rw [if_neg e] at h; cases h
  | .consume q :: ks, σ, τ, js, h => by
      cases js with
      | nil => simp [solveKinds] at h
      | cons j rest =>
          simp only [solveKinds] at h
          cases hm : matchT q σ j with
          | none => rw [hm] at h; cases h
          | some τ1 =>
              rw [hm] at h
              obtain ⟨g1, -, i1⟩ := matchT_sound q σ τ1 j hm
              obtain ⟨g2, i2⟩ := solveKinds_sound fr ks τ1 τ rest h
              refine ⟨g1.trans g2, ?_⟩
              simp only [instKinds, inst_extends i1 g2, i2]
  | .check ins ok :: ks, σ, τ, js, h => by
      simp only [solveKinds] at h
      cases hi : instAll σ ins with
      | none => simp [hi] at h
      | some vs =>
          simp only [hi] at h
          by_cases hok : ok fr vs = true
          · simp only [hok, ↓reduceIte] at h
            obtain ⟨g, i⟩ := solveKinds_sound fr ks σ τ js h
            refine ⟨g, ?_⟩
            simp only [instKinds, instAll_extends g hi, hok, ↓reduceIte, i]
          · simp [hok] at h
  | .compute r ins f :: ks, σ, τ, js, h => by
      simp only [solveKinds] at h
      cases hi : instAll σ ins with
      | none => simp [hi] at h
      | some vs =>
          simp only [hi] at h
          cases hf : f vs with
          | none => simp [hf] at h
          | some v =>
              simp only [hf] at h
              cases hm : matchT r σ v with
              | none => simp [hm] at h
              | some τ1 =>
                  simp only [hm] at h
                  obtain ⟨g1, -, i1⟩ := matchT_sound r σ τ1 v hm
                  obtain ⟨g2, i2⟩ := solveKinds_sound fr ks τ1 τ js h
                  refine ⟨g1.trans g2, ?_⟩
                  simp only [instKinds, instAll_extends (g1.trans g2) hi, inst_extends i1 g2, hf,
                    ↓reduceIte, i2]
  | .each l x p :: ks, σ, τ, js, h => by
      simp only [solveKinds] at h
      cases he : (l.inst σ).bind (fun lv => eachJudgments lv x p σ) with
      | none => rw [he] at h; simp at h
      | some es =>
          rw [he] at h
          simp only at h
          by_cases ht : js.take es.length = es
          · rw [if_pos ht] at h
            obtain ⟨g, i⟩ := solveKinds_sound fr ks σ τ (js.drop es.length) h
            refine ⟨g, ?_⟩
            have split : es ++ js.drop es.length = js := by
              calc es ++ js.drop es.length = js.take es.length ++ js.drop es.length := by rw [ht]
                _ = js := List.take_append_drop _ _
            simp only [instKinds, eachAt_extends g he, i, split]
          · rw [if_neg ht] at h; cases h

/-! ## Completeness of the matching -/

/-- A substitution restricted to a set of variables. -/
def restrict (σ : Subst ℕ Tm) (D : Finset ℕ) : Subst ℕ Tm := fun v => if v ∈ D then σ v else none

theorem restrict_empty (σ : Subst ℕ Tm) : restrict σ ∅ = emptySubst := by
  funext v; simp [restrict, emptySubst]

theorem restrict_extends (σ : Subst ℕ Tm) {D D' : Finset ℕ} (sub : D ⊆ D') :
    Extends (restrict σ D) (restrict σ D') := by
  intro v t h
  simp only [restrict] at h ⊢
  by_cases m : v ∈ D
  · rw [if_pos m] at h; rw [if_pos (sub m)]; exact h
  · rw [if_neg m] at h; cases h

/-- Matching a pattern against its own instance binds exactly its variables. -/
theorem matchT_restrict (σ : Subst ℕ Tm) (D : Finset ℕ) (q : Pat) {t : Tm} (h : q.inst σ = some t) :
    matchT q (restrict σ D) t = some (restrict σ (D ∪ q.vars)) := by
  apply matchT_complete
  · exact restrict_extends σ Finset.subset_union_left
  · intro v notIn
    simp only [restrict, Finset.mem_union, notIn, or_false]
  · rw [← h]
    apply TreePat.inst_local
    intro v m
    simp [restrict, m]

theorem patsVars_restrict {σ : Subst ℕ Tm} {D : Finset ℕ} {ps : List Pat} (sub : patsVars ps ⊆ D) :
    instAll (restrict σ D) ps = instAll σ ps :=
  instAll_local ps fun v m => by simp [restrict, sub m]

/-- **The walk finds every instance**: matching an instance's own judgment premises, in order,
binds exactly the formals the walk has determined so far. -/
theorem solveKinds_complete (fr : Frame) :
    ∀ (ks : List Kind) (σa : Subst ℕ Tm) (D D' : Finset ℕ) (js : List Tm),
      instKinds fr σa ks = some js → detKinds ks D = some D' →
        solveKinds fr ks (restrict σa D) js = some (restrict σa D')
  | [], σa, D, D', js, hi, hd => by
      simp only [instKinds, Option.some.injEq] at hi
      simp only [detKinds, Option.some.injEq] at hd
      subst hi hd
      simp [solveKinds]
  | .consume q :: ks, σa, D, D', js, hi, hd => by
      simp only [instKinds] at hi
      cases hq : q.inst σa with
      | none => rw [hq] at hi; simp at hi
      | some j =>
          cases hr : instKinds fr σa ks with
          | none => rw [hq, hr] at hi; simp at hi
          | some rest =>
              rw [hq, hr] at hi
              simp only [Option.some.injEq] at hi
              subst hi
              simp only [detKinds] at hd
              simp only [solveKinds, matchT_restrict σa D q hq]
              exact solveKinds_complete fr ks σa _ D' rest hr hd
  | .check ins ok :: ks, σa, D, D', js, hi, hd => by
      simp only [detKinds] at hd
      by_cases sub : patsVars ins ⊆ D
      · simp only [sub, ↓reduceIte] at hd
        simp only [instKinds] at hi
        cases ha : instAll σa ins with
        | none => simp [ha] at hi
        | some vs =>
            simp only [ha] at hi
            by_cases hok : ok fr vs = true
            · simp only [hok, ↓reduceIte] at hi
              simp only [solveKinds, patsVars_restrict sub, ha, hok, ↓reduceIte]
              exact solveKinds_complete fr ks σa D D' js hi hd
            · simp [hok] at hi
      · simp [sub] at hd
  | .compute r ins f :: ks, σa, D, D', js, hi, hd => by
      simp only [detKinds] at hd
      by_cases sub : patsVars ins ⊆ D
      · simp only [sub, ↓reduceIte] at hd
        simp only [instKinds] at hi
        cases ha : instAll σa ins with
        | none => simp [ha] at hi
        | some vs =>
            cases hrv : r.inst σa with
            | none => simp [ha, hrv] at hi
            | some rv =>
                simp only [ha, hrv] at hi
                by_cases hf : f vs = some rv
                · simp only [hf, ↓reduceIte] at hi
                  simp only [solveKinds, patsVars_restrict sub, ha, hf, matchT_restrict σa D r hrv]
                  exact solveKinds_complete fr ks σa _ D' js hi hd
                · simp [hf] at hi
      · simp [sub] at hd
  | .each l x p :: ks, σa, D, D', js, hi, hd => by
      simp only [detKinds] at hd
      by_cases sub : l.vars ∪ p.vars.erase x ⊆ D
      · simp only [sub, ↓reduceIte] at hd
        simp only [instKinds] at hi
        cases he : (l.inst σa).bind (fun lv => eachJudgments lv x p σa) with
        | none => rw [he] at hi; simp at hi
        | some es =>
            cases hr : instKinds fr σa ks with
            | none => rw [he, hr] at hi; simp at hi
            | some rest =>
                rw [he, hr] at hi
                simp only [Option.some.injEq] at hi
                subst hi
                have he' : (l.inst (restrict σa D)).bind (fun lv => eachJudgments lv x p (restrict σa D)) =
                    some es := by
                  rw [eachAt_local (σ := restrict σa D) (τ := σa) (fun v m => by simp [restrict, sub m])]
                  exact he
                simp only [solveKinds, he', List.take_left' rfl, List.drop_left' rfl, ↓reduceIte]
                exact solveKinds_complete fr ks σa D D' rest hr hd
      · simp [sub] at hd

/-! ## The matcher -/

theorem mapM_range_eq (τ : Subst ℕ Tm) (a : List Tm) (n : ℕ) (len : a.length = n)
    (agree : ∀ v < n, τ v = a[v]?) : (List.range n).mapM τ = some a := by
  induction n generalizing a with
  | zero =>
      cases a with
      | nil => rfl
      | cons _ _ => simp at len
  | succ n ih =>
      rw [List.range_succ, List.mapM_append]
      obtain ⟨init, last, rfl⟩ : ∃ init last, a = init ++ [last] := by
        cases a using List.reverseRecOn with
        | nil => simp at len
        | append_singleton init last => exact ⟨init, last, rfl⟩
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at len
      have hinit := ih init len fun v hv => by
        rw [agree v (by omega), List.getElem?_append_left (by omega)]
      have hlast : τ n = some last := by
        rw [agree n (by omega), List.getElem?_append_right (by omega)]
        simp [len]
      simp [hinit, hlast]

theorem mapM_range_spec (τ : Subst ℕ Tm) :
    ∀ (n : ℕ) (a : List Tm), (List.range n).mapM τ = some a →
      a.length = n ∧ ∀ v < n, τ v = a[v]?
  | 0, a, h => by
      simp only [List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h; simp
  | n + 1, a, h => by
      rw [List.range_succ, List.mapM_append] at h
      cases hi : (List.range n).mapM τ with
      | none => rw [hi] at h; simp at h
      | some init =>
          cases hl : τ n with
          | none => simp [hi, hl] at h
          | some last =>
              simp only [hi, hl, List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
                Option.bind_some, Option.some.injEq] at h
              obtain ⟨len, agree⟩ := mapM_range_spec τ n init hi
              subst h
              refine ⟨by simp [len], fun v hv => ?_⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hv with lt | rfl
              · rw [agree v lt, List.getElem?_append_left (by omega)]
              · rw [hl, List.getElem?_append_right (by omega)]
                simp [len]

theorem determined_parts {ru : Rule} (h : ru.determinedB = true) :
    kindsVars ru.kinds ⊆ Finset.range ru.nformals ∧ ru.concl.vars ⊆ Finset.range ru.nformals ∧
      ∃ D, detKinds ru.kinds ∅ = some D ∧ Finset.range ru.nformals ⊆ D := by
  simp only [Rule.determinedB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  cases hd : detKinds ru.kinds ∅ with
  | none => rw [hd] at h3; cases h3
  | some D => rw [hd] at h3; exact ⟨D, rfl, of_decide_eq_true h3⟩

/-- **Soundness of the kernel's matching**: its answer is an instance whose judgment premises are
the children's judgments. -/
theorem solve_sound (fr : Frame) {ru : Rule} (det : ru.determinedB = true) {js a : List Tm}
    (h : ru.solve fr js = some a) : ∃ c, ru.instance fr a = some (js, c) := by
  obtain ⟨varsIn, conclIn, -⟩ := determined_parts det
  unfold Rule.solve at h
  cases hs : solveKinds fr ru.kinds emptySubst js with
  | none => rw [hs] at h; cases h
  | some τ =>
      rw [hs] at h
      obtain ⟨len, agree⟩ := mapM_range_spec τ ru.nformals a h
      obtain ⟨-, inst⟩ := solveKinds_sound fr ru.kinds emptySubst τ js hs
      have same : ∀ v ∈ Finset.range ru.nformals, τ v = substOf a v :=
        fun v m => agree v (Finset.mem_range.mp m)
      have inst' : instKinds fr (substOf a) ru.kinds = some js := by
        rw [← instKinds_local fr ru.kinds (fun v m => same v (varsIn m))]; exact inst
      have bound : ∀ v ∈ ru.concl.vars, (substOf a v).isSome := by
        intro v m
        have lt := Finset.mem_range.mp (conclIn m)
        simp [substOf, len, lt]
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ((TreePat.inst_isSome _ _).mpr bound)
      refine ⟨c, ?_⟩
      simp [Rule.instance, len, inst', hc]

/-- **Completeness of the kernel's matching**: for a determined rule, matching an instance's own
judgment premises returns that instance. -/
theorem solve_instance (fr : Frame) {ru : Rule} (det : ru.determinedB = true) {a ps : List Tm}
    {c : Tm} (h : ru.instance fr a = some (ps, c)) : ru.solve fr ps = some a := by
  obtain ⟨-, -, D, hd, cover⟩ := determined_parts det
  unfold Rule.instance at h
  by_cases len : a.length = ru.nformals
  · rw [if_pos len] at h
    cases hi : instKinds fr (substOf a) ru.kinds with
    | none => rw [hi] at h; cases h
    | some ps' =>
        cases hc : ru.concl.inst (substOf a) with
        | none => rw [hi, hc] at h; cases h
        | some c' =>
            rw [hi, hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have run := solveKinds_complete fr ru.kinds (substOf a) ∅ D ps' hi hd
            rw [restrict_empty] at run
            unfold Rule.solve
            rw [run]
            exact mapM_range_eq _ a ru.nformals len fun v hv => by
              simp [restrict, cover (Finset.mem_range.mpr hv), substOf]
  · rw [if_neg len] at h; cases h

/-- Every rule of the table is determined. -/
def EnvDetermined {R : Type} (env : Env R) : Prop := ∀ r ru, env r = some ru → ru.determinedB = true

theorem judgmentPremises_presOf {R : Type} (env : Env R) (fr : Frame) (ps : List (presOf env fr).J) :
    ChildBound.judgmentPremises (presOf env fr) ps = ps := by
  unfold ChildBound.judgmentPremises
  exact List.filter_eq_self.mpr fun _ _ => rfl

/-- The kernel's matching at a rule name. -/
def solveEnv {R : Type} (env : Env R) (fr : Frame) (r : R) (js : List Tm) : Option (List Tm) :=
  match env r with
  | some ru => ru.solve fr js
  | none => none

/-- **The kernel's matching is a `ChildBound.Matcher`** for the presentation of a table of
determined rules. -/
def matcherOf {R : Type} (env : Env R) (fr : Frame) (wf : EnvDetermined env) :
    ChildBound.Matcher (presOf env fr) where
  solve := solveEnv env fr
  sound := by
    intro r js a h
    simp only [solveEnv] at h
    cases he : env r with
    | none => simp only [he] at h; cases h
    | some ru =>
        simp only [he] at h
        obtain ⟨c, hc⟩ := solve_sound fr (wf r ru he) h
        exact ⟨js, c, by simp [presOf, he, hc], judgmentPremises_presOf env fr js⟩
  complete := by
    intro r a ps c h
    rw [judgmentPremises_presOf]
    cases he : env r with
    | none => simp [presOf, he] at h
    | some ru =>
        simp only [presOf, he] at h
        simp only [solveEnv, he, solve_instance fr (wf r ru he) h]
        rfl
  determined := by
    intro r a a' ps c ps' c' h h' same
    rw [judgmentPremises_presOf, judgmentPremises_presOf] at same
    subst same
    cases he : env r with
    | none => simp [presOf, he] at h
    | some ru =>
        simp only [presOf, he] at h h'
        have e1 := solve_instance fr (wf r ru he) h
        have e2 := solve_instance fr (wf r ru he) h'
        rw [e1] at e2
        cases e2
        rw [h] at h'
        cases h'
        exact ⟨rfl, rfl⟩

/-- **Kernel version 2 over rule data accepts exactly the derivable judgments** of the
presentation, by the refinement `ChildBound.checkCB_iff_derivable` of `Kernel.check_iff_derivable`. -/
theorem accepts_iff_derivable {R : Type} (env : Env R) (fr : Frame) (wf : EnvDetermined env)
    (hyps : List Tm) (goal : Tm) :
    (∃ proof root, ChildBound.checkCB (matcherOf env fr wf) hyps proof root goal = true) ↔
      Derivable (presOf env fr) hyps goal :=
  ChildBound.checkCB_iff_derivable (matcherOf env fr wf) hyps goal

/-! ## Rule tables from lists -/

/-- The rule table of a list. -/
def envOf {R : Type} [BEq R] (rs : List (R × Rule)) : Env R := fun r => rs.lookup r

theorem lookup_mem {R : Type} [BEq R] [LawfulBEq R] {rs : List (R × Rule)} {r : R} {ru : Rule}
    (h : rs.lookup r = some ru) : (r, ru) ∈ rs := by
  induction rs with
  | nil => simp at h
  | cons x rest ih =>
      obtain ⟨k, v⟩ := x
      simp only [List.lookup] at h
      by_cases e : (r == k) = true
      · rw [e] at h
        simp only [Option.some.injEq] at h
        subst h
        have : r = k := by simpa using e
        subst this
        exact List.mem_cons_self
      · simp only [Bool.not_eq_true] at e
        rw [e] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem envOf_determined {R : Type} [BEq R] [LawfulBEq R] {rs : List (R × Rule)}
    (all : rs.all (fun x => x.2.determinedB) = true) : EnvDetermined (envOf rs) := by
  intro r ru h
  have mem := lookup_mem h
  exact (List.all_eq_true.mp all) _ mem

/-! ## Controls -/

namespace Controls

/-- `(wi a b)`. -/
def wi (a b : Pat) : Pat := pex [psym "wi", a, b]

/-- A Metamath-shaped presentation: a syntax rule, two axioms, modus ponens, and HOL-style
reflexivity whose term is no premise's, so it is a `given`. -/
def rules : List (String × Rule) :=
  [ ("wi", ⟨2, [.judg (pjd "wff" [pv 0]), .judg (pjd "wff" [pv 1])], pjd "wff" [wi (pv 0) (pv 1)]⟩),
    ("ax-1", ⟨2, [.judg (pjd "wff" [pv 0]), .judg (pjd "wff" [pv 1])],
      pjd "|-" [wi (pv 0) (wi (pv 1) (pv 0))]⟩),
    ("ax-2", ⟨3, [.judg (pjd "wff" [pv 0]), .judg (pjd "wff" [pv 1]), .judg (pjd "wff" [pv 2])],
      pjd "|-" [wi (wi (pv 0) (wi (pv 1) (pv 2))) (wi (wi (pv 0) (pv 1)) (wi (pv 0) (pv 2)))]⟩),
    ("ax-mp", ⟨2, [.judg (pjd "wff" [pv 0]), .judg (pjd "wff" [pv 1]), .judg (pjd "|-" [pv 0]),
      .judg (pjd "|-" [wi (pv 0) (pv 1)])], pjd "|-" [pv 1]⟩),
    ("refl", ⟨1, [.given (pv 0)], pjd "eqj" [pv 0, pv 0]⟩) ]

theorem rules_determined : rules.all (fun x => x.2.determinedB) = true := by decide

/-- A rule whose conclusion mentions a formal no premise binds is not determined. -/
theorem undetermined_refused :
    (⟨2, [.judg (pjd "wff" [pv 0])], pjd "|-" [wi (pv 0) (pv 1)]⟩ : Rule).determinedB = false := by
  decide

/-- A side condition before the premises binding its inputs is not determined (F1). -/
theorem late_inputs_refused :
    (⟨2, [.differ (pv 0) (pv 1), .judg (pjd "wff" [pv 0]), .judg (pjd "wff" [pv 1])],
      pjd "wff" [pv 0]⟩ : Rule).determinedB = false := by
  decide

/-- The same side condition after them is. -/
theorem early_inputs_admitted :
    (⟨2, [.judg (pjd "wff" [pv 0]), .judg (pjd "wff" [pv 1]), .differ (pv 0) (pv 1)],
      pjd "wff" [pv 0]⟩ : Rule).determinedB = true := by
  decide

/-- The claim's name `ph`. -/
def ph : Tm := fvar 0

def wiT (a b : Tm) : Tm := ex [sym "wi", a, b]

/-- The presentation in the frame of one name. -/
abbrev P1 : Presentation.{0} := presOf (envOf rules) ⟨1, []⟩

/-- `|- (wi ph ph)` from the hypothesis `wff ph`: every node is a rule and its children. -/
def idProof : List (ChildBound.CNode P1) :=
  [ ("wi", [.hyp 0, .hyp 0]),                       -- 0: wff (ph → ph)
    ("wi", [.hyp 0, .node 0]),                      -- 1: wff (ph → (ph → ph))
    ("wi", [.node 0, .hyp 0]),                      -- 2: wff ((ph → ph) → ph)
    ("ax-2", [.hyp 0, .node 0, .hyp 0]),            -- 3
    ("ax-1", [.hyp 0, .node 0]),                    -- 4
    ("wi", [.hyp 0, .node 2]),                      -- 5: wff (ph → ((ph → ph) → ph))
    ("wi", [.node 1, .node 0]),                     -- 6
    ("ax-mp", [.node 5, .node 6, .node 4, .node 3]),-- 7
    ("ax-1", [.hyp 0, .hyp 0]),                     -- 8
    ("ax-mp", [.node 1, .node 0, .node 8, .node 7]) -- 9: |- (ph → ph)
  ]

theorem id_accepted :
    ChildBound.checkCB (matcherOf (envOf rules) ⟨1, []⟩ (envOf_determined rules_determined))
      [jd "wff" [ph]] idProof (.node 9) (jd "|-" [wiT ph ph]) = true := by
  decide

/-- The last `ax-mp` with its two `|-` children swapped is refused. -/
theorem swapped_refused :
    ChildBound.checkCB (matcherOf (envOf rules) ⟨1, []⟩ (envOf_determined rules_determined))
      [jd "wff" [ph]]
      (idProof.take 9 ++ ([("ax-mp", [Kid.node 1, Kid.node 0, Kid.node 7, Kid.node 8])] :
        List (ChildBound.CNode P1)))
      (.node 9) (jd "|-" [wiT ph ph]) = false := by
  decide

/-- Reflexivity at a term cited from the claim's store: the child is the term's `given`. -/
theorem refl_accepted :
    ChildBound.checkCB (matcherOf (envOf rules) ⟨0, []⟩ (envOf_determined rules_determined))
      [givenTm (ex [sym "f", sym "c"])] [("refl", [.hyp 0])] (.node 0)
      (jd "eqj" [ex [sym "f", sym "c"], ex [sym "f", sym "c"]]) = true := by
  decide

/-- A `given` premise is not discharged by an ordinary judgment. -/
theorem refl_needs_given :
    ChildBound.checkCB (matcherOf (envOf rules) ⟨1, []⟩ (envOf_determined rules_determined))
      [jd "wff" [ph]] [("refl", [.hyp 0])] (.node 0) (jd "eqj" [ph, ph]) = false := by
  decide

/-- `beta` as in `v2_06_binders`: an open with locally closed inputs. -/
def beta : Rule :=
  ⟨3, [.judg (pjd "tm" [pex [psym "lam", pv 0]]), .judg (pjd "tm" [pv 1]), .isOpen (pv 2) (pv 0) (pv 1)],
    pjd "eqb" [pex [psym "app", pex [psym "lam", pv 0], pv 1], pv 2]⟩

theorem beta_determined : beta.determinedB = true := by decide

/-- The body `(f (bv 0) (bind a (g (bv 0) (bv 1))))` of `beta-ok`. -/
def betaBody : Tm := ex [sym "f", .idx 0, bnd (sym "a") (ex [sym "g", .idx 0, .idx 1])]

/-- Positive (`beta-ok`): `c` goes in at index `0` and at index `1` under the inner binder. -/
theorem beta_ok :
    beta.solve ⟨0, []⟩ [jd "tm" [ex [sym "lam", betaBody]], jd "tm" [sym "c"]] =
      some [betaBody, sym "c", ex [sym "f", sym "c", bnd (sym "a") (ex [sym "g", .idx 0, sym "c"])]] := by
  decide

/-- Negative (`beta-dangling`): the value `(bv 0)` is not locally closed. -/
theorem beta_dangling :
    beta.solve ⟨0, []⟩ [jd "tm" [ex [sym "lam", ex [sym "f", .idx 0]]], jd "tm" [.idx 0]] = none := by
  decide

end Controls

end Mettapedia.Logic.TierZero.Kernel2
