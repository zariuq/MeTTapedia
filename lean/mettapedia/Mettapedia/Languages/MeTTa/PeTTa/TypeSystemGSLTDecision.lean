import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard

/-!
# Decision semantics for the PeTTa guard system (four-valued,
proof-carrying, exhaustion separated)

A runtime verdict is a non-monotone decision over derivability — and a
bounded search that runs out of fuel is NOT evidence of semantic absence.
This module gives the guard system its decision semantics with the
audited defect repaired: `incomplete` (a resource bound) is its own
verdict, never conflated with `undetermined` (semantic openness).

The architecture is PROOF-CARRYING: the search functions return
CERTIFICATES (evidence trees mirroring the guard presentation's rules
node for node), a small structural checker validates them, and the
decision function trusts only checked certificates.  Soundness of the
whole decision is therefore one induction family over certificates —
`check = true → derivable` — instead of an induction over the search
functions' shapes.  The certificates are also exactly the derivation
evidence the runtime harness owes the generic checker for replay, and
the typed decision plan of the specialization step compiles THIS
function, with these theorems as its correspondence obligations.

Scope of this version, stated exactly: the refuted/established verdicts
are proven sound against the inductive derivability relations below
(which mirror the presentation's rules; rule identifiers cited).  The
completeness direction — `undetermined` implies genuine underivability —
is the named next obligation of the correspondence arc, not claimed
here.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDecision

/-! ## The typed mirror of the guard algebra -/

inductive Mode where
  | plain | det | semidet | nondet
deriving Repr, DecidableEq

inductive Ty where
  | num | str | bool | undefined
  | nominal (name : String)
  | union (members : List Ty)
  | list (element : Ty)
  | ctor (name : String) (arity : Nat)
deriving Repr

inductive DeclBody where
  | plain (type : Ty)
  | newtype (representation : Ty)
  | alias (representation : Ty)
deriving Repr

abbrev Env := List (String × DeclBody)

inductive Val where
  | num | str | vtrue | vfalse
  | nil
  | cons (head tail : Val)
  | sym (name : String)
deriving Repr, DecidableEq

def Val.baseSort? : Val → Option Ty
  | .num => some .num
  | .str => some .str
  | .vtrue => some .bool
  | .vfalse => some .bool
  | _ => none

def Mode.committed : Mode → Bool
  | .det | .semidet => true
  | _ => false

/-- Base sorts as tags, so base-pair disequality never needs full `Ty`
equality (the union constructor's nested list blocks derived
`DecidableEq`). -/
def Ty.baseTag : Ty → Option Nat
  | .num => some 0
  | .str => some 1
  | .bool => some 2
  | _ => none

def Ty.isBase (t : Ty) : Bool := t.baseTag.isSome

def Env.lookup (env : Env) (name : String) : List DeclBody :=
  env.filterMap fun entry =>
    if entry.1 = name then some entry.2 else none

/-- A declaration body resolves a nominal name transparently. -/
def DeclBody.resolves : DeclBody → Option Ty
  | .newtype r => some r
  | .alias r => some r
  | .plain _ => none

/-- Indexed transparent resolution: the certificate names WHICH
declaration resolved, so checking is deterministic. -/
def resolveAt (env : Env) (name : String) (index : Nat) : Option Ty :=
  ((env.lookup name)[index]?).bind DeclBody.resolves

theorem resolveAt_sound {env name index r}
    (h : resolveAt env name index = some r) :
    ∃ body, body ∈ env.lookup name ∧ body.resolves = some r := by
  unfold resolveAt at h
  cases hbody : (env.lookup name)[index]? with
  | none => rw [hbody] at h; cases h
  | some body =>
      rw [hbody] at h
      exact ⟨body, List.mem_of_getElem? hbody, h⟩

/-! ## Inductive derivability (the semantic model; rule identifiers of the
guard presentation cited on each constructor) -/

inductive SortConflicts : Env → Ty → Ty → Prop where
  /-- `sc-num-str` ... `sc-bool-str`. -/
  | base {env} {s t : Ty} {a b : Nat} :
      s.baseTag = some a → t.baseTag = some b → a ≠ b →
      SortConflicts env s t
  /-- `sc-newtype-formal` / `sc-alias-formal`. -/
  | resolveFormal {env s name body r} :
      body ∈ env.lookup name → body.resolves = some r →
      SortConflicts env s r →
      SortConflicts env s (.nominal name)
  /-- `sc-newtype-sort` / `sc-alias-sort`. -/
  | resolveSort {env name body r t} :
      body ∈ env.lookup name → body.resolves = some r →
      SortConflicts env r t →
      SortConflicts env (.nominal name) t

inductive Mismatch : Env → Val → Ty → Prop where
  /-- `dm-base`. -/
  | base {env v s t} :
      v.baseSort? = some s → SortConflicts env s t →
      Mismatch env v t
  /-- `dm-ctor`. -/
  | literalCtor {env v s name arity} :
      v.baseSort? = some s → Mismatch env v (.ctor name arity)
  /-- `dm-list-literal`. -/
  | literalList {env v s t} :
      v.baseSort? = some s → Mismatch env v (.list t)
  /-- `dm-list-here` / `dm-list-there`. -/
  | listHere {env v vs t} :
      Mismatch env v t → Mismatch env (.cons v vs) (.list t)
  | listThere {env v vs t} :
      Mismatch env vs (.list t) → Mismatch env (.cons v vs) (.list t)
  /-- `dm-newtype-formal` / `dm-alias-formal`. -/
  | resolveFormal {env v name body r} :
      body ∈ env.lookup name → body.resolves = some r →
      Mismatch env v r → Mismatch env v (.nominal name)

/-- The core `ValueHasType`, environment-extended
(`has-type-*` rules). -/
inductive HasType : Env → Val → Ty → Prop where
  | num {env} : HasType env .num .num
  | str {env} : HasType env .str .str
  | vtrue {env} : HasType env .vtrue .bool
  | vfalse {env} : HasType env .vfalse .bool
  | wildcard {env v} : HasType env v .undefined
  | nilList {env t} : HasType env .nil (.list t)
  | consList {env v vs t} :
      HasType env v t → HasType env vs (.list t) →
      HasType env (.cons v vs) (.list t)
  | resolve {env v name body r} :
      body ∈ env.lookup name → body.resolves = some r →
      HasType env v r → HasType env v (.nominal name)

/-! ## Certificates: evidence trees, one node shape per rule -/

inductive SCCert where
  | base
  | resolveFormal (index : Nat) (inner : SCCert)
  | resolveSort (index : Nat) (inner : SCCert)
deriving Repr, DecidableEq

inductive MMCert where
  | base (inner : SCCert)
  | literalCtor
  | literalList
  | listHere (inner : MMCert)
  | listThere (inner : MMCert)
  | resolveFormal (index : Nat) (inner : MMCert)
deriving Repr, DecidableEq

inductive HTCert where
  | literal
  | wildcard
  | nilList
  | consList (head tail : HTCert)
  | resolve (index : Nat) (inner : HTCert)
deriving Repr, DecidableEq

/-! ## Certificate checkers (small, structural, total) -/

def SCCert.check (env : Env) : SCCert → Ty → Ty → Bool
  | .base, s, t =>
      match s.baseTag, t.baseTag with
      | some a, some b => a != b
      | _, _ => false
  | .resolveFormal index inner, s, .nominal name =>
      match resolveAt env name index with
      | some r => inner.check env s r
      | none => false
  | .resolveFormal _ _, _, _ => false
  | .resolveSort index inner, .nominal name, t =>
      match resolveAt env name index with
      | some r => inner.check env r t
      | none => false
  | .resolveSort _ _, _, _ => false

def MMCert.check (env : Env) : MMCert → Val → Ty → Bool
  | .base inner, v, t =>
      match v.baseSort? with
      | some s => inner.check env s t
      | none => false
  | .literalCtor, v, .ctor _ _ => (v.baseSort?).isSome
  | .literalCtor, _, _ => false
  | .literalList, v, .list _ => (v.baseSort?).isSome
  | .literalList, _, _ => false
  | .listHere inner, .cons head _, .list element =>
      inner.check env head element
  | .listHere _, _, _ => false
  | .listThere inner, .cons _ tail, .list element =>
      inner.check env tail (.list element)
  | .listThere _, _, _ => false
  | .resolveFormal index inner, v, .nominal name =>
      match resolveAt env name index with
      | some r => inner.check env v r
      | none => false
  | .resolveFormal _ _, _, _ => false

def HTCert.check (env : Env) : HTCert → Val → Ty → Bool
  | .literal, v, t =>
      match v, t with
      | .num, .num | .str, .str | .vtrue, .bool | .vfalse, .bool => true
      | _, _ => false
  | .wildcard, _, .undefined => true
  | .wildcard, _, _ => false
  | .nilList, .nil, .list _ => true
  | .nilList, _, _ => false
  | .consList headCert tailCert, .cons head tail, .list element =>
      headCert.check env head element &&
      tailCert.check env tail (.list element)
  | .consList _ _, _, _ => false
  | .resolve index inner, v, .nominal name =>
      match resolveAt env name index with
      | some r => inner.check env v r
      | none => false
  | .resolve _ _, _, _ => false

/-! ## Checker soundness: a checked certificate IS a derivation -/

theorem SCCert.check_sound (env : Env) :
    ∀ (cert : SCCert) (s t : Ty), cert.check env s t = true →
      SortConflicts env s t := by
  intro cert
  induction cert with
  | base =>
      intro s t h
      simp only [check] at h
      match ha : s.baseTag, hb : t.baseTag with
      | some a, some b =>
          rw [ha, hb] at h
          simp only [bne_iff_ne, ne_eq] at h
          exact SortConflicts.base ha hb h
      | some _, none => rw [ha, hb] at h; cases h
      | none, _ => rw [ha] at h; cases h
  | resolveFormal index inner ih =>
      intro s t h
      match t with
      | .nominal name =>
          simp only [check] at h
          cases hres : resolveAt env name index with
          | none => rw [hres] at h; cases h
          | some r =>
              rw [hres] at h
              obtain ⟨body, hmem, hbody⟩ := resolveAt_sound hres
              exact SortConflicts.resolveFormal hmem hbody (ih s r h)
      | .num | .str | .bool | .undefined | .union _ | .list _
      | .ctor _ _ => simp [check] at h
  | resolveSort index inner ih =>
      intro s t h
      match s with
      | .nominal name =>
          simp only [check] at h
          cases hres : resolveAt env name index with
          | none => rw [hres] at h; cases h
          | some r =>
              rw [hres] at h
              obtain ⟨body, hmem, hbody⟩ := resolveAt_sound hres
              exact SortConflicts.resolveSort hmem hbody (ih r t h)
      | .num | .str | .bool | .undefined | .union _ | .list _
      | .ctor _ _ => simp [check] at h

theorem MMCert.check_sound (env : Env) :
    ∀ (cert : MMCert) (v : Val) (t : Ty), cert.check env v t = true →
      Mismatch env v t := by
  intro cert
  induction cert with
  | base inner =>
      intro v t h
      simp only [check] at h
      match hsort : v.baseSort? with
      | some s =>
          rw [hsort] at h
          exact Mismatch.base hsort (SCCert.check_sound env inner s t h)
      | none => rw [hsort] at h; cases h
  | literalCtor =>
      intro v t h
      match t with
      | .ctor name arity =>
          simp only [check, Option.isSome] at h
          match hsort : v.baseSort? with
          | some s => exact Mismatch.literalCtor hsort
          | none => rw [hsort] at h; cases h
      | .num | .str | .bool | .undefined | .union _ | .list _
      | .nominal _ => simp [check] at h
  | literalList =>
      intro v t h
      match t with
      | .list element =>
          simp only [check, Option.isSome] at h
          match hsort : v.baseSort? with
          | some s => exact Mismatch.literalList hsort
          | none => rw [hsort] at h; cases h
      | .num | .str | .bool | .undefined | .union _ | .ctor _ _
      | .nominal _ => simp [check] at h
  | listHere inner ih =>
      intro v t h
      match v, t with
      | .cons head tail, .list element =>
          simp only [check] at h
          exact Mismatch.listHere (ih head element h)
      | .num, _ | .str, _ | .vtrue, _ | .vfalse, _ | .nil, _
      | .sym _, _ => simp [check] at h
      | .cons _ _, .num | .cons _ _, .str | .cons _ _, .bool
      | .cons _ _, .undefined | .cons _ _, .union _
      | .cons _ _, .ctor _ _ | .cons _ _, .nominal _ =>
          simp [check] at h
  | listThere inner ih =>
      intro v t h
      match v, t with
      | .cons head tail, .list element =>
          simp only [check] at h
          exact Mismatch.listThere (ih tail (.list element) h)
      | .num, _ | .str, _ | .vtrue, _ | .vfalse, _ | .nil, _
      | .sym _, _ => simp [check] at h
      | .cons _ _, .num | .cons _ _, .str | .cons _ _, .bool
      | .cons _ _, .undefined | .cons _ _, .union _
      | .cons _ _, .ctor _ _ | .cons _ _, .nominal _ =>
          simp [check] at h
  | resolveFormal index inner ih =>
      intro v t h
      match t with
      | .nominal name =>
          simp only [check] at h
          cases hres : resolveAt env name index with
          | none => rw [hres] at h; cases h
          | some r =>
              rw [hres] at h
              obtain ⟨body, hmem, hbody⟩ := resolveAt_sound hres
              exact Mismatch.resolveFormal hmem hbody (ih v r h)
      | .num | .str | .bool | .undefined | .union _ | .list _
      | .ctor _ _ => simp [check] at h

theorem HTCert.check_sound (env : Env) :
    ∀ (cert : HTCert) (v : Val) (t : Ty), cert.check env v t = true →
      HasType env v t := by
  intro cert
  induction cert with
  | literal =>
      intro v t h
      match v, t with
      | .num, .num => exact HasType.num
      | .str, .str => exact HasType.str
      | .vtrue, .bool => exact HasType.vtrue
      | .vfalse, .bool => exact HasType.vfalse
      | .num, .str | .num, .bool | .num, .undefined | .num, .union _
      | .num, .list _ | .num, .ctor _ _ | .num, .nominal _
      | .str, .num | .str, .bool | .str, .undefined | .str, .union _
      | .str, .list _ | .str, .ctor _ _ | .str, .nominal _
      | .vtrue, .num | .vtrue, .str | .vtrue, .undefined
      | .vtrue, .union _ | .vtrue, .list _ | .vtrue, .ctor _ _
      | .vtrue, .nominal _
      | .vfalse, .num | .vfalse, .str | .vfalse, .undefined
      | .vfalse, .union _ | .vfalse, .list _ | .vfalse, .ctor _ _
      | .vfalse, .nominal _
      | .nil, _ | .cons _ _, _ | .sym _, _ => simp [check] at h
  | wildcard =>
      intro v t h
      match t with
      | .undefined => exact HasType.wildcard
      | .num | .str | .bool | .union _ | .list _ | .ctor _ _
      | .nominal _ => simp [check] at h
  | nilList =>
      intro v t h
      match v, t with
      | .nil, .list _ => exact HasType.nilList
      | .num, _ | .str, _ | .vtrue, _ | .vfalse, _ | .cons _ _, _
      | .sym _, _ => simp [check] at h
      | .nil, .num | .nil, .str | .nil, .bool | .nil, .undefined
      | .nil, .union _ | .nil, .ctor _ _ | .nil, .nominal _ =>
          simp [check] at h
  | consList headCert tailCert ihHead ihTail =>
      intro v t h
      match v, t with
      | .cons head tail, .list element =>
          simp only [check, Bool.and_eq_true] at h
          exact HasType.consList (ihHead head element h.1)
            (ihTail tail (.list element) h.2)
      | .num, _ | .str, _ | .vtrue, _ | .vfalse, _ | .nil, _
      | .sym _, _ => simp [check] at h
      | .cons _ _, .num | .cons _ _, .str | .cons _ _, .bool
      | .cons _ _, .undefined | .cons _ _, .union _
      | .cons _ _, .ctor _ _ | .cons _ _, .nominal _ =>
          simp [check] at h
  | resolve index inner ih =>
      intro v t h
      match t with
      | .nominal name =>
          simp only [check] at h
          cases hres : resolveAt env name index with
          | none => rw [hres] at h; cases h
          | some r =>
              rw [hres] at h
              obtain ⟨body, hmem, hbody⟩ := resolveAt_sound hres
              exact HasType.resolve hmem hbody (ih v r h)
      | .num | .str | .bool | .undefined | .union _ | .list _
      | .ctor _ _ => simp [check] at h

/-! ## Proof-carrying search -/

inductive Found (α : Type) where
  | yes (certificate : α)
  | no
  | out
deriving Repr

def searchSortConflicts : Nat → Env → Ty → Ty → Found SCCert
  | 0, _, _, _ => .out
  | fuel + 1, env, s, t =>
      if (match s.baseTag, t.baseTag with
          | some a, some b => a != b
          | _, _ => false) then .yes .base
      else
        match t with
        | .nominal name =>
            match resolveAt env name 0 with
            | some r =>
                match searchSortConflicts fuel env s r with
                | .yes inner => .yes (.resolveFormal 0 inner)
                | .no => .no
                | .out => .out
            | none => .no
        | _ =>
            match s with
            | .nominal name =>
                match resolveAt env name 0 with
                | some r =>
                    match searchSortConflicts fuel env r t with
                    | .yes inner => .yes (.resolveSort 0 inner)
                    | .no => .no
                    | .out => .out
                | none => .no
            | _ => .no

def searchMismatch : Nat → Env → Val → Ty → Found MMCert
  | 0, _, _, _ => .out
  | fuel + 1, env, v, t =>
      match t with
      | .ctor _ _ =>
          if (v.baseSort?).isSome then .yes .literalCtor else .no
      | .list element =>
          match v with
          | .cons head tail =>
              match searchMismatch fuel env head element with
              | .yes inner => .yes (.listHere inner)
              | .no =>
                  match searchMismatch fuel env tail (.list element) with
                  | .yes inner => .yes (.listThere inner)
                  | .no => .no
                  | .out => .out
              | .out => .out
          | .nil => .no
          | v => if (v.baseSort?).isSome then .yes .literalList else .no
      | .nominal name =>
          match resolveAt env name 0 with
          | some r =>
              match searchMismatch fuel env v r with
              | .yes inner => .yes (.resolveFormal 0 inner)
              | .no => .no
              | .out => .out
          | none => .no
      | t =>
          match v.baseSort? with
          | some _ =>
              match searchSortConflicts (fuel + 1) env
                  (v.baseSort?.getD .num) t with
              | .yes inner => .yes (.base inner)
              | .no => .no
              | .out => .out
          | none => .no

def searchHasType : Nat → Env → Val → Ty → Found HTCert
  | 0, _, _, _ => .out
  | fuel + 1, env, v, t =>
      match t with
      | .undefined => .yes .wildcard
      | .list element =>
          match v with
          | .nil => .yes .nilList
          | .cons head tail =>
              match searchHasType fuel env head element with
              | .yes headCert =>
                  match searchHasType fuel env tail (.list element) with
                  | .yes tailCert => .yes (.consList headCert tailCert)
                  | .no => .no
                  | .out => .out
              | .no => .no
              | .out => .out
          | _ => .no
      | .nominal name =>
          match resolveAt env name 0 with
          | some r =>
              match searchHasType fuel env v r with
              | .yes inner => .yes (.resolve 0 inner)
              | .no => .no
              | .out => .out
          | none => .no
      | t =>
          if (match v, t with
              | .num, .num | .str, .str
              | .vtrue, .bool | .vfalse, .bool => true
              | _, _ => false) then .yes .literal else .no

/-! ## The four-valued decision -/

inductive Evidence where
  | mismatch (certificate : MMCert)
  | unbound
deriving Repr, DecidableEq

inductive Verdict where
  | established (certificate : HTCert)
  | refuted (evidence : Evidence)
  | undetermined
  | incomplete
deriving Repr, DecidableEq

/-- The decision function.  A returned certificate is CHECKED before it is
trusted; a certificate the checker rejects is an infrastructure fault
surfaced as `incomplete`, never a silent verdict.  Exhaustion is its own
verdict by construction. -/
def decide (fuel : Nat) (env : Env) (value : Option Val) (formal : Ty)
    (mode : Mode) : Verdict :=
  match value with
  | none =>
      if mode.committed && formal.isBase then .refuted .unbound
      else .undetermined
  | some v =>
      match searchMismatch fuel env v formal with
      | .yes cert =>
          if cert.check env v formal then .refuted (.mismatch cert)
          else .incomplete
      | .out => .incomplete
      | .no =>
          match searchHasType fuel env v formal with
          | .yes cert =>
              if cert.check env v formal then .established cert
              else .incomplete
          | .out => .incomplete
          | .no => .undetermined

/-! ## Decision soundness (by construction through the checked
certificates) -/

theorem decide_refuted_mismatch_sound
    {fuel env v formal mode cert}
    (h : decide fuel env (some v) formal mode =
         .refuted (.mismatch cert)) :
    Mismatch env v formal := by
  simp only [decide] at h
  split at h
  · -- searchMismatch = .yes found
    split at h
    · -- certificate checked
      rename_i hcheck
      cases h
      exact MMCert.check_sound env _ v formal hcheck
    · cases h
  · cases h
  · -- searchMismatch = .no
    split at h
    · split at h
      · cases h
      · cases h
    · cases h
    · cases h

theorem decide_established_sound {fuel env v formal mode cert}
    (h : decide fuel env (some v) formal mode = .established cert) :
    HasType env v formal := by
  simp only [decide] at h
  split at h
  · split at h
    · cases h
    · cases h
  · cases h
  · split at h
    · split at h
      · rename_i hc
        cases h
        exact HTCert.check_sound env _ v formal hc
      · cases h
    · cases h
    · cases h

/-- Exhaustion is never spelled `undetermined`: at fuel zero on a bound
value, the verdict is `incomplete` by construction. -/
theorem decide_fuel_zero_incomplete (env : Env) (v : Val) (formal : Ty)
    (mode : Mode) :
    decide 0 env (some v) formal mode = .incomplete := by
  simp [decide, searchMismatch]

/-! ## Ground receipts: the decision agrees with the guard receipts -/

example : decide 64 [] (some .str) .num .plain =
    .refuted (.mismatch (.base .base)) := by decide

example : ∃ cert, decide 64 [] (some .num) .num .plain =
    .established cert := ⟨.literal, by decide⟩

example : decide 64 [] (some .num) (.nominal "SomeNominal") .plain =
    .undetermined := by decide

example : decide 64 [] none .bool .det = .refuted .unbound := by decide

example : decide 64 [] none .bool .plain = .undetermined := by decide

example :
    decide 64 [("Brand", .newtype .num)] (some .str)
      (.nominal "Brand") .plain =
    .refuted (.mismatch (.resolveFormal 0 (.base .base))) := by decide

example : decide 64 []
    (some (.cons .num (.cons .str .nil))) (.list .num) .plain =
    .refuted (.mismatch (.listThere (.listHere (.base .base)))) := by
  decide

/-! ## BANKED DISAGREEMENT CANARY (audited defect, deliberately pinned)

The authored GSLT derives `ValueHasType VNum (TUnion [TNum])` through
`has-type-union`; this module's search layer omits union traversal (and
brands, arrows, applied values, declaration-list conflicts), so `decide`
answers `undetermined` where the presentation proves membership.  The
mirror is therefore NOT the authored semantics — it is a thinner parallel
model, and compiling it further is blocked.

The repair direction is compilation FROM the presentation: a generic
head-indexed search over the authored `RuleSchema` data producing
`RawProof`s that `checkRaw` accepts, replacing this mirror as `decide`'s
substance.  When that lands, the second conjunct below MUST flip to
`established`-agreement and this canary gets rewritten to assert the
AGREEMENT — never deleted. -/

section Canary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT

private def canaryUnionProof : RawProof :=
  .node
    { ruleId := TypeSystemGSLT.ruleId "has-type-union"
      arguments := [vNum, tNum, tCons tNum tNil] }
    [.node { ruleId := TypeSystemGSLT.ruleId "union-member-here"
             arguments := [tNum, tNil] } [],
     .node { ruleId := TypeSystemGSLT.ruleId "has-type-num"
             arguments := [] } []]

theorem union_disagreement_canary :
    (checkRaw TypeSystemGSLT.checked
        (valueHasType vNum (tUnion (tCons tNum tNil)))
        canaryUnionProof = true) ∧
    decide 64 [] (some .num) (.union [.num]) .plain =
      Verdict.undetermined := by
  constructor
  · simp [checkRaw, checkRawChildren, TypeSystemGSLT.checked,
      TypeSystemGSLT.presentation, TypeSystemGSLT.language,
      canaryUnionProof,
      consistentRefl, consistentDynLeft, consistentDynRight,
      consistentUnionRight, consistentUnionLeft, consistentBrand,
      consistentArrow, consistentListNil, consistentListCons,
      unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr,
      hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
      hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
      instantiateRule?, Presentation.lookupRule?, argumentsValidAt,
      argumentValidAt, RuleSchema.sideConditionsHold,
      instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
      instantiateSchemasAt?, lookupArgumentAt?, valueHasType,
      unionMember, vNum, tNum, tNil, tCons, tUnion,
      TypeSystemGSLT.ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]
  · decide

end Canary

end Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDecision
