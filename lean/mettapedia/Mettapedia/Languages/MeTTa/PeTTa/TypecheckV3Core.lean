/-
# Typecheck-v3 core: the four-axis success-typing calculus (Prime-native seed)

The theoretical core of typecheck-v3: the factored, native-type-theory
grounded reconstruction of the INTENT of PeTTa's typecheck-v2, built from
the four axes the semantic census discovered:

1. **shape compatibility** — the flow-consistency relation with the
   Gentzen-polarity union rules (actual union = universal/left rule,
   required union = existential/right rule), nominal newtypes, and
   effect-graded arrows;
2. **result-cardinality grading** — det/semidet/nondet as an ordered
   grade; the census's eleven `mode-fits-*` rules collapse into ONE
   order relation (proved below, with the named rules as instances);
3. **source/evaluated-stage evidence** — grounding licenses structurally
   require compiled-stage evidence; source shape alone cannot strengthen
   a judgment;
4. **open-world `?Unknown`** — gradual permissiveness, the non-transitivity
   witness, and taint-widening as a *choice* between two proven-safe joins
   (v2's publication widening vs v3's precision-retaining union).

The two intent theorems at the bottom are the distilled meaning of
"success typing" that v3 must preserve from v2:

* `checkCall_reject_has_witness` — rejection only with a definite,
  nameable conflict (never from ignorance, never from exhaustion);
* `checkCall_unknown_permissive` — fully-unknown arguments always pass.

The executable checker is equivalent to the inductive judgment, including
the union–union permutation cases.  Arrows carry same-length argument
spines and named effect parameters; aliases resolve into an alias-free core;
and rational trees have a separate bounded replay with witnessed conflicts.
The remaining obligation (see `handoffObligations`) is the per-census-case
correspondence run.
-/
import Mathlib.Order.Basic

namespace Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core

/-! ## §1 Cardinality grades: eleven census rules, one order -/

/-- Result cardinality: how many answers a call may produce. -/
inductive Card where
  | det | semidet | nondet
  deriving DecidableEq, Repr

namespace Card

/-- Grade severity. -/
def toNat : Card → Nat
  | .det => 0
  | .semidet => 1
  | .nondet => 2

/-- The grade order: a weaker (more deterministic) effect fits a stronger
demand. -/
def le (a b : Card) : Bool := a.toNat ≤ b.toNat

/-- Sequencing two computations takes the worst cardinality. -/
def seq (a b : Card) : Card := if a.toNat ≤ b.toNat then b else a

@[simp] theorem le_refl (a : Card) : a.le a = true := by cases a <;> rfl

theorem le_trans {a b c : Card} (h₁ : a.le b = true) (h₂ : b.le c = true) :
    a.le c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [le, toNat]

theorem seq_comm (a b : Card) : a.seq b = b.seq a := by
  cases a <;> cases b <;> rfl

theorem seq_assoc (a b c : Card) : (a.seq b).seq c = a.seq (b.seq c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem seq_det_left (a : Card) : Card.det.seq a = a := by
  cases a <;> rfl

end Card

/-- Arrow modes separate a plain arrow, a concrete cardinality grade, and a
named effect parameter.  The parameter name is retained so a caller can
instantiate it explicitly instead of erasing it to an undifferentiated
wildcard. -/
inductive ArrowMode where
  | plain
  | grade (card : Card)
  | effect (index : Nat)
  deriving DecidableEq, Repr

/-- A partial instantiation of named effect parameters. -/
abbrev EffectSubst := Nat → Option Card

/-- Resolve an effect parameter when its caller supplies a grade. -/
def ArrowMode.instantiate (σ : EffectSubst) : ArrowMode → ArrowMode
  | .effect index =>
      match σ index with
      | none => .effect index
      | some card => .grade card
  | mode => mode

/-- Extract the concrete grade supplied by a direct higher-order parameter
when its required effect slot is the same named slot as the enclosing arrow.
This is the call-site evidence used by effect-polymorphic combinators such as
PeTTa's `map-flat`; unrelated slots and unresolved actual modes contribute no
evidence. -/
def ArrowMode.directEffectCard : ArrowMode → ArrowMode → ArrowMode → Option Card
  | .effect outer, .effect required, .grade actual =>
      if outer = required then some actual else none
  | _, _, _ => none

/-- The conservative concrete grade used only when an execution artifact must
materialize a named or unstated mode.  The typed signature keeps the symbolic
mode; a later call-site instantiation may recover a smaller concrete grade. -/
def ArrowMode.runtimeUpperCard : ArrowMode → Card
  | .grade card => card
  | .plain | .effect _ => .nondet

/-- Does an actual arrow mode fit a required arrow mode?  Plain,
nondeterministic, and unresolved effect requirements accept every
well-formed actual mode, exactly as in the v2 compatibility table.  A
concrete deterministic or semideterministic requirement needs positive
concrete-grade evidence. -/
def modeFits : ArrowMode → ArrowMode → Bool
  | _, .plain => true
  | _, .grade .nondet => true
  | _, .effect _ => true
  | .grade actual, .grade required => actual.le required
  | _, _ => false

/-- **The compression theorem**: fitting a stated demand IS the grade
order.  The census's eleven `mode-fits-*` rules are instances (named
below); v3 replaces the rule list with this one relation. -/
theorem modeFits_iff_le (e d : Card) :
    modeFits (.grade e) (.grade d) = true ↔ e.le d = true := by
  cases e <;> cases d <;> decide

@[simp] theorem modeFits_plain (actual : ArrowMode) :
    modeFits actual .plain = true := rfl

@[simp] theorem modeFits_effect (actual : ArrowMode) (index : Nat) :
    modeFits actual (.effect index) = true := rfl

@[simp] theorem modeFits_refl (mode : ArrowMode) :
    modeFits mode mode = true := by
  cases mode with
  | plain => rfl
  | grade card => cases card <;> rfl
  | effect index => rfl

/-- Materializing a mode at its conservative runtime upper bound never claims
more determinism than the signature permits. -/
theorem runtimeUpperCard_fits (mode : ArrowMode) :
    modeFits (.grade mode.runtimeUpperCard) mode = true := by
  cases mode with
  | plain => rfl
  | grade card => cases card <;> rfl
  | effect index => rfl

/-- A named effect remains polymorphic in the typed signature while its
conservative execution grade is nondeterministic. -/
example : (ArrowMode.effect 0).runtimeUpperCard = .nondet := rfl

/-- The upper bound cannot be reused as evidence for a deterministic demand. -/
example :
    modeFits (.grade (ArrowMode.effect 0).runtimeUpperCard)
      (.grade .det) = false := rfl

@[simp] theorem instantiate_unbound (index : Nat)
    (σ : EffectSubst) (h : σ index = none) :
    (ArrowMode.effect index).instantiate σ = .effect index := by
  simp [ArrowMode.instantiate, h]

@[simp] theorem instantiate_bound (index : Nat) (card : Card)
    (σ : EffectSubst) (h : σ index = some card) :
    (ArrowMode.effect index).instantiate σ = .grade card := by
  simp [ArrowMode.instantiate, h]

@[simp] theorem directEffectCard_same (index : Nat) (card : Card) :
    ArrowMode.directEffectCard (.effect index) (.effect index) (.grade card) =
      some card := by
  simp [ArrowMode.directEffectCard]

theorem directEffectCard_distinct (outer required : Nat) (card : Card)
    (h : outer ≠ required) :
    ArrowMode.directEffectCard (.effect outer) (.effect required) (.grade card) =
      none := by
  simp [ArrowMode.directEffectCard, h]

/-- An unresolved higher-order actual cannot manufacture a concrete grade. -/
example :
    ArrowMode.directEffectCard (.effect 0) (.effect 0) (.effect 0) = none :=
  rfl

/-- Census rule `mode-fits-det-det`. -/
example : modeFits (.grade .det) (.grade .det) = true := by decide
/-- Census rule `mode-fits-det-semidet` (a det callee fits a semidet demand). -/
example : modeFits (.grade .det) (.grade .semidet) = true := by decide
/-- Census rule `mode-fits-semidet-semidet`. -/
example : modeFits (.grade .semidet) (.grade .semidet) = true := by decide
/-- Census rule `mode-fits-nondet`. -/
example : modeFits (.effect 0) (.grade .nondet) = true := by decide
/-- Census rule `mode-fits-plain` (no demand accepts anything). -/
example : modeFits (.grade .nondet) .plain = true := by decide
/-- Census rule `mode-fits-effect`: an unresolved required effect parameter
is polymorphic in the actual mode. -/
example : modeFits .plain (.effect 0) = true := by decide
/-- The rejection side: a nondet callee does not fit a det demand
(census: `committed-lambda-nondeterminism-rejection` family). -/
example : modeFits (.grade .nondet) (.grade .det) = false := by decide

/-- Instantiating a polymorphic requirement can expose a definite conflict:
the unresolved parameter accepts a nondeterministic arrow, while its
deterministic instance rejects it. -/
example (σ : EffectSubst) (h : σ 0 = some .det) :
    modeFits (.grade .nondet) (.effect 0) = true ∧
      modeFits (.grade .nondet)
        ((ArrowMode.effect 0).instantiate σ) = false := by
  simp [h, modeFits, Card.le, Card.toNat]

/-! ## §2 Shape types -/

/-- Primitive shapes. -/
inductive Prim where
  | num | str | bool | sym
  deriving DecidableEq, Repr

/-! The v3 shape language.  `unknown` is the gradual `?Unknown`; `newtype`
is nominal (brand-indexed); arrows carry an argument spine and their effect
grade.  Aliases are deliberately absent: alias transparency is a resolution
pre-pass, not a type former (census: `consistent-alias-left/right`, handled
before this calculus). -/
mutual

inductive Ty where
  | unknown
  | prim (p : Prim)
  | list (elem : Ty)
  | product (fields : TyArgs)
  | arrow (doms : TyArgs) (eff : ArrowMode) (cod : Ty)
  | union (left right : Ty)
  | newtype (brand : Nat) (repr : Ty)
  deriving DecidableEq, Repr

/-- A first-order telescope of arrow argument shapes.  A dedicated spine
matches PeTTa's `TTNil`/`TTCons` encoding and keeps recursive evidence
strictly positive. -/
inductive TyArgs where
  | nil
  | cons (head : Ty) (tail : TyArgs)
  deriving DecidableEq, Repr

end

mutual

/-- Structural rank used for proofs that recurse through type and argument
spines together. -/
def Ty.rank : Ty → Nat
  | .unknown => 1
  | .prim _ => 1
  | .list elem => elem.rank + 1
  | .product fields => fields.rank + 1
  | .arrow doms _ cod => doms.rank + cod.rank + 1
  | .union left right => left.rank + right.rank + 1
  | .newtype _ repr => repr.rank + 1

def TyArgs.rank : TyArgs → Nat
  | .nil => 1
  | .cons head tail => head.rank + tail.rank + 1

end

/-! ## §3 Provider-wire elaboration

The five inherited provider relations speak the already generated v2 wire
vocabulary.  They do not return v3-private constructors.  An explicit
elaboration therefore separates the shared program-state contract from the
native calculus.  In particular, a provider name has one meaning no matter
which checker consumes it.

`ProviderEnv` is an admitted snapshot: each nominal has one source-ordered
meaning when present.  The admission pass retains the first abstract-type,
alias, or newtype declaration for that name; later alternatives do not alter
it.  Cycles and dangling names become `none` through the fuel-bounded
executable elaborator, never a type inconsistency.
-/

mutual

/-- Type terms carried by the inherited PeTTa provider contract. -/
inductive ProviderTy where
  | unknown
  | prim (p : Prim)
  | list (elem : ProviderTy)
  | product (fields : ProviderTyArgs)
  | arrow (doms : ProviderTyArgs) (eff : ArrowMode) (cod : ProviderTy)
  | union (members : ProviderTyArgs)
  | nominal (name : Nat)
  | brand (name : Nat) (repr : ProviderTy)
  deriving DecidableEq, Repr

/-- The provider wire uses first-order spines for arrows and unions. -/
inductive ProviderTyArgs where
  | nil
  | cons (head : ProviderTy) (tail : ProviderTyArgs)
  deriving DecidableEq, Repr

end


/-- Declaration forms supplied by `EnvDeclared/2`.  An abstract declaration
is the meaning of PeTTa's `(: Name Type)`: it introduces a nominal identity
while keeping its representation unknown. -/
inductive ProviderDecl where
  | abstract
  | alias (repr : ProviderTy)
  | newtype (repr : ProviderTy)
  deriving DecidableEq, Repr

/-- One revision-pinned, ambiguity-free declaration snapshot. -/
structure ProviderEnv where
  lookup : Nat → Option ProviderDecl

mutual

/-- Elaborate one provider-wire type into the alias-free v3 core.  Fuel makes
cyclic nominal declarations an explicit admission failure. -/
def elaborateProviderType (env : ProviderEnv) : Nat → ProviderTy → Option Ty
  | 0, _ => none
  | _ + 1, .unknown => some .unknown
  | _ + 1, .prim prim => some (.prim prim)
  | fuel + 1, .list elem =>
      return .list (← elaborateProviderType env fuel elem)
  | fuel + 1, .product fields =>
      return .product (← elaborateProviderArgs env fuel fields)
  | fuel + 1, .arrow doms eff cod =>
      return .arrow (← elaborateProviderArgs env fuel doms) eff
        (← elaborateProviderType env fuel cod)
  | fuel + 1, .union members => elaborateProviderUnion env fuel members
  | fuel + 1, .nominal name =>
      match env.lookup name with
      | none => none
      | some .abstract => some (.newtype name .unknown)
      | some (.alias repr) => elaborateProviderType env fuel repr
      | some (.newtype repr) =>
          return .newtype name (← elaborateProviderType env fuel repr)
  | fuel + 1, .brand name repr =>
      return .newtype name (← elaborateProviderType env fuel repr)

/-- Elaborate an arrow-domain spine componentwise. -/
def elaborateProviderArgs (env : ProviderEnv) :
    Nat → ProviderTyArgs → Option TyArgs
  | 0, _ => none
  | _ + 1, .nil => some .nil
  | fuel + 1, .cons head tail =>
      return .cons (← elaborateProviderType env fuel head)
        (← elaborateProviderArgs env fuel tail)

/-- Elaborate a nonempty provider union into the binary native union.  Empty
provider unions carry no positive type evidence. -/
def elaborateProviderUnion (env : ProviderEnv) :
    Nat → ProviderTyArgs → Option Ty
  | 0, _ => none
  | _ + 1, .nil => none
  | fuel + 1, .cons head .nil =>
      elaborateProviderType env fuel head
  | fuel + 1, .cons head tail@(.cons _ _) =>
      return .union (← elaborateProviderType env fuel head)
        (← elaborateProviderUnion env fuel tail)

end


/-- A concrete provider alias elaborates transparently. -/
def providerAliasNum : ProviderEnv where
  lookup
    | 0 => some (.alias (.prim .num))
    | _ => none

example : elaborateProviderType providerAliasNum 3 (.nominal 0) =
    some (.prim .num) := by decide

/-- A provider newtype retains its nominal identity. -/
def providerNewtypeNum : ProviderEnv where
  lookup
    | 7 => some (.newtype (.prim .num))
    | _ => none

example : elaborateProviderType providerNewtypeNum 3 (.nominal 7) =
    some (.newtype 7 (.prim .num)) := by decide

/-- An abstract declared type has nominal identity and an intentionally hidden
representation.  Distinct abstract declarations therefore stay distinct. -/
def providerAbstract : ProviderEnv where
  lookup
    | 3 | 4 => some .abstract
    | _ => none

example : elaborateProviderType providerAbstract 2 (.nominal 3) =
    some (.newtype 3 .unknown) := by decide

example :
    elaborateProviderType providerAbstract 2 (.nominal 3) =
        some (.newtype 3 .unknown) ∧
      elaborateProviderType providerAbstract 2 (.nominal 4) =
        some (.newtype 4 .unknown) ∧
      (some (.newtype 3 .unknown) : Option Ty) ≠
        some (.newtype 4 .unknown) := by
  decide

/-! ### Source-order admission -/

/-- Select the first declaration for a nominal name.  This is the small
executable law shared by the v2 census and the v3 provider adapter. -/
def firstProviderDecl : List (Nat × ProviderDecl) → Nat → Option ProviderDecl
  | [], _ => none
  | (declared, declaration) :: rest, name =>
      if declared = name then some declaration else firstProviderDecl rest name

@[simp] theorem firstProviderDecl_head
    (name : Nat) (declaration : ProviderDecl)
    (rest : List (Nat × ProviderDecl)) :
    firstProviderDecl ((name, declaration) :: rest) name = some declaration := by
  simp [firstProviderDecl]

/-- A later incompatible declaration cannot change the first meaning. -/
example :
    firstProviderDecl
      [(8, .alias (.prim .num)), (8, .newtype (.prim .str))] 8 =
        some (.alias (.prim .num)) := by
  decide

/-- Missing provider declarations are ignorance, not a core-type conflict. -/
example : elaborateProviderType providerAliasNum 3 (.nominal 12) = none := by
  decide

/-- Provider products retain heterogeneous field order and arity. -/
example : elaborateProviderType providerAliasNum 4
    (.product (.cons (.prim .sym) (.cons (.prim .num) .nil))) =
      some (.product (.cons (.prim .sym) (.cons (.prim .num) .nil))) := by
  decide

/-- A self-alias cannot enter the core: every finite admission budget ends in
an explicit failure. -/
def providerSelfAlias : ProviderEnv where
  lookup
    | 0 => some (.alias (.nominal 0))
    | _ => none

theorem provider_self_alias_rejected (fuel : Nat) :
    elaborateProviderType providerSelfAlias fuel (.nominal 0) = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [elaborateProviderType, providerSelfAlias] using ih

/-! ## §3 Alias admission: a total pre-pass into the core language -/

/- Input types may mention aliases.  Core `Ty` cannot: an admitted alias
environment maps every known alias directly to an alias-free core type, so
cycles and dangling references remain admission outcomes instead of entering
the consistency calculus. -/
mutual

inductive InputTy where
  | unknown
  | prim (p : Prim)
  | list (elem : InputTy)
  | product (fields : InputTyArgs)
  | arrow (doms : InputTyArgs) (eff : ArrowMode) (cod : InputTy)
  | union (left right : InputTy)
  | newtype (brand : Nat) (repr : InputTy)
  | alias (name : Nat)
  deriving DecidableEq, Repr

inductive InputTyArgs where
  | nil
  | cons (head : InputTy) (tail : InputTyArgs)
  deriving DecidableEq, Repr

end

/-- Alias declarations after admission.  The codomain is alias-free by type. -/
structure AliasEnv where
  lookup : Nat → Option Ty

mutual

/-- Resolve every alias occurrence before invoking the core judgment.  A
missing alias produces `none`; it is not converted into a type conflict. -/
def resolveAliases (env : AliasEnv) : InputTy → Option Ty
  | .unknown => some .unknown
  | .prim p => some (.prim p)
  | .list elem => return .list (← resolveAliases env elem)
  | .product fields => return .product (← resolveAliasArgs env fields)
  | .arrow doms eff cod =>
      return .arrow (← resolveAliasArgs env doms) eff
        (← resolveAliases env cod)
  | .union left right =>
      return .union (← resolveAliases env left) (← resolveAliases env right)
  | .newtype brand repr =>
      return .newtype brand (← resolveAliases env repr)
  | .alias name => env.lookup name
termination_by input => sizeOf input
decreasing_by all_goals (simp_wf <;> try omega)

/-- Resolve aliases componentwise through an input argument spine. -/
def resolveAliasArgs (env : AliasEnv) : InputTyArgs → Option TyArgs
  | .nil => some .nil
  | .cons head tail =>
      return .cons (← resolveAliases env head) (← resolveAliasArgs env tail)
termination_by inputs => sizeOf inputs
decreasing_by all_goals (simp_wf; omega)

end


mutual

/-- Embed an alias-free core type into the input language. -/
def Ty.toInput : Ty → InputTy
  | .unknown => .unknown
  | .prim p => .prim p
  | .list elem => .list elem.toInput
  | .product fields => .product fields.toInput
  | .arrow doms eff cod => .arrow doms.toInput eff cod.toInput
  | .union left right => .union left.toInput right.toInput
  | .newtype brand repr => .newtype brand repr.toInput
termination_by ty => sizeOf ty
decreasing_by all_goals (simp_wf <;> try omega)

/-- Embed an alias-free core argument spine into the input language. -/
def TyArgs.toInput : TyArgs → InputTyArgs
  | .nil => .nil
  | .cons head tail => .cons head.toInput tail.toInput
termination_by tys => sizeOf tys
decreasing_by all_goals (simp_wf; omega)

end

mutual

/-- Alias resolution is the identity on embedded core types. -/
@[simp] theorem resolveAliases_ofCore (env : AliasEnv) :
    ∀ ty : Ty, resolveAliases env ty.toInput = some ty
  | .unknown => by simp [Ty.toInput, resolveAliases]
  | .prim p => by simp [Ty.toInput, resolveAliases]
  | .list elem => by
      simp [Ty.toInput, resolveAliases, resolveAliases_ofCore env elem]
  | .product fields => by
      simp [Ty.toInput, resolveAliases, resolveAliasArgs_ofCore env fields]
  | .arrow doms eff cod => by
      simp [Ty.toInput, resolveAliases, resolveAliasArgs_ofCore env doms,
        resolveAliases_ofCore env cod]
  | .union left right => by
      simp [Ty.toInput, resolveAliases, resolveAliases_ofCore env left,
        resolveAliases_ofCore env right]
  | .newtype brand repr => by
      simp [Ty.toInput, resolveAliases, resolveAliases_ofCore env repr]
termination_by ty => sizeOf ty
decreasing_by all_goals (simp_wf <;> try omega)

/-- Alias resolution is the identity on embedded core argument spines. -/
@[simp] theorem resolveAliasArgs_ofCore (env : AliasEnv) :
    ∀ tys : TyArgs, resolveAliasArgs env tys.toInput = some tys
  | .nil => by simp [TyArgs.toInput, resolveAliasArgs]
  | .cons head tail => by
      simp [TyArgs.toInput, resolveAliasArgs, resolveAliases_ofCore env head,
        resolveAliasArgs_ofCore env tail]
termination_by tys => sizeOf tys
decreasing_by all_goals (simp_wf; omega)

end

/-! ## §4 Flow consistency: the directional gradual relation

`Consistent a b` reads: a value of shape `a` may flow into a requirement
of shape `b`.  The union rules carry the Gentzen polarity the census
recovered: an ACTUAL union flows only if every member flows (any member
may occur at runtime); a REQUIRED union is satisfied by one alternative. -/

mutual

inductive Consistent : Ty → Ty → Prop where
  | refl (t) : Consistent t t
  | unknownL (t) : Consistent .unknown t
  | unknownR (t) : Consistent t .unknown
  | listCong {a b} : Consistent a b → Consistent (.list a) (.list b)
  | productCong {fields fields'} : ConsistentArgs fields fields' →
      Consistent (.product fields) (.product fields')
  | arrowCong {ds ds' c c' e e'} : ConsistentArgs ds ds' →
      Consistent c c' → modeFits e e' = true →
      Consistent (.arrow ds e c) (.arrow ds' e' c')
  | unionL {a b c} : Consistent a c → Consistent b c →
      Consistent (.union a b) c
  | unionR1 {a b c} : Consistent a b → Consistent a (.union b c)
  | unionR2 {a b c} : Consistent a c → Consistent a (.union b c)
  | newtypeCong {n r r'} : Consistent r r' →
      Consistent (.newtype n r) (.newtype n r')

/-- Same-length componentwise flow for arrow argument spines. -/
inductive ConsistentArgs : TyArgs → TyArgs → Prop where
  | nil : ConsistentArgs .nil .nil
  | cons {a b as bs} : Consistent a b → ConsistentArgs as bs →
      ConsistentArgs (.cons a as) (.cons b bs)

end

/-- Gradual permissiveness, both directions: `?Unknown` is consistent with
everything (census: `dynamic-actual-compatibility`,
`dynamic-required-compatibility`). -/
theorem consistent_unknown (t : Ty) :
    Consistent t .unknown ∧ Consistent .unknown t :=
  ⟨.unknownR t, .unknownL t⟩

/-! ### The executable checker (NIK mode 1: direct decision, no certificate) -/

mutual

/-- Decide flow consistency.  Pattern order is semantic: unknown first,
then the actual-union (left) rule, then the required-union (right) rule. -/
def consistent? : Ty → Ty → Bool
  | .unknown, _ => true
  | _, .unknown => true
  | .union a b, c => consistent? a c && consistent? b c
  | a, .union b c => consistent? a b || consistent? a c
  | .prim p, .prim q => p = q
  | .list a, .list b => consistent? a b
  | .product fields, .product fields' => consistentList? fields fields'
  | .arrow ds e c, .arrow ds' e' c' =>
      consistentList? ds ds' && modeFits e e' && consistent? c c'
  | .newtype n r, .newtype n' r' => n = n' && consistent? r r'
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals (simp_wf; omega)

/-- Same-length, componentwise executable flow for an arrow's arguments. -/
def consistentList? : TyArgs → TyArgs → Bool
  | .nil, .nil => true
  | .cons a as, .cons b bs => consistent? a b && consistentList? as bs
  | _, _ => false
termination_by as bs => sizeOf as + sizeOf bs
decreasing_by all_goals (simp_wf; omega)

end

/-! ## §4a Explicit narrowing overlap

`mayOverlap? actual ascribed` is the static precondition for an explicit
`(the T expression)` runtime check.  Unlike ordinary flow consistency, unions
are existential on both sides.  A single nominal boundary may expose its
representation to the check, while two nominal values overlap only when their
brands agree. -/

/-- Decide whether two types have a possible common runtime inhabitant. -/
def mayOverlap? : Ty → Ty → Bool
  | .unknown, _ => true
  | _, .unknown => true
  | .union left right, .union left' right' =>
      mayOverlap? left left' || mayOverlap? left right' ||
        mayOverlap? right left' || mayOverlap? right right'
  | .union left right, other =>
      mayOverlap? left other || mayOverlap? right other
  | other, .union left right =>
      mayOverlap? other left || mayOverlap? other right
  | .newtype brand repr, .newtype brand' repr' =>
      brand = brand' && mayOverlap? repr repr'
  | .newtype _ repr, other => mayOverlap? repr other
  | other, .newtype _ repr => mayOverlap? other repr
  | actual, ascribed =>
      consistent? actual ascribed || consistent? ascribed actual
termination_by actual ascribed => sizeOf actual + sizeOf ascribed
decreasing_by all_goals (simp_wf; omega)

/-- Explicit narrowing overlap is symmetric. -/
theorem mayOverlap?_comm (actual ascribed : Ty) :
    mayOverlap? actual ascribed = mayOverlap? ascribed actual := by
  fun_induction mayOverlap? actual ascribed
  case case1 other =>
    cases other <;> simp only [mayOverlap?]
  case case2 other hUnknown =>
    cases other <;> simp_all [mayOverlap?]
  case case3 left right left' right' ihLL ihLR ihRL ihRR =>
    conv => rhs; rw [mayOverlap?]
    rw [ihLL, ihLR, ihRL, ihRR]
    ac_rfl
  case case4 left right other hUnknown hUnion ihLeft ihRight =>
    cases other <;> simp_all [mayOverlap?]
  case case5 other left right hUnknown hUnion ihLeft ihRight =>
    cases other <;> simp_all [mayOverlap?]
  case case6 brand repr brand' repr' ih =>
    conv => rhs; rw [mayOverlap?]
    rw [ih]
    simp only [eq_comm]
  case case7 brand repr other hUnknown hUnion hNewtype ih =>
    cases other <;> simp_all [mayOverlap?]
  case case8 other brand repr hUnknown hUnion hNewtype ih =>
    cases other <;> simp_all [mayOverlap?]
  case case9 actual ascribed hActualUnknown hAscribedUnknown hBothUnions
      hActualUnion hAscribedUnion hBothNewtypes hActualNewtype hAscribedNewtype =>
    cases actual <;> cases ascribed <;>
      simp_all [mayOverlap?, Bool.or_comm]

/-- Either member of an actual union can witness explicit narrowing. -/
example :
    mayOverlap? (.union (.prim .num) (.prim .str)) (.prim .str) = true := by
  simp [mayOverlap?, consistent?]

/-- Either member of an ascribed union can witness explicit narrowing. -/
example :
    mayOverlap? (.prim .num) (.union (.prim .str) (.prim .num)) = true := by
  simp [mayOverlap?, consistent?]

/-- One nominal boundary can expose a compatible representation. -/
example : mayOverlap? (.prim .num) (.newtype 5 (.prim .num)) = true := by
  simp [mayOverlap?, consistent?]

/-- Distinct nominal brands do not overlap merely because their hidden
representations coincide. -/
example :
    mayOverlap? (.newtype 5 (.prim .num)) (.newtype 6 (.prim .num)) = false := by
  simp [mayOverlap?]

/-- Disjoint primitive types provide a definite ascription conflict. -/
example : mayOverlap? (.prim .num) (.prim .str) = false := by
  simp [mayOverlap?, consistent?]

@[simp] theorem consistent?_unknownL (t : Ty) :
    consistent? .unknown t = true := by
  cases t <;> simp [consistent?]

@[simp] theorem consistent?_unknownR (t : Ty) :
    consistent? t .unknown = true := by
  cases t <;> simp [consistent?]

/-- Embedding a requirement into the left branch of a required union
preserves executable consistency.  Structural induction on the actual type
is essential here: when the actual type is itself a union, `consistent?`
commits to its universal rule before inspecting the required union. -/
theorem consistent?_unionR1 {a b c : Ty}
    (h : consistent? a b = true) :
    consistent? a (.union b c) = true := by
  cases a with
  | unknown => simp
  | prim p => cases b <;> simp_all [consistent?]
  | list elem => cases b <;> simp_all [consistent?]
  | product fields => cases b <;> simp_all [consistent?]
  | arrow doms eff cod => cases b <;> simp_all [consistent?]
  | union left right =>
      cases b <;> simp_all [consistent?]
      all_goals constructor <;> apply consistent?_unionR1 <;> try simp_all
  | newtype brand repr => cases b <;> simp_all [consistent?]
termination_by a.rank
decreasing_by all_goals (simp_all [Ty.rank]; omega)

/-- The right-branch counterpart of `consistent?_unionR1`. -/
theorem consistent?_unionR2 {a b c : Ty}
    (h : consistent? a c = true) :
    consistent? a (.union b c) = true := by
  cases a with
  | unknown => simp
  | prim p => cases c <;> simp_all [consistent?]
  | list elem => cases c <;> simp_all [consistent?]
  | product fields => cases c <;> simp_all [consistent?]
  | arrow doms eff cod => cases c <;> simp_all [consistent?]
  | union left right =>
      cases c <;> simp_all [consistent?]
      all_goals constructor <;> apply consistent?_unionR2 <;> try simp_all
  | newtype brand repr => cases c <;> simp_all [consistent?]
termination_by a.rank
decreasing_by all_goals (simp_all [Ty.rank]; omega)

mutual

/-- Executable consistency is reflexive for every finite v3 type. -/
@[simp] theorem consistent?_refl (t : Ty) : consistent? t t = true := by
  cases t with
  | unknown => simp
  | prim p => simp [consistent?]
  | list elem => simp [consistent?, consistent?_refl elem]
  | product fields =>
      simp [consistent?, consistentList?_refl fields]
  | arrow doms eff cod =>
      simp [consistent?, consistentList?_refl doms,
        consistent?_refl cod, modeFits_refl]
  | union left right =>
      simp [consistent?, consistent?_unionR1 (consistent?_refl left),
        consistent?_unionR2 (consistent?_refl right)]
  | newtype brand repr => simp [consistent?, consistent?_refl repr]
termination_by t.rank
decreasing_by all_goals (simp_all [Ty.rank] <;> try omega)

/-- Componentwise executable consistency is reflexive for every argument
spine. -/
@[simp] theorem consistentList?_refl (ts : TyArgs) :
    consistentList? ts ts = true := by
  cases ts with
  | nil => simp [consistentList?]
  | cons head tail =>
      simp [consistentList?, consistent?_refl head,
        consistentList?_refl tail]
termination_by ts.rank
decreasing_by all_goals (simp_all [TyArgs.rank]; omega)

end

mutual

/-- Soundness: everything the executable checker accepts is derivable. -/
theorem consistent?_sound :
    ∀ a b, consistent? a b = true → Consistent a b
  | .unknown, b, _ => .unknownL b
  | .prim p, .unknown, _ => .unknownR _
  | .prim p, .prim q, h => by
      have hpq : p = q := by simpa [consistent?] using h
      subst q
      exact .refl _
  | .prim p, .list elem, h => by simp [consistent?] at h
  | .prim p, .product fields, h => by simp [consistent?] at h
  | .prim p, .arrow doms eff cod, h => by simp [consistent?] at h
  | .prim p, .union left right, h => by
      have branches : consistent? (.prim p) left = true ∨
          consistent? (.prim p) right = true := by
        simpa [consistent?] using h
      cases branches with
      | inl hleft => exact .unionR1 (consistent?_sound _ _ hleft)
      | inr hright => exact .unionR2 (consistent?_sound _ _ hright)
  | .prim p, .newtype brand repr, h => by simp [consistent?] at h
  | .list elem, .unknown, _ => .unknownR _
  | .list elem, .prim q, h => by simp [consistent?] at h
  | .list elem, .list elem', h =>
      .listCong (consistent?_sound _ _ (by simpa [consistent?] using h))
  | .list elem, .product fields, h => by simp [consistent?] at h
  | .list elem, .arrow doms eff cod, h => by simp [consistent?] at h
  | .list elem, .union left right, h => by
      have branches : consistent? (.list elem) left = true ∨
          consistent? (.list elem) right = true := by
        simpa [consistent?] using h
      cases branches with
      | inl hleft => exact .unionR1 (consistent?_sound _ _ hleft)
      | inr hright => exact .unionR2 (consistent?_sound _ _ hright)
  | .list elem, .newtype brand repr, h => by simp [consistent?] at h
  | .product fields, .unknown, _ => .unknownR _
  | .product fields, .prim q, h => by simp [consistent?] at h
  | .product fields, .list elem, h => by simp [consistent?] at h
  | .product fields, .product fields', h =>
      .productCong
        (consistentList?_sound _ _ (by simpa [consistent?] using h))
  | .product fields, .arrow doms eff cod, h => by simp [consistent?] at h
  | .product fields, .union left right, h => by
      have branches : consistent? (.product fields) left = true ∨
          consistent? (.product fields) right = true := by
        simpa [consistent?] using h
      cases branches with
      | inl hleft => exact .unionR1 (consistent?_sound _ _ hleft)
      | inr hright => exact .unionR2 (consistent?_sound _ _ hright)
  | .product fields, .newtype brand repr, h => by simp [consistent?] at h
  | .arrow doms eff cod, .unknown, _ => .unknownR _
  | .arrow doms eff cod, .prim q, h => by simp [consistent?] at h
  | .arrow doms eff cod, .list elem, h => by simp [consistent?] at h
  | .arrow doms eff cod, .product fields, h => by simp [consistent?] at h
  | .arrow doms eff cod, .arrow doms' eff' cod', h => by
      have parts :
          (consistentList? doms doms' = true ∧ modeFits eff eff' = true) ∧
            consistent? cod cod' = true := by
        simpa [consistent?] using h
      exact .arrowCong
        (consistentList?_sound _ _ parts.1.1)
        (consistent?_sound _ _ parts.2) parts.1.2
  | .arrow doms eff cod, .union left right, h => by
      have branches : consistent? (.arrow doms eff cod) left = true ∨
          consistent? (.arrow doms eff cod) right = true := by
        simpa [consistent?] using h
      cases branches with
      | inl hleft => exact .unionR1 (consistent?_sound _ _ hleft)
      | inr hright => exact .unionR2 (consistent?_sound _ _ hright)
  | .arrow doms eff cod, .newtype brand repr, h => by
      simp [consistent?] at h
  | .union left right, .unknown, _ => .unknownR _
  | .union left right, .prim q, h => by
      have parts : consistent? left (.prim q) = true ∧
          consistent? right (.prim q) = true := by
        simpa [consistent?] using h
      exact .unionL (consistent?_sound _ _ parts.1)
        (consistent?_sound _ _ parts.2)
  | .union left right, .list elem, h => by
      have parts : consistent? left (.list elem) = true ∧
          consistent? right (.list elem) = true := by
        simpa [consistent?] using h
      exact .unionL (consistent?_sound _ _ parts.1)
        (consistent?_sound _ _ parts.2)
  | .union left right, .product fields, h => by
      have parts : consistent? left (.product fields) = true ∧
          consistent? right (.product fields) = true := by
        simpa [consistent?] using h
      exact .unionL (consistent?_sound _ _ parts.1)
        (consistent?_sound _ _ parts.2)
  | .union left right, .arrow doms eff cod, h => by
      have parts : consistent? left (.arrow doms eff cod) = true ∧
          consistent? right (.arrow doms eff cod) = true := by
        simpa [consistent?] using h
      exact .unionL (consistent?_sound _ _ parts.1)
        (consistent?_sound _ _ parts.2)
  | .union left right, .union left' right', h => by
      have parts : consistent? left (.union left' right') = true ∧
          consistent? right (.union left' right') = true := by
        simpa [consistent?] using h
      exact .unionL (consistent?_sound _ _ parts.1)
        (consistent?_sound _ _ parts.2)
  | .union left right, .newtype brand repr, h => by
      have parts : consistent? left (.newtype brand repr) = true ∧
          consistent? right (.newtype brand repr) = true := by
        simpa [consistent?] using h
      exact .unionL (consistent?_sound _ _ parts.1)
        (consistent?_sound _ _ parts.2)
  | .newtype brand repr, .unknown, _ => .unknownR _
  | .newtype brand repr, .prim q, h => by simp [consistent?] at h
  | .newtype brand repr, .list elem, h => by simp [consistent?] at h
  | .newtype brand repr, .product fields, h => by simp [consistent?] at h
  | .newtype brand repr, .arrow doms eff cod, h => by
      simp [consistent?] at h
  | .newtype brand repr, .union left right, h => by
      have branches : consistent? (.newtype brand repr) left = true ∨
          consistent? (.newtype brand repr) right = true := by
        simpa [consistent?] using h
      cases branches with
      | inl hleft => exact .unionR1 (consistent?_sound _ _ hleft)
      | inr hright => exact .unionR2 (consistent?_sound _ _ hright)
  | .newtype brand repr, .newtype brand' repr', h => by
      have parts : brand = brand' ∧ consistent? repr repr' = true := by
        simpa [consistent?] using h
      cases parts.1
      exact .newtypeCong (consistent?_sound _ _ parts.2)
termination_by a b => a.rank + b.rank
decreasing_by all_goals simp [Ty.rank]; omega

/-- Soundness of the argument-spine checker. -/
theorem consistentList?_sound :
    ∀ as bs, consistentList? as bs = true → ConsistentArgs as bs
  | .nil, .nil, _ => .nil
  | .nil, .cons head tail, h => by simp [consistentList?] at h
  | .cons head tail, .nil, h => by simp [consistentList?] at h
  | .cons head tail, .cons head' tail', h => by
      have parts : consistent? head head' = true ∧
          consistentList? tail tail' = true := by
        simpa [consistentList?] using h
      exact .cons (consistent?_sound _ _ parts.1)
        (consistentList?_sound _ _ parts.2)
termination_by as bs => as.rank + bs.rank
decreasing_by all_goals simp [TyArgs.rank]; omega

end

/-- The executable left-union rule composes two accepted branches. -/
theorem consistent?_unionL {a b c : Ty}
    (ha : consistent? a c = true) (hb : consistent? b c = true) :
    consistent? (.union a b) c = true := by
  cases c <;> simp_all [consistent?]

mutual

/-- Completeness: every derivable consistency judgment is accepted by the
executable checker.  The two required-union lemmas above are the permutation
argument: they commute an inductive `unionR` step through the checker's
left-first treatment of an actual union. -/
theorem consistent?_complete (a b : Ty) (h : Consistent a b) :
    consistent? a b = true :=
  match h with
  | .refl t => consistent?_refl t
  | .unknownL t => consistent?_unknownL t
  | .unknownR t => consistent?_unknownR t
  | .listCong inner => by
      simpa [consistent?] using consistent?_complete _ _ inner
  | .productCong fields => by
      simpa [consistent?] using consistentList?_complete _ _ fields
  | .arrowCong arguments result he => by
      simp [consistent?, consistentList?_complete _ _ arguments,
        consistent?_complete _ _ result, he]
  | .unionL left right =>
      consistent?_unionL (consistent?_complete _ _ left)
        (consistent?_complete _ _ right)
  | .unionR1 inner =>
      consistent?_unionR1 (consistent?_complete _ _ inner)
  | .unionR2 inner =>
      consistent?_unionR2 (consistent?_complete _ _ inner)
  | .newtypeCong inner => by
      simpa [consistent?] using consistent?_complete _ _ inner

/-- Completeness of the executable argument-spine checker. -/
theorem consistentList?_complete (as bs : TyArgs)
    (h : ConsistentArgs as bs) : consistentList? as bs = true :=
  match h with
  | .nil => by simp
  | .cons head tail => by
      simp [consistentList?, consistent?_complete _ _ head,
        consistentList?_complete _ _ tail]

end

/-- The executable checker decides exactly the inductive consistency
calculus. -/
theorem consistent?_eq_true_iff (a b : Ty) :
    consistent? a b = true ↔ Consistent a b :=
  ⟨consistent?_sound a b, consistent?_complete a b⟩

/-! ### Alias-prepass composition -/

/-- Resolve both input types, then invoke the alias-free core checker.
`none` is an admission outcome (a missing alias), never a rejection. -/
def consistentAfterAliases (env : AliasEnv) (actual required : InputTy) :
    Option Bool := do
  let actual' ← resolveAliases env actual
  let required' ← resolveAliases env required
  return consistent? actual' required'

/-- **Alias invariance**: successful pre-resolution does not alter or
approximate the core judgment; it transports the exact checker result. -/
theorem consistentAfterAliases_invariant (env : AliasEnv)
    {actual required : InputTy} {actual' required' : Ty}
    (ha : resolveAliases env actual = some actual')
    (hr : resolveAliases env required = some required') :
    consistentAfterAliases env actual required =
      some (consistent? actual' required') := by
  simp [consistentAfterAliases, ha, hr]

/-- Embedded core inputs pass through alias admission unchanged. -/
@[simp] theorem consistentAfterAliases_ofCore (env : AliasEnv)
    (actual required : Ty) :
    consistentAfterAliases env actual.toInput required.toInput =
      some (consistent? actual required) := by
  simp [consistentAfterAliases]

/-- Soundness of the composed alias pre-pass and core decision procedure. -/
theorem consistentAfterAliases_sound (env : AliasEnv)
    {actual required : InputTy}
    (h : consistentAfterAliases env actual required = some true) :
    ∃ actual' required',
      resolveAliases env actual = some actual' ∧
      resolveAliases env required = some required' ∧
      Consistent actual' required' := by
  unfold consistentAfterAliases at h
  cases ha : resolveAliases env actual with
  | none => simp [ha] at h
  | some actual' =>
      cases hr : resolveAliases env required with
      | none => simp [ha, hr] at h
      | some required' =>
          refine ⟨actual', required', rfl, rfl, consistent?_sound _ _ ?_⟩
          simpa [ha, hr] using h

/-- Positive alias witness: an admitted alias is transparent. -/
example :
    let env : AliasEnv :=
      { lookup := fun name => if name = 0 then some (.prim .num) else none }
    consistentAfterAliases env (.alias 0) (.prim .num) = some true := by
  simp [consistentAfterAliases, resolveAliases]

/-- Negative alias witness: resolving an alias can expose a real conflict. -/
example :
    let env : AliasEnv :=
      { lookup := fun name => if name = 0 then some (.prim .num) else none }
    consistentAfterAliases env (.alias 0) (.prim .str) = some false := by
  simp [consistentAfterAliases, resolveAliases, consistent?]

/-- A dangling alias stays unresolved rather than becoming a rejection. -/
example :
    let env : AliasEnv :=
      { lookup := fun name => if name = 0 then some (.prim .num) else none }
    consistentAfterAliases env (.alias 1) (.prim .str) = none := by
  simp [consistentAfterAliases, resolveAliases]

/-! ### Bounded rational-tree replay -/

/-- One node of a finite rational-tree presentation.  Child indices may
point backward, so a finite list can represent an infinite regular tree. -/
structure RationalNode where
  head : Nat
  children : List Nat
  deriving DecidableEq, Repr

abbrev RationalGraph := List RationalNode

/-- A structural conflict retains both node identities and both observed
outer shapes. -/
structure RationalConflict where
  left : Nat
  right : Nat
  leftNode : RationalNode
  rightNode : RationalNode
  deriving DecidableEq, Repr

/-- Bounded replay has a distinct exhaustion result.  It cannot refute from
running out of fuel or from a missing graph node. -/
inductive RationalResult where
  | compatible
  | conflict (witness : RationalConflict)
  | incomplete
  deriving DecidableEq, Repr

def RationalConflict.Valid (leftGraph rightGraph : RationalGraph)
    (witness : RationalConflict) : Prop :=
  leftGraph[witness.left]? = some witness.leftNode ∧
  rightGraph[witness.right]? = some witness.rightNode ∧
    (witness.leftNode.head ≠ witness.rightNode.head ∨
      witness.leftNode.children.length ≠ witness.rightNode.children.length)

def mkRationalConflict (left right : Nat)
    (leftNode rightNode : RationalNode) : RationalConflict :=
  { left, right, leftNode, rightNode }

/-- Compare two reified rational trees by bounded bisimulation replay.
Revisiting a node pair closes a coinductive cycle.  Fuel exhaustion and
missing nodes are `incomplete`; only a witnessed head/arity mismatch is a
conflict. -/
def rationalReplayAux (leftGraph rightGraph : RationalGraph) :
    Nat → List (Nat × Nat) → List (Nat × Nat) → RationalResult
  | _, _, [] => .compatible
  | 0, _, _ :: _ => .incomplete
  | fuel + 1, seen, (left, right) :: rest =>
      if (left, right) ∈ seen then
        rationalReplayAux leftGraph rightGraph fuel seen rest
      else
        match leftGraph[left]?, rightGraph[right]? with
        | some leftNode, some rightNode =>
            if leftNode.head = rightNode.head then
              if leftNode.children.length = rightNode.children.length then
                rationalReplayAux leftGraph rightGraph fuel
                  ((left, right) :: seen)
                  (leftNode.children.zip rightNode.children ++ rest)
              else
                .conflict
                  (mkRationalConflict left right leftNode rightNode)
            else
              .conflict (mkRationalConflict left right leftNode rightNode)
        | _, _ => .incomplete

/-- Start replay from a pair of root nodes. -/
def rationalReplay (fuel : Nat) (leftGraph : RationalGraph) (left : Nat)
    (rightGraph : RationalGraph) (right : Nat) : RationalResult :=
  rationalReplayAux leftGraph rightGraph fuel [] [(left, right)]

/-- Every negative replay result carries a genuine reachable outer-shape
conflict.  Exhaustion and missing nodes cannot inhabit this theorem. -/
theorem rationalReplayAux_conflict_valid
    (leftGraph rightGraph : RationalGraph) :
    ∀ fuel seen work witness,
      rationalReplayAux leftGraph rightGraph fuel seen work =
        .conflict witness →
      witness.Valid leftGraph rightGraph := by
  intro fuel
  induction fuel with
  | zero =>
      intro seen work witness h
      cases work <;> simp [rationalReplayAux] at h
  | succ fuel ih =>
      intro seen work witness h
      cases work with
      | nil => simp [rationalReplayAux] at h
      | cons pair rest =>
          rcases pair with ⟨left, right⟩
          by_cases hseen : (left, right) ∈ seen
          · apply ih seen rest witness
            simpa [rationalReplayAux, hseen] using h
          · cases hleft : leftGraph[left]? with
            | none =>
                simp [rationalReplayAux, hseen, hleft] at h
            | some leftNode =>
                cases hright : rightGraph[right]? with
                | none =>
                    simp [rationalReplayAux, hseen, hleft, hright] at h
                | some rightNode =>
                    by_cases hhead : leftNode.head = rightNode.head
                    · by_cases harity : leftNode.children.length =
                          rightNode.children.length
                      · apply ih ((left, right) :: seen)
                          (leftNode.children.zip rightNode.children ++ rest)
                          witness
                        simpa [rationalReplayAux, hseen, hleft, hright,
                          hhead, harity] using h
                      · simp [rationalReplayAux, hseen, hleft, hright,
                          hhead, harity] at h
                        subst witness
                        exact ⟨hleft, hright, Or.inr harity⟩
                    · simp [rationalReplayAux, hseen, hleft, hright,
                        hhead] at h
                      subst witness
                      exact ⟨hleft, hright, Or.inl hhead⟩

/-- Public root-replay form of conflict validity. -/
theorem rationalReplay_conflict_valid
    (fuel : Nat) (leftGraph : RationalGraph) (left : Nat)
    (rightGraph : RationalGraph) (right : Nat)
    (witness : RationalConflict)
    (h : rationalReplay fuel leftGraph left rightGraph right =
      .conflict witness) :
    witness.Valid leftGraph rightGraph :=
  rationalReplayAux_conflict_valid leftGraph rightGraph fuel []
    [(left, right)] witness h

/-- A two-node productive cycle is accepted coinductively. -/
example :
    let graph : RationalGraph :=
      [ { head := 0, children := [1] }
      , { head := 0, children := [0] } ]
    rationalReplay 4 graph 0 graph 1 = .compatible := by decide

/-- A recursive list/tree head contradiction is a definite conflict. -/
example :
    let lists : RationalGraph := [{ head := 0, children := [0] }]
    let trees : RationalGraph := [{ head := 1, children := [0] }]
    ∃ witness, rationalReplay 1 lists 0 trees 0 = .conflict witness := by
  exact ⟨mkRationalConflict 0 0 { head := 0, children := [0] }
    { head := 1, children := [0] }, rfl⟩

/-- Exhaustion is not a structural verdict. -/
example :
    rationalReplay 0 [{ head := 0, children := [0] }] 0
      [{ head := 0, children := [0] }] 0 = .incomplete := by rfl

/-! ### The census polarity classes, as kernel-checked witnesses -/

/-- `actual-union-universal-rejection`: an actual union with one
unacceptable member is rejected. -/
example : consistent? (.union (.prim .num) (.prim .str)) (.prim .num)
    = false := by simp [consistent?]

/-- Required union, existential accept. -/
example : consistent? (.prim .num) (.union (.prim .num) (.prim .str))
    = true := by simp [consistent?]

/-- `required-union-existential-rejection`: no alternative fits. -/
example : consistent? (.prim .bool) (.union (.prim .num) (.prim .str))
    = false := by simp [consistent?]

/-- `newtype-nominal-distinctness`: same representation, different brand,
not consistent. -/
example : consistent? (.newtype 0 (.prim .num)) (.newtype 1 (.prim .num))
    = false := by simp [consistent?]

/-- **The gradual essence — non-transitivity**: `num ~ ? ~ str` yet
`num ≁ str`.  This is the theorem that makes `?Unknown` ignorance rather
than a top type. -/
theorem consistency_not_transitive :
    consistent? (.prim .num) .unknown = true ∧
    consistent? .unknown (.prim .str) = true ∧
    consistent? (.prim .num) (.prim .str) = false := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [consistent?]

/-! ## §5 Open-world joins: taint-widening as a proven-safe choice -/

/-- v2's publication behavior: conflicting inferences widen to `?Unknown`
(census: `inferred-parameter-conflict-widens-unknown`,
`inferred-output-publication-normalization`). -/
def joinPublish (a b : Ty) : Ty := if a = b then a else .unknown

/-- v3 candidate improvement: retain the union instead of widening
(intake candidate class: publication kept shape information internally
that v2 discarded at the signature boundary). -/
def joinPrecise (a b : Ty) : Ty := if a = b then a else .union a b

/-- Both joins are gradual-safe: each argument flows into the join.  The
two lemmas make the v2-vs-v3 publication policies *both lawful*, so the
divergence is a reviewable choice, not a correctness question. -/
theorem joinPublish_safe (a b : Ty) :
    Consistent a (joinPublish a b) ∧ Consistent b (joinPublish b a) := by
  constructor <;> · unfold joinPublish; split
                    · exact .refl _
                    · exact .unknownR _

theorem joinPrecise_safe (a b : Ty) :
    Consistent a (joinPrecise a b) ∧ Consistent b (joinPrecise b a) := by
  refine ⟨?_, ?_⟩ <;> · unfold joinPrecise; split
                        · exact .refl _
                        · exact .unionR1 (.refl _)

/-- What v3's precise join retains and v2's publication discards. -/
example :
    joinPrecise (.prim .num) (.prim .str)
      = .union (.prim .num) (.prim .str) ∧
    joinPublish (.prim .num) (.prim .str) = .unknown := by decide

/-! ## §6 Stage evidence: grounding requires compiled-stage facts -/

/-- Which representation a fact describes. -/
inductive Stage where
  | source | evaluated | compiled
  deriving DecidableEq, Repr

/-- An evidence item: some fact tag at some stage. -/
structure Evidence where
  fact : Nat
  stage : Stage
  deriving DecidableEq, Repr

/-- A grounding license — the authority to strengthen a judgment using a
concrete fact — structurally requires compiled-stage evidence.  The unsafe
grounding bug (using source shape as compiled-stage evidence) is
unrepresentable against this structure. -/
structure GroundingLicense where
  evidence : Evidence
  compiledStage : evidence.stage = .compiled

/-- The discipline, stated: every grounding license is compiled-stage. -/
theorem grounding_is_compiled (l : GroundingLicense) :
    l.evidence.stage = .compiled := l.compiledStage

/-- Negative witness: no license can be built on source-stage evidence. -/
theorem no_source_grounding (e : Evidence) (h : e.stage = .source) :
    ¬ ∃ l : GroundingLicense, l.evidence = e := by
  rintro ⟨l, rfl⟩
  rw [l.compiledStage] at h
  cases h

/-! ### Executable evidence transport for H5

The stage census is mostly about transporting positive evidence without
confusing held code with an executed value.  The small algebra below makes
that distinction structural, preserves list/Boolean selector facts through
control flow, and keeps empty-result cardinality separate from result type.
-/

/-- Positive boundary facts used by total clause selection. -/
structure BoundaryFacts where
  properList : Bool := false
  boolean : Bool := false
  nonemptyExpression : Bool := false
  deriving DecidableEq, Repr

namespace BoundaryFacts

/-- Branch merging retains only facts established by every producing branch. -/
def meet (left right : BoundaryFacts) : BoundaryFacts :=
  { properList := left.properList && right.properList
    boolean := left.boolean && right.boolean
    nonemptyExpression :=
      left.nonemptyExpression && right.nonemptyExpression }

@[simp] theorem meet_self (facts : BoundaryFacts) : facts.meet facts = facts := by
  cases facts
  simp [meet]

theorem meet_comm (left right : BoundaryFacts) :
    left.meet right = right.meet left := by
  cases left
  cases right
  simp [meet, Bool.and_comm]

end BoundaryFacts

/-- Result knowledge separates ignorance from a proof that no value can be
produced.  This is the distinction needed by all-bottom conditionals and
superpositions: an empty computation vacuously satisfies any result shape,
whereas an unknown computation establishes none. -/
inductive ResultEvidence where
  | unknown
  | empty
  | typed (type : Ty)
  deriving DecidableEq, Repr

/-- Positive typing/cardinality evidence for an executed computation. -/
structure RuntimeEvidence where
  result : ResultEvidence
  card : Card
  stage : Stage
  facts : BoundaryFacts
  deriving DecidableEq, Repr

/-- Quotation retains latent evidence but does not expose it as runtime
typing evidence.  Only explicit evaluation can reactivate it. -/
structure HeldEvidence where
  result : ResultEvidence
  card : Card
  facts : BoundaryFacts
  deriving DecidableEq, Repr

def quoteEvidence (evidence : RuntimeEvidence) : HeldEvidence :=
  { result := evidence.result
    card := evidence.card
    facts := evidence.facts }

def evaluateEvidence (held : HeldEvidence) : RuntimeEvidence :=
  { result := held.result
    card := held.card
    stage := .evaluated
    facts := held.facts }

/-- The explicit quote/eval round trip preserves latent type, grade, and
selector evidence while changing the usable stage to evaluated. -/
theorem evaluate_quote_preserves (evidence : RuntimeEvidence) :
    evaluateEvidence (quoteEvidence evidence) =
      { evidence with stage := .evaluated } := by
  cases evidence
  rfl

/-- Quoting a structural expression produces an evaluated code datum whose
field spine includes the held head.  The contents have not executed: only
their code shapes are present. -/
def quotedProductEvidence (fields : TyArgs) : RuntimeEvidence :=
  { result := .typed (.product fields)
    card := .det
    stage := .evaluated
    facts := { nonemptyExpression := true } }

def quotedDataCodeFields : TyArgs :=
  .cons (.prim .sym) (.cons (.prim .sym) (.cons (.prim .num) .nil))

/-- Administrative aliases are exact evidence transport. -/
def aliasEvidence (evidence : RuntimeEvidence) : RuntimeEvidence := evidence

@[simp] theorem aliasEvidence_exact (evidence : RuntimeEvidence) :
    aliasEvidence evidence = evidence := rfl

/-! ### Pattern admission

Patterns consume types contravariantly: they describe the subset of a
scrutinee that can reach a clause and introduce local assumptions for the
variables they bind.  Provider lookup has already resolved a constructor to
its result and field types before it enters this calculus. -/

mutual

/-- Provider-resolved source patterns.  A constructor records its result type
and a spine pairing each child pattern with the constructor field type. -/
inductive Pattern where
  | variable (name : Nat)
  | literal (actual : Ty)
  | constructor (actual : Ty) (fields : PatternArgs)

inductive PatternArgs where
  | nil
  | cons (pattern : Pattern) (expected : Ty) (tail : PatternArgs)

end

abbrev PatternEnv := List (Nat × Ty)

def PatternEnv.lookup (env : PatternEnv) (name : Nat) : Option Ty :=
  match env.find? (fun binding => binding.1 = name) with
  | none => none
  | some binding => some binding.2

/-- Every statically empty pattern carries the exact failed overlap judgment. -/
structure PatternConflict where
  actual : Ty
  required : Ty
  witness : mayOverlap? actual required = false

inductive PatternOutcome where
  | admitted (env : PatternEnv)
  | empty (conflict : PatternConflict)

/-- Convert one decided overlap boundary into an admission outcome. -/
def admitPatternOverlap (actual required : Ty) (env : PatternEnv) :
    PatternOutcome :=
  if h : mayOverlap? actual required = true then
    .admitted env
  else
    .empty
      { actual := actual
        required := required
        witness := by
          cases hoverlap : mayOverlap? actual required <;> simp_all }

mutual

/-- Bind a provider-resolved pattern against the type of its scrutinee.
Repeated variables require possible overlap with their earlier assumption. -/
def bindPattern : Pattern → Ty → PatternEnv → PatternOutcome
  | .variable name, expected, env =>
      match env.lookup name with
      | none => .admitted ((name, expected) :: env)
      | some prior => admitPatternOverlap prior expected env
  | .literal actual, expected, env =>
      admitPatternOverlap actual expected env
  | .constructor actual fields, expected, env =>
      match admitPatternOverlap actual expected env with
      | .empty conflict => .empty conflict
      | .admitted narrowed => bindPatternArgs fields narrowed
termination_by pattern _expected _env => sizeOf pattern
decreasing_by all_goals (simp_wf; omega)

/-- Bind constructor fields from left to right so repeated names observe every
earlier occurrence. -/
def bindPatternArgs : PatternArgs → PatternEnv → PatternOutcome
  | .nil, env => .admitted env
  | .cons pattern expected tail, env =>
      match bindPattern pattern expected env with
      | .empty conflict => .empty conflict
      | .admitted extended => bindPatternArgs tail extended
termination_by patterns _env => sizeOf patterns
decreasing_by all_goals (simp_wf; omega)

end


/-- An empty-pattern certificate cannot be produced without failed overlap. -/
theorem PatternConflict.valid (conflict : PatternConflict) :
    mayOverlap? conflict.actual conflict.required = false :=
  conflict.witness

/-- A fresh variable always acquires exactly the demanded local assumption. -/
theorem bindPattern_fresh_variable (name : Nat) (expected : Ty)
    (env : PatternEnv) (h : env.lookup name = none) :
    bindPattern (.variable name) expected env =
      .admitted ((name, expected) :: env) := by
  simp [bindPattern, h]

/-- Positive witness: a constructor can narrow a required union and gives its
field variable the constructor's declared domain. -/
example :
    bindPattern
      (.constructor (.newtype 7 .unknown)
        (.cons (.variable 0) (.prim .num) .nil))
      (.union (.newtype 7 .unknown) (.list .unknown)) [] =
      .admitted [(0, .prim .num)] := by
  simp [bindPattern, bindPatternArgs, admitPatternOverlap,
    PatternEnv.lookup, mayOverlap?]

/-- Negative match witness: a literal disjoint from its domain makes the
clause unreachable rather than making the whole program ill-typed. -/
example :
    ∃ conflict,
      bindPattern (.literal (.prim .str)) (.prim .num) [] =
        .empty conflict := by
  simp [bindPattern, admitPatternOverlap, mayOverlap?, consistent?]

/-- Negative match witness: incompatible repeated occurrences make the clause
unreachable; exhaustiveness is a separate relation-level judgment. -/
example :
    ∃ conflict,
      bindPattern (.variable 0) (.prim .str) [(0, .prim .num)] =
        .empty conflict := by
  simp [bindPattern, admitPatternOverlap, PatternEnv.lookup,
    mayOverlap?, consistent?]

/-! ### Relation-level coverage

Coverage is decided once a whole mutually visible clause group is available.
It remains success-typing asymmetric: an open pattern column proves nothing,
while a fully keyed column may refute totality only by producing a concrete
inhabiting key that no clause covers. -/

/-- The top-level value shape observed by one pattern column.  The numeric tag
is provider-resolved constructor identity; arity distinguishes constructors
whose printed names happen to coincide. -/
structure PatternKey where
  tag : Nat
  arity : Nat
  deriving DecidableEq, Repr

/-- Turn a column into keys only when every pattern has a decidable top-level
shape.  `none` is a variable, wildcard, computed term, or otherwise open
pattern and deliberately makes the negative coverage test silent. -/
def collectPatternKeys : List (Option PatternKey) → Option (List PatternKey)
  | [] => some []
  | none :: _ => none
  | some key :: rest => (collectPatternKeys rest).map (key :: ·)

/-- Find a definitely inhabiting candidate shape absent from all observed
clause keys.  The provider supplies candidates: a closed finite domain may
supply all constructors, while an infinite primitive supplies one fresh
literal witness. -/
def findMissingKey (candidates observed : List PatternKey) :
    Option { key // key ∈ candidates ∧ key ∉ observed } :=
  match candidates with
  | [] => none
  | key :: rest =>
      if h : key ∈ observed then
        match findMissingKey rest observed with
        | none => none
        | some witness =>
            some ⟨witness.1, by
              constructor
              · simp [witness.2.1]
              · exact witness.2.2⟩
      else
        some ⟨key, by simp, h⟩

/-- A negative totality decision carries both evidence boundaries: every
clause in the selected column had a key, and the provider supplied a concrete
inhabiting key not among them. -/
structure CoverageConflict
    (candidates : List PatternKey) (column : List (Option PatternKey)) where
  observed : List PatternKey
  missing : PatternKey
  column_keyed : collectPatternKeys column = some observed
  candidate_witness : missing ∈ candidates
  uncovered_witness : missing ∉ observed

def coverageConflict? (candidates : List PatternKey)
    (column : List (Option PatternKey)) :
    Option (CoverageConflict candidates column) :=
  match hcolumn : collectPatternKeys column with
  | none => none
  | some observed =>
      match findMissingKey candidates observed with
      | none => none
      | some witness =>
          some
            { observed := observed
              missing := witness.1
              column_keyed := hcolumn
              candidate_witness := witness.2.1
              uncovered_witness := witness.2.2 }

/-- An open head pattern can never manufacture a non-exhaustiveness verdict. -/
theorem coverageConflict?_open_head (candidates : List PatternKey)
    (tail : List (Option PatternKey)) :
    coverageConflict? candidates (none :: tail) = none := rfl

/-- Positive finite-domain witness: matching only `true` misses `false`. -/
example :
    let truth := PatternKey.mk 0 0
    let falsity := PatternKey.mk 1 0
    ∃ conflict,
      coverageConflict? [truth, falsity] [some truth] = some conflict ∧
        conflict.missing = falsity := by
  simp [coverageConflict?, collectPatternKeys, findMissingKey]

/-- Negative finite-domain witness: both Boolean keys cover the candidate
domain, so no conflict is produced. -/
example :
    let truth := PatternKey.mk 0 0
    let falsity := PatternKey.mk 1 0
    coverageConflict? [truth, falsity] [some truth, some falsity] = none := by
  decide

/-- Positive infinite-domain witness: the provider-selected fresh numeric key
is enough to refute a literal-only column. -/
example :
    let one := PatternKey.mk 1 0
    let two := PatternKey.mk 2 0
    let other := PatternKey.mk 3 0
    ∃ conflict,
      coverageConflict? [other] [some one, some two] = some conflict := by
  simp [coverageConflict?, collectPatternKeys, findMissingKey]

/-! ### Lexical evidence bindings

Source variable names are elaborated to de Bruijn indices before this layer.
That makes `let`/`let*` evidence transport independent of spelling and makes
shadowing a list operation instead of a name-comparison side condition.
-/

abbrev EvidenceEnv := List RuntimeEvidence

/-- A sequential binding either introduces already computed evidence or
forwards evidence from an earlier lexical slot. -/
inductive BindingSource where
  | value (evidence : RuntimeEvidence)
  | alias (index : Nat)
  deriving DecidableEq, Repr

def resolveBindingSource (env : EvidenceEnv) : BindingSource →
    Option RuntimeEvidence
  | .value evidence => some evidence
  | .alias index => env[index]?

/-- Evaluate a `let*` spine.  Every successful binding is pushed at index
zero; a dangling alias is ignorance (`none`), never a fabricated conflict. -/
def applyBindings : EvidenceEnv → List BindingSource → Option EvidenceEnv
  | env, [] => some env
  | env, source :: rest => do
      let evidence ← resolveBindingSource env source
      applyBindings (evidence :: env) rest

/-- A lexical value is evaluated before its body.  The body determines the
result type and boundary facts; sequencing retains the weaker cardinality.
This is elaboration evidence computed once, not an evaluator-side recheck. -/
def letEvidence (value body : RuntimeEvidence) : RuntimeEvidence :=
  { body with
    card := value.card.seq body.card
    stage := .evaluated }

@[simp] theorem resolveBindingSource_value (env : EvidenceEnv)
    (evidence : RuntimeEvidence) :
    resolveBindingSource env (.value evidence) = some evidence := rfl

theorem resolveBindingSource_alias_exact (env : EvidenceEnv) (index : Nat)
    (evidence : RuntimeEvidence) (h : env[index]? = some evidence) :
    resolveBindingSource env (.alias index) = some evidence := by
  simpa [resolveBindingSource] using h

def boolEvidence : RuntimeEvidence :=
  { result := .typed (.prim .bool)
    card := .det
    stage := .evaluated
    facts := { boolean := true } }

def numberEvidence : RuntimeEvidence :=
  { result := .typed (.prim .num)
    card := .det
    stage := .evaluated
    facts := {} }

def nondetBoolEvidence : RuntimeEvidence :=
  { boolEvidence with card := .nondet }

/-- A three-hop administrative alias chain preserves Boolean evidence. -/
example :
    (applyBindings []
      [ .value boolEvidence, .alias 0, .alias 0 ]).bind
        (fun env => env[0]?) = some boolEvidence := by decide

/-- Alias forwarding preserves nondeterministic grade. -/
example :
    (applyBindings []
      [ .value nondetBoolEvidence, .alias 0 ]).bind
        (fun env => env[0]?.map RuntimeEvidence.card) = some .nondet := by
  decide

/-- A later shadowing binding cannot rewrite evidence already copied into an
earlier lexical slot.  After elaboration the retained alias has index one. -/
example :
    (applyBindings []
      [ .value numberEvidence, .alias 0, .value boolEvidence ]).bind
        (fun env => env[1]?) = some numberEvidence := by decide

/-- A dangling source index yields no environment. -/
example : applyBindings [] [.alias 0] = none := rfl

/-- A deterministic Boolean binding preserves the body's exact evidence. -/
example : letEvidence boolEvidence numberEvidence = numberEvidence := by
  decide

/-- A nondeterministic producer cannot be laundered into deterministic lexical
evidence merely because its body is deterministic. -/
example :
    (letEvidence nondetBoolEvidence numberEvidence).card = .nondet := by
  decide

/-- Join result knowledge.  Proven emptiness is neutral, two producing
branches use v3's precision-retaining join, and genuine ignorance remains
contagious. -/
def joinResultEvidence : ResultEvidence → ResultEvidence → ResultEvidence
  | .unknown, _ => .unknown
  | _, .unknown => .unknown
  | .empty, right => right
  | left, .empty => left
  | .typed left, .typed right => .typed (joinPrecise left right)

/-- Merge two control-flow branches.  An absent branch contributes semidet
cardinality but cannot erase the positive type/facts of the branch that does
produce.  Two absent branches have no result type. -/
def branchEvidence : Option RuntimeEvidence → Option RuntimeEvidence →
    RuntimeEvidence
  | none, none =>
      { result := .empty
        card := .semidet
        stage := .evaluated
        facts := {} }
  | some left, none =>
      { left with card := left.card.seq .semidet, stage := .evaluated }
  | none, some right =>
      { right with card := Card.semidet.seq right.card, stage := .evaluated }
  | some left, some right =>
      { result := joinResultEvidence left.result right.result
        card := left.card.seq right.card
        stage := .evaluated
        facts := left.facts.meet right.facts }

/-- Conditional execution also sequences the condition's grade. -/
def conditionalEvidence (condition : RuntimeEvidence)
    (thenBranch elseBranch : Option RuntimeEvidence) : RuntimeEvidence :=
  let branches := branchEvidence thenBranch elseBranch
  { branches with card := condition.card.seq branches.card }

/-- Both empty branches retain semidet cardinality without inventing a type. -/
example : branchEvidence none none =
    { result := .empty
      card := .semidet
      stage := .evaluated
      facts := {} } := rfl

/-- A producing branch and an empty branch retain the possible result type
and its list evidence, but the expression becomes semideterministic. -/
example :
    let listEvidence : RuntimeEvidence :=
      { result := .typed (.list (.prim .num))
        card := .det
        stage := .evaluated
        facts := { properList := true } }
    branchEvidence (some listEvidence) none =
      { listEvidence with card := .semidet } := by
  decide

/-- Requirements for a total selector. -/
inductive SelectionRequirement where
  | properList | boolean | nonemptyExpression
  deriving DecidableEq, Repr

def BoundaryFacts.supports (facts : BoundaryFacts) :
    SelectionRequirement → Bool
  | .properList => facts.properList
  | .boolean => facts.boolean
  | .nonemptyExpression => facts.nonemptyExpression

/-- A selector receives a grade only from positive domain evidence.  Missing
evidence is `none`, never a deterministic assumption. -/
def selectionCard (input : RuntimeEvidence)
    (requirement : SelectionRequirement) (continuation : Card) : Option Card :=
  if input.facts.supports requirement then
    some (input.card.seq continuation)
  else
    none

/-- Positive list-selection witness. -/
example :
    let input : RuntimeEvidence :=
      { result := .typed (.list (.prim .num))
        card := .det
        stage := .evaluated
        facts := { properList := true } }
    selectionCard input .properList .det = some .det := by decide

/-- Negative scalar-selection witness: a Number type does not manufacture a
proper-list boundary fact. -/
example :
    let input : RuntimeEvidence :=
      { result := .typed (.prim .num)
        card := .det
        stage := .evaluated
        facts := {} }
    selectionCard input .properList .det = none := by decide

/-- `once` preserves det/semidet and caps nondet at semidet. -/
def onceCard : Card → Card
  | .det => .det
  | .semidet => .semidet
  | .nondet => .semidet

/-- An empty fold returns exactly the initializer evidence. -/
def foldEmptyEvidence (initial : RuntimeEvidence) : RuntimeEvidence :=
  { initial with stage := .evaluated }

/-- An all-empty superposition has a known nondeterministic grade but no
positive result type or selector facts. -/
def allEmptySuperposeEvidence : RuntimeEvidence :=
  { result := .empty
    card := .nondet
    stage := .evaluated
    facts := {} }

example : onceCard .nondet = .semidet := rfl
example (initial : RuntimeEvidence) :
    (foldEmptyEvidence initial).result = initial.result := rfl
example : allEmptySuperposeEvidence.result = .empty ∧
    allEmptySuperposeEvidence.card = .nondet := by decide

/-! ## §7 Evidence outcomes: ignorance is not refutation -/

/-- A refutation identifies the axis on which positive evidence conflicts
with a requirement.  Missing evidence cannot construct either witness. -/
inductive EvidenceConflict where
  | shape (actual expected : Ty)
  | cardinality (actual : Card) (demand : ArrowMode)
  deriving DecidableEq, Repr

/-- Executable validation for refutation witnesses. -/
def EvidenceConflict.valid : EvidenceConflict → Bool
  | .shape actual expected => !(consistent? actual expected)
  | .cardinality actual demand => !(modeFits (.grade actual) demand)

/-- The NIK outcome algebra used at the evidence boundary.  Exhaustion is
separate from both ignorance and a witnessed refutation. -/
inductive EvidenceOutcome where
  | established
  | refuted (conflict : EvidenceConflict)
  | undetermined
  | incomplete
  deriving DecidableEq, Repr

/-- Check runtime evidence against a result shape and grade demand.  Unknown
result knowledge is undetermined.  Proven emptiness checks only the grade and
vacuously satisfies the result shape. -/
def checkEvidence (evidence : RuntimeEvidence) (expected : Ty)
    (demand : ArrowMode) : EvidenceOutcome :=
  match evidence.result with
  | .unknown => .undetermined
  | .empty =>
      if modeFits (.grade evidence.card) demand then .established
      else .refuted (.cardinality evidence.card demand)
  | .typed actual =>
      if consistent? actual expected then
        if modeFits (.grade evidence.card) demand then .established
        else .refuted (.cardinality evidence.card demand)
      else .refuted (.shape actual expected)

/-- Every negative evidence outcome carries a valid, replayable conflict. -/
theorem checkEvidence_refuted_valid (evidence : RuntimeEvidence)
    (expected : Ty) (demand : ArrowMode) (conflict : EvidenceConflict)
    (h : checkEvidence evidence expected demand = .refuted conflict) :
    conflict.valid = true := by
  cases evidence with
  | mk result card stage facts =>
      cases result with
      | unknown => simp [checkEvidence] at h
      | empty =>
          cases hcard : modeFits (.grade card) demand with
          | false =>
              simp [checkEvidence, hcard] at h
              subst conflict
              simp [EvidenceConflict.valid, hcard]
          | true => simp [checkEvidence, hcard] at h
      | typed actual =>
          cases hshape : consistent? actual expected with
          | false =>
              simp [checkEvidence, hshape] at h
              subst conflict
              simp [EvidenceConflict.valid, hshape]
          | true =>
              cases hcard : modeFits (.grade card) demand with
              | false =>
                  simp [checkEvidence, hshape, hcard] at h
                  subst conflict
                  simp [EvidenceConflict.valid, hcard]
              | true => simp [checkEvidence, hshape, hcard] at h

/-- Genuine ignorance is never converted into a refutation. -/
@[simp] theorem checkEvidence_unknown (card : Card) (stage : Stage)
    (facts : BoundaryFacts) (expected : Ty) (demand : ArrowMode) :
    checkEvidence { result := .unknown, card, stage, facts } expected demand =
      .undetermined := rfl

/-- Proven emptiness satisfies every result shape when its grade fits. -/
theorem checkEvidence_empty (card : Card) (stage : Stage)
    (facts : BoundaryFacts) (expected : Ty) (demand : ArrowMode)
    (h : modeFits (.grade card) demand = true) :
    checkEvidence { result := .empty, card, stage, facts } expected demand =
      .established := by simp [checkEvidence, h]

/-- Gradual unknown remains permissive when there is positive evidence that
the result is unknown.  This differs from having no evidence at all. -/
example :
    checkEvidence
      { result := .typed .unknown
        card := .det
        stage := .evaluated
        facts := {} }
      (.prim .num) (.grade .det) = .established := by
  simp [checkEvidence, modeFits, Card.le, Card.toNat]

/-- Positive disjoint shapes produce a named shape conflict. -/
example :
    checkEvidence
      { result := .typed (.prim .num)
        card := .det
        stage := .evaluated
        facts := {} }
      (.prim .str) (.grade .det) =
        .refuted (.shape (.prim .num) (.prim .str)) := by
  simp [checkEvidence, consistent?]

/-- A nondeterministic computation under a deterministic promise produces a
cardinality conflict rather than a shape conflict. -/
example :
    checkEvidence
      { result := .typed (.prim .num)
        card := .nondet
        stage := .evaluated
        facts := {} }
      (.prim .num) (.grade .det) =
        .refuted (.cardinality .nondet (.grade .det)) := by
  simp [checkEvidence, modeFits, Card.le, Card.toNat]

/-- H5 114: the code product includes `data`, its tag, and its payload. -/
example : checkEvidence (quotedProductEvidence quotedDataCodeFields)
    (.product quotedDataCodeFields) (.grade .det) = .established := by
  simp [checkEvidence, quotedProductEvidence, modeFits, Card.le, Card.toNat]

/-- H5 113: omitting the held `data` head is a replayable shape conflict. -/
example : checkEvidence (quotedProductEvidence quotedDataCodeFields)
    (.product (.cons (.prim .sym) (.cons (.prim .num) .nil)))
    (.grade .det) =
      .refuted
        (.shape (.product quotedDataCodeFields)
          (.product (.cons (.prim .sym) (.cons (.prim .num) .nil)))) := by
  simp [checkEvidence, quotedProductEvidence, quotedDataCodeFields,
    consistent?, consistentList?]

/-! ## §8 The composed judgment: multi-argument v3 calls -/

/-- A function signature carries a first-order argument spine, one effect
grade for the whole call, and a result shape. -/
structure FnSig where
  doms : TyArgs
  eff : ArrowMode
  cod : Ty

inductive Verdict where
  | accept
  | reject
  deriving DecidableEq, Repr

/-- Check one call: every argument must flow into the corresponding domain
and the effect must fit the demand.  All four axes compose here: shape
(`consistentList?`),
cardinality (`modeFits`), openness (via `unknown` in `consistent?`), and
stage discipline (grounded strengthening enters only via §6 licenses,
never inside this function). -/
def checkCall (sig : FnSig) (args : TyArgs)
    (demand : ArrowMode) : Verdict :=
  if consistentList? args sig.doms && modeFits sig.eff demand then .accept
  else .reject

/-- **Intent theorem 1 — success typing**: rejection only with a definite,
nameable conflict: either an argument spine provably cannot flow, or the effect
provably exceeds the demand.  Never from ignorance. -/
theorem checkCall_reject_has_witness (sig : FnSig) (args : TyArgs)
    (demand : ArrowMode) (h : checkCall sig args demand = .reject) :
    consistentList? args sig.doms = false ∨
      modeFits sig.eff demand = false := by
  unfold checkCall at h
  by_cases hc : consistentList? args sig.doms
  · by_cases hm : modeFits sig.eff demand
    · simp [hc, hm] at h
    · exact Or.inr (by simpa using hm)
  · exact Or.inl (by simpa using hc)

/-- Replace every domain in an argument spine by gradual unknown while
preserving arity. -/
def TyArgs.unknownLike : TyArgs → TyArgs
  | .nil => .nil
  | .cons _ tail => .cons .unknown tail.unknownLike

/-- An arity-correct, fully unknown argument spine passes the complete shape
axis. -/
@[simp] theorem consistentList?_unknownLike : ∀ doms : TyArgs,
    consistentList? doms.unknownLike doms = true
  | .nil => by simp [TyArgs.unknownLike]
  | .cons head tail => by
      simp [TyArgs.unknownLike, consistentList?,
        consistentList?_unknownLike tail]

/-- **Intent theorem 2 — gradual permissiveness**: an arity-correct,
fully-unknown argument spine always passes the shape axis; with a fitting
effect the call is accepted. -/
theorem checkCall_unknown_permissive (sig : FnSig) (demand : ArrowMode)
    (heff : modeFits sig.eff demand = true) :
    checkCall sig sig.doms.unknownLike demand = .accept := by
  unfold checkCall
  simp [heff]

/-- Positive multi-argument witness. -/
example :
    checkCall
      { doms := .cons (.prim .num) (.cons (.prim .str) .nil)
        eff := .grade .det
        cod := .prim .bool }
      (.cons (.prim .num) (.cons (.prim .str) .nil))
      (.grade .det) = .accept := by
  simp [checkCall, modeFits, Card.le, Card.toNat]

/-- Negative multi-argument witness: an arity mismatch is rejected. -/
example :
    checkCall
      { doms := .cons (.prim .num) (.cons (.prim .str) .nil)
        eff := .grade .det
        cod := .prim .bool }
      (.cons (.prim .num) .nil) (.grade .det) = .reject := by
  simp [checkCall, consistentList?, modeFits, Card.le, Card.toNat]

/-! ## §9 Checked langdef rule inventory

This ordered inventory is the Lean side of H7.  The cross-repository parity
gate compares these names, in this order, with the authored MeTTa
presentation.  In particular, the order records the unknown/actual-union/
required-union precedence of `consistent?`. -/

inductive LangdefRule where
  | cardLeDetDet
  | cardLeDetSemidet
  | cardLeDetNondet
  | cardLeSemidetSemidet
  | cardLeSemidetNondet
  | cardLeNondetNondet
  | modeFitsPlain
  | modeFitsNondetPlain
  | modeFitsNondetEffect
  | modeFitsEffect
  | modeFitsDemand
  | concretizeModeGrade
  | concretizeModePlain
  | concretizeModeEffect
  | directEffectCard
  | elaborateUnknown
  | elaborateNum
  | elaborateStr
  | elaborateBool
  | elaborateAtomWildcard
  | elaborateList
  | elaborateProduct
  | elaborateArrow
  | elaborateUnion
  | elaborateUnionSingleton
  | elaborateUnionCons
  | elaborateNominalAbstract
  | elaborateNominalAlias
  | elaborateNominalNewtype
  | elaborateBrand
  | elaborateArgsNil
  | elaborateArgsCons
  | elaborateModePlain
  | elaborateModeDet
  | elaborateModeSemidet
  | elaborateModeNondet
  | elaborateModeEffect
  | resolveUnknown
  | resolvePrim
  | resolveList
  | resolveProduct
  | resolveArrow
  | resolveUnion
  | resolveNewtype
  | resolveAlias
  | resolveDeclaredAbstract
  | resolveDeclaredNewtype
  | resolveArgsNil
  | resolveArgsCons
  | consistentInput
  | consistentUnknownLeft
  | consistentUnknownRight
  | consistentRefl
  | consistentUnionActual
  | consistentUnionRequiredLeft
  | consistentUnionRequiredRight
  | consistentList
  | consistentProduct
  | consistentArrow
  | consistentArgsNil
  | consistentArgsCons
  | consistentNewtype
  | mayOverlapUnionActualLeft
  | mayOverlapUnionActualRight
  | mayOverlapUnionRequiredLeft
  | mayOverlapUnionRequiredRight
  | mayOverlapNewtype
  | mayOverlapNewtypeRepresentationLeft
  | mayOverlapNewtypeRepresentationRight
  | mayOverlapForward
  | mayOverlapReverse
  | nonNominalPrim
  | nonNominalList
  | nonNominalProduct
  | nonNominalArrow
  | joinPublishEqual
  | joinPreciseEqual
  | cardSeqDetDet
  | cardSeqDetSemidet
  | cardSeqDetNondet
  | cardSeqSemidetDet
  | cardSeqSemidetSemidet
  | cardSeqSemidetNondet
  | cardSeqNondetDet
  | cardSeqNondetSemidet
  | cardSeqNondetNondet
  | factMeetNoNo
  | factMeetNoYes
  | factMeetYesNo
  | factMeetYesYes
  | factsMeet
  | factsUnknown
  | factsNum
  | factsStr
  | factsBool
  | factsSym
  | factsList
  | factsProduct
  | factsArrow
  | factsUnion
  | factsNewtype
  | expressionEvidenceKnown
  | expressionEvidenceQuotedProduct
  | expressionEvidenceQuote
  | expressionEvidenceEval
  | expressionEvidenceSuperposeTwoEmpty
  | expressionEvidenceIfAllEmpty
  | expressionEvidenceCaseAllEmpty
  | aliasEvidence
  | bindingLookupZero
  | bindingLookupSucc
  | bindingResolveValue
  | bindingResolveAlias
  | bindingApplyNil
  | bindingApplyCons
  | letEvidence
  | branchNoneNone
  | branchSomeNone
  | branchNoneSome
  | branchSomeSome
  | conditionalEvidence
  | selectionList
  | selectionBool
  | selectionExpression
  | foldEmpty
  | onceDet
  | onceSemidet
  | onceNondet
  | allEmptySuperpose
  | evidenceOutcomeUndetermined
  | evidenceOutcomeEmptyEstablished
  | evidenceOutcomeEstablished
  | groundingCompiled
  | callAccept
  deriving DecidableEq, Repr

def LangdefRule.name : LangdefRule → String
  | .cardLeDetDet => "v3-card-le-det-det"
  | .cardLeDetSemidet => "v3-card-le-det-semidet"
  | .cardLeDetNondet => "v3-card-le-det-nondet"
  | .cardLeSemidetSemidet => "v3-card-le-semidet-semidet"
  | .cardLeSemidetNondet => "v3-card-le-semidet-nondet"
  | .cardLeNondetNondet => "v3-card-le-nondet-nondet"
  | .modeFitsPlain => "v3-mode-fits-plain"
  | .modeFitsNondetPlain => "v3-mode-fits-nondet-plain"
  | .modeFitsNondetEffect => "v3-mode-fits-nondet-effect"
  | .modeFitsEffect => "v3-mode-fits-effect"
  | .modeFitsDemand => "v3-mode-fits-demand"
  | .concretizeModeGrade => "v3-concretize-mode-grade"
  | .concretizeModePlain => "v3-concretize-mode-plain"
  | .concretizeModeEffect => "v3-concretize-mode-effect"
  | .directEffectCard => "v3-direct-effect-card"
  | .elaborateUnknown => "v3-elaborate-unknown"
  | .elaborateNum => "v3-elaborate-num"
  | .elaborateStr => "v3-elaborate-str"
  | .elaborateBool => "v3-elaborate-bool"
  | .elaborateAtomWildcard => "v3-elaborate-atom-wildcard"
  | .elaborateList => "v3-elaborate-list"
  | .elaborateProduct => "v3-elaborate-product"
  | .elaborateArrow => "v3-elaborate-arrow"
  | .elaborateUnion => "v3-elaborate-union"
  | .elaborateUnionSingleton => "v3-elaborate-union-singleton"
  | .elaborateUnionCons => "v3-elaborate-union-cons"
  | .elaborateNominalAbstract => "v3-elaborate-nominal-abstract"
  | .elaborateNominalAlias => "v3-elaborate-nominal-alias"
  | .elaborateNominalNewtype => "v3-elaborate-nominal-newtype"
  | .elaborateBrand => "v3-elaborate-brand"
  | .elaborateArgsNil => "v3-elaborate-args-nil"
  | .elaborateArgsCons => "v3-elaborate-args-cons"
  | .elaborateModePlain => "v3-elaborate-mode-plain"
  | .elaborateModeDet => "v3-elaborate-mode-det"
  | .elaborateModeSemidet => "v3-elaborate-mode-semidet"
  | .elaborateModeNondet => "v3-elaborate-mode-nondet"
  | .elaborateModeEffect => "v3-elaborate-mode-effect"
  | .resolveUnknown => "v3-resolve-unknown"
  | .resolvePrim => "v3-resolve-prim"
  | .resolveList => "v3-resolve-list"
  | .resolveProduct => "v3-resolve-product"
  | .resolveArrow => "v3-resolve-arrow"
  | .resolveUnion => "v3-resolve-union"
  | .resolveNewtype => "v3-resolve-newtype"
  | .resolveAlias => "v3-resolve-alias"
  | .resolveDeclaredAbstract => "v3-resolve-declared-abstract"
  | .resolveDeclaredNewtype => "v3-resolve-declared-newtype"
  | .resolveArgsNil => "v3-resolve-args-nil"
  | .resolveArgsCons => "v3-resolve-args-cons"
  | .consistentInput => "v3-consistent-input"
  | .consistentUnknownLeft => "v3-consistent-unknown-left"
  | .consistentUnknownRight => "v3-consistent-unknown-right"
  | .consistentRefl => "v3-consistent-refl"
  | .consistentUnionActual => "v3-consistent-union-actual"
  | .consistentUnionRequiredLeft => "v3-consistent-union-required-left"
  | .consistentUnionRequiredRight => "v3-consistent-union-required-right"
  | .consistentList => "v3-consistent-list"
  | .consistentProduct => "v3-consistent-product"
  | .consistentArrow => "v3-consistent-arrow"
  | .consistentArgsNil => "v3-consistent-args-nil"
  | .consistentArgsCons => "v3-consistent-args-cons"
  | .consistentNewtype => "v3-consistent-newtype"
  | .mayOverlapUnionActualLeft => "v3-may-overlap-union-actual-left"
  | .mayOverlapUnionActualRight => "v3-may-overlap-union-actual-right"
  | .mayOverlapUnionRequiredLeft => "v3-may-overlap-union-required-left"
  | .mayOverlapUnionRequiredRight => "v3-may-overlap-union-required-right"
  | .mayOverlapNewtype => "v3-may-overlap-newtype"
  | .mayOverlapNewtypeRepresentationLeft =>
      "v3-may-overlap-newtype-representation-left"
  | .mayOverlapNewtypeRepresentationRight =>
      "v3-may-overlap-newtype-representation-right"
  | .mayOverlapForward => "v3-may-overlap-forward"
  | .mayOverlapReverse => "v3-may-overlap-reverse"
  | .nonNominalPrim => "v3-non-nominal-prim"
  | .nonNominalList => "v3-non-nominal-list"
  | .nonNominalProduct => "v3-non-nominal-product"
  | .nonNominalArrow => "v3-non-nominal-arrow"
  | .joinPublishEqual => "v3-join-publish-equal"
  | .joinPreciseEqual => "v3-join-precise-equal"
  | .cardSeqDetDet => "v3-card-seq-det-det"
  | .cardSeqDetSemidet => "v3-card-seq-det-semidet"
  | .cardSeqDetNondet => "v3-card-seq-det-nondet"
  | .cardSeqSemidetDet => "v3-card-seq-semidet-det"
  | .cardSeqSemidetSemidet => "v3-card-seq-semidet-semidet"
  | .cardSeqSemidetNondet => "v3-card-seq-semidet-nondet"
  | .cardSeqNondetDet => "v3-card-seq-nondet-det"
  | .cardSeqNondetSemidet => "v3-card-seq-nondet-semidet"
  | .cardSeqNondetNondet => "v3-card-seq-nondet-nondet"
  | .factMeetNoNo => "v3-fact-meet-no-no"
  | .factMeetNoYes => "v3-fact-meet-no-yes"
  | .factMeetYesNo => "v3-fact-meet-yes-no"
  | .factMeetYesYes => "v3-fact-meet-yes-yes"
  | .factsMeet => "v3-facts-meet"
  | .factsUnknown => "v3-facts-unknown"
  | .factsNum => "v3-facts-num"
  | .factsStr => "v3-facts-str"
  | .factsBool => "v3-facts-bool"
  | .factsSym => "v3-facts-sym"
  | .factsList => "v3-facts-list"
  | .factsProduct => "v3-facts-product"
  | .factsArrow => "v3-facts-arrow"
  | .factsUnion => "v3-facts-union"
  | .factsNewtype => "v3-facts-newtype"
  | .expressionEvidenceKnown => "v3-expression-evidence-known"
  | .expressionEvidenceQuotedProduct =>
      "v3-expression-evidence-quoted-product"
  | .expressionEvidenceQuote => "v3-expression-evidence-quote"
  | .expressionEvidenceEval => "v3-expression-evidence-eval"
  | .expressionEvidenceSuperposeTwoEmpty =>
      "v3-expression-evidence-superpose-two-empty"
  | .expressionEvidenceIfAllEmpty => "v3-expression-evidence-if-all-empty"
  | .expressionEvidenceCaseAllEmpty => "v3-expression-evidence-case-all-empty"
  | .aliasEvidence => "v3-alias-evidence"
  | .bindingLookupZero => "v3-binding-lookup-zero"
  | .bindingLookupSucc => "v3-binding-lookup-succ"
  | .bindingResolveValue => "v3-binding-resolve-value"
  | .bindingResolveAlias => "v3-binding-resolve-alias"
  | .bindingApplyNil => "v3-binding-apply-nil"
  | .bindingApplyCons => "v3-binding-apply-cons"
  | .letEvidence => "v3-let-evidence"
  | .branchNoneNone => "v3-branch-none-none"
  | .branchSomeNone => "v3-branch-some-none"
  | .branchNoneSome => "v3-branch-none-some"
  | .branchSomeSome => "v3-branch-some-some"
  | .conditionalEvidence => "v3-conditional-evidence"
  | .selectionList => "v3-selection-list"
  | .selectionBool => "v3-selection-bool"
  | .selectionExpression => "v3-selection-expression"
  | .foldEmpty => "v3-fold-empty"
  | .onceDet => "v3-once-det"
  | .onceSemidet => "v3-once-semidet"
  | .onceNondet => "v3-once-nondet"
  | .allEmptySuperpose => "v3-all-empty-superpose"
  | .evidenceOutcomeUndetermined => "v3-evidence-outcome-undetermined"
  | .evidenceOutcomeEmptyEstablished =>
      "v3-evidence-outcome-empty-established"
  | .evidenceOutcomeEstablished => "v3-evidence-outcome-established"
  | .groundingCompiled => "v3-grounding-compiled"
  | .callAccept => "v3-call-accept"

def langdefRules : List LangdefRule :=
  [ .cardLeDetDet
  , .cardLeDetSemidet
  , .cardLeDetNondet
  , .cardLeSemidetSemidet
  , .cardLeSemidetNondet
  , .cardLeNondetNondet
  , .modeFitsPlain
  , .modeFitsNondetPlain
  , .modeFitsNondetEffect
  , .modeFitsEffect
  , .modeFitsDemand
  , .concretizeModeGrade
  , .concretizeModePlain
  , .concretizeModeEffect
  , .directEffectCard
  , .elaborateUnknown
  , .elaborateNum
  , .elaborateStr
  , .elaborateBool
  , .elaborateAtomWildcard
  , .elaborateList
  , .elaborateProduct
  , .elaborateArrow
  , .elaborateUnion
  , .elaborateUnionSingleton
  , .elaborateUnionCons
  , .elaborateNominalAbstract
  , .elaborateNominalAlias
  , .elaborateNominalNewtype
  , .elaborateBrand
  , .elaborateArgsNil
  , .elaborateArgsCons
  , .elaborateModePlain
  , .elaborateModeDet
  , .elaborateModeSemidet
  , .elaborateModeNondet
  , .elaborateModeEffect
  , .resolveUnknown
  , .resolvePrim
  , .resolveList
  , .resolveProduct
  , .resolveArrow
  , .resolveUnion
  , .resolveNewtype
  , .resolveAlias
  , .resolveDeclaredAbstract
  , .resolveDeclaredNewtype
  , .resolveArgsNil
  , .resolveArgsCons
  , .consistentInput
  , .consistentUnknownLeft
  , .consistentUnknownRight
  , .consistentRefl
  , .consistentUnionActual
  , .consistentUnionRequiredLeft
  , .consistentUnionRequiredRight
  , .consistentList
  , .consistentProduct
  , .consistentArrow
  , .consistentArgsNil
  , .consistentArgsCons
  , .consistentNewtype
  , .mayOverlapUnionActualLeft
  , .mayOverlapUnionActualRight
  , .mayOverlapUnionRequiredLeft
  , .mayOverlapUnionRequiredRight
  , .mayOverlapNewtype
  , .mayOverlapNewtypeRepresentationLeft
  , .mayOverlapNewtypeRepresentationRight
  , .mayOverlapForward
  , .mayOverlapReverse
  , .nonNominalPrim
  , .nonNominalList
  , .nonNominalProduct
  , .nonNominalArrow
  , .joinPublishEqual
  , .joinPreciseEqual
  , .cardSeqDetDet
  , .cardSeqDetSemidet
  , .cardSeqDetNondet
  , .cardSeqSemidetDet
  , .cardSeqSemidetSemidet
  , .cardSeqSemidetNondet
  , .cardSeqNondetDet
  , .cardSeqNondetSemidet
  , .cardSeqNondetNondet
  , .factMeetNoNo
  , .factMeetNoYes
  , .factMeetYesNo
  , .factMeetYesYes
  , .factsMeet
  , .factsUnknown
  , .factsNum
  , .factsStr
  , .factsBool
  , .factsSym
  , .factsList
  , .factsProduct
  , .factsArrow
  , .factsUnion
  , .factsNewtype
  , .expressionEvidenceKnown
  , .expressionEvidenceQuotedProduct
  , .expressionEvidenceQuote
  , .expressionEvidenceEval
  , .expressionEvidenceSuperposeTwoEmpty
  , .expressionEvidenceIfAllEmpty
  , .expressionEvidenceCaseAllEmpty
  , .aliasEvidence
  , .bindingLookupZero
  , .bindingLookupSucc
  , .bindingResolveValue
  , .bindingResolveAlias
  , .bindingApplyNil
  , .bindingApplyCons
  , .letEvidence
  , .branchNoneNone
  , .branchSomeNone
  , .branchNoneSome
  , .branchSomeSome
  , .conditionalEvidence
  , .selectionList
  , .selectionBool
  , .selectionExpression
  , .foldEmpty
  , .onceDet
  , .onceSemidet
  , .onceNondet
  , .allEmptySuperpose
  , .evidenceOutcomeUndetermined
  , .evidenceOutcomeEmptyEstablished
  , .evidenceOutcomeEstablished
  , .groundingCompiled
  , .callAccept ]

def langdefRuleNames : List String := langdefRules.map LangdefRule.name

set_option maxRecDepth 2048 in
theorem langdefRules_nodup : langdefRules.Nodup := by decide

set_option maxRecDepth 2048 in
theorem langdefRuleNames_nodup : langdefRuleNames.Nodup := by decide

set_option maxRecDepth 2048 in
theorem langdefRules_count : langdefRules.length = 134 := rfl

/-! ## §9 Handoff obligations (for the completing agent) -/

def completedObligations : List String :=
  [ "H1-completeness: consistent?_complete and consistent?_eq_true_iff \
     close the executable/inductive equivalence through checked unionR \
     permutation lemmas."
  , "H2-multi-argument arrows: TyArgs and ConsistentArgs give same-length \
     pairwise flow; FnSig/checkCall and both intent theorems use argument \
     spines, with positive and arity-mismatch witnesses."
  , "H3-effect polymorphism: ArrowMode retains plain, concrete-grade, and \
     named-effect cases; EffectSubst performs explicit instantiation, direct \
     higher-order parameters provide only matching-slot grade evidence, the \
     five-mode v2 relation is executable, and modeFits_iff_le is its \
     concrete-grade restriction."
  , "H4-alias pre-pass: InputTy is resolved through an admitted alias-free \
     environment; unresolved aliases remain admission outcomes, while \
     consistentAfterAliases_invariant and sound prove exact transport."
  , "H6-rational trees: rationalReplay is a fuel-bounded bisimulation over \
     finite cyclic graphs; revisit closes productive cycles, exhaustion is \
     incomplete, and every conflict carries a validated head/arity witness."
  , "H7-langdef parity: LangdefRule.name is the ordered Lean inventory; \
     the cross-repository parity gate checks exact MeTTa rule order and \
     detects missing, reordered, and duplicate rules." ]

def handoffObligations : List String :=
  [ "H5-census correspondence: for each of the 51 intake candidates, an \
     executable witness that v3 gives the intended verdict (fixing the 25 \
     implementation-defect classes; divergences recorded with migrations)."
  ]

theorem completedObligations_count : completedObligations.length = 6 := rfl

theorem handoffObligations_count : handoffObligations.length = 1 := rfl

end Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
