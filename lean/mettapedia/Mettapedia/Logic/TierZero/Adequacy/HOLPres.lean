import Mettapedia.Logic.TierZero.Kernel2.Examples

/-!
# HOL Light's kernel as a tier-0 presentation

`holRules` is HOL Light's logical kernel (`fusion.ml`, revision 924faf0c) as kernel-v2 rules: the
two primitive type operators and the constant `=` of its initial signature, the formation of types
and terms, and its ten primitive inferences REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP,
DEDUCT_ANTISYM_RULE, INST, INST_TYPE. Its three extension operations, `new_axiom`,
`new_basic_definition` and `new_basic_type_definition`, and the signature operations `new_type` and
`new_constant`, are rule generators the owner admits (`newAxiomRules`, `newBasicDefinitionRules`,
`newBasicTypeDefinitionRules`, `newTypeRule`, `newConstantRule`).

## Encoding

Names are strings, as in HOL Light (`(atom-kind N string)` checks that a cited name is one).
* types: `(hol:tyvar "A")` and `(hol:tyapp "op" T₁ … Tₖ)`; `bool` is `(hol:tyapp "bool")`, `A → B`
  is `(hol:tyapp "fun" A B)`.
* terms: `(hol:var "x" T)`, `(hol:const "c" T)`, `(hol:comb F X)`, and the kernel's binder
  `(bind T B)` for an abstraction over a variable of type `T` whose body `B` calls it `(bv 0)`.
  Alpha-equivalent HOL terms are one kernel term: `\x:bool. x` and `\y:bool. y` are both
  `(bind (hol:tyapp "bool") (bv 0))`, so HOL Light's comparisons up to alpha (TRANS's middle
  term, EQ_MP's antecedent, hypothesis sets) are syntactic equality here.
* `s = t` at type `A`: `(hol:comb (hol:comb (hol:const "=" A→A→bool) s) t)` (`eqP`).
* hypothesis sets: `(set H₁ … Hₙ)`, cited by the claim; order and repetition do not matter
  (`union-of`, `remove-of`, `singleton-of`, `image-of` are set relations).

Judgments: `(hol.ty T)` `T` is a type; `(hol.tm M T)` `M` is a term of type `T`; `(hol.thm G P)`
the sequent `G ⊢ P`; `(hol.inst-pair ((hol:var "x" T) M))` and `(hol.type-pair ((hol:tyvar "A") T))`
one pair of an instantiation, asked once per pair by the list premise of INST and INST_TYPE.

## Departures from `fusion.ml`, all up to alpha

* BETA: HOL Light's `BETA` accepts `(\x. t) x` only for the bound variable's own name; here the
  name is gone, so `hol:BETA` accepts `(\x. t) y` for any variable `y` of `x`'s type. Such a
  theorem is HOL Light-derivable: BETA at a variable `z` fresh for `t` and `y`, then INST `[y/z]`,
  which yields an alpha-variant of it.
* INST and INST_TYPE rename no bound variable: with nameless binders no free variable is captured,
  and the result is alpha-equivalent to HOL Light's.

Example (`Controls.cTruth` in `HOLWorlds`): HOL Light's TRUTH, `⊢ T`, from `T_DEF` by `SYM` and `EQ_MP`, 13 nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOL

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Logic.TierZero.Kernel2

/-! ## Patterns -/

/-- The type variable `(hol:tyvar N)`. -/
def tyvarP (n : Pat) : Pat := pex [psym "hol:tyvar", n]
/-- The type `(hol:tyapp "op" T₁ … Tₖ)`. -/
def tyappP (op : String) (args : List Pat) : Pat := pex (psym "hol:tyapp" :: pstr op :: args)
/-- `bool`. -/
def boolP : Pat := tyappP "bool" []
/-- `A → B`. -/
def funP (a b : Pat) : Pat := tyappP "fun" [a, b]
/-- The variable `(hol:var N T)`. -/
def varP (n a : Pat) : Pat := pex [psym "hol:var", n, a]
/-- The constant `(hol:const "c" T)`. -/
def constP (c : String) (ty : Pat) : Pat := pex [psym "hol:const", pstr c, ty]
/-- The application `(hol:comb F X)`. -/
def combP (f x : Pat) : Pat := pex [psym "hol:comb", f, x]
/-- The type of `=` at `A`: `A → A → bool`. -/
def eqTyP (a : Pat) : Pat := funP a (funP a boolP)
/-- `s = t` at type `A`. -/
def eqP (a s t : Pat) : Pat := combP (combP (constP "=" (eqTyP a)) s) t
/-- The set `(set M₁ … Mₙ)`. -/
def setP (ms : List Pat) : Pat := pex (psym "set" :: ms)
/-- The empty set `(set)`. -/
def emptyP : Pat := setP []

/-- `(hol.ty T)`. -/
def tyJ (t : Pat) : Pat := pjd "hol.ty" [t]
/-- `(hol.tm M T)`. -/
def tmJ (m t : Pat) : Pat := pjd "hol.tm" [m, t]
/-- `(hol.thm G P)`. -/
def thmJ (g p : Pat) : Pat := pjd "hol.thm" [g, p]
/-- `(hol.inst-pair E)`. -/
def instPairJ (e : Pat) : Pat := pjd "hol.inst-pair" [e]
/-- `(hol.type-pair E)`. -/
def typePairJ (e : Pat) : Pat := pjd "hol.type-pair" [e]

/-- The atom kind of names. -/
def stringK : Pat := psym "string"

/-- The judgments of the presentation, with their arities. -/
def holJudgments : List (String × ℕ) :=
  [("hol.ty", 1), ("hol.tm", 2), ("hol.thm", 2), ("hol.inst-pair", 1), ("hol.type-pair", 1)]

/-! ## HOL types as data, for the signature -/

/-- A HOL type: a type variable, or a type operator applied to types. -/
inductive HolTy where
  | tyvar (n : String)
  | tyapp (op : String) (args : List HolTy)

/-- `bool`. -/
def HolTy.bool : HolTy := .tyapp "bool" []
/-- `A → B`. -/
def HolTy.fn (a b : HolTy) : HolTy := .tyapp "fun" [a, b]

/-- The position of a name in a list. -/
def posOf (n : String) : List String → Option ℕ
  | [] => none
  | m :: ms => if m = n then some 0 else (posOf n ms).map (· + 1)

mutual

/-- A type as a pattern: the type variables listed in `vs` are the formals `0, 1, …`; the others
stay data. -/
def HolTy.pat (vs : List String) : HolTy → Pat
  | .tyvar n => match posOf n vs with
    | some i => pv i
    | none => tyvarP (pstr n)
  | .tyapp op args => tyappP op (HolTy.patList vs args)

/-- Types as patterns. -/
def HolTy.patList (vs : List String) : List HolTy → List Pat
  | [] => []
  | a :: as => HolTy.pat vs a :: HolTy.patList vs as

end

mutual

/-- The type variables of a type, with repetitions, in order. -/
def HolTy.tyvarsRaw : HolTy → List String
  | .tyvar n => [n]
  | .tyapp _ args => HolTy.tyvarsList args

/-- The type variables of types. -/
def HolTy.tyvarsList : List HolTy → List String
  | [] => []
  | a :: as => HolTy.tyvarsRaw a ++ HolTy.tyvarsList as

end

/-- The type variables of a type, each once, in order of first occurrence. -/
def HolTy.tyvars (ty : HolTy) : List String := ty.tyvarsRaw.dedup

/-- A type as closed data: every type variable stays `(hol:tyvar "A")`. -/
def HolTy.closed (ty : HolTy) : Pat := ty.pat []

/-! ## The signature: type operators and constants -/

/-- **`new_type (op, k)`**: `hol:ty.op` over formals `a₁ … aₖ`:
`(hol.ty a₁) … (hol.ty aₖ) ⊢ (hol.ty (hol:tyapp "op" a₁ … aₖ))`. -/
def newTypeRule (op : String) (k : ℕ) : Rule :=
  ⟨k, (List.range k).map fun i => .judg (tyJ (pv i)), tyJ (tyappP op ((List.range k).map pv))⟩

/-- **`new_constant (c, ty)`**: `hol:const.c` over the type variables `α₁ … αₘ` of `ty`: every
instance of the generic type, at types, types the constant:
`(hol.ty α₁) … (hol.ty αₘ) ⊢ (hol.tm (hol:const "c" ty[α]) ty[α])`. Example: `=` at `A → A → bool`
has one formal, `A`. -/
def newConstantRule (c : String) (ty : HolTy) : Rule :=
  let vs := ty.tyvars
  ⟨vs.length, (List.range vs.length).map fun i => .judg (tyJ (pv i)),
    tmJ (constP c (ty.pat vs)) (ty.pat vs)⟩

/-- HOL Light's initial type operators (`the_type_constants`). -/
def baseTypes : List (String × ℕ) := [("bool", 0), ("fun", 2)]

/-- HOL Light's initial constant (`the_term_constants`): `=` at `A → A → bool`. -/
def baseConstants : List (String × HolTy) :=
  [("=", .fn (.tyvar "A") (.fn (.tyvar "A") .bool))]

/-! ## Formation of types and terms -/

/-- `hol:ty.var` (n): `(given n) (atom-kind n string) ⊢ (hol.ty (hol:tyvar n))`. -/
def tyVarRule : Rule := ⟨1, [.given (pv 0), .atomKind (pv 0) stringK], tyJ (tyvarP (pv 0))⟩

/-- `hol:tm.var` (n a): `(given n) (atom-kind n string) (hol.ty a) ⊢ (hol.tm (hol:var n a) a)`. -/
def tmVarRule : Rule :=
  ⟨2, [.given (pv 0), .atomKind (pv 0) stringK, .judg (tyJ (pv 1))], tmJ (varP (pv 0) (pv 1)) (pv 1)⟩

/-- `hol:tm.comb` (f x a b): `(hol.tm f (a → b)) (hol.tm x a) ⊢ (hol.tm (hol:comb f x) b)`. -/
def tmCombRule : Rule :=
  ⟨4, [.judg (tmJ (pv 0) (funP (pv 2) (pv 3))), .judg (tmJ (pv 1) (pv 2))],
    tmJ (combP (pv 0) (pv 1)) (pv 3)⟩

/-- `hol:tm.abs` (n a t b u): HOL Light's `mk_abs`: abstracting the variable `(hol:var n a)` from a
term `t` of type `b` gives a term of type `a → b`:
`(hol.tm (hol:var n a) a) (hol.tm t b) (is u (abstract (hol:var n a) t)) ⊢ (hol.tm (bind a u) (a → b))`.
-/
def tmAbsRule : Rule :=
  ⟨5, [.judg (tmJ (varP (pv 0) (pv 1)) (pv 1)), .judg (tmJ (pv 2) (pv 3)),
      .isAbstract (pv 4) (varP (pv 0) (pv 1)) (pv 2)],
    tmJ (pbnd (pv 1) (pv 4)) (funP (pv 1) (pv 3))⟩

/-! ## The ten primitive inferences -/

/-- `hol:REFL` (t a): `(hol.tm t a) ⊢ (hol.thm (set) (t = t))`. -/
def reflRule : Rule := ⟨2, [.judg (tmJ (pv 0) (pv 1))], thmJ emptyP (eqP (pv 1) (pv 0) (pv 0))⟩

/-- `hol:TRANS` (g a s t d v u): `(hol.thm g (s = t)) (hol.thm d (t = v)) (given u)
(union-of u g d) ⊢ (hol.thm u (s = v))`. -/
def transRule : Rule :=
  ⟨7, [.judg (thmJ (pv 0) (eqP (pv 1) (pv 2) (pv 3))), .judg (thmJ (pv 4) (eqP (pv 1) (pv 3) (pv 5))),
      .given (pv 6), .unionOf (pv 6) (pv 0) (pv 4)],
    thmJ (pv 6) (eqP (pv 1) (pv 2) (pv 5))⟩

/-- `hol:MK_COMB` (g a b f f₂ d x y u): `(hol.thm g (f = f₂)) (hol.thm d (x = y)) (given u)
(union-of u g d) ⊢ (hol.thm u (f x = f₂ y))`, with `f : a → b` and `x : a`. -/
def mkCombRule : Rule :=
  ⟨9, [.judg (thmJ (pv 0) (eqP (funP (pv 1) (pv 2)) (pv 3) (pv 4))),
      .judg (thmJ (pv 5) (eqP (pv 1) (pv 6) (pv 7))), .given (pv 8), .unionOf (pv 8) (pv 0) (pv 5)],
    thmJ (pv 8) (eqP (pv 2) (combP (pv 3) (pv 6)) (combP (pv 4) (pv 7)))⟩

/-- `hol:ABS` (g b s t n a s₂ t₂): `(hol.thm g (s = t)) (hol.tm (hol:var n a) a)
(absent-from (hol:var n a) g) (is s₂ (abstract (hol:var n a) s)) (is t₂ (abstract (hol:var n a) t))
⊢ (hol.thm g ((bind a s₂) = (bind a t₂)))`: the variable is free in no hypothesis. -/
def absRule : Rule :=
  ⟨8, [.judg (thmJ (pv 0) (eqP (pv 1) (pv 2) (pv 3))), .judg (tmJ (varP (pv 4) (pv 5)) (pv 5)),
      .absent (varP (pv 4) (pv 5)) (pv 0), .isAbstract (pv 6) (varP (pv 4) (pv 5)) (pv 2),
      .isAbstract (pv 7) (varP (pv 4) (pv 5)) (pv 3)],
    thmJ (pv 0) (eqP (funP (pv 5) (pv 1)) (pbnd (pv 5) (pv 6)) (pbnd (pv 5) (pv 7)))⟩

/-- `hol:BETA` (a u n b r): `(hol.tm ((bind a u) (hol:var n a)) b) (is r (open u (hol:var n a)))
⊢ (hol.thm (set) ((bind a u) (hol:var n a) = r))`. -/
def betaRule : Rule :=
  ⟨5, [.judg (tmJ (combP (pbnd (pv 0) (pv 1)) (varP (pv 2) (pv 0))) (pv 3)),
      .isOpen (pv 4) (pv 1) (varP (pv 2) (pv 0))],
    thmJ emptyP (eqP (pv 3) (combP (pbnd (pv 0) (pv 1)) (varP (pv 2) (pv 0))) (pv 4))⟩

/-- `hol:ASSUME` (p s): `(hol.tm p bool) (given s) (singleton-of s p) ⊢ (hol.thm s p)`. -/
def assumeRule : Rule :=
  ⟨2, [.judg (tmJ (pv 0) boolP), .given (pv 1), .singletonOf (pv 1) (pv 0)], thmJ (pv 1) (pv 0)⟩

/-- `hol:EQ_MP` (g p q d u): `(hol.thm g (p = q)) (hol.thm d p) (given u) (union-of u g d)
⊢ (hol.thm u q)`. -/
def eqMpRule : Rule :=
  ⟨5, [.judg (thmJ (pv 0) (eqP boolP (pv 1) (pv 2))), .judg (thmJ (pv 3) (pv 1)), .given (pv 4),
      .unionOf (pv 4) (pv 0) (pv 3)],
    thmJ (pv 4) (pv 2)⟩

/-- `hol:DEDUCT_ANTISYM_RULE` (g p d q g₁ d₁ u): `(hol.thm g p) (hol.thm d q) (given g₁)
(remove-of g₁ q g) (given d₁) (remove-of d₁ p d) (given u) (union-of u g₁ d₁)
⊢ (hol.thm u (p = q))`. -/
def deductAntisymRule : Rule :=
  ⟨7, [.judg (thmJ (pv 0) (pv 1)), .judg (thmJ (pv 2) (pv 3)), .given (pv 4),
      .removeOf (pv 4) (pv 3) (pv 0), .given (pv 5), .removeOf (pv 5) (pv 1) (pv 2), .given (pv 6),
      .unionOf (pv 6) (pv 4) (pv 5)],
    thmJ (pv 6) (eqP boolP (pv 1) (pv 3))⟩

/-- `hol:INST` (g p s g₂ p₂; list variable `e`): `(hol.thm g p) (given s)
(each e s (hol.inst-pair e)) (given g₂) (image-of g₂ s g) (is p₂ (subst s p)) ⊢ (hol.thm g₂ p₂)`. -/
def instRule : Rule :=
  ⟨5, [.judg (thmJ (pv 0) (pv 1)), .given (pv 2), .each 5 (pv 2) (instPairJ (pv 5)), .given (pv 3),
      .imageOf (pv 3) (pv 2) (pv 0), .isSubst (pv 4) (pv 2) (pv 1)],
    thmJ (pv 3) (pv 4)⟩

/-- `hol:inst-pair` (n a t): `(hol.tm (hol:var n a) a) (hol.tm t a)
⊢ (hol.inst-pair ((hol:var n a) t))`. -/
def instPairRule : Rule :=
  ⟨3, [.judg (tmJ (varP (pv 0) (pv 1)) (pv 1)), .judg (tmJ (pv 2) (pv 1))],
    instPairJ (pex [varP (pv 0) (pv 1), pv 2])⟩

/-- `hol:INST_TYPE` (g p s g₂ p₂; list variable `e`): as `hol:INST`, with type pairs. -/
def instTypeRule : Rule :=
  ⟨5, [.judg (thmJ (pv 0) (pv 1)), .given (pv 2), .each 5 (pv 2) (typePairJ (pv 5)), .given (pv 3),
      .imageOf (pv 3) (pv 2) (pv 0), .isSubst (pv 4) (pv 2) (pv 1)],
    thmJ (pv 3) (pv 4)⟩

/-- `hol:type-pair` (n t): `(hol.ty (hol:tyvar n)) (hol.ty t) ⊢ (hol.type-pair ((hol:tyvar n) t))`. -/
def typePairRule : Rule :=
  ⟨2, [.judg (tyJ (tyvarP (pv 0))), .judg (tyJ (pv 1))], typePairJ (pex [tyvarP (pv 0), pv 1])⟩

/-- **HOL Light's kernel as rules**: the formation of types and terms over the initial signature,
and the ten primitive inferences with their pair judgments. -/
def holRules : List (String × Rule) :=
  [("hol:ty.var", tyVarRule)] ++
  baseTypes.map (fun x => (s!"hol:ty.{x.1}", newTypeRule x.1 x.2)) ++
  [("hol:tm.var", tmVarRule), ("hol:tm.comb", tmCombRule), ("hol:tm.abs", tmAbsRule)] ++
  baseConstants.map (fun x => (s!"hol:const.{x.1}", newConstantRule x.1 x.2)) ++
  [("hol:REFL", reflRule), ("hol:TRANS", transRule), ("hol:MK_COMB", mkCombRule),
   ("hol:ABS", absRule), ("hol:BETA", betaRule), ("hol:ASSUME", assumeRule),
   ("hol:EQ_MP", eqMpRule), ("hol:DEDUCT_ANTISYM_RULE", deductAntisymRule),
   ("hol:INST", instRule), ("hol:inst-pair", instPairRule),
   ("hol:INST_TYPE", instTypeRule), ("hol:type-pair", typePairRule)]

/-! ## The extension operations, as rules the owner admits -/

/-- **`new_axiom P`**: `hol:axiom.k`: `⊢ (hol.thm (set) P)`, for a closed term `P` of type
`bool`. -/
def newAxiomRules (k : String) (p : Pat) : List (String × Rule) :=
  [(s!"hol:axiom.{k}", ⟨0, [], thmJ emptyP p⟩)]

/-- **`new_basic_definition (c = t)`**: the constant `c` at the type `ty` of `t` (`hol:const.c`),
and the theorem `⊢ c = t` (`hol:def.c`). -/
def newBasicDefinitionRules (c : String) (ty : HolTy) (t : Pat) : List (String × Rule) :=
  [(s!"hol:const.{c}", newConstantRule c ty),
   (s!"hol:def.{c}", ⟨0, [], thmJ emptyP (eqP ty.closed (constP c ty.closed) t)⟩)]

/-- **`new_basic_type_definition op (abs, rep) (⊢ P x)`**, for `P` closed, `x : rty`, and the
type variables `vs` of `P` in HOL Light's order: the type operator `op` of arity `|vs|`, the
constants `abs : rty → op vs` and `rep : op vs → rty`, and the two theorems
`⊢ abs (rep a) = a` and `⊢ P r = (rep (abs r) = r)`, each resting on the theorem `⊢ P x` as a
premise. -/
def newBasicTypeDefinitionRules (op absName repName : String) (vs : List String) (rty : HolTy)
    (P x : Pat) : List (String × Rule) :=
  let aty : HolTy := .tyapp op (vs.map HolTy.tyvar)
  let absC := constP absName (HolTy.fn rty aty).closed
  let repC := constP repName (HolTy.fn aty rty).closed
  let a := varP (pstr "a") aty.closed
  let r := varP (pstr "r") rty.closed
  let witness : Premise := .judg (thmJ emptyP (combP P x))
  [(s!"hol:ty.{op}", newTypeRule op vs.length),
   (s!"hol:const.{absName}", newConstantRule absName (HolTy.fn rty aty)),
   (s!"hol:const.{repName}", newConstantRule repName (HolTy.fn aty rty)),
   (s!"hol:tydef.{op}.abs-rep", ⟨0, [witness], thmJ emptyP (eqP aty.closed (combP absC (combP repC a)) a)⟩),
   (s!"hol:tydef.{op}.rep-abs", ⟨0, [witness],
      thmJ emptyP (eqP boolP (combP P r) (eqP rty.closed (combP repC (combP absC r)) r))⟩)]

/-- The admissions of a presentation: the judgments, then the rules. -/
def admissions (rs : List (String × Rule)) : List (Admission String) :=
  holJudgments.map (fun x => .judgment x.1 x.2) ++ rs.map fun x => .rule x.1 x.2

end Mettapedia.Logic.TierZero.Adequacy.HOL
