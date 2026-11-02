import Mettapedia.GSLT.Readers.MM0.Load
import Mettapedia.Logic.TierZero.Adequacy.HOLEnc

/-!
# Loading HOL Light's ProofTrace record into kernel version 2

The generated ProofTrace reader turns HOL Light's three files (proof records, theorem records, name
records) into checked record trees. This module is the loading semantics as an executable
definition: it reads the trees into HOL Light's syntax (OpenTheory's `SourceTerm`, the
specification's terms), cuts the record into claims, and prints a kernel-version-2 program over the
presentation `Adequacy.HOL.holRules`. The C program `hol-load` mirrors it and prints the same bytes.

* **Terms.** A record's term `A(v(x)(T))(B)` is `SourceTerm.abs`; it reaches the kernel as
  `encDB (toDB [] t)` (`HOLEnc`), so bound names are gone: `\x. x` and `\y. y` are one kernel term.
* **Claims (cut by owner).** A record is a claim's root when it is named, used by no record, used by
  records of two different claims, or the premise of a type definition; every other record is a node
  of the one claim that uses it. A claim states its root's sequent as HOL Light's theorem record
  writes it, `(hol.thm (set H₁ … Hₙ) C)` with `Hᵢ`, `C` encoded; every hypothesis set a rule asks
  for (`union-of`, `remove-of`, `singleton-of`, `image-of`) is cited from the theorem records too.
* **Sharing.** In a claim each distinct subterm, type, name, set and substitution gets one node or
  one store entry, cited by reference; nothing is unfolded.
* **Admissions.** `holRules`; the profile's signature (`new_type "ind" 0`, `new_constant "@"`,
  as HOL Light's `nums.ml` and `class.ml` declare them; ProofTrace records no signature step);
  `new_axiom` only for a statement of the profile (HOL Light's own statement of its three axioms);
  `new_basic_definition` and `new_basic_type_definition` with HOL Light's conditions checked here
  (a new name, a closed term whose type variables are its constant's, the type definition's laws
  equal to the ones `newBasicTypeDefinitionRules` makes).

Example: bool.ml's record 7 (`⊢ T`, TRUTH) is the claim `hol:r.7` over `hol:def.T`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.HOL.Load

open Mettapedia.GSLT.Readers.Metamath.Load (SX parseSX readItems leafText)
open Mettapedia.GSLT.Readers.MM0.Load (proofChunks)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Logic.TierZero.Adequacy.HOL
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.HOLLight.DefinitionAdapters (sourceOperatorName)

/-! ## Names -/

/-- HOL Light's printer writes a name with OCaml's `String.escaped`; a backslash and a double quote
are the only escapes a name can carry here (the reader admits printable bytes only), e.g. `/\\` is
the conjunction `/\`. Any other escape is refused. -/
def unescape (s : String) : Option String := go s.toList []
where
  go : List Char → List Char → Option String
    | [], acc => some (String.ofList acc.reverse)
    | '\\' :: '\\' :: rest, acc => go rest ('\\' :: acc)
    | '\\' :: '"' :: rest, acc => go rest ('"' :: acc)
    | '\\' :: _, _ => none
    | c :: rest, acc => go rest (c :: acc)

/-! ## The record as HOL Light's syntax -/

/-- One kernel step of the record. -/
inductive PTStep where
  | refl (t : SourceTerm)
  | trans (p q : Nat)
  | mkComb (p q : Nat)
  | abs (p : Nat) (v : SourceTerm)
  | beta (t : SourceTerm)
  | assume (t : SourceTerm)
  | eqMp (p q : Nat)
  | deduct (p q : Nat)
  | inst (p : Nat) (pairs : List (SourceTerm × SourceTerm))
  | instType (p : Nat) (pairs : List (Ty × Ty))
  | newAxiom (t : SourceTerm)
  | newDefinition (t : SourceTerm) (name : String)
  | newTypeDefinition (p : Nat) (t : SourceTerm) (name : String)

/-- A record of one of the three files. -/
inductive PTRecord where
  | proof (id : Nat) (s : PTStep)
  | thm (id : Nat) (hyps : List SourceTerm) (concl : SourceTerm)
  | name (id : Nat) (n : String)

def nameOf (x : SX) : Option String := leafText x >>= unescape

def numOf (x : SX) : Option Nat := leafText x >>= String.toNat?

/-- A type operator of the record as the specification's operator: HOL Light's `fun` is the
specification's `->` (`sourceOperatorName` swaps the two spellings and fixes every other). -/
def opOf (n : String) : TypeOp := .mk (sourceOperatorName (Name.global n)) .undefined

mutual

partial def tyOf : SX → Option Ty
  | .list [.atom "ty_var", n] => (nameOf n).map fun s => .var (Name.global s)
  | .list [.atom "ty_app", n, args] => do
      let s ← nameOf n
      let as ← tyArgsOf args
      pure (.op (opOf s) as)
  | _ => none

partial def tyArgsOf : SX → Option (List Ty)
  | .list [.atom "args_empty"] => some []
  | .list [.atom "args_more", t, rest] => do
      let a ← tyOf t
      let as ← tyArgsOf rest
      pure (a :: as)
  | _ => none

end

partial def tmOf : SX → Option SourceTerm
  | .list [.atom "tm_var", n, ty] => do
      let s ← nameOf n
      let t ← tyOf ty
      pure (.var (Name.global s) t)
  | .list [.atom "tm_const", n, ty] => do
      let s ← nameOf n
      let t ← tyOf ty
      pure (.const (.mk (Name.global s) .undefined) t)
  | .list [.atom "tm_comb", f, x] => do
      let a ← tmOf f
      let b ← tmOf x
      pure (.app a b)
  | .list [.atom "tm_abs", n, ty, body] => do
      let s ← nameOf n
      let t ← tyOf ty
      let b ← tmOf body
      pure (.abs (Name.global s) t b)
  | _ => none

/-- A term inside a JSON string, `(term_quoted " T ")`. -/
def textTm : SX → Option SourceTerm
  | .list [.atom "term_quoted", _, t, _] => tmOf t
  | _ => none

/-- A name inside a JSON string. -/
def textName : SX → Option String
  | .list [.atom "name_quoted", _, n, _] => nameOf n
  | _ => none

def instPairOf : SX → Option (SourceTerm × SourceTerm)
  | .list [.atom "inst_maplet", x, t] => do
      let a ← textTm x
      let b ← textTm t
      pure (a, b)
  | _ => none

partial def instPairsOf : SX → Option (List (SourceTerm × SourceTerm))
  | .list [.atom "inst_none"] => some []
  | .list [.atom "inst_end"] => some []
  | .list [.atom "inst_some", p, rest] => do
      let a ← instPairOf p
      let as ← instPairsOf rest
      pure (a :: as)
  | .list [.atom "inst_next", p, rest] => do
      let a ← instPairOf p
      let as ← instPairsOf rest
      pure (a :: as)
  | _ => none

def typePairOf : SX → Option (Ty × Ty)
  | .list [.atom "instt_maplet", _, a, _, _, t, _] => do
      let x ← tyOf a
      let y ← tyOf t
      pure (x, y)
  | _ => none

partial def typePairsOf : SX → Option (List (Ty × Ty))
  | .list [.atom "instt_none"] => some []
  | .list [.atom "instt_end"] => some []
  | .list [.atom "instt_some", p, rest] => do
      let a ← typePairOf p
      let as ← typePairsOf rest
      pure (a :: as)
  | .list [.atom "instt_next", p, rest] => do
      let a ← typePairOf p
      let as ← typePairsOf rest
      pure (a :: as)
  | _ => none

def stepOf : SX → Option PTStep
  | .list [.atom "step_refl", _, _, t] => (textTm t).map .refl
  | .list [.atom "step_trans", _, _, p, q] => do pure (.trans (← numOf p) (← numOf q))
  | .list [.atom "step_mk_comb", _, _, p, q] => do pure (.mkComb (← numOf p) (← numOf q))
  | .list [.atom "step_abs", _, _, p, v] => do pure (.abs (← numOf p) (← textTm v))
  | .list [.atom "step_beta", _, _, t] => (textTm t).map .beta
  | .list [.atom "step_assume", _, _, t] => (textTm t).map .assume
  | .list [.atom "step_eq_mp", _, _, p, q] => do pure (.eqMp (← numOf p) (← numOf q))
  | .list [.atom "step_deduct", _, _, p, q] => do pure (.deduct (← numOf p) (← numOf q))
  | .list [.atom "step_inst", _, _, p, ps] => do pure (.inst (← numOf p) (← instPairsOf ps))
  | .list [.atom "step_inst_type", _, _, p, ps] => do pure (.instType (← numOf p) (← typePairsOf ps))
  | .list [.atom "step_axiom", _, _, t] => (textTm t).map .newAxiom
  | .list [.atom "step_definition", _, _, t, n] => do pure (.newDefinition (← textTm t) (← textName n))
  | .list [.atom "step_type_definition", _, _, p, t, n] => do
      pure (.newTypeDefinition (← numOf p) (← textTm t) (← textName n))
  | _ => none

partial def hypsOf : SX → Option (List SourceTerm)
  | .list [.atom "hyps_none"] => some []
  | .list [.atom "hyps_end"] => some []
  | .list [.atom "hyps_some", t, rest] => do
      let a ← textTm t
      let as ← hypsOf rest
      pure (a :: as)
  | .list [.atom "hyps_next", t, rest] => do
      let a ← textTm t
      let as ← hypsOf rest
      pure (a :: as)
  | _ => none

def recordOf : SX → Option PTRecord
  | .list [.atom "record_proof", _, _, i, _, _, s] => do pure (.proof (← numOf i) (← stepOf s))
  | .list [.atom "record_theorem", _, _, i, _, _, .list [.atom "sequent_of", _, _, hs, _, _, c]] => do
      pure (.thm (← numOf i) (← hypsOf hs) (← textTm c))
  | .list [.atom "record_name", _, _, i, _, _, n] => do pure (.name (← numOf i) (← textName n))
  | _ => none

/-! ## HOL Light's types with HOL Light's names -/

mutual

/-- A type with HOL Light's spelling of its operators (`fun`, not the specification's `->`). -/
def holTyOf : Ty → HolTy
  | .var n => .tyvar n.component
  | .op op args => .tyapp (opName op) (holTysOf args)

def holTysOf : List Ty → List HolTy
  | [] => []
  | a :: as => holTyOf a :: holTysOf as

end

/-- A type's canonical text (its closed pattern, as the kernel prints it). -/
def holKey (t : HolTy) : String := renderPat t.closed

/-- Match an instance against a generic type, extending `θ` (type variable ↦ type). -/
partial def matchTy (θ : List (String × HolTy)) : HolTy → HolTy → Option (List (String × HolTy))
  | .tyvar a, t => match θ.lookup a with
      | some u => if holKey u == holKey t then some θ else none
      | none => some (θ ++ [(a, t)])
  | .tyapp op as, .tyapp op' bs =>
      if op == op' && as.length == bs.length then
        (as.zip bs).foldlM (fun θ xy => matchTy θ xy.1 xy.2) θ
      else none
  | _, _ => none

/-- The type variables of every annotation of a term, with repetitions. -/
partial def tmTyvars : SourceTerm → List String
  | .var _ ty => (holTyOf ty).tyvarsRaw
  | .const _ ty => (holTyOf ty).tyvarsRaw
  | .app f x => tmTyvars f ++ tmTyvars x
  | .abs _ ty b => (holTyOf ty).tyvarsRaw ++ tmTyvars b

/-- A de Bruijn term without free variables. -/
def dbClosed : DBTerm → Bool
  | .const _ _ => true
  | .free _ => false
  | .bound _ => true
  | .app f x => dbClosed f && dbClosed x
  | .abs _ b => dbClosed b

/-- An injective text of a term with its names, for sharing equal subterms of a claim. -/
partial def srcKey : SourceTerm → String
  | .var n ty => "v(" ++ quoteStr n.component ++ " " ++ holKey (holTyOf ty) ++ ")"
  | .const c ty => "c(" ++ quoteStr (constName c) ++ " " ++ holKey (holTyOf ty) ++ ")"
  | .app f x => "C(" ++ srcKey f ++ " " ++ srcKey x ++ ")"
  | .abs n ty b => "A(" ++ quoteStr n.component ++ " " ++ holKey (holTyOf ty) ++ " " ++ srcKey b ++ ")"

/-! ## Kernel terms of the record -/

mutual

/-- A kernel term as a closed pattern. -/
def patOf : Tm → Pat
  | .idx n => .idx n
  | .node h fs => .node h (patFields fs)

def patFields : Fields Head → TreePatFields Head ℕ
  | .nil => .nil
  | .cons d t rest => .cons d (patOf t) (patFields rest)

end

/-- **The kernel term of a record's term**: `encDB` of its de Bruijn form. -/
def encSrc (t : SourceTerm) : Tm := encDB (t.toDB [])

def patEnc (t : SourceTerm) : Pat := patOf (encSrc t)

/-- A hypothesis set, `(set H₁ … Hₙ)`, in the theorem record's order. -/
def setPatOf (hs : List SourceTerm) : Pat := setP (hs.map patEnc)

/-- **A claim's statement**: the theorem record's sequent, `(hol.thm (set H₁ … Hₙ) C)`. -/
def thmPatOf (hs : List SourceTerm) (c : SourceTerm) : Pat := thmJ (setPatOf hs) (patEnc c)

/-! ## The signature -/

structure HolSig where
  types : Std.HashMap String Nat
  consts : Std.HashMap String HolTy

/-- `(A → bool) → A`, the type of `@`. -/
def selectTy : HolTy := .fn (.fn (.tyvar "A") .bool) (.tyvar "A")

/-- HOL Light's signature steps that ProofTrace does not record: `new_type ("ind", 0)` (`nums.ml`)
and `new_constant ("@", (A → bool) → A)` (`class.ml`). -/
def profileSignature : List (String × Rule) :=
  [("hol:ty.ind", newTypeRule "ind" 0), ("hol:const.@", newConstantRule "@" selectTy)]

def initialSig : HolSig :=
  { types := Std.HashMap.ofList [("bool", 0), ("fun", 2), ("ind", 0)]
    consts := Std.HashMap.ofList
      [("=", .fn (.tyvar "A") (.fn (.tyvar "A") .bool)), ("@", selectTy)] }

/-! ## A claim -/

structure Ctx where
  sig : HolSig
  steps : Array (Option PTStep)
  thms : Array (Option (List SourceTerm × SourceTerm))
  owner : Array (Option Nat)
  admRule : Std.HashMap Nat (String × Option Nat)
  root : Nat

structure CState where
  nodes : Array (Nat × String × List CKid) := #[]
  terms : Array (Nat × Pat) := #[]
  termIds : Std.HashMap String Nat := {}
  tmMemo : Std.HashMap String Nat := {}
  tyMemo : Std.HashMap String Nat := {}
  recMemo : Std.HashMap Nat Nat := {}
  citeMemo : Std.HashMap String Nat := {}
  pairMemo : Std.HashMap String Nat := {}

abbrev CM := ReaderT Ctx (StateT CState (Except String))

instance {α : Type} : Inhabited (CM α) := ⟨fun _ _ => .error "unreachable"⟩

/-- A new node, named by its position from 1. -/
def push (rule : String) (kids : List CKid) : CM Nat := do
  let st ← get
  let n := st.nodes.size + 1
  set { st with nodes := st.nodes.push (n, rule, kids) }
  return n

/-- A store entry, once per distinct term. -/
def termId (p : Pat) : CM Nat := do
  let key := renderPat p
  match (← get).termIds.get? key with
  | some t => return t
  | none =>
      let st ← get
      let t := st.terms.size + 1
      set { st with terms := st.terms.push (t, p), termIds := st.termIds.insert key t }
      return t

/-- A node citing a rule (an admission or another claim), once per rule. -/
def cite (rule : String) (kids : List CKid) : CM Nat := do
  match (← get).citeMemo.get? rule with
  | some n => return n
  | none =>
      let n ← push rule kids
      modify fun st => { st with citeMemo := st.citeMemo.insert rule n }
      return n

/-- The node proving `(hol.ty T)`, once per type. -/
partial def tyNode (t : HolTy) : CM Nat := do
  let key := holKey t
  match (← get).tyMemo.get? key with
  | some n => return n
  | none =>
      let n ← match t with
        | .tyvar a => do
            let tid ← termId (pstr a)
            push "hol:ty.var" [.term tid]
        | .tyapp op args => do
            let ctx ← read
            let some k := ctx.sig.types.get? op | throw s!"undeclared type operator {op}"
            unless k == args.length do throw s!"type operator {op} has arity {k}"
            let ks ← args.mapM tyNode
            push s!"hol:ty.{op}" (ks.map .node)
      modify fun st => { st with tyMemo := st.tyMemo.insert key n }
      return n

/-- The node proving `(hol.tm M T)` for a term of the record, once per distinct term. -/
partial def tmNode (t : SourceTerm) : CM Nat := do
  let key := srcKey t
  match (← get).tmMemo.get? key with
  | some n => return n
  | none =>
      let n ← match t with
        | .var nm ty => do
            let tid ← termId (pstr nm.component)
            let a ← tyNode (holTyOf ty)
            push "hol:tm.var" [.term tid, .node a]
        | .const c ty => do
            let name := constName c
            let ctx ← read
            let some g := ctx.sig.consts.get? name | throw s!"undeclared constant {name}"
            let some θ := matchTy [] g (holTyOf ty)
              | throw s!"the constant {name} at a type that is no instance of its type"
            let ks ← g.tyvars.mapM fun a => match θ.lookup a with
              | some u => tyNode u
              | none => throw s!"the constant {name}: type variable {a} unmatched"
            push s!"hol:const.{name}" (ks.map .node)
        | .app f x => do
            let a ← tmNode f
            let b ← tmNode x
            push "hol:tm.comb" [.node a, .node b]
        | .abs nm ty b => do
            let v ← tmNode (.var nm ty)
            let bb ← tmNode b
            push "hol:tm.abs" [.node v, .node bb]
      modify fun st => { st with tmMemo := st.tmMemo.insert key n }
      return n

def thmOf (q : Nat) : CM (List SourceTerm × SourceTerm) := do
  match (← read).thms[q]? with
  | some (some th) => return th
  | _ => throw s!"theorem record {q} is missing"

/-- The node of a record cited from this claim: built here (this claim's), or a citation of
another claim's root, of an admission, or of a type definition's law over its premise. -/
partial def recNode (r : Nat) : CM Nat := do
  match (← get).recMemo.get? r with
  | some n => return n
  | none =>
      let ctx ← read
      let n ← match ctx.owner[r]? with
        | some (some o) =>
            if o == ctx.root then throw s!"record {r} is used before it is built"
            else if o != r then throw s!"record {r} belongs to the claim of {o}"
            else cite s!"hol:r.{r}" []
        | _ => match ctx.admRule.get? r with
            | some (rule, none) => cite rule []
            | some (rule, some p) => do
                let k ← recNode p
                cite rule [.node k]
            | none => throw s!"record {r} is neither proved nor admitted"
      modify fun st => { st with recMemo := st.recMemo.insert r n }
      return n

def instPairNode (k v : SourceTerm) : CM Nat := do
  let key := srcKey k ++ " " ++ srcKey v
  match (← get).pairMemo.get? key with
  | some m => return m
  | none =>
      let x ← tmNode k
      let y ← tmNode v
      let m ← push "hol:inst-pair" [.node x, .node y]
      modify fun st => { st with pairMemo := st.pairMemo.insert key m }
      return m

def typePairNode (a t : HolTy) : CM Nat := do
  let key := "T " ++ holKey a ++ " " ++ holKey t
  match (← get).pairMemo.get? key with
  | some m => return m
  | none =>
      let x ← tyNode a
      let y ← tyNode t
      let m ← push "hol:type-pair" [.node x, .node y]
      modify fun st => { st with pairMemo := st.pairMemo.insert key m }
      return m

/-- A type variable key of an INST_TYPE pair; HOL Light substitutes type variables only, so a pair
whose key is not one acts as nothing and is left out. -/
def tyvarKey : Ty → Bool
  | .var _ => true
  | _ => false

/-- **One record of this claim as its inference node.** -/
def buildRecord (r : Nat) : CM Unit := do
  let ctx ← read
  let some (some s) := ctx.steps[r]? | throw s!"proof record {r} is missing"
  let (hs, _) ← thmOf r
  let n ← match s with
    | .refl t => do
        let a ← tmNode t
        push "hol:REFL" [.node a]
    | .trans p q => do
        let a ← recNode p
        let b ← recNode q
        let u ← termId (setPatOf hs)
        push "hol:TRANS" [.node a, .node b, .term u]
    | .mkComb p q => do
        let a ← recNode p
        let b ← recNode q
        let u ← termId (setPatOf hs)
        push "hol:MK_COMB" [.node a, .node b, .term u]
    | .abs p v => do
        let a ← recNode p
        let b ← tmNode v
        push "hol:ABS" [.node a, .node b]
    | .beta t => do
        let a ← tmNode t
        push "hol:BETA" [.node a]
    | .assume t => do
        let a ← tmNode t
        let u ← termId (setPatOf hs)
        push "hol:ASSUME" [.node a, .term u]
    | .eqMp p q => do
        let a ← recNode p
        let b ← recNode q
        let u ← termId (setPatOf hs)
        push "hol:EQ_MP" [.node a, .node b, .term u]
    | .deduct p q => do
        let a ← recNode p
        let b ← recNode q
        let (hp, cp) ← thmOf p
        let (hq, cq) ← thmOf q
        let kp := renderPat (patEnc cp)
        let kq := renderPat (patEnc cq)
        let g1 := hp.filter fun h => renderPat (patEnc h) != kq
        let d1 := hq.filter fun h => renderPat (patEnc h) != kp
        let tg ← termId (setPatOf g1)
        let td ← termId (setPatOf d1)
        let tu ← termId (setPatOf hs)
        push "hol:DEDUCT_ANTISYM_RULE" [.node a, .node b, .term tg, .term td, .term tu]
    | .inst p pairs => do
        let a ← recNode p
        let ts ← termId (pex (pairs.map fun kv => pex [patEnc kv.1, patEnc kv.2]))
        let ks ← pairs.mapM fun kv => instPairNode kv.1 kv.2
        let u ← termId (setPatOf hs)
        push "hol:INST" ([.node a, .term ts] ++ ks.map .node ++ [.term u])
    | .instType p pairs => do
        let pairs := pairs.filter fun xt => tyvarKey xt.1
        let a ← recNode p
        let ts ← termId (pex (pairs.map fun xt => pex [patOf (encTy xt.1), patOf (encTy xt.2)]))
        let ks ← pairs.mapM fun xt => typePairNode (holTyOf xt.1) (holTyOf xt.2)
        let u ← termId (setPatOf hs)
        push "hol:INST_TYPE" ([.node a, .term ts] ++ ks.map .node ++ [.term u])
    | _ => throw s!"record {r} is an extension step, not an inference"
  modify fun st => { st with recMemo := st.recMemo.insert r n }

/-- The claim of root `r` over the records it owns (ascending). -/
def buildClaim (owned : List Nat) : CM Unit := owned.forM buildRecord

/-- The claim's messages: the claim with its first 50 nodes, then its later parts as chunks. -/
def claimLines (root : Nat) (concl : Pat) (st : CState) : List String :=
  let rootNode := (st.recMemo.get? root).getD 0
  let nodes := st.nodes.toList.map fun (n, rule, kids) =>
    toString n ++ " " ++ rule ++ " " ++ parens (kids.map CKid.render)
  let chains := proofChunks nodes
  let terms := parens (st.terms.toList.map fun (t, p) => "(t" ++ toString t ++ " " ++ renderPat p ++ ")")
  let id := "hol:r." ++ toString root
  let msg := "(claim " ++ id ++ " " ++ toString rootNode ++ " () () no-prem () () " ++ renderPat concl ++
    " " ++ terms ++ " " ++ chains.headD "no-node" ++ ")"
  ("!(transform &submit () (add-atom &submit " ++ msg ++ "))") ::
    (chains.drop 1).zipIdx.map fun (ch, i) =>
      "!(transform &submit () (add-atom &submit (chunk " ++ id ++ " " ++ toString (i + 1) ++ " " ++ ch ++ ")))"

/-! ## The fold over the record -/

def premisesOf : PTStep → List Nat
  | .trans p q | .mkComb p q | .eqMp p q | .deduct p q => [p, q]
  | .abs p _ | .inst p _ | .instType p _ | .newTypeDefinition p _ _ => [p]
  | _ => []

def isExtension : PTStep → Bool
  | .newAxiom _ | .newDefinition _ _ | .newTypeDefinition _ _ _ => true
  | _ => false

/-- The fold's state for the cut: for each record, the claim of its first user seen, whether users of two
claims cite it, and its claim. -/
structure OwnSt where
  first : Array (Option Nat)
  multi : Array Bool
  own : Array (Option Nat)

/-- A premise `p` cited by a record of the claim `o`: its first user's claim, or two claims' users. -/
def notePremise (o : Nat) (st : OwnSt) (p : Nat) : OwnSt :=
  match st.first[p]? with
  | some none => { st with first := st.first.set! p (some o) }
  | some (some f) => if f != o then { st with multi := st.multi.set! p true } else st
  | none => st

/-- The premises a record cites among the earlier records (a later one is refused by the fold,
`stepRec`, and touches no owner: a record's owner is set before the earlier records are visited). -/
def earlierPremises (s : PTStep) (i : Nat) : List Nat := (premisesOf s).filter (· < i)

/-- One record of the cut, visited from the last: an inference record is a root when it is named, a
type definition's premise, cited by records of two claims, or cited by none; otherwise it belongs to
the claim of its users. -/
def ownStep (steps : Array (Option PTStep)) (named : Nat → Bool) (forced : Array Bool) (st : OwnSt)
    (i : Nat) : OwnSt :=
  match steps[i]? with
  | some (some s) =>
      if isExtension s then st
      else
        let o := if named i || (forced[i]?).getD false || (st.multi[i]?).getD false then i
          else ((st.first[i]?).join).getD i
        (earlierPremises s i).foldl (notePremise o) { st with own := st.own.set! i (some o) }
  | _ => st

/-- The premises of type definitions: claims' roots by force (their laws cite them as rules). -/
def forcedOf (steps : Array (Option PTStep)) : Array Bool :=
  steps.foldl (fun fr s => match s with
    | some (.newTypeDefinition p _ _) => fr.set! p true
    | _ => fr) (Array.replicate steps.size false)

/-- **The cut by owner**: the claim each inference record belongs to (its own index when it is a
root). Records are visited from the last: a record's users come after it. -/
def owners (steps : Array (Option PTStep)) (named : Nat → Bool) : Array (Option Nat) :=
  let n := steps.size
  ((List.range n).reverse.foldl (ownStep steps named (forcedOf steps))
    ⟨Array.replicate n none, Array.replicate n false, Array.replicate n none⟩).own

/-- A claim as the loader made it: its root record, its statement, and its nodes and store. -/
structure ClaimOut where
  root : Nat
  concl : Pat
  cs : CState

/-- A message of the program: an admission, or the `i`-th claim. -/
inductive Msg where
  | admit (a : Admission String)
  | claim (i : Nat)

structure LState where
  sig : HolSig := initialSig
  out : Array Msg := #[]
  claimsOut : Array ClaimOut := #[]
  skip : Bool := false
  admRule : Std.HashMap Nat (String × Option Nat) := {}
  axioms : Std.HashMap String Unit := {}
  admitted : Nat := 0
  claims : Nat := 0
  notes : Array String := #[]
  stopped : Option String := none

def admitRules (st : LState) (rs : List (String × Rule)) : LState :=
  rs.foldl (fun st nr => { st with out := st.out.push (.admit (.rule nr.1 nr.2)), admitted := st.admitted + 1 }) st

def stop (st : LState) (k : Nat) (why : String) : LState :=
  { st with stopped := some ("record " ++ toString k ++ ": " ++ why) }

/-- `c = r` with `c` a constant: `(c, its type, r)`. -/
def defParts : SourceTerm → Option (String × Ty × SourceTerm)
  | .app (.app (.const e _) (.const c ty)) r => if constName e == "=" then some (constName c, ty, r) else none
  | _ => none

/-- `new_basic_definition`: HOL Light's conditions (a new name, a closed well-typed term whose type
variables are its constant's), then `newBasicDefinitionRules`. -/
def defineConst (st : LState) (k : Nat) (t : SourceTerm) (name : String) : LState :=
  match defParts t with
  | none => stop st k "a definition that is not `c = t`"
  | some (c, ty, r) =>
    if c != name then stop st k "the definition's constant is not the record's name"
    else if st.sig.consts.contains c then stop st k s!"the constant {c} is already declared"
    else if !dbClosed (r.toDB []) then stop st k "the defining term is not closed"
    else match r.inferType with
      | none => stop st k "the defining term does not type check"
      | some ty' =>
        if holKey (holTyOf ty') != holKey (holTyOf ty) then stop st k "the constant's type is not the term's"
        else if !((tmTyvars r).all fun a => (holTyOf ty).tyvarsRaw.contains a) then
          stop st k "a type variable of the term is not one of the constant's"
        else
          let st := admitRules st (newBasicDefinitionRules c (holTyOf ty) (patEnc r))
          { st with sig := { st.sig with consts := st.sig.consts.insert c (holTyOf ty) },
                    admRule := st.admRule.insert k ("hol:def." ++ c, none) }

/-- `new_axiom`: admitted only for a statement of the profile, under its name. -/
def admitAxiom (st : LState) (k : Nat) (t : SourceTerm) (profile : List (String × SourceTerm)) :
    LState :=
  let key := renderPat (patEnc t)
  match profile.find? (fun ns => renderPat (patEnc ns.2) == key) with
  | some (nm, _) =>
      let st := if st.axioms.contains nm then st
        else { admitRules st (newAxiomRules nm (patEnc t)) with axioms := st.axioms.insert nm () }
      { st with admRule := st.admRule.insert k ("hol:axiom." ++ nm, none) }
  | none =>
      { st with admRule := st.admRule.insert k ("hol:axiom.unlisted." ++ toString k, none),
                notes := st.notes.push ("record " ++ toString k ++ ": an axiom that is not in the profile; not admitted") }

/-- The variable `a` of the abstraction law `abs (rep a) = a`: its type `op vs`. -/
def absLawType : SourceTerm → Option Ty
  | .app (.app (.const _ _) _) (.var _ aty) => some aty
  | _ => none

def tyvarNames : List Ty → Option (List String)
  | [] => some []
  | .var n :: rest => (tyvarNames rest).map (n.component :: ·)
  | _ => none

/-- `new_basic_type_definition`, for the two records `k` (the abstraction law, named `abs`) and
`k + 1` (the representation law, named `rep`) over the premise `⊢ P x` of record `p`: HOL Light's
conditions, then `newBasicTypeDefinitionRules`, whose laws must be the records' own. -/
def defineType (st : LState) (k p : Nat) (tAbs tRep : SourceTerm) (absName repName : String)
    (thms : Array (Option (List SourceTerm × SourceTerm))) : LState :=
  match thms[p]? with
  | some (some ([], .app P x)) =>
    match absLawType tAbs with
    | some (.op op vsT) =>
      match tyvarNames vsT, x.inferType with
      | some vs, some rty =>
        let opn := opName op
        let sorted := ((tmTyvars P).dedup).mergeSort (fun a b => decide (a ≤ b))
        if st.sig.types.contains opn then stop st k s!"the type {opn} is already declared"
        else if st.sig.consts.contains absName || st.sig.consts.contains repName then
          stop st k "an abstraction or representation name is already declared"
        else if !dbClosed (P.toDB []) then stop st k "the predicate is not closed"
        else if vs != sorted then stop st k "the type's arguments are not the predicate's sorted type variables"
        else
          let rs := newBasicTypeDefinitionRules opn absName repName vs (holTyOf rty) (patEnc P) (patEnc x)
          let concls := rs.map fun nr => renderPat nr.2.concl
          if concls[3]? != some (renderPat (thmJ emptyP (patEnc tAbs))) then
            stop st k "the abstraction law is not new_basic_type_definition's"
          else if concls[4]? != some (renderPat (thmJ emptyP (patEnc tRep))) then
            stop st k "the representation law is not new_basic_type_definition's"
          else
            let aty : HolTy := .tyapp opn (vs.map HolTy.tyvar)
            let st := admitRules st rs
            { st with
              sig := { types := st.sig.types.insert opn vs.length,
                       consts := (st.sig.consts.insert absName (.fn (holTyOf rty) aty)).insert repName
                         (.fn aty (holTyOf rty)) },
              admRule := (st.admRule.insert k ("hol:tydef." ++ opn ++ ".abs-rep", some p)).insert (k + 1)
                ("hol:tydef." ++ opn ++ ".rep-abs", some p) }
      | _, _ => stop st k "the type definition's type or witness does not read"
    | _ => stop st k "the abstraction law does not read"
  | _ => stop st k "the type definition's premise is not a theorem `⊢ P x` without hypotheses"

/-! ## Well-formed claims

A claim the loader emits must be well-formed: its nodes are named `1, 2, …` in order, every child of
the node at position `i` is an earlier node (`1 … i`) or an entry of the claim's store, the store's
ids are `1, 2, …` in order (so each is cited once), and its root record has a node. The loader checks
this of every claim before emitting it (`wfB`); `Load` proves nothing about the partial builders,
it refuses a claim that is not well-formed. -/

/-- A child of the node at position `i` (named `i + 1`): an earlier node or a store entry. -/
def kidOk (i nterms : Nat) : CKid → Bool
  | .node m => 1 ≤ m && m ≤ i
  | .term t => 1 ≤ t && t ≤ nterms
  | _ => false

def nodeOk (nterms : Nat) (x : (Nat × String × List CKid) × Nat) : Bool :=
  x.1.1 == x.2 + 1 && x.1.2.2.all (kidOk x.2 nterms)

def termOk (x : (Nat × Pat) × Nat) : Bool := x.1.1 == x.2 + 1

def rootOk (root : Nat) (cs : CState) : Bool :=
  match cs.recMemo.get? root with
  | some r => 1 ≤ r && r ≤ cs.nodes.size
  | none => false

def wfB (root : Nat) (cs : CState) : Bool :=
  cs.nodes.toList.zipIdx.all (nodeOk cs.terms.size) && cs.terms.toList.zipIdx.all termOk &&
    rootOk root cs

/-- **A well-formed claim.** -/
def WellFormed (root : Nat) (cs : CState) : Prop :=
  (∀ x ∈ cs.nodes.toList.zipIdx, nodeOk cs.terms.size x = true) ∧
    (∀ x ∈ cs.terms.toList.zipIdx, termOk x = true) ∧ rootOk root cs = true

theorem wfB_iff (root : Nat) (cs : CState) : wfB root cs = true ↔ WellFormed root cs := by
  simp [wfB, WellFormed, List.all_eq_true, and_assoc]

/-- What the fold reads: the records, the cut, and each root's records. -/
structure Env where
  steps : Array (Option PTStep)
  thms : Array (Option (List SourceTerm × SourceTerm))
  profile : List (String × SourceTerm)
  own : Array (Option Nat)
  groups : Std.HashMap Nat (Array Nat)

/-- At a claim's root: its claim, if it builds and is well-formed; at another record of a claim:
nothing. -/
def claimStep (env : Env) (st : LState) (k : Nat) : LState :=
  if env.own[k]? == some (some k) then
    match env.thms[k]? with
    | some (some (hs, c)) =>
        let ctx : Ctx :=
          { sig := st.sig, steps := env.steps, thms := env.thms, owner := env.own,
            admRule := st.admRule, root := k }
        match ((buildClaim ((env.groups.getD k #[]).toList)).run ctx).run {} with
        | .ok ((), cs) =>
            if wfB k cs then
              { st with out := st.out.push (.claim st.claimsOut.size),
                        claimsOut := st.claimsOut.push ⟨k, thmPatOf hs c, cs⟩,
                        claims := st.claims + 1 }
            else stop st k "the claim is not well-formed"
        | .error e => stop st k e
    | _ => stop st k "the theorem record is missing"
  else st

/-- The two records of a type definition, `k` (the abstraction law) and `k + 1`. -/
def typeDefStep (env : Env) (st : LState) (k p : Nat) (tAbs : SourceTerm) (absName : String) : LState :=
  match env.steps[k + 1]? with
  | some (some (.newTypeDefinition p' tRep repName)) =>
      if p' != p then stop st k "the two type definition records have different premises"
      else { defineType st k p tAbs tRep absName repName env.thms with skip := true }
  | _ => stop st k "a type definition without its representation law"

/-- **One record of the fold**: its extension rules, or at a claim's root its claim (only a
well-formed one), or nothing (a record of some claim). -/
def stepRec (env : Env) (st : LState) (k : Nat) : LState :=
  if st.stopped.isSome then st
  else if st.skip then { st with skip := false }
  else match env.steps[k]? with
    | some (some s) =>
      if (premisesOf s).any (· ≥ k) then stop st k "a premise that is not an earlier record"
      else match s with
      | .newAxiom t => admitAxiom st k t env.profile
      | .newDefinition t name => defineConst st k t name
      | .newTypeDefinition p tAbs absName => typeDefStep env st k p tAbs absName
      | _ => claimStep env st k
    | _ => stop st k "the proof record is missing"

/-- A judgment's admission. -/
def admitJudgment (st : LState) (jn : String × Nat) : LState :=
  { st with out := st.out.push (.admit (.judgment jn.1 jn.2)), admitted := st.admitted + 1 }

/-- The presentation's admissions and the profile's signature. -/
def initial : LState :=
  admitRules (admitRules (holJudgments.foldl admitJudgment {}) holRules) profileSignature

/-- One record into its owner's group. -/
def groupStep (own : Array (Option Nat)) (g : Std.HashMap Nat (Array Nat)) (i : Nat) :
    Std.HashMap Nat (Array Nat) :=
  match own[i]? with
  | some (some o) => g.insert o ((g.getD o #[]).push i)
  | _ => g

/-- Each root's records, ascending. -/
def groupsOf (own : Array (Option Nat)) : Std.HashMap Nat (Array Nat) :=
  (List.range own.size).foldl (groupStep own) {}

/-- **The program**: the presentation and the profile, then for every record in order its
extension rules or, at a claim's root, its claim. -/
def load (steps : Array (Option PTStep)) (thms : Array (Option (List SourceTerm × SourceTerm)))
    (named : Nat → Bool) (profile : List (String × SourceTerm)) : LState :=
  let own := owners steps named
  let env : Env := { steps, thms, profile, own, groups := groupsOf own }
  (List.range steps.size).foldl (stepRec env) initial

/-- The footer: the accepted claims and the rules on the board. -/
def footer : List String :=
  ["!(size-atom (collapse (transform &theorems (every (read (accepted $x))) $x)))",
   "!(size-atom (collapse (transform &rules (every (read (rule $r $f $p $c))) $r)))",
   "!(sort-atom (collapse (transform &theorems (every (read (accepted $x))) $x)))"]

/-- A message's lines. -/
def msgLines (st : LState) : Msg → List String
  | .admit a => ["!(transform &admit () (add-atom &admit " ++ a.render ++ "))"]
  | .claim i => match st.claimsOut[i]? with
    | some co => claimLines co.root co.concl co.cs
    | none => []

/-- The whole program text. -/
def programText (kernelPath : String) (st : LState) : String :=
  "\n".intercalate (bootSrc kernelPath ++ st.out.toList.flatMap (msgLines st) ++ footer) ++ "\n"

/-! ## From the reader's items -/

/-- The records of an items file, in item order. -/
def recordsOf (items : Std.HashMap Nat SX) : Except String (Array PTRecord) := do
  let mut out : Array PTRecord := #[]
  for i in [0:items.size] do
    match items.get? i with
    | none => throw s!"item {i} is missing"
    | some t => match recordOf t with
      | some r => out := out.push r
      | none => throw s!"item {i} does not read as a record"
  return out

/-- Proof records by number, theorem records by number, the named numbers, the profile. -/
def tables (proofs theorems names profile : Array PTRecord) :
    Except String (Array (Option PTStep) × Array (Option (List SourceTerm × SourceTerm)) ×
      Std.HashMap Nat Unit × List (String × SourceTerm)) := do
  let n := proofs.size
  let mut steps : Array (Option PTStep) := Array.replicate n none
  for r in proofs do
    match r with
    | .proof i s => if i < n then steps := steps.set! i (some s) else throw s!"proof record {i} out of order"
    | _ => throw "a proof file holds a record that is no proof record"
  let mut thms : Array (Option (List SourceTerm × SourceTerm)) := Array.replicate n none
  for r in theorems do
    match r with
    | .thm i hs c => if i < n then thms := thms.set! i (some (hs, c)) else throw s!"theorem record {i} has no proof record"
    | _ => throw "a theorem file holds a record that is no theorem record"
  let mut named : Std.HashMap Nat Unit := {}
  for r in names do
    match r with
    | .name i _ => named := named.insert i ()
    | _ => throw "a names file holds a record that is no name record"
  let mut stmts : Std.HashMap Nat SourceTerm := {}
  let mut pnames : Array (Nat × String) := #[]
  for r in profile do
    match r with
    | .thm i [] c => stmts := stmts.insert i c
    | .thm _ _ _ => throw "a profile axiom with hypotheses"
    | .name i nm => pnames := pnames.push (i, nm)
    | _ => throw "a profile holds a proof record"
  let mut prof : List (String × SourceTerm) := []
  for (i, nm) in pnames.toList do
    match stmts.get? i with
    | some c => prof := prof ++ [(nm, c)]
    | none => throw s!"profile name {nm} has no statement"
  return (steps, thms, named, prof)

end Mettapedia.GSLT.Readers.HOL.Load
