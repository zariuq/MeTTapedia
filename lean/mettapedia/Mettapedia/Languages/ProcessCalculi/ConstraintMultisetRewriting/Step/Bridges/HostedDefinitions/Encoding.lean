import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Elaboration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.NativeSubstitution

/-!
# Native scoped terms represented as literal hosted data

The constructor and scalar tags are the existing native Pattern codec's tags.
A tagged node is a tuple whose first element is its symbol. Variables are
numeric data in this representation; hosted metavariable substitution does not
implement substitution of the represented object variables.

Decoding first reads this literal constructor tree and then invokes the
existing scope-checking native decoder. The complete native grammar is kept,
including type formers and terms beneath binders. Raw annotated lambdas use a
distinct tag, so a written domain is never silently discarded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration

def nodeC (tag : String) (children : List MClosed) : MClosed := ctuple (csym tag :: children)
def nodeD (tag : String) (children : List MData) : MData := tuple (sym tag :: children)

private def patternData : Pattern → MClosed
  | .apply tag children => nodeC tag (children.map patternData)
  | _ => csym ""

private theorem patternData_apply (tag : String) (children : List Pattern) :
    patternData (.apply tag children) = nodeC tag (children.map patternData) := by
  rw [patternData]

private inductive ConstructorTree : Pattern → Prop where
  | node (tag : String) (children : List Pattern)
      (all : ∀ child ∈ children, ConstructorTree child) : ConstructorTree (.apply tag children)

mutual

/-- Read a literal tagged tree, refusing a binder, variable or untagged datum. -/
def readPatternAt {context : Ctx MSig} {sort : Unit}
    (datum : Term MSig context sort) (closed : context = []) : Option Pattern :=
  match datum with
  | .op (.tup _) arguments => readNodeAt arguments closed
  | _ => none

def readNodeAt {arity : List (List Unit × Unit)} {context : Ctx MSig}
    (arguments : Args MSig arity context) (closed : context = []) : Option Pattern :=
  match arguments with
  | .nil => none
  | .cons (bs := bound) first rest =>
      if bound = [] then
        match first with
        | .op (.sym tag) _ => Pattern.apply tag <$> readPatternArgsAt rest closed
        | _ => none
      else none

def readPatternArgsAt {arity : List (List Unit × Unit)} {context : Ctx MSig}
    (arguments : Args MSig arity context) (closed : context = []) : Option (List Pattern) :=
  match arguments with
  | .nil => some []
  | .cons (bs := bound) first rest =>
      if empty : bound = [] then do
        return (← readPatternAt first (by subst empty; exact closed)) ::
          (← readPatternArgsAt rest closed)
      else none

end

abbrev readPattern (datum : MClosed) : Option Pattern := readPatternAt datum rfl
abbrev readPatternArgs {arity : List (List Unit × Unit)} (arguments : Args MSig arity []) :
    Option (List Pattern) := readPatternArgsAt arguments rfl

private theorem readPatternArgs_encoded (children : List Pattern)
    (read : ∀ child ∈ children, readPattern (patternData child) = some child) :
    readPatternArgs (ctupleArgs (children.map patternData)) = some children := by
  induction children with
  | nil => rfl
  | cons first rest ih =>
      change (do
        return (← readPattern (patternData first)) ::
          (← readPatternArgs (ctupleArgs (rest.map patternData)))) = some (first :: rest)
      rw [read first List.mem_cons_self,
        ih (fun child member => read child (List.mem_cons_of_mem first member))]
      rfl

private theorem readPattern_patternData {pattern : Pattern} (tree : ConstructorTree pattern) :
    readPattern (patternData pattern) = some pattern := by
  induction tree with
  | node tag children _ ih =>
      rw [patternData_apply]
      change Pattern.apply tag <$> readPatternArgs (ctupleArgs (children.map patternData)) = _
      rw [readPatternArgs_encoded children ih]
      rfl

private theorem constructor_nil (tag : String) : ConstructorTree (.apply tag []) :=
  .node tag [] (fun _ absent => False.elim (List.not_mem_nil absent))

private theorem constructor_one (tag : String) {a : Pattern} (ha : ConstructorTree a) :
    ConstructorTree (.apply tag [a]) :=
  .node tag [a] (fun _ member => (List.mem_singleton.mp member) ▸ ha)

private theorem constructor_two (tag : String) {a b : Pattern}
    (ha : ConstructorTree a) (hb : ConstructorTree b) : ConstructorTree (.apply tag [a, b]) := by
  refine .node tag [a, b] ?_
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact ha
  · exact (List.mem_singleton.mp member) ▸ hb

private theorem constructor_three (tag : String) {a b c : Pattern}
    (ha : ConstructorTree a) (hb : ConstructorTree b) (hc : ConstructorTree c) :
    ConstructorTree (.apply tag [a, b, c]) := by
  refine .node tag [a, b, c] ?_
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact ha
  · rcases List.mem_cons.mp member with rfl | member
    · exact hb
    · exact (List.mem_singleton.mp member) ▸ hc

private theorem nat_tree (number : Nat) : ConstructorTree (PatternCodec.encodeNat number) := by
  induction number with
  | zero => exact constructor_nil _
  | succ _ ih => exact constructor_one _ ih

private theorem chars_tree (characters : List Char) : ConstructorTree (PatternCodec.encodeChars characters) := by
  induction characters with
  | nil => exact constructor_nil _
  | cons character rest ih => exact constructor_two _ (nat_tree character.toNat) ih

private theorem name_tree (name : DeclName) : ConstructorTree (PatternCodec.encodeDeclName name) := by
  induction name with
  | anonymous => exact constructor_nil _
  | str pre component ih => exact constructor_two _ ih (chars_tree component.toList)
  | num pre component ih => exact constructor_two _ ih (nat_tree component)

private theorem level_tree (level : Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat) :
    ConstructorTree (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec.encodeLevel level) := by
  induction level with
  | const number => exact constructor_one _ (nat_tree number)
  | param index => exact constructor_one _ (nat_tree index)
  | succ _ ih => exact constructor_one _ ih
  | max _ _ ihLeft ihRight => exact constructor_two _ ihLeft ihRight

private theorem head_tree (head : Tower.Head) :
    ConstructorTree (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec.encodeTowerHead head) := by
  cases head with
  | legacyGround => exact constructor_nil _
  | sort level => exact constructor_one _ (level_tree level)

abbrev headCodec := Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec.towerHeadCodec

private theorem term_tree {n : Nat} (term : Tower.Tm n) :
    ConstructorTree (PatternCodec.encodeTm headCodec term) := by
  induction term with
  | var index => exact constructor_one _ (nat_tree index.val)
  | const name => exact constructor_one _ (name_tree name)
  | head head => exact constructor_one _ (head_tree head)
  | pi _ _ ihA ihB => exact constructor_two _ ihA ihB
  | sigma _ _ ihA ihB => exact constructor_two _ ihA ihB
  | id _ _ _ ihA iha ihb => exact constructor_three _ ihA iha ihb
  | lam _ ih => exact constructor_one _ ih
  | app _ _ ihF ihA => exact constructor_two _ ihF ihA
  | pair _ _ ihA ihB => exact constructor_two _ ihA ihB
  | fst _ ih => exact constructor_one _ ih
  | snd _ ih => exact constructor_one _ ih
  | refl _ ih => exact constructor_one _ ih

def encodeNat (number : Nat) : MClosed := patternData (PatternCodec.encodeNat number)
def encodeName (name : DeclName) : MClosed := patternData (PatternCodec.encodeDeclName name)
def encodeHead (head : Tower.Head) : MClosed := patternData (headCodec.encode head)

def encodeTm {n : Nat} (term : Tower.Tm n) : MClosed :=
  patternData (PatternCodec.encodeTm headCodec term)

def decodeTm (n : Nat) (datum : MClosed) : Option (Tower.Tm n) := do
  PatternCodec.decodeTm? headCodec n (← readPattern datum)

@[simp] theorem encodeNat_zero : encodeNat 0 = nodeC "prime-nat-zero" [] := patternData_apply _ _
@[simp] theorem encodeNat_succ (number : Nat) :
    encodeNat (number + 1) = nodeC "prime-nat-succ" [encodeNat number] := patternData_apply _ _

@[simp] theorem encodeTm_var {n : Nat} (index : Fin n) :
    encodeTm (.var index : Tower.Tm n) = nodeC "prime-tm-var" [encodeNat index.val] := patternData_apply _ _
@[simp] theorem encodeTm_const {n : Nat} (name : DeclName) :
    encodeTm (.const name : Tower.Tm n) = nodeC "prime-tm-const" [encodeName name] := patternData_apply _ _
@[simp] theorem encodeTm_head {n : Nat} (head : Tower.Head) :
    encodeTm (.head head : Tower.Tm n) = nodeC "prime-tm-head" [encodeHead head] := patternData_apply _ _
@[simp] theorem encodeTm_pi {n : Nat} (domain : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    encodeTm (.pi domain body) = nodeC "prime-tm-pi" [encodeTm domain, encodeTm body] := patternData_apply _ _
@[simp] theorem encodeTm_sigma {n : Nat} (domain : Tower.Tm n) (body : Tower.Tm (n + 1)) :
    encodeTm (.sigma domain body) = nodeC "prime-tm-sigma" [encodeTm domain, encodeTm body] := patternData_apply _ _
@[simp] theorem encodeTm_id {n : Nat} (carrier left right : Tower.Tm n) :
    encodeTm (.id carrier left right) = nodeC "prime-tm-id" [encodeTm carrier, encodeTm left, encodeTm right] := patternData_apply _ _
@[simp] theorem encodeTm_lam {n : Nat} (body : Tower.Tm (n + 1)) :
    encodeTm (.lam body) = nodeC "prime-tm-lam" [encodeTm body] := patternData_apply _ _
@[simp] theorem encodeTm_app {n : Nat} (function argument : Tower.Tm n) :
    encodeTm (.app function argument) = nodeC "prime-tm-app" [encodeTm function, encodeTm argument] := patternData_apply _ _
@[simp] theorem encodeTm_pair {n : Nat} (first second : Tower.Tm n) :
    encodeTm (.pair first second) = nodeC "prime-tm-pair" [encodeTm first, encodeTm second] := patternData_apply _ _
@[simp] theorem encodeTm_fst {n : Nat} (pair : Tower.Tm n) :
    encodeTm (.fst pair) = nodeC "prime-tm-fst" [encodeTm pair] := patternData_apply _ _
@[simp] theorem encodeTm_snd {n : Nat} (pair : Tower.Tm n) :
    encodeTm (.snd pair) = nodeC "prime-tm-snd" [encodeTm pair] := patternData_apply _ _
@[simp] theorem encodeTm_refl {n : Nat} (subject : Tower.Tm n) :
    encodeTm (.refl subject) = nodeC "prime-tm-refl" [encodeTm subject] := patternData_apply _ _

@[simp] theorem readPattern_encodeTm {n : Nat} (term : Tower.Tm n) :
    readPattern (encodeTm term) = some (PatternCodec.encodeTm headCodec term) :=
  readPattern_patternData (term_tree term)

@[simp] theorem decodeTm_encodeTm {n : Nat} (term : Tower.Tm n) :
    decodeTm n (encodeTm term) = some term := by
  simp only [decodeTm, readPattern_encodeTm, Bind.bind, Option.bind,
    PatternCodec.decodeTm?_encodeTm]

theorem encodeTm_injective {n : Nat} : Function.Injective (@encodeTm n) := by
  intro first second same
  have decoded := congrArg (decodeTm n) same
  simpa only [decodeTm_encodeTm, Option.some.injEq] using decoded

def rawTm {n : Nat} (term : Tower.Tm n) : NativeSyntax.Raw Tower.Head :=
  NativeSyntax.encode (ATm.ofTm term)

def quoteRaw : NativeSyntax.Raw Tower.Head → MClosed
  | .var index => nodeC "prime-tm-var" [encodeNat index]
  | .const name => nodeC "prime-tm-const" [encodeName name]
  | .head head => nodeC "prime-tm-head" [encodeHead head]
  | .pi domain body => nodeC "prime-tm-pi" [quoteRaw domain, quoteRaw body]
  | .sigma domain body => nodeC "prime-tm-sigma" [quoteRaw domain, quoteRaw body]
  | .id carrier left right => nodeC "prime-tm-id" [quoteRaw carrier, quoteRaw left, quoteRaw right]
  | .lamBare body => nodeC "prime-tm-lam" [quoteRaw body]
  | .lamTyped domain body => nodeC "prime-tm-lam-typed" [quoteRaw domain, quoteRaw body]
  | .app function argument => nodeC "prime-tm-app" [quoteRaw function, quoteRaw argument]
  | .pair first second => nodeC "prime-tm-pair" [quoteRaw first, quoteRaw second]
  | .fst pair => nodeC "prime-tm-fst" [quoteRaw pair]
  | .snd pair => nodeC "prime-tm-snd" [quoteRaw pair]
  | .refl subject => nodeC "prime-tm-refl" [quoteRaw subject]

@[simp] theorem quoteRaw_rawTm {n : Nat} (term : Tower.Tm n) : quoteRaw (rawTm term) = encodeTm term := by
  induction term <;> simp_all only [rawTm, ATm.ofTm, NativeSyntax.encode, quoteRaw,
    encodeTm_var, encodeTm_const, encodeTm_head, encodeTm_pi, encodeTm_sigma, encodeTm_id,
    encodeTm_lam, encodeTm_app, encodeTm_pair, encodeTm_fst, encodeTm_snd, encodeTm_refl]

theorem rawTm_injective {n : Nat} : Function.Injective (@rawTm n) := by
  intro first second same
  apply encodeTm_injective
  simpa only [quoteRaw_rawTm] using congrArg quoteRaw same

theorem malformed_index_refused :
    decodeTm 0 (nodeC "prime-tm-var" [encodeNat 0]) = none := by
  rw [← encodeTm_var (⟨0, by decide⟩ : Fin 1)]
  simp only [decodeTm, readPattern_encodeTm, Bind.bind, Option.bind]
  rfl

theorem typed_lambda_is_not_erased :
    decodeTm 0 (quoteRaw (.lamTyped (.const .anonymous) (.var 0))) = none := by
  change decodeTm 0 (nodeC "prime-tm-lam-typed"
    [nodeC "prime-tm-const" [encodeName .anonymous], nodeC "prime-tm-var" [encodeNat 0]]) = none
  rw [← encodeTm_const (n := 0) .anonymous, ← encodeTm_var (⟨0, by decide⟩ : Fin 1)]
  have read := readPattern_patternData
    (constructor_two "prime-tm-lam-typed" (term_tree (.const .anonymous : Tower.Tm 0))
      (term_tree (.var ⟨0, by decide⟩ : Tower.Tm 1)))
  rw [patternData_apply] at read
  change readPattern (nodeC "prime-tm-lam-typed"
    [encodeTm (.const .anonymous : Tower.Tm 0), encodeTm (.var ⟨0, by decide⟩ : Tower.Tm 1)]) = _ at read
  simp only [decodeTm, read, Bind.bind, Option.bind]
  rfl

theorem capture_sensitive_terms_distinct :
    encodeTm (.lam (.var 0) : Tower.Tm 1) ≠ encodeTm (.lam (.var 1) : Tower.Tm 1) := by
  intro same
  have equal := encodeTm_injective same
  cases equal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
