import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicSchema
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.TheoremDefinitions

/-!
# The Prime `set:` proof language and its native proofs

The candidate's proof checker reads the set signature (propositions, sets,
membership, the set operations and the universe operator), the user's
inductive declarations and definitions, and proofs built from hypotheses,
known facts, implication and universal quantification, retyped along
definitional conversion.  `set:native-proof` compiles a checked proof to a
term of the dependent calculus: the proof family `__cetta_holds_<digest>` of
propositions, with decoding equations for implication and each quantifier
instance, and one constant per assumed fact.

This module is that profile, in the calculus the kernel checks:

* the signature constants and the instance constants `all@A` and `eq@A` of
  the kernel chart, named exactly as the checker names them. An instance name
  is read back to its type (`allInstance?`, `eqInstance?`), so the declarations
  are a computable function of the name;
* the stored equations of `add` and `pow` as declared computation;
* the zero-addition theorem as a proof modulo the equations, with the
  conversion articles the checker decides;
* its compilation, typed at the proof family of its conclusion, closed and
  at an open index;
* the signature's definition `Falsum := ∀p. p` (`falsumEquation`) as the
  checker keeps it. `Falsum` is a declared constant, represented by its name,
  and its definition is the stored rule `Falsum ⟶ all@prop (λp. p)`, which a
  request selects once it mentions `Falsum`. The chart without the rule
  (`signature`) is the chart of every proof that does not mention `Falsum`;
  the chart with it (`definedSignature`) realizes the definition by its δ-step
  (`definedRealization`). Without the rule the definition is not realized,
  although both of its sides are represented
  (`falsumEquation_not_realized_without_rule`);
* ex falso through the definition (`exFalso`), compiled to the checker's term
  `λr. λh. h r` and typed at the proof family of `∀r. Falsum → r` in the chart
  with the rule (`exFalso_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface HOLNativeGenericProofCompiler
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.AlgebraicSchema
  (SchemaTable SchemaFamily)

/-! ## Source vocabulary -/

/-- The base types of the two developments: the signature's sets and the
declared inductive `num`. -/
inductive SetBase where
  | set
  | num
  deriving DecidableEq, Repr

abbrev setTy : HOL.Ty SetBase := .base .set
abbrev numTy : HOL.Ty SetBase := .base .num

/-- The signature constants, and the constants the developments define. -/
inductive SetConst : HOL.Ty SetBase → Type where
  | falsum : SetConst .prop
  | member : SetConst (.arr setTy (.arr setTy .prop))
  | empty : SetConst setTy
  | union : SetConst (.arr setTy setTy)
  | power : SetConst (.arr setTy setTy)
  | separation : SetConst (.arr setTy (.arr (.arr setTy .prop) setTy))
  | replacement : SetConst (.arr setTy (.arr (.arr setTy setTy) setTy))
  | epsilon : SetConst (.arr (.arr setTy .prop) setTy)
  | universeOf : SetConst (.arr setTy setTy)
  | zero : SetConst numTy
  | suc : SetConst (.arr numTy numTy)
  | add : SetConst (.arr numTy (.arr numTy numTy))
  | pow : SetConst (.arr numTy (.arr setTy setTy))

/-! ## Names of the kernel chart -/

def propName : DeclName := .mkSimple "prop"
def impName : DeclName := .mkSimple "imp"

def baseName : SetBase → DeclName
  | .set => .mkSimple "set"
  | .num => .mkSimple "num"

def constantName : {type : HOL.Ty SetBase} → SetConst type → DeclName
  | _, .falsum => .mkSimple "Falsum"
  | _, .member => .mkSimple "In"
  | _, .empty => .mkSimple "Empty"
  | _, .union => .mkSimple "Union"
  | _, .power => .mkSimple "Power"
  | _, .separation => .mkSimple "Sep"
  | _, .replacement => .mkSimple "Repl"
  | _, .epsilon => .mkSimple "Eps_set"
  | _, .universeOf => .mkSimple "UnivOf"
  | _, .zero => .mkSimple "zero"
  | _, .suc => .mkSimple "suc"
  | _, .add => .mkSimple "add"
  | _, .pow => .mkSimple "pow"

/-- The checker's spelling of a simple type, used in instance names such as
`all@(Pi num prop)`. -/
def renderChars : HOL.Ty SetBase → List Char
  | .prop => ['p', 'r', 'o', 'p']
  | .base .set => ['s', 'e', 't']
  | .base .num => ['n', 'u', 'm']
  | .arr domain codomain =>
      ['(', 'P', 'i', ' '] ++ renderChars domain ++ ' ' :: renderChars codomain ++ [')']

/-- The spelling is a prefix code: a rendered type is recovered from any
string it begins. -/
theorem renderChars_append_injective :
    ∀ (first second : HOL.Ty SetBase) (rest rest' : List Char),
      renderChars first ++ rest = renderChars second ++ rest' →
        first = second ∧ rest = rest'
  | .prop, .prop, rest, rest', equal => by simpa [renderChars] using equal
  | .prop, .base .set, _, _, equal => by simp [renderChars] at equal
  | .prop, .base .num, _, _, equal => by simp [renderChars] at equal
  | .prop, .arr _ _, _, _, equal => by simp [renderChars] at equal
  | .base .set, .prop, _, _, equal => by simp [renderChars] at equal
  | .base .set, .base .set, rest, rest', equal => by simpa [renderChars] using equal
  | .base .set, .base .num, _, _, equal => by simp [renderChars] at equal
  | .base .set, .arr _ _, _, _, equal => by simp [renderChars] at equal
  | .base .num, .prop, _, _, equal => by simp [renderChars] at equal
  | .base .num, .base .set, _, _, equal => by simp [renderChars] at equal
  | .base .num, .base .num, rest, rest', equal => by simpa [renderChars] using equal
  | .base .num, .arr _ _, _, _, equal => by simp [renderChars] at equal
  | .arr _ _, .prop, _, _, equal => by simp [renderChars] at equal
  | .arr _ _, .base .set, _, _, equal => by simp [renderChars] at equal
  | .arr _ _, .base .num, _, _, equal => by simp [renderChars] at equal
  | .arr domain codomain, .arr domain' codomain', rest, rest', equal => by
      simp only [renderChars, List.append_assoc, List.cons_append, List.nil_append,
        List.cons.injEq, true_and] at equal
      obtain ⟨sameDomain, tail⟩ := renderChars_append_injective domain domain' _ _ equal
      simp only [List.cons.injEq, true_and] at tail
      obtain ⟨sameCodomain, tail'⟩ := renderChars_append_injective codomain codomain' _ _ tail
      simp only [List.cons.injEq, true_and] at tail'
      exact ⟨by rw [sameDomain, sameCodomain], tail'⟩

theorem renderChars_injective : Function.Injective renderChars := by
  intro first second equal
  exact (renderChars_append_injective first second [] [] (by simpa using equal)).1

/-- `all@A`: the simple instance of the universal quantifier at `A`. -/
def allName (type : HOL.Ty SetBase) : DeclName :=
  .mkSimple (String.ofList (['a', 'l', 'l', '@'] ++ renderChars type))

/-- `eq@A`: the simple instance of equality at `A`. -/
def eqName (type : HOL.Ty SetBase) : DeclName :=
  .mkSimple (String.ofList (['e', 'q', '@'] ++ renderChars type))

theorem mkSimple_injective {first second : String}
    (equal : Lean.Name.mkSimple first = Lean.Name.mkSimple second) : first = second := by
  injection equal

theorem ofList_injective {first second : List Char}
    (equal : String.ofList first = String.ofList second) : first = second := by
  simpa only [String.toList_ofList] using congrArg String.toList equal

/-! ## Reading a rendered type -/

/-- Reads the rendering of a simple type from the front of a character list,
in at most `fuel` nested steps. -/
def readTyAux : Nat → List Char → Option (HOL.Ty SetBase × List Char)
  | 0, _ => none
  | _ + 1, 'p' :: 'r' :: 'o' :: 'p' :: rest => some (.prop, rest)
  | _ + 1, 's' :: 'e' :: 't' :: rest => some (.base .set, rest)
  | _ + 1, 'n' :: 'u' :: 'm' :: rest => some (.base .num, rest)
  | fuel + 1, '(' :: 'P' :: 'i' :: ' ' :: rest =>
      match readTyAux fuel rest with
      | some (domain, ' ' :: rest) =>
          match readTyAux fuel rest with
          | some (codomain, ')' :: rest) => some (.arr domain codomain, rest)
          | _ => none
      | _ => none
  | _ + 1, _ => none

/-- The simple type rendered at the front of a character list, and the
characters after it.  Every step consumes characters, so the length of the
list is enough fuel. -/
def readTy (chars : List Char) : Option (HOL.Ty SetBase × List Char) :=
  readTyAux chars.length chars

theorem readTyAux_renderChars (type : HOL.Ty SetBase) :
    ∀ (fuel : Nat) (rest : List Char), (renderChars type ++ rest).length ≤ fuel →
      readTyAux fuel (renderChars type ++ rest) = some (type, rest) := by
  induction type with
  | prop =>
      intro fuel rest enough
      cases fuel with
      | zero => exact absurd enough (Nat.not_succ_le_zero _)
      | succ fuel => rfl
  | base sort =>
      intro fuel rest enough
      cases fuel with
      | zero => cases sort <;> exact absurd enough (Nat.not_succ_le_zero _)
      | succ fuel => cases sort <;> rfl
  | arr domain codomain domainRead codomainRead =>
      intro fuel rest enough
      have shape : renderChars (.arr domain codomain) ++ rest =
          '(' :: 'P' :: 'i' :: ' ' ::
            (renderChars domain ++ ' ' :: (renderChars codomain ++ ')' :: rest)) := by
        simp only [renderChars, List.append_assoc, List.cons_append, List.nil_append]
      rw [shape] at enough ⊢
      cases fuel with
      | zero => exact absurd enough (Nat.not_succ_le_zero _)
      | succ fuel =>
          have domainFuel :
              (renderChars domain ++ ' ' :: (renderChars codomain ++ ')' :: rest)).length ≤
                fuel :=
            Nat.le_trans ((List.suffix_append ['P', 'i', ' '] _).length_le)
              (Nat.le_of_succ_le_succ enough)
          have codomainFuel : (renderChars codomain ++ ')' :: rest).length ≤ fuel :=
            Nat.le_trans
              (((List.suffix_cons ' ' _).trans (List.suffix_append _ _)).length_le)
              domainFuel
          simp only [readTyAux, domainRead fuel _ domainFuel, codomainRead fuel _ codomainFuel]

/-- The reader recognises every rendered type, whatever follows it. -/
theorem readTy_renderChars (type : HOL.Ty SetBase) (rest : List Char) :
    readTy (renderChars type ++ rest) = some (type, rest) :=
  readTyAux_renderChars type _ rest (Nat.le_refl _)

theorem readTyAux_sound :
    ∀ (fuel : Nat) {chars rest : List Char} {type : HOL.Ty SetBase},
      readTyAux fuel chars = some (type, rest) → chars = renderChars type ++ rest
  | 0, _, _, _, found => by cases found
  | fuel + 1, chars, rest, type, found => by
      unfold readTyAux at found
      split at found
      next => cases found
      next => cases found; rfl
      next => cases found; rfl
      next => cases found; rfl
      next fuel' _ same =>
        obtain rfl : fuel = fuel' := Nat.succ.inj same
        split at found
        next domainRead =>
          split at found
          next codomainRead =>
            cases found
            obtain rfl := readTyAux_sound fuel domainRead
            obtain rfl := readTyAux_sound fuel codomainRead
            simp only [renderChars, List.append_assoc, List.cons_append, List.nil_append]
          next => cases found
        next => cases found
      next => cases found

/-- The reader returns only rendered types, followed by the rest of its input. -/
theorem readTy_sound {chars rest : List Char} {type : HOL.Ty SetBase}
    (found : readTy chars = some (type, rest)) : chars = renderChars type ++ rest :=
  readTyAux_sound _ found

/-! ## Reading a spelling through its bytes -/

/-- The characters of a spelling read one byte of its UTF-8 encoding at a
time.  On an ASCII spelling, such as every name of the profile, this is the
spelling. -/
def byteChars (spelling : String) : List Char :=
  spelling.toByteArray.data.toList.map Char.ofUInt8

theorem byteChars_ofList_append (first second : List Char) :
    byteChars (String.ofList (first ++ second)) =
      byteChars (String.ofList first) ++ byteChars (String.ofList second) := by
  simp only [byteChars, String.toByteArray_ofList, List.utf8Encode,
    List.toList_data_toByteArray, List.flatMap_append, List.map_append]

/-- Rendered types are ASCII. -/
theorem byteChars_renderChars (type : HOL.Ty SetBase) :
    byteChars (String.ofList (renderChars type)) = renderChars type := by
  induction type with
  | prop => rfl
  | base sort => cases sort <;> rfl
  | arr domain codomain domainAscii codomainAscii =>
      have shape : renderChars (.arr domain codomain) =
          ['(', 'P', 'i', ' '] ++ renderChars domain ++ ([' '] ++ renderChars codomain) ++
            [')'] := rfl
      rw [shape, byteChars_ofList_append, byteChars_ofList_append, byteChars_ofList_append,
        byteChars_ofList_append, domainAscii, codomainAscii]
      rfl

/-- A spelling is determined by its byte reading. -/
theorem byteChars_injective : Function.Injective byteChars := by
  intro first second equal
  have bytes : first.toByteArray.data.toList = second.toByteArray.data.toList :=
    (List.map_inj_right fun _ _ same => UInt8.toUInt32_inj.mp (congrArg Char.val same)).mp
      equal
  exact String.toByteArray_inj.mp (ByteArray.ext (Array.ext' bytes))

/-! ## Instance names -/

/-- The simple type `A` of the name spelled `word` followed by the rendering
of `A`, and nothing on any other name. -/
def instanceType? (word : List Char) : DeclName → Option (HOL.Ty SetBase)
  | .str .anonymous spelling =>
      if (byteChars spelling).take word.length = word then
        match readTy ((byteChars spelling).drop word.length) with
        | some (type, []) => some type
        | _ => none
      else none
  | _ => none

/-- The type `A` of the instance name `all@A`, and nothing on any other name. -/
def allInstance? (name : DeclName) : Option (HOL.Ty SetBase) :=
  instanceType? ['a', 'l', 'l', '@'] name

/-- The type `A` of the instance name `eq@A`, and nothing on any other name. -/
def eqInstance? (name : DeclName) : Option (HOL.Ty SetBase) :=
  instanceType? ['e', 'q', '@'] name

theorem byteChars_instance {word : List Char} (ascii : byteChars (String.ofList word) = word)
    (type : HOL.Ty SetBase) :
    byteChars (String.ofList (word ++ renderChars type)) = word ++ renderChars type := by
  rw [byteChars_ofList_append, ascii, byteChars_renderChars]

theorem instanceType?_instance {word : List Char} (ascii : byteChars (String.ofList word) = word)
    (type : HOL.Ty SetBase) :
    instanceType? word (.mkSimple (String.ofList (word ++ renderChars type))) = some type := by
  have whole : readTy (renderChars type) = some (type, []) := by
    simpa only [List.append_nil] using readTy_renderChars type []
  simp only [instanceType?, byteChars_instance ascii, List.take_left, List.drop_left, whole,
    ↓reduceIte]

theorem instanceType?_eq_some {word : List Char} (ascii : byteChars (String.ofList word) = word)
    {name : DeclName} {type : HOL.Ty SetBase} (found : instanceType? word name = some type) :
    name = .mkSimple (String.ofList (word ++ renderChars type)) := by
  cases name with
  | anonymous => cases found
  | num _ _ => cases found
  | str pre spelling =>
      cases pre with
      | str _ _ => cases found
      | num _ _ => cases found
      | anonymous =>
          simp only [instanceType?] at found
          split at found
          next prefixed =>
            split at found
            next read =>
              cases found
              have spelled : byteChars spelling = word ++ renderChars type := by
                rw [← List.take_append_drop word.length (byteChars spelling), prefixed,
                  readTy_sound read, List.append_nil]
              rw [byteChars_injective (spelled.trans (byteChars_instance ascii type).symm)]
            next => cases found
          next => cases found

theorem instanceType?_mkSimple_of_prefix {word : List Char} {spelling : String}
    (different : (byteChars spelling).take word.length ≠ word) :
    instanceType? word (.mkSimple spelling) = none := by
  simp only [instanceType?, if_neg different]

/-! ## The two quantifier prefixes -/

theorem allInstance?_allName (type : HOL.Ty SetBase) : allInstance? (allName type) = some type :=
  instanceType?_instance (by decide) type

theorem allInstance?_eq_some {name : DeclName} {type : HOL.Ty SetBase}
    (found : allInstance? name = some type) : name = allName type :=
  instanceType?_eq_some (by decide) found

/-- `allInstance?` recognises exactly the names `all@A`. -/
theorem allInstance?_eq_some_iff {name : DeclName} {type : HOL.Ty SetBase} :
    allInstance? name = some type ↔ name = allName type :=
  ⟨allInstance?_eq_some, fun equal => equal ▸ allInstance?_allName type⟩

theorem eqInstance?_eqName (type : HOL.Ty SetBase) : eqInstance? (eqName type) = some type :=
  instanceType?_instance (by decide) type

theorem eqInstance?_eq_some {name : DeclName} {type : HOL.Ty SetBase}
    (found : eqInstance? name = some type) : name = eqName type :=
  instanceType?_eq_some (by decide) found

/-- `eqInstance?` recognises exactly the names `eq@A`. -/
theorem eqInstance?_eq_some_iff {name : DeclName} {type : HOL.Ty SetBase} :
    eqInstance? name = some type ↔ name = eqName type :=
  ⟨eqInstance?_eq_some, fun equal => equal ▸ eqInstance?_eqName type⟩

theorem allInstance?_eqName (type : HOL.Ty SetBase) : allInstance? (eqName type) = none := by
  apply instanceType?_mkSimple_of_prefix
  rw [byteChars_instance (by decide) type]
  intro same
  exact absurd (List.cons.inj same).1 (by decide)

theorem eqInstance?_allName (type : HOL.Ty SetBase) : eqInstance? (allName type) = none := by
  apply instanceType?_mkSimple_of_prefix
  rw [byteChars_instance (by decide) type]
  intro same
  exact absurd (List.cons.inj same).1 (by decide)

/-- A simple name whose spelling starts otherwise is no instance of `all`. -/
theorem allInstance?_mkSimple_of_prefix {spelling : String}
    (notAll : (byteChars spelling).take 4 ≠ ['a', 'l', 'l', '@']) :
    allInstance? (.mkSimple spelling) = none :=
  instanceType?_mkSimple_of_prefix notAll

/-- A simple name whose spelling starts otherwise is no instance of `eq`. -/
theorem eqInstance?_mkSimple_of_prefix {spelling : String}
    (notEq : (byteChars spelling).take 3 ≠ ['e', 'q', '@']) :
    eqInstance? (.mkSimple spelling) = none :=
  instanceType?_mkSimple_of_prefix notEq

/-! ## The instance names are distinct -/

theorem allName_injective : Function.Injective allName := by
  intro first second equal
  have read := allInstance?_allName first
  rw [equal, allInstance?_allName] at read
  exact (Option.some.inj read).symm

theorem eqName_injective : Function.Injective eqName := by
  intro first second equal
  have read := eqInstance?_eqName first
  rw [equal, eqInstance?_eqName] at read
  exact (Option.some.inj read).symm

/-- An instance name spells its quantifier before the type. -/
theorem allName_prefix {type : HOL.Ty SetBase} {spelling : String}
    (equal : allName type = .mkSimple spelling) :
    spelling.toList.take 4 = ['a', 'l', 'l', '@'] := by
  rw [← mkSimple_injective equal, String.toList_ofList]
  rfl

theorem eqName_prefix {type : HOL.Ty SetBase} {spelling : String}
    (equal : eqName type = .mkSimple spelling) :
    spelling.toList.take 3 = ['e', 'q', '@'] := by
  rw [← mkSimple_injective equal, String.toList_ofList]
  rfl

/-- A name whose spelling starts otherwise is no quantifier instance. -/
theorem not_allName {spelling : String}
    (different : spelling.toList.take 4 ≠ ['a', 'l', 'l', '@']) :
    ¬ ∃ type, allName type = .mkSimple spelling :=
  fun ⟨_, equal⟩ => different (allName_prefix equal)

theorem not_eqName {spelling : String}
    (different : spelling.toList.take 3 ≠ ['e', 'q', '@']) :
    ¬ ∃ type, eqName type = .mkSimple spelling :=
  fun ⟨_, equal⟩ => different (eqName_prefix equal)

/-- A name the reader does not read as an instance of `all` is no such
instance. -/
theorem allName_ne_of_allInstance? {name : DeclName} (notAll : allInstance? name = none)
    (type : HOL.Ty SetBase) : allName type ≠ name := by
  intro equal
  rw [← equal, allInstance?_allName] at notAll
  cases notAll

/-- A name the reader does not read as an instance of `eq` is no such
instance. -/
theorem eqName_ne_of_eqInstance? {name : DeclName} (notEq : eqInstance? name = none)
    (type : HOL.Ty SetBase) : eqName type ≠ name := by
  intro equal
  rw [← equal, eqInstance?_eqName] at notEq
  cases notEq

theorem allName_ne_eqName (first second : HOL.Ty SetBase) : allName first ≠ eqName second :=
  allName_ne_of_allInstance? (allInstance?_eqName second) first

/-! ## Native declarations -/

def types : TypeInterpretation SetBase where
  proposition := .const propName
  base := fun sort => .const (baseName sort)

/-- The type of `all@A`: `(A → prop) → prop`. -/
def allType (type : HOL.Ty SetBase) : Tower.Tm 0 :=
  typeAt types 0 (.arr (.arr type .prop) .prop)

/-- The type of `eq@A`: `A → A → prop`. -/
def eqType (type : HOL.Ty SetBase) : Tower.Tm 0 :=
  typeAt types 0 (.arr type (.arr type .prop))

/-- The declarations of fixed names: the three universe-level carriers,
implication and every source constant. -/
def fixedEntry (name : DeclName) : Option (Entry Tower.Head) :=
  if name = propName ∨ name = baseName .set ∨ name = baseName .num then
    some { type := sortTm Tower.zero }
  else if name = impName then
    some { type := typeAt types 0 (.arr .prop (.arr .prop .prop)) }
  else if name = constantName .falsum then some { type := typeAt types 0 .prop }
  else if name = constantName .member then
    some { type := typeAt types 0 (.arr setTy (.arr setTy .prop)) }
  else if name = constantName .empty then some { type := typeAt types 0 setTy }
  else if name = constantName .union then some { type := typeAt types 0 (.arr setTy setTy) }
  else if name = constantName .power then some { type := typeAt types 0 (.arr setTy setTy) }
  else if name = constantName .separation then
    some { type := typeAt types 0 (.arr setTy (.arr (.arr setTy .prop) setTy)) }
  else if name = constantName .replacement then
    some { type := typeAt types 0 (.arr setTy (.arr (.arr setTy setTy) setTy)) }
  else if name = constantName .epsilon then
    some { type := typeAt types 0 (.arr (.arr setTy .prop) setTy) }
  else if name = constantName .universeOf then
    some { type := typeAt types 0 (.arr setTy setTy) }
  else if name = constantName .zero then some { type := typeAt types 0 numTy }
  else if name = constantName .suc then some { type := typeAt types 0 (.arr numTy numTy) }
  else if name = constantName .add then
    some { type := typeAt types 0 (.arr numTy (.arr numTy numTy)) }
  else if name = constantName .pow then
    some { type := typeAt types 0 (.arr numTy (.arr setTy setTy)) }
  else none

/-- Every quantifier and equality instance is declared, at its simple type,
which the reader recovers from the instance name; every other name has its
fixed declaration. -/
def entries (name : DeclName) : Option (Entry Tower.Head) :=
  match allInstance? name with
  | some type => some { type := allType type }
  | none =>
      match eqInstance? name with
      | some type => some { type := eqType type }
      | none => fixedEntry name

/-- The stored equations of `add` and `pow`, pattern variables as de Bruijn
indices of the equation telescope. -/
def nativeEquations : SchemaTable Tower.Head :=
  [⟨1, (.app (.app (.const (constantName .add)) (.var 0)) (.const (constantName .zero)),
      .var 0)⟩,
   ⟨2, (.app (.app (.const (constantName .add)) (.var 1))
        (.app (.const (constantName .suc)) (.var 0)),
      .app (.const (constantName .suc))
        (.app (.app (.const (constantName .add)) (.var 1)) (.var 0)))⟩,
   ⟨1, (.app (.app (.const (constantName .pow)) (.const (constantName .zero))) (.var 0),
      .var 0)⟩,
   ⟨2, (.app (.app (.const (constantName .pow)) (.app (.const (constantName .suc)) (.var 1)))
        (.var 0),
      .app (.const (constantName .power))
        (.app (.app (.const (constantName .pow)) (.var 1)) (.var 0)))⟩]

def declarations : Signature Tower.Head where
  entries := entries
  computation := SchemaFamily.computation nativeEquations.family

abbrev rules : Rules Tower.Head := extendRules Tower.rules declarations

theorem lookup_allName (type : HOL.Ty SetBase) :
    rules.constantType (allName type) = some (allType type) := by
  change combinedType Tower.rules declarations (allName type) = _
  simp [combinedType, LevelTower.rules, Signature.typeOf?, declarations, entries,
    allInstance?_allName type]

theorem lookup_eqName (type : HOL.Ty SetBase) :
    rules.constantType (eqName type) = some (eqType type) := by
  change combinedType Tower.rules declarations (eqName type) = _
  simp [combinedType, LevelTower.rules, Signature.typeOf?, declarations, entries,
    allInstance?_eqName type, eqInstance?_eqName type]

/-- A name the reader reads as no instance has its fixed declaration. -/
theorem lookup_fixedName {name : DeclName} (notAll : allInstance? name = none)
    (notEq : eqInstance? name = none) :
    rules.constantType name = (fixedEntry name).map Entry.type := by
  change combinedType Tower.rules declarations name = _
  simp [combinedType, LevelTower.rules, Signature.typeOf?, declarations, entries, notAll, notEq]

theorem lookup_fixed {spelling : String}
    (notAll : spelling.toList.take 4 ≠ ['a', 'l', 'l', '@'])
    (notEq : spelling.toList.take 3 ≠ ['e', 'q', '@']) :
    rules.constantType (.mkSimple spelling) =
      (fixedEntry (.mkSimple spelling)).map Entry.type := by
  refine lookup_fixedName ?_ ?_
  · cases read : allInstance? (.mkSimple spelling) with
    | none => rfl
    | some type => exact absurd ⟨type, (allInstance?_eq_some read).symm⟩ (not_allName notAll)
  · cases read : eqInstance? (.mkSimple spelling) with
    | none => rfl
    | some type => exact absurd ⟨type, (eqInstance?_eq_some read).symm⟩ (not_eqName notEq)

theorem lookup_prop : rules.constantType propName = some (sortTm Tower.zero) :=
  (lookup_fixedName (by decide) (by decide)).trans rfl

theorem lookup_base (sort : SetBase) :
    rules.constantType (baseName sort) = some (sortTm Tower.zero) := by
  cases sort <;> exact (lookup_fixedName (by decide) (by decide)).trans rfl

theorem lookup_imp :
    rules.constantType impName = some (typeAt types 0 (.arr .prop (.arr .prop .prop))) :=
  (lookup_fixedName (by decide) (by decide)).trans rfl

theorem lookup_constant {type : HOL.Ty SetBase} (symbol : SetConst type) :
    rules.constantType (constantName symbol) = some (typeAt types 0 type) := by
  cases symbol <;> exact (lookup_fixedName (by decide) (by decide)).trans rfl

/-! ## Formation -/

theorem sort_formed {n : Nat} {context : Tower.Ctx n} {name : DeclName}
    (lookup : rules.constantType name = some (sortTm Tower.zero)) :
    Typing rules context (.const name) (sortTm Tower.zero) :=
  .const lookup (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

theorem proposition_formed : Typing rules .nil types.proposition (sortTm Tower.zero) :=
  sort_formed lookup_prop

theorem base_formed (sort : SetBase) :
    Typing rules .nil (types.base sort) (sortTm Tower.zero) :=
  sort_formed (lookup_base sort)

theorem simple_formed (type : HOL.Ty SetBase) {n : Nat} (context : Tower.Ctx n) :
    Typing rules context (typeAt types n type) (sortTm Tower.zero) :=
  typeAt_formed_of_atoms declarations types proposition_formed base_formed type context

theorem declared_typed {name : DeclName} {type : HOL.Ty SetBase}
    (lookup : rules.constantType name = some (typeAt types 0 type)) :
    Typing rules .nil (.const name) (typeAt types 0 type) := by
  simpa only [liftClosed, typeAt_rename] using
    (Typing.const (Γ := .nil) lookup (simple_formed type .nil) (.sort Tower.zero))

/-- The native term of each constant of the profile: the constant itself, by its
name in the kernel chart. -/
def constantTerm : {type : HOL.Ty SetBase} → SetConst type → Tower.Tm 0 :=
  fun symbol => .const (constantName symbol)

theorem constantTerm_typed {type : HOL.Ty SetBase} (symbol : SetConst type) :
    Typing rules .nil (constantTerm symbol) (typeAt types 0 type) :=
  declared_typed (lookup_constant symbol)

/-- The profile as a declared logical interface of the generic compiler: every
constant by its name, `Falsum` included. -/
def signature : LogicalSignature SetBase SetConst where
  declarations := declarations
  types := types
  proposition_formed := proposition_formed
  base_formed := base_formed
  constant := constantTerm
  constant_typed := constantTerm_typed
  implication := .const impName
  implication_typed := declared_typed lookup_imp
  universal := fun type => .const (allName type)
  universal_typed := fun type => declared_typed (lookup_allName type)
  equality := fun type => .const (eqName type)
  equality_typed := fun type => declared_typed (lookup_eqName type)

/-- The body of the definition `Falsum := ∀p. p`: `all@prop (λp. p)`. -/
def falsumBody : Tower.Tm 0 := .app (.const (allName .prop)) (.lam (.var 0))

theorem falsumBody_typed : Typing rules .nil falsumBody (typeAt types 0 .prop) :=
  represent_typed signature (gamma := []) (.all (σ := .prop) (.var .vz)) rfl

/-! ## The defining equations and their native realization -/

section Terms

variable {Γ : HOL.Ctx SetBase}

def zeroT : HOL.Term SetConst Γ numTy := .const .zero
def sucT (number : HOL.Term SetConst Γ numTy) : HOL.Term SetConst Γ numTy :=
  .app (.const .suc) number
def addT (left right : HOL.Term SetConst Γ numTy) : HOL.Term SetConst Γ numTy :=
  .app (.app (.const .add) left) right
def powerT (argument : HOL.Term SetConst Γ setTy) : HOL.Term SetConst Γ setTy :=
  .app (.const .power) argument
def powT (count : HOL.Term SetConst Γ numTy) (base : HOL.Term SetConst Γ setTy) :
    HOL.Term SetConst Γ setTy :=
  .app (.app (.const .pow) count) base

end Terms

/-- `add n zero = n`. -/
def addZeroEquation : HOL.DefiningEquation SetConst where
  context := [numTy]
  type := numTy
  left := addT (.var .vz) zeroT
  right := .var .vz

/-- `add n (suc m) = suc (add n m)`, with `m` the newest variable. -/
def addSucEquation : HOL.DefiningEquation SetConst where
  context := [numTy, numTy]
  type := numTy
  left := addT (.var (.vs .vz)) (sucT (.var .vz))
  right := sucT (addT (.var (.vs .vz)) (.var .vz))

/-- `pow zero x = x`. -/
def powZeroEquation : HOL.DefiningEquation SetConst where
  context := [setTy]
  type := setTy
  left := powT zeroT (.var .vz)
  right := .var .vz

/-- `pow (suc n) x = Power (pow n x)`, with `x` the newest variable. -/
def powSucEquation : HOL.DefiningEquation SetConst where
  context := [setTy, numTy]
  type := setTy
  left := powT (sucT (.var (.vs .vz))) (.var .vz)
  right := powerT (powT (.var (.vs .vz)) (.var .vz))

/-- `Falsum = ∀p. p`: the definition of `Falsum` in the signature. -/
def falsumEquation : HOL.DefiningEquation SetConst where
  context := []
  type := .prop
  left := .const .falsum
  right := .all (σ := .prop) (.var .vz)

/-- The equations of `add` and `pow`. -/
def sourceEquations : List (HOL.DefiningEquation SetConst) :=
  [addZeroEquation, addSucEquation, powZeroEquation, powSucEquation]

theorem realization : Modulo.EquationRealization signature sourceEquations := by
  intro equation listed
  simp only [sourceEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · refine ⟨_, _, rfl, rfl, fun substitution => ?_⟩
    exact RootStep.declared (SchemaTable.step_of_mem nativeEquations (by decide) substitution)
  · refine ⟨_, _, rfl, rfl, fun substitution => ?_⟩
    exact RootStep.declared (SchemaTable.step_of_mem nativeEquations (by decide) substitution)
  · refine ⟨_, _, rfl, rfl, fun substitution => ?_⟩
    exact RootStep.declared (SchemaTable.step_of_mem nativeEquations (by decide) substitution)
  · refine ⟨_, _, rfl, rfl, fun substitution => ?_⟩
    exact RootStep.declared (SchemaTable.step_of_mem nativeEquations (by decide) substitution)


/-! ## Proof family and assumed facts

The family name is the checker's, `__cetta_holds_` followed by the digest of
its signature text; each assumed fact becomes one constant of the proof
family at its proposition. -/

def holdsName : DeclName := .mkSimple "__cetta_holds_df87b3cd8ab4b6383b1d0591"

theorem holdsName_fresh : signature.rules.constantType holdsName = none := by
  change rules.constantType _ = none
  rw [lookup_fixedName (name := holdsName) (by decide) (by decide)]
  rfl

/-- `refl@num : ∀ a. a = a`. -/
def reflAxiom : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.eq (.var .vz) (.var .vz))

/-- `subst@num : ∀ P a b. a = b → P a → P b`. -/
def substAxiom : HOL.Formula SetConst [] :=
  .all (σ := .arr numTy .prop) (.all (σ := numTy) (.all (σ := numTy)
    (.imp (.eq (.var (.vs .vz)) (.var .vz))
      (.imp (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz))))))

/-- `num-ind : ∀ P. P zero → (∀ v. P v → P (suc v)) → ∀ x. P x`. -/
def inductionAxiom : HOL.Formula SetConst [] :=
  .all (σ := .arr numTy .prop)
    (.imp (.app (.var .vz) zeroT)
      (.imp (.all (σ := numTy) (.imp (.app (.var (.vs .vz)) (.var .vz))
          (.app (.var (.vs .vz)) (sucT (.var .vz)))))
        (.all (σ := numTy) (.app (.var (.vs .vz)) (.var .vz)))))

/-- The assumptions in the order the checker first uses them. -/
def zeroAddAssumptions : List (HOL.Formula SetConst []) :=
  [inductionAxiom, reflAxiom, substAxiom]

/-- `zero-add : ∀ k. add zero k = k`. -/
def zeroAddStatement : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.eq (addT zeroT (.var .vz)) (.var .vz))

def inductionName : DeclName := .mkSimple "__cetta_proof_edb893c30879ea3547bf6b13"
def reflName : DeclName := .mkSimple "__cetta_proof_3e526d1816b34ee602df380a"
def substName : DeclName := .mkSimple "__cetta_proof_7b7ae677596090a0fb1c398d"

def assumptionNames : Fin 3 → DeclName := ![inductionName, reflName, substName]

/-- The represented assumptions, as the checker's context records them. -/
def inductionCode : Tower.Tm 0 :=
  .app (.const (allName (.arr numTy .prop))) (.lam
    (.app (.app (.const impName) (.app (.var 0) (.const (constantName .zero))))
      (.app (.app (.const impName)
          (.app (.const (allName numTy)) (.lam
            (.app (.app (.const impName) (.app (.var 1) (.var 0)))
              (.app (.var 1) (.app (.const (constantName .suc)) (.var 0)))))))
        (.app (.const (allName numTy)) (.lam (.app (.var 1) (.var 0)))))))

def reflCode : Tower.Tm 0 :=
  .app (.const (allName numTy)) (.lam (.app (.app (.const (eqName numTy)) (.var 0)) (.var 0)))

def substCode : Tower.Tm 0 :=
  .app (.const (allName (.arr numTy .prop))) (.lam
    (.app (.const (allName numTy)) (.lam
      (.app (.const (allName numTy)) (.lam
        (.app (.app (.const impName) (.app (.app (.const (eqName numTy)) (.var 1)) (.var 0)))
          (.app (.app (.const impName) (.app (.var 2) (.var 1))) (.app (.var 2) (.var 0)))))))))

def assumptionCodes : Fin 3 → Tower.Tm 0 := ![inductionCode, reflCode, substCode]

/-- A property of the three assumption indices, checked at each. -/
theorem assumptionIndex_cases {P : Fin 3 → Prop} (at0 : P 0) (at1 : P 1) (at2 : P 2) :
    ∀ index, P index := fun index =>
  Fin.cases (motive := P) at0 (fun i => Fin.cases (motive := fun j => P j.succ) at1
    (fun j => Fin.cases (motive := fun k => P k.succ.succ) at2 (fun k => k.elim0) j) i) index

theorem assumption_represented (index : Fin 3) :
    represent signature (zeroAddAssumptions.get index) = some (assumptionCodes index) :=
  assumptionIndex_cases (P := fun index =>
    represent signature (zeroAddAssumptions.get index) = some (assumptionCodes index))
    rfl rfl rfl index

/-- The assumption constants, each at the proof family of its proposition. -/
def assumptionDeclarations : Signature Tower.Head :=
  Signature.ofList
    [(inductionName, { type := FormationSensitiveHOLGenericProofFamily.proof holdsName inductionCode }),
     (reflName, { type := FormationSensitiveHOLGenericProofFamily.proof holdsName reflCode }),
     (substName, { type := FormationSensitiveHOLGenericProofFamily.proof holdsName substCode })]

/-- The rules the kernel checks the compiled proof in: the profile, the proof
family with its two decoding equations, and the assumption constants. -/
abbrev proofRules : Rules Tower.Head :=
  FormationSensitiveHOLGenericProofFamily.rules signature holdsName

abbrev targetRules : Rules Tower.Head :=
  extendRules proofRules assumptionDeclarations

theorem inductionName_fresh : rules.constantType inductionName = none := by
  rw [lookup_fixedName (name := inductionName) (by decide) (by decide)]
  rfl

theorem reflName_fresh : rules.constantType reflName = none := by
  rw [lookup_fixedName (name := reflName) (by decide) (by decide)]
  rfl

theorem substName_fresh : rules.constantType substName = none := by
  rw [lookup_fixedName (name := substName) (by decide) (by decide)]
  rfl

theorem assumptionName_fresh (index : Fin 3) :
    rules.constantType (assumptionNames index) = none :=
  assumptionIndex_cases (P := fun index => rules.constantType (assumptionNames index) = none)
    inductionName_fresh reflName_fresh substName_fresh index

/-- The checker's native compiler has no equality rules: equality reasoning
reaches it through the assumed facts `refl@A` and `subst@A`. -/
noncomputable def operations : Operations signature holdsName :=
  Operations.logicalOnlyAt signature holdsName holdsName_fresh targetRules
    (includeMorphism proofRules assumptionDeclarations)


/-! ## The zero-addition proof

The checked proof is the expansion of
`(pf:induction num-ind (lam k (eq num (add zero k) k)) (pf:refl num zero)
  (pf:fix k (pf:assume ih (pf:cong num num (lam r (suc r)) (add zero k) k ih))))`:
an instance of `num-ind` at the motive, applied to reflexivity at `zero` and to
the step, whose congruence is `subst@num` at the motive
`λ z. suc (add zero k) = suc z`.  Each place where the checker compares a
synthesized proposition with the expected one by conversion is a retyping
step with its article. -/

section ZeroAdd

variable {Γ : HOL.Ctx SetBase}

/-- `λ k. add zero k = k`. -/
def motive : HOL.Term SetConst Γ (.arr numTy .prop) :=
  .lam (.eq (addT zeroT (.var .vz)) (.var .vz))

/-- `λ z. suc (add zero k) = suc z`, with `k` the newest outer variable. -/
def congruenceMotive : HOL.Term SetConst (numTy :: Γ) (.arr numTy .prop) :=
  .lam (.eq (sucT (addT zeroT (.var (.vs .vz)))) (sucT (.var .vz)))

end ZeroAdd

/-- The instance of a one-variable equation at a term. -/
def singleSubst {Γ : HOL.Ctx SetBase} {σ : HOL.Ty SetBase} (term : HOL.Term SetConst Γ σ) :
    HOL.Subst SetConst [σ] Γ :=
  fun {_} index => match index with
    | .vz => term

/-- The instance of a two-variable equation: the newest variable first. -/
def pairSubst {Γ : HOL.Ctx SetBase} {σ ρ : HOL.Ty SetBase}
    (newest : HOL.Term SetConst Γ σ) (older : HOL.Term SetConst Γ ρ) :
    HOL.Subst SetConst [σ, ρ] Γ :=
  fun {_} index => match index with
    | .vz => newest
    | .vs .vz => older

theorem singleSubst_core {Γ : HOL.Ctx SetBase} {σ : HOL.Ty SetBase}
    {term : HOL.Term SetConst Γ σ} (core : term.isCore = true) :
    ∀ {τ : HOL.Ty SetBase} (index : HOL.Var [σ] τ), (singleSubst term index).isCore = true
  | _, .vz => core

theorem pairSubst_core {Γ : HOL.Ctx SetBase} {σ ρ : HOL.Ty SetBase}
    {newest : HOL.Term SetConst Γ σ} {older : HOL.Term SetConst Γ ρ}
    (newestCore : newest.isCore = true) (olderCore : older.isCore = true) :
    ∀ {τ : HOL.Ty SetBase} (index : HOL.Var [σ, ρ] τ),
      (pairSubst newest older index).isCore = true
  | _, .vz => newestCore
  | _, .vs .vz => olderCore

theorem coreStep {Γ : HOL.Ctx SetBase} {τ : HOL.Ty SetBase}
    {left right : HOL.Term SetConst Γ τ} (step : HOL.SourceStep sourceEquations left right)
    (leftCore : left.isCore = true) (rightCore : right.isCore = true) :
    HOL.CoreConversion sourceEquations left right :=
  .rel _ _ ⟨leftCore, rightCore, step⟩

/-- `refl@num zero` proves `motive zero`: beta, then `add zero zero = zero`. -/
theorem baseArticle :
    HOL.CoreConversion sourceEquations (Γ := []) (.eq zeroT zeroT) (.app motive zeroT) := by
  refine .symm _ _ (.trans _ (.eq (addT zeroT zeroT) zeroT) _ ?_ ?_)
  · exact coreStep (.beta _ _) rfl rfl
  · exact coreStep (.eqLeft _ (.delta addZeroEquation (by simp [sourceEquations])
      (singleSubst zeroT) (singleSubst_core rfl))) rfl rfl

/-- The step hypothesis `motive k` is `add zero k = k`. -/
theorem hypothesisArticle :
    HOL.CoreConversion sourceEquations (Γ := [numTy]) (.app motive (.var .vz))
      (.eq (addT zeroT (.var .vz)) (.var .vz)) :=
  coreStep (.beta _ _) rfl rfl

/-- Reflexivity at `suc (add zero k)` proves the congruence motive at `add zero k`. -/
theorem reflexivityArticle :
    HOL.CoreConversion sourceEquations (Γ := [numTy])
      (.eq (sucT (addT zeroT (.var .vz))) (sucT (addT zeroT (.var .vz))))
      (.app congruenceMotive (addT zeroT (.var .vz))) :=
  .symm _ _ (coreStep (.beta _ _) rfl rfl)

/-- The congruence motive at `k` is `motive (suc k)`: beta on both sides and
`add zero (suc k) = suc (add zero k)`. -/
theorem stepArticle :
    HOL.CoreConversion sourceEquations (Γ := [numTy]) (.app congruenceMotive (.var .vz))
      (.app motive (sucT (.var .vz))) := by
  refine .trans _ (.eq (sucT (addT zeroT (.var .vz))) (sucT (.var .vz))) _
    (coreStep (.beta _ _) rfl rfl) (.symm _ _ ?_)
  refine .trans _ (.eq (addT zeroT (sucT (.var .vz))) (sucT (.var .vz))) _
    (coreStep (.beta _ _) rfl rfl) ?_
  exact coreStep (.eqLeft _ (.delta addSucEquation (by simp [sourceEquations])
    (pairSubst (.var .vz) zeroT) (pairSubst_core rfl rfl))) rfl rfl

/-- The instance of `num-ind` concludes `∀ x. motive x`, which is the theorem. -/
theorem conclusionArticle :
    HOL.CoreConversion sourceEquations (.all (.app motive (.var .vz))) zeroAddStatement :=
  coreStep (.all (.beta _ _)) rfl rfl

/-- The assumed facts, as hypotheses of the theorem. -/
def inductionHypothesis :
    HOL.ProofSyntaxModulo sourceEquations zeroAddAssumptions inductionAxiom :=
  .hyp ⟨0, by decide⟩

def reflHypothesis : HOL.ProofSyntaxModulo sourceEquations zeroAddAssumptions reflAxiom :=
  .hyp ⟨1, by decide⟩

/-- The hypotheses inside the step: the induction hypothesis, then the
weakened facts. -/
abbrev stepAssumptions : List (HOL.Formula SetConst [numTy]) :=
  .app motive (.var .vz) :: HOL.weakenHyps (σ := numTy) zeroAddAssumptions

def stepInductionHypothesis :
    HOL.ProofSyntaxModulo sourceEquations stepAssumptions (.app motive (.var .vz)) :=
  .hyp ⟨0, by decide⟩

def stepReflHypothesis :
    HOL.ProofSyntaxModulo sourceEquations stepAssumptions (HOL.weaken reflAxiom) :=
  .hyp ⟨2, by decide⟩

def stepSubstHypothesis :
    HOL.ProofSyntaxModulo sourceEquations stepAssumptions (HOL.weaken substAxiom) :=
  .hyp ⟨3, by decide⟩

/-- The induction step: `∀ k. motive k → motive (suc k)`. -/
def zeroAddStep :
    HOL.ProofSyntaxModulo sourceEquations stepAssumptions (.app motive (sucT (.var .vz))) :=
  .convert stepArticle
    (.impE
      (.impE
        (.allE (.var .vz) (.allE (addT zeroT (.var .vz))
          (.allE congruenceMotive stepSubstHypothesis)))
        (.convert hypothesisArticle stepInductionHypothesis))
      (.convert reflexivityArticle
        (.allE (sucT (addT zeroT (.var .vz))) stepReflHypothesis)))

/-- The checked proof of `zero-add`, modulo the equations of `add`. -/
def zeroAddProof :
    HOL.ProofSyntaxModulo sourceEquations zeroAddAssumptions zeroAddStatement :=
  .convert conclusionArticle
    (.impE
      (.impE (.allE motive inductionHypothesis)
        (.convert baseArticle (.allE zeroT reflHypothesis)))
      (.allI (.impI zeroAddStep)))

/-! ## Its native proof -/

def zeroAddHypotheses : Fin zeroAddAssumptions.length → Tower.Tm 0 :=
  fun index => .const (assumptionNames index)

def zeroNative {n : Nat} : Tower.Tm n := .const (constantName .zero)
def sucNative {n : Nat} (number : Tower.Tm n) : Tower.Tm n :=
  .app (.const (constantName .suc)) number
def addNative {n : Nat} (left right : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const (constantName .add)) left) right
def eqNumNative {n : Nat} (left right : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const (eqName numTy)) left) right

/-- The term `set:native-proof zero-add` returns, without lambda domains. -/
def zeroAddTerm : Tower.Tm 0 :=
  .app
    (.app
      (.app (.const inductionName) (.lam (eqNumNative (addNative zeroNative (.var 0)) (.var 0))))
      (.app (.const reflName) zeroNative))
    (.lam (.lam
      (.app
        (.app
          (.app
            (.app
              (.app (.const substName)
                (.lam (eqNumNative (sucNative (addNative zeroNative (.var 2)))
                  (sucNative (.var 0)))))
              (addNative zeroNative (.var 1)))
            (.var 1))
          (.var 0))
        (.app (.const reflName) (sucNative (addNative zeroNative (.var 1)))))))

/-- The proposition code of `zero-add`. -/
def zeroAddCode : Tower.Tm 0 :=
  .app (.const (allName numTy)) (.lam (eqNumNative (addNative zeroNative (.var 0)) (.var 0)))

theorem zeroAdd_compiles :
    Modulo.compileModulo signature zeroAddProof Fin.elim0 zeroAddHypotheses =
      some zeroAddTerm := by
  rfl

theorem zeroAdd_represented : represent signature zeroAddStatement = some zeroAddCode := by
  rfl


/-! ## Typing of the native proof -/

theorem subst_elim0 (term : Tower.Tm 0) :
    subst (Fin.elim0 : Sub Tower.Head 0 0) term = term := by
  have emptySub : (Fin.elim0 : Sub Tower.Head 0 0) = ids := by
    funext index
    exact Fin.elim0 index
  rw [emptySub, subst_ids]

theorem liftClosed_zero (term : Tower.Tm 0) : (liftClosed term : Tower.Tm 0) = term := by
  have emptyRen : (Fin.elim0 : Ren 0 0) = idRen := by
    funext index
    exact Fin.elim0 index
  rw [liftClosed, emptyRen, rename_id]

theorem proofRules_lookup_none {name : DeclName} (fresh : rules.constantType name = none)
    (distinct : name ≠ holdsName) : proofRules.constantType name = none := by
  change combinedType signature.rules
    (FormationSensitiveHOLGenericProofFamily.declarations signature holdsName) name = none
  have fresh' : signature.rules.constantType name = none := fresh
  simp [combinedType, fresh', Signature.typeOf?,
    FormationSensitiveHOLGenericProofFamily.declarations, Signature.insert, Signature.empty,
    distinct]

theorem target_lookup (index : Fin 3) :
    targetRules.constantType (assumptionNames index) =
      some (FormationSensitiveHOLGenericProofFamily.proof holdsName (assumptionCodes index)) := by
  have none_ : proofRules.constantType (assumptionNames index) = none :=
    proofRules_lookup_none (assumptionName_fresh index)
      (assumptionIndex_cases (P := fun index => assumptionNames index ≠ holdsName)
        (by decide) (by decide) (by decide) index)
  change combinedType proofRules assumptionDeclarations (assumptionNames index) = _
  rw [combinedType, none_]
  exact assumptionIndex_cases (P := fun index => assumptionDeclarations.typeOf? (assumptionNames index) =
    some (FormationSensitiveHOLGenericProofFamily.proof holdsName (assumptionCodes index)))
    rfl rfl rfl index

theorem assumption_formed (index : Fin 3) :
    Typing targetRules .nil
      (FormationSensitiveHOLGenericProofFamily.proof holdsName (assumptionCodes index))
      (sortTm Tower.zero) := by
  have coded := represent_typed signature (zeroAddAssumptions.get index)
    (assumption_represented index)
  have inProofRules := FormationSensitiveHOLGenericProofFamily.proof_formed signature holdsName
    holdsName_fresh (FormationSensitiveHOLGenericProofFamily.include_typed signature holdsName coded)
  have mapped := inProofRules.mapHead (includeMorphism proofRules assumptionDeclarations)
  simp only [Ctx.mapHead_id, Tm.mapHead_id] at mapped
  exact mapped

/-- Each assumed fact is realized by its constant at its proof family. -/
theorem hypotheses_typed :
    GenericTyping.Hypotheses signature operations (.nil : Tower.Ctx 0) Fin.elim0
      zeroAddHypotheses := by
  intro index
  refine ⟨assumptionCodes index, assumption_represented index, ?_⟩
  rw [subst_elim0]
  have typed := Typing.const (Γ := .nil) (target_lookup index) (assumption_formed index)
    (.sort Tower.zero)
  rw [liftClosed_zero] at typed
  exact typed

/-- The native proof of `zero-add` is checked at the proof family of its
represented conclusion, `∀ k. add zero k = k`. -/
theorem zeroAdd_typed :
    Typing targetRules .nil zeroAddTerm
      (FormationSensitiveHOLGenericProofFamily.proof holdsName zeroAddCode) := by
  obtain ⟨code, represented, typed⟩ :=
    Modulo.compileModulo_typed signature holdsName operations realization zeroAddProof
      (objects := Fin.elim0) (fun index => index.elim0) hypotheses_typed zeroAdd_compiles
  rw [zeroAdd_represented] at represented
  cases represented
  rw [subst_elim0] at typed
  exact typed

/-- Specialized at an open index `n`, the translated proof is evidence for
the represented proposition `add zero n = n`: the proof family of the source
equality, not a native identity. -/
theorem zeroAdd_at_open_index :
    Typing targetRules (.snoc .nil (typeAt types 0 numTy)) (.app (rename wk zeroAddTerm) (.var 0))
      (FormationSensitiveHOLGenericProofFamily.proof holdsName
        (eqNumNative (addNative zeroNative (.var 0)) (.var 0))) := by
  have major := zeroAdd_typed.weaken (extension := typeAt types 0 numTy)
  have body : Typing signature.rules
      (.snoc (.snoc .nil (typeAt types 0 numTy)) (typeAt types 1 numTy))
      (eqNumNative (addNative zeroNative (.var 0)) (.var 0)) (typeAt types 2 .prop) :=
    represent_typed signature (gamma := [numTy, numTy])
      (.eq (addT zeroT (.var .vz)) (.var .vz)) rfl
  have argument : Typing signature.rules (.snoc .nil (typeAt types 0 numTy)) (.var 0)
      (typeAt types 1 numTy) := by
    simpa only [Ctx.lookup_snoc_zero, typeAt_rename] using
      (Typing.var (R := signature.rules) (Γ := .snoc .nil (typeAt types 0 numTy)) 0)
  exact operations.universalElim (simple_formed numTy _) body major argument


/-! ## The definition of `Falsum`

The signature defines `Falsum := ∀p. p`. The checker keeps `Falsum` a declared
constant of `prop` and its definition a stored rule to the body, which a request
selects once it mentions `Falsum`. The chart with the rule extends the chart
without it by the δ-rule of the definition; nothing else changes. -/

/-- The declarations of the profile with the rule of `Falsum`: the same entries,
and the δ-rule `Falsum ⟶ all@prop (λp. p)` beside the equations of `add` and
`pow`. -/
def definedDeclarations : Signature Tower.Head where
  entries := entries
  computation := TypedEquality.Normalization.RootComputation.union declarations.computation
    (TypedEquality.deltaComputation (constantName .falsum) falsumBody)

abbrev definedRules : Rules Tower.Head := extendRules Tower.rules definedDeclarations

/-- The chart with the rule of `Falsum` extends the chart without it. -/
theorem declarations_extends : declarations.Extends definedDeclarations where
  entries := fun same => same
  computation := fun step => .inl step

theorem rules_defined : rules.Morphism definedRules (fun head => head) :=
  extensionMorphism Tower.rules declarations_extends

theorem defined_typed {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing rules context term type) : Typing definedRules context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead rules_defined

/-- The profile with the rule of `Falsum`, as a declared logical interface of the
generic compiler: the symbols of `signature`, `Falsum` by its name. -/
def definedSignature : LogicalSignature SetBase SetConst where
  declarations := definedDeclarations
  types := types
  proposition_formed := defined_typed proposition_formed
  base_formed := fun sort => defined_typed (base_formed sort)
  constant := constantTerm
  constant_typed := fun symbol => defined_typed (constantTerm_typed symbol)
  implication := .const impName
  implication_typed := defined_typed (declared_typed lookup_imp)
  universal := fun type => .const (allName type)
  universal_typed := fun type => defined_typed (declared_typed (lookup_allName type))
  equality := fun type => .const (eqName type)
  equality_typed := fun type => defined_typed (declared_typed (lookup_eqName type))

/-- The δ-step of the definition, in every context. -/
theorem falsum_delta {n : Nat} :
    definedSignature.rules.computation.step (.const (constantName .falsum) : Tower.Tm n)
      (liftClosed falsumBody) :=
  RootStep.declared (.inr ⟨rfl, rfl⟩)

/-- `Falsum` is represented by its name and the body of its definition by
`all@prop (λp. p)`: the two sides are one δ-step apart. -/
theorem falsum_represented :
    represent signature falsumEquation.left = some (.const (constantName .falsum)) ∧
      represent signature falsumEquation.right = some falsumBody :=
  ⟨rfl, rfl⟩

/-- The equations of the profile with `Falsum` defined: the signature's
definition, then the equations of `add` and `pow`. -/
def definedEquations : List (HOL.DefiningEquation SetConst) := falsumEquation :: sourceEquations

theorem sourceEquations_eq : definedEquations = falsumEquation :: sourceEquations := rfl

theorem falsumEquation_mem : falsumEquation ∈ definedEquations := .head _

/-- **The definition of `Falsum` is realized by its δ-step**, and the equations of
`add` and `pow` by their root steps, as without the rule. -/
theorem definedRealization : Modulo.EquationRealization definedSignature definedEquations := by
  intro equation listed
  simp only [definedEquations, sourceEquations, List.mem_cons, List.not_mem_nil,
    or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, _, rfl, rfl, fun (substitution : Sub Tower.Head 0 _) => ?_⟩
    change definedSignature.rules.computation.step (.const (constantName .falsum))
      (subst substitution falsumBody)
    rw [TypedEquality.Normalization.subst_closed substitution falsumBody]
    exact falsum_delta
  · refine ⟨_, _, rfl, rfl, fun substitution => ?_⟩
    exact RootStep.declared
      (.inl (SchemaTable.step_of_mem nativeEquations (by decide) substitution))
  · refine ⟨_, _, rfl, rfl, fun substitution => ?_⟩
    exact RootStep.declared
      (.inl (SchemaTable.step_of_mem nativeEquations (by decide) substitution))
  · refine ⟨_, _, rfl, rfl, fun substitution => ?_⟩
    exact RootStep.declared
      (.inl (SchemaTable.step_of_mem nativeEquations (by decide) substitution))
  · refine ⟨_, _, rfl, rfl, fun substitution => ?_⟩
    exact RootStep.declared
      (.inl (SchemaTable.step_of_mem nativeEquations (by decide) substitution))

/-- The left sides of the equations of `add` and `pow` are applications, at every
instance. -/
theorem nativeEquations_left_app {n : Nat} {left right : Tower.Tm n}
    (step : AlgebraicSchema.SchemaStep nativeEquations.family left right) :
    ∃ function argument, left = .app function argument := by
  cases step with
  | instantiate rule substitution =>
      simp only [SchemaTable.family, nativeEquations, List.mem_cons, List.not_mem_nil,
        or_false] at rule
      rcases rule with same | same | same | same <;> cases same <;> exact ⟨_, _, rfl⟩

/-- **Without the rule, the definition is not realized.** In the chart without
the rule of `Falsum` both sides of the definition are represented, `Falsum` by
its name, but no root step joins them: the δ-rule is what realizes it. -/
theorem falsumEquation_not_realized_without_rule :
    ¬ Modulo.EquationRealization signature [falsumEquation] := by
  intro realized
  obtain ⟨l, r, hl, hr, roots⟩ := realized falsumEquation (List.Mem.head _)
  cases hl
  have step := roots (n := 0) (fun i => Fin.elim0 i)
  change RootStep Tower.rules declarations 0 (.const (constantName .falsum))
    (subst (fun i => Fin.elim0 i) r) at step
  generalize subst (fun i => Fin.elim0 i) r = target at step
  cases step with
  | inherited inherited => exact inherited
  | delta unfolding =>
      rw [show declarations.valueOf? (constantName .falsum) = none from rfl] at unfolding
      cases unfolding
  | declared declared =>
      obtain ⟨_, _, same⟩ := nativeEquations_left_app declared
      cases same

/-! ### Ex falso through the definition -/

/-- `∀r. Falsum → r`. -/
def exFalsoStatement : HOL.Formula SetConst [] :=
  .all (σ := .prop) (.imp (.const .falsum) (.var .vz))

/-- Its code: `all@prop (λr. imp Falsum r)`. -/
def exFalsoCode : Tower.Tm 0 :=
  .app (.const (allName .prop))
    (.lam (.app (.app (.const impName) (.const (constantName .falsum))) (.var 0)))

theorem exFalso_represented : represent definedSignature exFalsoStatement = some exFalsoCode :=
  rfl

/-- The definition of `Falsum`, one step, under a proposition variable. -/
theorem falsumArticle :
    HOL.CoreConversion definedEquations (Γ := [.prop]) (.const .falsum)
      (.all (σ := .prop) (.var .vz)) :=
  .rel _ _ ⟨rfl, rfl, .delta falsumEquation falsumEquation_mem (fun i => nomatch i)
    (fun i => nomatch i)⟩

/-- Ex falso through the definition, as the checker proves `ex-falso`: the
hypothesis `Falsum` is retyped as `∀p. p` by the definition and instantiated at
`r`. -/
def exFalso : HOL.ProofSyntaxModulo definedEquations [] exFalsoStatement :=
  .allI (.impI (.allE (.var .vz) (.convert falsumArticle (.hyp ⟨0, by decide⟩))))

/-- Its native term: `λr. λh. h r`. -/
def exFalsoTerm : Tower.Tm 0 := .lam (.lam (.app (.var 0) (.var 1)))

theorem exFalso_compiles :
    Modulo.compileModulo definedSignature exFalso Fin.elim0 Fin.elim0 = some exFalsoTerm := by
  rfl

theorem definedHoldsName_fresh : definedSignature.rules.constantType holdsName = none :=
  holdsName_fresh

/-- The rules the kernel checks the native proof of ex falso in: the chart with
the rule of `Falsum`, and the proof family with its decoding equations. -/
abbrev definedProofRules : Rules Tower.Head :=
  FormationSensitiveHOLGenericProofFamily.rules definedSignature holdsName

noncomputable def definedOperations : Operations definedSignature holdsName :=
  Operations.logicalOnlyAt definedSignature holdsName definedHoldsName_fresh definedProofRules
    (Rules.Morphism.identity _)

/-- **Ex falso, typed.** The native proof of ex falso is checked at the proof
family of `∀r. Falsum → r` in the chart with the rule of `Falsum`: the
hypothesis at `Holds Falsum` is applied to `r` after the δ-step and the
decoding of the quantifier. -/
theorem exFalso_typed :
    Typing definedProofRules .nil exFalsoTerm
      (FormationSensitiveHOLGenericProofFamily.proof holdsName exFalsoCode) := by
  obtain ⟨code, represented, typed⟩ :=
    Modulo.compileModulo_typed definedSignature holdsName definedOperations definedRealization
      exFalso (objects := Fin.elim0) (fun index => index.elim0) (fun index => index.elim0)
      exFalso_compiles
  rw [exFalso_represented] at represented
  cases represented
  rw [subst_elim0] at typed
  exact typed


#print axioms renderChars_injective
#print axioms allName_injective
#print axioms lookup_allName
#print axioms lookup_eqName
#print axioms realization
#print axioms zeroAdd_compiles
#print axioms zeroAdd_represented
#print axioms hypotheses_typed
#print axioms zeroAdd_typed
#print axioms zeroAdd_at_open_index
#print axioms definedRealization
#print axioms falsumEquation_not_realized_without_rule
#print axioms exFalso_compiles
#print axioms exFalso_typed

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile
