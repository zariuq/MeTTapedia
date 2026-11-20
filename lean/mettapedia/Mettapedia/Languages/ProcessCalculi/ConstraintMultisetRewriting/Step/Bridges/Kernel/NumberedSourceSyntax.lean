import Mettapedia.Languages.HOLLight.ExportCodec
import Mathlib.Data.List.Forall2

/-!
# Certificates for numbered source syntax

The finite row decoders retain source indices, annotations and binder names.
References must point to earlier nodes, and constants resolve through the
supplied provenance-bearing symbol table. A cache licence concerns these
actual rows; it grants no theorem authority or signature-formation result.

The decoders are total. A failed row or reference check is a malformed or
unavailable syntax input, with no search budget involved. Reception of the
literal packet and its command history remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceSyntax

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight

inductive TypeRow where
  | variable (name : String)
  | operation (name : String) (arguments : List Nat)
  deriving DecidableEq, Repr

inductive TermRow where
  | variable (name : String) (annotation : Nat)
  | constant (name : String) (annotation : Nat)
  | application (function argument : Nat)
  | abstraction (binder body : Nat)
  deriving DecidableEq, Repr

def typeRow? (raw : Json) : Option TypeRow := do
  match ← ExportCodec.array? raw with
  | [.str "var", .str name] => pure (.variable name)
  | [.str "op", .str name, .arr arguments] =>
      pure (.operation name (← arguments.toList.mapM ExportCodec.natural?))
  | _ => none

def termRow? (raw : Json) : Option TermRow := do
  match ← ExportCodec.array? raw with
  | [.str "var", .str name, annotation] => pure (.variable name (← ExportCodec.natural? annotation))
  | [.str "const", .str name, annotation] => pure (.constant name (← ExportCodec.natural? annotation))
  | [.str "app", function, argument] =>
      pure (.application (← ExportCodec.natural? function) (← ExportCodec.natural? argument))
  | [.str "abs", binder, body] =>
      pure (.abstraction (← ExportCodec.natural? binder) (← ExportCodec.natural? body))
  | _ => none

def earlier? {A : Type} (known : Nat → Option A) (limit index : Nat) : Option A :=
  if index < limit then known index else none

theorem earlier_some {A : Type} (known : Nat → Option A) (limit index : Nat) (value : A)
    (found : earlier? known limit index = some value) : index < limit ∧ known index = some value := by
  by_cases before : index < limit
  · exact ⟨before, by simpa only [earlier?, if_pos before] using found⟩
  · simp only [earlier?, if_neg before] at found
    cases found

def references? {A : Type} (known : Nat → Option A) (limit : Nat) : List Nat → Option (List A)
  | [] => some []
  | index :: rest => do
      let first ← earlier? known limit index
      let later ← references? known limit rest
      pure (first :: later)

theorem references_sound {A : Type} (known : Nat → Option A) (limit : Nat)
    (relation : Nat → A → Prop) (correct : ∀ index value, known index = some value → relation index value)
    (indices : List Nat) (values : List A) (found : references? known limit indices = some values) :
    List.Forall₂ (fun index value => index < limit ∧ relation index value) indices values := by
  induction indices generalizing values with
  | nil =>
      simp only [references?, Option.some.injEq] at found
      subst values
      exact .nil
  | cons index rest ih =>
      cases head : earlier? known limit index with
      | none => simp [references?, head] at found
      | some first =>
          cases tail : references? known limit rest with
          | none => simp [references?, head, tail] at found
          | some later =>
              simp [references?, head, tail] at found
              subst values
              have actual := earlier_some known limit index first head
              exact .cons ⟨actual.1, correct index first actual.2⟩ (ih later tail)

mutual
inductive TypeAt (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) : Nat → Ty → Prop where
  | variable {index : Nat} {raw : Json} {name : String}
      (atRow : rows index = some raw) (parsed : typeRow? raw = some (.variable name)) :
      TypeAt symbols rows index (.var (.global name))
  | operation {index : Nat} {raw : Json} {name : String} {operator : TypeOp}
      {references : List Nat} {arguments : List Ty}
      (atRow : rows index = some raw) (parsed : typeRow? raw = some (.operation name references))
      (registered : List.lookup name symbols.operators = some operator)
      (children : TypeChildrenAt symbols rows index references arguments) :
      TypeAt symbols rows index (.op operator arguments)

inductive TypeChildrenAt (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) :
    Nat → List Nat → List Ty → Prop where
  | nil {limit : Nat} : TypeChildrenAt symbols rows limit [] []
  | cons {limit child : Nat} {type : Ty} {references : List Nat} {arguments : List Ty}
      (before : child < limit) (read : TypeAt symbols rows child type)
      (rest : TypeChildrenAt symbols rows limit references arguments) :
      TypeChildrenAt symbols rows limit (child :: references) (type :: arguments)
end

theorem TypeChildrenAt.of_forall₂ (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (limit : Nat) {references : List Nat} {arguments : List Ty}
    (reads : List.Forall₂ (fun child argument => child < limit ∧ TypeAt symbols rows child argument)
      references arguments) : TypeChildrenAt symbols rows limit references arguments := by
  induction reads with
  | nil => exact .nil
  | cons first _ ih => exact .cons first.1 first.2 ih

inductive TermAt (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json) : Nat → SourceTerm → Prop where
  | variable {index annotation : Nat} {raw : Json} {name : String} {type : Ty}
      (atRow : terms index = some raw) (parsed : termRow? raw = some (.variable name annotation))
      (typed : TypeAt symbols types annotation type) : TermAt symbols types terms index (.var (.global name) type)
  | constant {index annotation : Nat} {raw : Json} {name : String} {constant : Const} {type : Ty}
      (atRow : terms index = some raw) (parsed : termRow? raw = some (.constant name annotation))
      (registered : List.lookup name symbols.constants = some constant)
      (typed : TypeAt symbols types annotation type) : TermAt symbols types terms index (.const constant type)
  | application {index function argument : Nat} {raw : Json} {left right : SourceTerm}
      (atRow : terms index = some raw) (parsed : termRow? raw = some (.application function argument))
      (functionBefore : function < index) (argumentBefore : argument < index)
      (leftRead : TermAt symbols types terms function left) (rightRead : TermAt symbols types terms argument right) :
      TermAt symbols types terms index (.app left right)
  | abstraction {index binder body : Nat} {raw : Json} {name : Mettapedia.Languages.OpenTheory.Name} {type : Ty} {term : SourceTerm}
      (atRow : terms index = some raw) (parsed : termRow? raw = some (.abstraction binder body))
      (binderBefore : binder < index) (bodyBefore : body < index)
      (binderRead : TermAt symbols types terms binder (.var name type))
      (bodyRead : TermAt symbols types terms body term) :
      TermAt symbols types terms index (.abs name type term)

def typeStep? (symbols : ExportCodec.Symbols) (known : Nat → Option Ty)
    (index : Nat) (raw : Json) : Option Ty := do
  match ← typeRow? raw with
  | .variable name => pure (.var (.global name))
  | .operation name arguments =>
      pure (.op (← List.lookup name symbols.operators) (← references? known index arguments))

def termStep? (symbols : ExportCodec.Symbols) (types : Nat → Option Ty) (known : Nat → Option SourceTerm)
    (index : Nat) (raw : Json) : Option SourceTerm := do
  match ← termRow? raw with
  | .variable name annotation => pure (.var (.global name) (← types annotation))
  | .constant name annotation => pure (.const (← List.lookup name symbols.constants) (← types annotation))
  | .application function argument =>
      pure (.app (← earlier? known index function) (← earlier? known index argument))
  | .abstraction binder body =>
      match ← earlier? known index binder with
      | .var name type => pure (.abs name type (← earlier? known index body))
      | _ => none

theorem typeStep_sound (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (known : Nat → Option Ty) (correct : ∀ index type, known index = some type → TypeAt symbols rows index type)
    (index : Nat) (raw : Json) (type : Ty) (atRow : rows index = some raw)
    (found : typeStep? symbols known index raw = some type) : TypeAt symbols rows index type := by
  cases parsed : typeRow? raw with
  | none => simp [typeStep?, parsed] at found
  | some row =>
      cases row with
      | «variable» name =>
          simp [typeStep?, parsed] at found
          subst type
          exact .variable atRow parsed
      | operation name arguments =>
          cases registered : List.lookup name symbols.operators with
          | none => simp [typeStep?, parsed, registered] at found
          | some operator =>
              cases children : references? known index arguments with
              | none => simp [typeStep?, parsed, registered, children] at found
              | some values =>
                  simp [typeStep?, parsed, registered, children] at found
                  subst type
                  exact .operation atRow parsed registered
                    (TypeChildrenAt.of_forall₂ symbols rows index
                      (references_sound known index _ correct arguments values children))

theorem termStep_sound (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (knownTypes : Nat → Option Ty) (knownTerms : Nat → Option SourceTerm)
    (typeCorrect : ∀ index type, knownTypes index = some type → TypeAt symbols types index type)
    (termCorrect : ∀ index term, knownTerms index = some term → TermAt symbols types terms index term)
    (index : Nat) (raw : Json) (term : SourceTerm) (atRow : terms index = some raw)
    (found : termStep? symbols knownTypes knownTerms index raw = some term) : TermAt symbols types terms index term := by
  cases parsed : termRow? raw with
  | none => simp [termStep?, parsed] at found
  | some row =>
      cases row with
      | «variable» name annotation =>
          cases typed : knownTypes annotation with
          | none => simp [termStep?, parsed, typed] at found
          | some type =>
              simp [termStep?, parsed, typed] at found
              subst term
              exact .variable atRow parsed (typeCorrect annotation type typed)
      | constant name annotation =>
          cases registered : List.lookup name symbols.constants with
          | none => simp [termStep?, parsed, registered] at found
          | some constant =>
              cases typed : knownTypes annotation with
              | none => simp [termStep?, parsed, registered, typed] at found
              | some type =>
                  simp [termStep?, parsed, registered, typed] at found
                  subst term
                  exact .constant atRow parsed registered (typeCorrect annotation type typed)
      | application function argument =>
          cases left : earlier? knownTerms index function with
          | none => simp [termStep?, parsed, left] at found
          | some first =>
              cases right : earlier? knownTerms index argument with
              | none => simp [termStep?, parsed, left, right] at found
              | some second =>
                  simp [termStep?, parsed, left, right] at found
                  subst term
                  have firstRead := earlier_some knownTerms index function first left
                  have secondRead := earlier_some knownTerms index argument second right
                  exact .application atRow parsed firstRead.1 secondRead.1
                    (termCorrect function first firstRead.2) (termCorrect argument second secondRead.2)
      | abstraction binder body =>
          cases binderFound : earlier? knownTerms index binder with
          | none => simp [termStep?, parsed, binderFound] at found
          | some value =>
              cases value with
              | const constant type => simp [termStep?, parsed, binderFound] at found
              | app function argument => simp [termStep?, parsed, binderFound] at found
              | abs name type term => simp [termStep?, parsed, binderFound] at found
              | var name type =>
                  cases bodyFound : earlier? knownTerms index body with
                  | none => simp [termStep?, parsed, binderFound, bodyFound] at found
                  | some bodyTerm =>
                      simp [termStep?, parsed, binderFound, bodyFound] at found
                      subst term
                      have binderRead := earlier_some knownTerms index binder (.var name type) binderFound
                      have bodyRead := earlier_some knownTerms index body bodyTerm bodyFound
                      exact .abstraction atRow parsed binderRead.1 bodyRead.1
                        (termCorrect binder (.var name type) binderRead.2) (termCorrect body bodyTerm bodyRead.2)

def insert {A : Type} (known : Nat → Option A) (index : Nat) (value : A) : Nat → Option A :=
  fun query => if query = index then some value else known query

theorem insert_sound {A : Type} (relation : Nat → A → Prop) (known : Nat → Option A)
    (correct : ∀ index value, known index = some value → relation index value)
    (index : Nat) (value : A) (read : relation index value) :
    ∀ query result, insert known index value query = some result → relation query result := by
  intro query result found
  by_cases same : query = index
  · subst query
    simp [insert] at found
    exact found ▸ read
  · exact correct query result (by simpa only [insert, if_neg same] using found)

def TypeCacheCorrect (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (known : Nat → Option Ty) : Prop :=
  ∀ index type, known index = some type → TypeAt symbols rows index type

def TermCacheCorrect (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (known : Nat → Option SourceTerm) : Prop :=
  ∀ index term, known index = some term → TermAt symbols types terms index term

def appendType? (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (known : Nat → Option Ty) (index : Nat) : Option (Nat → Option Ty) := do
  let raw ← rows index
  pure (insert known index (← typeStep? symbols known index raw))

def appendTerm? (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (types : Nat → Option Ty) (known : Nat → Option SourceTerm) (index : Nat) :
    Option (Nat → Option SourceTerm) := do
  let raw ← rows index
  pure (insert known index (← termStep? symbols types known index raw))

theorem appendType_sound (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (known after : Nat → Option Ty) (correct : TypeCacheCorrect symbols rows known)
    (index : Nat) (found : appendType? symbols rows known index = some after) :
    TypeCacheCorrect symbols rows after := by
  cases atRow : rows index with
  | none => simp [appendType?, atRow] at found
  | some raw =>
      cases decoded : typeStep? symbols known index raw with
      | none => simp [appendType?, atRow, decoded] at found
      | some type =>
          simp [appendType?, atRow, decoded] at found
          subst after
          exact insert_sound _ known correct index type
            (typeStep_sound symbols rows known correct index raw type atRow decoded)

theorem appendTerm_sound (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (knownTypes : Nat → Option Ty) (known after : Nat → Option SourceTerm)
    (typesCorrect : TypeCacheCorrect symbols types knownTypes)
    (correct : TermCacheCorrect symbols types terms known) (index : Nat)
    (found : appendTerm? symbols terms knownTypes known index = some after) :
    TermCacheCorrect symbols types terms after := by
  cases atRow : terms index with
  | none => simp [appendTerm?, atRow] at found
  | some raw =>
      cases decoded : termStep? symbols knownTypes known index raw with
      | none => simp [appendTerm?, atRow, decoded] at found
      | some term =>
          simp [appendTerm?, atRow, decoded] at found
          subst after
          exact insert_sound _ known correct index term
            (termStep_sound symbols types terms knownTypes known typesCorrect correct index raw term atRow decoded)

def types? (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) :
    (Nat → Option Ty) → List Nat → Option (Nat → Option Ty)
  | known, [] => some known
  | known, index :: rest => do
      let after ← appendType? symbols rows known index
      types? symbols rows after rest

def terms? (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) (types : Nat → Option Ty) :
    (Nat → Option SourceTerm) → List Nat → Option (Nat → Option SourceTerm)
  | known, [] => some known
  | known, index :: rest => do
      let after ← appendTerm? symbols rows types known index
      terms? symbols rows types after rest

theorem types_sound (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (indices : List Nat) (known after : Nat → Option Ty) (correct : TypeCacheCorrect symbols rows known)
    (found : types? symbols rows known indices = some after) : TypeCacheCorrect symbols rows after := by
  induction indices generalizing known with
  | nil =>
      simp only [types?, Option.some.injEq] at found
      exact found ▸ correct
  | cons index rest ih =>
      cases appended : appendType? symbols rows known index with
      | none => simp [types?, appended] at found
      | some next =>
          apply ih next (appendType_sound symbols rows known next correct index appended)
          simpa [types?, appended] using found

theorem terms_sound (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (knownTypes : Nat → Option Ty) (typeCorrect : TypeCacheCorrect symbols types knownTypes)
    (indices : List Nat) (known after : Nat → Option SourceTerm)
    (correct : TermCacheCorrect symbols types terms known)
    (found : terms? symbols terms knownTypes known indices = some after) :
    TermCacheCorrect symbols types terms after := by
  induction indices generalizing known with
  | nil =>
      simp only [terms?, Option.some.injEq] at found
      exact found ▸ correct
  | cons index rest ih =>
      cases appended : appendTerm? symbols terms knownTypes known index with
      | none => simp [terms?, appended] at found
      | some next =>
          apply ih next (appendTerm_sound symbols types terms knownTypes known next typeCorrect correct index appended)
          simpa [terms?, appended] using found

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceSyntax
