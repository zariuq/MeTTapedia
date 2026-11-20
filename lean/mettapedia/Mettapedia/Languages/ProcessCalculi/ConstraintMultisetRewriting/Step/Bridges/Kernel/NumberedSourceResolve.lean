import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceDeterminism
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceRegistry

/-!
# Total reference queries on numbered source DAGs

Reference queries follow only earlier dependencies and use the actual finite
row decoders. Type annotations use their independent type-index space. The
reference is separate from memoized cache execution and has no search fuel.
Syntax and signature/theorem checking retain their separate roles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceResolve

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NumberedSourceSyntax

def type? (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) (index : Nat) : Option Ty := do
  let raw ← rows index
  typeStep? symbols (fun child => if _before : child < index then type? symbols rows child else none) index raw
termination_by index

def term? (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json) (index : Nat) : Option SourceTerm := do
  let raw ← terms index
  termStep? symbols (type? symbols types)
    (fun child => if _before : child < index then term? symbols types terms child else none) index raw
termination_by index

theorem type_unfold (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) (index : Nat) :
    type? symbols rows index = (do
      let raw ← rows index
      typeStep? symbols (fun child => if child < index then type? symbols rows child else none) index raw) := by
  rw [type?]
  simp only [dite_eq_ite]

theorem term_unfold (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json) (index : Nat) :
    term? symbols types terms index = (do
      let raw ← terms index
      termStep? symbols (type? symbols types)
        (fun child => if child < index then term? symbols types terms child else none) index raw) := by
  rw [term?]
  simp only [dite_eq_ite]

theorem type_sound (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) (index : Nat) (type : Ty)
    (found : type? symbols rows index = some type) : TypeAt symbols rows index type := by
  induction index using Nat.strong_induction_on generalizing type with
  | h index ih =>
      rw [type_unfold] at found
      cases atRow : rows index with
      | none => simp [atRow] at found
      | some raw =>
          have correct : ∀ child value,
              (if child < index then type? symbols rows child else none) = some value →
                TypeAt symbols rows child value := by
            intro child value actual
            by_cases before : child < index
            · apply ih child before value
              simpa only [if_pos before] using actual
            · simp only [if_neg before] at actual
              cases actual
          apply typeStep_sound symbols rows _ correct index raw type atRow
          simpa [atRow] using found

theorem term_sound (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (index : Nat) (term : SourceTerm) (found : term? symbols types terms index = some term) :
    TermAt symbols types terms index term := by
  induction index using Nat.strong_induction_on generalizing term with
  | h index ih =>
      rw [term_unfold] at found
      cases atRow : terms index with
      | none => simp [atRow] at found
      | some raw =>
          have correct : ∀ child value,
              (if child < index then term? symbols types terms child else none) = some value →
                TermAt symbols types terms child value := by
            intro child value actual
            by_cases before : child < index
            · apply ih child before value
              simpa only [if_pos before] using actual
            · simp only [if_neg before] at actual
              cases actual
          apply termStep_sound symbols types terms (type? symbols types) _ (type_sound symbols types) correct
            index raw term atRow
          simpa [atRow] using found

private theorem children_complete (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (known : Nat → Option Ty) (limit : Nat)
    (available : ∀ child, child < limit → ∀ type, TypeAt symbols rows child type → known child = some type)
    (references : List Nat) (arguments : List Ty)
    (read : TypeChildrenAt symbols rows limit references arguments) :
    references? known limit references = some arguments := by
  induction references generalizing arguments with
  | nil => cases read; rfl
  | cons child rest ih =>
      cases read with
      | cons before source later =>
          have first := available child before _ source
          have remaining := ih _ later
          simp [references?, earlier?, before, first, remaining]

theorem typeStep_complete (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (known : Nat → Option Ty) (index : Nat) (raw : Json) (type : Ty)
    (available : ∀ child, child < index → ∀ value, TypeAt symbols rows child value → known child = some value)
    (atRow : rows index = some raw) (read : TypeAt symbols rows index type) :
    typeStep? symbols known index raw = some type := by
  cases read with
  | «variable» original parsed =>
      cases Option.some.inj (original.symm.trans atRow)
      simp [typeStep?, parsed]
  | operation original parsed registered children =>
      cases Option.some.inj (original.symm.trans atRow)
      have decoded := children_complete symbols rows known index available _ _ children
      simp [typeStep?, parsed, registered, decoded]

theorem termStep_complete (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (knownTypes : Nat → Option Ty) (knownTerms : Nat → Option SourceTerm)
    (index : Nat) (raw : Json) (term : SourceTerm)
    (typesAvailable : ∀ child value, TypeAt symbols types child value → knownTypes child = some value)
    (termsAvailable : ∀ child, child < index → ∀ value,
      TermAt symbols types terms child value → knownTerms child = some value)
    (atRow : terms index = some raw) (read : TermAt symbols types terms index term) :
    termStep? symbols knownTypes knownTerms index raw = some term := by
  cases read with
  | «variable» original parsed typed =>
      cases Option.some.inj (original.symm.trans atRow)
      have annotation := typesAvailable _ _ typed
      simp [termStep?, parsed, annotation]
  | constant original parsed registered typed =>
      cases Option.some.inj (original.symm.trans atRow)
      have annotation := typesAvailable _ _ typed
      simp [termStep?, parsed, registered, annotation]
  | application original parsed firstBefore secondBefore left right =>
      cases Option.some.inj (original.symm.trans atRow)
      have first := termsAvailable _ firstBefore _ left
      have second := termsAvailable _ secondBefore _ right
      simp [termStep?, parsed, earlier?, firstBefore, secondBefore, first, second]
  | abstraction original parsed binderBefore bodyBefore binder body =>
      cases Option.some.inj (original.symm.trans atRow)
      have binderValue := termsAvailable _ binderBefore _ binder
      have source := termsAvailable _ bodyBefore _ body
      simp [termStep?, parsed, earlier?, binderBefore, bodyBefore, binderValue, source]

theorem type_complete (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) (index : Nat) (type : Ty)
    (read : TypeAt symbols rows index type) : type? symbols rows index = some type := by
  induction index using Nat.strong_induction_on generalizing type with
  | h index ih =>
      have available : ∀ child, child < index → ∀ value,
          TypeAt symbols rows child value →
            (if child < index then type? symbols rows child else none) = some value := by
        intro child before value source
        simpa only [if_pos before] using ih child before value source
      have rawExists : ∃ raw, rows index = some raw := by
        cases read with
        | «variable» atRow _ => exact ⟨_,atRow⟩
        | operation atRow _ _ _ => exact ⟨_,atRow⟩
      obtain ⟨raw,atRow⟩ := rawExists
      rw [type_unfold, atRow]
      have decoded := typeStep_complete symbols rows _ index raw type available atRow read
      simpa using decoded

theorem term_complete (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (index : Nat) (term : SourceTerm) (read : TermAt symbols types terms index term) :
    term? symbols types terms index = some term := by
  induction index using Nat.strong_induction_on generalizing term with
  | h index ih =>
      have available : ∀ child, child < index → ∀ value,
          TermAt symbols types terms child value →
            (if child < index then term? symbols types terms child else none) = some value := by
        intro child before value source
        simpa only [if_pos before] using ih child before value source
      have rawExists : ∃ raw, terms index = some raw := by
        cases read with
        | «variable» atRow _ _ => exact ⟨_,atRow⟩
        | constant atRow _ _ _ => exact ⟨_,atRow⟩
        | application atRow _ _ _ _ _ => exact ⟨_,atRow⟩
        | abstraction atRow _ _ _ _ _ => exact ⟨_,atRow⟩
      obtain ⟨raw,atRow⟩ := rawExists
      rw [term_unfold, atRow]
      have decoded := termStep_complete symbols types terms (type? symbols types) _ index raw term
        (type_complete symbols types) available atRow read
      simpa using decoded

theorem type_eq_some_iff (symbols : ExportCodec.Symbols) (rows : Nat → Option Json) (index : Nat) (type : Ty) :
    type? symbols rows index = some type ↔ TypeAt symbols rows index type :=
  ⟨type_sound symbols rows index type, type_complete symbols rows index type⟩

theorem term_eq_some_iff (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (index : Nat) (term : SourceTerm) :
    term? symbols types terms index = some term ↔ TermAt symbols types terms index term :=
  ⟨term_sound symbols types terms index term, term_complete symbols types terms index term⟩

theorem type_cache_read_agrees (symbols : ExportCodec.Symbols) (rows : Nat → Option Json)
    (cache : Nat → Option Ty) (correct : TypeCacheCorrect symbols rows cache)
    (index : Nat) (type : Ty) (found : cache index = some type) :
    type? symbols rows index = some type := type_complete symbols rows index type (correct index type found)

theorem term_cache_read_agrees (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (cache : Nat → Option SourceTerm) (correct : TermCacheCorrect symbols types terms cache)
    (index : Nat) (term : SourceTerm) (found : cache index = some term) :
    term? symbols types terms index = some term := term_complete symbols types terms index term (correct index term found)

theorem type_preserved {before after : ExportCodec.Symbols}
    (retained : NumberedSourceRegistry.LookupPreserving before after)
    (rows : Nat → Option Json) (index : Nat) (type : Ty)
    (found : type? before rows index = some type) : type? after rows index = some type :=
  type_complete after rows index type
    (NumberedSourceRegistry.typeAt_transport retained rows index type (type_sound before rows index type found))

theorem term_preserved {before after : ExportCodec.Symbols}
    (retained : NumberedSourceRegistry.LookupPreserving before after)
    (types terms : Nat → Option Json) (index : Nat) (term : SourceTerm)
    (found : term? before types terms index = some term) : term? after types terms index = some term :=
  term_complete after types terms index term
    (NumberedSourceRegistry.termAt_transport retained types terms index term
      (term_sound before types terms index term found))

theorem checked_cached_term_preserved {before after : ExportCodec.Symbols}
    (retained : NumberedSourceRegistry.preserves? before after = true)
    (types terms : Nat → Option Json) (cache : Nat → Option SourceTerm)
    (correct : TermCacheCorrect before types terms cache) (index : Nat) (term : SourceTerm)
    (found : cache index = some term) : term? after types terms index = some term :=
  term_preserved ((NumberedSourceRegistry.preserves?_eq_true_iff _ _).mp retained) types terms index term
    (term_cache_read_agrees before types terms cache correct index term found)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceResolve
