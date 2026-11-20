import Mettapedia.Languages.MeTTa.PeTTa.PatternUnifierByCells

/-!
# Structural data patterns for the full Atom carrier

Expressions are encoded as closed spines; variables and scalar leaves retain
their kinds. A symbol and the one-item expression containing it remain
different. The view primitive's name is a parameter, so interpreting a native
pattern does not globally rename source constructors.

The canonical `cons` instance is related to the existing pattern reading. A
native spelling such as `cons-atom` reaches it through a checked spine decode.
The host's interpretation of that primitive, whole-rule compilation and
administrative execution are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.GSLTDataPatterns

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)
open ListView

mutual
def encode (view : String) : Atom → Atom
  | .var name => .var name
  | .symbol name => .symbol name
  | .grounded value => .grounded value
  | .expression items => encodeItems view items

def encodeItems (view : String) : List Atom → Atom
  | [] => .expression []
  | first :: rest => .expression [.symbol view, encode view first, encodeItems view rest]
end

/-- Read only complete data-pattern spines. A malformed tail is not an empty
tail, and a different primitive name is not silently reinterpreted. -/
def decode (view : String) : Atom → Option Atom
  | .var name => some (.var name)
  | .symbol name => some (.symbol name)
  | .grounded value => some (.grounded value)
  | .expression [] => some (.expression [])
  | .expression [.symbol head, first, rest] =>
      if head = view then do
        let first ← decode view first
        let .expression rest ← decode view rest | none
        return .expression (first :: rest)
      else none
  | .expression _ => none

mutual
theorem decode_encode (view : String) :
    ∀ source : Atom, decode view (encode view source) = some source
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression items => decode_encodeItems view items

theorem decode_encodeItems (view : String) :
    ∀ items : List Atom, decode view (encodeItems view items) = some (.expression items)
  | [] => rfl
  | first :: rest => by
      simp only [encodeItems, decode, decode_encode view first,
        decode_encodeItems view rest]
      rfl
end

theorem encode_injective (view : String) : Function.Injective (encode view) := by
  intro first second same
  have read := congrArg (decode view) same
  simpa only [decode_encode, Option.some.injEq] using read

/-- Every accepted pattern is precisely the encoding of its decoded source. -/
theorem encode_decode (view : String) (pattern : Atom) : ∀ source : Atom,
    decode view pattern = some source → encode view source = pattern := by
  refine (measure (sizeOf : Atom → Nat)).wf.induction
    (C := fun current => ∀ source : Atom,
      decode view current = some source → encode view source = current) pattern ?_
  intro current smaller source read
  cases current with
  | var name => cases read; rfl
  | symbol name => cases read; rfl
  | grounded value => cases read; rfl
  | expression items =>
      cases items with
      | nil => cases read; rfl
      | cons head tail =>
          cases tail with
          | nil => cases head <;> simp [decode] at read
          | cons first tail =>
              cases tail with
              | nil => cases head <;> simp [decode] at read
              | cons rest tail =>
                  cases tail with
                  | cons next others => cases head <;> simp [decode] at read
                  | nil =>
                      cases head with
                      | var name => simp [decode] at read
                      | grounded value => simp [decode] at read
                      | expression nested => simp [decode] at read
                      | symbol name =>
                          by_cases same : name = view
                          · subst name
                            cases one : decode view first with
                            | none => simp [decode, one] at read
                            | some value =>
                                cases others : decode view rest with
                                | none => simp [decode, one, others] at read
                                | some remaining =>
                                    cases remaining with
                                    | var name => simp [decode, one, others] at read
                                    | symbol name => simp [decode, one, others] at read
                                    | grounded value => simp [decode, one, others] at read
                                    | expression values =>
                                        have firstExact := smaller first (by
                                          change sizeOf first < _
                                          simp
                                          omega) value one
                                        have restExact := smaller rest (by
                                          change sizeOf rest < _
                                          simp
                                          omega) (.expression values) others
                                        simp only [decode, one, others] at read
                                        cases read
                                        simpa only [encode, encodeItems, firstExact] using
                                          congrArg (fun tail => Atom.expression [.symbol view, first, tail]) restExact
                          · simp [decode, same] at read

/-- A primitive alias changes only the checked encoding, preserving the
source term's own symbols and scalar kinds. -/
def retarget (fromView toView : String) (pattern : Atom) : Option Atom :=
  (decode fromView pattern).map (encode toView)

theorem retarget_encode (fromView toView : String) (source : Atom) :
    retarget fromView toView (encode fromView source) = some (encode toView source) := by
  simp [retarget, decode_encode]

theorem retarget_reflects (fromView toView : String) {pattern translated : Atom}
    (checked : retarget fromView toView pattern = some translated) :
    ∃ source, encode fromView source = pattern ∧ encode toView source = translated := by
  unfold retarget at checked
  cases read : decode fromView pattern with
  | none => simp [read] at checked
  | some source =>
      refine ⟨source, encode_decode fromView pattern source read, ?_⟩
      simpa [read] using checked

theorem retarget_comp (first middle last : String) (pattern : Atom) :
    (retarget first middle pattern).bind (retarget middle last) =
      retarget first last pattern := by
  unfold retarget
  cases read : decode first pattern with
  | none => rfl
  | some source => simp [decode_encode]

mutual
/-- The ordered variable occurrences are unchanged, including repetitions. -/
theorem freeVars_encode (view : String) : ∀ source : Atom,
    atomFreeVars (encode view source) = atomFreeVars source
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression items => freeVars_encodeItems view items

theorem freeVars_encodeItems (view : String) : ∀ items : List Atom,
    atomFreeVars (encodeItems view items) = atomFreeVars.atomFreeVarsList items
  | [] => rfl
  | first :: rest => by
      simp only [encodeItems, atomFreeVars, atomFreeVars.atomFreeVarsList,
        List.nil_append, List.append_nil, freeVars_encode view first,
        freeVars_encodeItems view rest]
end

mutual
/-- The encoded pattern means the original data, including open values. -/
theorem readPattern_encode : ∀ source : Atom,
    readPattern (encode "cons" source) = spell source
  | .var _ => by simp [encode, spell]
  | .symbol _ => by simp [encode, spell]
  | .grounded _ => by simp [encode, readPattern, spell]
  | .expression items => readPattern_encodeItems items

theorem readPattern_encodeItems : ∀ items : List Atom,
    readPattern (encodeItems "cons" items) = spell.spellItems items
  | [] => by simp [encodeItems, readPattern, readPattern.readItems]
  | first :: rest => by
      rw [encodeItems, readPattern_view, readPattern_encode first,
        readPattern_encodeItems rest, spellItems_cons]
end

/-- Matching the encoding is structural equality after the same source
valuation. Repeated variables share that valuation; values may be open. -/
theorem patternHolds_iff (valuation : Valuation) (pattern value : Atom) :
    PatternHolds valuation (encode "cons" pattern) value ↔
      instantiate valuation pattern = instantiate valuation value := by
  change instantiate (fun name => spell (valuation name))
      (readPattern (encode "cons" pattern)) =
    instantiate (fun name => spell (valuation name)) (spell value) ↔ _
  rw [readPattern_encode, ← spell_instantiate valuation pattern,
    ← spell_instantiate valuation value]
  exact ⟨spell_injective _ _, congrArg spell⟩

theorem native_readback {native source translated : Atom}
    (decoded : decode "cons-atom" native = some source)
    (checked : retarget "cons-atom" "cons" native = some translated) :
    readPattern translated = spell source := by
  have exactOutput : encode "cons" source = translated := by
    simpa only [retarget, decoded, Option.map_some, Option.some.injEq] using checked
  rw [← exactOutput, readPattern_encode]

end Mettapedia.Languages.MeTTa.PeTTa.GSLTDataPatterns
