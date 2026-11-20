import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceDeterminism

/-!
# Numbered JSON envelopes and their source-node readback

The envelope reader checks the same identifier and body positions used by
the retained source reader. Prefixes compose at their actual next identifier;
rows, order and multiplicity are retained. The result joins a licensed source
cache to the original numbered JSON record, rather than merely to its body.
It does not establish file-byte identity or accept a source proof command.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceInput

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NumberedSourceSyntax

def identifier? (raw : Json) : Option Nat :=
  (ExportCodec.at? raw 0).bind ExportCodec.natural?

def numberedRow? (expected : Nat) (raw : Json) : Option Json :=
  if identifier? raw = some expected then ExportCodec.at? raw 1 else none

theorem numberedRow_eq_some_iff (expected : Nat) (raw body : Json) :
    numberedRow? expected raw = some body ↔
      identifier? raw = some expected ∧ ExportCodec.at? raw 1 = some body := by
  by_cases same : identifier? raw = some expected <;> simp [numberedRow?, same]

def numberedRows? : Nat → List Json → Option (List Json)
  | _, [] => some []
  | expected, raw :: rest => do
      let body ← numberedRow? expected raw
      let later ← numberedRows? (expected+1) rest
      pure (body :: later)

inductive NumberedAt : Nat → List Json → List Json → Prop where
  | nil {expected : Nat} : NumberedAt expected [] []
  | cons {expected : Nat} {raw body : Json} {rest bodies : List Json}
      (number : identifier? raw = some expected) (value : ExportCodec.at? raw 1 = some body)
      (later : NumberedAt (expected+1) rest bodies) :
      NumberedAt expected (raw :: rest) (body :: bodies)

theorem numberedRows_eq_some_iff (expected : Nat) (raw bodies : List Json) :
    numberedRows? expected raw = some bodies ↔ NumberedAt expected raw bodies := by
  induction raw generalizing expected bodies with
  | nil =>
      constructor
      · intro found
        simp only [numberedRows?, Option.some.injEq] at found
        subst bodies
        exact .nil
      · intro found
        cases found
        rfl
  | cons row rest ih =>
      constructor
      · intro found
        cases first : numberedRow? expected row with
        | none => simp [numberedRows?, first] at found
        | some body =>
            cases following : numberedRows? (expected+1) rest with
            | none => simp [numberedRows?, first, following] at found
            | some later =>
                simp [numberedRows?, first, following] at found
                subst bodies
                have header := (numberedRow_eq_some_iff expected row body).mp first
                exact .cons header.1 header.2 ((ih _ _).mp following)
      · intro found
        cases found with
        | cons number value later =>
            have first := (numberedRow_eq_some_iff _ _ _).mpr ⟨number,value⟩
            have following := (ih _ _).mpr later
            simp [numberedRows?, first, following]

theorem NumberedAt.length_eq {expected : Nat} {raw bodies : List Json}
    (read : NumberedAt expected raw bodies) : raw.length = bodies.length := by
  induction read with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem NumberedAt.append {expected : Nat} {firstRaw secondRaw firstBody secondBody : List Json}
    (first : NumberedAt expected firstRaw firstBody)
    (second : NumberedAt (expected+firstRaw.length) secondRaw secondBody) :
    NumberedAt expected (firstRaw ++ secondRaw) (firstBody ++ secondBody) := by
  induction first with
  | nil => simpa only [List.length_nil, Nat.add_zero, List.nil_append] using second
  | @cons expected raw body rest bodies number value later ih =>
      apply NumberedAt.cons number value
      apply ih
      have same : expected + (raw :: rest).length = (expected+1) + rest.length := by simp; omega
      exact same ▸ second

theorem NumberedAt.lookup {expected : Nat} {raw bodies : List Json}
    (read : NumberedAt expected raw bodies) (index : Nat) (body : Json)
    (found : bodies[index]? = some body) :
    ∃ original, raw[index]? = some original ∧
      identifier? original = some (expected+index) ∧ ExportCodec.at? original 1 = some body := by
  induction read generalizing index with
  | nil => simp at found
  | @cons expected original value rest bodies number valueRead later ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst body
          exact ⟨original, rfl, by simpa only [Nat.add_zero] using number, valueRead⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          obtain ⟨source,atRow,header,payload⟩ := ih index found
          refine ⟨source,by simpa only [List.getElem?_cons_succ] using atRow,?_,payload⟩
          have same : expected+1+index = expected+(index+1) := by omega
          exact same ▸ header

theorem numberedRows_append_checked (expected : Nat)
    (firstRaw secondRaw firstBody secondBody : List Json)
    (first : numberedRows? expected firstRaw = some firstBody)
    (second : numberedRows? (expected+firstRaw.length) secondRaw = some secondBody) :
    numberedRows? expected (firstRaw ++ secondRaw) = some (firstBody ++ secondBody) :=
  (numberedRows_eq_some_iff _ _ _).mpr
    (((numberedRows_eq_some_iff _ _ _).mp first).append ((numberedRows_eq_some_iff _ _ _).mp second))

theorem term_row_exists (symbols : ExportCodec.Symbols) (types terms : Nat → Option Json)
    (index : Nat) (term : SourceTerm) (read : TermAt symbols types terms index term) :
    ∃ raw, terms index = some raw := by
  cases read with
  | «variable» atRow _ _ => exact ⟨_,atRow⟩
  | constant atRow _ _ _ => exact ⟨_,atRow⟩
  | application atRow _ _ _ _ _ => exact ⟨_,atRow⟩
  | abstraction atRow _ _ _ _ _ => exact ⟨_,atRow⟩

theorem certified_term_readback (symbols : ExportCodec.Symbols) (types : Nat → Option Json)
    (raw bodies : List Json) (numbered : NumberedAt 0 raw bodies)
    (cache : Nat → Option SourceTerm)
    (correct : TermCacheCorrect symbols types (fun index => bodies[index]?) cache)
    (index : Nat) (term : SourceTerm) (found : cache index = some term) :
    ∃ original body, raw[index]? = some original ∧ identifier? original = some index ∧
      ExportCodec.at? original 1 = some body ∧ bodies[index]? = some body ∧
      TermAt symbols types (fun index => bodies[index]?) index term := by
  have node := correct index term found
  obtain ⟨body,bodyAt⟩ := term_row_exists symbols types (fun index => bodies[index]?) index term node
  obtain ⟨original,originalAt,header,payload⟩ := numbered.lookup index body bodyAt
  exact ⟨original,body,originalAt,by simpa only [Nat.zero_add] using header,payload,bodyAt,node⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceInput
