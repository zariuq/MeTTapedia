import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternCode
import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternLaws
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# Reading the exact emitted constructor spine as source code

The existing reader converts leaves; the structural emitter inserts only
native constructor applications. Reading the emitted tree therefore produces
exactly `atomCode` of the read template. Scalar spelling, value kinds and
variable identity are retained by the shared leaf reader.

This is raw-term readback. Anonymous-source admission and clause activation
have their own scoping contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa

theorem atomCode_readToken (token : String) :
    (SpaceSemantics.readToken token).map atomCode = SpaceSemantics.readToken token := by
  unfold SpaceSemantics.readToken
  split
  · rfl
  · split
    · dsimp only
      split <;> rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · split <;> rfl
          · split <;> rfl

theorem atomCode_of_readToken {token : String} {atom : Atom}
    (read : SpaceSemantics.readToken token = .ok atom) : atomCode atom = atom := by
  have mapped := atomCode_readToken token
  rw [read] at mapped
  exact Except.ok.inj mapped

mutual
  theorem read_atomCode {template : SExpr} {atom : Atom}
      (read : SpaceSemantics.readRawExpression template = .ok atom) :
      SpaceSemantics.readRawExpression (encode template) = .ok (atomCode atom) := by
    cases template with
    | atom token =>
        change SpaceSemantics.readToken token = .ok atom at read
        rw [atomCode_of_readToken read]
        exact read
    | list templates =>
        cases parsed : SpaceSemantics.readRawExpressions templates with
        | error reason => simp [SpaceSemantics.readRawExpression, parsed] at read
        | ok atoms =>
            have same : .expression atoms = atom := by
              rw [SpaceSemantics.readRawExpression, parsed] at read
              change Except.ok (.expression atoms) = Except.ok atom at read
              exact Except.ok.inj read
            subst atom
            exact read_listCode parsed
  termination_by sizeOf template

  theorem read_listCode {templates : List SExpr} {atoms : List Atom}
      (read : SpaceSemantics.readRawExpressions templates = .ok atoms) :
      SpaceSemantics.readRawExpression (encodeList templates) = .ok (listCode atoms) := by
    cases templates with
    | nil => cases read; rfl
    | cons first rest =>
        cases firstRead : SpaceSemantics.readRawExpression first with
        | error reason =>
            simp [SpaceSemantics.readRawExpressions, firstRead, bind, Except.bind] at read
        | ok firstAtom =>
            cases restRead : SpaceSemantics.readRawExpressions rest with
            | error reason =>
                simp [SpaceSemantics.readRawExpressions, firstRead, restRead, bind, Except.bind] at read
            | ok restAtoms =>
                have same : firstAtom :: restAtoms = atoms := by
                  simpa only [SpaceSemantics.readRawExpressions, firstRead, restRead,
                    bind, Except.bind, pure, Except.pure, Except.ok.injEq] using read
                subst atoms
                have headCode := read_atomCode firstRead
                have tailCode := read_listCode restRead
                have primitiveRead : SpaceSemantics.readToken "cons-atom" =
                    .ok (.symbol "cons-atom") := by decide +kernel
                simp only [encodeList, SpaceSemantics.readRawExpression,
                  SpaceSemantics.readRawExpressions, primitiveRead, headCode, tailCode,
                  bind, Except.bind, pure, Except.pure, listCode]
                rfl
  termination_by sizeOf templates
end

/-- The actual untrusted emitted tree is tied to its read code by the
whole-pattern evidence, rather than by a digest or operation-name match. -/
theorem checked_read_atomCode {template emitted : SExpr} {atom : Atom}
    (checked : check template emitted = true)
    (read : SpaceSemantics.readRawExpression template = .ok atom) :
    SpaceSemantics.readRawExpression emitted = .ok (atomCode atom) := by
  rw [(check_iff template emitted).1 checked]
  exact read_atomCode read

#print axioms read_atomCode
#print axioms checked_read_atomCode

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
