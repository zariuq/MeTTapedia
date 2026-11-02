import Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

/-! Source derivations contain Unicode scalar values. In particular, turning
their printed scalar sequence into a String cannot replace an invalid point
by a different character. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open ParserProfileSemantics LanguageDefScalarSyntax PresentationExprSemantics

theorem class_valid_char (profile : ParserProfileLayer) (className : String) (point : Nat)
    (formed : profile.ClassEvidence className point) : point.isValidChar := by
  unfold ParserProfileLayer.ClassEvidence ParserProfileLayer.classAccepts? at formed
  cases found : profile.class? className with
  | none => simp [found] at formed
  | some declaration =>
    have accepted : declaration.kind.accepts point = true := by simpa [found] using formed
    simp only [LexicalClassKind.accepts, Bool.and_eq_true] at accepted
    have valid := accepted.1
    simp only [isUnicodeScalar, decide_eq_true_eq] at valid
    simp only [Nat.isValidChar]
    omega

theorem stringScalars_valid (text : String) :
    ∀ point ∈ stringScalars text, point.isValidChar := by
  intro point member
  obtain ⟨character, _, rfl⟩ := List.mem_map.mp member
  exact character.valid

theorem char_ofNat_exact (point : Nat) (valid : point.isValidChar) :
    (Char.ofNat point).toNat = point := by
  rw [Char.ofNat, dif_pos valid]
  rfl

theorem stringScalars_of_valid (points : List Nat) (valid : ∀ point ∈ points, point.isValidChar) :
    stringScalars (String.ofList (points.map Char.ofNat)) = points := by
  simp only [stringScalars, String.toList_ofList, List.map_map]
  calc
    _ = points.map id := List.map_congr_left (fun point member => char_ofNat_exact point (valid point member))
    _ = points := List.map_id points

variable {profile : ParserProfileLayer} {grammar : LanguageDef} {input : List Nat}

mutual
  theorem render_valid {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt (fun text => some (stringScalars text)) profile grammar input sort start stop tree) :
      ∀ point ∈ render source, point.isValidChar :=
    match source with
    | .lexical _ _ formed => by
      intro point member
      have same := List.mem_singleton.mp member
      subst point
      exact class_valid_char _ _ _ formed
    | .structural _ body => renderItems_valid body
  termination_by structural source

  theorem renderItems_valid {rule : GrammarRule} {items : List SyntaxItem}
      {start stop : Nat} {children : List CST}
      (source : ItemsDeriveAt (fun text => some (stringScalars text)) profile grammar input
        rule items start stop children) :
      ∀ point ∈ renderItems source, point.isValidChar :=
    match source with
    | .nil => by simp [renderItems]
    | .terminal decoded _ rest => by
      intro point member
      simp only [Option.some.injEq] at decoded
      rcases List.mem_append.mp member with first | later
      · exact stringScalars_valid _ point (decoded ▸ first)
      · exact renderItems_valid rest point later
    | .nonterminal _ first rest => by
      intro point member
      rcases List.mem_append.mp member with head | tail
      · exact render_valid first point head
      · exact renderItems_valid rest point tail
  termination_by structural source
end

end Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
