/-
# GFCore.Frame — Semantic Frame IR with PLN-consistent terminology

Layer 4 of the GF↔Lean architecture.
Extracts structured meaning from RGLView, using terminology
consistent with PLN (Probabilistic Logic Networks):

  inheritance  = isA / subsumption (InheritanceLink)
  evaluation   = property attribution (EvaluationLink)
  evaluation2  = binary relation (EvaluationLink with 2 args)
  member       = part-of / membership (MemberLink)
  implication  = causal / conditional (ImplicationLink)

Reference: Geisweiller's PLN atom mapping, Council session 2026-03-20
-/

import GFCore.Syntax
import GFCore.RGLView
import GFCore.ConceptId

namespace GFCore

-- GroundedLexeme is now an alias for ConceptId.
-- All existing code using GroundedLexeme continues to work.
abbrev GroundedLexeme := ConceptId

-- baseName and fromGF are inherited from ConceptId namespace.
-- fromRGLView is a convenience wrapper.
namespace GroundedLexeme

def fromRGLView : RGLView → Option GroundedLexeme
  | .noun n => some (ConceptId.fromGF n "N")
  | .adj a => some (ConceptId.fromGF a "A")
  | .verb v => some (ConceptId.fromGF v "V")
  | .prep p => some (ConceptId.fromGF p "Prep")
  | .adv a => some (ConceptId.fromGF a "Adv")
  | .properNoun n => some (ConceptId.fromGF n "PN")
  | .pronoun p => some (ConceptId.fromGF p "Pron")
  | _ => none

end GroundedLexeme

/-- Semantic frames extracted from RGLView.
    Uses PLN-consistent terminology. -/
inductive Frame where
  -- Core PLN link types
  | inheritance (sub sup : GroundedLexeme)
  | evaluation  (pred arg : GroundedLexeme)
  | evaluation2 (pred arg1 arg2 : GroundedLexeme)
  | member      (part whole : GroundedLexeme)
  | implication (ante cons : Frame)
  -- Quantification
  | forAll  (var : String) (body : Frame)
  | exists_ (var : String) (body : Frame)
  -- Logical connectives
  | conj (frames : List Frame)
  | neg  (frame : Frame)
  -- Provenance: not yet extracted
  | opaque (description : String)
  deriving Repr, Inhabited

namespace Frame

/-- Human-readable pretty printing of a Frame. -/
partial def pretty : Frame → String
  | .inheritance sub sup => s!"Inheritance({sub.baseName}, {sup.baseName})"
  | .evaluation pred arg => s!"Evaluation({pred.baseName}, {arg.baseName})"
  | .evaluation2 pred a1 a2 => s!"Evaluation({pred.baseName}, {a1.baseName}, {a2.baseName})"
  | .member part whole => s!"Member({part.baseName}, {whole.baseName})"
  | .implication ante cons => s!"Implication({ante.pretty}, {cons.pretty})"
  | .forAll var body => s!"ForAll({var}, {body.pretty})"
  | .exists_ var body => s!"Exists({var}, {body.pretty})"
  | .conj frames => "Conj(" ++ String.intercalate ", " (frames.map pretty) ++ ")"
  | .neg f => s!"Not({f.pretty})"
  | .opaque desc => s!"Opaque({desc})"

/-- Is this frame an inheritance frame? -/
def isInheritance : Frame → Bool
  | .inheritance .. => true
  | _ => false

/-- Extract the sub/sup pair from an inheritance frame. -/
def getInheritance? : Frame → Option (GroundedLexeme × GroundedLexeme)
  | .inheritance sub sup => some (sub, sup)
  | _ => none

end Frame

end GFCore
