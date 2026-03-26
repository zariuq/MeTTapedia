/-
# GFCore.AtomExtract — Extract Atoms from NormClause

Maps normalized clauses to PLN-compatible Atoms.
Copular → isa / rel depending on complement type.
Predication → rel(verb, [subject, object]).

Attr(X, P) is Rel(P, [X]) — use Atom.attr smart constructor.
-/

import GFCore.Atom
import GFCore.NormClause
import GFCore.TermExtract

namespace GFCore

-- detectFocusSwap DELETED — FocusComp is now handled by CopulaOrigin
-- in NormClause, which guarantees copular(semantic_subject, complement)

/-- Check if a complement indicates "is a kind of" (inheritance). -/
private partial def isKindOfComplement : RGLView → Option Term
  | .kindOf _ ofView => some (extractTerm ofView)
  | .adjMod _ cn => isKindOfComplement cn
  | .det _ _ cn => isKindOfComplement cn
  | .mass cn => isKindOfComplement cn
  | .opaque _ args => args.findSome? isKindOfComplement
  | _ => none

/-- Extract an Atom from a NormClause. -/
partial def extractAtom : NormClause → Atom
  -- Copular: "X is Y"
  -- NormClause guarantees: subj = semantic subject, compl = complement
  -- (FocusComp reversal handled by CopulaOrigin in NormClause)
  | .copular subj compl =>
    let subjTerm := extractTerm subj
    -- Check for is-a-kind-of
    match isKindOfComplement compl with
    | some supTerm => .isa subjTerm supTerm
    | none =>
      -- Check complement type
      match compl with
      -- "X is adj" → Attr(X, adj) = Rel(adj, [X])
      | .adj a => Atom.attr subjTerm { gfFun := a, cat := "A" }
      | .adv a => Atom.attr subjTerm { gfFun := a, cat := "Adv" }
      -- "X is [det] Y" — inspect complement using typed modifiers
      | _ =>
        let complTerm := extractTerm compl
        match complTerm with
        | .entity head _ _ mods =>
          -- Check for PP modifiers: "element in stars" → Rel(element, [subj, star])
          let ppObjs := complTerm.ppObjects
          let appos := mods.filterMap fun | .appos h => some h | _ => none
          let nounMods := mods.filterMap fun | .nounMod n => some n | _ => none
          -- Filter out unknown PP objects
          let goodPPs := ppObjs.filter (·.gfFun != "?")
          if !goodPPs.isEmpty then
            match goodPPs with
            | obj :: _ => .rel head [subjTerm, Term.simple obj]
            | [] => Atom.attr subjTerm head
          else if !appos.isEmpty then
            match appos with
            | a :: _ => .rel head [subjTerm, Term.simple a]
            | [] => Atom.attr subjTerm head
          else if !nounMods.isEmpty then
            match nounMods with
            | n :: _ => .rel n [subjTerm, Term.simple head]
            | [] => Atom.attr subjTerm head
          else
            Atom.attr subjTerm head
        | _ =>
          match complTerm.head? with
          | some h => Atom.attr subjTerm h
          | none => .opaque "copular: can't extract"

  -- Predication: "X verb Y" or "X verb"
  | .predication subj verbView obj? =>
    let subjTerm := extractTerm subj
    let verbLex : GroundedLexeme := match verbView with
      | .verb v => { gfFun := v, cat := "V" }
      | .transV v _ => match v with
        | .verb vn => { gfFun := vn, cat := "V2" }
        | _ => (extractTerm v).head?.getD { gfFun := "?verb", cat := "V" }
      | _ => (extractTerm verbView).head?.getD { gfFun := "?verb", cat := "V" }
    -- Check for "causes" pattern → Atom.causes
    if verbLex.baseName == "cause" then
      match obj? with
      | some obj =>
        let objAtom := match obj with
          | .pred s v => extractAtom (normClause (.pred s v))
          | _ => .opaque (extractTerm obj).pretty
        .causes (.opaque subjTerm.pretty) objAtom
      | none => .rel verbLex [subjTerm]
    else
      match obj? with
      | some obj => .rel verbLex [subjTerm, extractTerm obj]
      | none => .rel verbLex [subjTerm]

  -- Passive: "X is verb-ed (by Y)"
  | .passive patient verb agent? =>
    let patTerm := extractTerm patient
    let verbLex := (extractTerm verb).head?.getD { gfFun := "?verb", cat := "V" }
    match agent? with
    | some ag => .rel verbLex [extractTerm ag, patTerm]
    | none => .rel verbLex [patTerm]

  -- Existential: "there is X"
  | .existential ent =>
    Atom.attr (extractTerm ent) { gfFun := "exists", cat := "?" }

  -- Conditional: "if X then Y"
  | .conditional ante cons =>
    .implies (extractAtom ante) (extractAtom cons)

  -- Coordination
  | .coordination _ clauses =>
    .conj (clauses.map extractAtom)

  -- Opaque
  | .opaque view => .opaque view.pretty

/-- Full extraction pipeline: RGLView → NormClause → Atom -/
def extractSemantics (view : RGLView) : Atom :=
  let norm := normClause view
  extractAtom norm

end GFCore
