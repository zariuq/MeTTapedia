/-
# GFCore.NormClause — Canonicalize RGLView surface variation

Maps different RGL surface realizations to a small set of canonical clause forms.
FocusComp, PredVPS+UseComp, PredVP+UseComp, AdvIsNP all become `copular`.
PredVP+ComplSlash, PredVPS+ComplVPS2 all become `predication`.

This eliminates the FocusComp problem: all copular sentences look the same
regardless of whether the subject is focused, definite, or mass.

Council: Pfenning (normalize before extraction), de Paiva (compositional passes)
-/

import GFCore.RGLView

namespace GFCore

/-- Normalized clause structure. All surface variants mapped to one form. -/
inductive NormClause where
  | copular     (subject : RGLView) (complement : RGLView)
  | predication (subject : RGLView) (verb : RGLView) (object? : Option RGLView)
  | passive     (patient : RGLView) (verb : RGLView) (agent? : Option RGLView)
  | existential (entity : RGLView)
  | conditional (ante cons : NormClause)
  | coordination (conj : String) (clauses : List NormClause)
  | opaque      (view : RGLView)
  deriving Repr, Inhabited

namespace NormClause

/-- Pretty-print a NormClause. -/
partial def pretty : NormClause → String
  | .copular subj compl => s!"copular({subj.pretty}, {compl.pretty})"
  | .predication subj verb obj? =>
    match obj? with
    | some obj => s!"pred({subj.pretty}, {verb.pretty}, {obj.pretty})"
    | none => s!"pred({subj.pretty}, {verb.pretty})"
  | .passive pat verb agent? =>
    match agent? with
    | some ag => s!"passive({pat.pretty}, {verb.pretty}, by {ag.pretty})"
    | none => s!"passive({pat.pretty}, {verb.pretty})"
  | .existential ent => s!"exists({ent.pretty})"
  | .conditional ante cons => s!"if({ante.pretty}, {cons.pretty})"
  | .coordination conj clauses =>
    s!"{conj}({String.intercalate ", " (clauses.map pretty)})"
  | .opaque view => s!"opaque({view.pretty})"

end NormClause

/-- Detect if a VP is a copular complement (UseComp, CompNP, CompCN, etc.). -/
private def isCopularVP : RGLView → Option RGLView
  -- Direct complement views from UseComp peeling
  | .noun _ => some (.noun "")  -- will be caught at a higher level
  | .adj _ => some (.adj "")
  | .adv _ => some (.adv "")
  | .det _ _ _ => some (.det .indefinite .singular (.noun ""))
  | .mass _ => some (.mass (.noun ""))
  | .kindOf _ _ => some (.kindOf (.noun "") (.noun ""))
  | _ => none

/-- Normalize an RGLView into a NormClause.
    Canonicalizes all surface clause variants. -/
partial def normClause : RGLView → NormClause
  -- Sentence wrapper: unwrap
  | .sentence _ _ core => normClause core
  -- Predication: subject | verb-phrase
  | .pred subj vp => normPred subj vp
  -- Copula with origin provenance
  | .copularSurface origin lhs rhs =>
    match origin with
    | .focusComp =>
      -- FocusComp: lhs=focused_complement, rhs=matrix_subject
      -- Swap to canonical: semantic subject = rhs, complement = lhs
      -- Wait — FocusComp(CompNP(focused), matrix_NP) → RGLView gets args[0]=focused, args[1]=matrix
      -- So lhs=focused (the semantic complement!), rhs=matrix (contains predicate structure)
      -- For "hydrogen is [element in sun]": lhs=hydrogen(focused), rhs=element_in_sun(matrix)
      -- Semantic subject = lhs (hydrogen), complement = rhs (element in sun)
      .copular lhs rhs
    | .advIsNP =>
      -- Existential/locative: "here is the tree"
      .existential rhs
    | _ =>
      .copular lhs rhs
  -- Coordination
  | .coordAnd xs => .coordination "and" (xs.map normClause)
  | .coordOr xs => .coordination "or" (xs.map normClause)
  -- Everything else → opaque
  | v => .opaque v
where
  /-- Normalize a predication (subject | vp). -/
  normPred (subj vp : RGLView) : NormClause :=
    match vp with
    -- Copular VP: subject | complement (via UseComp/CompNP/CompCN peeling)
    -- Detected by: VP is an NP-like or adj-like view (not a verb action)
    | .noun _ | .adj _ | .adv _ | .kindOf _ _ =>
      .copular subj vp
    | .det _ _ _ | .mass _ =>
      .copular subj vp
    -- Sentence wrapper inside VP (from MkVPS tense peeling)
    | .sentence _ _ inner => normPred subj inner
    -- Transitive verb: subject | verb(object)
    | .transV verb obj => .predication subj verb (some obj)
    -- Intransitive verb: subject | verb
    | .verb _ => .predication subj vp none
    -- Passive voice
    | .passiveV verb => .passive subj verb none
    -- Reflexive
    | .reflV verb arg => .predication subj verb (some arg)
    -- Adverbial modification of VP — recurse into the inner VP
    | .advMod _ inner => normPred subj inner
    -- Prepositional phrase as VP complement
    | .prepNP _ _ => .predication subj vp none
    -- Opaque VP
    | _ => .opaque (.pred subj vp)

end GFCore
