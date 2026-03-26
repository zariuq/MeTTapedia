/-
# GFCore.TermExtract — Extract structured Terms from RGLView

Maps RGLView NP-like structures to Term with head + modifiers.
Preserves PP modifiers, adjective modifiers, possessives.

"the most common element in stars" →
  Term.entity(element, the, sg, [adj:common, prep:in(star)])
-/

import GFCore.Term
import GFCore.RGLView

namespace GFCore

/-- Extract a structured Term from an RGLView NP. -/
partial def extractTerm : RGLView → Term
  -- Leaf lexemes
  | .noun n => .simple { gfFun := n, cat := "N" }
  | .adj a => .simple { gfFun := a, cat := "A" }
  | .verb v => .simple { gfFun := v, cat := "V" }
  | .prep p => .simple { gfFun := p, cat := "Prep" }
  | .adv a => .simple { gfFun := a, cat := "Adv" }
  | .properNoun n => .simple { gfFun := n, cat := "PN" }
  | .pronoun p => .simple { gfFun := p, cat := "Pron" }
  -- Determiner + CN
  | .det kind num cn =>
    let inner := extractTerm cn
    match inner with
    | .entity h _ _ mods => .entity h (some kind) (some num) mods
    | other => other
  -- Mass noun
  | .mass cn =>
    let inner := extractTerm cn
    match inner with
    | .entity h _ _ mods => .entity h (some .mass) none mods
    | other => other
  -- Adjective modifier: "bright star" → entity(star, [adj:bright])
  | .adjMod adjView cnView =>
    let inner := extractTerm cnView
    -- Extract modifier(s) from the adjective view
    -- CompoundAP produces nested adjMod: adjMod(noun, adj) → add both as mods
    let mods := extractMods adjView
    mods.foldl (fun t m => t.addMod m) inner
  -- Adverb modifier (often a PP)
  | .advMod advView inner =>
    let t := extractTerm inner
    let m := match advView with
      | .prepNP (.prep p) npView =>
        let objHead := (extractTerm npView).head?.getD { gfFun := "?", cat := "?" }
        Modifier.prep { gfFun := p, cat := "Prep" } objHead
      | .adv a => Modifier.adj { gfFun := a, cat := "Adv" }  -- adv as modifier
      | _ => Modifier.opaqueMod advView.pretty
    t.addMod m
  -- Prepositional phrase: "in stars"
  | .prepNP (.prep p) npView =>
    let objHead := (extractTerm npView).head?.getD { gfFun := "?", cat := "?" }
    -- As standalone NP, return the object with prep context
    let np := extractTerm npView
    np.addMod (Modifier.prep { gfFun := p, cat := "Prep" } objHead)
  | .prepNP prepView npView =>
    let np := extractTerm npView
    np.addMod (Modifier.opaqueMod prepView.pretty)
  -- Kind-of: "kind of star" → entity(star) with kind_of modifier
  | .kindOf kView ofView =>
    let of_ := extractTerm ofView
    let kHead := (extractTerm kView).head?.getD { gfFun := "kind_of", cat := "N2" }
    of_.addMod (Modifier.nounMod kHead)
  -- Predication as NP (gerund-like): "looking at X"
  | .pred subj vp =>
    let subjTerm := extractTerm subj
    let vpTerm := extractTerm vp
    .event (vpTerm.head?.getD { gfFun := "?", cat := "?" })
      [(.agent, subjTerm)]
  -- Transitive verb as term
  | .transV verb obj =>
    let verbLex := match verb with
      | .verb v => { gfFun := v, cat := "V" : GroundedLexeme }
      | _ => (extractTerm verb).head?.getD { gfFun := "?verb", cat := "V" }
    .event verbLex [(.patient, extractTerm obj)]
  -- Complement: "X is Y" as NP
  | .copularSurface _ subj _compl => extractTerm subj
  -- Sentence wrapper
  | .sentence _ _ core => extractTerm core
  -- Coordination
  | .coordAnd xs =>
    match xs.map extractTerm with
    | [t] => t
    | ts => .opaque s!"and({String.intercalate ", " (ts.map Term.pretty)})"
  | .coordOr xs =>
    match xs.map extractTerm with
    | [t] => t
    | ts => .opaque s!"or({String.intercalate ", " (ts.map Term.pretty)})"
  -- Passive, reflexive
  | .passiveV v => extractTerm v
  | .reflV v _ => extractTerm v
  -- Opaque fallback
  | .opaque name _ => .opaque name
where
  /-- Extract modifiers from an adjective/modifier view.
      Handles nested adjMod from CompoundAP. -/
  extractMods : RGLView → List Modifier
    | .adj a => [.adj { gfFun := a, cat := "A" }]
    | .noun n => [.nounMod { gfFun := n, cat := "N" }]
    | .properNoun n => [.appos { gfFun := n, cat := "PN" }]
    | .adjMod inner1 inner2 => extractMods inner1 ++ extractMods inner2
    | .prepNP (.prep p) np =>
      let objHead := (extractTerm np).head?.getD { gfFun := "?", cat := "?" }
      [.prep { gfFun := p, cat := "Prep" } objHead]
    | other => [.opaqueMod other.pretty]

end GFCore
