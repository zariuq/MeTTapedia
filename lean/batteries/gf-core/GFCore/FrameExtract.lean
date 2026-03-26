/-
# GFCore.FrameExtract — Extract semantic Frames from RGLView

Two-function approach (council recommendation):
  1. extractEntity : RGLView → Option GroundedLexeme  (NP → entity)
  2. extractFrame  : RGLView → Frame                  (sentence → relation)

Handles 6 PLN patterns: inheritance, evaluation, evaluation2,
member, implication, quantification.
-/

import GFCore.Frame

namespace GFCore

/-- Extract the primary entity (head concept) from any RGLView.
    Handles all NP-like patterns systematically. -/
partial def extractEntity : RGLView → Option GroundedLexeme
  | .noun n      => some { gfFun := n, cat := "N" }
  | .adj a       => some { gfFun := a, cat := "A" }
  | .verb v      => some { gfFun := v, cat := "V" }
  | .prep p      => some { gfFun := p, cat := "Prep" }
  | .adv a       => some { gfFun := a, cat := "Adv" }
  | .properNoun n => some { gfFun := n, cat := "PN" }
  | .pronoun p   => some { gfFun := p, cat := "Pron" }
  | .det _ _ cn  => extractEntity cn      -- "the star" → star
  | .mass cn     => extractEntity cn      -- "water" → water
  | .adjMod _ cn => extractEntity cn      -- "big star" → star
  | .advMod _ vp => extractEntity vp      -- pass through
  | .prepNP _ np => extractEntity np      -- "in stars" → stars
  | .kindOf k _  => extractEntity k       -- "kind of X" → head of kind
  | .pred s _    => extractEntity s       -- in NP context, take subject
  | .copularSurface _ s _    => extractEntity s
  | .transV v _  => extractEntity v       -- verb as entity (rare)
  | .sentence _ _ c => extractEntity c
  | .coordAnd xs => xs.findSome? extractEntity
  | .coordOr xs  => xs.findSome? extractEntity
  | .passiveV v  => extractEntity v
  | .reflV v _   => extractEntity v
  | .opaque _ _  => none                  -- honest: can't extract

/-- Extract ALL entity leaves from an RGLView (not just the head). -/
partial def extractAllEntities : RGLView → List GroundedLexeme
  | .noun n      => [{ gfFun := n, cat := "N" }]
  | .adj a       => [{ gfFun := a, cat := "A" }]
  | .verb v      => [{ gfFun := v, cat := "V" }]
  | .properNoun n => [{ gfFun := n, cat := "PN" }]
  | .det _ _ cn  => extractAllEntities cn
  | .mass cn     => extractAllEntities cn
  | .adjMod a cn => extractAllEntities a ++ extractAllEntities cn
  | .advMod a vp => extractAllEntities a ++ extractAllEntities vp
  | .prepNP p np => extractAllEntities p ++ extractAllEntities np
  | .kindOf k o  => extractAllEntities k ++ extractAllEntities o
  | .pred s v    => extractAllEntities s ++ extractAllEntities v
  | .copularSurface _ s c    => extractAllEntities s ++ extractAllEntities c
  | .transV v o  => extractAllEntities v ++ extractAllEntities o
  | .coordAnd xs => xs.flatMap extractAllEntities
  | .coordOr xs  => xs.flatMap extractAllEntities
  | _ => []

/-- Search for a kindOf pattern anywhere in a view tree. -/
partial def findKindOf? : RGLView → Option GroundedLexeme
  | .kindOf _ of_ => extractEntity of_
  | .sentence _ _ c => findKindOf? c
  | .pred _ vp => findKindOf? vp
  | .copularSurface _ _ c => findKindOf? c
  | .opaque _ args => args.findSome? findKindOf?
  | _ => none

/-- Extract a Frame from VP, given the subject entity. -/
partial def extractVPFrame (subj : Option GroundedLexeme) : RGLView → Frame
  -- Transitive verb: X | V(Y) → evaluation2(V, X, Y)
  | .transV verbView objView =>
    match extractEntity verbView, subj, extractEntity objView with
    | some verb, some arg1, some arg2 => .evaluation2 verb arg1 arg2
    | some verb, none, some arg2 => .evaluation2 verb { gfFun := "?subj", cat := "?" } arg2
    | _, _, _ => .opaque s!"transV: can't extract"
  -- Intransitive verb: X | V → evaluation(V, X)
  | .verb v =>
    match subj with
    | some arg => .evaluation { gfFun := v, cat := "V" } arg
    | none => .opaque s!"verb: {v} (no subject)"
  -- Predicate adjective: X | adj → evaluation(adj, X)
  | .adj a =>
    match subj with
    | some arg => .evaluation { gfFun := a, cat := "A" } arg
    | none => .opaque s!"adj: {a} (no subject)"
  -- Predicate adverb
  | .adv a =>
    match subj with
    | some arg => .evaluation { gfFun := a, cat := "Adv" } arg
    | none => .opaque s!"adv: {a} (no subject)"
  -- Adverbial modification of VP
  | .advMod _ inner => extractVPFrame subj inner
  -- kindOf in VP position: X is a kind of Y → inheritance
  | .kindOf _ of_ =>
    match subj, extractEntity of_ with
    | some sub, some sup => .inheritance sub sup
    | _, _ => .opaque "kindOf: can't extract entities"
  -- Nested sentence in VP (e.g., tense wrapper)
  | .sentence _ _ core => extractVPFrame subj core
  -- Passive voice
  | .passiveV v =>
    match extractEntity v, subj with
    | some verb, some arg => .evaluation verb arg
    | _, _ => .opaque "passive: can't extract"
  -- Reflexive
  | .reflV v arg =>
    match extractEntity v, subj, extractEntity arg with
    | some verb, some s, some a => .evaluation2 verb s a
    | _, _, _ => .opaque "reflV: can't extract"
  -- Copula complement in VP position: "X is [a/the] Y"
  -- This happens when UseComp/CompNP passes a det/mass NP as the VP
  | .det _ _ cn =>
    let complEntities := extractAllEntities cn
    let nouns := complEntities.filter (·.cat == "N")
    match subj, nouns with
    | some s, [n1, n2] => .evaluation2 n1 s n2
    | some s, [n] => .evaluation n s
    | some s, _ =>
      match extractEntity cn with
      | some c => .evaluation c s
      | none => .opaque s!"vp-det: can't extract from {cn.pretty}"
    | none, _ => .opaque "vp-det: no subject"
  | .mass cn =>
    match subj, extractEntity cn with
    | some s, some c => .evaluation c s
    | _, _ => .opaque s!"vp-mass: can't extract"
  -- Nested adjMod as VP (from CompoundAP in complement)
  | .adjMod a cn =>
    let allEntities := extractAllEntities (.adjMod a cn)
    let nouns := allEntities.filter (·.cat == "N")
    match subj, nouns with
    | some s, [n1, n2] => .evaluation2 n1 s n2
    | some s, [n] => .evaluation n s
    | some s, _ =>
      match extractEntity cn with
      | some c => .evaluation c s
      | none => .opaque s!"vp-adjMod: can't extract"
    | none, _ => .opaque "vp-adjMod: no subject"
  -- Noun as VP complement (rare, copula)
  | .noun n =>
    match subj with
    | some s => .evaluation { gfFun := n, cat := "N" } s
    | none => .opaque s!"vp-noun: {n}"
  -- Fallback
  | v => .opaque s!"vp: {v.pretty}"

/-- Extract a Frame from a sentence-level RGLView. -/
partial def extractFrame : RGLView → Frame
  -- Sentence wrapper: unwrap
  | .sentence _ _ core => extractFrame core
  -- Predication: subject | verb-phrase
  | .pred subj vp =>
    let subjEntity := extractEntity subj
    -- Check for kindOf pattern first
    match findKindOf? vp with
    | some sup =>
      match subjEntity with
      | some sub => .inheritance sub sup
      | none => .opaque "pred-kindOf: no subject"
    | none => extractVPFrame subjEntity vp
  -- Copula complement: subject is complement
  | .copularSurface _ subj compl =>
    let subjEntity := extractEntity subj
    -- Check for kindOf
    match findKindOf? compl with
    | some sup =>
      match subjEntity with
      | some sub => .inheritance sub sup
      | none => .opaque "comp-kindOf: no subject"
    | none =>
      -- "X is adj" → evaluation(adj, X)
      match compl with
      | .adj a =>
        match subjEntity with
        | some arg => .evaluation { gfFun := a, cat := "A" } arg
        | none => .opaque s!"comp-adj: no subject for {a}"
      | .adv a =>
        match subjEntity with
        | some arg => .evaluation { gfFun := a, cat := "Adv" } arg
        | none => .opaque s!"comp-adv: no subject"
      | _ =>
        -- FocusComp detection: if complement is a simple entity
        -- and subject is complex, the complement is the semantic subject.
        -- "hydrogen is [the most common element in the sun]"
        -- → comp(subj=[element,sun], compl=hydrogen)
        -- → evaluation2(element, hydrogen, sun)
        let complEntity := extractEntity compl
        let subjNouns := (extractAllEntities subj).filter
          (fun e => e.cat == "N" || e.cat == "PN")
        match complEntity with
        | some semSubj =>
          -- Complement is simple → likely FocusComp
          match subjNouns with
          | [pred, arg] => .evaluation2 pred semSubj arg
          | [pred] => .evaluation pred semSubj
          | pred :: _ =>
            let arg := match subjNouns.getLast? with
              | some a => a | none => pred
            .evaluation2 pred semSubj arg
          | [] =>
            match subjEntity with
            | some s => .evaluation s semSubj
            | none => .opaque "comp: no predicate"
        | none =>
          -- Both sides complex
          match subjEntity, extractEntity compl with
          | some s, some c => .evaluation c s
          | _, _ => .opaque "comp: can't extract"
  -- Coordination
  | .coordAnd xs => .conj (xs.map extractFrame)
  | .coordOr xs => .conj (xs.map extractFrame)
  -- Direct leaf in sentence position → opaque
  | v => .opaque v.pretty

end GFCore
