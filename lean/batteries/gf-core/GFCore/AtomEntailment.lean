/-
# GFCore.AtomEntailment — Verified entailment via backward-chaining proof search

Sequent calculus rules:
  Structural: identity
  Logical:    modus ponens, conj intro, conj elim
  IsA:        transitivity, monotone substitution
  Projection: IsA(A,B) → Rel(head(B), [A])

Backward chaining: decompose hypothesis into subgoals, search premises.
Fuel-bounded to guarantee termination. Multi-step derivations come from
recursive calls (e.g., 2-step IsA substitution chains).

Attr(X,P) = Rel(P,[X]) — unified, no separate handling.

TODO (Phase 3): Variance annotations per predicate argument position.

Council: Martin-Löf (substitution), de Paiva (unification, variance),
         Gowers (proof calculus > bag of rules), Goertzel/Geisweiller (PLN),
         Hammer (NARS inheritance), Pfenning (backward search)
-/

import GFCore.Atom
import GFCore.Background
import GFCore.Variance

namespace GFCore

/-- Result of entailment verification. -/
inductive AtomResult where
  | verified (rule : String) (derived : Atom)
  | notVerified (reason : String)
  deriving Repr, Inhabited

/-- Variable-aware term matching. -/
private def termMatchUnify (a b : Term) : Bool :=
  match a.head?, b.head? with
  | some ha, some hb => ha.matchesUnify hb
  | some _, none => true
  | none, some _ => true
  | none, none => true

/-- Variable-aware lexeme matching via ConceptId. -/
private def lexMatchUnify (a b : ConceptId) : Bool :=
  a.matchesUnify b

/-- Substitute a term inside another term. -/
partial def substTerm (old new_ : Term) : Term → Term
  | t@(.entity _h d n mods) =>
    if t.sameHead old then
      match new_ with
      | .entity h2 d2 n2 mods2 =>
        .entity h2 (d2.orElse fun () => d) (n2.orElse fun () => n) (mods2 ++ mods)
      | _ => new_
    else t
  | .event p args =>
    .event p (args.map fun (r, t) => (r, substTerm old new_ t))
  | t => t

/-- Substitute a term inside an atom. -/
partial def substAtom (old new_ : Term) : Atom → Atom
  | .isa sub sup => .isa (substTerm old new_ sub) (substTerm old new_ sup)
  | .rel p args => .rel p (args.map (substTerm old new_))
  | .compare c p x y => .compare c p (substTerm old new_ x) (substTerm old new_ y)
  | .causes c e => .causes (substAtom old new_ c) (substAtom old new_ e)
  | .implies a c => .implies (substAtom old new_ a) (substAtom old new_ c)
  | .conj xs => .conj (xs.map (substAtom old new_))
  | .neg x => .neg (substAtom old new_ x)
  | .forAll v b => .forAll v (substAtom old new_ b)
  | a@(.opaque _) => a

/-- Check if an atom mentions a term (by head match). -/
partial def atomMentions (a : Atom) (t : Term) : Bool :=
  (a.allTerms).any (termMatchUnify · t)

/-- Variable-aware structural equivalence of two atoms. -/
partial def atomEquiv (a b : Atom) : Bool :=
  match a, b with
  | .isa s1 p1, .isa s2 p2 => termMatchUnify s1 s2 && termMatchUnify p1 p2
  | .rel p1 args1, .rel p2 args2 =>
    lexMatchUnify p1 p2 && args1.length == args2.length &&
    (args1.zip args2).all fun (a, b) => termMatchUnify a b
  | .causes c1 e1, .causes c2 e2 => atomEquiv c1 c2 && atomEquiv e1 e2
  | .implies a1 c1, .implies a2 c2 => atomEquiv a1 a2 && atomEquiv c1 c2
  | .conj xs1, .conj xs2 =>
    xs1.length == xs2.length && (xs1.zip xs2).all fun (a, b) => atomEquiv a b
  | _, _ => false

-- ═══════════════════════════════════════════════════════════════════
-- Backward-chaining proof search
-- ═══════════════════════════════════════════════════════════════════

/-- Fuel-bounded backward proof search.
    Tries to derive `goal` from `premises`.
    Returns rule name + derived atom, or none.

    Rules tried in order:
    1. Identity (direct match in premises)
    2. Conjunction introduction (prove each conjunct)
    3. IsA transitivity
    4. IsA monotone substitution
    5. Modus ponens (with recursive proof of antecedent)
    6. Conjunction elimination
    7. IsA projection -/
partial def prove (premises : Array Atom) (fuel : Nat) (goal : Atom)
    : Option (String × Atom) :=
  if fuel == 0 then
    -- At fuel 0, only identity
    if premises.any (atomEquiv · goal) then some ("identity", goal) else none
  else
    -- 1. Identity: P ⊢ P
    if premises.any (atomEquiv · goal) then some ("identity", goal)
    else match goal with
    -- 2. Conjunction introduction: prove each conjunct recursively
    | .conj xs =>
      if xs.all fun x => (prove premises (fuel - 1) x).isSome then
        some ("conj_intro", goal)
      else none
    -- 3. Try each rule family
    | _ =>
      -- IsA transitivity: goal = IsA(A,C), find B via premises
      let isaTrans := Id.run do
        match goal with
        | .isa a c =>
          for p in premises do
            match p with
            | .isa x y =>
              if termMatchUnify x a then
                for q in premises do
                  match q with
                  | .isa y2 z =>
                    if termMatchUnify y y2 && termMatchUnify z c then
                      return some ("isa_transitivity", Atom.isa a c)
                  | _ => pure ()
            | _ => pure ()
          none
        | _ => none

      match isaTrans with
      | some r => some r
      | none =>

      -- IsA substitution: find IsA(sub,sup) + template P(...sup...)
      let isaSubst := Id.run do
        for p in premises do
          match p with
          | .isa sub sup =>
            for q in premises do
              if atomMentions q sup then
                let derived := substAtom sup sub q
                if atomEquiv derived goal then
                  return some ("isa_substitution", derived)
          | _ => pure ()
        none

      match isaSubst with
      | some r => some r
      | none =>

      -- Modus ponens: find Implies(A,C) where C ≡ goal, prove A recursively
      let modusPonens := Id.run do
        for p in premises do
          match p with
          | .implies ante cons =>
            if atomEquiv cons goal then
              match prove premises (fuel - 1) ante with
              | some _ => return some ("modus_ponens", cons)
              | none => pure ()
          | _ => pure ()
        none

      match modusPonens with
      | some r => some r
      | none =>

      -- Conjunction elimination: find Conj([...goal...])
      let conjElim := Id.run do
        for p in premises do
          match p with
          | .conj xs =>
            for x in xs do
              if atomEquiv x goal then
                return some ("conj_elim", x)
          | _ => pure ()
        none

      match conjElim with
      | some r => some r
      | none =>

      -- IsA projection: goal = Rel(P,[X]), find IsA(X, entity(P,...))
      match goal with
      | .rel pred [arg] => Id.run do
        for p in premises do
          match p with
          | .isa sub sup =>
            if termMatchUnify sub arg then
              match sup.head? with
              | some supHead =>
                if lexMatchUnify supHead pred then
                  return some ("isa_projection", Atom.attr sub supHead)
              | none => pure ()
          | _ => pure ()
        none
      | _ => none

/-- Diagnostic result from proof search with gap extraction. -/
inductive ProveResult where
  | proved (rule : String) (derived : Atom)
  | gap (description : String) (needed : List Atom)
  | noProgress
  deriving Repr, Inhabited

/-- Backward proof search with gap extraction.
    When proof fails, identifies what premise(s) would help.
    This enables LLM-guided gap filling with provenance tracking. -/
partial def proveWithGap (premises : Array Atom) (fuel : Nat) (goal : Atom)
    : ProveResult :=
  -- First try the standard proof search
  match prove premises fuel goal with
  | some (rule, derived) => .proved rule derived
  | none =>
    if fuel == 0 then .noProgress
    else Id.run do
      let mut gaps : Array (String × Atom) := #[]

      -- Check IsA transitivity gaps: goal = IsA(A,C)
      match goal with
      | .isa a c =>
        for p in premises do
          match p with
          | .isa x y =>
            if termMatchUnify x a then
              -- Have IsA(A, Y), need IsA(Y, C)
              let needed := Atom.isa y c
              gaps := gaps.push (s!"have IsA({x.pretty},{y.pretty}), need IsA({y.pretty},{c.pretty})", needed)
          | _ => pure ()
        -- Also: have IsA(Y, C), need IsA(A, Y)
        for p in premises do
          match p with
          | .isa y z =>
            if termMatchUnify z c then
              let needed := Atom.isa a y
              gaps := gaps.push (s!"have IsA({y.pretty},{z.pretty}), need IsA({a.pretty},{y.pretty})", needed)
          | _ => pure ()
      | _ => pure ()

      -- Check IsA substitution gaps: find IsA but no matching template
      for p in premises do
        match p with
        | .isa sub sup =>
          -- Have IsA(sub, sup). Need a premise mentioning sup.
          let anyMentions := premises.any (atomMentions · sup)
          if !anyMentions then
            gaps := gaps.push (s!"have IsA({sub.pretty},{sup.pretty}) but no premise mentions {sup.pretty}", goal)
        | _ => pure ()

      -- Check modus ponens gaps: found Implies(A, goal) but can't prove A
      for p in premises do
        match p with
        | .implies ante cons =>
          if atomEquiv cons goal then
            gaps := gaps.push (s!"have Implies({ante.pretty},{cons.pretty}), need to prove {ante.pretty}", ante)
        | _ => pure ()

      -- Check IsA projection gaps: goal = Rel(P,[X])
      match goal with
      | .rel pred [arg] =>
        -- Need IsA(arg, entity(pred,...))
        let needed := Atom.isa arg (Term.simple pred)
        gaps := gaps.push (s!"need IsA({arg.pretty},{pred.baseName}) for projection", needed)
      | _ => pure ()

      -- If no specific gaps found, the goal itself is the gap
      if gaps.isEmpty then
        .gap s!"goal not derivable: {goal.pretty}" [goal]
      else
        -- Return the most specific gap (first one found)
        let (desc, needed) := gaps[0]!
        .gap desc [needed]

/-- Verify entailment using backward-chaining proof search.
    Fuel bound of 10 allows multi-step chains while guaranteeing termination. -/
def verifyAtomEntailment (premises : Array Atom) (hypothesis : Atom) : AtomResult :=
  match prove premises 10 hypothesis with
  | some (rule, derived) => .verified rule derived
  | none => .notVerified "no derivation found"

/-- Verify entailment with gap diagnostics.
    Returns either a verified result or a description of what's missing. -/
def verifyWithGap (premises : Array Atom) (hypothesis : Atom) : ProveResult :=
  proveWithGap premises 10 hypothesis

/-- Verify entailment with background WordNet hypernymy.
    Augments premises with implicit IsA atoms from the hierarchy. -/
def verifyWithBackground (bg : Background) (premises : Array Atom)
    (hypothesis : Atom) : AtomResult := Id.run do
  let mut bgIsA : Array Atom := #[]
  for p in premises do
    for t in p.allTerms do
      match t.head? with
      | some h =>
        match h.synset? with
        | some sid =>
          for parentSid in bg.directParents sid do
            let parentId : ConceptId := {
              gfFun := parentSid, cat := h.cat, synset? := some parentSid
            }
            bgIsA := bgIsA.push (.isa t (.entity parentId none none []))
        | none => pure ()
      | none => pure ()
  let result := verifyAtomEntailment premises hypothesis
  match result with
  | .verified _ _ => return result
  | .notVerified _ =>
    if bgIsA.isEmpty then
      return result
    else
      let augmented := premises ++ bgIsA
      let result2 := verifyAtomEntailment augmented hypothesis
      match result2 with
      | .verified rule derived => return .verified s!"bg_{rule}" derived
      | .notVerified _ => return result2

end GFCore
