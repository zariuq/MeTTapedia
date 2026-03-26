/-
# GFCore.Entailment — Deterministic PLN reasoning rules

Implements single-step entailment rules over Frame IR.
All rules are deterministic (no probabilities).
Corresponds to PLN deduction with strength 1.0.

Rules:
  1. Inheritance transitivity: A⊆B + B⊆C → A⊆C
  2. Inheritance substitution: A⊆B + P(B,Y) → P(A,Y)
  3. Property inheritance: A⊆B + Q(B) → Q(A)
  4. Modus ponens: (F1→F2) + F1 → F2
  5. Conjunction introduction: F1 + F2 → F1∧F2
-/

import GFCore.Frame

namespace GFCore

/-- Check if two GroundedLexemes refer to the same concept.
    Compares base names (ignoring WordNet sense numbers). -/
def sameConcept (a b : GroundedLexeme) : Bool :=
  a.baseName == b.baseName

/-- Result of attempting to verify an entailment step. -/
inductive EntailmentResult where
  | verified (rule : String) (derived : Frame)
  | notVerified (reason : String)
  deriving Repr, Inhabited

/-- Try inheritance transitivity: A⊆B + B⊆C → A⊆C -/
def tryTransitivity (premises : Array Frame) : List Frame := Id.run do
  let mut results : List Frame := []
  for p1 in premises do
    for p2 in premises do
      match p1, p2 with
      | .inheritance a b, .inheritance c d =>
        if sameConcept b c then
          results := .inheritance a d :: results
      | _, _ => pure ()
  return results

/-- Try inheritance substitution:
    A⊆B + eval2(P, B, Y) → eval2(P, A, Y) -/
def trySubstitution (premises : Array Frame) : List Frame := Id.run do
  let mut results : List Frame := []
  for p1 in premises do
    for p2 in premises do
      match p1, p2 with
      | .inheritance sub sup, .evaluation2 pred arg1 arg2 =>
        if sameConcept sup pred then
          results := .evaluation2 sub arg1 arg2 :: results
        if sameConcept sup arg1 then
          results := .evaluation2 pred sub arg2 :: results
        if sameConcept sup arg2 then
          results := .evaluation2 pred arg1 sub :: results
      | _, _ => pure ()
  return results

/-- Try property inheritance: A⊆B + eval(P, B) → eval(P, A) -/
def tryPropertyInheritance (premises : Array Frame) : List Frame := Id.run do
  let mut results : List Frame := []
  for p1 in premises do
    for p2 in premises do
      match p1, p2 with
      | .inheritance sub sup, .evaluation pred arg =>
        if sameConcept sup arg then
          results := .evaluation pred sub :: results
      | _, _ => pure ()
  return results

/-- Check if two frames match structurally. -/
def frameMatches (a b : Frame) : Bool :=
  match a, b with
  | .inheritance a1 b1, .inheritance a2 b2 => sameConcept a1 a2 && sameConcept b1 b2
  | .evaluation p1 a1, .evaluation p2 a2 => sameConcept p1 p2 && sameConcept a1 a2
  | .evaluation2 p1 a1 b1, .evaluation2 p2 a2 b2 =>
    sameConcept p1 p2 && sameConcept a1 a2 && sameConcept b1 b2
  | _, _ => false

/-- Try modus ponens: (F1→F2) + F1 → F2 -/
def tryModusPonens (premises : Array Frame) : List Frame := Id.run do
  let mut results : List Frame := []
  for p in premises do
    match p with
    | .implication ante cons =>
      for q in premises do
        if frameMatches ante q then
          results := cons :: results
    | _ => pure ()
  return results

/-- Check if a derived frame matches the target hypothesis.
    For evaluation2, allows permuted argument order since
    FocusComp and PredVPS produce different orderings for
    the same semantic content. -/
def frameMatchesTarget (derived target : Frame) : Bool :=
  match derived, target with
  | .inheritance a1 b1, .inheritance a2 b2 =>
    sameConcept a1 a2 && sameConcept b1 b2
  | .evaluation p1 a1, .evaluation p2 a2 =>
    sameConcept p1 p2 && sameConcept a1 a2
  | .evaluation2 p1 a1 b1, .evaluation2 p2 a2 b2 =>
    -- Strict match
    (sameConcept p1 p2 && sameConcept a1 a2 && sameConcept b1 b2) ||
    -- Permuted: pred might be in arg position due to FocusComp
    (sameConcept p1 a2 && sameConcept a1 b2 && sameConcept b1 p2) ||
    (sameConcept p1 b2 && sameConcept a1 p2 && sameConcept b1 a2)
  | .evaluation2 p1 a1 b1, .evaluation p2 a2 =>
    -- eval2 can match eval if one arg matches pred
    (sameConcept p1 p2 && sameConcept a1 a2) ||
    (sameConcept b1 p2 && sameConcept a1 a2)
  | .evaluation p1 a1, .evaluation2 p2 a2 b2 =>
    (sameConcept p1 p2 && sameConcept a1 a2) ||
    (sameConcept p1 b2 && sameConcept a1 a2)
  | .member a1 b1, .member a2 b2 =>
    sameConcept a1 a2 && sameConcept b1 b2
  | _, _ => false

/-- Collect all GroundedLexeme entities from a Frame. -/
partial def frameEntities : Frame → List GroundedLexeme
  | .inheritance sub sup => [sub, sup]
  | .evaluation pred arg => [pred, arg]
  | .evaluation2 pred a1 a2 => [pred, a1, a2]
  | .member part whole => [part, whole]
  | .implication ante cons => frameEntities ante ++ frameEntities cons
  | .forAll _ body => frameEntities body
  | .exists_ _ body => frameEntities body
  | .conj fs => fs.flatMap frameEntities
  | .neg f => frameEntities f
  | .opaque _ => []

/-- Try inheritance substitution at the entity-set level:
    If we have inheritance(A,B) and premise contains B,
    check if hypothesis has A in that position. -/
def tryEntitySubstitution (premises : Array Frame) (hypothesis : Frame) : Option String := Id.run do
  for p in premises do
    match p with
    | .inheritance sub sup =>
      -- Check if any other premise mentions sup
      for q in premises do
        let qEntities := frameEntities q
        if qEntities.any (sameConcept · sup) then
          -- Check if hypothesis mentions sub (the substituted entity)
          let hEntities := frameEntities hypothesis
          if hEntities.any (sameConcept · sub) then
            -- Check that the rest of the entities match
            let qOther := qEntities.filter (!sameConcept · sup)
            let hOther := hEntities.filter (!sameConcept · sub)
            -- At least some overlap in the other entities
            let overlap := qOther.filter fun qe => hOther.any (sameConcept · qe)
            if !overlap.isEmpty then
              return some s!"entity_substitution: {sub.baseName} for {sup.baseName}"
    | _ => pure ()
  return none

def verifyEntailment (premises : Array Frame) (hypothesis : Frame) : EntailmentResult := Id.run do
  -- First check: is the hypothesis already a premise?
  if premises.any (frameMatchesTarget · hypothesis) then
    return .verified "identity" hypothesis

  -- Try each rule and check if the result matches the hypothesis
  for r in tryTransitivity premises do
    if frameMatchesTarget r hypothesis then
      return .verified "inheritance_transitivity" r

  for r in trySubstitution premises do
    if frameMatchesTarget r hypothesis then
      return .verified "inheritance_substitution" r

  for r in tryPropertyInheritance premises do
    if frameMatchesTarget r hypothesis then
      return .verified "property_inheritance" r

  for r in tryModusPonens premises do
    if frameMatchesTarget r hypothesis then
      return .verified "modus_ponens" r

  -- Entity-set substitution (approximate matching)
  match tryEntitySubstitution premises hypothesis with
  | some rule => return .verified rule hypothesis
  | none => pure ()

  return .notVerified "no applicable rule found"

end GFCore
