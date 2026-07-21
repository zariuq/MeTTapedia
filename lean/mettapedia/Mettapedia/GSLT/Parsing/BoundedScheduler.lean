import Mettapedia.GSLT.Parsing.PackedForest

/-!
# Executable bounded scheduler for guarded scannerless grammars

This module defines an exhaustive, fuel-bounded scheduler independently of
the relational grammar semantics.  A scheduler candidate carries an exact
stop position, parse tree, and replay certificate.  Recursive nonterminal and
lookahead calls consume fuel; terminals and the remainder of one production
do not.  The bound therefore measures nested source-rule applications rather
than input length.

Finite terminal sets are interpreted directly.  Their separate compaction
theorem explains how source exact-terminal alternatives may be merged before
this scheduler consumes the guarded compiled grammar.
-/

namespace Mettapedia.GSLT.Parsing.BoundedScheduler

open CompilerCorrespondence GuardCorrespondence PackedForest

structure Candidate where
  stop : Nat
  certificate : Certificate
  tree : ParseTree
  deriving Repr

structure BodyCandidate where
  stop : Nat
  certificates : List Certificate
  trees : List ParseTree
  deriving Repr

mutual
  /-- A compiled derivation using at most the supplied nesting fuel. -/
  inductive DerivesWithin (grammar : GuardCorrespondence.CompiledGrammar)
      (fullInput : List Codepoint) :
      Nat → Category → Nat → Nat → ParseTree → Prop where
    | apply (production : GuardCorrespondence.CompiledProduction)
        (member : production ∈ grammar.productions)
        (body : BodyDerivesWithin grammar fullInput fuel production.symbols
          start stop children)
        (guards : GuardsHoldWithin grammar fullInput fuel production.guards stop) :
        DerivesWithin grammar fullInput (fuel + 1) production.category
          start stop (.node production.sourceRule production.category children)

  inductive BodyDerivesWithin (grammar : GuardCorrespondence.CompiledGrammar)
      (fullInput : List Codepoint) :
      Nat → List CompiledSymbol → Nat → Nat → List ParseTree → Prop where
    | nil : BodyDerivesWithin grammar fullInput fuel [] cursor cursor []
    | terminal
        (lookup : fullInput[start]? = some codepoint)
        (rest : BodyDerivesWithin grammar fullInput fuel symbols
          (start + 1) stop children) :
        BodyDerivesWithin grammar fullInput fuel
          (.terminal codepoint :: symbols) start stop
          (.terminal codepoint :: children)
    | anyTerminal
        (lookup : fullInput[start]? = some codepoint)
        (rest : BodyDerivesWithin grammar fullInput fuel symbols
          (start + 1) stop children) :
        BodyDerivesWithin grammar fullInput fuel
          (.anyTerminal :: symbols) start stop
          (.terminal codepoint :: children)
    | oneOfTerminal
        (lookup : fullInput[start]? = some codepoint)
        (member : codepoint ∈ codepoints)
        (rest : BodyDerivesWithin grammar fullInput fuel symbols
          (start + 1) stop children) :
        BodyDerivesWithin grammar fullInput fuel
          (.oneOfTerminal codepoints :: symbols) start stop
          (.terminal codepoint :: children)
    | nonterminal
        (head : DerivesWithin grammar fullInput fuel category start middle tree)
        (rest : BodyDerivesWithin grammar fullInput fuel symbols
          middle stop children) :
        BodyDerivesWithin grammar fullInput fuel
          (.nonterminal category :: symbols) start stop (tree :: children)

  inductive GuardsHoldWithin (grammar : GuardCorrespondence.CompiledGrammar)
      (fullInput : List Codepoint) :
      Nat → List GuardCorrespondence.CompiledGuard → Nat → Prop where
    | nil : GuardsHoldWithin grammar fullInput fuel [] cursor
    | atEnd
        (endEq : cursor = fullInput.length)
        (rest : GuardsHoldWithin grammar fullInput fuel guards cursor) :
        GuardsHoldWithin grammar fullInput fuel (.atEnd :: guards) cursor
    | nextIn
        (lookup : fullInput[cursor]? = some codepoint)
        (member : codepoint ∈ codepoints)
        (rest : GuardsHoldWithin grammar fullInput fuel guards cursor) :
        GuardsHoldWithin grammar fullInput fuel
          (.nextIn codepoints allowEof :: guards) cursor
    | nextInEof
        (allowed : allowEof = true)
        (endEq : cursor = fullInput.length)
        (rest : GuardsHoldWithin grammar fullInput fuel guards cursor) :
        GuardsHoldWithin grammar fullInput fuel
          (.nextIn codepoints allowEof :: guards) cursor
    | lookahead
        (witness : DerivesWithin grammar fullInput fuel category
          cursor witnessStop tree)
        (rest : GuardsHoldWithin grammar fullInput fuel guards cursor) :
        GuardsHoldWithin grammar fullInput fuel
          (.lookahead category :: guards) cursor
end

mutual
  def eraseDerivation
      {grammar : GuardCorrespondence.CompiledGrammar}
      {fullInput fuel category start stop tree} :
      DerivesWithin grammar fullInput fuel category start stop tree →
        GuardCorrespondence.CompiledDerivesAt grammar fullInput
          category start stop tree
    | .apply production member body guards =>
        .apply production member (eraseBody body) (eraseGuards guards)

  def eraseBody
      {grammar : GuardCorrespondence.CompiledGrammar}
      {fullInput fuel symbols start stop trees} :
      BodyDerivesWithin grammar fullInput fuel symbols start stop trees →
        GuardCorrespondence.CompiledBodyDerivesAt grammar fullInput
          symbols start stop trees
    | .nil => .nil
    | .terminal lookup rest => .terminal lookup (eraseBody rest)
    | .anyTerminal lookup rest => .anyTerminal lookup (eraseBody rest)
    | .oneOfTerminal lookup member rest =>
        .oneOfTerminal lookup member (eraseBody rest)
    | .nonterminal head rest =>
        .nonterminal (eraseDerivation head) (eraseBody rest)

  def eraseGuards
      {grammar : GuardCorrespondence.CompiledGrammar}
      {fullInput fuel guards cursor} :
      GuardsHoldWithin grammar fullInput fuel guards cursor →
        GuardCorrespondence.CompiledGuardsHold grammar fullInput guards cursor
    | .nil => .nil
    | .atEnd endEq rest => .atEnd endEq (eraseGuards rest)
    | .nextIn lookup member rest =>
        .nextIn lookup member (eraseGuards rest)
    | .nextInEof allowed endEq rest =>
        .nextInEof allowed endEq (eraseGuards rest)
    | .lookahead witness rest =>
        .lookahead (eraseDerivation witness) (eraseGuards rest)
end

mutual
  def liftDerivationOne
      {grammar : GuardCorrespondence.CompiledGrammar}
      {input fuel category start stop tree} :
      DerivesWithin grammar input fuel category start stop tree →
        DerivesWithin grammar input (fuel + 1) category start stop tree
    | .apply production member body guards =>
        .apply production member (liftBodyOne body) (liftGuardsOne guards)

  def liftBodyOne
      {grammar : GuardCorrespondence.CompiledGrammar}
      {input fuel symbols start stop trees} :
      BodyDerivesWithin grammar input fuel symbols start stop trees →
        BodyDerivesWithin grammar input (fuel + 1) symbols start stop trees
    | .nil => .nil
    | .terminal lookup rest => .terminal lookup (liftBodyOne rest)
    | .anyTerminal lookup rest => .anyTerminal lookup (liftBodyOne rest)
    | .oneOfTerminal lookup member rest =>
        .oneOfTerminal lookup member (liftBodyOne rest)
    | .nonterminal head rest =>
        .nonterminal (liftDerivationOne head) (liftBodyOne rest)

  def liftGuardsOne
      {grammar : GuardCorrespondence.CompiledGrammar}
      {input fuel guards cursor} :
      GuardsHoldWithin grammar input fuel guards cursor →
        GuardsHoldWithin grammar input (fuel + 1) guards cursor
    | .nil => .nil
    | .atEnd endEq rest => .atEnd endEq (liftGuardsOne rest)
    | .nextIn lookup member rest =>
        .nextIn lookup member (liftGuardsOne rest)
    | .nextInEof allowed endEq rest =>
        .nextInEof allowed endEq (liftGuardsOne rest)
    | .lookahead witness rest =>
        .lookahead (liftDerivationOne witness) (liftGuardsOne rest)
end

def liftDerivationBy
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input fuel category start stop tree} :
    (extra : Nat) → DerivesWithin grammar input fuel category start stop tree →
      DerivesWithin grammar input (fuel + extra) category start stop tree
  | 0, derivation => derivation
  | extra + 1, derivation =>
      liftDerivationOne (liftDerivationBy extra derivation)

def liftBodyBy
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input fuel symbols start stop trees} :
    (extra : Nat) →
      BodyDerivesWithin grammar input fuel symbols start stop trees →
      BodyDerivesWithin grammar input (fuel + extra) symbols start stop trees
  | 0, derivation => derivation
  | extra + 1, derivation => liftBodyOne (liftBodyBy extra derivation)

def liftGuardsBy
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input fuel guards cursor} :
    (extra : Nat) → GuardsHoldWithin grammar input fuel guards cursor →
      GuardsHoldWithin grammar input (fuel + extra) guards cursor
  | 0, derivation => derivation
  | extra + 1, derivation => liftGuardsOne (liftGuardsBy extra derivation)

def liftDerivationTo
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input fuel target category start stop tree}
    (le : fuel ≤ target)
    (derivation : DerivesWithin grammar input fuel category start stop tree) :
    DerivesWithin grammar input target category start stop tree := by
  have lifted := liftDerivationBy (target - fuel) derivation
  simpa [Nat.add_sub_of_le le] using lifted

def liftBodyTo
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input fuel target symbols start stop trees}
    (le : fuel ≤ target)
    (derivation : BodyDerivesWithin grammar input fuel symbols start stop trees) :
    BodyDerivesWithin grammar input target symbols start stop trees := by
  have lifted := liftBodyBy (target - fuel) derivation
  simpa [Nat.add_sub_of_le le] using lifted

def liftGuardsTo
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input fuel target guards cursor}
    (le : fuel ≤ target)
    (derivation : GuardsHoldWithin grammar input fuel guards cursor) :
    GuardsHoldWithin grammar input target guards cursor := by
  have lifted := liftGuardsBy (target - fuel) derivation
  simpa [Nat.add_sub_of_le le] using lifted

theorem compiledDerivation_hasBound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input category start stop tree}
    (derivation : GuardCorrespondence.CompiledDerivesAt grammar input
      category start stop tree) :
    ∃ fuel, DerivesWithin grammar input fuel category start stop tree := by
  exact GuardCorrespondence.CompiledDerivesAt.rec
    (motive_1 := fun category start stop tree _ =>
      ∃ fuel, DerivesWithin grammar input fuel category start stop tree)
    (motive_2 := fun symbols start stop trees _ =>
      ∃ fuel, BodyDerivesWithin grammar input fuel symbols start stop trees)
    (motive_3 := fun guards cursor _ =>
      ∃ fuel, GuardsHoldWithin grammar input fuel guards cursor)
    (fun production member _ _ bodyBound guardsBound => by
      obtain ⟨bodyFuel, boundedBody⟩ := bodyBound
      obtain ⟨guardFuel, boundedGuards⟩ := guardsBound
      let fuel := max bodyFuel guardFuel
      exact ⟨fuel + 1,
        .apply production member
          (liftBodyTo (Nat.le_max_left bodyFuel guardFuel) boundedBody)
          (liftGuardsTo (Nat.le_max_right bodyFuel guardFuel) boundedGuards)⟩)
    (by exact ⟨0, .nil⟩)
    (fun lookup _ restBound => by
      obtain ⟨fuel, boundedRest⟩ := restBound
      exact ⟨fuel, .terminal lookup boundedRest⟩)
    (fun lookup _ restBound => by
      obtain ⟨fuel, boundedRest⟩ := restBound
      exact ⟨fuel, .anyTerminal lookup boundedRest⟩)
    (fun lookup member _ restBound => by
      obtain ⟨fuel, boundedRest⟩ := restBound
      exact ⟨fuel, .oneOfTerminal lookup member boundedRest⟩)
    (fun _ _ headBound restBound => by
      obtain ⟨headFuel, boundedHead⟩ := headBound
      obtain ⟨restFuel, boundedRest⟩ := restBound
      let fuel := max headFuel restFuel
      exact ⟨fuel,
        .nonterminal
          (liftDerivationTo (Nat.le_max_left headFuel restFuel) boundedHead)
          (liftBodyTo (Nat.le_max_right headFuel restFuel) boundedRest)⟩)
    (by exact ⟨0, .nil⟩)
    (fun endEq _ restBound => by
      obtain ⟨fuel, boundedRest⟩ := restBound
      exact ⟨fuel, .atEnd endEq boundedRest⟩)
    (fun lookup member _ restBound => by
      obtain ⟨fuel, boundedRest⟩ := restBound
      exact ⟨fuel, .nextIn lookup member boundedRest⟩)
    (fun allowed endEq _ restBound => by
      obtain ⟨fuel, boundedRest⟩ := restBound
      exact ⟨fuel, .nextInEof allowed endEq boundedRest⟩)
    (fun _ _ witnessBound restBound => by
      obtain ⟨witnessFuel, boundedWitness⟩ := witnessBound
      obtain ⟨restFuel, boundedRest⟩ := restBound
      let fuel := max witnessFuel restFuel
      exact ⟨fuel,
        .lookahead
          (liftDerivationTo (Nat.le_max_left witnessFuel restFuel)
            boundedWitness)
          (liftGuardsTo (Nat.le_max_right witnessFuel restFuel) boundedRest)⟩)
    derivation

theorem certificateReplays_spans
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input certificate category start stop tree}
    (replay : GuardCorrespondence.CertificateReplays grammar input certificate
      category start stop tree) :
    certificate.start = start ∧ certificate.stop = stop := by
  cases replay
  exact ⟨rfl, rfl⟩

theorem certificateBodyReplays_nonterminal
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint}
    {headCertificate : Certificate} {category : Category}
    {start middle : Nat} {headTree : ParseTree}
    {symbols : List CompiledSymbol} {stop : Nat}
    {certificates : List Certificate} {trees : List ParseTree}
    (headReplay : GuardCorrespondence.CertificateReplays grammar input
      headCertificate category start middle headTree)
    (restReplay : GuardCorrespondence.CertificateBodyReplays grammar input
      symbols middle stop certificates trees) :
    GuardCorrespondence.CertificateBodyReplays grammar input
      (.nonterminal category :: symbols) start stop
      (headCertificate :: certificates) (headTree :: trees) := by
  have spans := certificateReplays_spans headReplay
  cases headCertificate with
  | terminal codepoint childStart childStop => cases headReplay
  | node sourceRule childCategory childStart childStop children =>
      simp only [Certificate.start, Certificate.stop] at spans
      rcases spans with ⟨rfl, rfl⟩
      cases headReplay with
      | node production productionMember bodyReplay guardsReplay =>
          exact .nonterminal
            (.node production productionMember bodyReplay guardsReplay)
            restReplay

/-- Enumerate one production body using a supplied scheduler for recursive
nonterminal calls. -/
def scheduleBody
    (recurse : Category → Nat → List Candidate)
    (input : List Codepoint) :
    List CompiledSymbol → Nat → List BodyCandidate
  | [], cursor =>
      [{ stop := cursor, certificates := [], trees := [] }]
  | .terminal codepoint :: symbols, start =>
      if input[start]? = some codepoint then
        (scheduleBody recurse input symbols (start + 1)).map fun rest =>
          { stop := rest.stop
            certificates :=
              .terminal codepoint start (start + 1) :: rest.certificates
            trees := .terminal codepoint :: rest.trees }
      else []
  | .anyTerminal :: symbols, start =>
      match input[start]? with
      | none => []
      | some codepoint =>
          (scheduleBody recurse input symbols (start + 1)).map fun rest =>
            { stop := rest.stop
              certificates :=
                .terminal codepoint start (start + 1) :: rest.certificates
              trees := .terminal codepoint :: rest.trees }
  | .oneOfTerminal codepoints :: symbols, start =>
      match input[start]? with
      | none => []
      | some codepoint =>
          if codepoint ∈ codepoints then
            (scheduleBody recurse input symbols (start + 1)).map fun rest =>
              { stop := rest.stop
                certificates :=
                  .terminal codepoint start (start + 1) :: rest.certificates
                trees := .terminal codepoint :: rest.trees }
          else []
  | .nonterminal category :: symbols, start =>
      (recurse category start).flatMap fun head =>
        (scheduleBody recurse input symbols head.stop).map fun rest =>
          { stop := rest.stop
            certificates := head.certificate :: rest.certificates
            trees := head.tree :: rest.trees }

/-- Check zero-width guards using the same bounded scheduler for lookahead. -/
def guardsPass
    (recurse : Category → Nat → List Candidate)
    (input : List Codepoint) :
    List GuardCorrespondence.CompiledGuard → Nat → Bool
  | [], _ => true
  | .atEnd :: guards, cursor =>
      decide (cursor = input.length) && guardsPass recurse input guards cursor
  | .nextIn codepoints allowEof :: guards, cursor =>
      match input[cursor]? with
      | some codepoint =>
          decide (codepoint ∈ codepoints) &&
            guardsPass recurse input guards cursor
      | none =>
          allowEof && decide (cursor = input.length) &&
            guardsPass recurse input guards cursor
  | .lookahead category :: guards, cursor =>
      !(recurse category cursor).isEmpty &&
        guardsPass recurse input guards cursor

/-- Exhaustive bounded scheduler.  Every recursive call receives strictly
less fuel; body sequencing remains at the current recursive bound. -/
def scheduleCategory (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) : Nat → Category → Nat → List Candidate
  | 0, _, _ => []
  | fuel + 1, category, start =>
      grammar.productions.flatMap fun production =>
        if production.category = category then
          (scheduleBody (scheduleCategory grammar input fuel) input
              production.symbols start).flatMap fun body =>
            if guardsPass (scheduleCategory grammar input fuel) input
                production.guards body.stop then
              [{ stop := body.stop
                 certificate := .node production.sourceRule
                   production.category start body.stop body.certificates
                 tree := .node production.sourceRule
                   production.category body.trees }]
            else []
        else []

def scheduleRoot (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (fuel : Nat) : List Candidate :=
  (scheduleCategory grammar input fuel grammar.start 0).filter
    fun candidate => candidate.stop = input.length

theorem scheduleBody_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    {recurse : Category → Nat → List Candidate}
    (recurseSound : ∀ {category start candidate},
      candidate ∈ recurse category start →
        DerivesWithin grammar input fuel category start candidate.stop
            candidate.tree ∧
          GuardCorrespondence.CertificateReplays grammar input
            candidate.certificate category start candidate.stop candidate.tree)
    {symbols start candidate}
    (member : candidate ∈ scheduleBody recurse input symbols start) :
    BodyDerivesWithin grammar input fuel symbols start candidate.stop
        candidate.trees ∧
      GuardCorrespondence.CertificateBodyReplays grammar input symbols start
        candidate.stop candidate.certificates candidate.trees := by
  induction symbols generalizing start candidate with
  | nil =>
      simp [scheduleBody] at member
      subst candidate
      exact ⟨.nil, .nil⟩
  | cons symbol symbols inductionHypothesis =>
      cases symbol with
      | terminal codepoint =>
          by_cases lookup : input[start]? = some codepoint
          · simp only [scheduleBody, lookup, if_pos] at member
            obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp member
            obtain ⟨restDerivation, restReplay⟩ :=
              inductionHypothesis restMember
            exact ⟨.terminal lookup restDerivation,
              .terminal lookup restReplay⟩
          · simp [scheduleBody, lookup] at member
      | anyTerminal =>
          cases lookup : input[start]? with
          | none => simp [scheduleBody, lookup] at member
          | some codepoint =>
              simp only [scheduleBody, lookup] at member
              obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp member
              obtain ⟨restDerivation, restReplay⟩ :=
                inductionHypothesis restMember
              exact ⟨.anyTerminal lookup restDerivation,
                .anyTerminal lookup restReplay⟩
      | oneOfTerminal codepoints =>
          cases lookup : input[start]? with
          | none => simp [scheduleBody, lookup] at member
          | some codepoint =>
              by_cases codepointMember : codepoint ∈ codepoints
              · simp only [scheduleBody, lookup, codepointMember, if_pos] at member
                obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp member
                obtain ⟨restDerivation, restReplay⟩ :=
                  inductionHypothesis restMember
                exact ⟨.oneOfTerminal lookup codepointMember restDerivation,
                  .oneOfTerminal lookup codepointMember restReplay⟩
              · simp [scheduleBody, lookup, codepointMember] at member
      | nonterminal category =>
          simp only [scheduleBody] at member
          obtain ⟨head, headMember, restMapMember⟩ :=
            List.mem_flatMap.mp member
          rcases head with ⟨headStop, headCertificate, headTree⟩
          obtain ⟨rest, restMember, rfl⟩ :=
            List.mem_map.mp restMapMember
          obtain ⟨headDerivation, headReplay⟩ := recurseSound headMember
          obtain ⟨restDerivation, restReplay⟩ :=
            inductionHypothesis restMember
          exact ⟨.nonterminal headDerivation restDerivation,
            certificateBodyReplays_nonterminal headReplay restReplay⟩

theorem scheduleBody_complete
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    {recurse : Category → Nat → List Candidate}
    (recurseComplete : ∀ {category start stop tree},
      DerivesWithin grammar input fuel category start stop tree →
        ∃ candidate,
          candidate ∈ recurse category start ∧
          candidate.stop = stop ∧ candidate.tree = tree ∧
          GuardCorrespondence.CertificateReplays grammar input
            candidate.certificate category start stop tree)
    {symbols start stop trees}
    (derivation : BodyDerivesWithin grammar input fuel symbols start stop trees) :
    ∃ candidate,
      candidate ∈ scheduleBody recurse input symbols start ∧
      candidate.stop = stop ∧ candidate.trees = trees ∧
      GuardCorrespondence.CertificateBodyReplays grammar input symbols start
        stop candidate.certificates trees := by
  induction symbols generalizing start stop trees with
  | nil =>
      cases derivation with
      | nil =>
          exact ⟨{ stop := _, certificates := [], trees := [] },
            by simp [scheduleBody], rfl, rfl, .nil⟩
  | cons symbol symbols inductionHypothesis =>
      cases symbol with
      | terminal codepoint =>
          cases derivation with
          | terminal lookup rest =>
              obtain ⟨candidate, member, stopEq, treesEq, replay⟩ :=
                inductionHypothesis rest
              let result : BodyCandidate :=
                { stop := candidate.stop
                  certificates :=
                    .terminal codepoint start (start + 1) ::
                      candidate.certificates
                  trees := .terminal codepoint :: candidate.trees }
              refine ⟨result, ?_, stopEq, ?_, ?_⟩
              · simp only [scheduleBody, lookup, if_pos]
                exact List.mem_map.mpr ⟨candidate, member, rfl⟩
              · simp [result, treesEq]
              · simpa [result, treesEq] using
                  GuardCorrespondence.CertificateBodyReplays.terminal
                    lookup replay
      | anyTerminal =>
          cases derivation with
          | anyTerminal lookup rest =>
              rename_i codepoint children
              obtain ⟨candidate, member, stopEq, treesEq, replay⟩ :=
                inductionHypothesis rest
              let result : BodyCandidate :=
                { stop := candidate.stop
                  certificates :=
                    .terminal codepoint start (start + 1) ::
                      candidate.certificates
                  trees := .terminal codepoint :: candidate.trees }
              refine ⟨result, ?_, stopEq, ?_, ?_⟩
              · simp only [scheduleBody, lookup]
                exact List.mem_map.mpr ⟨candidate, member, rfl⟩
              · simp [result, treesEq]
              · simpa [result, treesEq] using
                  GuardCorrespondence.CertificateBodyReplays.anyTerminal
                    lookup replay
      | oneOfTerminal codepoints =>
          cases derivation with
          | oneOfTerminal lookup codepointMember rest =>
              rename_i codepoint children
              obtain ⟨candidate, member, stopEq, treesEq, replay⟩ :=
                inductionHypothesis rest
              let result : BodyCandidate :=
                { stop := candidate.stop
                  certificates :=
                    .terminal codepoint start (start + 1) ::
                      candidate.certificates
                  trees := .terminal codepoint :: candidate.trees }
              refine ⟨result, ?_, stopEq, ?_, ?_⟩
              · simp only [scheduleBody, lookup, codepointMember, if_pos]
                exact List.mem_map.mpr ⟨candidate, member, rfl⟩
              · simp [result, treesEq]
              · simpa [result, treesEq] using
                  GuardCorrespondence.CertificateBodyReplays.oneOfTerminal
                    lookup codepointMember replay
      | nonterminal category =>
          cases derivation with
          | nonterminal head rest =>
              obtain ⟨headCandidate, headMember, headStop, headTree,
                  headReplay⟩ := recurseComplete head
              obtain ⟨restCandidate, restMember, restStop, restTrees,
                  restReplay⟩ := inductionHypothesis rest
              let result : BodyCandidate :=
                { stop := restCandidate.stop
                  certificates :=
                    headCandidate.certificate :: restCandidate.certificates
                  trees := headCandidate.tree :: restCandidate.trees }
              refine ⟨result, ?_, restStop, ?_, ?_⟩
              · simp only [scheduleBody]
                apply List.mem_flatMap.mpr
                refine ⟨headCandidate, headMember, ?_⟩
                rw [headStop]
                exact List.mem_map.mpr ⟨restCandidate, restMember, rfl⟩
              · simp [result, headTree, restTrees]
              · simpa [result, headTree, restTrees, headStop] using
                  certificateBodyReplays_nonterminal headReplay restReplay

theorem guardsPass_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    {recurse : Category → Nat → List Candidate}
    (recurseSound : ∀ {category start candidate},
      candidate ∈ recurse category start →
        DerivesWithin grammar input fuel category start candidate.stop
          candidate.tree)
    {guards cursor}
    (accepted : guardsPass recurse input guards cursor = true) :
    GuardsHoldWithin grammar input fuel guards cursor := by
  induction guards generalizing cursor with
  | nil => exact .nil
  | cons guard guards inductionHypothesis =>
      cases guard with
      | atEnd =>
          simp only [guardsPass, Bool.and_eq_true, decide_eq_true_eq] at accepted
          exact .atEnd accepted.1 (inductionHypothesis accepted.2)
      | nextIn codepoints allowEof =>
          cases lookup : input[cursor]? with
          | none =>
              simp only [guardsPass, lookup, Bool.and_eq_true,
                decide_eq_true_eq] at accepted
              exact .nextInEof accepted.1.1 accepted.1.2
                (inductionHypothesis accepted.2)
          | some codepoint =>
              simp only [guardsPass, lookup, Bool.and_eq_true,
                decide_eq_true_eq] at accepted
              exact .nextIn lookup accepted.1
                (inductionHypothesis accepted.2)
      | lookahead category =>
          cases candidatesEq : recurse category cursor with
          | nil => simp [guardsPass, candidatesEq] at accepted
          | cons candidate candidates =>
              have candidateMember :
                  candidate ∈ recurse category cursor := by
                simp [candidatesEq]
              have restAccepted :
                  guardsPass recurse input guards cursor = true := by
                simpa [guardsPass, candidatesEq] using accepted
              exact .lookahead (recurseSound candidateMember)
                (inductionHypothesis restAccepted)

theorem guardsPass_complete
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    {recurse : Category → Nat → List Candidate}
    (recurseComplete : ∀ {category start stop tree},
      DerivesWithin grammar input fuel category start stop tree →
        ∃ candidate, candidate ∈ recurse category start)
    {guards cursor}
    (derivation : GuardsHoldWithin grammar input fuel guards cursor) :
    guardsPass recurse input guards cursor = true := by
  induction guards generalizing cursor with
  | nil => rfl
  | cons guard guards inductionHypothesis =>
      cases guard with
      | atEnd =>
          cases derivation with
          | atEnd endEq rest =>
              simp only [guardsPass, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨endEq, inductionHypothesis rest⟩
      | nextIn codepoints allowEof =>
          cases derivation with
          | nextIn lookup member rest =>
              simp only [guardsPass, lookup, Bool.and_eq_true,
                decide_eq_true_eq]
              exact ⟨member, inductionHypothesis rest⟩
          | nextInEof allowed endEq rest =>
              have lookupNone : input[cursor]? = none := by
                rw [endEq]
                simp
              simp only [guardsPass, lookupNone, Bool.and_eq_true,
                decide_eq_true_eq]
              exact ⟨⟨allowed, endEq⟩, inductionHypothesis rest⟩
      | lookahead category =>
          cases derivation with
          | lookahead witness rest =>
              obtain ⟨candidate, candidateMember⟩ :=
                recurseComplete witness
              cases candidatesEq : recurse category cursor with
              | nil => simp [candidatesEq] at candidateMember
              | cons head tail =>
                  simpa [guardsPass, candidatesEq] using
                    inductionHypothesis rest

theorem scheduleCategory_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    {category start candidate}
    (member : candidate ∈ scheduleCategory grammar input fuel category start) :
    DerivesWithin grammar input fuel category start candidate.stop
        candidate.tree ∧
      GuardCorrespondence.CertificateReplays grammar input
        candidate.certificate category start candidate.stop candidate.tree := by
  induction fuel generalizing category start candidate with
  | zero => simp [scheduleCategory] at member
  | succ fuel inductionHypothesis =>
      simp only [scheduleCategory] at member
      obtain ⟨production, productionMember, productionBranch⟩ :=
        List.mem_flatMap.mp member
      by_cases categoryEq : production.category = category
      · simp only [categoryEq, if_pos] at productionBranch
        obtain ⟨body, bodyMember, candidateBranch⟩ :=
          List.mem_flatMap.mp productionBranch
        by_cases guardsAccepted :
            guardsPass (scheduleCategory grammar input fuel) input
              production.guards body.stop = true
        · simp only [guardsAccepted, if_pos] at candidateBranch
          have candidateEq : candidate =
              { stop := body.stop
                certificate := .node production.sourceRule
                  category start body.stop body.certificates
                tree := .node production.sourceRule category
                  body.trees } := by
            simpa using candidateBranch
          subst candidate
          obtain ⟨bodyDerivation, bodyReplay⟩ :=
            scheduleBody_sound
              (recurseSound := fun {_ _ _} recursiveMember =>
                inductionHypothesis recursiveMember)
              bodyMember
          have guardDerivation := guardsPass_sound
            (recurseSound := fun {_ _ _} recursiveMember =>
              (inductionHypothesis recursiveMember).1)
            guardsAccepted
          rcases categoryEq with rfl
          exact ⟨.apply production productionMember bodyDerivation
              guardDerivation,
            .node production productionMember bodyReplay
              (eraseGuards guardDerivation)⟩
        · simp [guardsAccepted] at candidateBranch
      · simp [categoryEq] at productionBranch

theorem scheduleCategory_complete
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    {category start stop tree}
    (derivation : DerivesWithin grammar input fuel category start stop tree) :
    ∃ candidate,
      candidate ∈ scheduleCategory grammar input fuel category start ∧
      candidate.stop = stop ∧ candidate.tree = tree ∧
      GuardCorrespondence.CertificateReplays grammar input
        candidate.certificate category start stop tree := by
  induction fuel generalizing category start stop tree with
  | zero => cases derivation
  | succ fuel inductionHypothesis =>
      cases derivation with
      | apply production productionMember body guards =>
          obtain ⟨bodyCandidate, bodyMember, bodyStop, bodyTrees,
              bodyReplay⟩ :=
            scheduleBody_complete
              (recurseComplete := fun {_ _ _ _} recursiveDerivation =>
                inductionHypothesis recursiveDerivation)
              body
          have guardsAccepted := guardsPass_complete
            (recurseComplete := fun {_ _ _ _} recursiveDerivation => by
              obtain ⟨candidate, candidateMember, _⟩ :=
                inductionHypothesis recursiveDerivation
              exact ⟨candidate, candidateMember⟩)
            guards
          let result : Candidate :=
            { stop := bodyCandidate.stop
              certificate := .node production.sourceRule production.category
                start bodyCandidate.stop bodyCandidate.certificates
              tree := .node production.sourceRule production.category
                bodyCandidate.trees }
          refine ⟨result, ?_, bodyStop, ?_, ?_⟩
          · simp only [scheduleCategory, List.mem_flatMap]
            refine ⟨production, productionMember, ?_⟩
            rw [if_pos (by rfl)]
            apply List.mem_flatMap.mpr
            refine ⟨bodyCandidate, bodyMember, ?_⟩
            have guardsAtCandidate :
                guardsPass (scheduleCategory grammar input fuel) input
                  production.guards bodyCandidate.stop = true := by
              simpa [bodyStop] using guardsAccepted
            rw [if_pos guardsAtCandidate]
            simp [result]
          · simp [result, bodyTrees]
          · simpa [result, bodyStop, bodyTrees] using
              GuardCorrespondence.CertificateReplays.node production
                productionMember bodyReplay (eraseGuards guards)

theorem certificateReplays_hasKey
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input certificate category start stop tree}
    (replay : GuardCorrespondence.CertificateReplays grammar input certificate
      category start stop tree) :
    ∃ key, certificateKey certificate = some key := by
  cases replay with
  | node production member body guards =>
      exact ⟨{ category := production.category, start := start, stop := stop },
        rfl⟩

theorem scheduleRoot_sound
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {fuel : Nat} {candidate : Candidate}
    (member : candidate ∈ scheduleRoot grammar input fuel) :
    DerivesWithin grammar input fuel grammar.start 0 input.length
        candidate.tree ∧
      GuardCorrespondence.CertificateReplays grammar input
        candidate.certificate grammar.start 0 input.length candidate.tree := by
  obtain ⟨categoryMember, stopAccepted⟩ := List.mem_filter.mp member
  have stopEq : candidate.stop = input.length := by
    simpa only [decide_eq_true_eq] using stopAccepted
  obtain ⟨derivation, replay⟩ := scheduleCategory_sound categoryMember
  rw [stopEq] at derivation replay
  exact ⟨derivation, replay⟩

theorem scheduleRoot_complete
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input : List Codepoint} {fuel : Nat} {tree : ParseTree}
    (derivation : DerivesWithin grammar input fuel grammar.start
      0 input.length tree) :
    ∃ candidate,
      candidate ∈ scheduleRoot grammar input fuel ∧
      candidate.tree = tree ∧
      GuardCorrespondence.CertificateReplays grammar input
        candidate.certificate grammar.start 0 input.length tree := by
  obtain ⟨candidate, categoryMember, stopEq, treeEq, replay⟩ :=
    scheduleCategory_complete derivation
  have stopAccepted : decide (candidate.stop = input.length) = true := by
    simpa only [decide_eq_true_eq] using stopEq
  refine ⟨candidate, List.mem_filter.mpr ⟨categoryMember, stopAccepted⟩,
    treeEq, ?_⟩
  simpa [treeEq] using replay

theorem compiledDerivation_eventually_scheduled
    {grammar : GuardCorrespondence.CompiledGrammar}
    {input category start stop tree}
    (derivation : GuardCorrespondence.CompiledDerivesAt grammar input
      category start stop tree) :
    ∃ fuel candidate,
      candidate ∈ scheduleCategory grammar input fuel category start ∧
      candidate.stop = stop ∧ candidate.tree = tree ∧
      GuardCorrespondence.CertificateReplays grammar input
        candidate.certificate category start stop tree := by
  obtain ⟨fuel, bounded⟩ := compiledDerivation_hasBound derivation
  obtain ⟨candidate, member, stopEq, treeEq, replay⟩ :=
    scheduleCategory_complete bounded
  exact ⟨fuel, candidate, member, stopEq, treeEq, replay⟩

theorem sourceDerivation_eventually_scheduled
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint} {tree : ParseTree}
    (derivation : SourceDerivesAt presentation input presentation.start
      0 input.length tree) :
    ∃ fuel candidate,
      candidate ∈ scheduleRoot (GuardCorrespondence.compile presentation)
        input fuel ∧
      candidate.tree = tree ∧
      GuardCorrespondence.RootCertificateReplays presentation input
        candidate.certificate tree := by
  have compiled := GuardCorrespondence.compile_preserves derivation
  obtain ⟨fuel, bounded⟩ := compiledDerivation_hasBound compiled
  obtain ⟨candidate, member, treeEq, replay⟩ :=
    scheduleRoot_complete bounded
  have spans := certificateReplays_spans replay
  refine ⟨fuel, candidate, member, treeEq, ?_⟩
  constructor
  · simpa [GuardCorrespondence.compile, treeEq] using replay
  · exact spans

def scheduleForest (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (fuel : Nat) : Forest :=
  packCertificates
    ((scheduleRoot grammar input fuel).map fun candidate => candidate.certificate)

theorem sourceDerivation_hasScheduledPackedWitness
    {presentation : GuardCorrespondence.SourcePresentation}
    {input : List Codepoint} {tree : ParseTree}
    (derivation : SourceDerivesAt presentation input presentation.start
      0 input.length tree) :
    ∃ fuel certificate,
      PackedReplays
        (scheduleForest (GuardCorrespondence.compile presentation) input fuel)
        presentation input certificate tree := by
  obtain ⟨fuel, candidate, member, treeEq, replay⟩ :=
    sourceDerivation_eventually_scheduled derivation
  refine ⟨fuel, candidate.certificate, ?_, ?_⟩
  · apply member_packCertificates_unfolds
      (certificates :=
        (scheduleRoot (GuardCorrespondence.compile presentation) input fuel).map
          fun result => result.certificate)
    · exact List.mem_map.mpr ⟨candidate, member, rfl⟩
    · exact certificateReplays_hasKey replay.1
  · simpa [treeEq] using replay

def boundedResults (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (fuel : Nat) : Set ParseTree :=
  { tree | DerivesWithin grammar input fuel grammar.start 0 input.length tree }

def scheduledResults (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (fuel : Nat) : Set ParseTree :=
  { tree | ∃ candidate,
      candidate ∈ scheduleRoot grammar input fuel ∧ candidate.tree = tree }

theorem bounded_result_set_agreement
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (fuel : Nat) :
    scheduledResults grammar input fuel = boundedResults grammar input fuel := by
  ext tree
  constructor
  · rintro ⟨candidate, member, rfl⟩
    exact (scheduleRoot_sound member).1
  · intro derivation
    obtain ⟨candidate, member, treeEq, replay⟩ :=
      scheduleRoot_complete derivation
    exact ⟨candidate, member, treeEq⟩

def Ambiguous (results : Set ParseTree) : Prop :=
  ∃ first ∈ results, ∃ second ∈ results, first ≠ second

theorem bounded_ambiguity_agreement
    (grammar : GuardCorrespondence.CompiledGrammar)
    (input : List Codepoint) (fuel : Nat) :
    Ambiguous (scheduledResults grammar input fuel) ↔
      Ambiguous (boundedResults grammar input fuel) := by
  rw [bounded_result_set_agreement]

def BoundedComplete (forest : Forest)
    (presentation : GuardCorrespondence.SourcePresentation)
    (input : List Codepoint) (fuel : Nat) : Prop :=
  ∀ tree,
    DerivesWithin (GuardCorrespondence.compile presentation) input fuel
      presentation.start 0 input.length tree →
    ∃ certificate, PackedReplays forest presentation input certificate tree

theorem scheduleForest_bounded_complete
    (presentation : GuardCorrespondence.SourcePresentation)
    (input : List Codepoint) (fuel : Nat) :
    BoundedComplete
      (scheduleForest (GuardCorrespondence.compile presentation) input fuel)
      presentation input fuel := by
  intro tree derivation
  obtain ⟨candidate, member, treeEq, replay⟩ :=
    scheduleRoot_complete derivation
  have spans := certificateReplays_spans replay
  have hasKey := certificateReplays_hasKey replay
  refine ⟨candidate.certificate, ?_, ?_⟩
  · apply member_packCertificates_unfolds
      (certificates :=
        (scheduleRoot (GuardCorrespondence.compile presentation) input fuel).map
          fun result => result.certificate)
    · exact List.mem_map.mpr ⟨candidate, member, rfl⟩
    · exact hasKey
  · constructor
    · simpa [GuardCorrespondence.compile, treeEq] using replay
    · exact spans

/-! ## Executable scheduler controls -/

def schedulerToyPresentation : GuardCorrespondence.SourcePresentation :=
  { start := "start"
    rules := [
      { sourceRule := "left", category := "start",
        symbols := [.exact 97], guards := [.atEnd] },
      { sourceRule := "right", category := "start",
        symbols := [.exact 97], guards := [.atEnd] }] }

def schedulerToyGrammar : GuardCorrespondence.CompiledGrammar :=
  GuardCorrespondence.compile schedulerToyPresentation

theorem zeroFuel_hasNoResults :
    (scheduleRoot schedulerToyGrammar [97] 0).length = 0 := by
  decide

theorem toySchedule_hasTwoResults :
    (scheduleRoot schedulerToyGrammar [97] 1).length = 2 := by
  decide

theorem toySchedule_rejectsTrailingInput :
    (scheduleRoot schedulerToyGrammar [97, 98] 1).length = 0 := by
  decide

theorem toyScheduleForest_sharesRoot :
    (scheduleForest schedulerToyGrammar [97] 1).roots.length = 1 := by
  decide

theorem toyScheduleForest_retainsAlternatives :
    (scheduleForest schedulerToyGrammar [97] 1).families.length = 2 := by
  decide

def leftRecursivePresentation : GuardCorrespondence.SourcePresentation :=
  { start := "start"
    rules := [
      { sourceRule := "grow", category := "start",
        symbols := [.call "start", .exact 97], guards := [.atEnd] },
      { sourceRule := "base", category := "start",
        symbols := [.exact 97], guards := [] }] }

def leftRecursiveGrammar : GuardCorrespondence.CompiledGrammar :=
  GuardCorrespondence.compile leftRecursivePresentation

theorem productiveLeftRecursion_needsEnoughFuel :
    (scheduleRoot leftRecursiveGrammar [97, 97] 1).length = 0 := by
  decide

theorem productiveLeftRecursion_acceptsAtDepthTwo :
    (scheduleRoot leftRecursiveGrammar [97, 97] 2).length = 1 := by
  decide

end Mettapedia.GSLT.Parsing.BoundedScheduler
