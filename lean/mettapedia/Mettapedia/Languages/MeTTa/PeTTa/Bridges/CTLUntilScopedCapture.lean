import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedCapture

/-!
# Uniform typed capture through actual query preparation

Every phase starts from its reached caller and retains the fresh handle
equation. The current mixed-store decoder and matcher derive the full ordered
captured list; successful capture is not supplied as an oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedCapture

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore
open CTLUntilSourceRows (number located)
open ClosedOnceQueryFrame (FreshFor)

def frontierCode (formula round next : String) : Atom :=
  .expression [.symbol "fr", .var formula, .var round, .var next]

theorem pattern_name_retained (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (name : String) (member : name ∈ (encode pattern).freeVars) :
    name ∈ (ScopedMatchPreparation.entry caller destination handle pattern body).support := by
  apply GuardedInsertionPairSource.goal_atom_support _ (ScopedMatchPreparation.source handle pattern body) name
    (by simp [ScopedMatchPreparation.entry, Goal.atoms])
  rw [ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
  exact ⟨pattern, by simp, member⟩

theorem body_name_retained (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (name : String) (member : name ∈ (encode body).freeVars) :
    name ∈ (ScopedMatchPreparation.entry caller destination handle pattern body).support := by
  apply GuardedInsertionPairSource.goal_atom_support _ (ScopedMatchPreparation.source handle pattern body) name
    (by simp [ScopedMatchPreparation.entry, Goal.atoms])
  rw [ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
  exact ⟨body, by simp, member⟩

theorem frontier_pattern_read {Label : Type} (codec : Codec Label) (label : Label) (round : Nat)
    (formulaName roundName nextName : String) (environment : Environment)
    (formulaRead : read environment (.var formulaName) = codec.encode label)
    (roundRead : read environment (.var roundName) = number round)
    (nextRead : read environment (.var nextName) = .var nextName) :
    read environment (frontierCode formulaName roundName nextName) = frontierPattern codec label round nextName := by
  simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at formulaRead roundRead nextRead
  simp only [frontierCode, frontierPattern, read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation,
    List.map_cons, List.map_nil, formulaRead, roundRead, nextRead]

theorem frontier_capture {Context Label : Type} [DecidableEq Label] (codec : Codec Label)
    (program : SpaceSemantics.Program) (handle : NamedSpaces.Handle) (label : Label) (round : Nat)
    (formulaName roundName nextName : String) (body destination : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (principal : Environment) (atoms : List Atom) (rows : List (Row Label))
    (resolved : resolve caller.bindings = some principal)
    (formulaRead : read principal (.var formulaName) = codec.encode label)
    (roundRead : read principal (.var roundName) = number round)
    (nextFresh : FreshFor nextName caller.bindings)
    (bodyCode : ConstantQuerySource.isScalar body = false)
    (snapshot : state.world.state.read handle = some atoms) (decoded : decodeRows codec atoms = some rows) :
    let pattern := frontierCode formulaName roundName nextName
    let ready := ScopedMatchPreparation.ready caller destination handle pattern body
    (ScopedMatchEntry.execute program handle pattern body destination caller state context origins pending).budget = 4 ∧
      ∃ selected, (ScopedMatchEntry.execute program handle pattern body destination caller state context origins pending).result = .captured selected ∧
        selected.choices = (located (frontSelect label round) 0 rows).map
          (fun entry => (entry.1, ScopedQuerySource.bodyControl ready [(nextName, number entry.2)] body destination caller.goals)) := by
  dsimp only
  let pattern := frontierCode formulaName roundName nextName
  let ready := ScopedMatchPreparation.ready caller destination handle pattern body
  obtain ⟨environment, prepared⟩ := resolve_complete
    (ScopedMatchPreparation.ready_consistent caller destination handle pattern body ⟨principal, resolve_sound resolved⟩)
  have formulaAfter := ScopedMatchPreparation.closed_reading caller destination handle pattern body principal environment
    (.var formulaName) (codec.encode label) resolved prepared formulaRead (LiteralQuerySource.read_literal _ (codec.literal label))
  have roundAfter := ScopedMatchPreparation.closed_reading caller destination handle pattern body principal environment
    (.var roundName) (number round) resolved prepared roundRead (CTLUntilSourceCapture.number_closed round)
  have nextRetained := pattern_name_retained caller destination handle pattern body nextName (by
    dsimp only [pattern]
    rw [frontierCode, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var nextName, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩)
  have fresh := ScopedMatchPreparation.retained_fresh caller destination handle pattern body nextName nextFresh nextRetained
  have nextAfter := ClosedOnceQueryFrame.fresh_read ready.bindings nextName environment fresh prepared
  have reading := frontier_pattern_read codec label round formulaName roundName nextName environment formulaAfter roundAfter nextAfter
  obtain ⟨actual, admitted⟩ := decode_rows_sound codec atoms rows decoded
  have captured := CTLUntilMixedCapture.single_capture codec (frontSelect label round) _ nextName
    (frontier_match codec label round nextName) ready environment nextName body destination caller.goals 0 rows admitted prepared nextAfter
  apply ScopedMatchEntry.captured_of_checks program handle pattern body destination caller state context origins pending
    principal environment atoms _ resolved prepared snapshot
  · rw [reading, ← actual]
    exact rows_ready codec "fr" _ (by simp) rows admitted
  · simp [ScopedQuerySource.fused, bodyCode]
  · rw [reading, ← actual]
    exact captured

theorem edge_pattern_read (nextName priorName : String) (next : Nat) (environment : Environment)
    (nextRead : read environment (.var nextName) = number next)
    (priorRead : read environment (.var priorName) = .var priorName) :
    read environment (CTLUntilSourceRows.reversePattern nextName priorName) = CTLUntilSourceCapture.preparedEdge next priorName := by
  simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at nextRead priorRead
  simp only [CTLUntilSourceRows.reversePattern, CTLUntilSourceCapture.preparedEdge, read_eq_applyTypeValuation,
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_cons, List.map_nil, nextRead, priorRead]

theorem edge_capture {Context Label : Type} (codec : Codec Label)
    (program : SpaceSemantics.Program) (handle : NamedSpaces.Handle) (next : Nat)
    (nextName priorName : String) (body destination : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (principal : Environment) (atoms : List Atom) (rows : List (Row Label))
    (resolved : resolve caller.bindings = some principal)
    (nextRead : read principal (.var nextName) = number next) (priorFresh : FreshFor priorName caller.bindings)
    (bodyCode : ConstantQuerySource.isScalar body = false)
    (snapshot : state.world.state.read handle = some atoms) (decoded : decodeRows codec atoms = some rows) :
    let pattern := CTLUntilSourceRows.reversePattern nextName priorName
    let ready := ScopedMatchPreparation.ready caller destination handle pattern body
    (ScopedMatchEntry.execute program handle pattern body destination caller state context origins pending).budget = 4 ∧
      ∃ selected, (ScopedMatchEntry.execute program handle pattern body destination caller state context origins pending).result = .captured selected ∧
        selected.choices = (located (edgeSelect next) 0 rows).map
          (fun entry => (entry.1, ScopedQuerySource.bodyControl ready [(priorName, number entry.2)] body destination caller.goals)) := by
  dsimp only
  let pattern := CTLUntilSourceRows.reversePattern nextName priorName
  let ready := ScopedMatchPreparation.ready caller destination handle pattern body
  obtain ⟨environment, prepared⟩ := resolve_complete
    (ScopedMatchPreparation.ready_consistent caller destination handle pattern body ⟨principal, resolve_sound resolved⟩)
  have nextAfter := ScopedMatchPreparation.closed_reading caller destination handle pattern body principal environment
    (.var nextName) (number next) resolved prepared nextRead (CTLUntilSourceCapture.number_closed next)
  have priorRetained := pattern_name_retained caller destination handle pattern body priorName (by
    dsimp only [pattern]
    rw [CTLUntilSourceRows.reversePattern, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var priorName, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩)
  have fresh := ScopedMatchPreparation.retained_fresh caller destination handle pattern body priorName priorFresh priorRetained
  have priorAfter := ClosedOnceQueryFrame.fresh_read ready.bindings priorName environment fresh prepared
  have reading := edge_pattern_read nextName priorName next environment nextAfter priorAfter
  obtain ⟨actual, admitted⟩ := decode_rows_sound codec atoms rows decoded
  have captured := CTLUntilMixedCapture.single_capture codec (edgeSelect next) _ priorName
    (CTLUntilMixedCapture.prepared_edge_match codec next priorName) ready environment priorName body destination caller.goals 0 rows admitted prepared priorAfter
  apply ScopedMatchEntry.captured_of_checks program handle pattern body destination caller state context origins pending
    principal environment atoms _ resolved prepared snapshot
  · rw [reading, ← actual]
    exact rows_ready codec "rt" _ (by simp) rows admitted
  · simp [ScopedQuerySource.fused, bodyCode]
  · rw [reading, ← actual]
    exact captured

theorem satisfaction_pattern_read {Label : Type} (codec : Codec Label) (label : Label) (node : Nat)
    (labelName nodeName : String) (environment : Environment)
    (labelRead : read environment (.var labelName) = codec.encode label)
    (nodeRead : read environment (.var nodeName) = number node) :
    read environment (NamedPresenceSource.patternCode labelName nodeName) =
      CTLUntilMixedCapture.preparedSatisfaction codec label node := by
  simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at labelRead nodeRead
  simp only [NamedPresenceSource.patternCode, CTLUntilMixedCapture.preparedSatisfaction, read_eq_applyTypeValuation,
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_cons, List.map_nil, labelRead, nodeRead]

theorem satisfaction_capture {Context Label : Type} [DecidableEq Label] (codec : Codec Label)
    (program : SpaceSemantics.Program) (handle : NamedSpaces.Handle) (label : Label) (node : Nat)
    (labelName nodeName : String) (body destination : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (principal : Environment) (atoms : List Atom) (rows : List (Row Label))
    (resolved : resolve caller.bindings = some principal)
    (labelRead : read principal (.var labelName) = codec.encode label)
    (nodeRead : read principal (.var nodeName) = number node)
    (bodyCode : ConstantQuerySource.isScalar body = false)
    (snapshot : state.world.state.read handle = some atoms) (decoded : decodeRows codec atoms = some rows) :
    let pattern := NamedPresenceSource.patternCode labelName nodeName
    let ready := ScopedMatchPreparation.ready caller destination handle pattern body
    (ScopedMatchEntry.execute program handle pattern body destination caller state context origins pending).budget = 4 ∧
      ∃ selected, (ScopedMatchEntry.execute program handle pattern body destination caller state context origins pending).result = .captured selected ∧
        selected.choices = (located (satSelect label node) 0 rows).map
          (fun entry => (entry.1, ScopedQuerySource.bodyControl ready [] body destination caller.goals)) := by
  dsimp only
  let pattern := NamedPresenceSource.patternCode labelName nodeName
  let ready := ScopedMatchPreparation.ready caller destination handle pattern body
  obtain ⟨environment, prepared⟩ := resolve_complete
    (ScopedMatchPreparation.ready_consistent caller destination handle pattern body ⟨principal, resolve_sound resolved⟩)
  have labelAfter := ScopedMatchPreparation.closed_reading caller destination handle pattern body principal environment
    (.var labelName) (codec.encode label) resolved prepared labelRead (LiteralQuerySource.read_literal _ (codec.literal label))
  have nodeAfter := ScopedMatchPreparation.closed_reading caller destination handle pattern body principal environment
    (.var nodeName) (number node) resolved prepared nodeRead (CTLUntilSourceCapture.number_closed node)
  have reading := satisfaction_pattern_read codec label node labelName nodeName environment labelAfter nodeAfter
  obtain ⟨actual, admitted⟩ := decode_rows_sound codec atoms rows decoded
  have captured := CTLUntilMixedCapture.satisfaction_capture codec label node ready body destination caller.goals 0 rows admitted
    ⟨environment, resolve_sound prepared⟩
  apply ScopedMatchEntry.captured_of_checks program handle pattern body destination caller state context origins pending
    principal environment atoms _ resolved prepared snapshot
  · rw [reading, ← actual]
    exact rows_ready codec "sat" _ (by simp) rows admitted
  · simp [ScopedQuerySource.fused, bodyCode]
  · rw [reading, ← actual]
    exact captured

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedCapture
