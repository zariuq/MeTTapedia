import Mettapedia.Languages.MeTTa.SpaceTheory.FirstOrderForwarding
import Mettapedia.GSLT.Contracts.PaperRhoOuterBag

/-!
# Direct forwarding and the rho calculus

The worked native rule uses two closed literal channels and a fixed
receiver that releases its payload. The proof compares its literal
test to the paper's name equality, and reflects an isolated paper
communication back to the actual first-order match. It does not treat
general quoted processes as literal channels or general input bodies
as first-order forwarding templates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.RhoDirectComparison

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Contracts.PaperRho
open PatternBoundary (encodeName encodeProcess)
open Adequacy (canonicalForm canonicalize_send canonicalize_receive canonicalize_encodeName_eq_iff)
open OuterBag (outer needed forwarder)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (canonicalize)
open FirstOrderForwarding (request send wait declaration)

def channel : Bool → Atom
  | false => .symbol "cold"
  | true => .symbol "warm"

def namedChannel : Bool → Name
  | false => .quote .zero
  | true => .quote (.send (.quote .zero) .zero)

def packet (data : Bool) : Atom := .expression [.symbol "datum", channel data]
def code (data : Bool) : Process := .drop (namedChannel data)

theorem channel_scoped (name : Bool) : ScopedName 0 (namedChannel name) := by
  cases name
  · exact .literal .zero
  · exact .literal (.send (.literal .zero) .zero)

theorem name_test_exact (offered waiting : Bool) :
    channel offered = channel waiting ↔ NameEquivalence (namedChannel offered) (namedChannel waiting) := by
  have distinct : ¬NameEquivalence (namedChannel false) (namedChannel true) := by
    intro same
    have witness := (canonicalize_encodeName_eq_iff _ _).mpr same
    exact (by decide +kernel :
      canonicalize rhoReflectivePresentation (encodeName (namedChannel false)) ≠
      canonicalize rhoReflectivePresentation (encodeName (namedChannel true))) witness
  cases offered <;> cases waiting
  · exact ⟨fun _ => .refl _, fun _ => rfl⟩
  · exact ⟨fun bad => ((by decide : channel false ≠ channel true) bad).elim, fun same => (distinct same).elim⟩
  · exact ⟨fun bad => ((by decide : channel true ≠ channel false) bad).elim, fun same => (distinct same.symm).elim⟩
  · exact ⟨fun _ => .refl _, fun _ => rfl⟩

private theorem send_name_of_equal {left right : Name} {p q : Process}
    (same : canonicalForm (.send left p) = canonicalForm (.send right q)) :
    NameEquivalence left right := by
  change canonicalize rhoReflectivePresentation (encodeProcess (.send left p)) =
    canonicalize rhoReflectivePresentation (encodeProcess (.send right q)) at same
  rw [canonicalize_send, canonicalize_send] at same
  exact (canonicalize_encodeName_eq_iff left right).mp ((List.cons.inj (Pattern.apply.inj same).2).1)

private theorem receive_name_of_equal {left right : Name} {p q : Process}
    (same : canonicalForm (.receive left p) = canonicalForm (.receive right q)) :
    NameEquivalence left right := by
  change canonicalize rhoReflectivePresentation (encodeProcess (.receive left p)) =
    canonicalize rhoReflectivePresentation (encodeProcess (.receive right q)) at same
  rw [canonicalize_receive, canonicalize_receive] at same
  exact (canonicalize_encodeName_eq_iff left right).mp ((List.cons.inj (Pattern.apply.inj same).2).1)

private theorem send_not_receive (left right : Name) (p q : Process) :
    canonicalForm (.send left p) ≠ canonicalForm (.receive right q) := by
  change canonicalize rhoReflectivePresentation (encodeProcess (.send left p)) ≠
    canonicalize rhoReflectivePresentation (encodeProcess (.receive right q))
  rw [canonicalize_send, canonicalize_receive]
  intro impossible
  have tags := (Pattern.apply.inj impossible).1
  exact (by decide : "POutput" ≠ "PInput") tags

theorem isolated_pair_needs_agreeing_names {sent expected : Name} {data body after : Process}
    (fired : Reduction (.par (.send sent data) (.receive expected body)) after) :
    NameEquivalence sent expected := by
  obtain ⟨offered, waiting, payload, target, frame, _, _, _, _, transfer, focus, _⟩ :=
    (OuterBag.reduction_iff_outer _ _).mp fired
  have outgoing : canonicalForm (.send offered payload) ∈ outer (.par (.send sent data) (.receive expected body)) := by
    rw [focus]; simp [needed]
  have incoming : canonicalForm (.receive waiting target) ∈ outer (.par (.send sent data) (.receive expected body)) := by
    rw [focus]; simp [needed]
  simp only [OuterBag.outer_par, OuterBag.outer_send, OuterBag.outer_receive, Multiset.mem_add,
    Multiset.mem_singleton] at outgoing incoming
  have fst := outgoing.resolve_right (send_not_receive _ _ _ _)
  have snd := incoming.resolve_left (fun no => send_not_receive _ _ _ _ no.symm)
  exact (send_name_of_equal fst).symm.trans (transfer.trans (receive_name_of_equal snd))

theorem literal_forwarding_exact (offered waiting datum : Bool) :
    ModuleTheories.InstanceOf declaration
      (request (send (channel offered) (packet datum)) (wait (channel waiting))) (packet datum) ↔
      Reduction (.par (.send (namedChannel offered) (code datum)) (forwarder (namedChannel waiting))) (code datum) := by
  rw [FirstOrderForwarding.one_definition_matches_iff]
  constructor
  · rintro ⟨same, _⟩
    exact .comm (channel_scoped offered) (channel_scoped waiting) (.drop (channel_scoped datum))
      (.drop (.bound (by decide))) ((name_test_exact offered waiting).mp same) (.drop_hit (.refl _))
  · intro admitted
    exact ⟨(name_test_exact offered waiting).mpr (isolated_pair_needs_agreeing_names admitted), rfl⟩

/-- In a space, the extra send remains a separate occurrence. In the
paper, it remains a separate unguarded parallel component. -/
theorem duplicate_literal_send_one_receiver (name datum : Bool) :
    FirstOrderForwarding.Step
      ({send (channel name) (packet datum)} + {wait (channel name)} + {send (channel name) (packet datum)})
      ({packet datum} + {send (channel name) (packet datum)}) ∧
    Reduction (.par (.par (.send (namedChannel name) (code datum)) (forwarder (namedChannel name)))
      (.send (namedChannel name) (code datum))) (.par (code datum) (.send (namedChannel name) (code datum))) :=
  ⟨FirstOrderForwarding.duplicated_send_consumes_only_one _ _,
    OuterBag.forward_closed _ _ _ _ (channel_scoped name) (channel_scoped name) (.drop (channel_scoped datum)) (.refl _)⟩

theorem literal_channels_differ :
    ¬Reduction (.par (.send (namedChannel false) (code false)) (forwarder (namedChannel true))) (code false) := by
  intro fired
  have agrees := (name_test_exact false true).mpr (isolated_pair_needs_agreeing_names fired)
  exact (by decide : channel false ≠ channel true) agrees

private def old : Atom := .symbol "frost"
private def present : Atom := channel false
private def equality : Atom := (Atoms.Content.equation .rightward old present []).syntax

/-- A written ground alias can let the saturated rule enter by a common
spelling. The raw nonlinear matcher still refuses the two unequal
spellings. No quoted-process equality is derived from such an alias. -/
theorem written_alias_licenses_the_literal_call (payload : Atom) :
    ¬ModuleTheories.InstanceOf declaration (request (send old payload) (wait present)) payload ∧
      (ModuleTheories.theory (fun _ _ => False) [declaration, equality]).Step
        (request (send old payload) (wait present)) payload := by
  refine ⟨FirstOrderForwarding.different_channel_fails (by decide), ?_⟩
  have relates : AtomEquations.Equivalent [declaration, equality] old present :=
    AtomEquations.authored ⟨.rightward, present, [], List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self⟩
  let position := AtomEquations.Context.child [.symbol "communicate"]
    (.child [.symbol "send"] .hole [payload]) [wait present]
  have transport : AtomEquations.Equivalent [declaration, equality]
      (request (send old payload) (wait present)) (request (send present payload) (wait present)) :=
    AtomEquations.fill_equivalent position relates
  exact ⟨_, _, transport, Or.inr ⟨declaration, List.mem_cons_self,
    (FirstOrderForwarding.one_definition_matches_iff _ _ _ _).mpr ⟨rfl, rfl⟩⟩, .refl _⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.RhoDirectComparison
