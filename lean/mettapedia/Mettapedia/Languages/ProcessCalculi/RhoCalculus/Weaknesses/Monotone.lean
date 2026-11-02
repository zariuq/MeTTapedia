import Mettapedia.GSLT.Coordination.ConsensusNumbers.Absence

/-!
# In rho, a neighbour can only add behaviour

Whatever a rho process can show, it can still show with any process beside it: COMM still fires
in a larger parallel composition, and an output stays visible (`weakBarb_par`). So a feature whose
whole point is that a neighbour can switch it off has no compositional rho encoding
(`rho_no_encoding_of_disableable`). This is one theorem behind several missing features:

* **firing now or else** (`TryReceive`): Prime's `else`, Go's `select` with `default`, Erlang's
  `receive … after 0`, Linda's `inp`. Alone it falls back; beside a message it never does
  (`tryReceive_falls_back`, `tryReceive_blocked`, `rho_cannot_encode_tryReceive`);
* **priority** (`Priority`): serve the low-priority queue only when the high one is empty
  (`priority_serves_low`, `priority_blocked`, `rho_cannot_encode_priority`);
* **exact counts** (`ExactlyOne`): Prime's `unique`, "close the auction when there is exactly one
  bid" (`exactlyOne_sells`, `exactlyOne_blocked`, `rho_cannot_encode_exactlyOne`);
* **absence** itself, negation as failure and inhibitor arcs: the existing
  `ConsensusNumbers.rho_cannot_encode_absence`.

Each source here is a set of steps over bags (`OccurrenceCommits.Equivalence.Rule`); the barb is
a weak barb (some run shows the atom); an encoding is compositional when it sends a union of bags
to a parallel composition. The step language expresses every one of these features: they are the
source languages themselves.

What the theorem does not exclude: an encoding that keeps the whole configuration in one message
(`ConsensusNumbers.Controls.whole_configuration_encoding`), which gives up running a space one
part at a time.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Monotone

open Mettapedia.GSLT.Coordination.ConsensusNumbers (WeakBarb no_parallel_encoding rhoPar HasOutput
  reflTransGen_par)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Reduces)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Monotonicity of rho -/

/-- One rho reduction, as a proposition. -/
def RhoStep (P Q : Pattern) : Prop := Nonempty (P ⇝ Q)

/-- **Composition only adds behaviour.** A weak output barb of `P` is a weak output barb of `P`
beside any `Q`. -/
theorem weakBarb_par (n : Pattern) {P : Pattern} (Q : Pattern)
    (h : WeakBarb RhoStep (HasOutput n) P) : WeakBarb RhoStep (HasOutput n) (rhoPar P Q) := by
  obtain ⟨P', run, barb⟩ := h
  exact ⟨rhoPar P' Q, reflTransGen_par (fun _ _ u ⟨step⟩ => ⟨Reduces.par (rest := [u]) step⟩) Q run,
    HasOutput.inBag (by simp) barb⟩

/-- **No compositional rho encoding of a feature a neighbour can switch off.** If a source
configuration `P` can show the barb and `P` beside `Q` cannot, no encoding that sends `P` beside `Q`
to the parallel composition of the images is complete and sound for weak barbs. -/
theorem rho_no_encoding_of_disableable {S : Type*} (step : S → S → Prop) (barb : S → Prop)
    (comp : S → S → S) (n : Pattern) {P Q : S} (fires : WeakBarb step barb P)
    (blocked : ¬ WeakBarb step barb (comp P Q)) (enc : S → Pattern)
    (compositional : enc (comp P Q) = rhoPar (enc P) (enc Q))
    (complete : ∀ s, WeakBarb step barb s → WeakBarb RhoStep (HasOutput n) (enc s))
    (sound : ∀ s, WeakBarb RhoStep (HasOutput n) (enc s) → WeakBarb step barb s) : False :=
  no_parallel_encoding (tgtPar := rhoPar)
    (fun _ _ u ⟨step⟩ => ⟨Reduces.par (rest := [u]) step⟩)
    (fun t u barb => HasOutput.inBag (p := t) (by simp) barb)
    fires blocked enc ⟨_, compositional⟩ complete sound

/-! ## Source languages with a feature a neighbour can switch off -/

section Sources

variable {A : Type} [DecidableEq A]

/-- The weak barb of a bag language: some run reaches a bag holding the atom. -/
def Shows (Γ : Rule A → Prop) (x : A) (M : Multiset A) : Prop :=
  WeakBarb (Reduces Γ) (fun M' => x ∈ M') M

/-- Reachable bags stay in a set closed under the steps, so a barb outside it is never shown. -/
theorem not_shows_of_invariant (Γ : Rule A → Prop) (x : A) (Inv : Multiset A → Prop)
    {M : Multiset A} (start : Inv M) (closed : ∀ N N', Inv N → Reduces Γ N N' → Inv N')
    (absent : ∀ N, Inv N → x ∉ N) : ¬ Shows Γ x M := by
  rintro ⟨M', run, barb⟩
  have : Inv M' := by
    clear barb
    induction run with
    | refl => exact start
    | tail _ last ih => exact closed _ _ ih last
  exact absent _ this barb

end Sources

/-! ### Firing now or else -/

/-- Atoms of a try-receive. -/
inductive TryAtom where
  | try_ | msg | got | fallback
  deriving DecidableEq

/-- Take a message if one is there. -/
def tryTake : Rule TryAtom := ⟨{.try_, .msg}, 0, {.got}, fun _ => false⟩

/-- Otherwise fall back: fires only when no message is present. -/
def tryElse : Rule TryAtom := ⟨{.try_}, 0, {.fallback}, fun a => decide (a = .msg)⟩

def TryReceive (ρ : Rule TryAtom) : Prop := ρ = tryTake ∨ ρ = tryElse

/-- **Alone, a try-receive falls back.** -/
theorem tryReceive_falls_back : Shows TryReceive .fallback {.try_} :=
  ⟨{.fallback}, .single ⟨tryElse, Or.inr rfl, ⟨by decide, by decide⟩, by decide⟩, by simp⟩

/-- **Beside a message it never falls back.** -/
theorem tryReceive_blocked : ¬ Shows TryReceive .fallback ({.try_} + {.msg}) := by
  apply not_shows_of_invariant TryReceive .fallback
    (fun N => N = {.try_} + {.msg} ∨ N = {.got}) (Or.inl rfl)
  · rintro N N' (rfl | rfl) ⟨ρ, (rfl | rfl), ⟨le, avoids⟩, rfl⟩
    · exact Or.inr (by decide)
    · exact absurd (avoids .msg (by decide)) (by decide)
    · exact absurd le (by decide)
    · exact absurd le (by decide)
  · rintro N (rfl | rfl) <;> decide

/-- **Rho cannot encode a try-receive compositionally.** -/
theorem rho_cannot_encode_tryReceive (n : Pattern) (enc : Multiset TryAtom → Pattern)
    (compositional : enc ({.try_} + {.msg}) = rhoPar (enc {.try_}) (enc {.msg}))
    (complete : ∀ s, Shows TryReceive .fallback s → WeakBarb RhoStep (HasOutput n) (enc s))
    (sound : ∀ s, WeakBarb RhoStep (HasOutput n) (enc s) → Shows TryReceive .fallback s) :
    False :=
  rho_no_encoding_of_disableable (Reduces TryReceive) (fun M => TryAtom.fallback ∈ M) (· + ·) n
    tryReceive_falls_back tryReceive_blocked enc compositional complete sound

/-! ### Priority -/

/-- Atoms of a two-queue server. -/
inductive PrioAtom where
  | server | hi | lo | servedHi | servedLo
  deriving DecidableEq

def serveHi : Rule PrioAtom := ⟨{.server, .hi}, 0, {.servedHi}, fun _ => false⟩

/-- Serve the low queue only when the high queue is empty. -/
def serveLo : Rule PrioAtom := ⟨{.server, .lo}, 0, {.servedLo}, fun a => decide (a = .hi)⟩

def Priority (ρ : Rule PrioAtom) : Prop := ρ = serveHi ∨ ρ = serveLo

/-- **With only low-priority work, it is served.** -/
theorem priority_serves_low : Shows Priority .servedLo ({.server, .lo}) :=
  ⟨{.servedLo}, .single ⟨serveLo, Or.inr rfl, ⟨by decide, by decide⟩, by decide⟩, by simp⟩

/-- **Beside high-priority work it never is.** -/
theorem priority_blocked : ¬ Shows Priority .servedLo ({.server, .lo} + {.hi}) := by
  apply not_shows_of_invariant Priority .servedLo
    (fun N => N = {.server, .lo} + {.hi} ∨ N = {.lo, .servedHi}) (Or.inl rfl)
  · rintro N N' (rfl | rfl) ⟨ρ, (rfl | rfl), ⟨le, avoids⟩, rfl⟩
    · exact Or.inr (by decide)
    · exact absurd (avoids .hi (by decide)) (by decide)
    · exact absurd le (by decide)
    · exact absurd le (by decide)
  · rintro N (rfl | rfl) <;> decide

/-- **Rho cannot encode priority compositionally.** -/
theorem rho_cannot_encode_priority (n : Pattern) (enc : Multiset PrioAtom → Pattern)
    (compositional : enc ({.server, .lo} + {.hi}) = rhoPar (enc {.server, .lo}) (enc {.hi}))
    (complete : ∀ s, Shows Priority .servedLo s → WeakBarb RhoStep (HasOutput n) (enc s))
    (sound : ∀ s, WeakBarb RhoStep (HasOutput n) (enc s) → Shows Priority .servedLo s) :
    False :=
  rho_no_encoding_of_disableable (Reduces Priority) (fun M => PrioAtom.servedLo ∈ M) (· + ·) n
    priority_serves_low priority_blocked enc compositional complete sound

/-! ### Exact counts -/

/-- Atoms of an auction. -/
inductive BidAtom where
  | close | bid | sold
  deriving DecidableEq

/-- Close when there is exactly one bid: keep one bid, and no other bid may be present. -/
def sellToOnly : Rule BidAtom := ⟨{.close}, {.bid}, {.sold}, fun a => decide (a = .bid)⟩

def ExactlyOne (ρ : Rule BidAtom) : Prop := ρ = sellToOnly

/-- **With one bid, the auction closes.** -/
theorem exactlyOne_sells : Shows ExactlyOne .sold ({.close, .bid}) :=
  ⟨({.close, .bid} : Multiset BidAtom) - {.close} + {.sold},
    .single ⟨sellToOnly, rfl, ⟨by decide, by decide⟩, rfl⟩, by decide⟩

/-- **With a second bid beside it, it never closes.** -/
theorem exactlyOne_blocked : ¬ Shows ExactlyOne .sold ({.close, .bid} + {.bid}) := by
  apply not_shows_of_invariant ExactlyOne .sold (fun N => N = {.close, .bid} + {.bid}) rfl
  · rintro N N' rfl ⟨ρ, rfl, ⟨_, avoids⟩, rfl⟩
    exact absurd (avoids .bid (by decide)) (by decide)
  · rintro N rfl
    decide

/-- **Rho cannot encode an exact count compositionally.** -/
theorem rho_cannot_encode_exactlyOne (n : Pattern) (enc : Multiset BidAtom → Pattern)
    (compositional : enc ({.close, .bid} + {.bid}) = rhoPar (enc {.close, .bid}) (enc {.bid}))
    (complete : ∀ s, Shows ExactlyOne .sold s → WeakBarb RhoStep (HasOutput n) (enc s))
    (sound : ∀ s, WeakBarb RhoStep (HasOutput n) (enc s) → Shows ExactlyOne .sold s) :
    False :=
  rho_no_encoding_of_disableable (Reduces ExactlyOne) (fun M => BidAtom.sold ∈ M) (· + ·) n
    exactlyOne_sells exactlyOne_blocked enc compositional complete sound

/-! ## Controls -/

namespace Controls

/-- **Positive**: an output beside anything still shows. -/
theorem output_beside (n q u : Pattern) :
    WeakBarb RhoStep (HasOutput n) (rhoPar (.apply "POutput" [n, q]) u) :=
  weakBarb_par n u ⟨_, .refl, .here⟩

/-- **Negative**: without the condition on the rest of the bag, the fallback is not switched off
by a message, so the theorem does not apply: the unconditional fallback still fires beside it. -/
def tryElseAnyway : Rule TryAtom := ⟨{.try_}, 0, {.fallback}, fun _ => false⟩

theorem unconditional_fallback_fires_beside :
    Shows (fun ρ => ρ = tryElseAnyway) .fallback ({.try_} + {.msg}) :=
  ⟨{.msg, .fallback}, .single ⟨tryElseAnyway, rfl, ⟨by decide, fun _ _ => rfl⟩, by decide⟩,
    by simp⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Monotone
