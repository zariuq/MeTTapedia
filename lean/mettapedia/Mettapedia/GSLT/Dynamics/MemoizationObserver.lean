import Mathlib.Logic.Function.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.ByContra

/-!
# Memoization is an observer

A memo table serves a consumer `obs : X → O` through a key `key : X → K`.
The table stores, under a key, the observation of an earlier input carrying
that key, and answers later inputs with the same key from the store.  The one
law that makes this correct is descent of the consumer along the key: inputs
with equal keys must have equal observations.  This is the master non-collapse
law specialised to memoization.  The key is the observer, and the consumer
must factor through it.

Two consequences matter for a runtime.

* Eviction is a performance decision.  Restricting a coherent table to any
  subtable cannot change an answer, so a memo cap affects work and the amount
  of reuse, never correctness.  In the guarantee lattice a cap is a resource
  knob, not a soundness knob.
* A key that erases a coordinate some consumer reads is unsound, and the table
  then returns a wrong answer on a concrete two-input sequence.  The canary is
  a compact-syntax key serving a cost-bearing consumer: two inputs with the
  same erased syntax and different elaboration colour have different cost.
  The same compact key is sound for a consumer that reads only the syntax, so
  soundness is a property of the pair `(key, consumer)`, never of the key
  alone.

The law composes in the two directions a runtime needs: a key that refines a
sound key is sound, and a consumer that factors through a served consumer is
served by the same key.
-/

namespace Mettapedia.GSLT.Dynamics.MemoizationObserver

universe uX uK uO uK' uO'

variable {X : Type uX} {K : Type uK} {O : Type uO}

/-- The consumer `obs` descends along `key`: equal keys force equal
observations. -/
def SoundKey (key : X → K) (obs : X → O) : Prop :=
  ∀ x y, key x = key y → obs x = obs y

/-- A memo table is a partial map from keys to stored observations. -/
def Table (K : Type uK) (O : Type uO) := K → Option O

/-- The empty table. -/
def Table.empty : Table K O := fun _ => none

/-- A table is coherent for `(key, obs)` when every stored entry equals the
observation of every input carrying that key. -/
def Coherent (key : X → K) (obs : X → O) (table : Table K O) : Prop :=
  ∀ k o, table k = some o → ∀ x, key x = k → obs x = o

/-- `t'` is a subtable of `t`: every entry of `t'` is an entry of `t`.  Eviction
produces subtables. -/
def Subtable (t' t : Table K O) : Prop :=
  ∀ k o, t' k = some o → t k = some o

/-- Answer `x` from the table when its key is present, otherwise compute. -/
def lookupOrCompute (key : X → K) (obs : X → O) (table : Table K O) (x : X) : O :=
  match table (key x) with
  | some o => o
  | none => obs x

/-- The input was answered from the store rather than recomputed. -/
def Reused (key : X → K) (table : Table K O) (x : X) : Prop :=
  (table (key x)).isSome

section Store

variable [DecidableEq K]

/-- Store the observation of `x` under its key. -/
def store (key : X → K) (obs : X → O) (table : Table K O) (x : X) : Table K O :=
  fun k => if k = key x then some (obs x) else table k

theorem store_key (key : X → K) (obs : X → O) (table : Table K O) (x : X) :
    store key obs table x (key x) = some (obs x) := by
  simp [store]

theorem store_other (key : X → K) (obs : X → O) (table : Table K O) (x : X)
    {k : K} (hk : k ≠ key x) :
    store key obs table x k = table k := by
  simp [store, hk]

end Store

/-! ## Coherent tables answer correctly -/

theorem lookupOrCompute_eq_obs {key : X → K} {obs : X → O} {table : Table K O}
    (h : Coherent key obs table) (x : X) :
    lookupOrCompute key obs table x = obs x := by
  unfold lookupOrCompute
  cases htable : table (key x) with
  | none => rfl
  | some o => exact (h (key x) o htable x rfl).symm

theorem coherent_empty (key : X → K) (obs : X → O) :
    Coherent key obs (Table.empty : Table K O) := by
  intro k o h
  cases h

/-- Eviction preserves coherence. -/
theorem coherent_of_subtable {key : X → K} {obs : X → O} {t t' : Table K O}
    (h : Coherent key obs t) (hsub : Subtable t' t) :
    Coherent key obs t' :=
  fun k o hk x hx => h k o (hsub k o hk) x hx

/-- Eviction never changes an answer. -/
theorem lookupOrCompute_evict {key : X → K} {obs : X → O} {t t' : Table K O}
    (h : Coherent key obs t) (hsub : Subtable t' t) (x : X) :
    lookupOrCompute key obs t' x = lookupOrCompute key obs t x := by
  rw [lookupOrCompute_eq_obs (coherent_of_subtable h hsub),
    lookupOrCompute_eq_obs h]

/-- Eviction can only lose reuse: what a subtable answers from the store, the
original table answered from the store. -/
theorem reused_of_subtable {key : X → K} {t t' : Table K O}
    (hsub : Subtable t' t) {x : X} (h : Reused key t' x) :
    Reused key t x := by
  unfold Reused at *
  cases htable : t' (key x) with
  | none => simp [htable] at h
  | some o => simp [hsub (key x) o htable]

/-! ## Soundness of the key is exactly what keeps stores coherent -/

section Store

variable [DecidableEq K]

theorem coherent_store_of_soundKey {key : X → K} {obs : X → O} {table : Table K O}
    (hs : SoundKey key obs) (h : Coherent key obs table) (x : X) :
    Coherent key obs (store key obs table x) := by
  intro k o hk y hy
  by_cases hkx : k = key x
  · subst hkx
    rw [store_key] at hk
    cases hk
    exact hs y x hy
  · rw [store_other key obs table x hkx] at hk
    exact h k o hk y hy

/-- Every table reachable from the empty table by stores is coherent when the
key is sound. -/
theorem coherent_foldl_store_of_soundKey {key : X → K} {obs : X → O}
    (hs : SoundKey key obs) (inputs : List X) :
    Coherent key obs (inputs.foldl (store key obs) Table.empty) := by
  suffices h : ∀ (table : Table K O), Coherent key obs table →
      Coherent key obs (inputs.foldl (store key obs) table) from
    h Table.empty (coherent_empty key obs)
  induction inputs with
  | nil => intro table h; simpa using h
  | cons x rest ih =>
    intro table h
    simpa using ih (store key obs table x) (coherent_store_of_soundKey hs h x)

/-- An unsound key returns a wrong answer on a concrete two-input sequence:
store the first input, then look up the second. -/
theorem exists_wrong_answer_of_not_soundKey {key : X → K} {obs : X → O}
    (h : ¬ SoundKey key obs) :
    ∃ x y, lookupOrCompute key obs (store key obs Table.empty x) y ≠ obs y := by
  by_contra hall
  apply h
  intro x y hxy
  have hcorrect : lookupOrCompute key obs (store key obs Table.empty x) y = obs y := by
    by_contra hne
    exact hall ⟨x, y, hne⟩
  unfold lookupOrCompute at hcorrect
  rw [← hxy, store_key] at hcorrect
  exact hcorrect

/-- Soundness of the key is equivalent to correctness of the single-store
memo on every second input. -/
theorem soundKey_iff_store_correct {key : X → K} {obs : X → O} :
    SoundKey key obs ↔
      ∀ x y, lookupOrCompute key obs (store key obs Table.empty x) y = obs y := by
  constructor
  · intro hs x y
    exact lookupOrCompute_eq_obs
      (coherent_store_of_soundKey hs (coherent_empty key obs) x) y
  · intro hcorrect x y hkey
    have := hcorrect x y
    unfold lookupOrCompute at this
    rw [← hkey, store_key] at this
    exact this

end Store

/-! ## The law composes -/

/-- A key that refines a sound key is sound. -/
theorem soundKey_of_refines {K' : Type uK'} {key : X → K} {obs : X → O}
    (hs : SoundKey key obs) (key' : X → K') (g : K' → K)
    (hfactor : ∀ x, key x = g (key' x)) :
    SoundKey key' obs := by
  intro x y hxy
  apply hs
  rw [hfactor x, hfactor y, hxy]

/-- A consumer that factors through a served consumer is served by the same
key. -/
theorem soundKey_comp {O' : Type uO'} {key : X → K} {obs : X → O}
    (hs : SoundKey key obs) (f : O → O') :
    SoundKey key (f ∘ obs) := by
  intro x y hxy
  simp [hs x y hxy]

/-- Two consumers served by one key are jointly served by it. -/
theorem soundKey_pair {O' : Type uO'} {key : X → K} {obs : X → O} {obs' : X → O'}
    (hs : SoundKey key obs) (hs' : SoundKey key obs') :
    SoundKey key (fun x => (obs x, obs' x)) := by
  intro x y hxy
  simp [hs x y hxy, hs' x y hxy]

/-! ## Canary: the compact-syntax key and a cost-bearing consumer -/

namespace Canary

/-- A term with its erased syntactic shape and its elaboration colour. -/
structure Term where
  shape : Nat
  colour : Bool
  deriving DecidableEq

/-- Cost depends on colour: the coloured elaboration is dearer. -/
def cost (t : Term) : Nat := if t.colour then 7 else 1

/-- The compact key forgets colour. -/
def syntaxKey (t : Term) : Nat := t.shape

/-- The provenance-bearing key retains colour. -/
def colourKey (t : Term) : Nat × Bool := (t.shape, t.colour)

/-- The compact key is unsound for the cost consumer. -/
theorem syntaxKey_unsound_for_cost : ¬ SoundKey syntaxKey cost := by
  intro h
  have := h ⟨0, true⟩ ⟨0, false⟩ rfl
  simp [cost] at this

/-- The provenance-bearing key is sound for the cost consumer. -/
theorem colourKey_sound_for_cost : SoundKey colourKey cost := by
  intro x y hxy
  simp only [colourKey, Prod.mk.injEq] at hxy
  simp [cost, hxy.2]

/-- The compact key is sound for a consumer that reads only the shape. -/
theorem syntaxKey_sound_for_shape : SoundKey syntaxKey Term.shape :=
  fun _ _ h => h

/-- The concrete wrong answer: store the coloured term, look up the plain one,
receive the coloured cost. -/
theorem syntax_memo_returns_wrong_cost :
    lookupOrCompute syntaxKey cost
        (store syntaxKey cost Table.empty ⟨0, true⟩) ⟨0, false⟩ = 7 ∧
      cost ⟨0, false⟩ = 1 := by
  refine ⟨?_, rfl⟩
  unfold lookupOrCompute
  rw [show syntaxKey ⟨0, false⟩ = syntaxKey ⟨0, true⟩ from rfl, store_key]
  rfl

/-- The provenance-bearing memo answers correctly on the same sequence, and
its eviction to the empty table answers the same. -/
theorem colour_memo_correct_and_evictable :
    lookupOrCompute colourKey cost
        (store colourKey cost Table.empty ⟨0, true⟩) ⟨0, false⟩ = 1 ∧
      lookupOrCompute colourKey cost Table.empty ⟨0, false⟩ = 1 := by
  constructor
  · exact lookupOrCompute_eq_obs
      (coherent_store_of_soundKey colourKey_sound_for_cost
        (coherent_empty colourKey cost) _) _
  · rfl

end Canary

end Mettapedia.GSLT.Dynamics.MemoizationObserver
