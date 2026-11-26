import Mettapedia.Machines.TIsa.StoreInstructions.NativeWords
import Mettapedia.Machines.TIsa.X86IndexedAddress

/-!
# Fetched register copies between native phases

A finite shuffle has sequential meaning. In particular, a
later copy reads the register value left by earlier copies.
Unspecified registers need not be initialized by a caller.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRegisterCopies

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code registerCode)
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev Native := X86RegisterRefinement.State

structure Copy where
  source : Fin 16
  target : Fin 16

abbrev Values := Fin 16 → Option Word

def interpret : List Copy → Values → Option Values
  | [], input => some input
  | c :: rest, input => do
    let word ← input c.source
    interpret rest (Function.update input c.target (some word))

def emit : List Copy → List ℕ
  | [] => []
  | c :: rest => registerCode 0x89 c.source c.target ++ emit rest

theorem emit_size (moves : List Copy) : (emit moves).length = 3 * moves.length := by
  induction moves with
  | nil => rfl
  | cons c rest ih =>
    simp only [emit, List.length_append, show (registerCode 0x89 c.source c.target).length = 3 from rfl,
      ih, List.length_cons]
    omega

def clobbers : List Copy → Finset Register
  | [] => ∅
  | c :: rest => ({key c.target, .rip} : Finset Register) ∪ clobbers rest

def Ready (values : Values) (state : Native) : Prop :=
  ∀ r w, values r = some w → lookup state r = some w

theorem Ready.empty (state : Native) : Ready (fun _ => none) state := by simp [Ready]

theorem Ready.set {values : Values} {state : Native} (known : Ready values state)
    (register : Fin 16) (word : Word) (present : lookup state register = some word) :
    Ready (Function.update values register (some word)) state := by
  intro r w exactValue
  by_cases same : r = register
  · subst r
    rw [Function.update_self] at exactValue
    exact (Option.some.inj exactValue) ▸ present
  · rw [Function.update_of_ne same] at exactValue
    exact known r w exactValue

noncomputable abbrev handlers := X86IndexedAddress.handlers

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (moves : List Copy) (extent : start + 3 * moves.length ≤ image.size)
    (code : Code image start (emit moves)) (values output : Values) (input : Ready values before)
    (calculated : interpret moves values = some output) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches moves.length).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers moves) ∅ before after ∧ Ready output after ∧
      Nonempty (At image after base (start + 3 * moves.length)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction moves generalizing values start before with
  | nil =>
    obtain rfl := Option.some.inj calculated
    exact ⟨before, X86FuelPrefix.fetches_zero before, X86StateFrame.Frame.refl _ _ _, input, ⟨by simpa using point⟩⟩
  | cons c rest ih =>
    obtain ⟨w, loaded, continued⟩ := Option.bind_eq_some_iff.mp calculated
    obtain ⟨move, suffix⟩ := NativeWords.code_append (show Code image start
      (registerCode 0x89 c.source c.target ++ emit rest) from code)
    simp only [List.length_cons] at extent
    obtain ⟨middle, fetched, moved, word, ⟨atRest⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector point (by omega) c.source c.target w (input _ _ loaded) move
    have physical : Ready (Function.update values c.target (some w)) middle := by
      intro r v known
      by_cases same : r = c.target
      · subst r
        rw [Function.update_self] at known
        exact (Option.some.inj known) ▸ word
      · rw [Function.update_of_ne same] at known
        apply (moved.lookup r _).trans (input _ _ known)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun e => same (key_injective e), (by decide : ∀ i : Fin 16, key i ≠ .rip) r⟩
    obtain ⟨after, ran, restFrame, ready, endpoint⟩ :=
      ih atRest (by omega) suffix (Function.update values c.target (some w)) physical continued
    have run := X86FuelPrefix.fetches_then 1 rest.length before middle after fetched ran
    refine ⟨after, ?_, ((X86StateFrame.registerOnly moved).trans restFrame).mono (Finset.Subset.refl _) (by simp),
      ready, ?_⟩
    · simpa only [List.length_cons, Nat.add_comm] using run
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 3] using endpoint

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRegisterCopies
