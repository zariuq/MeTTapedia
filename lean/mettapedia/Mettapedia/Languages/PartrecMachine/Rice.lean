import Mettapedia.Languages.PartrecMachine.Adequacy
import Mettapedia.Computability.ToPartrecCodeEncoding
import Mettapedia.Computability.HaltingGate

/-!
# Rice's theorem for the authored machine

Programs are codes of the authored partial-recursive machine, and what a program
computes is read off reduction in that `LanguageDef` (`HaltsWith`), not off a Lean
evaluator.  No computable procedure decides a nontrivial set of programs that is
invariant under what they compute (`rice`).

The scope is exactly codes of the authored machine, indexed by the `Primcodable`
encoding of `Turing.ToPartrec.Code`.  It is not a statement about arbitrary
patterns of arbitrary language definitions.

The theorem is an instance of Rice's theorem from a halting gate
(`HaltingGate.not_computable`), and the gate is built in the machine.

* **Compilation.**  One universal machine code runs Mathlib's `Nat.Partrec.Code`
  given its number; prefixing that number gives a primitive-recursive compilation
  `compile` whose evaluation is the source code's evaluation at the head of the
  input (`compile_eval`).
* **Gating.**  `gate p c` first runs `compile c` on `0` and then behaves as `p`.
  What it computes is what `p` computes when `c` halts on `0`, and nothing
  otherwise (`haltingGate`).

Any observation no finer than what programs compute inherits the theorem
(`HaltingGate.coarsen`); halting on the empty input is one
(`haltsOnEmpty_not_computable`).  The coarseness hypothesis is load-bearing:
syntactic identity is finer, and under it a decidable nontrivial invariant set
exists (`syntax_observer_escapes`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Turing.ToPartrec
open Mettapedia.Computability.ToPartrecCodeEncoding

/-! ## Compilation from Mathlib's codes -/

theorem exists_universal :
    ∃ universal : Code, ∀ index input : ℕ,
      universal.eval [index, input] =
        (fun output => [output]) <$> (Denumerable.ofNat Nat.Partrec.Code index).eval input := by
  have partrec : Nat.Partrec' fun v : List.Vector ℕ 2 =>
      (Denumerable.ofNat Nat.Partrec.Code v.head).eval v.tail.head :=
    Nat.Partrec'.part_iff₂.mpr
      (show Partrec₂ fun (index input : ℕ) => (Denumerable.ofNat Nat.Partrec.Code index).eval input from
        Nat.Partrec.Code.eval_part.comp
          ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst) Computable.snd)
  obtain ⟨universal, spec⟩ := Code.exists_code partrec
  refine ⟨universal, fun index input => ?_⟩
  have := spec ⟨[index, input], rfl⟩
  simp only [List.Vector.head, List.Vector.tail, Part.map_eq_map] at this
  rw [this]
  rfl

/-- A universal machine code, fixed once. -/
noncomputable def universal : Code := Classical.choose exists_universal

theorem universal_eval (index input : ℕ) :
    universal.eval [index, input] =
      (fun output => [output]) <$> (Denumerable.ofNat Nat.Partrec.Code index).eval input :=
  Classical.choose_spec exists_universal index input

/-- Compile a code of Mathlib's partial recursive functions into a host program. -/
noncomputable def compile (source : Nat.Partrec.Code) : Code :=
  .comp universal (.cons (constCode (Encodable.encode source)) .head)

theorem compile_eval (source : Nat.Partrec.Code) (input : List ℕ) :
    (compile source).eval input = (fun output => [output]) <$> source.eval input.headI := by
  simp only [compile, Code.comp_eval, Code.cons_eval, constCode_eval, Code.head_eval,
    Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some, List.headI_cons]
  exact (Part.bind_some _ _).trans ((universal_eval _ _).trans (by rw [Denumerable.ofNat_encode]))

theorem compile_primrec : Primrec compile :=
  primrec₂_comp.comp (Primrec.const _)
    (primrec₂_cons.comp (constCode_primrec.comp Primrec.encode) (Primrec.const _))

/-! ## Evaluation read off reduction -/

/-- The program, run on `input`, halts with `output`: its pending evaluation
reduces in the authored language to the halted configuration. -/
def HaltsWith (program : Code) (input output : List ℕ) : Prop :=
  Relation.ReflTransGen Reduces (normalTerm program .halt input) (encCfg (.halt output))

/-- The same relation, as multi-step reduction in the generated theory. -/
theorem haltsWith_iff_multiStep {program : Code} {input output : List ℕ} :
    HaltsWith program input output ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT partrecMachine).MultiStep
        (normalTerm program .halt input) (encCfg (.halt output)) :=
  reflTransGen_reduces_iff_multiStep _ _

theorem haltsWith_iff {program : Code} {input output : List ℕ} :
    HaltsWith program input output ↔ output ∈ program.eval input :=
  adequacy program input output

theorem haltsWith_eq_iff {first second : Code} :
    HaltsWith first = HaltsWith second ↔ first.eval = second.eval := by
  constructor
  · intro same
    funext input
    apply Part.ext
    intro output
    rw [← haltsWith_iff, ← haltsWith_iff, same]
  · intro same
    funext input output
    apply propext
    rw [haltsWith_iff, haltsWith_iff, same]

/-! ## The silent program and the gate -/

/-- A program that never halts. -/
noncomputable def silent : Code := compile Mettapedia.Computability.silentCode

theorem silent_eval (input : List ℕ) : silent.eval input = Part.none := by
  simp [silent, compile_eval, Mettapedia.Computability.silentCode_eval]

/-- Run `compile source` on `0`, discard its output, then behave as `program`. -/
noncomputable def gate (program : Code) (source : Nat.Partrec.Code) : Code :=
  .comp program (.comp .tail (.cons (.comp (compile source) .zero) .id))

theorem gate_eval (program : Code) (source : Nat.Partrec.Code) (input : List ℕ) :
    (gate program source).eval input =
      (source.eval 0).bind fun _ => program.eval input := by
  simp only [gate, Code.comp_eval, Code.cons_eval, Code.tail_eval, Code.id_eval, Code.zero_eval,
    Mettapedia.Computability.bind_partialFunction, Part.pure_eq_some, Part.bind_some, compile_eval]
  apply Part.ext
  intro output
  simp [Part.mem_bind_iff, Part.bind_eq_bind, Part.map_eq_map]

theorem gate_primrec (program : Code) : Primrec (gate program) :=
  primrec₂_comp.comp (Primrec.const _)
    (primrec₂_comp.comp (Primrec.const _)
      (primrec₂_cons.comp (primrec₂_comp.comp compile_primrec (Primrec.const _))
        (Primrec.const _)))

/-- **The machine has a halting gate** for what its programs compute. -/
noncomputable def haltingGate : Mettapedia.Computability.HaltingGate HaltsWith where
  silent := silent
  gate := gate
  gate_computable program := (gate_primrec program).to_comp
  observe_gate_of_halts program source halts := by
    refine haltsWith_eq_iff.mpr (funext fun input => ?_)
    rw [gate_eval, Part.eq_some_iff.mpr (Part.dom_iff_mem.mp halts).choose_spec]
    simp
  observe_gate_of_diverges program source diverges := by
    refine haltsWith_eq_iff.mpr (funext fun input => ?_)
    rw [gate_eval, silent_eval, Part.eq_none_iff'.mpr diverges]
    simp

/-! ## Rice's theorem for the machine -/

open Mettapedia.Computability

/-- **Rice's theorem for the authored machine.**  A set of programs that depends
only on what they compute, read off reduction, and is neither empty nor
everything, is not computably decidable. -/
theorem rice {programs : Set Code} (invariant : ObservationInvariant HaltsWith programs)
    (nontrivial : programs.Nonempty ∧ programsᶜ.Nonempty) : ¬ ComputablePred (· ∈ programs) :=
  haltingGate.not_computable invariant nontrivial

/-! ## Coarser observations -/

/-- The program halts on the empty input, read off reduction. -/
def HaltsOnEmpty (program : Code) : Prop := ∃ output, HaltsWith program [] output

theorem haltsOnEmpty_iff_dom (program : Code) : HaltsOnEmpty program ↔ (program.eval []).Dom := by
  simp only [HaltsOnEmpty, haltsWith_iff, Part.dom_iff_mem]

theorem haltsOnEmpty_noFinerThan : NoFinerThan HaltsOnEmpty HaltsWith := by
  intro first second same
  simp only [HaltsOnEmpty, same]

/-- Positive instance of a coarser observation: halting on the empty input. -/
theorem haltsOnEmpty_not_computable : ¬ ComputablePred HaltsOnEmpty := by
  refine (haltingGate.coarsen haltsOnEmpty_noFinerThan).not_computable (programs := {p | HaltsOnEmpty p})
    (fun first second same => by simp only [Set.mem_ofPred_eq, same]) ⟨⟨.zero', ?_⟩, ⟨silent, ?_⟩⟩
  · exact (haltsOnEmpty_iff_dom _).mpr (by simp)
  · exact fun halts => by simpa [silent_eval] using (haltsOnEmpty_iff_dom _).mp halts

/-- **The coarseness hypothesis is load-bearing.**  Syntactic identity is finer
than what programs compute, and the set containing only `zero'` is invariant under
it, nontrivial, and decidable. -/
theorem syntax_observer_escapes :
    ¬ NoFinerThan (id : Code → Code) HaltsWith ∧
      ObservationInvariant (id : Code → Code) {program | program = .zero'} ∧
      ({program | program = .zero'} : Set Code).Nonempty ∧
      ({program | program = .zero'} : Set Code)ᶜ.Nonempty ∧
      ComputablePred (· ∈ ({program | program = .zero'} : Set Code)) := by
  refine ⟨fun noFiner => ?_, fun first second same => by simp only [id] at same; rw [same],
    ⟨.zero', rfl⟩, ⟨.succ, by simp⟩,
    ⟨inferInstance, (Primrec.eq.comp Primrec.id (Primrec.const _)).decide.to_comp⟩⟩
  have same : HaltsWith .zero' = HaltsWith (.comp .zero' .id) :=
    haltsWith_eq_iff.mpr (by funext input; simp)
  exact absurd (noFiner _ _ same) (by simp)

/-! ## Axiom audit -/

#print axioms compile_eval
#print axioms compile_primrec
#print axioms haltsWith_eq_iff
#print axioms rice
#print axioms haltsOnEmpty_not_computable
#print axioms syntax_observer_escapes

end Mettapedia.Languages.PartrecMachine
