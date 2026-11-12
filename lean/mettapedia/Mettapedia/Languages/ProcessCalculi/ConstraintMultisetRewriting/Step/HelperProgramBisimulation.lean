import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperProgramRuns

/-!
# Component equivalence at the declaration-shape observation

The local program profile is deterministic: a nonempty selected run has one
pending head. Equality of the complete ordered declaration shapes therefore
supplies an event-fibre bisimulation. It says nothing about observations of
the helpers' values or of resource identities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Program

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open EventMultiplicity
variable {S : Signature} {O : Type} [DecidableEq O]

theorem Head.unique : ∀ {program : Program S O} (first second : Head program), first = second
  | _, .cons _ _ _, second => by cases second; rfl

theorem Head.word : ∀ {program : Program S O} (head : Head program),
    helperWord program.run = head.firing.helper :: helperWord head.next.run
  | _, .cons _ _ _ => rfl

theorem Head.nonempty_word {program : Program S O} (head : Head program) : helperWord program.run ≠ [] := by
  rw [head.word]
  exact List.cons_ne_nil _ _

def headOfNonempty : ∀ (program : Program S O), helperWord program.run ≠ [] → Head program
  | ⟨_, .nil _⟩, nonempty => False.elim (nonempty rfl)
  | ⟨_, .cons f allowed rest⟩, _nonempty => .cons f allowed rest

def headsEquiv (first second : Program S O) (same : helperWord first.run = helperWord second.run) :
    Head first ≃ Head second where
  toFun head := headOfNonempty second (same ▸ head.nonempty_word)
  invFun head := headOfNonempty first (same.symm ▸ head.nonempty_word)
  left_inv head := Head.unique _ head
  right_inv head := Head.unique _ head

def wordBisimulation : Bisimulation (system (S := S) (O := O)) (system (S := S) (O := O))
    (fun first second => helperWord first.run = helperWord second.run) where
  choices same := headsEquiv _ _ same
  actions same head := by
    have words := same
    rw [head.word, (headsEquiv _ _ same head).word] at words
    exact (List.cons.inj words).1
  successors same head := by
    have words := same
    rw [head.word, (headsEquiv _ _ same head).word] at words
    exact (List.cons.inj words).2

theorem bisimilar_of_word {first second : Program S O} (same : helperWord first.run = helperWord second.run) :
    Bisimilar system first system second := ⟨_, ⟨wordBisimulation⟩, same⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Program
