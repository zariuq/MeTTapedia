import Ramsey36.Basic
import Hammer

open SimpleGraph Finset

variable {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]

-- Test: Can hammer prove the Fubini/handshake lemma with limited premises?
example
    (N M : Finset (Fin 18))
    (h_disj : Disjoint N M) :
    N.sum (fun n => (M.filter (fun w => G.Adj n w)).card) =
    M.sum (fun w => (N.filter (fun n => G.Adj n w)).card) := by
  -- Try with reduced premise limits (default is 32 for aesop, 16 for auto)
  hammer (config := { aesopPremises := 64, autoPremises := 32 })
