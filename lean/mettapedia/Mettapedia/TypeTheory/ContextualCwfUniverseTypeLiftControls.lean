import Mettapedia.TypeTheory.ContextualCwfUniverseTypeLift
import Mettapedia.TypeTheory.ContextualCwfUniverseLiftControls

/-!
# Lifted varying dependent products and sums

The supplied function and dependent pair retain their finite witnesses,
including after a nonidentity base substitution. An additional Boolean sum
component separates beta from the eta hypothesis: lifting does not supply
an equation absent from the original operations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCwfUniverseTypeLiftControls

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualSumComprehension ContextualCwfUniverseLift
open ContextualCwfUniverseLiftControls (original raised context domain diagonal successor)

abbrev products := liftProducts.{1, 0, 1, 0, 1, 1, 1, 1} Families.products.{0}

theorem native_products_eta : ContextualPiEta.PiEta Families.products.{0}
    Families.products_substitution.1 := by
  intro Γ A B function
  rfl

def nativeSums : StableSums original.toCwf where
  operations := Families.sums
  beta := SigmaOperations.ofQualified_beta ContextualSumComparison.familiesSums
  eta := by intro Γ A B value; rfl
  substitution := Families.sums_substitution

abbrev sums := liftStableSums.{1, 0, 1, 0, 1, 1, 1, 1} nativeSums

abbrev codomain : raised.toCwf.Ty (raised.toCwf.ext context domain) :=
  ⟨fun (point : Σ n : Nat, Fin (n + 1)) => Fin (point.1 + point.2.val + 1)⟩

def body : raised.toCwf.Tm (raised.toCwf.ext context domain) codomain :=
  ⟨fun (point : Σ n : Nat, Fin (n + 1)) => ⟨point.2.val, by omega⟩⟩

def function : raised.toCwf.Tm context (products.pi domain codomain) := products.lam body

theorem function_retains_argument (n : Nat) (argument : Fin (n + 1)) :
    (function.down n argument).val = argument.val := rfl

theorem actual_application_readout (n : Nat) :
    ((products.app function diagonal).down n).val = n := rfl

theorem actual_application_beta :
    products.app function diagonal = raised.toCwf.tmSub body
      (ContextualProductComparison.selfExtend raised.toCwf diagonal) :=
  lifted_products_beta Families.products
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) body diagonal

theorem actual_generic_variable_eta :
    products.lam (ContextualPiEta.genericSection products
      (lifted_products_formation Families.products Families.products_substitution.1) function) = function :=
  lifted_products_eta Families.products Families.products_substitution.1 native_products_eta function

theorem actual_product_substitution : StrictPiSubstitution products :=
  lifted_products_substitution Families.products Families.products_substitution

def second : raised.toCwf.Tm context (raised.toCwf.tySub codomain
    (ContextualProductComparison.selfExtend raised.toCwf diagonal)) :=
  ⟨fun (n : Nat) => ⟨n, by change n < n + n + 1; omega⟩⟩

def paired : raised.toCwf.Tm context (sums.operations.sigma domain codomain) :=
  sums.operations.pair diagonal second

theorem exact_sum_witnesses (n : Nat) : (paired.down n).1.val = n ∧
    (paired.down n).2.val = n := ⟨rfl, rfl⟩

theorem shifted_sum_witnesses (n : Nat) :
    ((raised.toCwf.tmSub paired successor).down n).1.val = n + 1 ∧
    ((raised.toCwf.tmSub paired successor).down n).2.val = n + 1 := ⟨rfl, rfl⟩

theorem sum_pair_eta : sums.operations.pair (sums.operations.fst paired)
    (sums.operations.snd paired) = paired := sums.eta paired

theorem omitted_substitution_changes_readout (n : Nat) :
    ((raised.toCwf.tmSub paired successor).down n).2.val ≠ (paired.down n).2.val := by
  change n + 1 ≠ n
  omega

def hidden : SigmaOperations original.toCwf where
  sigma A B γ := (Σ a : A γ, B ⟨γ, a⟩) × Bool
  pair a b γ := (⟨a γ, b γ⟩, false)
  fst value γ := (value γ).1.1
  snd value γ := (value γ).1.2

theorem hidden_beta : SigmaBeta hidden := ⟨fun _ _ => rfl, fun _ _ => HEq.rfl⟩

def hiddenValue : raised.toCwf.Tm context
    ((liftSums.{1, 0, 1, 0, 1, 1, 1, 1} hidden).sigma domain codomain) :=
  ⟨fun (n : Nat) => (⟨diagonal.down n, second.down n⟩, true)⟩

theorem lifted_hidden_beta : SigmaBeta (liftSums.{1, 0, 1, 0, 1, 1, 1, 1} hidden) :=
  lifted_sums_beta hidden hidden_beta

theorem lifted_beta_does_not_supply_eta :
    ¬ SigmaEta (liftSums.{1, 0, 1, 0, 1, 1, 1, 1} hidden) := by
  intro eta
  have equation := eta hiddenValue
  have booleans := congrArg (fun term : raised.toCwf.Tm context
    ((liftSums.{1, 0, 1, 0, 1, 1, 1, 1} hidden).sigma domain codomain) => (term.down 0).2) equation
  exact Bool.false_ne_true booleans

end Mettapedia.TypeTheory.ContextualCwfUniverseTypeLiftControls
