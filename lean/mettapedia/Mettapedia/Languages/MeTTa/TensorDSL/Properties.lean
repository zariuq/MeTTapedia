import Mettapedia.Languages.MeTTa.TensorDSL.Lowering

/-!
# MeTTa Tensor DSL Proof Obligations

Named obligations for the optional tensor profile.
-/

namespace Mettapedia.Languages.MeTTa.TensorDSL

open Valence

theorem canonicalize_idempotence_obligation
    (dummy : Finset String) (v : Valence) :
    canonicalize dummy (canonicalize dummy v) = canonicalize dummy v :=
  canonicalize_idempotent dummy v

theorem dummy_renaming_alpha_invariance_obligation
    (dummy : Finset String) (fresh : String) (v : Valence)
    (hfresh : fresh ∉ v.names) :
    canonicalize (insert fresh dummy) (renameDummies dummy fresh v) = canonicalize dummy v :=
  canonicalize_dummy_rename_invariant dummy fresh v hfresh

theorem contraction_soundness_obligation
    (name : String) (body : Expr) :
    Expr.valence (.contract name body) = Valence.contract name (Expr.valence body) :=
  Expr.valence_contract_sound name body

theorem contraction_arity_monotone_obligation
    (name : String) (v : Valence) :
    (Valence.contract name v).arity ≤ v.arity :=
  Valence.contract_arity_le name v

theorem reduction_preserves_valence_arity_obligation
    {e e' : Expr} (h : Reduces e e') :
    (Expr.valence e).arity = (Expr.valence e').arity :=
  reduces_preserves_valence_arity h

end Mettapedia.Languages.MeTTa.TensorDSL
