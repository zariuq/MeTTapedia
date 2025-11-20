import FourColor.Geometry.NoDigons
import FourColor.Geometry.RotationSystem

namespace FourColor.Geometry

open RotationSystem

inductive ThetaV | u | v | a | b | c deriving DecidableEq, Fintype, Repr
inductive ThetaE | e1 | e2 | e3 | e4 | e5 | e6 deriving DecidableEq, Fintype, Repr
inductive ThetaD
  | e1_u | e1_a
  | e2_a | e2_v
  | e3_u | e3_b
  | e4_b | e4_v
  | e5_u | e5_c
  | e6_c | e6_v
  deriving DecidableEq, Fintype, Repr

open ThetaV ThetaE ThetaD

def theta_edgeOf : ThetaD → ThetaE
  | e1_u => e1 | e1_a => e1
  | e2_a => e2 | e2_v => e2
  | e3_u => e3 | e3_b => e3
  | e4_b => e4 | e4_v => e4
  | e5_u => e5 | e5_c => e5
  | e6_c => e6 | e6_v => e6

def theta_vertOf : ThetaD → ThetaV
  | e1_u => u | e3_u => u | e5_u => u
  | e2_v => v | e4_v => v | e6_v => v
  | e1_a => a | e2_a => a
  | e3_b => b | e4_b => b
  | e5_c => c | e6_c => c

def theta_alpha_fn : ThetaD → ThetaD
  | e1_u => e1_a | e1_a => e1_u
  | e2_a => e2_v | e2_v => e2_a
  | e3_u => e3_b | e3_b => e3_u
  | e4_b => e4_v | e4_v => e4_b
  | e5_u => e5_c | e5_c => e5_u
  | e6_c => e6_v | e6_v => e6_c

def theta_alpha : Equiv.Perm ThetaD :=
{ toFun := theta_alpha_fn,
  invFun := theta_alpha_fn,
  left_inv := by intro x; cases x <;> rfl,
  right_inv := by intro x; cases x <;> rfl }

def theta_rho_fn : ThetaD → ThetaD
  | e1_u => e3_u | e3_u => e5_u | e5_u => e1_u
  | e2_v => e6_v | e6_v => e4_v | e4_v => e2_v
  | e1_a => e2_a | e2_a => e1_a
  | e3_b => e4_b | e4_b => e3_b
  | e5_c => e6_c | e6_c => e5_c

def theta_rho_inv_fn : ThetaD → ThetaD
  | e1_u => e5_u | e3_u => e1_u | e5_u => e3_u
  | e2_v => e4_v | e6_v => e2_v | e4_v => e6_v
  | e1_a => e2_a | e2_a => e1_a
  | e3_b => e4_b | e4_b => e3_b
  | e5_c => e6_c | e6_c => e5_c

def theta_rho : Equiv.Perm ThetaD :=
{ toFun := theta_rho_fn,
  invFun := theta_rho_inv_fn,
  left_inv := by intro x; cases x <;> rfl,
  right_inv := by intro x; cases x <;> rfl }

theorem theta_edge_fiber_two (e : ThetaE) : (Finset.univ.filter (fun d => theta_edgeOf d = e)).card = 2 := by
  cases e <;> native_decide

theorem theta_vert_rho : ∀ d, theta_vertOf (theta_rho d) = theta_vertOf d := by
  intro d; cases d <;> rfl

theorem theta_no_self_loops : ∀ d, theta_vertOf d ≠ theta_vertOf (theta_alpha d) := by
  intro d; cases d <;> decide

def ThetaRS : RotationSystem ThetaV ThetaE := {
  D := ThetaD
  edgeOf := theta_edgeOf
  vertOf := theta_vertOf
  alpha := theta_alpha
  rho := theta_rho
  alpha_involutive := by intro d; cases d <;> rfl
  alpha_fixfree := by intro d; cases d <;> decide
  edge_alpha := by intro d; cases d <;> rfl
  edge_fiber_two := theta_edge_fiber_two
  vert_rho := theta_vert_rho
  outer := e1_u
  no_self_loops := theta_no_self_loops
}

-- The specific property instance we want to refute
def naiveProperty (RS : RotationSystem ThetaV ThetaE) : Prop :=
  ∀ {f g : Finset ThetaE}
    (hf : f ∈ RS.internalFaces)
    (hg : g ∈ RS.internalFaces)
    (hfg : f ≠ g)
    {e1 e2 : ThetaE},
    e1 ∈ f → e1 ∈ g →
    e2 ∈ f → e2 ∈ g →
    e1 ∉ RS.boundaryEdges →
    e2 ∉ RS.boundaryEdges →
    e1 ≠ e2 → False

theorem naive_no_digons_false : ¬ naiveProperty ThetaRS := by
  intro h_naive
  let RS := ThetaRS
  let f1 := RS.faceEdges e3_u
  let f2 := RS.faceEdges e5_u
  
  have hf1_int : f1 ∈ RS.internalFaces := by native_decide
  have hf2_int : f2 ∈ RS.internalFaces := by native_decide
  have h_diff : f1 ≠ f2 := by native_decide
  
  have he3_f1 : e3 ∈ f1 := by native_decide
  have he3_f2 : e3 ∈ f2 := by native_decide
  have he4_f1 : e4 ∈ f1 := by native_decide
  have he4_f2 : e4 ∈ f2 := by native_decide

  have he3_int : e3 ∉ RS.boundaryEdges := by native_decide
  have he4_int : e4 ∉ RS.boundaryEdges := by native_decide
  
  have he3_ne_e4 : e3 ≠ e4 := by decide

  apply h_naive hf1_int hf2_int h_diff
  exact he3_f1; exact he3_f2
  exact he4_f1; exact he4_f2
  exact he3_int; exact he4_int
  exact he3_ne_e4

end FourColor.Geometry
