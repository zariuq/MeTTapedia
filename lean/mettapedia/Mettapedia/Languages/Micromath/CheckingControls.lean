import Mettapedia.Languages.Micromath.Checking
import Mettapedia.Languages.Micromath.KernelControls

/-!
# Common checker acceptance and refusal controls

The positive certificate derives a new claim from two consistent seeds and
two projection leaves. The negative join has individually accepted, jointly
consistent leaves but disagrees on their shared substitution input. Its
advertised conclusion is false in the same nontrivial Boolean model.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Micromath.CheckingControls
open Checking KernelControls

def leaf (claim : Claim) (tag : RuleTag) : Certificate := .node claim tag 0 (fun index => Fin.elim0 index)
def four (first second third fourth : Certificate) : Fin 4 → Certificate :=
  Fin.cases first (Fin.cases second (Fin.cases third (fun _ => fourth)))

def seeds : List Claim := [main,packed]
def transferredCertificate : Certificate := .node transferred .substitute1 4 (four
  (leaf main .assumption) (leaf left .projectionFirst) (leaf right .projectionSecond) (leaf packed .assumption))

theorem transferred_accepted : Checking.accepted seeds transferredCertificate = true := by decide +kernel
theorem transferred_new : transferred ∉ seeds := by decide +kernel
theorem transferred_from_common_checker : Micromath.Derives (Checking.basis seeds) transferred :=
  accepted_derives seeds transferredCertificate transferred_accepted

theorem seeds_hold : ∀ claim ∈ seeds, Holds boolAssignment claim := by
  intro claim member
  apply source_seeds_hold claim
  change claim = main ∨ claim = packed
  simpa only [seeds,List.mem_cons,List.not_mem_nil,or_false] using member

theorem transferred_semantics : Holds boolAssignment transferred :=
  accepted_holds boolAssignment bool_projects seeds seeds_hold transferredCertificate transferred_accepted

def reverseCertificate : Certificate := .node packed .substitute2 4 (four
  (leaf main .assumption) (leaf left .projectionFirst) (leaf right .projectionSecond) transferredCertificate)
theorem reverse_accepted : Checking.accepted seeds reverseCertificate = true := by decide +kernel

def wrongConclusionCertificate : Certificate := .node projectionCollapse .substitute1 4 (four
  (leaf main .assumption) (leaf left .projectionFirst) (leaf right .projectionSecond) (leaf packed .assumption))
theorem wrong_conclusion_refused : Checking.accepted seeds wrongConclusionCertificate = false := by decide +kernel
theorem omitted_seed_refused : Checking.accepted [main] transferredCertificate = false := by decide +kernel
theorem wrong_leaf_tag_refused : Checking.accepted seeds (leaf main .reflexivity) = false := by decide +kernel
theorem extra_leaf_child_refused : Checking.accepted seeds
    (.node (Micromath.reflexivity 5) .reflexivity 1 (fun _ => leaf main .assumption)) = false := by decide +kernel
theorem missing_substitution_premise_refused : validate seeds .substitute1 [main,left,right] transferred = false := by decide +kernel
theorem reordered_substitution_premises_refused : validate seeds .substitute1 [main,right,left,packed] transferred = false := by decide +kernel
theorem projection_future_symbols_accepted : Checking.accepted []
    (leaf (Micromath.projectionFirst 7000 9000) .projectionFirst) = true := by decide +kernel

def wrongJoinSeeds : List Claim := [diagonalAnd,firstIdentity,differentFirstInput]
def wrongJoinChildren : Fin 4 → Certificate := four
  (leaf diagonalAnd .assumption) (leaf firstIdentity .assumption)
  (leaf differentFirstInput .assumption) (leaf firstIdentity .assumption)
def wrongJoinCertificate : Certificate := .node falseMixedAnd .substitute1 4 wrongJoinChildren

theorem wrong_join_leaves_accepted : ∀ index : Fin 4,
    Checking.accepted wrongJoinSeeds (wrongJoinChildren index) = true := by decide +kernel
theorem wrong_join_seeds_hold : ∀ claim ∈ wrongJoinSeeds, Holds boolAssignment claim := by
  intro claim member
  simp only [wrongJoinSeeds,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact diagonal_and_holds
  · exact first_identity_holds
  · exact different_first_input_holds

theorem wrong_join_refused : Checking.accepted wrongJoinSeeds wrongJoinCertificate = false := by decide +kernel
theorem wrong_join_conclusion_false : ¬ Holds boolAssignment wrongJoinCertificate.concl := mixed_and_false

theorem no_accepted_wrong_join_conclusion : ¬ ∃ certificate : Certificate,
    Checking.accepted wrongJoinSeeds certificate = true ∧ certificate.concl = falseMixedAnd := by
  rintro ⟨certificate,checked,same⟩
  have valid := accepted_holds boolAssignment bool_projects wrongJoinSeeds wrong_join_seeds_hold certificate checked
  rw [same] at valid
  exact mixed_and_false valid

theorem source_proof_has_common_certificate : ∃ certificate : Certificate,
    Checking.accepted seeds certificate = true ∧ certificate.concl = transferred :=
  derives_has_certificate seeds transferred_from_common_checker

#print axioms transferred_from_common_checker
#print axioms transferred_semantics
#print axioms no_accepted_wrong_join_conclusion
#print axioms source_proof_has_common_certificate
end Mettapedia.Languages.Micromath.CheckingControls
