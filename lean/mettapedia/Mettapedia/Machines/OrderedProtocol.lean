import Mathlib.Data.List.Basic

/-!
# Ordered primitive protocols with separate terminal continuations

Primitive services may refine local state, retain ordered alternatives, change
the world, fault, or suspend. Sequencing forwards each of these continuations;
it also forwards the enclosing saved failure delimiter. This finite protocol
algebra does not specify any particular primitive service or native lifetime.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedProtocol

abbrev Failure (World Result : Type) := World → Result
abbrev Success (State World Result : Type) :=
  State → Failure World Result → World → Result
abbrev Kernel (State World Fault Pause Result : Type) :=
  State → Success State World Result → Failure World Result →
    Failure World Result → (Fault → World → Result) →
    (Pause → World → Result) → World → Result

variable {State World Fault Pause Result Op : Type}

def done : Kernel State World Fault Pause Result :=
  fun state success pending _ _ _ world => success state pending world

def sequence (first second : Kernel State World Fault Pause Result) :
    Kernel State World Fault Pause Result :=
  fun state success pending saved fault pause world =>
    first state (fun prepared remaining current =>
      second prepared success remaining saved fault pause current)
      pending saved fault pause world

def choice (first second : Kernel State World Fault Pause Result) :
    Kernel State World Fault Pause Result :=
  fun state success pending saved fault pause world =>
    first state success
      (fun current => second state success pending saved fault pause current)
      saved fault pause world

def execute (primitive : Op → Kernel State World Fault Pause Result) :
    List Op → Kernel State World Fault Pause Result
  | [] => done
  | operation :: rest => sequence (primitive operation) (execute primitive rest)

theorem sequence_assoc (first second third : Kernel State World Fault Pause Result) :
    sequence (sequence first second) third = sequence first (sequence second third) := rfl

theorem sequence_done (body : Kernel State World Fault Pause Result) :
    sequence body done = body := by
  funext state success pending saved fault pause world
  simp only [sequence, done]

theorem done_sequence (body : Kernel State World Fault Pause Result) :
    sequence done body = body := rfl

theorem execute_append (primitive : Op → Kernel State World Fault Pause Result)
    (first second : List Op) :
    execute primitive (first ++ second) =
      sequence (execute primitive first) (execute primitive second) := by
  induction first with
  | nil => rfl
  | cons operation first ih =>
      simp only [List.cons_append, execute, ih, sequence_assoc]

def alternatives : List (Kernel State World Fault Pause Result) →
    Kernel State World Fault Pause Result
  | [] => fun _ _ pending _ _ _ world => pending world
  | first :: rest => choice first (alternatives rest)

theorem alternatives_map_congr
    (source target : Op → Kernel State World Fault Pause Result)
    (operations : List Op) (same : ∀ operation ∈ operations, source operation = target operation) :
    alternatives (operations.map source) = alternatives (operations.map target) := by
  congr 1
  exact List.map_congr_left same

namespace Controls

def faulting : Kernel Nat (List String) String Nat (List String) :=
  fun _ _ _ _ fault _ world => fault "bad" (world ++ ["effect"])

def suspended : Kernel Nat (List String) String Nat (List String) :=
  fun _ _ _ _ _ pause world => pause 7 (world ++ ["suspend"])

def later : Kernel Nat (List String) String Nat (List String) :=
  fun state success pending _ _ _ world => success (state + 1) pending (world ++ ["later"])

theorem fault_does_not_run_later :
    sequence faulting later 0 (fun _ _ world => world) id id
      (fun reason world => world ++ [reason]) (fun _ world => world) [] =
      ["effect", "bad"] := rfl

theorem suspension_does_not_become_exhaustion :
    sequence suspended later 0 (fun _ _ world => world)
      (fun world => world ++ ["exhausted"]) id
      (fun _ world => world) (fun _ world => world ++ ["retained"]) [] =
      ["suspend", "retained"] := rfl

end Controls
end Mettapedia.Machines.OrderedProtocol
