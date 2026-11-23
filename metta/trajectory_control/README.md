# Finite trajectory control in MeTTa

This example chooses and executes coordinated actions using a task objective,
a stochastic reference, and explicit actuator admission. Policy construction,
sampling, information readouts and state updates run in MeTTa on CeTTa's
corrected PeTTa profile, using its existing `lib_transform` library.

From the workspace containing Mettapedia and Hyperon:

```sh
bash Mettapedia/metta/trajectory_control/run.sh
python3 Mettapedia/metta/trajectory_control/test_control.py
```

The runner locates the sibling CeTTa executable. For another installation, set
`CETTA_BIN` for the runner and pass `--cetta EXECUTABLE` to the test script.
Python is needed only for the independent test harness.

The world supplies three sensor bits `(a b c)`. The controller sets actuator bits
`(x y z)` with target `(b xor c, a xor c, a xor b xor c)`. Each correct bit earns
`+1`; each incorrect bit earns `-1`, so utility `U` lies between `-3` and `3`.
An actuator budget `B` permits actions with at most `B` bits set.

The reference is `R(world, action) = 1/64`. The admissible family consists of
one-step policies that observe the current sensors, preserve their uniform
initial law, and assign probability only to permitted actions. For pressure
`beta >= 0`, the objective and its conditional optimizer are

```text
F_beta(Q) = KL(Q || R) - beta E_Q[U]
          = E_Q[C_beta] + KL(Q || R),   C_beta = -beta U

pi_beta(action | world)
  = exp(beta U(world, action)) / sum_permitted exp(beta U(world, alternative))

Q(world, action) = (1/8) pi_beta(action | world)
```

`Objective` in the output is `-F_beta`. Admission restricts the policy family;
it leaves the reference unchanged. At zero pressure a restricted policy still
pays the KL cost of excluding reference actions. Exponentials are stabilized by
subtracting the largest admitted utility before normalization.

Representative unrestricted results are:

| Pressure | Mean utility | KL to reference, nats | Past to future, bits | Minimum unit cut, bits |
|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 | 0 |
| 1 | 2.284782 | 0.983440 | 1.418804 | 1.160262 |
| 2 | 2.892083 | 1.809157 | 2.610062 | 1.830495 |
| 4 | 2.997988 | 2.070387 | 2.986937 | 1.994972 |

The temporal readout compares the whole sensor triple with the whole action
triple. The spatial readout groups each sensor and its corresponding actuator
as a unit: `(a,x)`, `(b,y)`, `(c,z)`. It takes the minimum mutual information
across the three one-unit-versus-two-unit cuts. These are different questions.
All fifteen pairwise coordinate covariances vanish in the unrestricted model,
despite positive temporal and spatial information. The unit-cut score is a
trajectory information measure inspired by IIT; it is not the full IIT
cause-effect construction or a consciousness test.

`tc:passive-tilt` supplies a negative control. It normalizes all permitted
histories together. With budget `2` and pressure `2`, this changes an initial
world probability by `0.117429437536`. The actual controller normalizes each
conditional policy separately, keeping all initial probabilities at `1/8`.
A controller cannot select an easier starting world by reweighting it.

The execution interface is:

```metta
!(bind! &board (new-space))
!(tc:open &board episode (0 1 1) 3)
!(tc:step &board episode 2.0 0.5)
```

`tc:open` constructs the trusted fixture. `tc:step` reads its sensors and current
budget, computes a policy, and samples it using the supplied draw in `[0,1)`.
The demo uses a fixed draw for reproducibility. If supplied independent uniform
draws, this inverse-CDF interface realizes the specified conditional law; the
fixed demo is not an empirical sampling experiment.

`tc:execute` then uses the existing `transform` operation to consume `Pending`,
replace `ActuatorState`, and publish an `Executed` receipt. Sensors and budget
are preserved read resources. The executor rechecks the proposed action against
the current budget and sensor state. A replay or over-budget proposal returns
`Refused Admission` without mutation. Missing sensors or budget return
`Unresolved`; inconsistent observations, invalid policy inputs and empty policy
support have explicit refusal outcomes. No external actuator or irreversible
I/O is performed: the actuator state is the MeTTa space itself.

The fixture is not a security boundary against arbitrary code that can mutate
the space. Production hosting must use the host's authority and space-access
contracts. The example establishes serial execution through the transform API;
it does not establish a concurrent or native-machine atomicity theorem.

The independent Python harness checks every probability for eight worlds, four
budgets and five pressures; sampling intervals; joint laws and coarse readouts;
actual actuator changes, receipts, preserved resources, replays and refusals.
Its numerical oracle uses direct finite sums and groups observations before
taking mutual information. It also checks stale-permit rejection and missing
observation outcomes. All planning and execution in the demo remain MeTTa.
Numerical comparisons use absolute and relative tolerances of `2e-10`.

For unrestricted actuators, the computed distribution agrees numerically with
the Lean model `TrajectoryFreeEnergy.PressuredParity` at correlation
`tanh(beta)`. That model proves the Gibbs optimizer, fixed marginals, expected
utility, KL and temporal-information formulas. The full soft spatial-cut formula
is a numerical control here. This example uses floating-point arithmetic; a
proof connecting its actual MeTTa evaluation and transform commits to the Lean
model and the consolidated tcalc event semantics remains separate work.
