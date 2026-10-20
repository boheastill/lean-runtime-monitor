# Lean 4 runtime safety monitor

[![CI](https://github.com/boheastill/lean-runtime-monitor/actions/workflows/ci.yml/badge.svg)](https://github.com/boheastill/lean-runtime-monitor/actions/workflows/ci.yml)

A small, complete Lean 4 + mathlib project: a runtime safety monitor over real-valued geometry, proved with zero `sorry`.

Written on 21 October 2026 as a sample for a formal-verification brief. It is a synthetic scenario and contains no client material.

Rendered page with the source and the build log: https://demo.boheastill.com/lean-monitor/

## The scenario

An untrusted controller proposes the next position. The monitor computes the margin that would remain after the step and, through a threshold switch, either accepts the proposal or applies a fallback (stay in place). The question a reviewer asks: can any sequence of proposals bring the system closer than the safe distance `dmin` to the obstacle? The file proves it cannot.

## What is proved

All in [`LeanMonitor/Monitor.lean`](LeanMonitor/Monitor.lean).

| Theorem | Statement in plain English |
|---|---|
| `nextMode_eq_fallback_iff`, `nextMode_eq_normal_iff` | The switch selects the fallback exactly when the margin is below the threshold. The monitor decides through this switch. |
| `safe_after_step`, `monitor_safe` | A step accepted by the monitor never ends inside the safe distance. Proved in any metric space. |
| `always_safe`, `always_safe_plane` | Every state reachable under any sequence of proposals is safe, by induction over an inductive reachability predicate; then the same result in `EuclideanSpace ℝ (Fin 2)`. |
| `stop_within_gap`, `braking_fits_after_step` | With deceleration `a > 0`, the braking distance `v² / (2a)` fits a gap `g` when `v² ≤ 2ag`; if it fits the margin left after a step, the system is still at least `dmin + v² / (2a)` from the obstacle. |
| `unchecked_breaks_invariant`, `monitor_rejects_unsafe_step` | Without the monitor the invariant fails: from the safe start 2 on the real line, one unchecked step reaches 1/2, inside the safe distance, and the monitor rejects exactly that step. |

Every theorem is checked with `#print axioms` at the end of the file and depends only on Lean's standard axioms: `propext`, `Classical.choice` and `Quot.sound`.

## Model assumptions

Stated so the theorems are read correctly:

- discrete steps; the system moves exactly to the position the monitor outputs;
- a static obstacle and a fixed minimum distance `dmin`;
- the start is safe;
- the fallback "stay in place" can always be executed. A physical system would brake instead; the braking theorems give the bound such a fallback needs.

## What this sample does not cover

Continuous-time trajectories (they need a flow invariant), moving obstacles, and sensor or timing uncertainty. Each of these changes what has to be proved, so I would scope them with you before writing code rather than assume.

## Build it

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager).

```bash
git clone https://github.com/boheastill/lean-runtime-monitor
cd lean-runtime-monitor
lake exe cache get   # download prebuilt mathlib
lake build
```

Expected: `Build completed successfully`, with one `depends on axioms: [propext, Classical.choice, Quot.sound]` line per theorem and no warnings. CI runs the same build on every push.

## Versions

- Lean `v4.36.0-rc1` (see `lean-toolchain`)
- mathlib `v4.36.0-rc1`, commit `625d8914` (pinned in `lake-manifest.json`)

## Project layout

```
lakefile.toml            package and mathlib dependency
lean-toolchain           Lean version
lake-manifest.json       pinned dependency revisions
LeanMonitor.lean         library root
LeanMonitor/Monitor.lean definitions, theorems and axiom checks
.github/workflows/ci.yml build on every push
```

## How this was developed

The commit history is the real sequence of today's work: project setup, a first version, a lint clean-up, then a refinement pass. The refinement pass made the refutation a statement about unchecked steps, added the `a > 0` precondition to the braking theorem, routed the monitor's decision through the threshold switch, and added an axioms check for every theorem.

## How I deliver formalization work

- Before proving, I restate each property in plain English for you to confirm, so the proof answers the question you actually have.
- Each iteration is a clean `lake build` from a fresh checkout, with the build log.
- Delivered theorems carry zero `sorry`, checked with `#print axioms`.
- Anything I cannot close comes back as an explicit TODO that names the missing lemma, or as a counterexample if the property is false.

## License

MIT, see [LICENSE](LICENSE).
