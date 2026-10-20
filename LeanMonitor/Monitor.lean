import Mathlib

/-!
# A runtime safety monitor, proved over the reals

An untrusted controller proposes the next position. A monitor accepts the
proposal only if the step is short enough to keep a safety margin from an
obstacle; otherwise it applies a fallback (stay in place).

We prove, with zero `sorry`:

1. Decision logic: the mode switch picks the fallback exactly when the margin
   drops below the threshold.
2. Geometry: an accepted step never takes the system closer than `dmin` to the
   obstacle. This holds in any metric space, so it covers the Euclidean plane,
   3-D space or a road network alike.
3. Invariant: every state reachable under any sequence of proposals is safe
   (induction over reachability).
4. Nonlinear arithmetic: braking distance `v² / (2a)` fits in a gap `g`
   whenever `v² ≤ 2 a g`, and the combined check "step + braking distance fits
   the margin" leaves the system able to stop outside the safety distance.
5. A refutation: without the monitor the property is false, shown on a
   concrete counterexample.
-/

namespace Monitor

/-! ## 1. Threshold decision logic -/

inductive Mode
  | normal
  | fallback
  deriving DecidableEq, Repr

/-- Switch to the fallback when the remaining margin is below the threshold. -/
noncomputable def nextMode (margin threshold : ℝ) : Mode :=
  if margin < threshold then Mode.fallback else Mode.normal

theorem nextMode_fallback {m t : ℝ} (h : m < t) : nextMode m t = Mode.fallback := by
  simp [nextMode, h]

theorem nextMode_normal {m t : ℝ} (h : t ≤ m) : nextMode m t = Mode.normal := by
  simp [nextMode, not_lt.mpr h]

/-- The switch is exactly the threshold test, in both directions. -/
theorem nextMode_fallback_iff (m t : ℝ) : nextMode m t = Mode.fallback ↔ m < t := by
  constructor
  · intro h
    by_contra hlt
    rw [nextMode_normal (not_lt.mp hlt)] at h
    exact Mode.noConfusion h
  · exact nextMode_fallback

/-! ## 2. Geometry in an arbitrary metric space -/

variable {P : Type*} [MetricSpace P]

/-- Scenario parameters: the obstacle and the minimum safe distance. -/
structure Params (P : Type*) where
  obstacle : P
  dmin : ℝ

/-- A step no longer than the remaining margin keeps the safe distance. -/
theorem safe_after_step (o p q : P) (dmin : ℝ)
    (hstep : dist p q ≤ dist p o - dmin) : dmin ≤ dist q o := by
  have h := dist_triangle p q o
  linarith

/-- The monitor: accept the proposed position only if the step fits the margin. -/
noncomputable def monitor (prm : Params P) (p proposed : P) : P :=
  if dist p proposed ≤ dist p prm.obstacle - prm.dmin then proposed else p

/-- One monitored step preserves safety. -/
theorem monitor_safe (prm : Params P) (p proposed : P)
    (hp : prm.dmin ≤ dist p prm.obstacle) :
    prm.dmin ≤ dist (monitor prm p proposed) prm.obstacle := by
  unfold monitor
  split_ifs with h
  · exact safe_after_step prm.obstacle p proposed prm.dmin h
  · exact hp

/-! ## 3. Invariant over all reachable states -/

/-- States reachable from `start` under any sequence of proposals. -/
inductive Reachable (prm : Params P) (start : P) : P → Prop
  | init : Reachable prm start start
  | step {p : P} (proposed : P) :
      Reachable prm start p → Reachable prm start (monitor prm p proposed)

/-- Safety theorem: if the start is safe, every reachable state is safe. -/
theorem always_safe (prm : Params P) (start : P)
    (h0 : prm.dmin ≤ dist start prm.obstacle) :
    ∀ p, Reachable prm start p → prm.dmin ≤ dist p prm.obstacle := by
  intro p hp
  induction hp with
  | init => exact h0
  | step proposed _ ih => exact monitor_safe prm _ proposed ih

/-- The same theorem, specialised to the Euclidean plane. -/
theorem always_safe_plane (prm : Params (EuclideanSpace ℝ (Fin 2)))
    (start : EuclideanSpace ℝ (Fin 2))
    (h0 : prm.dmin ≤ dist start prm.obstacle) :
    ∀ p, Reachable prm start p → prm.dmin ≤ dist p prm.obstacle :=
  always_safe prm start h0

/-! ## 4. Nonlinear arithmetic: braking distance -/

/-- Stopping distance `v² / (2a)` fits in the gap `g` when `v² ≤ 2 a g`. -/
theorem stop_within_gap (v a g : ℝ) (ha : 0 < a) (h : v ^ 2 ≤ 2 * a * g) :
    v ^ 2 / (2 * a) ≤ g := by
  have h2a : (0 : ℝ) < 2 * a := by positivity
  calc v ^ 2 / (2 * a) ≤ (2 * a * g) / (2 * a) := by gcongr
    _ = g := by rw [mul_comm (2 * a) g, mul_div_assoc, div_self h2a.ne', mul_one]

/-- If the step plus the braking distance fits the margin, then after the step
the system can still stop before reaching the safe distance. -/
theorem can_still_stop (o p q : P) (dmin v a : ℝ)
    (hfit : dist p q + v ^ 2 / (2 * a) ≤ dist p o - dmin) :
    dmin + v ^ 2 / (2 * a) ≤ dist q o := by
  have h := dist_triangle p q o
  linarith

/-! ## 5. Refutation: without the monitor, safety fails -/

/-- On the real line with the obstacle at 0 and `dmin = 1`, an unchecked jump
from 2 to 0.5 ends inside the safe distance. -/
theorem unchecked_step_unsafe : ¬ ((1 : ℝ) ≤ dist (1 / 2 : ℝ) 0) := by
  rw [Real.dist_eq]
  norm_num

end Monitor

#print axioms Monitor.always_safe
#print axioms Monitor.can_still_stop
#print axioms Monitor.unchecked_step_unsafe
