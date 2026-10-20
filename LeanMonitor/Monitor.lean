/-
Sample written for a formal-verification brief.
Synthetic scenario; it contains no client material.
-/
module

public import Mathlib

/-!
# A runtime safety monitor, proved over the reals

An untrusted controller proposes the next position. The monitor computes the
margin that would remain after the step and, through a threshold switch,
either accepts the proposal or applies a fallback (stay in place).

Model assumptions, stated so the theorems can be read correctly:
* discrete steps; the system moves exactly to the position the monitor outputs;
* a static obstacle and a fixed minimum distance `dmin`;
* the start is safe;
* the fallback "stay in place" can always be executed. A physical system would
  brake instead; section 4 proves the bound such a braking fallback needs.

Proved with no `sorry`:
1. the threshold switch selects the fallback exactly when the margin is below
   the threshold, and the monitor makes its decision through that switch;
2. a step accepted by the monitor never ends inside the safe distance, in any
   metric space (the Euclidean plane is one instance);
3. every state reachable under any sequence of proposals is safe;
4. with deceleration `a > 0`, if the braking distance `v² / (2a)` fits the
   margin left after a step, the system is still at least `dmin + v² / (2a)`
   away from the obstacle after that step;
5. without the monitor the invariant fails: from a safe start, one unchecked
   step reaches an unsafe state, and the monitor rejects exactly that step.
-/

public section

namespace Monitor

/-! ## 1. Threshold switch -/

inductive Mode
  | normal
  | fallback
  deriving DecidableEq, Repr

/-- Switch to the fallback when the margin is below the threshold. -/
noncomputable def nextMode (margin threshold : ℝ) : Mode :=
  if margin < threshold then Mode.fallback else Mode.normal

theorem nextMode_eq_fallback_iff (m t : ℝ) : nextMode m t = Mode.fallback ↔ m < t := by
  unfold nextMode
  split_ifs with h <;> simp [h]

theorem nextMode_eq_normal_iff (m t : ℝ) : nextMode m t = Mode.normal ↔ t ≤ m := by
  unfold nextMode
  split_ifs with h
  · simp [not_le.mpr h]
  · simp [not_lt.mp h]

/-! ## 2. The monitor, in an arbitrary metric space -/

variable {P : Type*} [MetricSpace P]

/-- Scenario parameters: the obstacle and the minimum safe distance. -/
structure Params (P : Type*) where
  obstacle : P
  dmin : ℝ

/-- Margin that would remain after moving from `p` to `q`. -/
noncomputable def margin (prm : Params P) (p q : P) : ℝ :=
  dist p prm.obstacle - prm.dmin - dist p q

/-- The monitor accepts the proposal unless the switch selects the fallback. -/
noncomputable def monitor (prm : Params P) (p proposed : P) : P :=
  match nextMode (margin prm p proposed) 0 with
  | Mode.normal => proposed
  | Mode.fallback => p

/-- A step no longer than the remaining margin keeps the safe distance. -/
theorem safe_after_step (o p q : P) (dmin : ℝ)
    (hstep : dist p q ≤ dist p o - dmin) : dmin ≤ dist q o := by
  have h := dist_triangle p q o
  linarith

/-- One monitored step preserves safety. -/
theorem monitor_safe (prm : Params P) (p proposed : P)
    (hp : prm.dmin ≤ dist p prm.obstacle) :
    prm.dmin ≤ dist (monitor prm p proposed) prm.obstacle := by
  unfold monitor
  split
  next h =>
    have h0 : 0 ≤ margin prm p proposed := (nextMode_eq_normal_iff _ _).mp h
    unfold margin at h0
    exact safe_after_step prm.obstacle p proposed prm.dmin (by linarith)
  next => exact hp

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

/-! ## 4. Braking distance -/

/-- Stopping distance `v² / (2a)` fits in the gap `g` when `v² ≤ 2 a g`. -/
theorem stop_within_gap (v a g : ℝ) (ha : 0 < a) (h : v ^ 2 ≤ 2 * a * g) :
    v ^ 2 / (2 * a) ≤ g := by
  have h2a : (0 : ℝ) < 2 * a := by positivity
  calc v ^ 2 / (2 * a) ≤ (2 * a * g) / (2 * a) := by gcongr
    _ = g := by rw [mul_comm (2 * a) g, mul_div_assoc, div_self h2a.ne', mul_one]

/-- With deceleration `a > 0`: if the braking distance fits the margin left
after the step, the system is still at least `dmin + v² / (2a)` from the
obstacle after the step. -/
theorem braking_fits_after_step (o p q : P) (dmin v a : ℝ) (ha : 0 < a)
    (hfit : v ^ 2 ≤ 2 * a * (dist p o - dmin - dist p q)) :
    dmin + v ^ 2 / (2 * a) ≤ dist q o := by
  have hb := stop_within_gap v a (dist p o - dmin - dist p q) ha hfit
  have h := dist_triangle p q o
  linarith

/-! ## 5. Refutation: without the monitor, the invariant fails -/

/-- Reachability without the monitor: every proposal is executed. -/
inductive ReachableUnchecked (start : P) : P → Prop
  | init : ReachableUnchecked start start
  | step {p : P} (proposed : P) :
      ReachableUnchecked start p → ReachableUnchecked start proposed

/-- The real line with the obstacle at 0 and minimum distance 1. -/
noncomputable def lineParams : Params ℝ := ⟨0, 1⟩

/-- From the safe start 2, one unchecked step reaches 1/2, inside the safe
distance. -/
theorem unchecked_breaks_invariant :
    lineParams.dmin ≤ dist (2 : ℝ) lineParams.obstacle ∧
    ReachableUnchecked (2 : ℝ) (1 / 2) ∧
    ¬ (lineParams.dmin ≤ dist (1 / 2 : ℝ) lineParams.obstacle) := by
  refine ⟨?_, .step _ .init, ?_⟩ <;> norm_num [lineParams, Real.dist_eq]

/-- The monitor rejects exactly that step: from 2 it stays at 2. -/
theorem monitor_rejects_unsafe_step : monitor lineParams (2 : ℝ) (1 / 2) = 2 := by
  have h : margin lineParams (2 : ℝ) (1 / 2) < 0 := by
    norm_num [margin, lineParams, Real.dist_eq]
  simp only [monitor, (nextMode_eq_fallback_iff _ _).mpr h]

end Monitor

end

#print axioms Monitor.nextMode_eq_fallback_iff
#print axioms Monitor.nextMode_eq_normal_iff
#print axioms Monitor.safe_after_step
#print axioms Monitor.monitor_safe
#print axioms Monitor.always_safe
#print axioms Monitor.always_safe_plane
#print axioms Monitor.stop_within_gap
#print axioms Monitor.braking_fits_after_step
#print axioms Monitor.unchecked_breaks_invariant
#print axioms Monitor.monitor_rejects_unsafe_step
