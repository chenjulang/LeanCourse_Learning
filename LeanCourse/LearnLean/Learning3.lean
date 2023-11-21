
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan -- 反正切
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine -- 仿射

open scoped Real



namespace InnerProductGeometry -- 内积几何
  variable {V : Type*} [NormedAddCommGroup V] -- 赋范群是一个具有范数的加法群
  [InnerProductSpace ℝ V] -- 内积空间

  /-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
  theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V)
  : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2
  := by
    rw [norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
    exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end InnerProductGeometry



namespace EuclideanGeometry
  open InnerProductGeometry

  variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] -- 伪度量空间
    [NormedAddTorsor V P] --加性半范数群的torsor ?

  /-- **Pythagorean theorem**, if-and-only-if angle-at-point form. -/
  theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p1 p2 p3 : P)
  :
    dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2
    ↔
    ∠ p1 p2 p3 = π / 2
  := by
    erw [dist_comm p3 p2,
    dist_eq_norm_vsub V p1 p3,
    dist_eq_norm_vsub V p1 p2,
    dist_eq_norm_vsub V p2 p3,
    ← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
    vsub_sub_vsub_cancel_right p1,
    ← neg_vsub_eq_vsub_rev p2 p3,
    norm_neg]


end EuclideanGeometry
