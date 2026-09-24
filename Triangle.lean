/- Three planks covering a triangle have total relative width at least one. -/
module
public import Triangle.Proof
@[expose] public section
set_option autoImplicit false

namespace Triangle
open scoped BigOperators

abbrev Point := ℝ × ℝ

/-- A filled, nondegenerate triangle, including its edges and vertices. -/
def IsTriangle (T : Set Point) : Prop :=
  ∃ A B C : Point, ¬ Collinear ℝ ({A, B, C} : Set Point) ∧
    T = convexHull ℝ ({A, B, C} : Set Point)

/-- A plank represented by a nonconstant affine function f(x,y) = ax + by + c. -/
abbrev Plank :=
  {f : Point →ᵃ[ℝ] ℝ // ∃ x y, f x ≠ f y}

/-- Its points lie between the parallel lines where the function equals 0 and 1. -/
instance : Coe Plank (Set Point) :=
  ⟨fun P => {x | 0 ≤ P.val x ∧ P.val x ≤ 1}⟩

/-- Plank width divided by triangle width in the same direction.
`P.val '' T` is the image of T on the real line; its diameter is the shadow's length. -/
noncomputable def relativeWidth (T : Set Point) (P : Plank) : ℝ :=
  1 / Metric.diam (P.val '' T)

/-- If three planks cover a triangle, their relative widths sum to at least one.
`Fin 3` indexes the planks by 0, 1 and 2. -/
theorem three_planks_cover_triangle
    (T : Set Point) (triangle : IsTriangle T)
    (P : Fin 3 → Plank)
    (covers : T ⊆ ⋃ i, (P i : Set Point)) :
    1 ≤ ∑ i, relativeWidth T (P i) := by
  obtain ⟨A, B, C, noncollinear, rfl⟩ := triangle
  simpa only [relativeWidth, sub_zero] using
    _root_.TriangleProof.three_planks_cover_triangle
      A B C noncollinear (fun i => (P i).val) (fun _ => 0) (fun _ => 1)
      (fun i => (P i).property)
      (by intro i; norm_num) covers

end Triangle
