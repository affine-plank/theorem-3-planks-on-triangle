/- The proof supporting Triangle.lean. Only the triangle case is included. -/
module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Instances.ENNReal.Lemmas
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace TriangleProof
open Finset
open scoped BigOperators

/-! ## Normalized covers -/

/-- Each row records the values of one affine function at the three vertices.
Its minimum and maximum are normalized to `0` and `1`; its window is `[lo, hi]`.
Coverage is stated on all nonnegative barycentric coordinates of sum one. -/
structure Cover (n : ℕ) where
  g : Fin n → Fin 3 → ℝ
  σ : Fin n → Equiv.Perm (Fin 3)
  lo : Fin n → ℝ
  hi : Fin n → ℝ
  bounds : ∀ i j, 0 ≤ g i j ∧ g i j ≤ 1
  zero : ∀ i, g i (σ i 0) = 0
  one : ∀ i, g i (σ i 2) = 1
  ordered : ∀ i, lo i ≤ hi i
  covered : ∀ l : Fin 3 → ℝ, (∀ j, 0 ≤ l j) → ∑ j, l j = 1 →
    ∃ i, lo i ≤ ∑ j, l j * g i j ∧ (∑ j, l j * g i j) ≤ hi i

/-- In normalized coordinates, each relative width is simply `hi - lo`. -/
def Cover.width {n : ℕ} (C : Cover n) : ℝ := ∑ i, (C.hi i - C.lo i)

/-! ## Affine normalization -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The directional range on a three-generator convex hull. -/
def vertexSpread (v : Fin 3 → E) (f : E →ᵃ[ℝ] ℝ) : ℝ :=
  max (f (v 0)) (max (f (v 1)) (f (v 2))) -
    min (f (v 0)) (min (f (v 1)) (f (v 2)))

/-- Total interval width relative to the three vertex ranges. -/
def relativeWidthSum (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) : ℝ := ∑ k, (hi k - lo k) / vertexSpread v (f k)

private theorem max3_eq {s : Fin 3 → ℝ} {a : Fin 3} (h : ∀ i, s i ≤ s a) :
    max (s 0) (max (s 1) (s 2)) = s a := by
  fin_cases a <;> simp_all

private theorem min3_eq {s : Fin 3 → ℝ} {a : Fin 3} (h : ∀ i, s a ≤ s i) :
    min (s 0) (min (s 1) (s 2)) = s a := by
  fin_cases a <;> simp_all

/-- Affine windows on a three-generator hull give a normalized scalar cover
with exactly the same total relative width. -/
theorem exists_normalized_cover
    (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (hpos : ∀ k, 0 < vertexSpread v (f k)) (hle : ∀ k, lo k ≤ hi k)
    (hcover : ∀ X ∈ convexHull ℝ (Set.range v), ∃ k, lo k ≤ f k X ∧ f k X ≤ hi k) :
    ∃ C : Cover 3, C.width = relativeWidthSum v f lo hi := by
  let σ (k : Fin 3) := Tuple.sort (fun i => f k (v i))
  have hmono (k : Fin 3) : Monotone ((fun i => f k (v i)) ∘ σ k) :=
    Tuple.monotone_sort (fun i => f k (v i))
  have hlb (k i : Fin 3) : f k (v (σ k 0)) ≤ f k (v i) := by
    simpa using hmono k (Fin.zero_le ((σ k).symm i))
  have hub (k i : Fin 3) : f k (v i) ≤ f k (v (σ k 2)) := by
    simpa using hmono k (Fin.le_last ((σ k).symm i))
  let m (k : Fin 3) := f k (v (σ k 0))
  let W (k : Fin 3) := vertexSpread v (f k)
  have hW (k : Fin 3) : W k = f k (v (σ k 2)) - m k := by
    exact congrArg₂ (· - ·)
      (max3_eq (s := fun i => f k (v i)) (hub k))
      (min3_eq (s := fun i => f k (v i)) (a := σ k 0) (hlb k))
  let g (k i : Fin 3) := (f k (v i) - m k) / W k
  refine ⟨{
    g := g
    σ := σ
    lo := fun k => (lo k - m k) / W k
    hi := fun k => (hi k - m k) / W k
    bounds := fun k i => ⟨div_nonneg (sub_nonneg.mpr (hlb k i)) (hpos k).le,
      (div_le_one (show 0 < W k from hpos k)).mpr (by rw [hW]; exact sub_le_sub_right (hub k i) _)⟩
    zero := fun k => by simp [g, m]
    one := fun k => by dsimp [g]; rw [← hW]; exact div_self (hpos k).ne'
    ordered := fun k => (div_le_div_iff_of_pos_right (hpos k)).mpr
      (sub_le_sub_right (hle k) _)
    covered := ?_ }, ?_⟩
  · intro l hl0 hl1
    let X := univ.affineCombination ℝ v l
    obtain ⟨k, hk⟩ := hcover X (affineCombination_mem_convexHull (fun j _ => hl0 j) hl1)
    have heval : f k X = ∑ j, l j * f k (v j) := by
      simpa [X, affineCombination_eq_linear_combination, hl1] using
        univ.map_affineCombination v l hl1 (f k)
    have hlevel : (∑ j, l j * g k j) = (f k X - m k) / W k := by
      simp only [g, ← mul_div_assoc, mul_sub, ← sum_div, sum_sub_distrib,
        ← sum_mul, hl1, one_mul, ← heval]
    refine ⟨k, ?_, ?_⟩ <;> rw [hlevel]
    · exact (div_le_div_iff_of_pos_right (hpos k)).mpr (sub_le_sub_right hk.1 _)
    · exact (div_le_div_iff_of_pos_right (hpos k)).mpr (sub_le_sub_right hk.2 _)
  · change (∑ k, ((hi k - m k) / W k - (lo k - m k) / W k)) = _
    simp only [← sub_div, sub_sub_sub_cancel_right]
    rfl

/-! ## Removing a plank -/

private theorem level_bounds {n : ℕ} (C : Cover n) (l : Fin 3 → ℝ)
    (hl0 : ∀ k, 0 ≤ l k) (hl1 : ∑ k, l k = 1) (i : Fin n) :
    0 ≤ ∑ k, l k * C.g i k ∧ (∑ k, l k * C.g i k) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun k _ => mul_nonneg (hl0 k) (C.bounds i k).1), ?_⟩
  calc
    (∑ k, l k * C.g i k) ≤ ∑ k, l k :=
      Finset.sum_le_sum (fun k _ => mul_le_of_le_one_right (hl0 k) (C.bounds i k).2)
    _ = 1 := hl1

/-- A deficient cover with a window reaching `0` or `1` gives a deficient
cover with that row deleted. The retained normalized rows and endpoint
permutations are unchanged; only their window endpoints are pulled back. -/
theorem drop_bad_window {n : ℕ} (C : Cover (n + 1)) (hsmall : C.width < 1)
    (j : Fin (n + 1)) (hbad : C.lo j ≤ 0 ∨ 1 ≤ C.hi j) :
    ∃ D : Cover n, D.width < 1 := by
  let B := ∑ k : Fin n, (C.hi (j.succAbove k) - C.lo (j.succAbove k))
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun k _ => sub_nonneg.mpr (C.ordered _))
  have hsum : C.width = C.hi j - C.lo j + B :=
    Fin.sum_univ_succAbove (fun i => C.hi i - C.lo i) j
  have hB : B < 1 - (C.hi j - C.lo j) := by linarith only [hsum, hsmall]
  obtain ⟨r, hBr, hrw⟩ := exists_between hB
  have hr0 : 0 < r := hB0.trans_lt hBr
  have hr1 : r < 1 := by linarith only [hrw, C.ordered j]
  -- The chosen vertex makes the entire shrunken simplex miss the deleted window.
  obtain ⟨v, hv⟩ : ∃ v : Fin 3,
      (C.g j v = 1 ∧ C.hi j < 1 - r) ∨ (C.g j v = 0 ∧ r < C.lo j) := by
    rcases hbad with hbad | hbad
    · exact ⟨C.σ j 2, Or.inl ⟨C.one j, by linarith only [hrw, hbad]⟩⟩
    · exact ⟨C.σ j 0, Or.inr ⟨C.zero j, by linarith only [hrw, hbad]⟩⟩
  let q (l : Fin 3 → ℝ) (k : Fin 3) := (if k = v then 1 - r else 0) + r * l k
  have hq (l : Fin 3 → ℝ) (i : Fin (n + 1)) :
      (∑ k, q l k * C.g i k) = (1 - r) * C.g i v + r * (∑ k, l k * C.g i k) := by
    simp [q, add_mul, ite_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  refine ⟨{
    g := fun k => C.g (j.succAbove k)
    σ := fun k => C.σ (j.succAbove k)
    lo := fun k => (C.lo (j.succAbove k) - (1 - r) * C.g (j.succAbove k) v) / r
    hi := fun k => (C.hi (j.succAbove k) - (1 - r) * C.g (j.succAbove k) v) / r
    bounds := fun k => C.bounds (j.succAbove k)
    zero := fun k => C.zero (j.succAbove k)
    one := fun k => C.one (j.succAbove k)
    ordered := fun k => (div_le_div_iff_of_pos_right hr0).mpr
      (sub_le_sub_right (C.ordered (j.succAbove k)) _)
    covered := ?_ }, ?_⟩
  · intro l hl0 hl1
    have hq0 (k : Fin 3) : 0 ≤ q l k := by
      dsimp [q]
      exact add_nonneg (by split_ifs <;> linarith only [hr1]) (mul_nonneg hr0.le (hl0 k))
    have hq1 : ∑ k, q l k = 1 := by
      simp [q, Finset.sum_add_distrib, ← Finset.mul_sum, hl1]
    obtain ⟨i, hi⟩ := C.covered (q l) hq0 hq1
    rw [hq] at hi
    have hij : i ≠ j := by
      intro he
      subst i
      have hb := level_bounds C l hl0 hl1 j
      rcases hv with ⟨hv, hh⟩ | ⟨hv, hh⟩
      · rw [hv] at hi
        nlinarith only [hi.2, hh, mul_nonneg hr0.le hb.1]
      · rw [hv] at hi
        nlinarith only [hi.1, hh, mul_le_mul_of_nonneg_left hb.2 hr0.le]
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    refine ⟨k, ?_, ?_⟩
    · apply (div_le_iff₀ hr0).mpr
      linarith only [hi.1]
    · apply (le_div_iff₀ hr0).mpr
      linarith only [hi.2]
  · change (∑ k : Fin n,
      ((C.hi (j.succAbove k) - (1 - r) * C.g (j.succAbove k) v) / r -
       (C.lo (j.succAbove k) - (1 - r) * C.g (j.succAbove k) v) / r)) < 1
    calc
      _ = B / r := by
        simp only [← sub_div, sub_sub_sub_cancel_right, ← sum_div, B]
      _ < 1 := (div_lt_one hr0).mpr hBr

/-! ## The side-length inequalities -/

/-- Sum the three values starting at any cyclic label. -/
theorem sum_cyclic {α : Type*} [AddCommMonoid α] (f : Fin 3 → α) (i : Fin 3) :
    (∑ j, f j) = f i + f (i + 1) + f (i + 2) := by
  rw [← Equiv.sum_comp (Equiv.addLeft i) f]
  simp only [Fin.sum_univ_three, Equiv.coe_addLeft, add_zero]

/-- A deficient total budget and three side-trace budgets propagate `u₀ ≤ v₀`
to `uᵢ < vᵢ` everywhere and force a lower gap inequality to fail.
Only `u` needs a nonnegativity assumption; the conclusion also makes `v` positive. -/
theorem trace_deficit_forces_lower_gap (d u v : Fin 3 → ℝ)
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hu : ∀ i, 0 ≤ u i)
    (hS : (∑ i, (d i * u i + (1 - d i) * v i)) < 1)
    (htrace : ∀ i, 1 ≤ d i * u i + (1 - d i) * v i + u (i + 1) + v (i + 2))
    (hstart : u 0 ≤ v 0) :
    (∀ i, u i < v i) ∧ ∃ i, d i * u i + u (i + 1) < d i := by
  let h := fun i => v i - u i
  have he (i : Fin 3) : 0 < 1 - d i := sub_pos.mpr (hd1 i)
  -- Subtracting the total budget from each trace propagates the sign of h.
  have hcycle (i : Fin 3) :
      (1 - d (i + 1)) * h (i + 1) < d (i + 2) * h (i + 2) := by
    have hs := hS
    rw [sum_cyclic _ i] at hs
    dsimp [h]
    nlinarith only [htrace i, hs]
  have hnext (i : Fin 3) (hi : 0 ≤ h (i + 1)) : 0 < h (i + 2) :=
    pos_of_mul_pos_right
      (lt_of_le_of_lt (mul_nonneg (le_of_lt (he _)) hi) (hcycle i))
      (le_of_lt (hd0 _))
  have hh1 : 0 < h 1 := hnext 2 (sub_nonneg.mpr hstart)
  have hh2 : 0 < h 2 := hnext 0 (le_of_lt hh1)
  have hh0 : 0 < h 0 := hnext 1 (le_of_lt hh2)
  have hh (i : Fin 3) : 0 < h i := by fin_cases i <;> assumption
  -- Positive h makes the unweighted sum of u smaller than the budget.
  have hless (i : Fin 3) : u i < d i * u i + (1 - d i) * v i := by
    have hi := mul_pos (he i) (hh i)
    dsimp [h] at hi
    nlinarith only [hi]
  have hU : (∑ i, u i) < 1 :=
    (sum_le_sum (fun i _ => (hless i).le)).trans_lt hS
  refine ⟨fun i => sub_pos.mp (hh i), ?_⟩
  by_contra hfail
  have hgu (i : Fin 3) : d i ≤ d i * u i + u (i + 1) :=
    le_of_not_gt (fun hi => hfail ⟨i, hi⟩)
  -- Every lower gap inequality would give a strict comparison in the opposite direction.
  have hlower (i : Fin 3) : d i * u (i + 2) < (1 - d i) * u (i + 1) := by
    have hi := hgu i
    have hiU := mul_pos (hd0 i) (sub_pos.mpr hU)
    rw [sum_cyclic _ i] at hiU
    nlinarith only [hi, hiU]
  -- Combine the two comparisons before multiplying; no uᵢ is cancelled.
  let a (i : Fin 3) := d i * h i
  have ha (i : Fin 3) : 0 < a i := mul_pos (hd0 i) (hh i)
  have step (i : Fin 3) : a i * u (i + 2) < a (i + 1) * u (i + 1) := by
    calc
      a i * u (i + 2) < ((1 - d i) * h i) * u (i + 1) := by
        simpa only [a, mul_assoc, mul_left_comm, mul_comm] using
          mul_lt_mul_of_pos_right (hlower i) (hh i)
      _ ≤ a (i + 1) * u (i + 1) := by
        have hi : (1 - d i) * h i ≤ a (i + 1) := by
          simpa only [a, add_assoc, show (2 : Fin 3) + 1 = 0 by decide,
            show (2 : Fin 3) + 2 = 1 by decide, add_zero] using (hcycle (i + 2)).le
        exact mul_le_mul_of_nonneg_right hi (hu _)
  -- After multiplication by aᵢ₊₂, the three comparisons form a strict cycle.
  have h0 := mul_lt_mul_of_pos_left (step 0) (ha 2)
  have h1 := mul_lt_mul_of_pos_left (step 1) (ha 0)
  have h2 := mul_lt_mul_of_pos_left (step 2) (ha 1)
  dsimp at h0 h1 h2
  linarith only [h0, h1, h2]


/-! ## Covering an interval -/

/-- The three traces `[0, 1−A]`, `[B, 1]` and `[C, D]` cover `[0,1]`
only if the first two meet or the third bridges their gap. -/
theorem cover3 {A B C D : ℝ} (hA1 : A ≤ 1) (hB1 : B ≤ 1)
    (hcov : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → s ≤ 1 - A ∨ B ≤ s ∨ (C ≤ s ∧ s ≤ D)) :
    (A + B ≤ 1) ∨ (C ≤ 1 - A ∧ B ≤ D) := by
  rcases le_or_gt (A + B) 1 with h | h
  · exact Or.inl h
  -- The open gap lies in the band, hence so does its closure.
  have hgap : Set.Ioo (1 - A) B ⊆ Set.Icc C D := fun s ⟨hs1, hs2⟩ =>
    ((hcov s (by linarith) (by linarith)).resolve_left (by linarith)).resolve_left (by linarith)
  have := closure_minimal hgap isClosed_Icc
  rw [closure_Ioo (by linarith : 1 - A ≠ B), Set.Icc_subset_Icc_iff (by linarith)] at this
  exact Or.inr this

/-! ## The cyclic covering argument -/

/-- The level of window `i` is `dᵢ λᵢ + λᵢ₊₂`; the window contains its
middle vertex. The parameters `u, v` are the covered side fractions. -/
def CyclicCover (d u v : Fin 3 → ℝ) : Prop :=
  ∀ l : Fin 3 → ℝ, (∀ i, 0 ≤ l i) → ∑ i, l i = 1 →
    ∃ i, d i * (1 - u i) ≤ d i * l i + l (i + 2) ∧
      d i * l i + l (i + 2) ≤ d i + (1 - d i) * v i

private theorem three_indices : ∀ i j : Fin 3, j = i ∨ j = i + 1 ∨ j = i + 2 := by decide
private theorem add_one_one : ∀ i : Fin 3, i + 1 + 1 = i + 2 := by decide
private theorem add_one_two : ∀ i : Fin 3, i + 1 + 2 = i := by decide
private theorem add_two_one : ∀ i : Fin 3, i + 2 + 1 = i := by decide
private theorem add_two_two : ∀ i : Fin 3, i + 2 + 2 = i + 1 := by decide

/-- Each covered side either has meeting endpoint intervals, or the third
window reaches both ends of the gap between them. -/
theorem CyclicCover.side_alternative {d u v : Fin 3 → ℝ}
    (cover : CyclicCover d u v) (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (i : Fin 3) :
    1 ≤ u (i + 1) + v (i + 2) ∨
      (d i ≤ d i * u i + u (i + 1) ∧ 1 - d i ≤ (1 - d i) * v i + v (i + 2)) := by
  have hedge (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
      s ≤ u (i + 1) ∨ 1 - v (i + 2) ≤ s ∨
        (d i * (1 - u i) ≤ s ∧ s ≤ d i + (1 - d i) * v i) := by
    let l : Fin 3 → ℝ := fun j => ![0, 1 - s, s] (j - i)
    have hl0 (j : Fin 3) : 0 ≤ l j := by
      dsimp [l]
      generalize j - i = k
      fin_cases k <;> simp [hs0, sub_nonneg.mpr hs1]
    have hl1 : ∑ j, l j = 1 := by
      rw [sum_cyclic l i]
      simp [l]
    have hli : l i = 0 := by simp [l]
    have hlp : l (i + 1) = 1 - s := by simp [l]
    have hlq : l (i + 2) = s := by simp [l]
    obtain ⟨j, hj⟩ := cover l hl0 hl1
    rcases three_indices i j with rfl | rfl | rfl
    · exact Or.inr (Or.inr (by simpa only [hli, hlq, mul_zero, zero_add] using hj))
    · left
      rw [add_one_two, hli, hlp, add_zero] at hj
      have h := le_of_mul_le_mul_left hj.1 (hd0 (i + 1))
      linarith only [h]
    · right; left
      rw [add_two_two, hlp, hlq] at hj
      have h : (1 - d (i + 2)) * (1 - v (i + 2)) ≤ (1 - d (i + 2)) * s := by
        nlinarith only [hj.2]
      exact le_of_mul_le_mul_left h (sub_pos.mpr (hd1 _))
  have h := cover3
    (A := 1 - u (i + 1)) (B := 1 - v (i + 2)) (C := d i * (1 - u i)) (D := d i + (1 - d i) * v i)
    (by linarith only [hu (i + 1)]) (by linarith only [hv (i + 2)])
    (by simpa only [sub_sub_cancel] using hedge)
  rcases h with h | ⟨hlo, hhi⟩
  · exact Or.inl (by linarith only [h])
  · exact Or.inr ⟨by nlinarith only [hlo], by nlinarith only [hhi]⟩

/-- If each side is covered by its two vertex planks, a small total width
leaves an uncovered point. Its coordinates are the cyclically shifted widths,
with the remaining mass divided equally between the three vertices. -/
private theorem CyclicCover.width_bound_of_sides {d u v : Fin 3 → ℝ}
    (cover : CyclicCover d u v) (hd1 : ∀ i, d i < 1) (hu : ∀ i, 0 ≤ u i)
    (huw : ∀ i, u i ≤ d i * u i + (1 - d i) * v i)
    (caps : ∀ i, 1 ≤ u (i + 1) + v (i + 2)) :
    1 ≤ ∑ i, (d i * u i + (1 - d i) * v i) := by
  by_contra! hS
  let w (j : Fin 3) := d j * u j + (1 - d j) * v j
  -- Shift the three widths cyclically and share the deficit equally.
  let r := (1 - ∑ j, w j) / 3
  have hr : 0 < r := div_pos (sub_pos.mpr hS) (by norm_num)
  let l (j : Fin 3) := w (j + 2) + r
  have hl0 (j : Fin 3) : 0 ≤ l j := add_nonneg ((hu _).trans (huw _)) hr.le
  have hl1 : ∑ j, l j = 1 := by
    dsimp [l, r]
    simp only [Fin.sum_univ_three]
    dsimp
    ring
  have hlcap (j : Fin 3) : 1 ≤ l j + v j := by
    have hc := caps (j + 1)
    rw [add_one_one, add_one_two] at hc
    change 1 ≤ w (j + 2) + r + v j
    linarith only [hc, huw (j + 2), hr]
  obtain ⟨j, hj⟩ := cover l hl0 hl1
  have hnonpos : (1 - d j) * (1 - l j - v j) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr (hd1 j)).le
      (by linarith only [hlcap j])
  have hid : l (j + 1) = w j + r := by simp only [l, add_one_two]
  -- The lower-bound residual is -r + (1 - dⱼ) * (1 - lⱼ - vⱼ), hence negative.
  have hgap : d j * l j + l (j + 2) - d j * (1 - u j) ≤ -r := by
    have hs := hl1
    rw [sum_cyclic _ j] at hs
    dsimp [w] at hid
    linear_combination hnonpos + hs - hid
  linarith only [hj.1, hgap, hr]

private theorem no_deficient_cover_of_le {d u v : Fin 3 → ℝ}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (cover : CyclicCover d u v)
    (hS : (∑ i, (d i * u i + (1 - d i) * v i)) < 1) (hstart : u 0 ≤ v 0) : False := by
  have side := cover.side_alternative hd0 hd1 hu hv
  have htrace (i : Fin 3) : 1 ≤ d i * u i + (1 - d i) * v i + u (i + 1) + v (i + 2) := by
    rcases side i with hc | ⟨hlo, hhi⟩
    · have hw := add_nonneg (mul_nonneg (hd0 i).le (hu i))
        (mul_nonneg (sub_nonneg.mpr (hd1 i).le) (hv i))
      linarith only [hc, hw]
    · linarith only [hlo, hhi]
  obtain ⟨huv, i, hi⟩ := trace_deficit_forces_lower_gap d u v hd0 hd1 hu hS htrace hstart
  let w (j : Fin 3) := d j * u j + (1 - d j) * v j
  have huw (j : Fin 3) : u j ≤ w j := by
    have h := mul_nonneg (sub_pos.mpr (hd1 j)).le (sub_nonneg.mpr (huv j).le)
    dsimp [w]
    nlinarith only [h]
  have hcap : 1 ≤ u (i + 1) + v (i + 2) := (side i).resolve_right (fun h => (not_lt_of_ge h.1) hi)
  -- A gap followed by endpoint coverage would already spend the whole budget.
  have prev (j : Fin 3) (hnext : 1 ≤ u (j + 2) + v j) :
      1 ≤ u (j + 1) + v (j + 2) := by
    rcases side j with h | ⟨hgap, _⟩
    · exact h
    have hs : w j + w (j + 1) + w (j + 2) < 1 := by
      rw [← sum_cyclic w j]
      exact hS
    have hbudget : w j + u (j + 1) + u (j + 2) < 1 :=
      (add_le_add (add_le_add le_rfl (huw (j + 1))) (huw (j + 2))).trans_lt hs
    have hleg := mul_nonneg (hd0 j).le (hu (j + 2))
    have hcap := mul_nonneg (sub_pos.mpr (hd1 j)).le (sub_nonneg.mpr hnext)
    dsimp [w] at hbudget
    exfalso
    nlinarith only [hbudget, hgap, hleg, hcap]
  have hp : 1 ≤ u i + v (i + 1) := by
    simpa only [add_two_one, add_two_two] using prev (i + 2) (by simpa only [add_two_two] using hcap)
  have hq : 1 ≤ u (i + 2) + v i := by
    simpa only [add_one_one, add_one_two] using prev (i + 1) (by simpa only [add_one_two] using hp)
  have caps (j : Fin 3) : 1 ≤ u (j + 1) + v (j + 2) := by
    rcases three_indices i j with rfl | rfl | rfl
    · exact hcap
    · simpa only [add_one_one, add_one_two] using hq
    · simpa only [add_two_one, add_two_two] using hp
  exact (not_le_of_gt hS) (cover.width_bound_of_sides hd1 hu huw caps)

/-- Reversing the cyclic order and all level scales exchanges `u` and `v`. -/
theorem CyclicCover.reflect {d u v : Fin 3 → ℝ} (cover : CyclicCover d u v) :
    CyclicCover (fun i => 1 - d (2 * i)) (fun i => v (2 * i)) (fun i => u (2 * i)) := by
  intro l hl0 hl1
  obtain ⟨i, hi⟩ := cover (fun i => l (2 * i)) (fun i => hl0 _) (by
    simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using hl1)
  refine ⟨2 * i, ?_⟩
  fin_cases i <;> simp only [Fin.sum_univ_three] at hl1 <;>
    dsimp at hi ⊢ <;> constructor <;> nlinarith only [hi.1, hi.2, hl1]

/-- Three cyclic affine windows containing their middle vertices and
covering the whole triangle have total width at least one. -/
theorem cyclic_cover_width_bound (d u v : Fin 3 → ℝ)
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (cover : CyclicCover d u v) :
    1 ≤ ∑ i, (d i * u i + (1 - d i) * v i) := by
  by_contra! hS
  rcases le_total (u 0) (v 0) with hstart | hstart
  · exact no_deficient_cover_of_le hd0 hd1 hu hv cover hS hstart
  · apply no_deficient_cover_of_le (d := fun i => 1 - d (2 * i)) (u := fun i => v (2 * i))
      (v := fun i => u (2 * i))
      (fun i => sub_pos.mpr (hd1 _)) (fun i => by linarith only [hd0 (2 * i)])
      (fun i => hv _) (fun i => hu _) cover.reflect _ hstart
    calc
      _ = ∑ i, (d i * u i + (1 - d i) * v i) := by simp only [Fin.sum_univ_three]; dsimp; ring
      _ < 1 := hS

/-- The scalar endgame in the original lower and upper window endpoints.
Only the strict middle levels and coverage of the whole simplex are needed. -/
theorem canonical_cover_width_bound (d lo hi : Fin 3 → ℝ)
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hlo : ∀ i, lo i ≤ d i) (hhi : ∀ i, d i ≤ hi i)
    (cover : ∀ l : Fin 3 → ℝ, (∀ i, 0 ≤ l i) → ∑ i, l i = 1 →
      ∃ i, lo i ≤ d i * l i + l (i + 2) ∧ d i * l i + l (i + 2) ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) := by
  let u (i : Fin 3) := (d i - lo i) / d i
  let v (i : Fin 3) := (hi i - d i) / (1 - d i)
  have hdu (i : Fin 3) : d i * u i = d i - lo i := mul_div_cancel₀ _ (hd0 i).ne'
  have hev (i : Fin 3) : (1 - d i) * v i = hi i - d i := mul_div_cancel₀ _ (sub_pos.mpr (hd1 i)).ne'
  have hl (i : Fin 3) : d i * (1 - u i) = lo i := by nlinarith only [hdu i]
  have hh (i : Fin 3) : d i + (1 - d i) * v i = hi i := by linarith only [hev i]
  have hw (i : Fin 3) : d i * u i + (1 - d i) * v i = hi i - lo i := by
    linarith only [hdu i, hev i]
  have h := cyclic_cover_width_bound d u v hd0 hd1
    (fun i => div_nonneg (sub_nonneg.mpr (hlo i)) (hd0 i).le)
    (fun i => div_nonneg (sub_nonneg.mpr (hhi i)) (sub_nonneg.mpr (hd1 i).le)) (by
      intro l hl0 hl1
      obtain ⟨i, hi⟩ := cover l hl0 hl1
      exact ⟨i, by rwa [hl, hh]⟩)
  simpa only [hw] using h

/-! ## Assigning vertices to planks -/

private theorem endpoints (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (hm : σ 1 = i) :
    (σ 0 = i + 1 ∧ σ 2 = i + 2) ∨ (σ 0 = i + 2 ∧ σ 2 = i + 1) := by
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  omega

/-- At most three normalized windows strictly inside `(0,1)` cannot cover
the barycentric triangle with total width less than one. Vertex values may tie;
only the two specified endpoint values are excluded by an interior window. -/
theorem interior_width_bound {n : ℕ} (C : Cover n) (hn : n ≤ 3)
    (hlo : ∀ i, 0 < C.lo i) (hhi : ∀ i, C.hi i < 1) : 1 ≤ C.width := by
  have hvertices (i : Fin 3) : ∃ k, C.lo k ≤ C.g k i ∧ C.g k i ≤ C.hi k := by
    obtain ⟨k, hk⟩ := C.covered (fun j => if j = i then 1 else 0)
      (fun j => by split_ifs <;> norm_num) (by simp)
    exact ⟨k, by simpa using hk⟩
  have hmiddle (k : Fin n) (i : Fin 3)
      (hi : C.lo k ≤ C.g k i ∧ C.g k i ≤ C.hi k) : C.σ k 1 = i := by
    obtain ⟨j, rfl⟩ := (C.σ k).surjective i
    fin_cases j
    · have hz : C.lo k ≤ C.g k (C.σ k 0) := hi.1
      rw [C.zero] at hz
      exact ((not_le_of_gt (hlo k)) hz).elim
    · rfl
    · have ho : C.g k (C.σ k 2) ≤ C.hi k := hi.2
      rw [C.one] at ho
      exact ((not_le_of_gt (hhi k)) ho).elim
  -- Choose each vertex's covering row once. Its middle label returns that vertex.
  choose owner howner using hvertices
  have hmid : Function.LeftInverse (fun k => C.σ k 1) owner :=
    fun i => hmiddle (owner i) i (howner i)
  have hthree : 3 ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective owner hmid.injective
  have hn3 : n = 3 := Nat.le_antisymm hn hthree
  subst n
  let π : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective owner (Finite.injective_iff_bijective.mp hmid.injective)
  have hπ (i : Fin 3) : C.σ (π i) 1 = i := hmid i
  have hown (i : Fin 3) : C.lo (π i) ≤ C.g (π i) i ∧ C.g (π i) i ≤ C.hi (π i) := howner i
  -- Reverse a row's scale when needed, so its next vertex is 0 and its previous is 1.
  let rev (i : Fin 3) : Prop := C.σ (π i) 0 = i + 2
  let r (i j : Fin 3) := if rev i then 1 - C.g (π i) j else C.g (π i) j
  let d (i : Fin 3) := r i i
  let a (i : Fin 3) := if rev i then 1 - C.hi (π i) else C.lo (π i)
  let b (i : Fin 3) := if rev i then 1 - C.lo (π i) else C.hi (π i)
  have hends (i : Fin 3) : r i (i + 1) = 0 ∧ r i (i + 2) = 1 := by
    rcases endpoints (C.σ (π i)) i (hπ i) with ⟨h0, h2⟩ | ⟨h0, h2⟩ <;>
      simp [r, rev, ← h0, ← h2, C.zero, C.one]
  have hlevels (i : Fin 3) (l : Fin 3 → ℝ) :
      (∑ j, l j * r i j) = d i * l i + l (i + 2) := by
    rw [sum_cyclic _ i, (hends i).1, (hends i).2]
    change l i * d i + l (i + 1) * 0 + l (i + 2) * 1 = _
    ring
  have hwindow (i : Fin 3) : 0 < a i ∧ a i ≤ d i ∧ d i ≤ b i ∧ b i < 1 := by
    dsimp [d, r, a, b]
    split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith only [hlo (π i), hhi (π i), (hown i).1, (hown i).2]
  have hcost : (∑ i, (b i - a i)) = C.width := by
    calc
      (∑ i, (b i - a i)) = ∑ i, (C.hi (π i) - C.lo (π i)) := by
        apply sum_congr rfl
        intro i _
        dsimp [a, b]; split_ifs <;> ring
      _ = C.width := Equiv.sum_comp π (fun i => C.hi i - C.lo i)
  have hcover (l : Fin 3 → ℝ) (hl0 : ∀ j, 0 ≤ l j) (hl1 : ∑ j, l j = 1) :
      ∃ i, a i ≤ d i * l i + l (i + 2) ∧ d i * l i + l (i + 2) ≤ b i := by
    obtain ⟨k, hk⟩ := C.covered l hl0 hl1
    obtain ⟨i, rfl⟩ := π.surjective k
    have hw : a i ≤ ∑ j, l j * r i j ∧ (∑ j, l j * r i j) ≤ b i := by
      dsimp [a, b, r]
      split_ifs
      · simp only [mul_sub, mul_one, sum_sub_distrib, hl1]
        exact ⟨by linarith only [hk.2], by linarith only [hk.1]⟩
      · exact hk
    exact ⟨i, by simpa only [hlevels] using hw⟩
  have h := canonical_cover_width_bound d a b
    (fun i => (hwindow i).1.trans_le (hwindow i).2.1)
    (fun i => (hwindow i).2.2.1.trans_lt (hwindow i).2.2.2)
    (fun i => (hwindow i).2.1) (fun i => (hwindow i).2.2.1) hcover
  rwa [hcost] at h

/-! ## The normalized width bound -/

/-- Remove an endpoint window from a deficient cover. If none exists,
every plank owns a different middle vertex, so the cyclic argument applies. -/
theorem width_bound {n : ℕ} (C : Cover n) (hn : n ≤ 3) : 1 ≤ C.width := by
  induction n with
  | zero =>
    obtain ⟨i, _⟩ := C.covered (fun j => if j = 0 then 1 else 0)
      (fun j => by split_ifs <;> norm_num) (by simp)
    exact i.elim0
  | succ n ih =>
    by_contra hs
    by_cases hbad : ∃ j, C.lo j ≤ 0 ∨ 1 ≤ C.hi j
    · obtain ⟨j, hj⟩ := hbad
      obtain ⟨D, hD⟩ := drop_bad_window C (lt_of_not_ge hs) j hj
      exact (not_le_of_gt hD) (ih D (by omega))
    · simp only [not_exists, not_or, not_le] at hbad
      exact hs (interior_width_bound C hn (fun i => (hbad i).1) (fun i => (hbad i).2))

/-- The three functions need only have positive ranges on the generators.
No ambient dimension, affine independence, or compactness assumption is used. -/
theorem sum_relative_width_ge_one
    (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (hpos : ∀ k, 0 < vertexSpread v (f k)) (hle : ∀ k, lo k ≤ hi k)
    (hcover : ∀ X ∈ convexHull ℝ (Set.range v), ∃ k, lo k ≤ f k X ∧ f k X ≤ hi k) :
    1 ≤ relativeWidthSum v f lo hi := by
  obtain ⟨C, hwidth⟩ := exists_normalized_cover v f lo hi hpos hle hcover
  simpa only [hwidth] using width_bound C (by decide)

/-! ## Returning to the geometric triangle -/

abbrev Point := ℝ × ℝ

/-- Three noncollinear points of the plane affinely span it. -/
private theorem affineSpan_eq_top_of_not_collinear (A B C : Point)
    (h : ¬ Collinear ℝ ({A, B, C} : Set Point)) :
    affineSpan ℝ ({A, B, C} : Set Point) = ⊤ := by
  have hind : AffineIndependent ℝ ![A, B, C] := affineIndependent_iff_not_collinear_set.mpr h
  simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union] using
    hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)

/-- An affine function equal at the three vertices of a triangle is constant. -/
private theorem eq_const_of_vertices (A B C : Point) (h : ¬ Collinear ℝ ({A, B, C} : Set Point))
    (f : Point →ᵃ[ℝ] ℝ) (hB : f B = f A) (hC : f C = f A) :
    f = AffineMap.const ℝ Point (f A) := by
  refine AffineMap.ext_on (affineSpan_eq_top_of_not_collinear A B C h) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> simp [hB, hC]

/-- Positive vertex range. A nonconstant affine function takes two different values at the
vertices of a nondegenerate triangle: its vertex spread `max − min` is positive. -/
private theorem vertex_range_pos (A B C : Point) (h : ¬ Collinear ℝ ({A, B, C} : Set Point))
    (f : Point →ᵃ[ℝ] ℝ) (hf : ∃ x y, f x ≠ f y) :
    min (f A) (min (f B) (f C)) < max (f A) (max (f B) (f C)) := by
  by_contra! hle
  -- If the maximum is at most the minimum, all three vertex values coincide.
  simp only [max_le_iff, le_min_iff] at hle
  obtain ⟨⟨_, hBA, hCA⟩, ⟨hAB, _, _⟩, ⟨hAC, _, _⟩⟩ := hle
  have hB : f B = f A := le_antisymm hBA hAB
  have hC : f C = f A := le_antisymm hCA hAC
  obtain ⟨x, y, hxy⟩ := hf
  apply hxy
  rw [eq_const_of_vertices A B C h f hB hC]
  simp

/-- The affine shadow fills exactly the interval between its extreme vertex values. -/
private theorem image_hull_eq_Icc (A B C : Point) (f : Point →ᵃ[ℝ] ℝ) :
    f '' convexHull ℝ ({A, B, C} : Set Point) =
      Set.Icc (min (f A) (min (f B) (f C))) (max (f A) (max (f B) (f C))) := by
  rw [f.image_convexHull]
  simp only [Set.image_insert_eq, Set.image_singleton]
  have hm := (isLeast_pair (a := f B) (b := f C)).insert (f A)
  have hM := (isGreatest_pair (a := f B) (b := f C)).insert (f A)
  refine Set.Subset.antisymm
    (convexHull_min (fun x hx => ⟨hm.2 hx, hM.2 hx⟩) (convex_Icc _ _)) ?_
  exact (convex_convexHull ℝ _).ordConnected.out
    (subset_convexHull ℝ _ hm.1) (subset_convexHull ℝ _ hM.1)

/-- Taking the convex hull does not change the diameter of the three vertex values. -/
theorem diam_eq_vertices (A B C : Point) (f : Point →ᵃ[ℝ] ℝ) :
    Metric.diam (f '' convexHull ℝ ({A, B, C} : Set Point)) =
      max (f A) (max (f B) (f C)) - min (f A) (min (f B) (f C)) := by
  rw [image_hull_eq_Icc]
  exact Real.diam_Icc ((min_le_left _ _).trans (le_max_left _ _))

/-- Three nonconstant affine-function planks covering an arbitrary
noncollinear triangle have total relative width at least one, with each
denominator the diameter of the affine image of that entire triangle. -/
theorem three_planks_cover_triangle
    (A B C : Point) (noncollinear : ¬ Collinear ℝ ({A, B, C} : Set Point))
    (f : Fin 3 → (Point →ᵃ[ℝ] ℝ)) (lo hi : Fin 3 → ℝ)
    (nonconstant : ∀ i, ∃ x y, f i x ≠ f i y) (ordered : ∀ i, lo i ≤ hi i)
    (covers : convexHull ℝ ({A, B, C} : Set Point) ⊆
      ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) :
    1 ≤ ∑ i, (hi i - lo i) /
      Metric.diam ((f i) '' convexHull ℝ ({A, B, C} : Set Point)) := by
  have hpos (i : Fin 3) : 0 < vertexSpread ![A, B, C] (f i) :=
    sub_pos.mpr (vertex_range_pos A B C noncollinear (f i) (nonconstant i))
  have h := sum_relative_width_ge_one ![A, B, C] f lo hi hpos ordered (fun x hx => by
    apply Set.mem_iUnion.mp (covers ?_)
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] using hx)
  simpa [diam_eq_vertices, relativeWidthSum, vertexSpread] using h

end TriangleProof
