import Mathbin.Data.Matrix.Notation
import Mathbin.Data.Real.Nnreal
import Mathbin.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.SchurComplement
import Mathbin.LinearAlgebra.Matrix.Trace
import Mathbin.RingTheory.PowerSeries.Basic
import Mathbin.Tactic.NormFin
import Mathbin.Topology.MetricSpace.Basic
import Project.MatrixCookbook.Lib.TraceDetFinFour

#align_import matrix_cookbook.«1_basic»

/-! # Basics -/


variable {ι : Type _} {R : Type _} {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

namespace MatrixCookbook

open scoped Matrix BigOperators Filter Topology

open Matrix

-- anyone looking at the cookbook likely only cares about fields anyway!
variable [Field R]

theorem eq_1 {A : Matrix m m R} {B : Matrix m m R} : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  Matrix.mul_inv_rev _ _

theorem eq_2 {l : List (Matrix m m R)} : l.Prod⁻¹ = (l.reverse.map Inv.inv).Prod :=
  Matrix.list_prod_inv_reverse _

theorem eq_3 {A : Matrix m m R} : Aᵀ⁻¹ = A⁻¹ᵀ :=
  (transpose_nonsing_inv _).symm

theorem eq_4 {A B : Matrix m n R} : (A + B)ᵀ = Aᵀ + Bᵀ :=
  transpose_add _ _

theorem eq_5 {A : Matrix m n R} {B : Matrix n p R} : (A ⬝ B)ᵀ = Bᵀ ⬝ Aᵀ :=
  transpose_mul _ _

theorem eq_6 {l : List (Matrix m m R)} : l.Prodᵀ = (l.map transpose).reverse.Prod :=
  Matrix.transpose_list_prod _

theorem eq_7 [StarRing R] {A : Matrix m m R} : Aᴴ⁻¹ = A⁻¹ᴴ :=
  (conjTranspose_nonsing_inv _).symm

theorem eq_8 [StarRing R] {A B : Matrix m n R} : (A + B)ᴴ = Aᴴ + Bᴴ :=
  conjTranspose_add _ _

theorem eq_9 [StarRing R] {A : Matrix m n R} {B : Matrix n p R} : (A ⬝ B)ᴴ = Bᴴ ⬝ Aᴴ :=
  conjTranspose_mul _ _

theorem eq_10 [StarRing R] {l : List (Matrix m m R)} :
    l.Prodᴴ = (l.map conjTranspose).reverse.Prod :=
  Matrix.conjTranspose_list_prod _

/-! ### Trace -/


section

theorem eq_11 {A : Matrix m m R} : trace A = ∑ i, A i i :=
  rfl

theorem eq_12 {A : Matrix m m R} [IsAlgClosed R] : trace A = A.charpoly.roots.Sum :=
  trace_eq_sum_roots_charpoly _

theorem eq_13 {A : Matrix m m R} : trace A = trace Aᵀ :=
  (Matrix.trace_transpose _).symm

theorem eq_14 {A : Matrix m n R} {B : Matrix n m R} : trace (A ⬝ B) = trace (B ⬝ A) :=
  Matrix.trace_mul_comm _ _

theorem eq_15 {A B : Matrix m m R} : trace (A + B) = trace A + trace B :=
  trace_add _ _

theorem eq_16 {A : Matrix m n R} {B : Matrix n p R} {C : Matrix p m R} :
    trace (A ⬝ B ⬝ C) = trace (B ⬝ C ⬝ A) :=
  (Matrix.trace_mul_cycle B C A).symm

theorem eq_17 {a : m → R} : dotProduct a a = trace (col a ⬝ row a) :=
  (Matrix.trace_col_mul_row _ _).symm

end

/-! ### Determinant -/


-- `matrix.is_hermitian.det_eq_prod_eigenvalues` is close, but needs `A` to be hermitian which is too strong
theorem eq_18 {A : Matrix m m R} [IsAlgClosed R] : det A = A.charpoly.roots.Prod :=
  det_eq_prod_roots_charpoly _

theorem eq_19 (c : R) {A : Matrix m m R} : det (c • A) = c ^ Fintype.card m * det A :=
  det_smul _ _

theorem eq_20 {A : Matrix m m R} : det Aᵀ = det A :=
  det_transpose _

theorem eq_21 {A B : Matrix m m R} : det (A * B) = det A * det B :=
  det_mul _ _

theorem eq_22 {A : Matrix m m R} : det A⁻¹ = (det A)⁻¹ :=
  (det_nonsing_inv _).trans (Ring.inverse_eq_inv _)

theorem eq_23 {A : Matrix m m R} (k : ℕ) : det (A ^ k) = det A ^ k :=
  det_pow _ _

theorem eq_24 {u v : m → R} : det (1 + col u ⬝ row v) = 1 + dotProduct u v := by
  rw [det_one_add_col_mul_row u v, dot_product_comm]

theorem eq_25 {A : Matrix (Fin 2) (Fin 2) R} : det (1 + A) = 1 + det A + trace A := by
  simp [det_fin_two, trace_fin_two]; ring

theorem eq_26 {A : Matrix (Fin 3) (Fin 3) R} [Invertible (2 : R)] :
    det (1 + A) = 1 + det A + trace A + ⅟ 2 * trace A ^ 2 - ⅟ 2 * trace (A ^ 2) :=
  by
  apply mul_left_cancel₀ (isUnit_of_invertible (2 : R)).NeZero
  simp only [det_fin_three, trace_fin_three, pow_two, Matrix.mul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.one_apply]
  dsimp
  simp only [mul_add, mul_sub, mul_invOf_self_assoc]
  simp_rw [Matrix.one_apply]
  simp
  norm_num
  ring

-- ring,
theorem eq_27 {A : Matrix (Fin 4) (Fin 4) R} [CharZero R] :
    det (1 + A) =
      1 + det A + trace A + 1 / 2 * (trace A ^ 2 - trace (A ^ 2)) +
        1 / 6 * (trace A ^ 3 - 3 * trace A * trace (A ^ 2) + 2 * trace (A ^ 3)) :=
  by
  -- TODO: it might be cleaner to prove this via the
  -- [Girard-Waring formula](https://math.stackexchange.com/a/2779104/1896), which wouldn't produce
  -- such a frighteniningly long goal state!
  field_simp
  rw [det_one_add_fin_four, det_fin_four, trace_pow_three_fin_four, trace_pow_two_fin_four,
    sq_trace_fin_four, trace_fin_four]
  ring

/-! Note: it is likely that eq (28) is just wrong in the source material! -/


-- TODO: is this statement correct?
theorem eq_28 {A : Matrix n n ℝ} :
    (fun ε : NNReal => det (1 + ε • A)) =ᶠ[Filter.atBot] fun ε =>
      1 + det A + ε * trace A + 1 / 2 * ε ^ 2 * trace A ^ 2 - 1 / 2 * ε ^ 2 * trace (A ^ 2) :=
  sorry

-- TODO: or is this statement correct?
theorem eq_28' {A : Matrix n n R} :
    let ε : PowerSeries R := PowerSeries.X
    let A : Matrix n n (PowerSeries R) := A.map (PowerSeries.C _)
    (det (1 + ε • A)).Trunc 2 =
      (1 + det A + ε • trace A + (1 / 2 : R) • ε ^ 2 * trace A ^ 2 -
            (1 / 2 : R) • ε ^ 2 * trace (A ^ 2)).Trunc
        2 :=
  sorry

/-! ### The special case 2×2-/


section

theorem eq_29 {A : Matrix (Fin 2) (Fin 2) R} : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 :=
  det_fin_two _

theorem eq_30 {A : Matrix (Fin 2) (Fin 2) R} : trace A = A 0 0 + A 1 1 :=
  trace_fin_two _

/-! Note: there are some non-numbered eigenvalue things here -/


theorem eq_31 {A : Matrix (Fin 2) (Fin 2) R} : A⁻¹ = (det A)⁻¹ • !![A 1 1, -A 0 1; -A 1 0, A 0 0] :=
  by rw [inv_def, adjugate_fin_two, Ring.inverse_eq_inv]

end

end MatrixCookbook

