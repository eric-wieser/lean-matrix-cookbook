/-
Copyright (c) 2023 Mohanad Ahmed, Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed, Eric Wieser
-/
import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import linear_algebra.charpoly.to_matrix
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.matrix.to_linear_equiv
import linear_algebra.matrix.charpoly.eigs

/-! # Lemmas about Eigenvalues with "correct" multiplicities -/

/- TODO1: Add minpoly invariance under algebraic maps using Erics lemmas and use
that to show that charpoly roots are minpoly roots and minpoly linmap roots -/

/- TODO2: Link these eigenvalues to the "disconnected eigenvalues in 
`is_hermitian.eigenvalues` "-/

variables {n: Type*}[fintype n][decidable_eq n]
variables {R: Type*}[field R][is_alg_closed R]

open matrix polynomial
open linear_map module.End  
open_locale matrix big_operators

noncomputable def eigs (A: matrix n n R): multiset R := 
  polynomial.roots (matrix.charpoly A)

lemma det_eq_prod_eigs (A: matrix n n R): A.det = (eigs A).prod :=
by apply det_eq_prod_roots_charpoly

lemma trace_eq_sum_eigs (A: matrix n n R) : A.trace = (eigs A).sum :=
by apply trace_eq_sum_roots_charpoly


lemma root_charpoly_of_has_eigenvalue (A: matrix n n R)(μ: R):
  has_eigenvalue (matrix.to_lin' A) μ → A.charpoly.is_root μ:=
begin
  intro heig,
  have va := has_eigenvalue.exists_has_eigenvector heig, 
  have xa : (∃ (v : n → R) (H : v ≠ 0), (μ • 1 - A).mul_vec v = 0), 
  { cases va with v hv, 
    use v, 
    rw [has_eigenvector, mem_eigenspace_iff,to_lin'_apply, and_comm, eq_comm] at hv,
    rwa [sub_mul_vec, smul_mul_vec_assoc, one_mul_vec, sub_eq_zero], },
  rw [matrix.charpoly, is_root, eval_det, mat_poly_equiv_charmatrix,
    eval_sub, eval_C, eval_X, coe_scalar,← (matrix.exists_mul_vec_eq_zero_iff.1 xa)],
end

lemma has_eigenvalue_of_root_charpoly (A: matrix n n R)(μ: R):
   A.charpoly.is_root μ → has_eigenvalue (matrix.to_lin' A) μ :=
begin
  rw [matrix.charpoly, is_root, eval_det, mat_poly_equiv_charmatrix,eval_sub], 
  rw [eval_C, eval_X, coe_scalar], 
  dsimp,

  intro h,
  have h := matrix.exists_mul_vec_eq_zero_iff.2 h, 
  rcases h with ⟨v, hv_nz, hv⟩,
  rw [sub_mul_vec, smul_mul_vec_assoc, one_mul_vec, sub_eq_zero, eq_comm] at hv,
  rw [has_eigenvalue, submodule.ne_bot_iff], 
  use v,
  rw [mem_eigenspace_iff, to_lin'_apply],
  split, assumption',
end

lemma root_charpoly_iff_has_eigenvalue (A: matrix n n R)(μ: R) :
   A.charpoly.is_root μ ↔ has_eigenvalue (matrix.to_lin' A) μ := 
begin
  split,
  apply has_eigenvalue_of_root_charpoly,
  apply root_charpoly_of_has_eigenvalue,
end

lemma root_charpoly_iff_root_minpoly (A: matrix n n R)(μ: R) :
  (minpoly R (matrix.to_lin' A)).is_root μ ↔ A.charpoly.is_root μ := 
begin
  split,
  /- Bridge over has_eigenvalue to connect root_chapoly and root minpoly linear map-/
  intro h, 
  rw root_charpoly_iff_has_eigenvalue, 
  apply has_eigenvalue_iff_is_root.2 h,
  
  rw root_charpoly_iff_has_eigenvalue, 
  intro h,
  apply has_eigenvalue_iff_is_root.1 h,
end

lemma eig_if_eigenvalue (A: matrix n n R)(μ: R) :
  μ ∈ eigs A → has_eigenvalue (matrix.to_lin' A) μ := 
begin
  rw eigs, 
  rw mem_roots',
  intro h, 
  cases h with hne hcp,
  exact has_eigenvalue_of_root_charpoly _ _ hcp,
end

lemma eigenvalue_if_eig [nonempty n](A: matrix n n R)(μ: R) :
  has_eigenvalue (matrix.to_lin' A) μ → μ ∈ eigs A  := 
begin
  rw eigs, rw mem_roots,
  intro h,
  exact root_charpoly_of_has_eigenvalue _ _ h,
  have p_nz : matrix.charpoly A ≠ 0, 
  { by_contra, 
    replace h := congr_arg nat_degree h, 
    have p_deg := matrix.charpoly_nat_degree_eq_dim A, 
    have hn: fintype.card n ≠ 0, {exact fintype.card_ne_zero,},
    rw [nat_degree_zero, p_deg] at h, 
    exact hn h, }, 
  exact p_nz,
end

lemma mem_eigs_iff_eigenvalue [nonempty n] (A: matrix n n R)(μ: R):
  μ ∈ eigs A ↔  has_eigenvalue (matrix.to_lin' A) μ := 
begin
  split,
  apply eig_if_eigenvalue,
  apply eigenvalue_if_eig,
end


