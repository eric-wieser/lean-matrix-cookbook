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

noncomputable def eigs (A : matrix n n R) : multiset R := A.charpoly.roots

lemma det_eq_prod_eigs (A : matrix n n R): A.det = (eigs A).prod :=
det_eq_prod_roots_charpoly A

lemma trace_eq_sum_eigs (A : matrix n n R) : A.trace = (eigs A).sum :=
trace_eq_sum_roots_charpoly A

lemma root_charpoly_of_has_eigenvalue (A : matrix n n R) (μ : R)
  (heig : has_eigenvalue (matrix.to_lin' A) μ) :
  A.charpoly.is_root μ:=
begin
  have va := has_eigenvalue.exists_has_eigenvector heig,
  have xa : (∃ (v : n → R) (H : v ≠ 0), (μ • 1 - A).mul_vec v = 0),
  { cases va with v hv,
    use v,
    rw [has_eigenvector, mem_eigenspace_iff,to_lin'_apply, and_comm, eq_comm] at hv,
    rwa [sub_mul_vec, smul_mul_vec_assoc, one_mul_vec, sub_eq_zero], },
  rw [matrix.charpoly, is_root, eval_det, mat_poly_equiv_charmatrix,
    eval_sub, eval_C, eval_X, coe_scalar,← (matrix.exists_mul_vec_eq_zero_iff.1 xa)],
end

lemma has_eigenvalue_of_root_charpoly (A : matrix n n R) (μ : R) (h : A.charpoly.is_root μ) :
  has_eigenvalue (matrix.to_lin' A) μ :=
begin
  rw [matrix.charpoly, is_root, eval_det, mat_poly_equiv_charmatrix, eval_sub, eval_C, eval_X,
    coe_scalar] at h,
  dsimp only at h,
  obtain ⟨v, hv_nz, hv⟩ := matrix.exists_mul_vec_eq_zero_iff.2 h,
  rw [sub_mul_vec, smul_mul_vec_assoc, one_mul_vec, sub_eq_zero, eq_comm] at hv,
  rw [has_eigenvalue, submodule.ne_bot_iff],
  use v,
  rw [mem_eigenspace_iff, to_lin'_apply],
  exact ⟨hv, hv_nz⟩,
end

lemma root_charpoly_iff_has_eigenvalue (A : matrix n n R) (μ : R) :
  A.charpoly.is_root μ ↔ has_eigenvalue (matrix.to_lin' A) μ :=
⟨has_eigenvalue_of_root_charpoly _ _, root_charpoly_of_has_eigenvalue _ _⟩

lemma root_charpoly_iff_root_minpoly (A : matrix n n R) (μ : R) :
  (minpoly R (matrix.to_lin' A)).is_root μ ↔ A.charpoly.is_root μ :=
by rw [root_charpoly_iff_has_eigenvalue, has_eigenvalue_iff_is_root]

lemma has_eigenvalue_of_mem_eigs (A : matrix n n R) (μ : R) (h : μ ∈ eigs A) :
  has_eigenvalue (matrix.to_lin' A) μ :=
begin
  rw [eigs, mem_roots'] at h,
  cases h with hne hcp,
  exact has_eigenvalue_of_root_charpoly _ _ hcp,
end

lemma mem_eigs_of_has_eigenvalue [nonempty n](A : matrix n n R) (μ : R)
  (h : has_eigenvalue (matrix.to_lin' A) μ) :
  μ ∈ eigs A :=
begin
  rw [eigs, mem_roots],
  exact root_charpoly_of_has_eigenvalue _ _ h,
  have p_nz : matrix.charpoly A ≠ 0,
  { apply ne_of_apply_ne nat_degree,
    rw [charpoly_nat_degree_eq_dim, nat_degree_zero],
    exact fintype.card_ne_zero },
  exact p_nz,
end

lemma mem_eigs_iff_has_eigenvalue [nonempty n] {A : matrix n n R} {μ : R} :
  μ ∈ eigs A ↔ has_eigenvalue (matrix.to_lin' A) μ :=
⟨has_eigenvalue_of_mem_eigs _ _, mem_eigs_of_has_eigenvalue _ _⟩


