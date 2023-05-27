import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import linear_algebra.charpoly.basic
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.charpoly.to_matrix
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.matrix.to_linear_equiv

variables {n: Type*}[fintype n][decidable_eq n] --[nonempty n]
variables {R: Type*}[field R][is_alg_closed R]

open matrix polynomial
open linear_map module.End  
open_locale matrix big_operators

noncomputable def eigs (A: matrix n n R): multiset R := 
  polynomial.roots (matrix.charpoly A)

lemma det_eq_prod_eigs (A: matrix n n R): A.det = (eigs A).prod :=
begin
  rw eigs,
  by_cases hn: nonempty n, {
    rw det_eq_sign_charpoly_coeff,
    have hdeg := charpoly_nat_degree_eq_dim A,
    rw ← hdeg,
    rw polynomial.prod_roots_eq_coeff_zero_of_monic_of_split,
    rw ← mul_assoc, rw ← pow_two,
    rw ← pow_mul, 
    by_cases h2: ring_char R ≠ 2, {
      have hstupid: -1 ≠ (1:R), 
        {exact ring.neg_one_ne_one_of_char_ne_two h2,},
      have hs2 : even(A.charpoly.nat_degree*2),
        {simp only [even.mul_left, even_two],},
        rw (neg_one_pow_eq_one_iff_even hstupid).2 hs2, rw one_mul,
    },{
      rw [ne.def, not_not] at h2, 
      rw neg_one_eq_one_iff.2 h2, rw one_pow, rw one_mul,
    },
    apply matrix.charpoly_monic,
    exact is_alg_closed.splits A.charpoly,
  }, {
    rw not_nonempty_iff at hn,
    rw matrix.charpoly, 
    repeat {rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 hn)},
    rw polynomial.roots_one,
    simp only [multiset.empty_eq_zero, multiset.prod_zero],
  }
end

lemma trace_eq_sum_eigs (A: matrix n n R) : A.trace = (eigs A).sum :=
begin
  rw eigs,
  by_cases hn: (nonempty n), {  
    haveI hn1 := hn,
    apply_fun (has_neg.neg),
    rw ← polynomial.sum_roots_eq_next_coeff_of_monic_of_split ,
    rw trace_eq_neg_charpoly_coeff, rw next_coeff,
    rw neg_neg, rw charpoly_nat_degree_eq_dim, 
    have fn: 0 < fintype.card n, by apply (fintype.card_pos),    
    have fne := ne_of_lt fn, 
    symmetry' at fne, rw ne.def at fne,
    split_ifs, refl,
    apply matrix.charpoly_monic,
    exact is_alg_closed.splits A.charpoly,
    rintros a x hax, rwa neg_inj at hax,
  }, {
    rw not_nonempty_iff at hn,
    rw matrix.trace, 
    rw fintype.sum_empty _, rotate, exact hn,
    rw matrix.charpoly, 
    rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 hn),
    rw polynomial.roots_one,
    simp only [multiset.empty_eq_zero, multiset.sum_zero],
  },
end

lemma root_charpoly_of_has_eigenvalue (A: matrix n n R)(μ: R):
  has_eigenvalue (matrix.to_lin' A) μ → A.charpoly.is_root μ:=
begin
  intro heig,
  have va := has_eigenvalue.exists_has_eigenvector heig, 
  have xa : (∃ (v : n → R) (H : v ≠ 0), (μ • 1 - A).mul_vec v = 0), {
    cases va with v hv, use v, cases hv with hv hnz, split, exact hnz,
    rw mem_eigenspace_iff at hv, 
    rw to_lin'_apply at hv, 
    symmetry' at hv,
    rw ← sub_eq_zero at hv, 
    rw sub_mul_vec, rw smul_mul_vec_assoc, rw one_mul_vec, exact hv,
  },
  have ya := matrix.exists_mul_vec_eq_zero_iff.1 xa,

  rw matrix.charpoly, 
  rw is_root, 
  rw eval_det,
  rw mat_poly_equiv_charmatrix,
  rw eval_sub, rw eval_C, rw eval_X, rw coe_scalar,

  rw ← ya,
end

lemma has_eigenvalue_of_root_charpoly (A: matrix n n R)(μ: R):
   A.charpoly.is_root μ → has_eigenvalue (matrix.to_lin' A) μ :=
begin

  rw matrix.charpoly, 
  rw is_root,
  rw eval_det,
  rw mat_poly_equiv_charmatrix,
  rw eval_sub, rw eval_C, rw eval_X, rw coe_scalar, dsimp,

  intro h,
  have h := matrix.exists_mul_vec_eq_zero_iff.2 h, 
  rcases h with ⟨v, hv_nz, hv⟩,
  rw sub_mul_vec at hv, rw smul_mul_vec_assoc at hv, rw one_mul_vec at hv,
  rw sub_eq_zero at hv,  symmetry' at hv,
  rw [has_eigenvalue, submodule.ne_bot_iff], 
   use v, rw mem_eigenspace_iff, 
  rw to_lin'_apply, split, assumption',
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

  intro h, rw root_charpoly_iff_has_eigenvalue, 
  apply has_eigenvalue_iff_is_root.2 h,
  
  rw root_charpoly_iff_has_eigenvalue, intro h,
  apply has_eigenvalue_iff_is_root.1 h,
end

lemma eig_if_eigenvalue (A: matrix n n R)(μ: R) :
  μ ∈ eigs A → has_eigenvalue (matrix.to_lin' A) μ := 
begin
  rw eigs, rw mem_roots',
  intro h, cases h with hne hcp,
  exact has_eigenvalue_of_root_charpoly _ _ hcp,
end

lemma eigenvalue_if_eig [nonempty n](A: matrix n n R)(μ: R) :
  has_eigenvalue (matrix.to_lin' A) μ → μ ∈ eigs A  := 
begin
  rw eigs, rw mem_roots,
  intro h,
  exact root_charpoly_of_has_eigenvalue _ _ h,
  have p_nz : matrix.charpoly A ≠ 0, { 
    by_contra, replace h := congr_arg nat_degree h, simp only [nat_degree_zero] at h, 
    have p_deg := matrix.charpoly_nat_degree_eq_dim A, rw p_deg at h,
    have hn: fintype.card n ≠ 0, {exact fintype.card_ne_zero,},
    exact hn h,
  }, exact p_nz,
end

