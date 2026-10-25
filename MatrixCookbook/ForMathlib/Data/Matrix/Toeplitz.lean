import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.ZMod.Defs

namespace Matrix

variable {n : ℕ}


def toeplitz {n : ℕ} (e : Set.Ioo (-n : ℤ) n → R) :
    Matrix (Fin n) (Fin n) R :=
  of fun i j => e ⟨j.val - i.val, by omega, by omega⟩

abbrev toeplitzSymm {n : ℕ} (e : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  toeplitz fun i => e ⟨i.val.natAbs, by obtain ⟨i, hi, hi'⟩ := i; simp; omega⟩

-- TODO: this is the transpose of `Matrix.circulant`
abbrev toeplitzCirc {n : ℕ} (e : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  toeplitz fun i =>
    have : NeZero n := ⟨by obtain ⟨i, hi, hi'⟩ := i; omega⟩
    e (open scoped Fin.CommRing in Int.cast i)

abbrev toeplitzUpper [Zero R] {n : ℕ} (e : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  toeplitz fun i =>
    if h : i.val ≥ 0 then
      e ⟨i.val.toNat, by obtain ⟨i, hi, hi'⟩ := i; simp; omega⟩
    else 0

abbrev toeplitzLower [Zero R] {n : ℕ} (e : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  toeplitz fun i =>
    if h : i.val ≤ 0 then
      e ⟨(-i.val).toNat, by obtain ⟨i, hi, hi'⟩ := i; simp; omega⟩
    else 0

end Matrix
