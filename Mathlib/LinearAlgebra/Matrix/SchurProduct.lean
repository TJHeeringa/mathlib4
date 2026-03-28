/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Hadamard product and Kronecker product identity

The Hadamard (entrywise) product quadratic form can be expressed in terms of
the Kronecker product via diagonal embeddings.

## Main declarations

* `Matrix.star_dotProduct_hadamard_mulVec_eq_kronecker`: the identity
  `star x ⬝ᵥ (A ⊙ B) *ᵥ x' = star (vec (diagonal x)) ⬝ᵥ (A ⊗ₖ B) *ᵥ vec (diagonal x')`.
-/

@[expose] public section

open scoped Matrix Kronecker

namespace Matrix

variable {m n : Type*}

/-- The Hadamard quadratic form equals the Kronecker quadratic form on diagonal embeddings.
This identity relates the entrywise product to the Kronecker product via
`star x ⬝ᵥ (A ⊙ B) *ᵥ x' = star (vec (diagonal x)) ⬝ᵥ (A ⊗ₖ B) *ᵥ vec (diagonal x')`. -/
theorem star_dotProduct_hadamard_mulVec_eq_kronecker
    {R : Type*} [NonUnitalSemiring R] [StarRing R]
    [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
    {A B : Matrix m n R} (x : m → R) (x' : n → R) :
    star x ⬝ᵥ (A ⊙ B).mulVec x' =
      star (vec (diagonal x)) ⬝ᵥ (A ⊗ₖ B).mulVec (vec (diagonal x')) := by
  let y := vec (diagonal x)
  let y' := vec (diagonal x')
  symm
  calc
    star y ⬝ᵥ (A ⊗ₖ B).mulVec y'
        = ∑ p, star (y p) * ((A ⊗ₖ B).mulVec y') p := by
          simp only [dotProduct, Pi.star_apply]
    _ = ∑ i, ∑ j, star (y (i, j)) * ((A ⊗ₖ B).mulVec y') (i, j) :=
          Fintype.sum_prod_type _
    _ = ∑ i, ∑ j, star (y (i, j)) * (∑ k, ∑ l, A i k * B j l * y' (k, l)) := by
          congr! 3 with i _ j _
          calc
            ((A ⊗ₖ B).mulVec y') (i, j)
                = ∑ q, ((A ⊗ₖ B) (i, j) q) * y' q := by
                    simp only [Matrix.mulVec, dotProduct]
            _ = ∑ q, A i q.1 * B j q.2 * y' q := by rfl
            _ = ∑ k, ∑ l, A i k * B j l * y' (k, l) := by
                    simpa using Fintype.sum_prod_type
                      (fun q => A i q.1 * B j q.2 * y' q)
    _ = ∑ i, ∑ k, star (x i) * (A i k * B i k * x' k) := by
          simp [y, y', diagonal, flip, Finset.mul_sum, eq_comm,
            apply_ite star, star_zero]
    _ = star x ⬝ᵥ (A ⊙ B).mulVec x' := by
          simp only [dotProduct, Pi.star_apply, Matrix.mulVec, Matrix.hadamard,
            Matrix.of_apply, Finset.mul_sum]

end Matrix
