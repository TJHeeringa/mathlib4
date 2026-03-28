/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Analysis.Matrix.Order

/-!
# Schur Product Theorem

The **Schur product theorem** states that the Hadamard (entrywise) product of two
positive semidefinite Hermitian matrices is positive semidefinite (and positive
definite if both inputs are). The proof uses
`Matrix.star_dotProduct_hadamard_mulVec_eq_kronecker` to reduce to the Kronecker product.

## Main declarations

* `Matrix.IsHermitian.hadamard`: the Hadamard product of Hermitian matrices is Hermitian.
* `Matrix.PosSemidef.hadamard`: the Hadamard product of positive semidefinite matrices is
  positive semidefinite.
* `Matrix.PosDef.hadamard`: the Hadamard product of positive definite matrices is
  positive definite.

The supporting Hermitian results (`conjTranspose_hadamard`, `IsHermitian.hadamard`) are
in `Mathlib.LinearAlgebra.Matrix.Hadamard`.

## References

* [I. Schur, *Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich vielen
  Veränderlichen*][schur1911]
-/

@[expose] public section

open scoped Matrix Kronecker ComplexOrder

namespace Matrix

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜]

/-- The Hadamard product of Hermitian matrices is Hermitian. -/
theorem IsHermitian.hadamard {α : Type*} [CommMonoid α] [StarMul α] {A B : Matrix ι ι α}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊙ B).IsHermitian := by
  rw [IsHermitian, conjTranspose_hadamard, hB.eq, hA.eq, hadamard_comm]

private lemma vec_diagonal_ne_zero [DecidableEq ι] {x : ι → 𝕜} (hx : x ≠ 0) :
    vec (diagonal x) ≠ 0 := by
  rwa [ne_eq, vec_eq_zero_iff, diagonal_eq_zero]

/-- **Schur product theorem** (positive semidefinite version): the Hadamard (entrywise) product
of positive semidefinite matrices is positive semidefinite. -/
theorem PosSemidef.hadamard [Finite ι] {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊙ B).PosSemidef := by
  classical
  have := Fintype.ofFinite ι
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  exact ⟨hA.isHermitian.hadamard hB.isHermitian, fun x => by
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    exact (hA.kronecker hB).dotProduct_mulVec_nonneg _⟩

/-- **Schur product theorem**: the Hadamard (entrywise) product of positive definite
matrices is positive definite. -/
theorem PosDef.hadamard [Finite ι] {A B : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) : (A ⊙ B).PosDef := by
  classical
  have := Fintype.ofFinite ι
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  exact ⟨hA.isHermitian.hadamard hB.isHermitian, fun x hx => by
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    exact (PosDef.kronecker hA hB).dotProduct_mulVec_pos (vec_diagonal_ne_zero hx)⟩

end Matrix
