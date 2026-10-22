import Mathlib

/-!
# Can Reciprocal RIS Perform as Non-Reciprocal RIS?

Formalization of the results of *Can Reciprocal RIS Perform as Non-Reciprocal RIS?*
(M. Nerini, J. Vidal Alegría, B. Clerckx).

Throughout, `𝒰` is the set of `M × M` unitary matrices (`unitaryGroup (Fin M) ℂ`) and `𝒮 ⊆ 𝒰`
the set of symmetric unitary matrices (`A.IsSymm` means `Aᵀ = A`), i.e. the feasible scattering
matrices of a lossless non-reciprocal and reciprocal RIS, respectively.

* **Lemma 1** (`exists_unitary_mul_eq_iff`): for `X, Y ∈ ℂ^{M×K}`, there is `Θ ∈ 𝒰` with
  `Θ X = Y` if and only if `Xᴴ X = Yᴴ Y`.
* **Lemma 2** (`exists_symmUnitary_mul_eq_iff`): there is `Θ ∈ 𝒮` with `Θ X = Y` if and only if
  `Xᴴ X = Yᴴ Y` and `Xᵀ Y` is symmetric.
* **Definition 1** (`ReciprocalPerformsAsNonReciprocal`): for a metric `f(Θ H_T)`, some optimal
  non-reciprocal RIS is reciprocal.
* **Theorem 1** (`reciprocalPerformsAsNonReciprocal_iff`): this holds if and only if some optimal
  non-reciprocal RIS `Θ⋆` makes `H_Tᵀ Θ⋆ H_T` symmetric.
* **Corollary 1** (`reciprocalPerformsAsNonReciprocal_of_rank_eq_one`): this holds if
  `rank H_T = 1`.
* **Definition 2** (`ReciprocalPerformsAsNonReciprocalWithPrecoding`): for a metric
  `g(F, Θ H_T F)`, some optimal pair of non-reciprocal RIS and precoder `F ∈ 𝓕` has a reciprocal
  RIS.
* **Theorem 2** (`reciprocalPerformsAsNonReciprocalWithPrecoding_iff`): this holds if and only if
  some optimal pair `(Θ⋆, F⋆)` makes `F⋆ᵀ H_Tᵀ Θ⋆ H_T F⋆` symmetric.
* **Corollary 2** (`reciprocalPerformsAsNonReciprocalWithPrecoding_of_single_stream`): this holds
  for single-stream transmission (`K = 1`).

The paper also remarks that, for metrics of the form `f(H_R Θ)`, the same results hold with the
round-trip channel `H_R Θ⋆ H_Rᵀ` from the receiving antennas back to themselves, and that, for
metrics of the whole channel `H_RT + H_R Θ H_T`, it suffices that `H_T` or `H_R` has rank one
(so single-user SISO, SIMO and MISO systems never benefit from non-reciprocal RIS). These are
formalized as `ReciprocalPerformsAsNonReciprocalRx`, `reciprocalPerformsAsNonReciprocalRx_iff`,
`reciprocalPerformsAsNonReciprocalRx_of_rank_eq_one` and
`reciprocalPerformsAsNonReciprocal_channel_of_rank_eq_one`.

## Proof of Lemma 1

(⇒) `Yᴴ Y = Xᴴ Θᴴ Θ X = Xᴴ X`.

(⇐) For every `v`, `‖X v‖² = vᴴ Xᴴ X v = vᴴ Yᴴ Y v = ‖Y v‖²`. Hence `ker X ⊆ ker Y`, so
`X v ↦ Y v` is a well-defined linear isometry from `range X` into `ℂ^M`. Any linear isometry
from a subspace of a finite-dimensional inner product space extends to a linear isometry of the
whole space (`LinearIsometry.extend`), which is unitary; its matrix is the required `Θ`. (This
differs from the SVD-based proof in the paper.)

## Proof of Lemma 2

(⇒) `Xᵀ Y = Xᵀ Θ X`, which is symmetric when `Θ` is.

(⇐) The two conditions say exactly that `[X, Ȳ]` and `[Y, X̄]` have the same Gram matrix, so
Lemma 1 gives a unitary `Θ` with `Θ X = Y` and `Θ Ȳ = X̄`. Let `W = range X + range Ȳ`, let the
columns of `E` be an orthonormal basis of `Wᗮ`, and let `P = I - E Eᴴ`. Then `Θ' = Θ P + Ē Eᴴ`
is unitary, symmetric and satisfies `Θ' X = Y`. (This also differs from the SVD-based proof in
the paper.)

## Proofs of Theorems 1-2 and Corollaries 1-2

Theorem 1 follows from Lemma 2 with `X = H_T` and `Y = Θ⋆ H_T`. Corollary 1 follows because
`H_Tᵀ Θ H_T = (aᵀ Θ a) b bᵀ` is symmetric when `H_T = a bᵀ`. Theorem 2 follows from Lemma 2 with
`X = H_T F⋆` and `Y = Θ⋆ H_T F⋆`. Corollary 2 follows because a `1 × 1` matrix is symmetric.
The receive-side version of Theorem 1 follows from Lemma 2 with `X = H_Rᵀ` and `Y = Θ⋆ᵀ H_Rᵀ`.
-/

open Matrix

namespace ReciprocalRIS

/-! ### Lemma 1 -/

/-- `‖X v‖² = vᴴ (Xᴴ X) v`, as an inner product identity. -/
lemma inner_toEuclideanLin_self {M K : ℕ}
    (X : Matrix (Fin M) (Fin K) ℂ) (v : EuclideanSpace ℂ (Fin K)) :
    inner ℂ (toEuclideanLin X v) (toEuclideanLin X v) =
      inner ℂ v (toEuclideanLin (Xᴴ * X) v) := by
  rw [toLpLin_mul_same, LinearMap.comp_apply, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

/-- If `Xᴴ X = Yᴴ Y` then `‖X v‖ = ‖Y v‖` for every `v`. -/
lemma norm_eq_of_gram_eq {M K : ℕ} {X Y : Matrix (Fin M) (Fin K) ℂ}
    (h : Xᴴ * X = Yᴴ * Y) (v : EuclideanSpace ℂ (Fin K)) :
    ‖toEuclideanLin X v‖ = ‖toEuclideanLin Y v‖ := by
  have h2 : ‖toEuclideanLin X v‖ ^ 2 = ‖toEuclideanLin Y v‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ,
      inner_toEuclideanLin_self, inner_toEuclideanLin_self, h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- **Lemma 1.** For `X, Y ∈ ℂ^{M×K}`, there is a unitary `Θ` with `Θ X = Y` if and only
if `Xᴴ X = Yᴴ Y`. -/
theorem exists_unitary_mul_eq_iff {M K : ℕ} (X Y : Matrix (Fin M) (Fin K) ℂ) :
    (∃ Θ ∈ unitaryGroup (Fin M) ℂ, Θ * X = Y) ↔ Xᴴ * X = Yᴴ * Y := by
  constructor
  · rintro ⟨Θ, hΘ, rfl⟩
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Θᴴ, ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').1 hΘ, Matrix.one_mul]
  · intro h
    set f := toEuclideanLin X
    set g := toEuclideanLin Y
    -- `ker f ≤ ker g`
    have hker : LinearMap.ker f ≤ LinearMap.ker g := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [← norm_eq_zero, ← norm_eq_of_gram_eq h, hv, norm_zero]
    -- the map `X v ↦ Y v` on `range X`
    let L₀ : LinearMap.range f →ₗ[ℂ] EuclideanSpace ℂ (Fin M) :=
      (LinearMap.ker f).liftQ g hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
    have hL₀ : ∀ v, L₀ ⟨f v, LinearMap.mem_range_self f v⟩ = g v := fun v ↦ by
      simp [L₀, LinearMap.quotKerEquivRange_symm_apply_image]
    let L : LinearMap.range f →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin M) :=
      { toLinearMap := L₀
        norm_map' := by
          rintro ⟨_, v, rfl⟩
          rw [hL₀, ← norm_eq_of_gram_eq h]
          rfl }
    -- extend to an isometry `T` of the whole space; its matrix is `Θ`
    let T := L.extend.toLinearIsometryEquiv rfl
    refine ⟨toEuclideanLin.symm T.toLinearEquiv.toLinearMap,
      T.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun _ ℂ) (EuclideanSpace.basisFun _ ℂ), ?_⟩
    refine toEuclideanLin.injective (LinearMap.ext fun v ↦ ?_)
    rw [toLpLin_mul_same, LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
    change L.extend (f v) = g v
    exact (L.extend_apply ⟨f v, LinearMap.mem_range_self f v⟩).trans (hL₀ v)

/-! ### Entrywise complex conjugate -/

/-- Entrywise complex conjugate `Ā` of a matrix. -/
def cj {M K : ℕ} (A : Matrix (Fin M) (Fin K) ℂ) : Matrix (Fin M) (Fin K) ℂ :=
  A.map (starRingEnd ℂ)

section cj

variable {M K N : ℕ}

lemma cj_mul (A : Matrix (Fin M) (Fin K) ℂ) (B : Matrix (Fin K) (Fin N) ℂ) :
    cj (A * B) = cj A * cj B :=
  Matrix.map_mul

@[simp] lemma cj_cj (A : Matrix (Fin M) (Fin K) ℂ) : cj (cj A) = A := by ext; simp [cj]
@[simp] lemma conjTranspose_cj (A : Matrix (Fin M) (Fin K) ℂ) : (cj A)ᴴ = Aᵀ := by
  ext; simp [cj]
@[simp] lemma transpose_cj (A : Matrix (Fin M) (Fin K) ℂ) : (cj A)ᵀ = Aᴴ := by ext; simp [cj]
@[simp] lemma cj_conjTranspose (A : Matrix (Fin M) (Fin K) ℂ) : cj Aᴴ = Aᵀ := by
  ext; simp [cj]
@[simp] lemma cj_transpose (A : Matrix (Fin M) (Fin K) ℂ) : cj Aᵀ = Aᴴ := by ext; simp [cj]
@[simp] lemma cj_zero : cj (0 : Matrix (Fin M) (Fin K) ℂ) = 0 := by ext; simp [cj]
@[simp] lemma cj_one : cj (1 : Matrix (Fin M) (Fin M) ℂ) = 1 := by ext; simp [cj, Matrix.one_apply]
@[simp] lemma conjTranspose_transpose_eq_cj (A : Matrix (Fin M) (Fin K) ℂ) : Aᵀᴴ = cj A := by
  ext; simp [cj]
@[simp] lemma transpose_conjTranspose_eq_cj (A : Matrix (Fin M) (Fin K) ℂ) : Aᴴᵀ = cj A := by
  ext; simp [cj]

end cj

/-! ### Lemma 2 -/

/-- **Lemma 2.** For `X, Y ∈ ℂ^{M×K}`, there is a symmetric unitary `Θ`
(`Θᴴ Θ = I`, `Θᵀ = Θ`) with `Θ X = Y` if and only if `Xᴴ X = Yᴴ Y` and `Xᵀ Y` is symmetric. -/
theorem exists_symmUnitary_mul_eq_iff {M K : ℕ} (X Y : Matrix (Fin M) (Fin K) ℂ) :
    (∃ Θ ∈ unitaryGroup (Fin M) ℂ, Θ.IsSymm ∧ Θ * X = Y) ↔
      Xᴴ * X = Yᴴ * Y ∧ (Xᵀ * Y).IsSymm := by
  constructor
  · rintro ⟨Θ, hΘu, hΘs, rfl⟩
    refine ⟨(exists_unitary_mul_eq_iff X (Θ * X)).1 ⟨Θ, hΘu, rfl⟩, ?_⟩
    simp only [IsSymm, transpose_mul, transpose_transpose, hΘs.eq, Matrix.mul_assoc]
  · rintro ⟨hu, hs⟩
    -- Step 1: a unitary `Θ` with `Θ X = Y` and `Θ Ȳ = X̄`, from Lemma 1 applied to
    -- `[X, Ȳ]` and `[Y, X̄]` (columns reindexed by `Fin (K + K)`).
    obtain ⟨Θ, hΘu, hΘX, hΘY⟩ : ∃ Θ ∈ unitaryGroup (Fin M) ℂ, Θ * X = Y ∧ Θ * cj Y = cj X := by
      let e := (finSumFinEquiv (m := K) (n := K)).symm
      have h3 : Yᵀ * X = Xᵀ * Y := by rw [← hs.eq, transpose_mul, transpose_transpose]
      have h1 : Xᴴ * cj Y = Yᴴ * cj X := by
        rw [← cj_transpose X, ← cj_transpose Y, ← cj_mul, ← cj_mul, h3]
      have h2 : Yᵀ * cj Y = Xᵀ * cj X := by
        rw [← cj_conjTranspose X, ← cj_conjTranspose Y, ← cj_mul, ← cj_mul, hu]
      have hgram : (fromCols X (cj Y))ᴴ * fromCols X (cj Y) =
          (fromCols Y (cj X))ᴴ * fromCols Y (cj X) := by
        simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
          conjTranspose_cj]
        rw [hu, h1, h2, h3]
      obtain ⟨Θ, hΘu, hΘ⟩ := (exists_unitary_mul_eq_iff ((fromCols X (cj Y)).submatrix id e)
        ((fromCols Y (cj X)).submatrix id e)).2 (by
          rw [conjTranspose_submatrix, conjTranspose_submatrix,
            ← submatrix_mul _ _ _ _ _ Function.bijective_id,
            ← submatrix_mul _ _ _ _ _ Function.bijective_id, hgram])
      rw [← submatrix_id_id Θ, ← submatrix_mul _ _ _ _ _ Function.bijective_id] at hΘ
      have := congrArg (fun A ↦ A.submatrix id e.symm) hΘ
      simp only [submatrix_submatrix, Function.comp_id, Equiv.self_comp_symm, submatrix_id_id,
        mul_fromCols, fromCols_ext_iff] at this
      exact ⟨Θ, hΘu, this⟩
    -- Step 2: a matrix `E` whose columns are an orthonormal basis of `Wᗮ`, `W = range X + range Ȳ`
    obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ (EuclideanSpace ℂ (Fin M)),
        W = LinearMap.range (toEuclideanLin X) ⊔ LinearMap.range (toEuclideanLin (cj Y)) :=
      ⟨_, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p, Module.finrank ℂ Wᗮ = p := ⟨_, rfl⟩
    let b : OrthonormalBasis (Fin p) ℂ Wᗮ := (stdOrthonormalBasis ℂ Wᗮ).reindex (finCongr hp)
    let J := Wᗮ.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    obtain ⟨E, hJ⟩ : ∃ E : Matrix (Fin M) (Fin p) ℂ, toEuclideanLin E = J.toLinearMap :=
      ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    have hE1 : Eᴴ * E = 1 := by
      apply toEuclideanLin.injective
      refine LinearMap.ext fun v ↦ ext_inner_left ℂ fun w ↦ ?_
      rw [toLpLin_mul_same, LinearMap.comp_apply, toEuclideanLin_conjTranspose_eq_adjoint, hJ,
        LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap,
        LinearIsometry.inner_map_map, toLpLin_one, LinearMap.id_apply]
    have hEW : ∀ A : Matrix (Fin M) (Fin K) ℂ,
        LinearMap.range (toEuclideanLin A) ≤ W → Eᴴ * A = 0 := by
      intro A hA
      apply toEuclideanLin.injective
      refine LinearMap.ext fun v ↦ ext_inner_left ℂ fun w ↦ ?_
      rw [toLpLin_mul_same, LinearMap.comp_apply, toEuclideanLin_conjTranspose_eq_adjoint, hJ,
        LinearMap.adjoint_inner_right, map_zero, LinearMap.zero_apply, inner_zero_right]
      exact Submodule.inner_left_of_mem_orthogonal (hA (LinearMap.mem_range_self _ v))
        (b.repr.symm w).2
    have hEX : Eᴴ * X = 0 := hEW X (hW ▸ le_sup_left)
    have hEY : Eᴴ * cj Y = 0 := hEW (cj Y) (hW ▸ le_sup_right)
    -- the columns of `X`, `Ȳ` and `E` span `ℂ^M`
    have hspan : ∀ {N : ℕ} (D : Matrix (Fin N) (Fin M) ℂ),
        D * X = 0 → D * cj Y = 0 → D * E = 0 → D = 0 := by
      intro N D h1 h2 h3
      have key : ∀ {L : ℕ} (A : Matrix (Fin M) (Fin L) ℂ) v,
          toEuclideanLin D (toEuclideanLin A v) = toEuclideanLin (D * A) v := by
        intro L A v; rw [toLpLin_mul_same]; rfl
      have hWk : W ≤ LinearMap.ker (toEuclideanLin D) := by
        rw [hW]
        refine sup_le ?_ ?_ <;> rintro _ ⟨v, rfl⟩
        · rw [LinearMap.mem_ker, key, h1, map_zero, LinearMap.zero_apply]
        · rw [LinearMap.mem_ker, key, h2, map_zero, LinearMap.zero_apply]
      have hWp : Wᗮ ≤ LinearMap.ker (toEuclideanLin D) := by
        intro u hu
        rw [LinearMap.mem_ker]
        have hu' : J (b.repr ⟨u, hu⟩) = u := by simp [J]
        calc toEuclideanLin D u = toEuclideanLin D (toEuclideanLin E (b.repr ⟨u, hu⟩)) := by
              rw [hJ, LinearIsometry.coe_toLinearMap, hu']
          _ = 0 := by rw [key, h3, map_zero, LinearMap.zero_apply]
      have htop : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin M))) ≤
          LinearMap.ker (toEuclideanLin D) := by
        rw [← Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := W)]
        exact sup_le hWk hWp
      have hD : toEuclideanLin D = 0 := LinearMap.ext fun v ↦
        (LinearMap.mem_ker.mp (htop Submodule.mem_top)).trans (LinearMap.zero_apply v).symm
      exact toEuclideanLin.injective (hD.trans (map_zero _).symm)
    -- Step 3: `Θ' = Θ P + Ē Eᴴ`, where `P = I - E Eᴴ` projects onto `W`
    obtain ⟨P, hP⟩ : ∃ P, P = 1 - E * Eᴴ := ⟨_, rfl⟩
    have hPh : Pᴴ = P := by
      rw [hP, conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
    have hPE : P * E = 0 := by
      rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hE1, Matrix.mul_one, sub_self]
    have hEP : Eᴴ * P = 0 := by
      rw [← hPh, ← conjTranspose_mul, hPE, conjTranspose_zero]
    have hPP : P * P = P := by
      nth_rewrite 1 [hP]
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hEP, Matrix.mul_zero, sub_zero]
    have hPA : ∀ A : Matrix (Fin M) (Fin K) ℂ, Eᴴ * A = 0 → P * A = A := by
      intro A hA
      rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hA, Matrix.mul_zero, sub_zero]
    have hΘ1 : Θᴴ * Θ = 1 := by
      rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff').1 hΘu
    have hΘX' : Θᴴ * Y = X := by rw [← hΘX, ← Matrix.mul_assoc, hΘ1, Matrix.one_mul]
    have hΘY' : Θᴴ * cj X = cj Y := by rw [← hΘY, ← Matrix.mul_assoc, hΘ1, Matrix.one_mul]
    have hEcE : Eᵀ * cj E = 1 := by rw [← cj_conjTranspose, ← cj_mul, hE1, cj_one]
    have hK : Eᵀ * Θ * P = 0 := by
      apply hspan
      · rw [Matrix.mul_assoc, hPA X hEX, Matrix.mul_assoc, hΘX, ← cj_conjTranspose E, ← cj_cj Y,
          ← cj_mul, hEY, cj_zero]
      · rw [Matrix.mul_assoc, hPA _ hEY, Matrix.mul_assoc, hΘY, ← cj_conjTranspose E, ← cj_mul,
          hEX, cj_zero]
      · rw [Matrix.mul_assoc, hPE, Matrix.mul_zero]
    have hK' : P * Θᴴ * cj E = 0 := by
      simpa [conjTranspose_mul, hPh, Matrix.mul_assoc] using congrArg conjTranspose hK
    have hsym : Pᵀ * Θᵀ = Θ * P := by
      have hPt : Pᵀ = cj P := by rw [← cj_conjTranspose, hPh]
      have hΘt : Θᵀ = cj Θᴴ := (cj_conjTranspose Θ).symm
      rw [← sub_eq_zero]
      apply hspan
      · rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hPA X hEX, hΘX, hPt, hΘt, ← cj_cj X,
          ← cj_mul, hΘY', ← cj_mul, hPA _ hEY, cj_cj, sub_self]
      · rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hPA _ hEY, hΘY, hPt, hΘt, ← cj_mul,
          hΘX', ← cj_mul, hPA X hEX, sub_self]
      · rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hPE, Matrix.mul_zero, sub_zero, hPt,
          hΘt, ← cj_cj E, ← cj_mul, ← cj_mul, ← Matrix.mul_assoc, hK', cj_zero]
    refine ⟨Θ * P + cj E * Eᴴ, ?_, ?_, ?_⟩
    · rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
      have : (Θ * P + cj E * Eᴴ)ᴴ * (Θ * P + cj E * Eᴴ) =
          P * (Θᴴ * Θ) * P + P * Θᴴ * cj E * Eᴴ + E * (Eᵀ * Θ * P) + E * (Eᵀ * cj E) * Eᴴ := by
        simp only [conjTranspose_add, conjTranspose_mul, hPh, conjTranspose_conjTranspose,
          conjTranspose_cj, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel
      rw [this, hΘ1, hK, hK', hEcE]
      simp only [Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero]
      rw [hPP, hP, sub_add_cancel]
    · simp only [IsSymm, transpose_add, transpose_mul, transpose_conjTranspose_eq_cj, transpose_cj,
        hsym]
    · simp only [Matrix.add_mul, Matrix.mul_assoc, hPA X hEX, hΘX, hEX, Matrix.mul_zero, add_zero]

/-! ### Definition 1, Theorem 1, and Corollary 1 -/

/-- **Definition 1.** Reciprocal RIS performs as non-reciprocal RIS for the metric `f` and the
channel `H_T ∈ ℂ^{M×N_T}` when some optimal non-reciprocal RIS is reciprocal, i.e. some
symmetric unitary `Θ` maximizes `f(Θ H_T)` over all unitary matrices. Since `𝒮 ⊆ 𝒰`, this is
equivalent to `max_{Θ ∈ 𝒮} f(Θ H_T) = max_{Θ ∈ 𝒰} f(Θ H_T)` with both maxima attained. -/
def ReciprocalPerformsAsNonReciprocal {M NT : ℕ} (f : Matrix (Fin M) (Fin NT) ℂ → ℝ)
    (HT : Matrix (Fin M) (Fin NT) ℂ) : Prop :=
  ∃ Θ ∈ unitaryGroup (Fin M) ℂ, Θ.IsSymm ∧
    IsMaxOn (fun Θ ↦ f (Θ * HT)) (unitaryGroup (Fin M) ℂ) Θ

/-- **Theorem 1.** Reciprocal RIS performs as non-reciprocal RIS if and only if there exists an
optimal non-reciprocal RIS `Θ⋆ ∈ 𝒰` for which `H_Tᵀ Θ⋆ H_T` is symmetric. -/
theorem reciprocalPerformsAsNonReciprocal_iff {M NT : ℕ} (f : Matrix (Fin M) (Fin NT) ℂ → ℝ)
    (HT : Matrix (Fin M) (Fin NT) ℂ) :
    ReciprocalPerformsAsNonReciprocal f HT ↔
      ∃ Θ ∈ unitaryGroup (Fin M) ℂ, IsMaxOn (fun Θ ↦ f (Θ * HT)) (unitaryGroup (Fin M) ℂ) Θ ∧
        (HTᵀ * Θ * HT).IsSymm := by
  constructor
  · -- an optimal reciprocal RIS is an optimal non-reciprocal RIS, and `H_Tᵀ Θ H_T` is symmetric
    rintro ⟨Θ, hΘu, hΘs, hmax⟩
    exact ⟨Θ, hΘu, hmax, by simp only [IsSymm, transpose_mul, transpose_transpose, hΘs.eq,
      Matrix.mul_assoc]⟩
  · -- by Lemma 2, a reciprocal RIS reproduces `Θ⋆ H_T`, so it is optimal too
    rintro ⟨Θ, hΘu, hmax, hsym⟩
    obtain ⟨Θs, hΘsu, hΘss, hΘsH⟩ := (exists_symmUnitary_mul_eq_iff HT (Θ * HT)).2
      ⟨(exists_unitary_mul_eq_iff HT (Θ * HT)).1 ⟨Θ, hΘu, rfl⟩,
        by simpa only [Matrix.mul_assoc] using hsym⟩
    refine ⟨Θs, hΘsu, hΘss, fun Θ' hΘ' ↦ ?_⟩
    simpa only [hΘsH] using hmax hΘ'

/-- A rank-one matrix is an outer product: `H = a bᵀ`. -/
lemma exists_eq_outer_of_rank_eq_one {M N : ℕ} (H : Matrix (Fin M) (Fin N) ℂ)
    (hH : H.rank = 1) : ∃ (a : Fin M → ℂ) (b : Fin N → ℂ), ∀ i j, H i j = a i * b j := by
  rw [Matrix.rank, finrank_eq_one_iff'] at hH
  obtain ⟨v, -, hv⟩ := hH
  choose c hc using fun j ↦ hv ⟨H.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨v, c, fun i j ↦ ?_⟩
  have := congrArg (fun w : LinearMap.range H.mulVecLin ↦ (w : Fin M → ℂ) i) (hc j)
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mulVecLin_apply,
    mulVec_single_one, col_apply] at this
  rw [← this, mul_comm]

/-- If `rank H = 1`, then `Hᵀ Θ H = (aᵀ Θ a) b bᵀ` is symmetric for every `Θ`. -/
lemma isSymm_transpose_mul_mul_of_rank_eq_one {M N : ℕ} (H : Matrix (Fin M) (Fin N) ℂ)
    (hH : H.rank = 1) (Θ : Matrix (Fin M) (Fin M) ℂ) : (Hᵀ * Θ * H).IsSymm := by
  obtain ⟨a, b, hab⟩ := exists_eq_outer_of_rank_eq_one H hH
  refine IsSymm.ext fun k l ↦ ?_
  simp only [transpose_apply, Matrix.mul_apply, hab, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Corollary 1.** If `rank H_T = 1`, then reciprocal RIS performs as non-reciprocal RIS
(provided an optimal non-reciprocal RIS exists). -/
theorem reciprocalPerformsAsNonReciprocal_of_rank_eq_one {M NT : ℕ}
    (f : Matrix (Fin M) (Fin NT) ℂ → ℝ) (HT : Matrix (Fin M) (Fin NT) ℂ) (hHT : HT.rank = 1)
    (hopt : ∃ Θ ∈ unitaryGroup (Fin M) ℂ,
      IsMaxOn (fun Θ ↦ f (Θ * HT)) (unitaryGroup (Fin M) ℂ) Θ) :
    ReciprocalPerformsAsNonReciprocal f HT :=
  let ⟨Θ, hΘu, hΘ⟩ := hopt
  (reciprocalPerformsAsNonReciprocal_iff f HT).2
    ⟨Θ, hΘu, hΘ, isSymm_transpose_mul_mul_of_rank_eq_one HT hHT Θ⟩

/-! ### Metrics of the form `f(H_R Θ)` -/

/-- Analogue of **Definition 1** for metrics of the form `f(H_R Θ)`, with `H_R ∈ ℂ^{N_R×M}`:
some symmetric unitary `Θ` maximizes `f(H_R Θ)` over all unitary matrices. -/
def ReciprocalPerformsAsNonReciprocalRx {M NR : ℕ} (f : Matrix (Fin NR) (Fin M) ℂ → ℝ)
    (HR : Matrix (Fin NR) (Fin M) ℂ) : Prop :=
  ∃ Θ ∈ unitaryGroup (Fin M) ℂ, Θ.IsSymm ∧
    IsMaxOn (fun Θ ↦ f (HR * Θ)) (unitaryGroup (Fin M) ℂ) Θ

/-- The transpose of a unitary matrix is unitary. -/
lemma transpose_mem_unitaryGroup {M : ℕ} {Θ : Matrix (Fin M) (Fin M) ℂ}
    (hΘ : Θ ∈ unitaryGroup (Fin M) ℂ) : Θᵀ ∈ unitaryGroup (Fin M) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_transpose_eq_cj,
    ← cj_conjTranspose, ← cj_mul, ← star_eq_conjTranspose, (mem_unitaryGroup_iff).1 hΘ, cj_one]

/-- Analogue of **Theorem 1** for metrics of the form `f(H_R Θ)`: reciprocal RIS performs as
non-reciprocal RIS if and only if there exists an optimal non-reciprocal RIS `Θ⋆ ∈ 𝒰` for which
the round-trip channel `H_R Θ⋆ H_Rᵀ` from the receiving antennas back to themselves is
symmetric. -/
theorem reciprocalPerformsAsNonReciprocalRx_iff {M NR : ℕ} (f : Matrix (Fin NR) (Fin M) ℂ → ℝ)
    (HR : Matrix (Fin NR) (Fin M) ℂ) :
    ReciprocalPerformsAsNonReciprocalRx f HR ↔
      ∃ Θ ∈ unitaryGroup (Fin M) ℂ, IsMaxOn (fun Θ ↦ f (HR * Θ)) (unitaryGroup (Fin M) ℂ) Θ ∧
        (HR * Θ * HRᵀ).IsSymm := by
  constructor
  · rintro ⟨Θ, hΘu, hΘs, hmax⟩
    exact ⟨Θ, hΘu, hmax, by simp only [IsSymm, transpose_mul, transpose_transpose, hΘs.eq,
      Matrix.mul_assoc]⟩
  · -- by Lemma 2 with `X = H_Rᵀ`, a reciprocal RIS reproduces `Θ⋆ᵀ H_Rᵀ = (H_R Θ⋆)ᵀ`
    rintro ⟨Θ, hΘu, hmax, hsym⟩
    have hsym' : (HRᵀᵀ * (Θᵀ * HRᵀ)).IsSymm := by
      have : HR * Θᵀ * HRᵀ = HR * Θ * HRᵀ := by
        simpa only [transpose_mul, transpose_transpose, Matrix.mul_assoc] using hsym.eq
      rw [transpose_transpose, ← Matrix.mul_assoc, this]
      exact hsym
    obtain ⟨Θs, hΘsu, hΘss, hΘsH⟩ := (exists_symmUnitary_mul_eq_iff HRᵀ (Θᵀ * HRᵀ)).2
      ⟨(exists_unitary_mul_eq_iff HRᵀ (Θᵀ * HRᵀ)).1 ⟨Θᵀ, transpose_mem_unitaryGroup hΘu, rfl⟩,
        hsym'⟩
    have hR : HR * Θs = HR * Θ := by
      simpa only [transpose_mul, transpose_transpose, hΘss.eq] using congrArg transpose hΘsH
    refine ⟨Θs, hΘsu, hΘss, fun Θ' hΘ' ↦ ?_⟩
    simpa only [hR] using hmax hΘ'

/-- If `rank H = 1`, then `H Θ Hᵀ` is symmetric for every `Θ`. -/
lemma isSymm_mul_mul_transpose_of_rank_eq_one {M N : ℕ} (H : Matrix (Fin N) (Fin M) ℂ)
    (hH : H.rank = 1) (Θ : Matrix (Fin M) (Fin M) ℂ) : (H * Θ * Hᵀ).IsSymm := by
  obtain ⟨a, b, hab⟩ := exists_eq_outer_of_rank_eq_one H hH
  refine IsSymm.ext fun k l ↦ ?_
  simp only [transpose_apply, Matrix.mul_apply, hab, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

/-- Analogue of **Corollary 1** for metrics of the form `f(H_R Θ)`: if `rank H_R = 1`, then
reciprocal RIS performs as non-reciprocal RIS (provided an optimal non-reciprocal RIS exists). -/
theorem reciprocalPerformsAsNonReciprocalRx_of_rank_eq_one {M NR : ℕ}
    (f : Matrix (Fin NR) (Fin M) ℂ → ℝ) (HR : Matrix (Fin NR) (Fin M) ℂ) (hHR : HR.rank = 1)
    (hopt : ∃ Θ ∈ unitaryGroup (Fin M) ℂ,
      IsMaxOn (fun Θ ↦ f (HR * Θ)) (unitaryGroup (Fin M) ℂ) Θ) :
    ReciprocalPerformsAsNonReciprocalRx f HR :=
  let ⟨Θ, hΘu, hΘ⟩ := hopt
  (reciprocalPerformsAsNonReciprocalRx_iff f HR).2
    ⟨Θ, hΘu, hΘ, isSymm_mul_mul_transpose_of_rank_eq_one HR hHR Θ⟩

/-! ### Metrics of the whole channel `H = H_RT + H_R Θ H_T` -/

/-- For any metric `h` of the channel `H = H_RT + H_R Θ H_T`, if `rank H_T = 1` or
`rank H_R = 1`, then some reciprocal RIS is optimal among all non-reciprocal RISs (provided an
optimal non-reciprocal RIS exists). In particular, single-user SISO, SIMO and MISO systems never
benefit from non-reciprocal RIS. -/
theorem reciprocalPerformsAsNonReciprocal_channel_of_rank_eq_one {M NT NR : ℕ}
    (h : Matrix (Fin NR) (Fin NT) ℂ → ℝ) (HRT : Matrix (Fin NR) (Fin NT) ℂ)
    (HR : Matrix (Fin NR) (Fin M) ℂ) (HT : Matrix (Fin M) (Fin NT) ℂ)
    (hrank : HT.rank = 1 ∨ HR.rank = 1)
    (hopt : ∃ Θ ∈ unitaryGroup (Fin M) ℂ,
      IsMaxOn (fun Θ ↦ h (HRT + HR * Θ * HT)) (unitaryGroup (Fin M) ℂ) Θ) :
    ∃ Θ ∈ unitaryGroup (Fin M) ℂ, Θ.IsSymm ∧
      IsMaxOn (fun Θ ↦ h (HRT + HR * Θ * HT)) (unitaryGroup (Fin M) ℂ) Θ := by
  rcases hrank with hHT | hHR
  · -- a metric of `Θ H_T`
    simp only [Matrix.mul_assoc] at hopt ⊢
    exact reciprocalPerformsAsNonReciprocal_of_rank_eq_one (fun Z ↦ h (HRT + HR * Z)) HT hHT hopt
  · -- a metric of `H_R Θ`
    exact reciprocalPerformsAsNonReciprocalRx_of_rank_eq_one (fun Z ↦ h (HRT + Z * HT)) HR hHR
      hopt

/-! ### Definition 2, Theorem 2, and Corollary 2 -/

/-- **Definition 2.** Reciprocal RIS performs as non-reciprocal RIS in the presence of precoding,
for the metric `g`, the channel `H_T ∈ ℂ^{M×N_T}` and the set `𝓕 ⊆ ℂ^{N_T×K}` of feasible
precoders, when some optimal pair of non-reciprocal RIS and precoder has a reciprocal RIS, i.e.
some `(Θ, F)` with `Θ` symmetric unitary and `F ∈ 𝓕` maximizes `g(F, Θ H_T F)` over `𝒰 × 𝓕`.
The metric depends on `Θ` through `Θ H_T F`, and may also depend on `F` directly (e.g. through
`H_RT F`). Since `𝒮 ⊆ 𝒰`, this is equivalent to
`max_{Θ ∈ 𝒮, F ∈ 𝓕} g(F, Θ H_T F) = max_{Θ ∈ 𝒰, F ∈ 𝓕} g(F, Θ H_T F)` with both maxima
attained. -/
def ReciprocalPerformsAsNonReciprocalWithPrecoding {M NT K : ℕ}
    (g : Matrix (Fin NT) (Fin K) ℂ → Matrix (Fin M) (Fin K) ℂ → ℝ)
    (HT : Matrix (Fin M) (Fin NT) ℂ) (𝓕 : Set (Matrix (Fin NT) (Fin K) ℂ)) : Prop :=
  ∃ Θ ∈ unitaryGroup (Fin M) ℂ, Θ.IsSymm ∧ ∃ F ∈ 𝓕,
    IsMaxOn (fun p ↦ g p.2 (p.1 * HT * p.2)) (unitaryGroup (Fin M) ℂ ×ˢ 𝓕) (Θ, F)

/-- **Theorem 2.** Reciprocal RIS performs as non-reciprocal RIS in the presence of precoding if
and only if there exists an optimal pair of non-reciprocal RIS `Θ⋆ ∈ 𝒰` and precoder `F⋆ ∈ 𝓕`
for which `F⋆ᵀ H_Tᵀ Θ⋆ H_T F⋆` is symmetric. -/
theorem reciprocalPerformsAsNonReciprocalWithPrecoding_iff {M NT K : ℕ}
    (g : Matrix (Fin NT) (Fin K) ℂ → Matrix (Fin M) (Fin K) ℂ → ℝ)
    (HT : Matrix (Fin M) (Fin NT) ℂ) (𝓕 : Set (Matrix (Fin NT) (Fin K) ℂ)) :
    ReciprocalPerformsAsNonReciprocalWithPrecoding g HT 𝓕 ↔
      ∃ Θ ∈ unitaryGroup (Fin M) ℂ, ∃ F ∈ 𝓕,
        IsMaxOn (fun p ↦ g p.2 (p.1 * HT * p.2)) (unitaryGroup (Fin M) ℂ ×ˢ 𝓕) (Θ, F) ∧
        (Fᵀ * HTᵀ * Θ * HT * F).IsSymm := by
  constructor
  · -- an optimal reciprocal pair is optimal over `𝒰 × 𝓕`, and `Fᵀ H_Tᵀ Θ H_T F` is symmetric
    rintro ⟨Θ, hΘu, hΘs, F, hF, hmax⟩
    exact ⟨Θ, hΘu, F, hF, hmax, by simp only [IsSymm, transpose_mul, transpose_transpose, hΘs.eq,
      Matrix.mul_assoc]⟩
  · -- by Lemma 2 with `X = H_T F⋆`, a reciprocal RIS reproduces `Θ⋆ H_T F⋆`, hence optimal
    rintro ⟨Θ, hΘu, F, hF, hmax, hsym⟩
    obtain ⟨Θs, hΘsu, hΘss, hΘsH⟩ := (exists_symmUnitary_mul_eq_iff (HT * F) (Θ * HT * F)).2
      ⟨(exists_unitary_mul_eq_iff (HT * F) (Θ * HT * F)).1 ⟨Θ, hΘu, (Matrix.mul_assoc _ _ _).symm⟩,
        by simpa only [transpose_mul, Matrix.mul_assoc] using hsym⟩
    refine ⟨Θs, hΘsu, hΘss, F, hF, fun p hp ↦ ?_⟩
    simpa only [Matrix.mul_assoc, hΘsH] using hmax hp

/-- **Corollary 2.** If single-stream transmission (`K = 1`) is used, then reciprocal RIS performs
as non-reciprocal RIS in the presence of precoding (provided an optimal pair of non-reciprocal RIS
and precoder exists). -/
theorem reciprocalPerformsAsNonReciprocalWithPrecoding_of_single_stream {M NT : ℕ}
    (g : Matrix (Fin NT) (Fin 1) ℂ → Matrix (Fin M) (Fin 1) ℂ → ℝ)
    (HT : Matrix (Fin M) (Fin NT) ℂ) (𝓕 : Set (Matrix (Fin NT) (Fin 1) ℂ))
    (hopt : ∃ Θ ∈ unitaryGroup (Fin M) ℂ, ∃ F ∈ 𝓕,
      IsMaxOn (fun p ↦ g p.2 (p.1 * HT * p.2)) (unitaryGroup (Fin M) ℂ ×ˢ 𝓕) (Θ, F)) :
    ReciprocalPerformsAsNonReciprocalWithPrecoding g HT 𝓕 :=
  let ⟨Θ, hΘu, F, hF, hΘF⟩ := hopt
  -- `Fᵀ H_Tᵀ Θ H_T F` is `1 × 1`, hence symmetric
  (reciprocalPerformsAsNonReciprocalWithPrecoding_iff g HT 𝓕).2
    ⟨Θ, hΘu, F, hF, hΘF, IsSymm.ext fun i j ↦ by rw [Subsingleton.elim i j]⟩

end ReciprocalRIS
