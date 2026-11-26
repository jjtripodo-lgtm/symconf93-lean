module
public import Symconf93.AmbientNormPositive
public import Symconf93.DiagonalConvolution

@[expose] public section

/-! Verify the count-facing interface of a literal modular congruence
certificate, not a prescribed diagonal factor of an arbitrary source. -/
namespace Symconf93
open Matrix
open scoped BigOperators Matrix

section General
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

omit [DecidableEq ι] in
private theorem gram_reindex_mulVec (G E : Matrix ι ι R) (x : ι→R) :
    gramNorm (Eᵀ*G*E) x=gramNorm G (E *ᵥ x) := by
  unfold gramNorm
  rw [←mulVec_mulVec,←mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]

theorem gram_contrast_unit_congruence (G : Matrix ι ι R)
    (E : (Matrix ι ι R)ˣ) (t : R) :
    contrast (gramNorm ((E:Matrix ι ι R)ᵀ*G*(E:Matrix ι ι R))) t =
      contrast (gramNorm G) t := by
  let M : Matrix ι ι R := ↑E
  let N : Matrix ι ι R := ↑E⁻¹
  have hn : N*M=1 := Units.inv_mul E
  have hm : M*N=1 := Units.mul_inv E
  let e : (ι→R) ≃ (ι→R) :=
    {toFun := fun x => M *ᵥ x
     invFun := fun x => N *ᵥ x
     left_inv := by
       intro x
       change N *ᵥ (M *ᵥ x)=x
       rw [mulVec_mulVec,hn,one_mulVec]
     right_inv := by
       intro x
       change M *ᵥ (N *ᵥ x)=x
       rw [mulVec_mulVec,hm,one_mulVec] }
  have h (b : R) :
      Nat.card {v : ι→R // gramNorm (Mᵀ*G*M) v=b} =
        Nat.card {v : ι→R // gramNorm G v=b} := by
    apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
    intro x
    change gramNorm (Mᵀ*G*M) x=b ↔
      gramNorm G (M *ᵥ x)=b
    rw [gram_reindex_mulVec]
  unfold contrast
  change (Nat.card {v : ι→R // gramNorm (Mᵀ*G*M) v=0}:ℤ)-
    Nat.card {v : ι→R // gramNorm (Mᵀ*G*M) v=t}=_
  rw [h,h]

theorem diagonalNorm_same_quadratic {n : ℕ} (D x : Fin n→R) :
    gramNorm (Matrix.diagonal D) x=diagonalNorm D x := by
  unfold gramNorm diagonalNorm dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  ring

theorem diagonal_gram_contrast {n : ℕ} (D : Fin n→R) (t : R) :
    contrast (gramNorm (Matrix.diagonal D)) t =
      (diagonalCount D 0:ℤ)-diagonalCount D t := by
  have h := funext (diagonalNorm_same_quadratic D)
  rw [h]
  rfl

end General

section Integer
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Nonempty ι] [DecidableEq ι] in
private theorem reduce_factor (q : ℕ) (A : Matrix ι ι ℤ) :
    Symconf59.reduceMatrix q (A*Aᵀ)=(Symconf59.reduceMatrix q A)*(Symconf59.reduceMatrix q A)ᵀ := by
  change Matrix.map (A*Aᵀ) (Int.castRingHom (ZMod q))=_
  rw [Matrix.map_mul]
  rfl

/-- Fully explicit input contract for one concrete order-93 modulo-49
arithmetic certificate. The inverse is an exact integral identity, not a
rational number silently reduced modulo an invalid denominator. -/
theorem no_integral_gram49_of_negative_contrast (G B : Matrix ι ι ℤ)
    (d : ℤ) (hd : d≠0) (hB : B*G=d • (1:Matrix ι ι ℤ))
    (w : ZMod 49) (hw : w*(d:ZMod 49)=7)
    (hneg : contrast (gramNorm (Symconf59.reduceMatrix 49 G)) (7:ZMod 49)<0) :
    ¬∃ A:Matrix ι ι ℤ,G=A*Aᵀ := by
  rintro ⟨A,hA⟩
  obtain ⟨M,hM⟩ := integer_gram_has_reduced_scaled_image 49 G A B d hd hA hB 7 w hw
  have hp := genuineGram49_contrast_nonnegative _ M hM
  rw [hA,reduce_factor] at hneg
  exact (not_lt_of_ge hp) hneg

theorem no_integral_gram625_of_negative_contrast (G B : Matrix ι ι ℤ)
    (d : ℤ) (hd : d≠0) (hB : B*G=d • (1:Matrix ι ι ℤ))
    (w : ZMod 625) (hw : w*(d:ZMod 625)=25)
    (hneg : contrast (gramNorm (Symconf59.reduceMatrix 625 G)) (125:ZMod 625)<0) :
    ¬∃ A:Matrix ι ι ℤ,G=A*Aᵀ := by
  rintro ⟨A,hA⟩
  obtain ⟨M,hM⟩ := integer_gram_has_reduced_scaled_image 625 G A B d hd hA hB 25 w hw
  have hp := genuineGram625_contrast_nonnegative _ M hM
  rw [hA,reduce_factor] at hneg
  exact (not_lt_of_ge hp) hneg

end Integer
end Symconf93

#print axioms Symconf93.gram_contrast_unit_congruence
#print axioms Symconf93.diagonal_gram_contrast
#print axioms Symconf93.no_integral_gram49_of_negative_contrast
#print axioms Symconf93.no_integral_gram625_of_negative_contrast
