module
public import Symconf93.Terminal93
public import Symconf93.OddDeterminantValuation
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! Arithmetic bridge for the ten literal even profiles. No numerical
cycle determinant claims enter this file. -/
namespace Symconf93
open Matrix Symconf59
open scoped BigOperators Matrix

def cycleH93 (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  9*(if i=j then 1 else 0)-(if j=cnext i then 1 else 0)-(if j=cprev i then 1 else 0)

def profileH93 (P : List ℕ) : Matrix (BlocksOf P) (BlocksOf P) ℤ :=
  fun i j => profileGram93 P i j-1

private theorem profileH93_rows (P : List ℕ) (i : BlocksOf P) :
    ∑ j, profileH93 P i j=7 := by
  unfold profileH93 profileGram93 profileAdj93
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, eq_comm]
  ring

/-- For the literal original Gram, the rank-one correction is exact.
No invertibility of H is presumed. -/
theorem profile_det_rank_one93 (P : List ℕ) (hN : Fintype.card (BlocksOf P)=93) :
    7*(profileGram93 P).det=100*(profileH93 P).det := by
  let I := BlocksOf P
  let H : Matrix I I ℚ := (profileH93 P).map (Int.castRingHom ℚ)
  let G : Matrix I I ℚ := (profileGram93 P).map (Int.castRingHom ℚ)
  let u : I → ℚ := fun _ => 1/7
  let v : I → ℚ := fun _ => 1
  let L : Matrix I Unit ℚ := replicateCol Unit u
  let R : Matrix Unit I ℚ := replicateRow Unit v
  have hH (i : I) : ∑ j, H i j=7 := by
    change (∑ j : BlocksOf P, (profileH93 P i j:ℚ))=7
    exact_mod_cast profileH93_rows P i
  have hL : H*L=replicateCol Unit v := by
    ext i j
    change (∑ a, H i a*(1/7))=1
    rw [←Finset.sum_mul,hH]
    norm_num
  have hFF : H*(1+L*R)=G := by
    rw [Matrix.mul_add,Matrix.mul_one,←Matrix.mul_assoc,hL]
    ext i j
    have h : (replicateCol Unit v*R) i j=1 := by
      simp [R,v,Matrix.mul_apply]
    rw [Matrix.add_apply,h]
    change (profileH93 P i j:ℚ)+1=(profileGram93 P i j:ℚ)
    simp [profileH93]
  have hSmall : (1+L*R).det=(100:ℚ)/7 := by
    change (1+replicateCol Unit u*replicateRow Unit v).det=_
    rw [det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct,u,v,hN,I]
    norm_num
  have hDet := congrArg Matrix.det hFF
  rw [Matrix.det_mul,hSmall] at hDet
  have hC : (7:ℚ)*(profileGram93 P).det=100*(profileH93 P).det := by
    change H.det*(100/7)=G.det at hDet
    rw [Int.cast_det,Int.cast_det]
    change (7:ℚ)*G.det=100*H.det
    linarith only [hDet]
  exact_mod_cast hC

private def blockEquiv93 (P : List ℕ) (i : Fin P.length) :
    Fin (P.get i) ≃ {x : BlocksOf P // x.1=i} where
  toFun j := ⟨⟨i,j⟩,rfl⟩
  invFun x := x.property ▸ x.val.2
  left_inv j := rfl
  right_inv := by
    rintro ⟨⟨a,b⟩,h⟩
    change a=i at h
    subst a
    rfl

theorem profile_H_det_product93 (P : List ℕ) :
    (profileH93 P).det=∏ i : Fin P.length, (cycleH93 (P.get i)).det := by
  have hTri : (profileH93 P).BlockTriangular (fun x : BlocksOf P => x.1) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    have h : j≠i := ne_of_lt hij
    have hEq {z : Fin (P.get i)} : (⟨j,b⟩:BlocksOf P)≠⟨i,z⟩ := by
      intro hz
      exact h (congrArg Sigma.fst hz)
    have hNe : (⟨i,a⟩:BlocksOf P)≠⟨j,b⟩ := (hEq (z:=a)).symm
    simp [profileH93,profileGram93,profileAdj93,hEq,hNe]
  rw [hTri.det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  rw [←Matrix.det_submatrix_equiv_self (blockEquiv93 P i)]
  congr 1
  ext a b
  change profileH93 P ⟨i,a⟩ ⟨i,b⟩=cycleH93 (P.get i) a b
  simp only [profileH93,profileGram93,profileAdj93,cycleH93,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  ring

/-- The final scalar valuation bridge. Its hSmall premise is the seven
closed-cycle unit certificates, not an arbitrary determinant oracle. -/
theorem profile_gram_val7_of_cycle_units {P : List ℕ}
    (hN : Fintype.card (BlocksOf P)=93)
    (hSmall : ∀ i : Fin P.length, ((cycleH93 (P.get i)).det.natAbs.factorization 7)=1) :
    (profileGram93 P).det.natAbs.factorization 7=P.length-1 := by
  let H := (profileH93 P).det.natAbs
  let G := (profileGram93 P).det.natAbs
  have hMul : 7*G=100*H := by
    have h := congrArg Int.natAbs (profile_det_rank_one93 P hN)
    rw [Int.natAbs_mul,Int.natAbs_mul] at h
    exact h
  have hC (i : Fin P.length) : (cycleH93 (P.get i)).det.natAbs≠0 := by
    intro h
    have hv := hSmall i
    rw [h] at hv
    simp at hv
  have hProd : H=∏ i : Fin P.length, (cycleH93 (P.get i)).det.natAbs := by
    unfold H
    rw [profile_H_det_product93]
    let f : ℤ →* ℕ := ⟨⟨Int.natAbs,rfl⟩,Int.natAbs_mul⟩
    exact map_prod f _ _
  have hH : H≠0 := by
    rw [hProd]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hC i)
  have hG : G≠0 := by
    intro h
    rw [h,mul_zero] at hMul
    omega
  have hHval : H.factorization 7=P.length := by
    rw [hProd,Nat.factorization_prod_apply (fun i _ => hC i)]
    calc
      _ = ∑ _ : Fin P.length, (1:ℕ) :=
        Finset.sum_congr rfl (fun i _ => hSmall i)
      _ = _ := by simp
  have h7 : (7:ℕ).factorization 7=1 := Nat.Prime.factorization_self (by decide)
  have h100 : (100:ℕ).factorization 7=0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  have hX := congrArg (fun n : ℕ => n.factorization 7) hMul
  rw [Nat.factorization_mul (by decide : (7:ℕ)≠0) hG,Nat.factorization_mul (by decide : (100:ℕ)≠0) hH,
    Finsupp.add_apply,Finsupp.add_apply,h7,h100,hHval] at hX
  change G.factorization 7=P.length-1
  omega

#print axioms profile_det_rank_one93
#print axioms profile_H_det_product93
#print axioms profile_gram_val7_of_cycle_units
end Symconf93
