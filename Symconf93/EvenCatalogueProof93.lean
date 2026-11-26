module
public import Symconf93.EvenReduction93

@[expose] public section

-- AnchoredDeterminant93.lean section

/-! Extract one row-sum eigenvalue over the integers, and retain the
exact anchored quotient matrix. No division or nonsingularity premise. -/
namespace Symconf93
open Matrix
open scoped BigOperators Matrix

def anchoredMinor93 {R : Type*} [Sub R] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => M i.succ j.succ - M 0 j.succ

section
variable {R : Type*} [CommRing R] {n : ℕ}

/-- Use all ones as the first basis vector. This determinant identity
is valid over any commutative ring, including integer modulo 49. -/
theorem det_eq_rowsum_mul_anchored93 (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (d : R) (hs : ∀ i, ∑ j, M i j=d) :
    M.det=d*(anchoredMinor93 M).det := by
  let U := Matrix.updateCol M 0 (fun _ => d)
  let c : Fin (n+1) → R := fun i => if i=0 then 1 else -1
  let T := Matrix.updateCol (1:Matrix (Fin (n+1)) (Fin (n+1)) R) 0 c
  let V := T*U
  have hU : U.det=M.det := by
    have h := Matrix.det_updateCol_sum M (0:Fin (n+1)) (fun _ => (1:R))
    simpa only [one_smul,hs,U] using h
  have hT : T.det=1 := by
    have hc : (fun k => ∑ i, c i • (1:Matrix (Fin (n+1)) (Fin (n+1)) R) k i)=c := by
      funext k
      simp [Matrix.one_apply,smul_eq_mul,mul_ite]
    have h := Matrix.det_updateCol_sum (1:Matrix (Fin (n+1)) (Fin (n+1)) R) 0 c
    rw [hc] at h
    simpa [T,c] using h
  have hVzero (j : Fin (n+1)) : V 0 j=U 0 j := by
    have hNe (i : Fin n) : (0:Fin (n+1))≠i.succ := (Fin.succ_ne_zero i).symm
    simp [V,T,c,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.updateCol_apply,Matrix.one_apply,hNe]
  have hVsucc (i : Fin n) (j : Fin (n+1)) : V i.succ j=U i.succ j-U 0 j := by
    simp [V,T,c,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.updateCol_apply,Matrix.one_apply,ite_mul]
    ring
  have hV0 : V 0 0=d := by rw [hVzero]; simp [U]
  have hV1 (i : Fin n) : V i.succ 0=0 := by
    rw [hVsucc]
    simp [U]
  have hMinor : V.submatrix Fin.succ Fin.succ=anchoredMinor93 M := by
    ext i j
    change V i.succ j.succ=_
    rw [hVsucc]
    simp [U,anchoredMinor93]
  have hDet : V.det=M.det := by
    change (T*U).det=M.det
    rw [Matrix.det_mul,hT,hU,one_mul]
  rw [←hDet,Matrix.det_succ_column_zero,Fin.sum_univ_succ]
  simp [hV0,hV1,hMinor]

end
#print axioms det_eq_rowsum_mul_anchored93
end Symconf93

-- CycleUnitValuation93.lean section

/-! Every cycle of length prime to seven contributes exactly one factor
of seven. The proof is the actual anchored modulo-seven cycle kernel. -/
namespace Symconf93
open Matrix Symconf59
open scoped BigOperators Matrix
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def nextEquiv93 (n : ℕ) : Fin n ≃ Fin n where
  toFun := cnext
  invFun := cprev
  left_inv := by
    intro i
    letI : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩
    change (i+1)-1=i
    exact add_sub_cancel_right i 1
  right_inv := cnext_prev

private theorem prev_next93 {n : ℕ} (i : Fin n) : cprev (cnext i)=i :=
  (nextEquiv93 n).symm_apply_apply i

private theorem cycle_const_of_next93 {n : ℕ} {A : Type*} (v : Fin (n+1) → A)
    (hv : ∀ i, v (cnext i)=v i) (i : Fin (n+1)) : v i=v 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i hi =>
    have h : cnext i.castSucc=i.succ := by
      apply Fin.ext
      letI : NeZero (n+1) := ⟨by omega⟩
      change ((i.castSucc + 1 : Fin (n+1)):ℕ)=(i:ℕ)+1
      rw [Fin.val_add,Fin.val_castSucc,Fin.val_one',Nat.add_mod_mod]
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
    rw [←h,hv,hi]

private def cycleHF7 (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 7) :=
  (cycleH93 n).map (Int.castRingHom (ZMod 7))

private theorem cycleH_rows93 {n : ℕ} (i : Fin n) :
    ∑ j, cycleH93 n i j=7 := by
  simp [cycleH93,Finset.sum_sub_distrib]

private theorem cycleHF7_action {n : ℕ} (x : Fin n → ZMod 7) (i : Fin n) :
    (cycleHF7 n *ᵥ x) i=2*x i-x (cnext i)-x (cprev i) := by
  change (∑ j, (cycleHF7 n i j)*x j)=_
  have h (j : Fin n) :
      (cycleHF7 n i j)*x j =
        (if j=i then 2*x j else 0)-(if j=cnext i then x j else 0)-
          (if j=cprev i then x j else 0) := by
    have h9 : (9:ZMod 7)=2 := by decide
    simp only [cycleHF7,cycleH93,Matrix.map_apply,map_sub,map_mul,map_ofNat,
      apply_ite, map_one, map_zero, h9, eq_comm (a:=i)]
    split_ifs <;> ring
  simp_rw [h,Finset.sum_sub_distrib]
  simp

private theorem cycleHF7_sum_zero {n : ℕ} (x : Fin n → ZMod 7) :
    ∑ i, (cycleHF7 n *ᵥ x) i=0 := by
  have hs : (∑ i, x (cnext i)) = ∑ i, x i := Equiv.sum_comp (nextEquiv93 n) x
  have hs' : (∑ i, x (cprev i)) = ∑ i, x i := Equiv.sum_comp (nextEquiv93 n).symm x
  simp_rw [cycleHF7_action,Finset.sum_sub_distrib]
  rw [hs,hs']
  rw [←Finset.mul_sum]
  ring

private theorem cycleHF7_kernel_constant {n : ℕ}
    (hN : ((n+1:ℕ):ZMod 7)≠0) (x : Fin (n+1) → ZMod 7)
    (hx : ∀ i, (cycleHF7 (n+1) *ᵥ x) i=0) :
    ∀ i, x i=x 0 := by
  let d : Fin (n+1) → ZMod 7 := fun i => x i-x (cprev i)
  have hd (i : Fin (n+1)) : d (cnext i)=d i := by
    have h := hx i
    rw [cycleHF7_action] at h
    change x (cnext i)-x (cprev (cnext i))=x i-x (cprev i)
    rw [prev_next93]
    linear_combination -h
  have hC := cycle_const_of_next93 d hd
  have hS := Equiv.sum_comp (nextEquiv93 (n+1)).symm x
  have hD : ∑ i, d i=0 := by
    change (∑ i : Fin (n+1), (x i - x (cprev i))) = 0
    rw [Finset.sum_sub_distrib]
    change (∑ i, x i)-(∑ i, x ((nextEquiv93 (n+1)).symm i))=0
    rw [hS,sub_self]
  have hd₀ : d 0=0 := by
    simp_rw [hC] at hD
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hD
    exact (mul_eq_zero.mp hD).resolve_left hN
  have hn (i : Fin (n+1)) : x (cnext i)=x i := by
    have h := (hC (cnext i)).trans hd₀
    change x (cnext i)-x (cprev (cnext i))=0 at h
    rw [prev_next93] at h
    exact sub_eq_zero.mp h
  exact cycle_const_of_next93 x hn

private theorem anchorMinorMod7_unit {n : ℕ} (hN : ((n+1:ℕ):ZMod 7)≠0) :
    ((anchoredMinor93 (cycleH93 (n+1))).map (Int.castRingHom (ZMod 7))).det≠0 := by
  let B := (anchoredMinor93 (cycleH93 (n+1))).map (Int.castRingHom (ZMod 7))
  have hKer (x : Fin n → ZMod 7) (hx : B *ᵥ x=0) : x=0 := by
    let v : Fin (n+1) → ZMod 7 := Fin.cases 0 x
    let F := cycleHF7 (n+1)
    have hSum (i : Fin (n+1)) : (F *ᵥ v) i=∑ j : Fin n, F i j.succ*x j := by
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,v]
    have hDiff (i : Fin n) : (B *ᵥ x) i=(F *ᵥ v) i.succ-(F *ᵥ v) 0 := by
      rw [hSum,hSum]
      simp [B,F,cycleHF7,Matrix.mulVec,dotProduct,anchoredMinor93,Finset.sum_sub_distrib,sub_mul]
    have hCon (i : Fin (n+1)) : (F *ᵥ v) i=(F *ᵥ v) 0 := by
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        have hh : (B *ᵥ x) i=0 := congrFun hx i
        rw [hDiff] at hh
        exact sub_eq_zero.mp hh
    have hH : (F *ᵥ v) 0=0 := by
      have h := cycleHF7_sum_zero v
      change (∑ i, (F *ᵥ v) i)=0 at h
      simp_rw [hCon] at h
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_left hN
    have hV := cycleHF7_kernel_constant hN v (fun i => (hCon i).trans hH)
    funext i
    exact hV i.succ
  have hInj : Function.Injective B.mulVec := by
    intro x y h
    apply sub_eq_zero.mp
    apply hKer
    rw [Matrix.mulVec_sub,h,sub_self]
  have hU : IsUnit B := Matrix.mulVec_injective_iff_isUnit.mp hInj
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero

theorem cycleH93_valuation_seven {n : ℕ} (hn : ¬7∣n) :
    (cycleH93 n).det.natAbs.factorization 7=1 := by
  cases n with
  | zero => exact (hn (dvd_zero 7)).elim
  | succ n =>
    let B := anchoredMinor93 (cycleH93 (n+1))
    have hN : ((n+1:ℕ):ZMod 7)≠0 := fun h => hn ((ZMod.natCast_eq_zero_iff _ _).mp h)
    have hF : (B.det:ZMod 7)≠0 := by
      rw [Int.cast_det]
      exact anchorMinorMod7_unit hN
    have hP : ¬7∣B.det.natAbs := by
      intro h
      exact hF ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr (Int.natCast_dvd.mpr h))
    have hB : B.det.natAbs≠0 := by
      intro h
      exact hP (h ▸ dvd_zero 7)
    have h : (cycleH93 (n+1)).det=7*B.det :=
      det_eq_rowsum_mul_anchored93 (cycleH93 (n+1)) 7 cycleH_rows93
    rw [h,Int.natAbs_mul]
    change ((7:ℕ)*B.det.natAbs).factorization 7=1
    rw [Nat.factorization_mul (by decide : (7:ℕ)≠0) hB,Finsupp.add_apply,
      Nat.Prime.factorization_self (by decide : Nat.Prime 7),
      Nat.factorization_eq_zero_of_not_dvd hP,add_zero]

#print axioms cycleH93_valuation_seven
end Symconf93

-- EvenCatalogue93.lean section

/-! The ten genuine even-profile exclusions. The selector reads the
already-bound profiles37 and never accepts a permutation of a literal
Gram without proof. -/
namespace Symconf93
open Matrix
open scoped BigOperators Matrix

def evenProfiles93 : List (List ℕ) :=
  profiles37.filter (fun P => P.length % 2 == 0)

theorem evenProfiles93_valuations :
    evenProfiles93.map (fun P => P.length-1)=[21,19,13,17,11,9,5,15,9,3] := by
  decide

private theorem evenProfiles93_lengths :
    evenProfiles93.all (fun P => decide (P.sum=93) &&
      P.all (fun l => decide (¬7∣l)))=true := by decide

private theorem evenProfile_mem {P : List ℕ} (hP : P∈profiles37) (hEven : P.length%2=0) :
    P∈evenProfiles93 := by
  simp [evenProfiles93,hP,hEven]

private theorem card_blocks93 (P : List ℕ) :
    Fintype.card (BlocksOf P)=P.sum := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp

theorem original_even_profile_val7 {P : List ℕ} (hP : P∈profiles37)
    (hEven : P.length%2=0) :
    (profileGram93 P).det.natAbs.factorization 7=P.length-1 := by
  have h := List.all_eq_true.mp evenProfiles93_lengths P (evenProfile_mem hP hEven)
  have hS : P.sum=93 := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  have hA := (Bool.and_eq_true_iff.mp h).2
  apply profile_gram_val7_of_cycle_units ((card_blocks93 P).trans hS)
  intro i
  apply cycleH93_valuation_seven
  exact of_decide_eq_true (List.all_eq_true.mp hA _ (List.get_mem P i))

/-- All ten even rows of the original 37-row Gram catalogue are false
as genuine integral Gram factors, with no assumptions on any odd row. -/
theorem no_original_even_profile_gram {P : List ℕ} (hP : P∈profiles37)
    (hEven : P.length%2=0) :
    ¬∃ B : Matrix (BlocksOf P) (BlocksOf P) ℤ,profileGram93 P=B*Bᵀ := by
  have h := List.all_eq_true.mp evenProfiles93_lengths P (evenProfile_mem hP hEven)
  have hS : P.sum=93 := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  have hLen : 0<P.length := by cases P <;> simp_all
  apply no_integral_gram_of_odd_val (profileGram93 P) 7
  rw [original_even_profile_val7 hP hEven]
  omega

/-- The Arithmetic93 owner need now supply only the odd-count rows
other than the two original endgame shapes. -/
theorem Arithmetic93_of_odd_rows
    (hOdd : ∀ P : List ℕ, P∈profiles37 → P.length%2=1 → P≠P31 → P≠Mixed37 →
      ¬∃ B : Matrix (BlocksOf P) (BlocksOf P) ℤ,profileGram93 P=B*Bᵀ) :
    Arithmetic93 := by
  intro P hP h31 hMix
  by_cases hEven : P.length%2=0
  · exact no_original_even_profile_gram hP hEven
  · exact hOdd P hP (by omega) h31 hMix

#print axioms evenProfiles93_valuations
#print axioms original_even_profile_val7
#print axioms no_original_even_profile_gram
#print axioms Arithmetic93_of_odd_rows
end Symconf93
