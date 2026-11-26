module
public import Symconf59.GramObstruction
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Exact no-Gram certificate for the literal wrapped 59-cycle. -/
namespace Symconf59
open Matrix
open scoped Matrix BigOperators

abbrev Site := Fin 59
abbrev F353 := ZMod 353
instance : Fact (Nat.Prime 353) := ⟨by norm_num⟩

def cycleGram (R : Type*) [Ring R] : Matrix Site Site R :=
  fun i j => (if j=i then 7 else 0)+1-(if j=i+1 then 1 else 0)-(if j=i-1 then 1 else 0)

def cycleGram59 : Matrix Site Site ℤ := cycleGram ℤ

theorem cycleGram_action {R : Type*} [Ring R] (x : Site → R) (i : Site) :
    (cycleGram R *ᵥ x) i =
      7*x i+(∑ j, x j)-x (i+1)-x (i-1) := by
  simp [cycleGram,Matrix.mulVec,dotProduct,add_mul,sub_mul,ite_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]

@[simp] theorem cycleGram59_reduce : reduceMatrix 353 cycleGram59 = cycleGram F353 := by
  ext i j
  change ((cycleGram ℤ i j : ℤ) : F353)=cycleGram F353 i j
  unfold cycleGram
  split_ifs <;> norm_num

def k1 (i : Site) : ℤ := (#[352, 346, 305, 24, 216, 76, 316, 18, 163, 64, 285, 166, 171, 325, 339, 283, 230, 268, 234, 311, 178, 229, 13, 215, 80, 345, 217, 115, 235, 118, 238, 136, 8, 273, 138, 340, 124, 175, 42, 119, 85, 123, 70, 14, 28, 182, 187, 68, 289, 190, 335, 37, 277, 137, 329, 48, 7, 1, 0])[i.val]'i.isLt
def k2 (i : Site) : ℤ := (#[7, 48, 329, 137, 277, 37, 335, 190, 289, 68, 187, 182, 28, 14, 70, 123, 85, 119, 42, 175, 124, 340, 138, 273, 8, 136, 238, 118, 235, 115, 217, 345, 80, 215, 13, 229, 178, 311, 234, 268, 230, 283, 339, 325, 171, 166, 285, 64, 163, 18, 316, 76, 216, 24, 305, 346, 352, 0, 1])[i.val]'i.isLt

set_option maxRecDepth 30000 in
private theorem k1_total : (∑ i, k1 i)=10237 := by decide +kernel
set_option maxRecDepth 30000 in
private theorem k2_total : (∑ i, k2 i)=10237 := by decide +kernel

private theorem k1_total_field : (∑ i, reduceVec 353 k1 i)=0 := by
  change (∑ i, (Int.castRingHom F353) (k1 i))=0
  rw [← map_sum,k1_total]
  decide

private theorem k2_total_field : (∑ i, reduceVec 353 k2 i)=0 := by
  change (∑ i, (Int.castRingHom F353) (k2 i))=0
  rw [← map_sum,k2_total]
  decide

set_option maxRecDepth 30000 in
private theorem k1_rec_field : ∀ i : Site,
    7*reduceVec 353 k1 i-reduceVec 353 k1 (i+1)-reduceVec 353 k1 (i-1)=0 := by decide +kernel

set_option maxRecDepth 30000 in
private theorem k2_rec_field : ∀ i : Site,
    7*reduceVec 353 k2 i-reduceVec 353 k2 (i+1)-reduceVec 353 k2 (i-1)=0 := by decide +kernel

theorem k1_kernel : cycleGram F353 *ᵥ reduceVec 353 k1=0 := by
  funext i
  rw [cycleGram_action,k1_total_field,add_zero]
  exact k1_rec_field i

theorem k2_kernel : cycleGram F353 *ᵥ reduceVec 353 k2=0 := by
  funext i
  rw [cycleGram_action,k2_total_field,add_zero]
  exact k2_rec_field i

private theorem pair_certificate (x y : Site → ℤ) :
    gramPair cycleGram59 x y =
      ∑ i, x i*(7*y i+(∑ j,y j)-y (i+1)-y (i-1)) := by
  unfold gramPair dotProduct
  exact Finset.sum_congr rfl (fun i _ => by rw [cycleGram59,cycleGram_action])

set_option maxRecDepth 30000 in
theorem k11_pair : gramPair cycleGram59 k1 k1=353*336478 := by
  rw [pair_certificate,k1_total]
  decide +kernel

set_option maxRecDepth 30000 in
theorem k12_pair : gramPair cycleGram59 k1 k2=353*325401 := by
  rw [pair_certificate,k2_total]
  decide +kernel

set_option maxRecDepth 30000 in
theorem k21_pair : gramPair cycleGram59 k2 k1=353*325401 := by
  rw [pair_certificate,k1_total]
  decide +kernel

set_option maxRecDepth 30000 in
theorem k22_pair : gramPair cycleGram59 k2 k2=353*336478 := by
  rw [pair_certificate,k2_total]
  decide +kernel

private theorem sum_shift (x : Site → F353) (a : Site) :
    (∑ i, x (i+a))=∑ i, x i := Equiv.sum_comp (Equiv.addRight a) x

/-- Summing the actual kernel equations kills the constant term:
the row sum 64 is a unit modulo 353. -/
theorem cycle_kernel_sum (x : Site → F353)
    (hx : cycleGram F353 *ᵥ x=0) : (∑ i, x i)=0 := by
  have h (i : Site) : 7*x i+(∑ j, x j)-x (i+1)-x (i-1)=0 := by
    rw [← cycleGram_action,hx]
    rfl
  have hs : (∑ i : Site, (7*x i+(∑ j, x j)-x (i+1)-x (i-1)))=0 :=
    Finset.sum_eq_zero (fun i _ => h i)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  rw [sum_shift,show (∑ i : Site,x (i-1))=∑ i,x i by
    simpa only [sub_eq_add_neg] using sum_shift x (-1)] at hs
  have h64 : (64:F353)*(∑ i,x i)=0 := by linear_combination hs
  exact (mul_eq_zero.mp h64).resolve_left (by decide)

private theorem succ_cast (i : ℕ) (hi : i+1<59) :
    (⟨i, by omega⟩ : Site)+1=⟨i+1,hi⟩ := by
  apply Fin.ext
  exact Fin.val_add_eq_of_add_lt (by change i+1<59; exact hi)

/-- Two adjacent coordinates determine every actual modular kernel vector. -/
theorem cycle_kernel_unique_of_first_two (x : Site → F353)
    (hx : cycleGram F353 *ᵥ x=0) (h0 : x 0=0) (h1 : x 1=0) : x=0 := by
  have hsum := cycle_kernel_sum x hx
  have hh (i : ℕ) (hi : i<59) : x ⟨i,hi⟩=0 := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      cases i with
      | zero => exact h0
      | succ n =>
        cases n with
        | zero => exact h1
        | succ j =>
          let q : Site := ⟨j+1,by omega⟩
          have hqnext : q+1=⟨j+2,hi⟩ := succ_cast (j+1) hi
          have hqprev : q-1=⟨j,by omega⟩ := sub_eq_iff_eq_add.mpr (succ_cast j (by omega)).symm
          have he := congrFun hx q
          rw [cycleGram_action,hsum,add_zero,hqnext,hqprev] at he
          have hq0 : x q=0 := ih (j+1) (by omega) (by omega)
          rw [hq0,ih j (by omega) (by omega),mul_zero,sub_zero,zero_sub,Pi.zero_apply,
            neg_eq_zero] at he
          exact he
  funext i
  exact hh i.val i.isLt

theorem k1_0 : reduceVec 353 k1 0=(-1:F353) := by decide
theorem k1_1 : reduceVec 353 k1 1=(-7:F353) := by decide
theorem k2_0 : reduceVec 353 k2 0=(7:F353) := by decide
theorem k2_1 : reduceVec 353 k2 1=(48:F353) := by decide

/-- This spans the entire kernel, not just a checked pair of zero vectors. -/
theorem cycle_kernel_span (x : Site → F353) (hx : cycleGram F353 *ᵥ x=0) :
    ∃ a b : F353, x=a • reduceVec 353 k1+b • reduceVec 353 k2 := by
  let a := 48*x 0-7*x 1
  let b := 7*x 0-x 1
  refine ⟨a,b,sub_eq_zero.mp (cycle_kernel_unique_of_first_two _ ?_ ?_ ?_)⟩
  · rw [Matrix.mulVec_sub,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hx,
      k1_kernel,k2_kernel,smul_zero,smul_zero,add_zero,sub_zero]
  · change x 0-(a*reduceVec 353 k1 0+b*reduceVec 353 k2 0)=0
    rw [k1_0,k2_0]
    dsimp [a,b]
    ring
  · change x 1-(a*reduceVec 353 k1 1+b*reduceVec 353 k2 1)=0
    rw [k1_1,k2_1]
    dsimp [a,b]
    ring

/-- The actual modular kernel is linearly isomorphic to its first two coordinates. -/
noncomputable def cycle_kernel_coordinates :
    (cycleGram F353).mulVecLin.ker ≃ₗ[F353] F353×F353 := by
  let W := (cycleGram F353).mulVecLin.ker
  let f : W →ₗ[F353] (F353×F353) :=
    {toFun := fun x => (x.val 0,x.val 1),map_add' := fun _ _ => rfl,map_smul' := fun _ _ => rfl}
  refine LinearEquiv.ofBijective f ⟨?_,?_⟩
  · intro x y he
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply cycle_kernel_unique_of_first_two
    · change cycleGram F353 *ᵥ (x.val-y.val)=0
      have hx : cycleGram F353 *ᵥ x.val=0 := x.property
      have hy : cycleGram F353 *ᵥ y.val=0 := y.property
      rw [Matrix.mulVec_sub,hx,hy,sub_zero]
    · exact sub_eq_zero.mpr (congrArg Prod.fst he)
    · exact sub_eq_zero.mpr (congrArg Prod.snd he)
  · rintro ⟨c,d⟩
    let a := 48*c-7*d
    let b := 7*c-d
    refine ⟨⟨a • reduceVec 353 k1+b • reduceVec 353 k2,?_⟩,?_⟩
    · change cycleGram F353 *ᵥ (a • reduceVec 353 k1+b • reduceVec 353 k2)=0
      rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,k1_kernel,k2_kernel,
        smul_zero,smul_zero,add_zero]
    · apply Prod.ext
      · change a*reduceVec 353 k1 0+b*reduceVec 353 k2 0=c
        rw [k1_0,k2_0]
        dsimp [a,b]
        ring
      · change a*reduceVec 353 k1 1+b*reduceVec 353 k2 1=d
        rw [k1_1,k2_1]
        dsimp [a,b]
        ring

/-- The exact field rank of the original integer Gram after reduction. -/
theorem cycle_gram_rank_353 : (reduceMatrix 353 cycleGram59).rank=57 := by
  rw [cycleGram59_reduce]
  have hk : Module.finrank F353 (cycleGram F353).mulVecLin.ker=2 := by
    rw [cycle_kernel_coordinates.finrank_eq,Module.finrank_prod,Module.finrank_self]
  have hn := ((cycleGram F353).mulVecLin).finrank_range_add_finrank_ker
  rw [hk,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hn
  change (cycleGram F353).rank+2=59 at hn
  omega

set_option maxRecDepth 30000 in
theorem nonsquare_170 : ∀ x : F353, x*x≠170 := by decide +kernel

private theorem aniso_small (a b : F353)
    (h : a*a*69+a*b*288+b*a*288+b*b*69=0) : a=0 ∧ b=0 := by
  by_cases hb : b=0
  · refine ⟨?_,hb⟩
    simp only [hb,mul_zero,zero_mul,add_zero] at h
    rcases mul_eq_zero.mp h with hh|hh
    · exact (mul_eq_zero.mp hh).elim id id
    · exact ((by decide : (69:F353)≠0) hh).elim
  exfalso
  have hdisc : (288:F353)^2-69^2=170 := by decide
  have he : (69*a+288*b)*(69*a+288*b)=170*(b*b) := by
    linear_combination 69*h + (b*b)*hdisc
  apply nonsquare_170 ((69*a+288*b)/b)
  rw [← mul_div_mul_comm,he,mul_div_cancel_right₀ _ (mul_ne_zero hb hb)]

/-- The exact wrapped single 59-cycle Gram matrix has no square integral
realization, even without incidence/Boolean constraints on the factor. -/
theorem cycle59_no_integral_gram : ¬∃ A : Matrix Site Site ℤ, cycleGram59=A*Aᵀ := by
  apply no_integral_gram_of_anisotropic_pair 353 cycleGram59 k1 k2
    336478 325401 325401 336478
  · refine ⟨reduceVec 353 k1,?_ ,?_⟩
    · intro h
      have hh := congrFun h 0
      rw [k1_0] at hh
      exact (by decide : (-1:F353)≠0) hh
    · rw [cycleGram59_reduce]
      exact k1_kernel
  · rw [cycleGram59_reduce]
    exact cycle_kernel_span
  · exact k11_pair
  · exact k12_pair
  · exact k21_pair
  · exact k22_pair
  · intro a b h
    have h1 : ((336478:ℤ):F353)=69 := by decide
    have h2 : ((325401:ℤ):F353)=288 := by decide
    rw [h1,h2] at h
    exact aniso_small a b h

end Symconf59
