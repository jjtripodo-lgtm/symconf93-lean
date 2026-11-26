module
public import Symconf93.Incidence
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-! Source-native exact double counts on unrestricted integer incidence. -/
namespace Symconf93
open Matrix
open scoped BigOperators Matrix

/-- The actual sum of Gram entries over two literal groups of rows is
the scalar product of their actual column-count profiles. -/
theorem gram_rectangle_col_products (A : Int93)
    {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Site) (s : Y → Site) :
    (∑ x, ∑ y, (A*Aᵀ) (r x) (s y)) =
      ∑ j, (∑ x,A (r x) j)*(∑ y,A (s y) j) := by
  simp only [row_gram_entry,Finset.sum_mul_sum]
  calc
    _ = ∑ x : X, ∑ j : Site, ∑ y : Y, A (r x) j*A (s y) j := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

/-- On a genuine leave component, precisely two neighbors are internal;
the diagonal part and all-ones part of the literal Gram give a(a+7). -/
theorem gram_inside_cycle (A : Int93) {n : ℕ} (r : Fin n → Site)
    (hr : Function.Injective r)
    (hR : ∀ x, (∑ y, rowLeave A (r x) (r y))=2) :
    (∑ x, ∑ y,(A*Aᵀ) (r x) (r y))=(n:ℤ)*((n:ℤ)+7) := by
  have hD (x : Fin n) : (∑ y,(A*Aᵀ) (r x) (r y))=(n:ℤ)+7 := by
    have hI : (∑ y : Fin n,(1:Int93) (r x) (r y))=1 := by
      simp [Matrix.one_apply,hr.eq_iff]
    have hJ : (∑ y : Fin n,allOnes (r x) (r y))=n := by
      simp [allOnes,Finset.sum_const]
    simp only [row_gram_eq,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hI,hJ,hR]
    omega
  simp only [hD,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Rows on different actual components meet in exactly one line. -/
theorem gram_cross_cycles (A : Int93) {a b : ℕ} (r : Fin a → Site) (s : Fin b → Site)
    (hn : ∀ x y,r x≠s y) (hR : ∀ x y,rowLeave A (r x) (s y)=0) :
    (∑ x,∑ y,(A*Aᵀ) (r x) (s y))=(a:ℤ)*(b:ℤ) := by
  have hh (x : Fin a) (y : Fin b) : (A*Aᵀ) (r x) (s y)=1 := by
    rw [row_gram_eq]
    change 9*(1:Int93) (r x) (s y)+allOnes (r x) (s y)-rowLeave A (r x) (s y)=1
    rw [Matrix.one_apply_ne (hn x y),hR]
    rfl
  simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

/-- A real selected common-support contribution is paid by an actual
positive row product. Even on other entries the product is nonnegative. -/
theorem binary_common_support_bound {A : Int93} (hA : Incidence93 A)
    (x y : Site) (hne : x≠y) (T : Finset Site)
    (he : ∀j∈T,A x j=A y j) : (∑ j∈T,A x j)≤1 := by
  have hm : (∑ j∈T,A x j)=(∑ j∈T,A x j*A y j) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← he j hj]
    rcases hA.binary x j with hh|hh <;> simp [hh]
  rw [hm]
  have hb : (∑ j∈T,A x j*A y j) ≤ ∑ j,A x j*A y j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    intro i _ _
    have hx : 0≤A x i := by rcases hA.binary x i with h|h <;> omega
    have hy : 0≤A y i := by rcases hA.binary y i with h|h <;> omega
    exact mul_nonneg hx hy
  exact hb.trans (hA.overlap x y hne)

end Symconf93
