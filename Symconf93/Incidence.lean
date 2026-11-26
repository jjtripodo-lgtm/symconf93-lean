module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! Literal integer incidence input and its two genuine leave matrices.
No automorphism or common cycle profile is a premise. -/
namespace Symconf93
set_option maxRecDepth 4000
open Matrix
open scoped Matrix BigOperators

abbrev Site := Fin 93

abbrev Int93 := Matrix Site Site ℤ

structure Incidence93 (A : Int93) : Prop where
  binary : ∀ i j, A i j=0 ∨ A i j=1
  rows : ∀ i, (∑ j, A i j)=10
  cols : ∀ j, (∑ i, A i j)=10
  overlap : ∀ i i', i≠i' → (∑ j,A i j*A i' j)≤1

private def common (f g : Site → ℤ) : Finset Site :=
  Finset.univ.filter (fun t => f t=1 ∧ g t=1)

private theorem product_eq_indicator (f g : Site → ℤ)
    (hf : ∀ t, f t=0 ∨ f t=1) (hg : ∀ t,g t=0 ∨ g t=1) (t : Site) :
    f t*g t=(if f t=1 ∧ g t=1 then 1 else 0 : ℤ) := by
  rcases hf t with h|h <;> rcases hg t with h'|h' <;> simp [h,h']

private theorem overlap_card (f g : Site → ℤ)
    (hf : ∀ t, f t=0 ∨ f t=1) (hg : ∀ t,g t=0 ∨ g t=1) :
    (∑ t,f t*g t)=((common f g).card:ℤ) := by
  simp only [product_eq_indicator f g hf hg, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one, common]

/-- Literal row-overlap excludes every actual 2×2 all-one submatrix. -/
theorem Incidence93.no_rectangle {A : Int93} (h : Incidence93 A)
    {i i' j j' : Site} (hi : i≠i') (hj : j≠j')
    (hij : A i j=1) (hij' : A i j'=1) (hi'j : A i' j=1) (hi'j' : A i' j'=1) : False := by
  have hsub : ({j,j'}:Finset Site) ⊆ common (A i) (A i') := by
    intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl
    · simp [common,hij,hi'j]
    · simp [common,hij',hi'j']
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simpa using hj),Finset.card_singleton] at hc
  have hb := h.overlap i i' hi
  rw [overlap_card _ _ (h.binary i) (h.binary i')] at hb
  omega

/-- The column-overlap condition follows from the given row-overlap
condition; it is not an extra incidence hypothesis. -/
theorem Incidence93.transpose {A : Int93} (h : Incidence93 A) : Incidence93 Aᵀ := by
  refine ⟨fun i j => h.binary j i,h.cols,h.rows,?_⟩
  intro j j' hj
  change (∑ i,A i j*A i j')≤1
  rw [overlap_card _ _ (fun i => h.binary i j) (fun i => h.binary i j')]
  by_contra hh
  have hc : 1 < (common (fun i => A i j) (fun i => A i j')).card := by omega
  obtain ⟨i,hi,i',hi',hne⟩ := Finset.one_lt_card.mp hc
  simp only [common,Finset.mem_filter,Finset.mem_univ,true_and] at hi hi'
  exact h.no_rectangle hne hj hi.1 hi.2 hi'.1 hi'.2

def allOnes : Int93 := fun _ _ => 1

def rowLeave (A : Int93) : Int93 := (9:ℤ) • (1 : Int93)+allOnes-A*Aᵀ

def colLeave (A : Int93) : Int93 := rowLeave Aᵀ

/-- Literal Gram identities on the row and column sets. -/
theorem row_gram_eq (A : Int93) : A*Aᵀ=(9:ℤ) • (1 : Int93)+allOnes-rowLeave A := by
  unfold rowLeave
  abel

theorem col_gram_eq (A : Int93) : Aᵀ*A=(9:ℤ) • (1 : Int93)+allOnes-colLeave A := by
  simpa only [colLeave,Matrix.transpose_transpose] using row_gram_eq Aᵀ

theorem row_gram_entry (A : Int93) (i j : Site) : (A*Aᵀ) i j=∑ q,A i q*A j q := rfl

theorem row_gram_diag {A : Int93} (h : Incidence93 A) (i : Site) : (A*Aᵀ) i i=10 := by
  calc
    _ = ∑ j, A i j := by
      rw [row_gram_entry]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rcases h.binary i j with h0|h1
      · simp [h0]
      · simp [h1]
    _ = 10 := h.rows i

theorem rowLeave_diag {A : Int93} (h : Incidence93 A) (i : Site) : rowLeave A i i=0 := by
  change 9 * (1 : Int93) i i+allOnes i i-(A*Aᵀ) i i=0
  rw [Matrix.one_apply_eq, row_gram_diag h]
  rfl

theorem rowLeave_offdiag {A : Int93} {i j : Site} (hij : i≠j) :
    rowLeave A i j=1-∑ q,A i q*A j q := by
  change 9 * (1 : Int93) i j+allOnes i j-(A*Aᵀ) i j=_
  rw [Matrix.one_apply_ne hij,mul_zero,zero_add,row_gram_entry]
  rfl

theorem rowLeave_binary {A : Int93} (h : Incidence93 A) (i j : Site) :
    rowLeave A i j=0 ∨ rowLeave A i j=1 := by
  by_cases he : i=j
  · subst j
    exact Or.inl (rowLeave_diag h i)
  rw [rowLeave_offdiag he]
  have hn : 0≤∑ q,A i q*A j q := by
    rw [overlap_card _ _ (h.binary i) (h.binary j)]
    exact_mod_cast Nat.zero_le _
  have ho := h.overlap i j he
  omega

theorem rowLeave_symm (A : Int93) : (rowLeave A)ᵀ=rowLeave A := by
  rw [rowLeave,Matrix.transpose_sub,Matrix.transpose_add,Matrix.transpose_smul,
    Matrix.transpose_one,Matrix.transpose_mul,Matrix.transpose_transpose]
  rfl

theorem row_gram_sum {A : Int93} (h : Incidence93 A) (i : Site) : (∑ j,(A*Aᵀ) i j)=100 := by
  simp only [row_gram_entry]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,h.cols]
  rw [← Finset.sum_mul,h.rows]
  norm_num

theorem rowLeave_sum {A : Int93} (h : Incidence93 A) (i : Site) : (∑ j,rowLeave A i j)=2 := by
  change (∑ j,(9 * (1 : Int93) i j+allOnes i j-(A*Aᵀ) i j))=2
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,row_gram_sum h]
  have hI : (∑ j,(1 : Int93) i j)=1 := by simp [Matrix.one_apply]
  have hJ : (∑ j,allOnes i j)=93 := by simp [allOnes,Finset.sum_const,Fintype.card_fin]
  rw [hI,hJ]
  norm_num

/-- The complete original leave conditions on both sides. -/
theorem binary_simple_two_regular_leave {A : Int93} (h : Incidence93 A) :
    (∀ i j, rowLeave A i j=0 ∨ rowLeave A i j=1) ∧
    (∀ i j, colLeave A i j=0 ∨ colLeave A i j=1) ∧
    (∀ i, rowLeave A i i=0 ∧ colLeave A i i=0) ∧
    (rowLeave A)ᵀ=rowLeave A ∧ (colLeave A)ᵀ=colLeave A ∧
    ∀ i, (∑ j,rowLeave A i j)=2 ∧ (∑ j,colLeave A i j)=2 :=
  ⟨rowLeave_binary h,rowLeave_binary h.transpose,fun i => ⟨rowLeave_diag h i,rowLeave_diag h.transpose i⟩,
    rowLeave_symm A,rowLeave_symm Aᵀ,fun i => ⟨rowLeave_sum h i,rowLeave_sum h.transpose i⟩⟩

/-- Associativity gives the exact original intertwining, without assuming
either invertibility or conjugacy of the two leave graphs. -/
theorem leave_intertwines {A : Int93} (h : Incidence93 A) :
    rowLeave A*A=A*colLeave A := by
  have hJ : allOnes*A=A*allOnes := by
    ext i j
    simp only [Matrix.mul_apply,allOnes,one_mul,mul_one,h.cols,h.rows]
  have hM : (A*Aᵀ)*A=A*(Aᵀ*A) := mul_assoc _ _ _
  unfold colLeave
  rw [rowLeave,rowLeave,Matrix.transpose_transpose,sub_mul,add_mul,mul_sub,mul_add,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one,hJ,hM]

end Symconf93
