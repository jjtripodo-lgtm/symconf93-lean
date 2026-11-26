module
public import Symconf93.Terminal93
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section

/-! A scaled integral inverse of the literal order-93 profile Gram is
certified with short integer rows, one per cycle length, not dense
matrix multiplication. -/
namespace Symconf93
open Matrix Symconf59
open scoped BigOperators Matrix

/-- At center offset zero the cleared cyclic resolvent has source 700c;
its row sum is 100c. All entries here are actual integers. -/
structure CyclicInverse93 (P : List ℕ) where
  c : ℤ
  row : (i : Fin P.length) → Fin (P.get i) → ℤ
  totalSites : Fintype.card (BlocksOf P) = 93
  rowSum : ∀ i, (∑ j, row i j) = 100*c
  step : ∀ i (j : Fin (P.get i)), 9*row i j - row i (cprev j) - row i (cnext j) =
    if j.val=0 then 700*c else 0

def CyclicInverse93.clearEntry {P : List ℕ} (C : CyclicInverse93 P)
    (x y : BlocksOf P) : ℤ :=
  if h : y.1=x.1 then C.row x.1 ((h ▸ y.2) - x.2) else 0

def CyclicInverse93.clearedMatrix {P : List ℕ} (C : CyclicInverse93 P) :
    Matrix (BlocksOf P) (BlocksOf P) ℤ :=
  fun x y => C.clearEntry x y - C.c

private def blockPrev {P : List ℕ} (w : BlocksOf P) : BlocksOf P :=
  ⟨w.1,cprev w.2⟩

private def blockNext {P : List ℕ} (w : BlocksOf P) : BlocksOf P :=
  ⟨w.1,cnext w.2⟩

private theorem prev_next {P : List ℕ} (w : BlocksOf P) : blockPrev (blockNext w)=w := by
  rcases w with ⟨i,x⟩
  letI : NeZero (P.get i) := ⟨x.pos.ne'⟩
  simp [blockPrev,blockNext,cprev,cnext]
  exact add_sub_cancel_right x 1

private theorem next_prev {P : List ℕ} (w : BlocksOf P) : blockNext (blockPrev w)=w := by
  rcases w with ⟨i,x⟩
  letI : NeZero (P.get i) := ⟨x.pos.ne'⟩
  simp [blockPrev,blockNext,cprev,cnext]
  exact sub_add_cancel x 1

private theorem adj_flip {P : List ℕ} (w z : BlocksOf P) :
    profileAdj93 P w z = ((if w=blockPrev z then 1 else 0):ℤ)+
      (if w=blockNext z then 1 else 0) := by
  have hn : z=blockNext w ↔ w=blockPrev z :=
    ⟨fun h => by rw [h,prev_next],fun h => by rw [h,next_prev]⟩
  have hp : z=blockPrev w ↔ w=blockNext z :=
    ⟨fun h => by rw [h,next_prev],fun h => by rw [h,prev_next]⟩
  change (if z=blockNext w then 1 else 0)+(if z=blockPrev w then 1 else 0)=_
  simp only [hn,hp]

private theorem clear_sum {P : List ℕ} (C : CyclicInverse93 P) (x : BlocksOf P) :
    (∑ y, C.clearEntry x y)=100*C.c := by
  rcases x with ⟨i,x⟩
  letI : NeZero (P.get i) := ⟨x.pos.ne'⟩
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [CyclicInverse93.clearEntry,dif_pos]
    exact (Equiv.sum_comp (Equiv.subRight x) (C.row i)).trans (C.rowSum i)
  · intro j _ hj
    simp [CyclicInverse93.clearEntry,hj]
  · simp

private theorem clear_matrix_sum {P : List ℕ} (C : CyclicInverse93 P) (x : BlocksOf P) :
    (∑ y, C.clearedMatrix x y)=7*C.c := by
  simp only [CyclicInverse93.clearedMatrix,Finset.sum_sub_distrib,clear_sum,Finset.sum_const,
    Finset.card_univ,C.totalSites,nsmul_eq_mul]
  ring

private theorem clear_step {P : List ℕ} (C : CyclicInverse93 P) (x z : BlocksOf P) :
    9*C.clearEntry x z - C.clearEntry x (blockPrev z) - C.clearEntry x (blockNext z) =
      if x=z then 700*C.c else 0 := by
  obtain ⟨i,x⟩ := x
  obtain ⟨j,z⟩ := z
  by_cases h : j=i
  · subst j
    letI : NeZero (P.get i) := ⟨x.pos.ne'⟩
    change 9 * C.clearEntry ⟨i,x⟩ ⟨i,z⟩ -
      C.clearEntry ⟨i,x⟩ ⟨i,cprev z⟩ - C.clearEntry ⟨i,x⟩ ⟨i,cnext z⟩ = _
    simp only [CyclicInverse93.clearEntry,dif_pos,
      Sigma.mk.injEq,heq_eq_eq,true_and]
    have hp : cprev z-x = cprev (z-x) := by unfold cprev; abel
    have hn : cnext z-x = cnext (z-x) := by unfold cnext; abel
    rw [hp,hn,C.step]
    have he : (z-x).val=0 ↔ x=z := by
      have : (z-x).val=0 ↔ z-x=(0:Fin (P.get i)) := by rw [Fin.ext_iff]; simp
      rw [this,sub_eq_zero,eq_comm]
    simp [he]
  · have hh : (⟨i,x⟩ : BlocksOf P) ≠ ⟨j,z⟩ := by
      intro hz
      exact h (congrArg Sigma.fst hz).symm
    simp [CyclicInverse93.clearEntry,blockPrev,blockNext,h,hh]

private theorem profile_product_formula {P : List ℕ}
    (B : Matrix (BlocksOf P) (BlocksOf P) ℤ) (x z : BlocksOf P) :
    (B*profileGram93 P) x z =
      9*B x z+(∑ y,B x y)-B x (blockPrev z)-B x (blockNext z) := by
  rw [Matrix.mul_apply]
  simp only [profileGram93,adj_flip,mul_sub,mul_add,mul_ite,mul_one,mul_zero,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

theorem CyclicInverse93.scaled_inverse {P : List ℕ} (C : CyclicInverse93 P) :
    C.clearedMatrix * profileGram93 P=(700*C.c) • (1:Matrix (BlocksOf P) (BlocksOf P) ℤ) := by
  ext x z
  rw [profile_product_formula,clear_matrix_sum]
  have h := clear_step C x z
  simp only [CyclicInverse93.clearedMatrix,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  split_ifs at h ⊢ <;> linarith

end Symconf93

#print axioms Symconf93.CyclicInverse93.scaled_inverse
