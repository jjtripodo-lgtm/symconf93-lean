module
public import Symconf93.DoubleCounts
public import Symconf93.ProfileDefinitions

@[expose] public section

/-! Physical block charts imply every arithmetic premise, including
period bounds from two distinct actual row sites. -/
namespace Symconf93
open Matrix
open scoped BigOperators Matrix

abbrev BlocksOf (P : List ℕ) := Σ i : Fin P.length, Fin (P.get i)

/-- Genuine coordinates of both literal original site sets. Only the
existence of these ordered cyclic/constant-sum coordinates remains for
the original geometric construction; moments are not assumed. -/
structure PhysicalBlocks (A : Int93) (P : List ℕ) where
  rows : BlocksOf P ≃ Site
  cols : BlocksOf P ≃ Site
  within : ∀ (i : Fin P.length) (x : Fin (P.get i)),
    (∑ y : Fin (P.get i), rowLeave A (rows ⟨i,x⟩) (rows ⟨i,y⟩))=2
  across : ∀ (i j : Fin P.length), i≠j → ∀ x y,
    rowLeave A (rows ⟨i,x⟩) (rows ⟨j,y⟩)=0
  u : Fin P.length → Fin P.length → ℕ
  v : Fin P.length → Fin P.length → ℕ
  rowCount : ∀ (i j : Fin P.length) (x : Fin (P.get i)),
    (∑ y : Fin (P.get j), A (rows ⟨i,x⟩) (cols ⟨j,y⟩))=(u i j:ℤ)
  colCount : ∀ (i j : Fin P.length) (y : Fin (P.get j)),
    (∑ x : Fin (P.get i), A (rows ⟨i,x⟩) (cols ⟨j,y⟩))=(v i j:ℤ)
  periods : ∀ (i : Fin P.length) (d : ℕ), 0<d → d<P.get i →
    ∃ x y : Fin (P.get i), x≠y ∧
      ∀ j : Fin P.length, Nat.gcd (P.get i) (P.get j)∣d →
        ∀ z : Fin (P.get j), A (rows ⟨i,x⟩) (cols ⟨j,z⟩)=A (rows ⟨i,y⟩) (cols ⟨j,z⟩)

theorem cols_sum {P : List ℕ} (e : BlocksOf P ≃ Site) (f : Site → ℤ) :
    (∑ j : Fin P.length,∑ y : Fin (P.get j),f (e ⟨j,y⟩))=∑y,f y := by
  exact (Fintype.sum_sigma (fun z : BlocksOf P => f (e z))).symm.trans (Equiv.sum_comp e f)

theorem product_sums {P : List ℕ} {A : Int93} (G : PhysicalBlocks A P)
    (i h : Fin P.length) :
    (∑ x : Fin (P.get i),∑ y : Fin (P.get h),
      (A*Aᵀ) (G.rows ⟨i,x⟩) (G.rows ⟨h,y⟩))=
      ∑ j : Fin P.length, (P.get j:ℤ)*(G.v i j:ℤ)*(G.v h j:ℤ) := by
  rw [gram_rectangle_col_products]
  let f (y : Site) := (∑x : Fin (P.get i),A (G.rows ⟨i,x⟩) y)*
    (∑ x : Fin (P.get h),A (G.rows ⟨h,x⟩) y)
  change (∑y,f y)=_
  rw [← cols_sum G.cols f]
  simp only [f,G.colCount,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_assoc]

theorem exact_block_total {P : List ℕ} {A : Int93} (G : PhysicalBlocks A P)
    (i j : Fin P.length) : P.get i*G.u i j=P.get j*G.v i j := by
  have hh : (∑ x : Fin (P.get i),∑ y : Fin (P.get j), A (G.rows ⟨i,x⟩) (G.cols ⟨j,y⟩))=
      ∑ y : Fin (P.get j),∑ x : Fin (P.get i), A (G.rows ⟨i,x⟩) (G.cols ⟨j,y⟩) :=
    Finset.sum_comm
  simp only [G.rowCount,G.colCount,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact_mod_cast hh

theorem exact_period_bound {P : List ℕ} {A : Int93} (G : PhysicalBlocks A P)
    (hA : Incidence93 A) (i : Fin P.length) (d : ℕ) (hd : 0<d) (hd' : d<P.get i) :
    (∑ j : Fin P.length,if Nat.gcd (P.get i) (P.get j)∣d then G.u i j else 0)≤1 := by
  obtain ⟨x,y,hxy,hper⟩ := G.periods i d hd hd'
  let r := G.rows ⟨i,x⟩
  let s := G.rows ⟨i,y⟩
  have hrs : r≠s := by
    intro hh
    have hs := G.rows.injective hh
    exact hxy (eq_of_heq (Sigma.mk.inj_iff.mp hs).2)
  have hE : (∑ j : Fin P.length,((if Nat.gcd (P.get i) (P.get j)∣d then G.u i j else 0:ℕ):ℤ))=
      ∑j : Fin P.length,∑ z : Fin (P.get j),
        if Nat.gcd (P.get i) (P.get j)∣d then A r (G.cols ⟨j,z⟩) else 0 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with he
    · exact (G.rowCount i j x).symm
    · simp
  have hL : (∑j : Fin P.length,∑ z : Fin (P.get j),
        if Nat.gcd (P.get i) (P.get j)∣d then A r (G.cols ⟨j,z⟩) else 0)≤
      ∑j : Fin P.length,∑ z : Fin (P.get j), A r (G.cols ⟨j,z⟩)*A s (G.cols ⟨j,z⟩) := by
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro z _
    split_ifs with hp
    · change A r (G.cols ⟨j,z⟩) ≤ A r (G.cols ⟨j,z⟩)*A s (G.cols ⟨j,z⟩)
      have hz : A r (G.cols ⟨j,z⟩)=A s (G.cols ⟨j,z⟩) := hper j hp z
      rw [← hz]
      rcases hA.binary r (G.cols ⟨j,z⟩) with h | h <;> simp [h]
    · apply mul_nonneg
      · rcases hA.binary r (G.cols ⟨j,z⟩) with h | h <;> omega
      · rcases hA.binary s (G.cols ⟨j,z⟩) with h | h <;> omega
  rw [cols_sum G.cols (fun y => A r y*A s y),← hE] at hL
  have hh := hL.trans (hA.overlap r s hrs)
  exact_mod_cast hh

/-- Construct the original arithmetic record from literal matrix blocks.
All required square and cross moments and every aggregated period bound
are derived here. -/
def physical_blocks_to_profile {P : List ℕ} {A : Int93} (hA : Incidence93 A)
    (G : PhysicalBlocks A P) (hS : P.sum=93) (hpos : ∀b∈P,3≤b)
    (hSorted : P.Pairwise (· ≥ ·)) : OriginalProfileFacts P := by
  have hLen (i : Fin P.length) : 0<P.get i :=
    lt_of_lt_of_le (by decide : 0<3) (hpos _ (List.get_mem P i))
  let row (i : Fin P.length) : ProfileRow P.get (P.get i) := by
    refine ⟨G.u i,G.v i,exact_block_total G i,?_ ,?_⟩
    · let x : Fin (P.get i) := ⟨0,hLen i⟩
      have hs := cols_sum G.cols (A (G.rows ⟨i,x⟩))
      rw [hA.rows] at hs
      simp only [G.rowCount] at hs
      have hu : (∑ j,G.u i j)=10 := by exact_mod_cast hs
      simp only [← exact_block_total G i,← Finset.mul_sum,hu,mul_comm]
    · have hg := (product_sums G i i).symm.trans
        (gram_inside_cycle A (fun x => G.rows ⟨i,x⟩)
          (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp (G.rows.injective h)).2) (G.within i))
      exact_mod_cast hg
  refine ⟨hS,hpos,hSorted,row,?_,?_,?_⟩
  · intro i j
    let y : Fin (P.get j) := ⟨0,hLen j⟩
    let q := G.cols ⟨j,y⟩
    have hn : (∑ x : Fin (P.get i),A (G.rows ⟨i,x⟩) q) ≤
         ∑ k : Fin P.length,∑ x : Fin (P.get k), A (G.rows ⟨k,x⟩) q := by
      apply Finset.single_le_sum _ (Finset.mem_univ i)
      intro k _
      apply Finset.sum_nonneg
      intro x _
      rcases hA.binary (G.rows ⟨k,x⟩) q with h|h <;> omega
    rw [cols_sum G.rows (fun x => A x q),hA.cols] at hn
    change (∑ x : Fin (P.get i),A (G.rows ⟨i,x⟩) (G.cols ⟨j,y⟩))≤10 at hn
    rw [G.colCount] at hn
    change G.v i j≤10
    exact_mod_cast hn
  · intro i d hd hd'
    exact exact_period_bound G hA i d hd hd'
  · intro i j hne
    have hsite (x : Fin (P.get i)) (y : Fin (P.get j)) :
        G.rows ⟨i,x⟩≠G.rows ⟨j,y⟩ := by
      intro h
      exact hne ((Sigma.mk.inj_iff.mp (G.rows.injective h)).1)
    have hg := (product_sums G i j).symm.trans
      (gram_cross_cycles A (fun x => G.rows ⟨i,x⟩) (fun y => G.rows ⟨j,y⟩) hsite
        (G.across i j hne))
    change (∑ k,P.get k*G.v i k*G.v j k)=P.get i*P.get j
    exact_mod_cast hg

end Symconf93
