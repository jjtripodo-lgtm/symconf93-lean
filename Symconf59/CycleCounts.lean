module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! Exact inversion of fixed-vertex divisor counts and component matching. -/
namespace Symconf59
open scoped BigOperators

def divisorScore (cnt : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (n+1), if d∣n then d*cnt d else 0

/-- Finite triangular inversion, not an appeal to spectral equivalence. -/
theorem divisorScore_injective_off_zero (f g : ℕ → ℕ)
    (h : ∀n,0<n → divisorScore f n=divisorScore g n) :
    ∀n,0<n → f n=g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hbase : (∑ d ∈ Finset.range n, if d∣n then d*f d else 0) =
        ∑ d ∈ Finset.range n, if d∣n then d*g d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hzero : d=0
      · subst d
        simp
      · have hw := ih d (Finset.mem_range.mp hd) (Nat.pos_of_ne_zero hzero)
        rw [hw]
    have he := h n hn
    unfold divisorScore at he
    rw [Finset.sum_range_succ,Finset.sum_range_succ,hbase,if_pos (dvd_refl n),
      if_pos (dvd_refl n)] at he
    exact Nat.eq_of_mul_eq_mul_left hn (Nat.add_left_cancel he)

section Components
variable {C D : Type*} [Fintype C] [Fintype D]

def lengthCount (L : C → ℕ) (n : ℕ) : ℕ := (Finset.univ.filter (fun c => L c=n)).card

/-- The cumulative fixed-point signal of a disjoint cycle family is its
length multiplicity divisor score. -/
theorem cycle_weighted_divisor_score (L : C → ℕ) (n : ℕ) (hn : 0<n) :
    divisorScore (lengthCount L) n = ∑ c, if L c∣n then L c else 0 := by
  classical
  unfold divisorScore
  calc
    _ = ∑ d ∈ Finset.range (n+1), ∑ c : C, if L c=d ∧ d∣n then d else 0 := by
      refine Finset.sum_congr rfl (fun d _ => ?_)
      by_cases hdiv : d∣n
      · simp only [hdiv,if_true,and_true,lengthCount,← Finset.sum_filter,Finset.sum_const,
          smul_eq_mul,mul_comm]
      · simp [hdiv]
    _ = ∑ c : C, ∑ d ∈ Finset.range (n+1), if L c=d ∧ d∣n then d else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      by_cases hd : L c∣n
      · have hle : L c≤n := Nat.le_of_dvd hn hd
        have hMem : L c∈Finset.range (n+1) := Finset.mem_range.mpr (by omega)
        have he (d : ℕ) : (if L c=d ∧ d∣n then d else 0)=(if d=L c then L c else 0) := by
          by_cases h : d=L c
          · subst d
            simp [hd]
          · simp [h,Ne.symm h]
        simp only [he,if_pos hd, Finset.sum_ite_eq',hMem,if_true]
      · rw [if_neg hd]
        apply Finset.sum_eq_zero
        intro d _
        apply if_neg
        rintro ⟨he,h⟩
        exact hd (he.symm ▸ h)

private def unfoldFibers (L : C → ℕ) : (Σ n : ℕ, {c : C // L c=n}) ≃ C where
  toFun p := p.2.val
  invFun c := ⟨L c,⟨c,rfl⟩⟩
  left_inv := by
    rintro ⟨n,⟨c,rfl⟩⟩
    rfl
  right_inv := fun _ => rfl

/-- Equal cycle length multiplicities give a bijection of the actual
component index sets preserving every length, not just a multiset equality. -/
theorem match_cycle_lengths (L : C → ℕ) (M : D → ℕ)
    (h : ∀n,lengthCount L n=lengthCount M n) :
    ∃ e : C≃D,∀ c,M (e c)=L c := by
  classical
  let f (n : ℕ) : {c : C // L c=n} ≃ {d : D // M d=n} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype,lengthCount] using h n)
  let e := (unfoldFibers L).symm.trans ((Equiv.sigmaCongrRight f).trans (unfoldFibers M))
  refine ⟨e,fun c => ?_⟩
  exact (f (L c) ⟨c,rfl⟩).property

end Components

end Symconf59
