module
public import Symconf59.DiscreteWave
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Constant row and column sums and exact periods of a genuinely
intertwining cyclic rectangular binary block. -/
namespace Symconf59
open scoped BigOperators

section Blocks
variable {a b : ℕ} [NeZero a] [NeZero b]

def BlockWave (f : ZMod a → ZMod b → ℤ) : Prop :=
  ∀ x y, f (x+1) y+f (x-1) y=f x (y+1)+f x (y-1)

private theorem period_one_zmod (n : ℕ) :
    n • (1:ZMod n)=0 := by
  simpa only [nsmul_eq_mul,mul_one] using ZMod.natCast_self n

private theorem sum_shift_zmod {n : ℕ} [NeZero n] (g : ZMod n → ℤ) (t : ZMod n) :
    (∑ i,g (i+t))=∑i,g i := Equiv.sum_comp (Equiv.addRight t) g

/-- The harmonic invariant has no hidden spectral simplicity hypothesis. -/
theorem cyclic_block_rows_constant (f : ZMod a → ZMod b → ℤ) (h : BlockWave f) :
    ∀ x, (∑ j, f x j)=∑j, f 0 j := by
  let g : ZMod a → ℤ := fun x => ∑ j,f x j
  have hg (x : ZMod a) : g (x+1)+g (x-1)=2*g x := by
    change (∑j, f (x+1) j)+(∑j,f (x-1) j)=2*(∑j,f x j)
    rw [← Finset.sum_add_distrib]
    rw [show (∑ j, (f (x+1) j+f (x-1) j)) =
      ∑ j, (f x (j+1)+f x (j-1)) from Finset.sum_congr rfl (fun j _ => h x j)]
    rw [Finset.sum_add_distrib,sum_shift_zmod]
    have hs : (∑ j : ZMod b,f x (j-1))=∑j,f x j := by
      simpa only [sub_eq_add_neg] using sum_shift_zmod (f x) (-1)
    rw [hs,two_mul]
  intro x
  have hc := finite_cycle_harmonic g (1:ZMod a) a (NeZero.pos _) (period_one_zmod a) hg 0 x.val
  change g x=g 0
  simpa only [zero_add,nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val] using hc

theorem cyclic_block_cols_constant (f : ZMod a → ZMod b → ℤ) (h : BlockWave f) :
    ∀ y, (∑ i, f i y)=∑i, f i 0 := by
  exact cyclic_block_rows_constant (fun y x => f x y) (fun y x => (h x y).symm)

omit [NeZero a] [NeZero b] in
theorem cyclic_block_binary_gcd_period (f : ZMod a → ZMod b → ℤ)
    (h : BlockWave f) (hBin : ∀ x y,f x y=0 ∨ f x y=1) :
    ∀ d : ℕ, Nat.gcd a b∣d → ∀ x y, f (x+(d:ZMod a)) y=f x y := by
  intro d hd x y
  have hh := wave_binary_gcd_period f (1:ZMod a) (1:ZMod b) h hBin a b
    (period_one_zmod a) (period_one_zmod b) d hd x y
  simpa only [nsmul_eq_mul,mul_one] using hh

/-- The literal block's two sums count precisely the same incidences. -/
theorem cyclic_block_totals (f : ZMod a → ZMod b → ℤ) (h : BlockWave f) :
    (a:ℤ)*(∑ j,f 0 j)=(b:ℤ)*(∑ i,f i 0) := by
  calc
    _ = ∑ i : ZMod a, ∑ j : ZMod b,f i j := by
      simp only [cyclic_block_rows_constant f h,Finset.sum_const,Finset.card_univ,
        ZMod.card,nsmul_eq_mul]
    _ = ∑ j : ZMod b, ∑ i : ZMod a,f i j := Finset.sum_comm
    _ = _ := by
      simp only [cyclic_block_cols_constant f h,Finset.sum_const,Finset.card_univ,
        ZMod.card,nsmul_eq_mul]

end Blocks
end Symconf59
