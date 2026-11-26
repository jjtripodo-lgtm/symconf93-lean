module
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel

@[expose] public section

/-! The exact pre-spectral substitute for Fourier block periodicity. -/
namespace Symconf59

section Wave
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

private theorem double_shift (f : X → ℤ) (u x : X) (n : ℕ) :
    f (x+u+(n+1) • u)+f (x+u-(n+1) • u)+
    (f (x-u+(n+1) • u)+f (x-u-(n+1) • u)) =
      f (x+(n+2) • u)+f (x-(n+2) • u)+
      (f (x+n • u)+f (x-n • u)) := by
  have h0 : x+u+(n+1) • u=x+(n+2) • u := by
    rw [show n+2=n+1+1 by omega]
    simp only [add_nsmul,one_nsmul]
    abel
  have h1 : x+u-(n+1) • u=x-n • u := by
    simp only [add_nsmul,one_nsmul]
    abel
  have h2 : x-u+(n+1) • u=x+n • u := by
    simp only [add_nsmul,one_nsmul]
    abel
  have h3 : x-u-(n+1) • u=x-(n+2) • u := by
    rw [show n+2=n+1+1 by omega]
    simp only [add_nsmul,one_nsmul]
    abel
  rw [h0,h1,h2,h3]
  abel

/-- All nonbacktracking powers interchange, proved on the literal values,
with no Fourier transform, invertibility, or positivity hypothesis. -/
theorem wave_all_steps (f : X → Y → ℤ) (u : X) (v : Y)
    (h : ∀ x y, f (x+u) y+f (x-u) y=f x (y+v)+f x (y-v)) :
    ∀ (n : ℕ) x y, f (x+n • u) y+f (x-n • u) y=
      f x (y+n • v)+f x (y-n • v) := by
  let P : ℕ → Prop := fun n => ∀ x y, f (x+n • u) y+f (x-n • u) y=
    f x (y+n • v)+f x (y-n • v)
  have h0 : P 0 := by intro x y; simp
  have h1 : P 1 := by intro x y; simpa only [one_nsmul] using h x y
  have hnext : ∀ n, P n → P (n+1) → P (n+2) := by
    intro n hn hₙ x y
    have hx := double_shift (fun z => f z y) u x n
    have hy := double_shift (f x) v y n
    have hx₁ := hₙ (x+u) y
    have hx₂ := hₙ (x-u) y
    have hy₁ := h x (y+(n+1) • v)
    have hy₂ := h x (y-(n+1) • v)
    have hc := hn x y
    change f (x+(n+2) • u) y+f (x-(n+2) • u) y=
      f x (y+(n+2) • v)+f x (y-(n+2) • v)
    have h01 : y+(n+1) • v+v=y+v+(n+1) • v := by abel
    have h02 : y+(n+1) • v-v=y-v+(n+1) • v := by abel
    have h03 : y-(n+1) • v+v=y+v-(n+1) • v := by abel
    have h04 : y-(n+1) • v-v=y-v-(n+1) • v := by abel
    rw [h01,h02] at hy₁
    rw [h03,h04] at hy₂
    linear_combination -hx+hy+hx₁+hx₂+hy₁+hy₂-hc
  have hp (n : ℕ) : P n ∧ P (n+1) := by
    induction n with
    | zero => exact ⟨h0,h1⟩
    | succ n ih => exact ⟨ih.2,hnext n ih.1 ih.2⟩
  exact fun n => (hp n).1

/-- On a binary block, one full turn on the other side is an exact period.
The equality of the two neighboring samples is not inferred over ℚ or ℝ. -/
theorem wave_binary_period (f : X → Y → ℤ) (u : X) (v : Y)
    (h : ∀ x y, f (x+u) y+f (x-u) y=f x (y+v)+f x (y-v))
    (hb : ∀ x y, f x y=0 ∨ f x y=1) (n : ℕ) (hvn : n • v=0) :
    ∀ x y, f (x+n • u) y=f x y := by
  intro x y
  have hn := wave_all_steps f u v h n x y
  rw [hvn,add_zero,sub_zero] at hn
  rcases hb (x+n • u) y with h₁|h₁ <;>
    rcases hb (x-n • u) y with h₂|h₂ <;>
    rcases hb x y with h₃|h₃ <;> omega

omit [AddCommGroup Y] in
private theorem period_zmul (f : X → Y → ℤ) (u : X)
    (hp : ∀ x y, f (x+u) y=f x y) (a : ℤ) (x : X) (y : Y) :
    f (x+a • u) y=f x y := by
  have hN (n : ℕ) (z : X) : f (z+n • u) y=f z y := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul,← add_assoc,hp,ih]
  cases a with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,natCast_zsmul] using hN n x
  | negSucc n =>
    change f (x+(-((n+1:ℕ):ℤ)) • u) y=f x y
    rw [neg_zsmul,natCast_zsmul]
    have hh := hN (n+1) (x+-((n+1) • u))
    rw [add_assoc,neg_add_cancel,add_zero] at hh
    exact hh.symm

/-- The true period is the gcd of the two cycle lengths; Bézout is exact,
and the row's own full period is allowed to be nonminimal. -/
theorem wave_binary_gcd_period (f : X → Y → ℤ) (u : X) (v : Y)
    (h : ∀ x y, f (x+u) y+f (x-u) y=f x (y+v)+f x (y-v))
    (hb : ∀ x y, f x y=0 ∨ f x y=1) (a b : ℕ) (ha : a • u=0) (hb' : b • v=0) :
    ∀ (d : ℕ), Nat.gcd a b∣d → ∀ x y, f (x+d • u) y=f x y := by
  intro d hd x y
  have hp := wave_binary_period f u v h hb b hb'
  have hd₁ : (Nat.gcd a b) • u=Nat.gcdB a b • (b • u) := by
    rw [← natCast_zsmul, Nat.gcd_eq_gcd_ab, add_zsmul,
      mul_comm (a:ℤ),mul_comm (b:ℤ),mul_zsmul,mul_zsmul,natCast_zsmul,natCast_zsmul,
      ha,zsmul_zero,zero_add]
  obtain ⟨q,rfl⟩ := hd
  rw [mul_nsmul,hd₁,← natCast_zsmul,← mul_zsmul]
  exact period_zmul f (b • u) hp ((q:ℤ)*Nat.gcdB a b) x y

/-- An integral harmonic function on a finite cycle is constant along it.
The exact full-turn period forces its linear discrete drift to vanish. -/
theorem finite_cycle_harmonic (g : X → ℤ) (u : X) (m : ℕ) (hm : 0<m)
    (hper : m • u=0) (h : ∀ x, g (x+u)+g (x-u)=2*g x) :
    ∀ (x : X) (q : ℕ), g (x+q • u)=g x := by
  intro x q
  let z := fun n : ℕ => g (x+n • u)
  let d := g (x+u)-g x
  have hRec (n : ℕ) : z (n+2)+z n=2*z (n+1) := by
    have he : x+(n+1) • u+u=x+(n+2) • u := by
      rw [show n+2=n+1+1 by omega]
      simp only [add_nsmul,one_nsmul,add_assoc]
    have hf : x+(n+1) • u-u=x+n • u := by
      rw [add_nsmul,one_nsmul,← add_assoc,add_sub_cancel_right]
    have hh := h (x+(n+1) • u)
    rwa [he,hf] at hh
  have hLin (n : ℕ) : z n=g x+(n:ℤ)*d ∧ z (n+1)=g x+((n+1:ℕ):ℤ)*d := by
    induction n with
    | zero =>
      refine ⟨by simp [z],?_⟩
      simp [z,d]
    | succ n ih =>
      refine ⟨ih.2,?_⟩
      have hh := hRec n
      change z (n+2)=g x+((n+2:ℕ):ℤ)*d
      simp only [Nat.cast_add,Nat.cast_one, Nat.cast_ofNat] at *
      linear_combination hh-ih.1+2*ih.2
  have hh := (hLin m).1
  change g (x+m • u)=g x+(m:ℤ)*d at hh
  rw [hper,add_zero] at hh
  have hs : (m:ℤ)*d=0 := by omega
  have hne : (m:ℤ)≠0 := by exact_mod_cast Nat.ne_zero_of_lt hm
  have hd := (mul_eq_zero.mp hs).resolve_left hne
  change z q=g x
  rw [(hLin q).1,hd,mul_zero,add_zero]

end Wave
end Symconf59
