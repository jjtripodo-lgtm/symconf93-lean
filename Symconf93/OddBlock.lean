module
public import Symconf59.CyclicBlock
public import Mathlib.Tactic.Ring

@[expose] public section

/-! A direct discrete-wave proof, no spectral splitting or real eigenvalues. -/
namespace Symconf93
open Symconf59

private theorem all_two_step {α : Type*} (h : ZMod 31 → α)
    (hs : ∀ a, h (a+2)=h a) : ∀ a,h a=h 0 := by
  intro a
  have hn (n : ℕ) (x : ZMod 31) : h (x+2*(n:ZMod 31))=h x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, mul_add, mul_one, ← add_assoc, hs, ih]
  have h₂ := hn (a*(16:ZMod 31)).val 0
  rw [zero_add, ZMod.natCast_zmod_val] at h₂
  have he : (2:ZMod 31)*(a*16)=a := by
    rw [mul_left_comm]
    rw [show (2:ZMod 31)*16=1 by decide, mul_one]
  rwa [he] at h₂

/-- In the actual cycle coordinates, a 0/1 block obeying
adjacency intertwining at length 31 must be circulant or reverse-circulant. -/
theorem binary31_block_orientation (f : ZMod 31 → ZMod 31 → ℤ)
    (hw : BlockWave f) (hb : ∀ i j, f i j=0 ∨ f i j=1) :
    (∃ g : ZMod 31 → ℤ, ∀ i j, f i j = g (j-i)) ∨
    (∃ g : ZMod 31 → ℤ, ∀ i j, f i j = g (j+i)) := by
  let g (u v : ZMod 31) := f (16*(u-v)) (16*(u+v))
  have zw (u v : ZMod 31) :
      g (u+2) v+g u (v+2)=g (u+2) (v+2)+g u v := by
    have hh := hw (16*(u-v)) (16*(u+v)+1)
    change f (16*(u-v)+1) (16*(u+v)+1)+f (16*(u-v)-1) (16*(u+v)+1) =
      f (16*(u-v)) (16*(u+v)+1+1)+f (16*(u-v)) (16*(u+v)+1-1) at hh
    have h32 : (16:ZMod 31)*2=1 := by decide
    change f (16*(u+2-v)) (16*(u+2+v))+
      f (16*(u-(v+2))) (16*(u+(v+2))) =
        f (16*(u+2-(v+2))) (16*(u+2+(v+2)))+f (16*(u-v)) (16*(u+v))
    have hv1 : 16*(u+2-v)=16*(u-v)+1 := by
      rw [show u+2-v=u-v+2 by ring,mul_add,h32]
    have hv2 : 16*(u-(v+2))=16*(u-v)-1 := by
      rw [show u-(v+2)=u-v-2 by ring,mul_sub,h32]
    have hv3 : 16*(u+2+v)=16*(u+v)+1 := by
      rw [show u+2+v=u+v+2 by ring,mul_add,h32]
    have hv4 : 16*(u+(v+2))=16*(u+v)+1 := by
      rw [show u+(v+2)=u+v+2 by ring,mul_add,h32]
    have hv5 : 16*(u+2-(v+2))=16*(u-v) := by ring
    have hv6 : 16*(u+2+(v+2))=16*(u+v)+1+1 := by
      rw [show u+2+(v+2)=u+v+2+2 by ring,mul_add,mul_add,h32]
    rw [hv1,hv2,hv3,hv4,hv5,hv6]
    simpa only [add_sub_cancel_right] using hh
  have eq1 (u v : ZMod 31) :
      g u (v+2)-g u v = g 0 (v+2)-g 0 v := by
    apply all_two_step (fun u => g u (v+2)-g u v) _ u
    intro t
    exact sub_eq_sub_iff_add_eq_add.mpr ((zw t v).symm.trans (add_comm _ _))
  have eq2 (u v : ZMod 31) :
      g u v - g 0 v = g u 0 - g 0 0 := by
    apply all_two_step (fun v => g u v - g 0 v) _ v
    intro t
    have hh := eq1 u t
    omega
  have gbin (u v : ZMod 31) : g u v=0 ∨ g u v=1 := hb _ _
  have back (i j : ZMod 31) : g (j+i) (j-i)=f i j := by
    have h32 : (16:ZMod 31)*2=1 := by decide
    have hi : 16*(j+i-(j-i))=i := by
      rw [show j+i-(j-i)=2*i by ring, ← mul_assoc,h32, one_mul]
    have hj : 16*(j+i+(j-i))=j := by
      rw [show j+i+(j-i)=2*j by ring, ← mul_assoc,h32, one_mul]
    simp only [g,hi,hj]
  by_cases hh : ∀ u : ZMod 31, g u 0=g 0 0
  · left
    refine ⟨g 0,fun i j => ?_⟩
    have hs := eq2 (j+i) (j-i)
    rw [hh, sub_self, sub_eq_zero,back] at hs
    exact hs
  · right
    push Not at hh
    obtain ⟨u,hu⟩ := hh
    refine ⟨fun z => g z 0,fun i j => ?_⟩
    have hv (v : ZMod 31) : g 0 v=g 0 0 := by
      have hh := eq2 u v
      rcases gbin u 0 with h0|h0 <;> rcases gbin 0 0 with h1|h1 <;>
        rcases gbin u v with he|he <;> rcases gbin 0 v with hf|hf <;> omega
    change f i j = g (j+i) 0
    have he := eq2 (j+i) (j-i)
    rw [hv,back] at he
    omega

end Symconf93

#print axioms Symconf93.binary31_block_orientation
