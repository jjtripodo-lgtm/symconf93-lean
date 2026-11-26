module
public import Symconf93.CycleReducedForms625

@[expose] public section

/-! Reduce the only q=25 cycle (length 15) to an actual two-coordinate
diagonal frequency table. This does not pivot the profile. -/
namespace Symconf93.AffineCycle625
set_option maxRecDepth 40000
set_option maxHeartbeats 6000000

def seed15Equiv : ZMod 25×ZMod 25 ≃ ZMod 25×ZMod 25 where
  toFun u := (3*(u.1+8*u.2),2*u.2)
  invFun u := (17*u.1-8*(13*u.2),13*u.2)
  left_inv u := by
    have hz : (25:ZMod 25)=0 := by decide +kernel
    apply Prod.ext
    · change 17*(3*(u.1+8*u.2))-8*(13*(2*u.2))=u.1
      linear_combination (2*u.1+8*u.2)*hz
    · change 13*(2*u.2)=u.2
      linear_combination u.2*hz
  right_inv u := by
    have hz : (25:ZMod 25)=0 := by decide +kernel
    apply Prod.ext
    · change 3*((17*u.1-8*(13*u.2))+8*(13*u.2))=u.1
      linear_combination 2*u.1*hz
    · change 2*(13*u.2)=u.2
      linear_combination u.2*hz

def binary15 (u : ZMod 25×ZMod 25) : ZMod 25 := u.1^2+2*u.2^2

theorem phase_fifteen_as_diag (u : ZMod 25×ZMod 25) :
    phase (normalized (5:Fin 11)) u=binary15 (seed15Equiv u) := by
  rw [normalized_fifteen]
  unfold phase act binary15
  change
    u.2*(((6906762568022:ℤ):ZMod 25)*u.1+((-777133772816:ℤ):ZMod 25)*u.2)-
    u.1*(((777133772816:ℤ):ZMod 25)*u.1+((-87441387322:ℤ):ZMod 25)*u.2)=
    (3*(u.1+8*u.2))^2+2*(2*u.2)^2
  rw [show ((6906762568022:ℤ):ZMod 25)=22 by decide +kernel,
      show ((-777133772816:ℤ):ZMod 25)=9 by decide +kernel,
      show ((777133772816:ℤ):ZMod 25)=16 by decide +kernel,
      show ((-87441387322:ℤ):ZMod 25)=3 by decide +kernel]
  have hz : (25:ZMod 25)=0 := by decide +kernel
  linear_combination -(u.1^2+5*u.1*u.2+23*u.2^2)*hz

def binary15Count (t : ZMod 25) : ℕ :=
  (Finset.univ.filter fun u : ZMod 25×ZMod 25 => binary15 u=t).card

def binary15Expected (t : ZMod 25) : ℕ :=
  if t=0 then 25 else if t.val%5=0 then 0 else 30

theorem binary15_histogram : ∀ t : ZMod 25, binary15Count t=binary15Expected t := by
  decide +kernel

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.phase_fifteen_as_diag
#print axioms Symconf93.AffineCycle625.binary15_histogram
