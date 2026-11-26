module
public import Symconf93.CycleTransfer625

@[expose] public section

/-! Eleven original cycle lengths, verified from only two columns of
the transfer and a fixed 5-element residue computation. -/
namespace Symconf93.AffineCycle625
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def lengths (j : Fin 11) : ℕ :=
  (#[3,5,6,9,12,15,18,21,24,27,93] : Array ℕ)[j.val]!

def layers (j : Fin 11) : ℕ :=
  (#[1,0,1,1,1,2,1,1,1,1,1] : Array ℕ)[j.val]!

def normalized (j : Fin 11) : (ℤ×ℤ)×(ℤ×ℤ) :=
  let M := cols (lengths j)
  let q := (5:ℤ)^layers j
  (((M.1.1-1)/q, M.1.2/q), (M.2.1/q,(M.2.2-1)/q))

def inflated (q : ℤ) (M : (ℤ×ℤ)×(ℤ×ℤ)) : (ℤ×ℤ)×(ℤ×ℤ) :=
  ((1+q*M.1.1,q*M.1.2), (q*M.2.1,1+q*M.2.2))

def det2 {R : Type*} [Ring R] (M : (ℤ×ℤ)×(ℤ×ℤ)) : R :=
  (M.1.1:R)*(M.2.2:R)-(M.1.2:R)*(M.2.1:R)

theorem cols_normalized :
    ∀ j : Fin 11, cols (lengths j)=inflated (5^layers j) (normalized j) := by
  decide +kernel

theorem det_normalized25 :
    ∀ j : Fin 11, (det2 (normalized j):ZMod 25)^20=1 := by
  decide +kernel

private theorem scaled_act {R : Type*} [CommRing R]
    (q : R) (M : (ℤ×ℤ)×(ℤ×ℤ)) (u : R×R)
    (hD : IsUnit (det2 M : R)) :
    (q*(act M u).1=0 ∧ q*(act M u).2=0) ↔ (q*u.1=0 ∧ q*u.2=0) := by
  obtain ⟨w,hw⟩ := hD
  constructor
  · rintro ⟨h0,h1⟩
    have hd0 : (w:R)*(q*u.1)=0 := by
      rw [hw]
      unfold det2 at *
      unfold act at h0 h1
      linear_combination (M.2.2:R)*h0 - (M.2.1:R)*h1
    have hd1 : (w:R)*(q*u.2)=0 := by
      rw [hw]
      unfold det2 at *
      unfold act at h0 h1
      linear_combination (M.1.1:R)*h1 - (M.1.2:R)*h0
    constructor
    · exact (Units.mul_right_inj w).mp (hd0.trans (mul_zero _).symm)
    · exact (Units.mul_right_inj w).mp (hd1.trans (mul_zero _).symm)
  · rintro ⟨h0,h1⟩
    unfold act
    constructor
    · linear_combination (M.1.1:R)*h0+(M.2.1:R)*h1
    · linear_combination (M.1.2:R)*h0+(M.2.2:R)*h1

theorem fixed_seed625 (j : Fin 11) (u : ZMod 25×ZMod 25) :
    run (lengths j) u=u ↔
      (5:ZMod 25)^layers j*u.1=0 ∧ (5:ZMod 25)^layers j*u.2=0 := by
  let q : ZMod 25 := 5^(layers j)
  let M := normalized j
  have hD : IsUnit (det2 M : ZMod 25) := by
    have hh := det_normalized25 j
    change (det2 M:ZMod 25)^20=1 at hh
    refine isUnit_iff_exists_inv.mpr ⟨(det2 M : ZMod 25)^19,?_⟩
    rw [← pow_succ']
    exact hh
  have hR : run (lengths j) u=(u.1+q*(act M u).1,u.2+q*(act M u).2) := by
    rw [run_eq_act,cols_normalized]
    unfold M q inflated act
    push_cast
    exact Prod.ext (by ring) (by ring)
  rw [hR,Prod.ext_iff]
  change (u.1+q*(act M u).1=u.1 ∧ u.2+q*(act M u).2=u.2) ↔ _
  rw [← scaled_act q M u hD]
  constructor
  · intro h
    exact ⟨add_left_cancel (h.1.trans (add_zero _).symm),
           add_left_cancel (h.2.trans (add_zero _).symm)⟩
  · intro h
    rw [h.1,h.2,add_zero,add_zero]
    exact ⟨rfl,rfl⟩

theorem five_zero_iff : ∀ u : ZMod 25, (5:ZMod 25)*u=0 ↔ u.val%5=0 := by
  decide +kernel

theorem normalized_fifteen :
    normalized (5:Fin 11)=
    ((6906762568022,777133772816),(-777133772816,-87441387322)) := by
  decide +kernel

def binaryActive (m : ZMod 5) (u : ZMod 5×ZMod 5) : ZMod 5 :=
  2*m*(u.1^2+u.2^2+(u.1+u.2)^2)

theorem binaryActive_count :
    ∀ (m t : ZMod 5), m≠0 →
      (Finset.univ.filter fun u : ZMod 5×ZMod 5 => binaryActive m u=t).card =
        if t=0 then 1 else 6 := by
  decide +kernel

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.fixed_seed625
#print axioms Symconf93.AffineCycle625.normalized_fifteen
#print axioms Symconf93.AffineCycle625.binaryActive_count
