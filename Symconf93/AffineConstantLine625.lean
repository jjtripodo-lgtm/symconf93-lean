module
public import Symconf93.AffineSplit625

@[expose] public section

namespace Symconf93.AffineFiber625
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- The exact constant line after adding J, before the /25 reduction. -/
def lineNorm (s : ZMod 25) : ZMod 625 := (9300 : ZMod 625)*(lowCast s)^2

def lineNatCount (z t : ZMod 625) : ℕ :=
  (Finset.univ.filter (fun s : ZMod 25 => z+lineNorm s=t)).card

theorem line_contrast_exact : ∀ z : ZMod 625,
    (lineNatCount z 0:ℤ) - (lineNatCount z 125:ℤ) =
      5*((if z=0 then (1:ℤ) else 0)-(if z=125 then (1:ℤ) else 0)) := by
  decide +kernel

private theorem card_line_fiber {α : Type*} [Fintype α] (q : α → ZMod 625) (t : ZMod 625) :
    Nat.card {p : α×ZMod 25 // q p.1+lineNorm p.2=t} = ∑ a, lineNatCount (q a) t := by
  classical
  let e : {p : α×ZMod 25 // q p.1+lineNorm p.2=t} ≃ Σ a : α, {s : ZMod 25 // q a+lineNorm s=t} :=
    { toFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      invFun := fun p=> ⟨(p.1,p.2.val),p.2.property⟩
      left_inv := by rintro ⟨⟨a,s⟩,h⟩;rfl
      right_inv := by rintro ⟨a,⟨s,h⟩⟩;rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [lineNatCount,Fintype.card_subtype]

private theorem count_indicator {α : Type*} [Fintype α] (q : α → ZMod 625) (t : ZMod 625) :
    (∑ a,if q a=t then (1:ℤ) else 0) = (Nat.card {a // q a=t}:ℤ) := by
  classical
  rw [←Finset.sum_filter]
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem rankOne_constant_line_contrast {α : Type*} [Fintype α] (q : α → ZMod 625) :
    (Nat.card {p : α×ZMod 25 // q p.1+lineNorm p.2=0}:ℤ) -
      (Nat.card {p : α×ZMod 25 // q p.1+lineNorm p.2=125}:ℤ) =
    5*((Nat.card {a // q a=0}:ℤ) - (Nat.card {a // q a=125}:ℤ)) := by
  rw [card_line_fiber,card_line_fiber]
  push_cast
  rw [←Finset.sum_sub_distrib]
  simp_rw [line_contrast_exact]
  rw [←Finset.mul_sum,Finset.sum_sub_distrib,count_indicator,count_indicator]

#print axioms line_contrast_exact
#print axioms rankOne_constant_line_contrast
end Symconf93.AffineFiber625
