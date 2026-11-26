module
public import Symconf93.AffineSplit625

@[expose] public section

namespace Symconf93.AffineFiber625
open scoped BigOperators

private theorem card_pair_fibers {α β : Type*} [Fintype α] [Fintype β]
    (S : α → β → Prop) :
    Nat.card {p : α × β // S p.1 p.2} =
      ∑ a : α, Nat.card {b : β // S a b} := by
  classical
  let E : {p : α × β // S p.1 p.2} ≃ Σ a : α, {b : β // S a b} :=
    { toFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
      left_inv := by rintro ⟨⟨a,b⟩,h⟩; rfl
      right_inv := by rintro ⟨a,⟨b,h⟩⟩; rfl }
  rw [Nat.card_congr E]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]

private theorem card_constant {β : Type*} (p : Prop) [Decidable p] :
    Nat.card {_b : β // p} = if p then Nat.card β else 0 := by
  by_cases hp : p
  · rw [if_pos hp]
    exact Nat.card_congr
      { toFun := Subtype.val
        invFun := fun b => ⟨b,hp⟩
        left_inv := by intro b; rfl
        right_inv := by intro b; rfl }
  · haveI : IsEmpty {b : β // p} := ⟨fun b => hp b.property⟩
    simp [hp]

private theorem sum_indicator {α : Type*} [Fintype α] (Q : α → Prop) [DecidablePred Q] :
    (∑ a : α, if Q a then (1 : ℤ) else 0) = (Nat.card {a // Q a} : ℤ) := by
  classical
  rw [← Finset.sum_filter]
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- Count differences supported on the original low-digit stationary fibre.
All other low digits have explicit matched upper-digit fibres, even if a
nonzero derivative coefficient is not a unit modulo 25. -/
theorem affine_contrast_to_stationary {ι : Type*} [Fintype ι]
    (m : ι → ι → ZMod 625) (hm : ∀ i j, m i j = m j i) :
    (Nat.card {x : ι → ZMod 625 // quad m x = 0} : ℤ) -
      (Nat.card {x : ι → ZMod 625 // quad m x = 125} : ℤ) =
    (25 : ℤ) ^ Fintype.card ι *
      ((Nat.card {a : ι → ZMod 25 //
         derivative m (fun i => lowCast (a i)) = 0 ∧ quad m (fun i => lowCast (a i)) = 0} : ℤ) -
       (Nat.card {a : ι → ZMod 25 //
         derivative m (fun i => lowCast (a i)) = 0 ∧ quad m (fun i => lowCast (a i)) = 125} : ℤ)) := by
  classical
  let α := ι → ZMod 25
  let q (a : α) := quad m (fun i => lowCast (a i))
  let f (a : α) := derivative m (fun i => lowCast (a i))
  let cc (a : α) (t : ZMod 625) := Nat.card {b : α // linearFiberValue (q a) (f a) b = t}
  let n := Nat.card α
  have H (t : ZMod 625) :
      Nat.card {x : ι → ZMod 625 // quad m x = t} = ∑ a : α, cc a t := by
    have E := (pointwiseDigits (ι:=ι)).subtypeEquiv
      (p:=fun u => linearFiberValue (q u.1) (f u.1) u.2 = t)
      (q:=fun x => quad m x = t)
      (fun u => by rw [quadratic_digit_expansion m hm])
    rw [Nat.card_congr E.symm]
    exact card_pair_fibers (fun (a b : α) => linearFiberValue (q a) (f a) b = t)
  let pred (t : ZMod 625) (a : α) := f a = 0 ∧ q a = t
  have nz : (n : ℤ) = (25 : ℤ) ^ Fintype.card ι := by
    simp [n,α, Nat.card_eq_fintype_card,ZMod.card]
  have hconst (a : α) (ha : f a = 0) (t : ZMod 625) :
      cc a t = if q a = t then n else 0 := by
    have EqB (b : α) : linearFiberValue (q a) (f a) b = q a := by simp [linearFiberValue,ha,highLift]
    change Nat.card {b : α // linearFiberValue (q a) (f a) b = t} = _
    simp_rw [EqB]
    exact card_constant (β:=α) (q a = t)
  have hpoint (a : α) : (cc a 0 : ℤ) - (cc a 125 : ℤ) =
      (n : ℤ)*((if pred 0 a then (1:ℤ) else 0)-(if pred 125 a then (1:ℤ) else 0)) := by
    by_cases ha : f a = 0
    · rw [hconst a ha, hconst a ha]
      have ne125 : (0 : ZMod 625) ≠ 125 := by decide +kernel
      by_cases h0 : q a = 0 <;> by_cases h5 : q a = 125 <;> simp [pred,ha,h0,h5,ne125,Ne.symm ne125]
    · have e : cc a 0 = cc a 125 := nonzero_affine_fiber (q a) (f a) ha
      simp [e,pred,ha]
  rw [H,H]
  push_cast
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,sum_indicator,sum_indicator,nz]

#print axioms affine_contrast_to_stationary
end Symconf93.AffineFiber625
