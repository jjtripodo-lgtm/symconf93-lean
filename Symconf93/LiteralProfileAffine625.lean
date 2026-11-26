module
public import Symconf93.LocalCycleAction625
public import Symconf93.ModularProfiles93

@[expose] public section

/-! Actual original H=G−J low-digit contrast for all 23 literal mod-625 profiles. -/
namespace Symconf93.AffineCycle625
open AffineFiber625
open scoped BigOperators
set_option maxRecDepth 25000
set_option maxHeartbeats 5000000

private def indexLength (l : ℕ) : Fin 11 :=
  ((List.finRange 11).find? (fun j => lengths j == l)).getD 0

def localExponent625 (i : Fin 23) : ℕ :=
  (#[31,23,11,21,17,19,15,13,13,13,9,7,17,11,7,7,11,11,11,7,5,13,1] : Array ℕ)[i.val]!

private theorem literal_cycle_membership625 :
    ∀ (i : Fin 23) (b : Fin (ModCount625.profile i).length),
      lengths (indexLength ((ModCount625.profile i).get b))=(ModCount625.profile i).get b := by
  decide +kernel

private theorem literal_cycle_factor625 :
    ∀ i : Fin 23,
       (∏ b : Fin (ModCount625.profile i).length,
          cycleFactor625 (indexLength ((ModCount625.profile i).get b))) =
        -(5:ℤ)^localExponent625 i := by
  decide +kernel

theorem literalProfileCard625 :
    ∀ i : Fin 23, Fintype.card (BlocksOf (ModCount625.profile i))=93 := by
  decide +kernel

theorem literalProfileDiffAction625 (i : Fin 23) :
    DiffAction (125:ZMod 625) (profileKernelQuad (ModCount625.profile i))
      (-(5:ℤ)^localExponent625 i) := by
  let P := ModCount625.profile i
  let A (b : Fin P.length) := CycleKernel (P.get b)
  let Q (b : Fin P.length) : A b→ZMod 625 := stationaryCycleQuad (P.get b)
  let c (b : Fin P.length) := cycleFactor625 (indexLength (P.get b))
  have h (b : Fin P.length) : DiffAction (125:ZMod 625) (Q b) (c b) := by
    have H := localCycleAction625 (indexLength (P.get b))
    have e : lengths (indexLength (P.get b))=P.get b := literal_cycle_membership625 i b
    rw [e] at H
    exact H
  have hp := diffAction_pi (125:ZMod 625) A Q c h
  have H := diffAction_transport (125:ZMod 625) (profileKernelQuad P)
    (fun x : ∀ b,A b => ∑ b,Q b (x b)) (∏ b,c b) (profileKernel_blocks_equiv P)
    (profileKernelQuad_blocks P) hp
  have he : (∏ b,c b)=-(5:ℤ)^localExponent625 i := literal_cycle_factor625 i
  rw [he] at H
  exact H

private theorem sum_indicatorS {α : Type*} [Fintype α] (p : α→Prop) [DecidablePred p] :
    (∑ x : α, if p x then (1:ℤ) else 0) = (Nat.card {x : α // p x}:ℤ) := by
  rw [← Finset.sum_filter]
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype]

private def stat_fiber_equiv (P : List ℕ) (t : ZMod 625) :
    {x : ProfileKernel P // profileKernelQuad P x=t} ≃
      {x : BlocksOf P→ZMod 25 //
        derivative (profileM P) (fun i=>lowCast (x i))=0 ∧
          quad (profileM P) (fun i=>lowCast (x i))=t} where
  toFun x := ⟨x.val.val,x.val.property,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- All 23 literal H low-digit contrasts; the separate high-digit and rank-one
rules still supply 25^93 and the G/H factor of 5 respectively. -/
theorem literalProfileStationaryContrast625 (i : Fin 23) :
    let P := ModCount625.profile i
    (Nat.card {x : BlocksOf P→ZMod 25 //
      derivative (profileM P) (fun j=>lowCast (x j))=0 ∧
        quad (profileM P) (fun j=>lowCast (x j))=0}:ℤ)-
    (Nat.card {x : BlocksOf P→ZMod 25 //
      derivative (profileM P) (fun j=>lowCast (x j))=0 ∧
        quad (profileM P) (fun j=>lowCast (x j))=125}:ℤ) =
      -(5:ℤ)^localExponent625 i := by
  classical
  let P := ModCount625.profile i
  let f (t : ZMod 625) : ℤ := if t=0 then 1 else 0
  have h := literalProfileDiffAction625 i f 0
  have nz : (125:ZMod 625)≠0 := by decide +kernel
  simp only [f,zero_sub,neg_eq_zero,zero_add,sub_eq_zero,ite_true,ite_false,nz,sub_zero,mul_one] at h
  rw [Finset.sum_sub_distrib] at h
  simp_rw [eq_comm (a:=(125:ZMod 625))] at h
  rw [sum_indicatorS,sum_indicatorS,
    Nat.card_congr (stat_fiber_equiv P 0),
    Nat.card_congr (stat_fiber_equiv P 125)] at h
  exact h

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.literalProfileDiffAction625
#print axioms Symconf93.AffineCycle625.literalProfileStationaryContrast625

#print axioms Symconf93.AffineCycle625.literalProfileCard625
