module
public import Symconf93.PivotFreeCycleCount49
public import Symconf93.LiteralJoint49Case0
public import Symconf93.LiteralJoint49Case1
public import Symconf93.LiteralCyclicInverses93
public import Symconf93.GramCongruence93

@[expose] public section

/-! Terminal for the two actual source q49 profiles. Uses the original
integral scaled inverse only to relate an actual Gram factor to ambient
counts; the negative counts themselves are entirely pivot-free. -/
namespace Symconf93.AffineFiber49
open Symconf59 Matrix
open scoped Matrix

private theorem length_pos49 : ∀ i : Fin 2, 0<(ModCount49.profile i).length := by decide +kernel

private theorem cycles_unit49 : ∀ (i : Fin 2) (b : Fin (ModCount49.profile i).length),
    ((ModCount49.profile i).get b:ZMod 7)≠0 := by decide +kernel

private theorem coset_delta49 (i : Fin 2) :
    (jointCount (ModCount49.profile i) (0,0):ℤ)-jointCount (ModCount49.profile i) (0,1) =
      -(7:ℤ)^(if i=0 then 12 else 5) := by
  fin_cases i
  · change (jointCount (ModCount49.profile 0) (0,0):ℤ)-jointCount (ModCount49.profile 0) (0,1)=-(7:ℤ)^12
    rw [show ModCount49.profile 0=[5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] by decide +kernel]
    exact jointCount_case0_delta
  · change (jointCount (ModCount49.profile 1) (0,0):ℤ)-jointCount (ModCount49.profile 1) (0,1)=-(7:ℤ)^5
    rw [show ModCount49.profile 1=[15, 15, 15, 15, 15, 3, 3, 3, 3, 3, 3] by decide +kernel]
    exact jointCount_case1_delta

theorem literal_mod49_direct_contrast (i : Fin 2) :
    contrast (gramNorm (Symconf59.reduceMatrix 49 (profileGram93 (ModCount49.profile i)))) (7:ZMod 49) =
      -(7:ℤ)^(if i=0 then 105 else 98) := by
  rw [true_cycle_contrast49 (length_pos49 i) (cycles_unit49 i),coset_delta49,
      (ModCount49.actual_inverse i).totalSites]
  split_ifs <;> norm_num

theorem no_integral_gram49_without_pivots (i : Fin 2) :
    ¬∃ A : Matrix (BlocksOf (ModCount49.profile i)) (BlocksOf (ModCount49.profile i)) ℤ,
      profileGram93 (ModCount49.profile i)=A*Aᵀ := by
  let b : Fin (ModCount49.profile i).length := ⟨0,length_pos49 i⟩
  have hL : 0 < (ModCount49.profile i).get b := by
    apply Nat.pos_of_ne_zero
    intro h
    exact cycles_unit49 i b (by simp only [h,Nat.cast_zero])
  letI : Nonempty (BlocksOf (ModCount49.profile i)) := ⟨⟨b,⟨0,hL⟩⟩⟩
  have hneg : contrast (gramNorm (Symconf59.reduceMatrix 49
      (profileGram93 (ModCount49.profile i)))) (7:ZMod 49) < 0 := by
    rw [literal_mod49_direct_contrast]
    exact neg_lt_zero.mpr (pow_pos (by decide : (0:ℤ)<7) _)
  exact no_integral_gram49_of_negative_contrast _ (ModCount49.actual_inverse i).clearedMatrix
    (700*ModCount49.invC i) (ModCount49.actual_inverse_nonzero i)
    (ModCount49.actual_inverse i).scaled_inverse (ModCount49.invW i:ZMod 49)
    (ModCount49.actual_inverse_modulus i) hneg

end Symconf93.AffineFiber49

#print axioms Symconf93.AffineFiber49.literal_mod49_direct_contrast
#print axioms Symconf93.AffineFiber49.no_integral_gram49_without_pivots
