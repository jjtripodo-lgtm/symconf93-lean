module
public import Symconf93.Actual31Bridge
public import Symconf93DegreeNormalize

@[expose] public section

namespace Symconf93
open scoped BigOperators

private theorem corr_swap (A B : Z31→ℤ) (d : Z31) :
    cycleCorr31 B A d = cycleCorr31 A B (-d) := by
  unfold cycleCorr31
  have h := Equiv.sum_comp (Equiv.addRight d) (fun z => B (z-d)*A z)
  simpa [sub_neg_eq_add,mul_comm] using h.symm

def TwoBank31.reindex (S : TwoBank31) (e : Equiv.Perm (Fin 3)) : TwoBank31 where
  f := S.f ∘ e
  g := S.g ∘ e
  binary_f i := S.binary_f (e i)
  binary_g i := S.binary_g (e i)
  sum_f := (Equiv.sum_comp e (fun j => ∑ z,S.f j z)).trans S.sum_f
  sum_g := (Equiv.sum_comp e (fun j => ∑ z,S.g j z)).trans S.sum_g
  square_f := (Equiv.sum_comp e (fun j => (∑ z,S.f j z)^2)).trans S.square_f
  square_g := (Equiv.sum_comp e (fun j => (∑ z,S.g j z)^2)).trans S.square_g
  degreeCross := (Equiv.sum_comp e (fun j => (∑ z,S.f j z)*(∑ z,S.g j z))).trans S.degreeCross
  native_f d h := (Equiv.sum_comp e (fun j => cycleAuto31 (S.f j) d)).trans (S.native_f d h)
  native_g d h := (Equiv.sum_comp e (fun j => cycleAuto31 (S.g j) d)).trans (S.native_g d h)
  commonColumn j d h := S.commonColumn (e j) d h
  mixed_cover d := (Equiv.sum_comp e (fun j => cycleCorr31 (S.f j) (S.g j) d)).trans (S.mixed_cover d)

def TwoBank31.swap (S : TwoBank31) : TwoBank31 where
  f := S.g
  g := S.f
  binary_f := S.binary_g
  binary_g := S.binary_f
  sum_f := S.sum_g
  sum_g := S.sum_f
  square_f := S.square_g
  square_g := S.square_f
  degreeCross := by simpa only [mul_comm] using S.degreeCross
  native_f := S.native_g
  native_g := S.native_f
  commonColumn j d h := by simpa only [add_comm] using S.commonColumn j d h
  mixed_cover d := by
    have h : (∑ j,cycleCorr31 (S.g j) (S.f j) d)=
        ∑ j,cycleCorr31 (S.f j) (S.g j) (-d) :=
      Finset.sum_congr rfl (fun j _ => corr_swap (S.f j) (S.g j) d)
    exact h.trans (S.mixed_cover (-d))

structure FixedBanks31 extends TwoBank31 where
  exact_f : ∀ j, (∑ z,f j z)=(DegreeNormalize.tri 2 3 5 j:ℤ)
  exact_g : ∀ j, (∑ z,g j z)=(DegreeNormalize.tri 3 5 2 j:ℤ)

/-- Exact physical any-order two banks can be placed in the unique
coded degree order by harmless column reindexings and bank exchange. -/
theorem normalize_physical_banks31 (S : TwoBank31) : Nonempty FixedBanks31 := by
  let v (j : Fin 3) := (∑ z,S.f j z).toNat
  let w (j : Fin 3) := (∑ z,S.g j z).toNat
  have hv (j : Fin 3) : (v j:ℤ)=∑ z,S.f j z := by
    apply Int.toNat_of_nonneg
    apply Finset.sum_nonneg
    intro z _
    rcases S.binary_f j z with h|h <;> simp [h]
  have hw (j : Fin 3) : (w j:ℤ)=∑ z,S.g j z := by
    apply Int.toNat_of_nonneg
    apply Finset.sum_nonneg
    intro z _
    rcases S.binary_g j z with h|h <;> simp [h]
  have hnv : (∑ j,v j)=10 := by
    exact_mod_cast (show (∑ j,(v j:ℤ))=10 by simp only [hv];exact S.sum_f)
  have hnv2 : (∑ j,(v j)^2)=38 := by
    exact_mod_cast (show (∑ j,(v j:ℤ)^2)=38 by simp only [hv];exact S.square_f)
  have hnw : (∑ j,w j)=10 := by
    exact_mod_cast (show (∑ j,(w j:ℤ))=10 by simp only [hw];exact S.sum_g)
  have hnw2 : (∑ j,(w j)^2)=38 := by
    exact_mod_cast (show (∑ j,(w j:ℤ)^2)=38 by simp only [hw];exact S.square_g)
  have hcross : (∑ j,v j*w j)=31 := by
    exact_mod_cast (show (∑ j,(v j:ℤ)*(w j:ℤ))=31 by simp only [hv,hw];exact S.degreeCross)
  obtain ⟨e,hh|hh⟩ := DegreeNormalize.normalize_two_degree_rows v w hnv hnv2 hnw hnw2 hcross
  · refine ⟨⟨S.reindex e,fun j => ?_,fun j => ?_⟩⟩
    · change (∑ z,S.f (e j) z)=(DegreeNormalize.tri 2 3 5 j:ℤ)
      rw [← hv,hh.1]
    · change (∑ z,S.g (e j) z)=(DegreeNormalize.tri 3 5 2 j:ℤ)
      rw [← hw,hh.2]
  · refine ⟨⟨S.swap.reindex e,fun j => ?_,fun j => ?_⟩⟩
    · change (∑ z,S.g (e j) z)=(DegreeNormalize.tri 2 3 5 j:ℤ)
      rw [← hw,hh.1]
    · change (∑ z,S.f (e j) z)=(DegreeNormalize.tri 3 5 2 j:ℤ)
      rw [← hv,hh.2]

theorem actual_31cubed_to_fixed_banks {A : Int93} (hA : Incidence93 A)
    (R : OrderedCycles (rowLeave A) P31) (C : OrderedCycles (colLeave A) P31) :
    Nonempty FixedBanks31 := by
  obtain ⟨S⟩ := actual_31cubed_to_two_bank hA R C
  exact normalize_physical_banks31 S

end Symconf93

#print axioms Symconf93.normalize_physical_banks31
#print axioms Symconf93.actual_31cubed_to_fixed_banks
