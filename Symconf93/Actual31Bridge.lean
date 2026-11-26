module
public import Symconf93.ActualSieveInput
public import Symconf93.Physical31Correlations

@[expose] public section

/-! Unrestricted actual 93-incidence → two physical 31-edge banks.
The endpoint leaves only the named, finite nonlinear support check. -/
namespace Symconf93
open Matrix Symconf59
open scoped BigOperators Matrix

abbrev P31 : List ℕ := [31,31,31]

theorem length31 (i : Fin 3) : P31.get i=31 := by fin_cases i <;> rfl

def coord31 (i : Fin 3) : Z31 ≃ Fin (P31.get i) :=
  (ZMod.finEquiv 31).symm.toEquiv.trans (finCongr (length31 i).symm)

private theorem coord31_succ (i : Fin 3) :
    coord31 i 1=cnext (coord31 i 0) := by
  fin_cases i <;> decide

private theorem coord31_prev (i : Fin 3) :
    coord31 i (-1)=cprev (coord31 i 0) := by
  fin_cases i <;> decide

def trueSite31 {M : Int93} (Q : OrderedCycles M P31) (i : Fin 3) (x : Z31) : Site :=
  Q.sites ⟨i,coord31 i x⟩

private theorem trueSite31_inj {M : Int93} (Q : OrderedCycles M P31)
    {i j : Fin 3} {x y : Z31} (h : trueSite31 Q i x=trueSite31 Q j y) : i=j :=
  (Sigma.mk.inj_iff.mp (Q.sites.injective h)).1

private theorem trueSite31_inj_coord {M : Int93} (Q : OrderedCycles M P31)
    {i : Fin 3} {x y : Z31} (h : trueSite31 Q i x=trueSite31 Q i y) : x=y :=
  (coord31 i).injective (eq_of_heq (Sigma.mk.inj_iff.mp (Q.sites.injective h)).2)

private theorem count_trueSites31 {M : Int93} (Q : OrderedCycles M P31) (f : Site → ℤ) :
    (∑ i : Fin 3, ∑ x : Z31, f (trueSite31 Q i x))=∑ q, f q := by
  calc
    _ = ∑ i : Fin 3, ∑ x : Fin (P31.get i), f (Q.sites ⟨i,x⟩) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp (coord31 i) (fun x => f (Q.sites ⟨i,x⟩))
    _ = ∑ x : BlocksOf P31, f (Q.sites x) := (Fintype.sum_sigma (fun x : BlocksOf P31 => f (Q.sites x))).symm
    _ = _ := Equiv.sum_comp Q.sites f

def actualBlock31 {A : Int93} (R : OrderedCycles (rowLeave A) P31)
    (C : OrderedCycles (colLeave A) P31) (i j : Fin 3) (x y : Z31) : ℤ :=
  A (trueSite31 R i x) (trueSite31 C j y)

private theorem actualBlock31_wave {A : Int93} (hA : Incidence93 A)
    (R : OrderedCycles (rowLeave A) P31) (C : OrderedCycles (colLeave A) P31) (i j : Fin 3) :
    BlockWave (actualBlock31 R C i j) := by
  letI (k : Fin 3) : NeZero (P31.get k) := ⟨by rw [length31]; decide⟩
  fin_cases i <;> fin_cases j
  all_goals
    first | exact zblock_wave R C (0:Fin 3) (0:Fin 3) hA
          | exact zblock_wave R C (0:Fin 3) (1:Fin 3) hA
          | exact zblock_wave R C (0:Fin 3) (2:Fin 3) hA
          | exact zblock_wave R C (1:Fin 3) (0:Fin 3) hA
          | exact zblock_wave R C (1:Fin 3) (1:Fin 3) hA
          | exact zblock_wave R C (1:Fin 3) (2:Fin 3) hA
          | exact zblock_wave R C (2:Fin 3) (0:Fin 3) hA
          | exact zblock_wave R C (2:Fin 3) (1:Fin 3) hA
          | exact zblock_wave R C (2:Fin 3) (2:Fin 3) hA

def nativeRequired31 (d : Z31) : ℤ := if d=1 ∨ d=-1 then 0 else 1

structure TwoBank31 where
  f : Fin 3 → Z31 → ℤ
  g : Fin 3 → Z31 → ℤ
  binary_f : ∀ j z, f j z=0 ∨ f j z=1
  binary_g : ∀ j z, g j z=0 ∨ g j z=1
  sum_f : (∑ j, ∑ z, f j z)=10
  sum_g : (∑ j, ∑ z, g j z)=10
  square_f : (∑ j, (∑ z, f j z)^2)=38
  square_g : (∑ j, (∑ z, g j z)^2)=38
  degreeCross : (∑ j, (∑ z, f j z)*(∑ z,g j z))=31
  native_f : ∀ d, d≠0 → (∑ j,cycleAuto31 (f j) d)=nativeRequired31 d
  native_g : ∀ d, d≠0 → (∑ j,cycleAuto31 (g j) d)=nativeRequired31 d
  commonColumn : ∀ (j : Fin 3) d, d≠0 →
    cycleAuto31 (f j) d+cycleAuto31 (g j) d≤1
  mixed_cover : ∀ d, (∑ j,cycleCorr31 (f j) (g j) d)=1

private theorem within31 {A : Int93}
    (R : OrderedCycles (rowLeave A) P31) (C : OrderedCycles (colLeave A) P31)
    (i : Fin 3) (d : Z31) (hd : d≠0) :
    (∑ j, ∑ z,actualBlock31 R C i j 0 z * actualBlock31 R C i j d z)=nativeRequired31 d := by
  have hn : trueSite31 R i 0 ≠ trueSite31 R i d := by
    intro h
    exact hd (trueSite31_inj_coord R h).symm
  rw [show (∑ j,∑ z,actualBlock31 R C i j 0 z * actualBlock31 R C i j d z)=
      ∑ q, A (trueSite31 R i 0) q * A (trueSite31 R i d) q
      from count_trueSites31 C (fun q => A (trueSite31 R i 0) q * A (trueSite31 R i d) q)]
  have he := rowLeave_offdiag (A:=A) hn
  have hr := R.same_block i (coord31 i 0) (coord31 i d)
  change rowLeave A (trueSite31 R i 0) (trueSite31 R i d)=_ at hr
  rw [←coord31_succ i,←coord31_prev i] at hr
  simp only [(coord31 i).injective.eq_iff] at hr
  have ho : (∑ q, A (trueSite31 R i 0) q * A (trueSite31 R i d) q) =
      1-rowLeave A (trueSite31 R i 0) (trueSite31 R i d) := by omega
  rw [ho,hr]
  unfold nativeRequired31
  by_cases h1 : d=1
  · rw [if_pos (Or.inl h1),if_pos h1,if_neg (show d≠(-1:Z31) by rw [h1];decide)]
    decide
  · by_cases h2 : d=(-1:Z31)
    · rw [if_pos (Or.inr h2),if_neg h1,if_pos h2]
      decide
    · rw [if_neg (not_or.mpr ⟨h1,h2⟩),if_neg h1,if_neg h2]
      decide

private theorem cross31 {A : Int93}
    (R : OrderedCycles (rowLeave A) P31) (C : OrderedCycles (colLeave A) P31)
    {i k : Fin 3} (hik : i≠k) (d : Z31) :
    (∑ j, ∑ z, actualBlock31 R C i j d z * actualBlock31 R C k j 0 z)=1 := by
  have hn : trueSite31 R i d≠trueSite31 R k 0 :=
    fun hh => hik (trueSite31_inj R hh)
  have he := rowLeave_offdiag (A:=A) hn
  have hh := R.different_blocks hik (coord31 i d) (coord31 k 0)
  change rowLeave A (trueSite31 R i d) (trueSite31 R k 0)=0 at hh
  rw [hh] at he
  rw [show (∑ j,∑ z, actualBlock31 R C i j d z * actualBlock31 R C k j 0 z)=
      ∑ q, A (trueSite31 R i d) q*A (trueSite31 R k 0) q
      from count_trueSites31 C (fun q => A (trueSite31 R i d) q*A (trueSite31 R k 0) q)]
  omega

private theorem column31_bound {A : Int93} (hA : Incidence93 A)
    (R : OrderedCycles (rowLeave A) P31) (C : OrderedCycles (colLeave A) P31)
    (j : Fin 3) (d : Z31) (hd : d≠0) :
    (∑ z, actualBlock31 R C 0 j z 0*actualBlock31 R C 0 j z d)+
      (∑ z, actualBlock31 R C 1 j z 0*actualBlock31 R C 1 j z d)≤1 := by
  have hn : trueSite31 C j 0 ≠ trueSite31 C j d := by
    intro h
    exact hd (trueSite31_inj_coord C h).symm
  have hh := hA.transpose.overlap _ _ hn
  change (∑ q, A q (trueSite31 C j 0)*A q (trueSite31 C j d))≤1 at hh
  rw [← count_trueSites31 R] at hh
  change (∑ i : Fin 3, ∑ z, actualBlock31 R C i j z 0*actualBlock31 R C i j z d)≤1 at hh
  rw [Fin.sum_univ_three] at hh
  have hnn : 0≤∑ z, actualBlock31 R C 2 j z 0*actualBlock31 R C 2 j z d := by
    apply Finset.sum_nonneg
    intro x _
    rcases hA.binary (trueSite31 R 2 x) (trueSite31 C j 0) with he|he <;>
      rcases hA.binary (trueSite31 R 2 x) (trueSite31 C j d) with hf|hf <;>
        simp [actualBlock31,he,hf]
  linarith

/-- Every true 31^3 incidence yields literal two-bank data, no cyclic
assumption and no global alignment of the six block orientations. -/
theorem actual_31cubed_to_two_bank {A : Int93} (hA : Incidence93 A)
    (R : OrderedCycles (rowLeave A) P31) (C : OrderedCycles (colLeave A) P31) :
    Nonempty TwoBank31 := by
  classical
  let B := actualBlock31 R C
  have bin (i j : Fin 3) (x y : Z31) : B i j x y=0 ∨ B i j x y=1 :=
    hA.binary _ _
  have hw (i j : Fin 3) : BlockWave (B i j) := actualBlock31_wave hA R C i j
  have hp : ∀ a∈P31,3≤a := by decide
  let H := physical_of_ordered_cycles hA hp R C
  let X := physical_blocks_to_profile hA H (by decide) hp (by decide)
  have dd (i j : Fin 3) : (∑z, B i j 0 z)=(H.v i j:ℤ) := by
    calc
      _ = ∑ y:Fin (P31.get j), A (R.sites ⟨i,coord31 i 0⟩) (C.sites ⟨j,y⟩) :=
        Equiv.sum_comp (coord31 j) _
      _ = (H.u i j : ℤ) := H.rowCount i j _
      _ = _ := by
        have h := (X.row i).block j
        change P31.get i*H.u i j=P31.get j*H.v i j at h
        rw [length31,length31] at h
        exact_mod_cast (show H.u i j=H.v i j by omega)
  have d1 (i : Fin 3) : (∑ j : Fin 3, (H.v i j:ℤ))=10 := by
    have h := (X.row i).momentOne
    change (∑ j : Fin 3, P31.get j*(H.v i j))=10*(P31.get i) at h
    simp only [length31,← Finset.mul_sum] at h
    exact_mod_cast (show (∑ j : Fin 3,H.v i j)=10 by omega)
  have d2 (i : Fin 3) : (∑ j : Fin 3, (H.v i j:ℤ)^2)=38 := by
    have h := (X.row i).momentTwo
    change (∑j:Fin 3,P31.get j*(H.v i j)*(H.v i j))=P31.get i*(P31.get i+7) at h
    simp only [length31,mul_assoc,← Finset.mul_sum] at h
    have hn : (∑ j : Fin 3,(H.v i j)^2)=38 := by
      simp only [pow_two]
      omega
    exact_mod_cast hn
  have d3 : (∑ j : Fin 3, (H.v 0 j:ℤ)*(H.v 1 j:ℤ))=31 := by
    have h := X.cross (0:Fin 3) (1:Fin 3) (by decide)
    change (∑ j : Fin 3,P31.get j*(H.v 0 j)*(H.v 1 j))=P31.get 0*P31.get 1 at h
    simp only [length31,mul_assoc,← Finset.mul_sum] at h
    exact_mod_cast (show (∑ j : Fin 3,H.v 0 j*H.v 1 j)=31 by omega)
  choose f g hc hfr hgr hfu hgu hor using fun j : Fin 3 =>
    binary31_fixed_cross_pair (B 0 j) (B 1 j) (hw 0 j) (bin 0 j)
  have ff (j : Fin 3) : (∑ z,f j z)=(H.v 0 j:ℤ) := (hfu j).trans (dd 0 j)
  have gg (j : Fin 3) : (∑ z,g j z)=(H.v 1 j:ℤ) := (hgu j).trans (dd 1 j)
  refine ⟨⟨f,g,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro j z
    rcases hor j with h|h
    · rw [(h z).1]
      exact bin _ _ _ _
    · rw [(h z).1]
      exact bin _ _ _ _
  · intro j z
    rcases hor j with h|h
    · rw [(h z).2]
      exact bin _ _ _ _
    · rw [(h z).2]
      exact bin _ _ _ _
  · rw [← d1 0]
    exact Finset.sum_congr rfl (fun j _ => ff j)
  · rw [← d1 1]
    exact Finset.sum_congr rfl (fun j _ => gg j)
  · rw [← d2 0]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun x : ℤ => x^2) (ff j))
  · rw [← d2 1]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun x : ℤ => x^2) (gg j))
  · rw [← d3]
    exact Finset.sum_congr rfl (fun j _ => by rw [ff j,gg j])
  · intro d hd
    have ht := within31 R C 0 d hd
    change (∑ j, ∑ z,B 0 j 0 z*B 0 j d z)=_ at ht
    simp only [hfr,← (binary31_block_same_signature (B 0 _) (hw 0 _) (bin 0 _) d).1]
    exact ht
  · intro d hd
    have ht := within31 R C 1 d hd
    change (∑ j, ∑ z,B 1 j 0 z*B 1 j d z)=_ at ht
    simp only [hgr,← (binary31_block_same_signature (B 1 _) (hw 1 _) (bin 1 _) d).1]
    exact ht
  · intro j d hd
    rw [hfr,hgr,← (binary31_block_same_signature (B 0 j) (hw 0 j) (bin 0 j) d).2,
      ← (binary31_block_same_signature (B 1 j) (hw 1 j) (bin 1 j) d).2]
    exact column31_bound hA R C j d hd
  · intro d
    simp only [← hc]
    exact cross31 R C (show (0:Fin 3)≠1 by decide) d

end Symconf93

#print axioms Symconf93.actual_31cubed_to_two_bank
