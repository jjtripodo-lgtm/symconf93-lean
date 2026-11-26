module
public import Symconf93.TraceRecurrence
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

/-! Exact nonbacktracking registers from one genuine orientation of the
actual two-regular leaves. -/
namespace Symconf93
open Matrix
open scoped Matrix BigOperators

def permMat (s : Equiv.Perm Site) : Int93 :=
  fun i j => if j=s i then 1 else 0

theorem permMat_left (s : Equiv.Perm Site) (B : Int93) (i j : Site) :
    (permMat s*B) i j=B (s i) j := by
  simp [Matrix.mul_apply,permMat,ite_mul]

theorem permMat_right (s : Equiv.Perm Site) (B : Int93) (i j : Site) :
    (B*permMat s) i j=B i (s⁻¹ j) := by
  have h (q : Site) : (j=s q) ↔ q=s⁻¹ j := by
    change (j=s q) ↔ q=s.symm j
    constructor
    · intro e
      rw [e,s.symm_apply_apply]
    · intro e
      rw [e,s.apply_symm_apply]
  simp [Matrix.mul_apply,permMat,mul_ite,h]

theorem permMat_mul (s t : Equiv.Perm Site) :
    permMat s*permMat t=permMat (t*s) := by
  ext i j
  rw [permMat_left]
  rfl

theorem permMat_one : permMat (1 : Equiv.Perm Site)=1 := by
  ext i j
  simp [permMat,Matrix.one_apply,eq_comm]

def symmetricStep (s : Equiv.Perm Site) (n : ℕ) : Int93 :=
  permMat (s^n)+permMat ((s⁻¹)^n)

theorem symmetricStep_succ (s : Equiv.Perm Site) (n : ℕ) :
    symmetricStep s (n+2) = symmetricStep s 1*symmetricStep s (n+1)-symmetricStep s n := by
  unfold symmetricStep
  rw [pow_one,pow_one,add_mul,mul_add,mul_add,permMat_mul,permMat_mul,permMat_mul,permMat_mul]
  rw [← pow_succ s (n+1),← pow_succ s⁻¹ (n+1),
    show (s⁻¹)^(n+1)*s=(s⁻¹)^n by rw [pow_succ,mul_assoc,inv_mul_cancel,mul_one],
    show s^(n+1)*s⁻¹=s^n by rw [pow_succ,mul_assoc,mul_inv_cancel,mul_one]]
  abel

theorem permMat_mul_allOnes (s : Equiv.Perm Site) : permMat s*allOnes=allOnes := by
  ext i j
  rw [permMat_left]
  rfl

/-- The whole original symmetric-step register is produced from the
literal successor permutation, not granted in the spectral calculation. -/
def stepRegisterOfPerm (s : Equiv.Perm Site) : StepRegister (symmetricStep s 1) where
  step := symmetricStep s
  zero := by
    unfold symmetricStep
    rw [pow_zero,pow_zero,permMat_one,two_smul]
  one := rfl
  stepRec := symmetricStep_succ s
  ones := by
    intro n
    unfold symmetricStep
    rw [add_mul,permMat_mul_allOnes,permMat_mul_allOnes,two_smul]

private theorem fixed_inverse (v : Equiv.Perm Site) (i : Site) :
    v⁻¹ i=i ↔ v i=i := by
  change v.symm i=i ↔ v i=i
  constructor
  · intro he
    have h := congrArg v he
    rw [v.apply_symm_apply] at h
    exact h.symm
  · intro he
    have h := congrArg v.symm he
    rw [v.symm_apply_apply] at h
    exact h.symm

private theorem trace_symmetricStep (s : Equiv.Perm Site) (n : ℕ) :
    Matrix.trace (symmetricStep s n)=2*(∑ i : Site,if (s^n) i=i then (1:ℤ) else 0) := by
  rw [symmetricStep,Matrix.trace_add,inv_pow]
  have h : Matrix.trace (permMat ((s^n)⁻¹))=Matrix.trace (permMat (s^n)) := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diag_apply,permMat]
    have hf : (i=(s^n)⁻¹ i) ↔ i=(s^n) i :=
      eq_comm.trans ((fixed_inverse (s^n) i).trans eq_comm)
    by_cases h : i=(s^n) i
    · simp only [if_pos h,if_pos (hf.mpr h)]
    · simp only [if_neg h,if_neg (hf.not.mpr h)]
  rw [h,two_mul]
  have he : Matrix.trace (permMat (s^n)) = ∑ i : Site, if (s^n) i=i then (1:ℤ) else 0 := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diag_apply,permMat]
    by_cases h : (s^n) i=i
    · simp only [if_pos h,if_pos h.symm]
    · simp only [if_neg h,if_neg (fun he : i=(s^n) i => h he.symm)]
  rw [he]

/-- On the literal original incidence family, powers of the two oriented
leave permutations have the same number of fixed vertices. This is the
complete trace output before arithmetic cycle-profile inversion. -/
theorem original_power_fixed_counts {A : Int93} (hA : Incidence93 A)
    (s t : Equiv.Perm Site)
    (hs : rowLeave A=symmetricStep s 1) (ht : colLeave A=symmetricStep t 1) :
    ∀ n, (∑ i : Site,if (s^n) i=i then (1:ℤ) else 0)=
      ∑ i : Site,if (t^n) i=i then (1:ℤ) else 0 := by
  let P : StepRegister (rowLeave A) :=
    ⟨symmetricStep s,(stepRegisterOfPerm s).zero,hs.symm,
      fun n => hs.symm ▸ symmetricStep_succ s n,(stepRegisterOfPerm s).ones⟩
  let Q : StepRegister (colLeave A) :=
    ⟨symmetricStep t,(stepRegisterOfPerm t).zero,ht.symm,
      fun n => ht.symm ▸ symmetricStep_succ t n,(stepRegisterOfPerm t).ones⟩
  intro n
  have h := original_symmetric_step_trace_agrees hA P Q n
  change Matrix.trace (symmetricStep s n)=Matrix.trace (symmetricStep t n) at h
  rw [trace_symmetricStep,trace_symmetricStep] at h
  omega

end Symconf93
