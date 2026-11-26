module
public import Symconf93.Incidence
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Exact nonspectral trace transport for the original leave matrices. -/
namespace Symconf93
open Matrix
open scoped Matrix

/-- A symmetric-step register from a cycle layout has these four
identities; the trace proof itself does not ask for conjugacy or an
invertible incidence matrix. -/
structure StepRegister (R : Int93) where
  step : ℕ → Int93
  zero : step 0=(2:ℤ) • (1:Int93)
  one : step 1=R
  stepRec : ∀ n, step (n+2)=R*step (n+1)-step n
  ones : ∀ n, step n*allOnes=(2:ℤ) • allOnes

private theorem step_intertwine {R C A : Int93} (P : StepRegister R) (Q : StepRegister C)
    (hc : R*A=A*C) : ∀ n, P.step n*A=A*Q.step n := by
  let D : ℕ → Prop := fun n => P.step n*A=A*Q.step n
  have h₀ : D 0 := by
    change P.step 0*A=A*Q.step 0
    rw [P.zero,Q.zero,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  have h₁ : D 1 := by
    change P.step 1*A=A*Q.step 1
    rw [P.one,Q.one,hc]
  have hstep : ∀ n, D n → D (n+1) → D (n+2) := by
    intro n hn hprev
    change P.step n*A=A*Q.step n at hn
    change P.step (n+1)*A=A*Q.step (n+1) at hprev
    change P.step (n+2)*A=A*Q.step (n+2)
    rw [P.stepRec,Q.stepRec,sub_mul,mul_sub,mul_assoc,hprev,← mul_assoc,hc,mul_assoc,hn]
  have happ (n : ℕ) : D n ∧ D (n+1) := by
    induction n with
    | zero => exact ⟨h₀,h₁⟩
    | succ n ih => exact ⟨ih.2,hstep n ih.1 ih.2⟩
  exact fun n => (happ n).1

/-- The only difference compatible with both physical Gram identities
satisfies a second-order recurrence with two zero seeds. -/
theorem original_symmetric_step_trace_agrees {A : Int93} (hA : Incidence93 A)
    (P : StepRegister (rowLeave A)) (Q : StepRegister (colLeave A)) :
    ∀ n, Matrix.trace (P.step n)=Matrix.trace (Q.step n) := by
  have hInt := step_intertwine P Q (leave_intertwines hA)
  have hTrace (n : ℕ) : Matrix.trace (P.step n*(A*Aᵀ))=Matrix.trace (Q.step n*(Aᵀ*A)) := by
    rw [← mul_assoc,hInt,mul_assoc,Matrix.trace_mul_comm A, mul_assoc]
  have hBase (n : ℕ) :
      9*Matrix.trace (P.step n)-Matrix.trace (P.step n*rowLeave A)=
        9*Matrix.trace (Q.step n)-Matrix.trace (Q.step n*colLeave A) := by
    have he := hTrace n
    rw [row_gram_eq,col_gram_eq,mul_sub,mul_sub,mul_add,mul_add,mul_smul_comm,mul_smul_comm,
      mul_one,mul_one,P.ones,Q.ones,Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_add,
      Matrix.trace_add] at he
    simp only [Matrix.trace_smul,smul_eq_mul] at he
    linear_combination he
  have htP (n : ℕ) : Matrix.trace (P.step (n+2))+Matrix.trace (P.step n)=
      Matrix.trace (P.step (n+1)*rowLeave A) := by
    rw [P.stepRec,Matrix.trace_sub,Matrix.trace_mul_comm (rowLeave A),sub_add_cancel]
  have htQ (n : ℕ) : Matrix.trace (Q.step (n+2))+Matrix.trace (Q.step n)=
      Matrix.trace (Q.step (n+1)*colLeave A) := by
    rw [Q.stepRec,Matrix.trace_sub,Matrix.trace_mul_comm (colLeave A),sub_add_cancel]
  let D : ℕ → Prop := fun n => Matrix.trace (P.step n)=Matrix.trace (Q.step n)
  have d₀ : D 0 := by
    change Matrix.trace (P.step 0)=Matrix.trace (Q.step 0)
    rw [P.zero,Q.zero]
  have d₁ : D 1 := by
    change Matrix.trace (P.step 1)=Matrix.trace (Q.step 1)
    rw [P.one,Q.one]
    unfold Matrix.trace
    simp only [Matrix.diag_apply,rowLeave_diag hA,colLeave,rowLeave_diag hA.transpose,Finset.sum_const_zero]
  have hstep : ∀ n, D n → D (n+1) → D (n+2) := by
    intro n hd hp
    change Matrix.trace (P.step n)=Matrix.trace (Q.step n) at hd
    change Matrix.trace (P.step (n+1))=Matrix.trace (Q.step (n+1)) at hp
    change Matrix.trace (P.step (n+2))=Matrix.trace (Q.step (n+2))
    have he := hBase (n+1)
    linear_combination (-he)+9*hp+htP n-htQ n-hd
  have hs (n : ℕ) : D n ∧ D (n+1) := by
    induction n with
    | zero => exact ⟨d₀,d₁⟩
    | succ n ih => exact ⟨ih.2,hstep n ih.1 ih.2⟩
  exact fun n => (hs n).1

end Symconf93
