module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Sort

@[expose] public section

/-! Parity-free exact profile sieve, using bounded normalized integer
budgets and just the local consequence of periodicity at most one. -/
namespace Symconf59

def partitionLists : (fuel rem hi : ℕ) → List (List ℕ)
  | 0, rem, _ => if rem=0 then [[]] else []
  | f+1, rem, hi =>
    if rem=0 then [[]]
    else ((List.range (min rem hi+1)).filter (fun b => 3≤b)).flatMap
      (fun b => (partitionLists f (rem-b) b).map (List.cons b))

/-- Every descending positive list with the specified entry bounds is
covered; no restriction on the parity of the part count. -/
theorem partitionLists_complete (P : List ℕ) (fuel hi : ℕ)
    (hFuel : P.length≤fuel) (hMin : ∀ b∈P, 3≤b) (hMax : ∀ b∈P, b≤hi)
    (hSort : P.Pairwise (· ≥ ·)) : P∈partitionLists fuel P.sum hi := by
  induction P generalizing fuel hi with
  | nil =>
    cases fuel <;> simp [partitionLists]
  | cons a P ih =>
    have ha := hMin a (by simp)
    have hMaxa := hMax a (by simp)
    have hPos : (a::P).sum≠0 := by simp only [List.sum_cons]; omega
    have hFuelpos : 0<fuel := by simp only [List.length_cons] at hFuel; omega
    obtain ⟨f,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel≠0)
    simp only [partitionLists,hPos,if_false,List.mem_flatMap,List.mem_filter,List.mem_range,
      List.mem_map,decide_eq_true_eq]
    refine ⟨a,⟨?_,ha⟩,P,?_,rfl⟩
    · simp only [List.sum_cons,Nat.lt_succ_iff,Nat.le_min]
      exact ⟨Nat.le_add_right a P.sum,hMaxa⟩
    · simp only [List.sum_cons,Nat.add_sub_cancel_left]
      exact ih f a (by simpa using hFuel)
        (fun b hb => hMin b (List.mem_cons_of_mem _ hb))
        (List.pairwise_cons.mp hSort).1 (List.pairwise_cons.mp hSort).2

private theorem length_budget (P : List ℕ) (h : ∀ b∈P, 3≤b) : 3*P.length≤P.sum := by
  induction P with
  | nil => decide
  | cons a P ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.length_cons,List.sum_cons]
    omega

def profileLists59 : List (List ℕ) := partitionLists 19 59 59

theorem member_le_sum {b : ℕ} {P : List ℕ} (h : b∈P) : b≤P.sum := by
  induction P with
  | nil => simp at h
  | cons a P ih =>
    rcases List.mem_cons.mp h with rfl|hh
    · exact Nat.le_add_right _ _
    · exact (ih hh).trans (Nat.le_add_left _ _)

theorem original_profile_mem (P : List ℕ) (hSum : P.sum=59)
    (hMin : ∀ b∈P, 3≤b) (hSort : P.Pairwise (· ≥ ·)) : P∈profileLists59 := by
  have hn := length_budget P hMin
  have hMax : ∀ b∈P, b≤59 := fun b hb => hSum ▸ member_le_sum hb
  have hf : P.length≤19 := by omega
  simpa only [hSum,profileLists59] using partitionLists_complete P 19 59 hf hMin hMax hSort

/-- Structural witness corresponding to an actual original row's block
sums after normalizing its first and second moments by its length. -/
inductive LocalRowBudget (a : ℕ) : List ℕ → ℕ → ℕ → Prop where
  | nil : LocalRowBudget a [] 0 0
  | cons (b : ℕ) (P : List ℕ) (u v s q : ℕ) :
      0<b → u≤8 → v≤8 → a*u=b*v →
      (a∣b ∨ u≤1) → LocalRowBudget a P s q →
      LocalRowBudget a (b::P) (u+s) (u*v+q)

def rowPossible (a : ℕ) (P : List ℕ) (s q : ℕ) : Bool :=
  match P with
  | [] => decide (s=0 ∧ q=0)
  | b::P => (List.range (min s 8+1)).any (fun u =>
      let v := a*u/b
      decide (0<b ∧ a*u=b*v ∧ v≤8 ∧ u*v≤q ∧ (a∣b ∨ u≤1)) &&
        rowPossible a P (s-u) (q-u*v))

/-- A genuine local row never gets rejected by the fast bounded checker. -/
theorem rowPossible_complete {a : ℕ} {P : List ℕ} {s q : ℕ}
    (h : LocalRowBudget a P s q) : rowPossible a P s q=true := by
  induction h with
  | nil => rfl
  | cons b P u v s q hb hu hv hdiv hlocal htail ih =>
    have hV : a*u/b=v := by rw [hdiv,Nat.mul_comm,Nat.mul_div_cancel _ hb]
    rw [rowPossible,List.any_eq_true]
    refine ⟨u,?_ ,?_⟩
    · rw [List.mem_range,Nat.lt_succ_iff,Nat.le_min]
      exact ⟨Nat.le_add_right _ _,hu⟩
    · simp only [hV,Bool.and_eq_true,decide_eq_true_eq,Nat.add_sub_cancel_left]
      exact ⟨⟨hb,hdiv,hv,Nat.le_add_right _ _,hlocal⟩,ih⟩

def checkProfile (P : List ℕ) : Bool := P.all (fun a => rowPossible a P 8 (a+5))

theorem checkProfile_complete (P : List ℕ)
    (h : ∀ a∈P, LocalRowBudget a P 8 (a+5)) : checkProfile P=true :=
  List.all_eq_true.mpr (fun a ha => rowPossible_complete (h a ha))

def locallyAllowed : List (List ℕ) :=
  [[59],[21,7,7,7,7,7,3],[15,15,15,5,3,3,3],[15,15,5,5,5,5,3,3,3],
    [5,5,5,5,5,5,5,3,3,3,3,3,3,3,3]]

def afterFirst (a : ℕ) : List (List ℕ) :=
  (partitionLists 18 (59-a) a).map (List.cons a)

private theorem profile_nonempty (P : List ℕ) (h : P.sum=59) : P≠[] := by
  intro he
  rw [he,List.sum_nil] at h
  omega

/-- Split by the first (largest) part, for bounded reflection per top. -/
theorem original_afterFirst (P : List ℕ) (hSum : P.sum=59)
    (hMin : ∀ b∈P, 3≤b) (hSort : P.Pairwise (· ≥ ·)) :
    ∃ a : Fin 60, 3≤a.val ∧ P∈afterFirst a.val := by
  cases P with
  | nil => simp at hSum
  | cons a P =>
    simp only [List.sum_cons] at hSum
    have hle : a≤59 := by omega
    refine ⟨⟨a,by omega⟩,hMin a (by simp),?_⟩
    rw [afterFirst,List.mem_map]
    refine ⟨P,?_ ,rfl⟩
    have hlen := length_budget P (fun b hb => hMin b (List.mem_cons_of_mem _ hb))
    have ha := hMin a (by simp)
    have hsum : P.sum=59-a := by omega
    have hf : P.length≤18 := by omega
    simpa only [hsum] using partitionLists_complete P 18 a hf
      (fun b hb => hMin b (List.mem_cons_of_mem _ hb))
      (List.pairwise_cons.mp hSort).1 (List.pairwise_cons.mp hSort).2

def topPass (a : ℕ) : Bool :=
  ((afterFirst a).filter checkProfile).all (fun p => locallyAllowed.contains p)

end Symconf59
