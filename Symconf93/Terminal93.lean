module
public import Symconf93.Actual31Bridge
public import Symconf93.ProfileSieve93

@[expose] public section

/-! The actual original-incidence terminal conditional on three explicitly
named finite gates. No condition on either actual leave is an input. -/
namespace Symconf93
open Matrix Symconf59
open scoped BigOperators Matrix

def profileAdj93 (P : List ℕ) (x y : BlocksOf P) : ℤ :=
  (if y=⟨x.1,cnext x.2⟩ then 1 else 0)+
    (if y=⟨x.1,cprev x.2⟩ then 1 else 0)

def profileGram93 (P : List ℕ) : Matrix (BlocksOf P) (BlocksOf P) ℤ :=
  fun x y => 9*(if x=y then 1 else 0)+1-profileAdj93 P x y

private theorem physical_profile_adj {P : List ℕ} {A : Int93}
    (R : OrderedCycles (rowLeave A) P) (x y : BlocksOf P) :
    rowLeave A (R.sites x) (R.sites y)=profileAdj93 P x y := by
  rcases x with ⟨i,x⟩
  rcases y with ⟨j,y⟩
  by_cases h : i=j
  · subst j
    rw [R.same_block]
    simp only [profileAdj93,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  · rw [R.different_blocks h]
    have hn (z : Fin (P.get i)) :
        (⟨j,y⟩ : BlocksOf P) ≠ ⟨i,z⟩ :=
      fun hz => h ((Sigma.mk.inj_iff.mp hz).1.symm)
    simp only [profileAdj93,if_neg (hn _),add_zero]

/-- Exact literal Gram link for the catalogue's intrinsic ordered leaves.
The incidence is genuinely resited using both ends of a bijection; no
equality of purported physical rows or counts is assumed. -/
theorem physical_profile_gram_factor {P : List ℕ} {A : Int93}
    (R : OrderedCycles (rowLeave A) P) :
    ∃ B : Matrix (BlocksOf P) (BlocksOf P) ℤ, profileGram93 P=B*Bᵀ := by
  let B : Matrix (BlocksOf P) (BlocksOf P) ℤ := fun x y => A (R.sites x) (R.sites y)
  refine ⟨B,?_⟩
  ext x y
  change profileGram93 P x y = ∑ u, A (R.sites x) (R.sites u)*A (R.sites y) (R.sites u)
  rw [Equiv.sum_comp R.sites (fun z => A (R.sites x) z*A (R.sites y) z)]
  rw [← row_gram_entry,row_gram_eq]
  change profileGram93 P x y = 9*(1:Int93) (R.sites x) (R.sites y)+1-rowLeave A (R.sites x) (R.sites y)
  rw [physical_profile_adj]
  simp only [profileGram93,Matrix.one_apply,R.sites.injective.eq_iff]

abbrev Mixed37 : List ℕ := List.replicate 9 7 ++ List.replicate 10 3

def profiles37 : List (List ℕ) := [
  [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [9, 9, 9, 9, 9, 9, 9, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3],
  [12, 12, 12, 12, 12, 6, 6, 3, 3, 3, 3, 3, 3, 3],
  [9, 9, 9, 9, 9, 9, 9, 9, 3, 3, 3, 3, 3, 3, 3],
  [12, 12, 12, 12, 12, 12, 3, 3, 3, 3, 3, 3, 3],
  [15, 15, 15, 15, 15, 3, 3, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3],
  [12, 12, 12, 12, 12, 6, 6, 6, 3, 3, 3, 3, 3],
  [9, 9, 9, 9, 9, 9, 9, 9, 9, 3, 3, 3, 3],
  [18, 18, 18, 18, 9, 3, 3, 3, 3],
  [27, 27, 27, 3, 3, 3, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 3, 3],
  [12, 12, 12, 12, 12, 6, 6, 6, 6, 3, 3, 3],
  [12, 12, 12, 12, 12, 12, 6, 6, 3, 3, 3],
  [12, 12, 12, 12, 12, 12, 12, 3, 3, 3],
  [24, 24, 24, 12, 3, 3, 3],
  [21, 21, 21, 21, 3, 3, 3],
  [15, 15, 15, 15, 15, 5, 5, 5, 3],
  [30, 30, 15, 10, 5, 3],
  [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3],
  [12, 12, 12, 12, 12, 6, 6, 6, 6, 6, 3],
  [12, 12, 12, 12, 12, 12, 6, 6, 6, 3],
  [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 3],
  [18, 18, 18, 18, 9, 9, 3],
  [27, 27, 27, 9, 3],
  [15, 15, 15, 15, 15, 15, 3],
  [30, 30, 30, 3],
  [31, 31, 31],
  [93]
]

def Coverage93 : Prop := ∀ P : List ℕ,
  P∈Symconf59.partitionLists 31 93 93 → profileSieve93 P=true → P∈profiles37

def Arithmetic93 : Prop := ∀ P : List ℕ, P∈profiles37 → P≠P31 → P≠Mixed37 →
  ¬∃ B : Matrix (BlocksOf P) (BlocksOf P) ℤ, profileGram93 P=B*Bᵀ

def PhaseEndgame93 : Prop := ¬Nonempty TwoBank31

theorem no_unrestricted_incidence93_of_certified_gates
    (coverage : Coverage93) (arithmetic : Arithmetic93) (phaseEndgame : PhaseEndgame93) :
    ¬∃ A : Int93, Incidence93 A := by
  rintro ⟨A,hA⟩
  obtain ⟨P,hP,R,C,⟨F⟩⟩ := physical_profile_mem_parity_free hA
  have hc := coverage P hP (true_profile_passes_sieve F)
  by_cases h31 : P=P31
  · subst P
    exact phaseEndgame (actual_31cubed_to_two_bank hA R C)
  · by_cases hM : P=Mixed37
    · subst P
      exact no_three_seven_original_profile F
    · exact arithmetic P hc h31 hM (physical_profile_gram_factor R)

end Symconf93

#print axioms Symconf93.physical_profile_gram_factor
#print axioms Symconf93.no_unrestricted_incidence93_of_certified_gates
