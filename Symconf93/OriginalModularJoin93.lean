module
public import Symconf93.OriginalTerminalStaging93
public import Symconf93.ModularProfiles93

@[expose] public section

/-! The two literal modular lists are exactly, not merely subsets of,
the remaining 25 actual odd arithmetic profiles. -/
namespace Symconf93
open Matrix
open scoped Matrix

def originalModularRoster93 : List (List ℕ) :=
  ((List.finRange 2).map ModCount49.profile) ++
    ((List.finRange 23).map ModCount625.profile)

private theorem oddCovered93 :
    oddArithmeticProfiles93.all (fun P => decide (P∈originalModularRoster93))=true := by decide

private theorem oddExact93 :
    originalModularRoster93.all (fun P => decide (P∈oddArithmeticProfiles93))=true := by decide

theorem mem_originalModularRoster93 {P : List ℕ} :
    P∈originalModularRoster93 ↔ P∈oddArithmeticProfiles93 := by
  exact ⟨fun h => of_decide_eq_true (List.all_eq_true.mp oddExact93 P h),
    fun h => of_decide_eq_true (List.all_eq_true.mp oddCovered93 P h)⟩

theorem originalModularRoster93_nodup : originalModularRoster93.Nodup :=
  source_modular_profiles_nodup

/-- Literal row proof inputs. Neither of these definitions erases the
source index, modulus class, list order or actual Gram matrix. -/
def Mod49RosterExclusions93 : Prop := ∀ i : Fin 2,
    ¬∃ A : Matrix (BlocksOf (ModCount49.profile i)) (BlocksOf (ModCount49.profile i)) ℤ,
      profileGram93 (ModCount49.profile i)=A*Aᵀ

def Mod625RosterExclusions93 : Prop := ∀ i : Fin 23,
    ¬∃ A : Matrix (BlocksOf (ModCount625.profile i)) (BlocksOf (ModCount625.profile i)) ℤ,
      profileGram93 (ModCount625.profile i)=A*Aᵀ

theorem odd_arithmetic93_of_literal_modular_rosters
    (h49 : Mod49RosterExclusions93) (h625 : Mod625RosterExclusions93) :
    OddArithmetic93 := by
  intro P hP
  have h := mem_originalModularRoster93.mpr hP
  simp only [originalModularRoster93,List.mem_append,List.mem_map,List.mem_finRange,true_and] at h
  rcases h with ⟨i,rfl⟩|⟨i,rfl⟩
  · exact h49 i
  · exact h625 i

theorem arithmetic93_of_literal_modular_rosters
    (h49 : Mod49RosterExclusions93) (h625 : Mod625RosterExclusions93) : Arithmetic93 :=
  arithmetic93_of_pinned_odd (odd_arithmetic93_of_literal_modular_rosters h49 h625)

/-- Original unrestricted incidence terminal, with only the exact still
independent coverage and indexed arithmetic inputs visible. -/
theorem no_unrestricted_incidence93_of_coverage_and_literal_modular_rosters
    (hC : Coverage93) (h49 : Mod49RosterExclusions93) (h625 : Mod625RosterExclusions93) :
    ¬∃ A : Int93, Incidence93 A :=
  no_unrestricted_incidence93_of_coverage_and_arithmetic hC
    (arithmetic93_of_literal_modular_rosters h49 h625)

end Symconf93

#print axioms Symconf93.mem_originalModularRoster93
#print axioms Symconf93.originalModularRoster93_nodup
#print axioms Symconf93.arithmetic93_of_literal_modular_rosters
#print axioms Symconf93.no_unrestricted_incidence93_of_coverage_and_literal_modular_rosters
