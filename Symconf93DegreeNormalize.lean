module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Literal degree normalization for two actual 31-cycle rows.
Only the elementary three-coordinate arithmetic is checked here. -/
namespace Symconf93.DegreeNormalize
open scoped BigOperators

def tri (a b c : Nat) (i : Fin 3) : Nat :=
  if i = 0 then a else if i = 1 then b else c

def allowed (p : Fin 6) : Fin 3 → Nat :=
  if p = 0 then tri 2 3 5 else
  if p = 1 then tri 2 5 3 else
  if p = 2 then tri 3 2 5 else
  if p = 3 then tri 3 5 2 else
  if p = 4 then tri 5 2 3 else tri 5 3 2

def perm (p : Fin 6) : Equiv.Perm (Fin 3) :=
  if p = 0 then Equiv.refl _ else
  if p = 1 then Equiv.swap 1 2 else
  if p = 2 then Equiv.swap 0 1 else
  if p = 3 then (Equiv.swap 0 1).trans (Equiv.swap 0 2) else
  if p = 4 then (Equiv.swap 0 2).trans (Equiv.swap 0 1) else Equiv.swap 0 2

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem check_one :
    ∀ a b c : Fin 11, a.val+b.val+c.val=10 →
      a.val^2+b.val^2+c.val^2=38 →
      ∃ p : Fin 6, ∀ i : Fin 3, tri a.val b.val c.val i = allowed p i := by decide

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem check_two :
    ∀ a b : Fin 6, (∑ i : Fin 3, allowed a i * allowed b i) = 31 →
      ∃ p : Fin 6,
        ((∀ i : Fin 3, allowed a (perm p i) = tri 2 3 5 i) ∧
          (∀ i : Fin 3, allowed b (perm p i) = tri 3 5 2 i)) ∨
        ((∀ i : Fin 3, allowed b (perm p i) = tri 2 3 5 i) ∧
          (∀ i : Fin 3, allowed a (perm p i) = tri 3 5 2 i)) := by decide

theorem degree_triple (v : Fin 3 → Nat)
    (h : (∑ i : Fin 3, v i) = 10)
    (hs : (∑ i : Fin 3, v i ^ 2) = 38) :
    ∃ p : Fin 6, v = allowed p := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h hs
  change v 0 + (v 1 + (v 2 + 0)) = 10 at h
  change (v 0)^2 + ((v 1)^2 + ((v 2)^2 + 0)) = 38 at hs
  let a : Fin 11 := ⟨v 0, by omega⟩
  let b : Fin 11 := ⟨v 1, by omega⟩
  let c : Fin 11 := ⟨v 2, by omega⟩
  have h1 : a.val+b.val+c.val=10 := by dsimp [a,b,c]; omega
  have h2 : a.val^2+b.val^2+c.val^2=38 := by dsimp [a,b,c]; omega
  obtain ⟨p, hp⟩ := check_one a b c h1 h2
  refine ⟨p, ?_⟩
  funext i
  calc
    v i = tri a.val b.val c.val i := by fin_cases i <;> rfl
    _ = allowed p i := hp i

/-- Simultaneous original column permutation; banks may be swapped first.
There are no symmetry assumptions about the underlying incidence. -/
theorem normalize_two_degree_rows (v w : Fin 3 → Nat)
    (hv : (∑ i : Fin 3, v i)=10) (hv2 : (∑ i : Fin 3, v i^2)=38)
    (hw : (∑ i : Fin 3, w i)=10) (hw2 : (∑ i : Fin 3, w i^2)=38)
    (hcross : (∑ i : Fin 3, v i*w i)=31) :
    ∃ e : Equiv.Perm (Fin 3),
      ((∀ i : Fin 3, v (e i)=tri 2 3 5 i) ∧ (∀ i : Fin 3, w (e i)=tri 3 5 2 i)) ∨
      ((∀ i : Fin 3, w (e i)=tri 2 3 5 i) ∧ (∀ i : Fin 3, v (e i)=tri 3 5 2 i)) := by
  obtain ⟨a, rfl⟩ := degree_triple v hv hv2
  obtain ⟨b, rfl⟩ := degree_triple w hw hw2
  obtain ⟨p, hp⟩ := check_two a b hcross
  exact ⟨perm p, hp⟩

#print axioms normalize_two_degree_rows
end Symconf93.DegreeNormalize
