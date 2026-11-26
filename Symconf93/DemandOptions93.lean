module
public import Symconf93.CoverageBasics93
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Sort

@[expose] public section

/-! Exact positive-row options and the full demand extraction. A skipped
column has u=0. Every kept column has its own physical multiplicity. -/
namespace Symconf93
open scoped List

structure PositiveOption93 where
  b : Nat
  u : Nat
  v : Nat
  deriving DecidableEq

def PositiveOption93.cost (x : PositiveOption93) : Nat := x.u*x.v

def optionAllowed93 (a : Nat) (o : PositiveOption93) : Prop :=
  3≤o.b ∧ o.b≤93 ∧ o.b≠4 ∧ 1≤o.u ∧ o.u≤10 ∧
    1≤o.v ∧ o.v≤10 ∧ a*o.u=o.b*o.v ∧ (a∣o.b ∨ o.u≤1)

instance (a : Nat) (o : PositiveOption93) : Decidable (optionAllowed93 a o) :=
  inferInstanceAs (Decidable (_∧_))

def optionOrder93 (x y : PositiveOption93) : Bool := decide (y.v≤x.v)

def positiveBlock93 (a v : Nat) : List PositiveOption93 :=
  (List.range' 1 10).reverse.map (fun u => ⟨a*u/v,u,v⟩)

def rawOptions93 (a : Nat) : List PositiveOption93 :=
  (List.range' 1 10).reverse.flatMap (positiveBlock93 a)

def rowOptions93 (a : Nat) : List PositiveOption93 :=
  (rawOptions93 a).filter (fun o => decide (optionAllowed93 a o))

theorem rowOptions93_iff {a : Nat} {o : PositiveOption93} :
    o∈rowOptions93 a ↔ optionAllowed93 a o := by
  rw [rowOptions93,rawOptions93,List.mem_filter]
  constructor
  · intro hh
    exact decide_eq_true_eq.mp hh.2
  · intro hh
    refine ⟨List.mem_flatMap.mpr ⟨o.v,?_ ,?_⟩,decide_eq_true_eq.mpr hh⟩
    · rw [List.mem_reverse,List.mem_range'_1]
      exact ⟨hh.2.2.2.2.2.1,by have := hh.2.2.2.2.2.2.1; omega⟩
    · unfold positiveBlock93
      apply List.mem_map.mpr
      refine ⟨o.u,?_ ,?_⟩
      · rw [List.mem_reverse,List.mem_range'_1]
        exact ⟨hh.2.2.2.1,by have := hh.2.2.2.2.1; omega⟩
      · have hv : 0<o.v := hh.2.2.2.2.2.1
        have hV : a*o.u/o.v=o.b := by rw [hh.2.2.2.2.2.2.2.1,Nat.mul_div_cancel _ hv]
        cases o
        simp only [hV]

private theorem positiveBlock93_value {a v : Nat} {o : PositiveOption93}
    (h : o∈positiveBlock93 a v) : o.v=v := by
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp h
  rfl

private theorem optionsFlat_sorted93 (a : Nat) (V : List Nat) (h : V.Pairwise (·≥·)) :
    (V.flatMap (positiveBlock93 a)).Pairwise (fun x y=>y.v≤x.v) := by
  induction V with
  | nil => simp
  | cons v V ih =>
    rw [List.flatMap_cons,List.pairwise_append]
    refine ⟨List.pairwise_iff_getElem.mpr ?_,ih (List.pairwise_cons.mp h).2,?_⟩
    · intro i j hi hj _
      rw [positiveBlock93_value (List.getElem_mem hj),positiveBlock93_value (List.getElem_mem hi)]
    · intro x hx y hy
      obtain ⟨b,hB,hY⟩ := List.mem_flatMap.mp hy
      rw [positiveBlock93_value hx,positiveBlock93_value hY]
      exact (List.pairwise_cons.mp h).1 b hB

theorem rowOptions93_sorted (a : Nat) :
    (rowOptions93 a).Pairwise (fun x y => y.v≤x.v) := by
  have h : (List.range' 1 10).reverse.Pairwise (·≥·) := by
    rw [List.pairwise_reverse]
    exact (List.sortedLT_range' 1 10 (by decide : (1:Nat)≠0)).pairwise.imp (fun h=>le_of_lt h)
  exact (optionsFlat_sorted93 a _ h).sublist (List.filter_sublist ..)

/-- Read every genuinely positive block of a realizable normalized row.
Its physical sizes form a bona fide sublist of the original columns. -/
theorem loose_positive_options93 {a : Nat} (ha : 0<a) {P : List Nat} {s q : Nat}
    (h : LooseRow93 a P s q)
    (hP : ∀ b∈P,3≤b ∧ b≤93 ∧ b≠4) :
    ∃ L : List PositiveOption93, (∀ o∈L,o∈rowOptions93 a) ∧
      (L.map PositiveOption93.u).sum=s ∧ (L.map PositiveOption93.cost).sum=q ∧
      L.map PositiveOption93.b <+ P := by
  induction h with
  | nil => exact ⟨[],by simp⟩
  | cons b P u v s q hb hu hv he hper _ ih =>
    obtain ⟨L,hL,hs,hq,hsub⟩ := ih (fun c hc=>hP c (List.mem_cons_of_mem _ hc))
    by_cases hu0 : u=0
    · exact ⟨L,hL,by simpa only [hu0,zero_add] using hs,
        by simpa only [hu0,zero_mul,zero_add] using hq,hsub.cons _⟩
    · let o : PositiveOption93 := ⟨b,u,v⟩
      have hv0 : 1≤v := by
        by_contra hn
        have h0 : v=0 := by omega
        exact (Nat.ne_of_gt (Nat.mul_pos ha (Nat.pos_of_ne_zero hu0))) (by simpa [h0] using he)
      have hO : o∈rowOptions93 a := rowOptions93_iff.mpr
        ⟨(hP b (by simp)).1,(hP b (by simp)).2.1,(hP b (by simp)).2.2,
          Nat.pos_of_ne_zero hu0,hu,hv0,hv,he,hper⟩
      refine ⟨o::L,?_ ,?_ ,?_ ,hsub.cons_cons _⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl|hm
        · exact hO
        · exact hL x hm
      · simp [o,hs]
      · simp [o,PositiveOption93.cost,hq]

end Symconf93

#print axioms Symconf93.rowOptions93_iff
#print axioms Symconf93.loose_positive_options93
