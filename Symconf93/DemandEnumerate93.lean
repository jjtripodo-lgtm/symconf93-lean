module
public import Symconf93.DemandOptions93

@[expose] public section

/-! Bounded independent enumeration of all positive demand multisets.
Options are in decreasing v. Every witness pays first and second moments
exactly; q>s*v or q<s discards a truly impossible suffix branch. -/
namespace Symconf93
open scoped List

def demandEnum93 : List PositiveOption93 → Nat → Nat → List (List Nat)
  | O,s,q =>
    if s=0 then
      if q=0 then [[]] else []
    else
      match O with
      | [] => []
      | o::T =>
        if s≤q ∧ q≤s*o.v then
          (List.range (min (s/o.u) (q/o.cost)+1)).flatMap (fun m =>
            (demandEnum93 T (s-m*o.u) (q-m*o.cost)).map (fun D=> List.replicate m o.b ++ D))
        else []

def rowDemand93 (a : Nat) : List (List Nat) := demandEnum93 (rowOptions93 a) 10 (a+7)

private theorem weighted_bounds93 (L : List PositiveOption93) (v : Nat)
    (hV : ∀ x∈L, 1≤x.v ∧ x.v≤v) :
    (L.map PositiveOption93.u).sum≤(L.map PositiveOption93.cost).sum ∧
      (L.map PositiveOption93.cost).sum≤(L.map PositiveOption93.u).sum*v := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨hlo,hup⟩ := ih (fun x hx=>hV x (List.mem_cons_of_mem _ hx))
    obtain ⟨ha₁,ha₂⟩ := hV a (by simp)
    have h₁ : a.u≤a.cost := by
      simpa only [Nat.mul_one,PositiveOption93.cost] using Nat.mul_le_mul_left a.u ha₁
    have h₂ : a.cost≤a.u*v := Nat.mul_le_mul_left a.u ha₂
    simp only [List.map_cons,List.sum_cons,Nat.add_mul]
    exact ⟨Nat.add_le_add h₁ hlo,Nat.add_le_add h₂ hup⟩

/-- An arbitrary sequence of available positive options is located by the
finite multiplicity enumerator, without assuming the physical row is sorted. -/
theorem demandEnum93_complete (O L : List PositiveOption93) (s q : Nat)
    (hsort : O.Pairwise (fun x y=>y.v≤x.v))
    (hp : ∀ o∈O, 1≤o.u ∧ 1≤o.v) (hL : ∀ o∈L,o∈O)
    (hs : (L.map PositiveOption93.u).sum=s) (hq : (L.map PositiveOption93.cost).sum=q) :
    ∃ D∈demandEnum93 O s q, D.Perm (L.map PositiveOption93.b) := by
  induction O generalizing L s q with
  | nil =>
    cases L with
    | nil => simp at hs hq; subst s; subst q; exact ⟨[],by simp [demandEnum93]⟩
    | cons x L => simpa using hL x (by simp)
  | cons o O ih =>
    cases L with
    | nil => simp at hs hq; subst s; subst q; exact ⟨[],by simp [demandEnum93]⟩
    | cons x X =>
      let L := x::X
      have hs0 : s≠0 := by
        have h := (hp x (hL x (by simp))).1
        simp only [List.map_cons,List.sum_cons] at hs
        omega
      have hlimits : s≤q ∧ q≤s*o.v := by
        have hh := weighted_bounds93 L o.v (fun z hz => by
          have hm := hL z hz
          refine ⟨(hp z hm).2,?_⟩
          rcases List.mem_cons.mp hm with rfl|hr
          · exact le_rfl
          · exact (List.pairwise_cons.mp hsort).1 z hr)
        change ((x::X).map _).sum≤((x::X).map _).sum ∧
          ((x::X).map _).sum≤((x::X).map _).sum*o.v at hh
        rwa [hs,hq] at hh
      let p : PositiveOption93→Bool := fun x=>decide (x=o)
      let M := L.filter p
      let N := L.filter (fun z=>!p z)
      let m := M.length
      have hpL : (M++N).Perm L := List.filter_append_perm p L
      have hm : M=List.replicate m o := by
        apply List.eq_replicate_of_mem
        intro z hz
        exact decide_eq_true_eq.mp (List.mem_filter.mp hz).2
      have hN (z : PositiveOption93) (hz : z∈N) : z∈O := by
        obtain ⟨h1,h2⟩ := List.mem_filter.mp hz
        have h3 : z≠o := by simpa [p] using h2
        exact (List.mem_cons.mp (hL z h1)).resolve_left h3
      have hu' := (hpL.map PositiveOption93.u).sum_eq
      have hv' := (hpL.map PositiveOption93.cost).sum_eq
      have hsplit1 : m*o.u+(N.map PositiveOption93.u).sum=s := by
        simpa only [List.map_append,hm,List.map_replicate,List.sum_append,List.sum_replicate,
          Nat.nsmul_eq_mul] using (hu'.trans (show (L.map PositiveOption93.u).sum=s from hs))
      have hsplit2 : m*o.cost+(N.map PositiveOption93.cost).sum=q := by
        simpa only [List.map_append,hm,List.map_replicate,List.sum_append,List.sum_replicate,
          Nat.nsmul_eq_mul] using (hv'.trans (show (L.map PositiveOption93.cost).sum=q from hq))
      have hu0 : 0<o.u := (hp o (by simp)).1
      have hv0 : 0<o.v := (hp o (by simp)).2
      have hcost : 0<o.cost := Nat.mul_pos hu0 hv0
      have hML : m≤min (s/o.u) (q/o.cost) := by
        apply Nat.le_min.mpr
        exact ⟨(Nat.le_div_iff_mul_le hu0).mpr (by omega),
          (Nat.le_div_iff_mul_le hcost).mpr (by omega)⟩
      have hNS : (N.map PositiveOption93.u).sum=s-m*o.u := by omega
      have hNQ : (N.map PositiveOption93.cost).sum=q-m*o.cost := by omega
      obtain ⟨D,hD,hDP⟩ := ih N (s-m*o.u) (q-m*o.cost)
        (List.pairwise_cons.mp hsort).2 (fun z hz=>hp z (List.mem_cons_of_mem _ hz)) hN hNS hNQ
      refine ⟨List.replicate m o.b++D,?_ ,?_⟩
      · rw [demandEnum93,if_neg hs0,if_pos hlimits]
        exact List.mem_flatMap.mpr ⟨m,List.mem_range.mpr (by omega),
          List.mem_map.mpr ⟨D,hD,rfl⟩⟩
      · have hmP := hpL.map PositiveOption93.b
        have hp' : (List.replicate m o.b++N.map PositiveOption93.b).Perm
            ((x::X).map PositiveOption93.b) := by
          simpa only [List.map_append,hm,List.map_replicate] using hmP
        exact (hDP.append_left _).trans hp'

theorem rowDemand93_complete {a : Nat} (ha : 0<a) {P : List Nat}
    (h : LooseRow93 a P 10 (a+7))
    (hP : ∀ b∈P, 3≤b ∧ b≤93 ∧ b≠4) :
    ∃ D∈rowDemand93 a, D <+~ P := by
  obtain ⟨L,hL,hs,hq,hsub⟩ := loose_positive_options93 ha h hP
  have hp (o : PositiveOption93) (ho : o∈rowOptions93 a) : 1≤o.u ∧ 1≤o.v := by
    have hh := rowOptions93_iff.mp ho
    exact ⟨hh.2.2.2.1,hh.2.2.2.2.2.1⟩
  obtain ⟨D,hD,hperm⟩ := demandEnum93_complete (rowOptions93 a) L 10 (a+7)
    (rowOptions93_sorted a) hp hL hs hq
  exact ⟨D,hD,hperm.subperm.trans hsub.subperm⟩

end Symconf93

#print axioms Symconf93.demandEnum93_complete
#print axioms Symconf93.rowDemand93_complete
