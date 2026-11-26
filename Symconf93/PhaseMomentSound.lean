module
public import Symconf93.PhaseMomentCheck
public import Symconf93OffsetMoments
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Meaning of the discriminant-root Veto, independently of any
support catalogue coverage claim. The 35-record roster is proof data. -/
namespace Symconf93
open scoped BigOperators
open OffsetMoments

private theorem cast_first_offset (A B C : PhaseM31) :
    (firstOffset31 A B C:F)=tVal A.s B.s C.s := by
  unfold firstOffset31 tVal
  rw [ZMod.natCast_mod,Nat.cast_sub (Nat.mod_lt _ (by decide:0<31)).le]
  have hz : (31:F)=0 := by decide
  simp [hz,ZMod.natCast_mod]

private theorem cast_second_linear (A B C : PhaseM31) :
    (secondLinear31 A B C:F)=bVal B.s C.s (tVal A.s B.s C.s) := by
  simp [secondLinear31,ZMod.natCast_mod,cast_first_offset,bVal]

private theorem cast_second_constant (A B C : PhaseM31) :
    (secondConstant31 A B C:F)=dVal A.q B.q C.q C.s (tVal A.s B.s C.s) := by
  simp [secondConstant31,ZMod.natCast_mod,cast_first_offset,dVal,pow_two,mul_assoc]

private theorem disc_lt (A B C : PhaseM31) : discriminant31 A B C<31 :=
  Nat.mod_lt _ (by decide)

private theorem cast_disc (A B C : PhaseM31) :
    (discriminant31 A B C:F)=(secondLinear31 A B C:F)^2-88*(secondConstant31 A B C:F) := by
  have hsmall := Nat.mod_lt (88*secondConstant31 A B C) (by decide : 0<31)
  unfold discriminant31
  rw [ZMod.natCast_mod,Nat.cast_sub (by omega)]
  have hz : (31:F)=0 := by decide
  simp [Nat.cast_add,Nat.cast_mul,hz,ZMod.natCast_mod,pow_two]

private theorem cast_second_decode (A B C : PhaseM31) (r : Nat) :
    (decodedSecond31 A B C r:F)=12*((r:F)-(secondLinear31 A B C:F)) := by
  have h : secondLinear31 A B C<31 := Nat.mod_lt _ (by decide)
  unfold decodedSecond31
  rw [ZMod.natCast_mod,Nat.cast_mul,Nat.cast_sub (by omega)]
  have hz : (31:F)=0 := by decide
  simp [hz]

private theorem cast_third_decode (A B C : PhaseM31) (x : Nat) :
    (decodedThird31 A B C x:F)=tVal A.s B.s C.s+14*(x:F) := by
  simp [decodedThird31,ZMod.natCast_mod,cast_first_offset]

def thirdPoly31 (M : PhaseM31) (x : F) : F :=
  M.c+3*x*M.q+3*x^2*M.s+(M.n:F)*x^3

def fourthPoly31 (M : PhaseM31) (x : F) : F :=
  M.d+4*x*M.c+6*x^2*M.q+4*x^3*M.s+(M.n:F)*x^4

private theorem cast_third_poly (M : PhaseM31) (x : Nat) :
    (thirdShiftedM31 M x:F)=thirdPoly31 M x := by
  simp [thirdShiftedM31,thirdPoly31,ZMod.natCast_mod]
  ring

private theorem cast_fourth_poly (M : PhaseM31) (x : Nat) :
    (fourthShiftedM31 M x:F)=fourthPoly31 M x := by
  simp [fourthShiftedM31,fourthPoly31,ZMod.natCast_mod]
  ring

/-- Exactly the arithmetic necessary four moments, after normalizing the
first translation by one common choice of origin. -/
theorem phaseMomentVeto31_excludes (A B C : PhaseM31) (x y : F)
    (hcheck : phaseMomentVeto31 A B C=true)
    (h1 : (A.s:F)+B.s+C.s+15*x+10*y=0)
    (h2 : (A.q:F)+B.q+C.q+2*x*B.s+15*x^2+2*y*C.s+10*y^2=0)
    (h3 : (A.c:F)+thirdPoly31 B x+thirdPoly31 C y=0)
    (h4 : (A.d:F)+fourthPoly31 B x+fourthPoly31 C y=0) : False := by
  have hy := translate_first A.s B.s C.s x y h1
  have hquad := translate_second B.s C.s A.q B.q C.q _ _ _ hy h2
  rw [←cast_second_linear,←cast_second_constant] at hquad
  obtain ⟨r,hr,hx⟩ := discriminant_candidate _ _ _ hquad
  rw [←cast_disc] at hr
  have hr' : r.val*r.val%31=discriminant31 A B C := by
    have hh := congrArg ZMod.val hr
    simpa only [pow_two,ZMod.val_mul,ZMod.val_natCast_of_lt (disc_lt A B C)] using hh
  let b : Fin 31 := ⟨discriminant31 A B C,disc_lt A B C⟩
  let rIdx : Fin 31 := ⟨r.val,ZMod.val_lt r⟩
  have hm : r.val ∈ squareRoots31 (discriminant31 A B C) := by
    apply List.contains_iff_mem.mp
    have hh := squareRoot31_lookup b rIdx
    change (squareRoots31 (discriminant31 A B C)).contains r.val =
      decide (r.val*r.val%31=discriminant31 A B C) at hh
    rw [hh,decide_eq_true hr']
  let u := decodedSecond31 A B C r.val
  let v := decodedThird31 A B C u
  have hu : (u:F)=x := by
    dsimp only [u]
    rw [cast_second_decode,ZMod.natCast_zmod_val,←hx]
  have hv : (v:F)=y := by
    dsimp only [v]
    rw [cast_third_decode,hu,hy]
  have hh := List.all_eq_true.mp hcheck _ hm
  change (((A.c+thirdShiftedM31 B u+thirdShiftedM31 C v)%31 != 0) ||
    ((A.d+fourthShiftedM31 B u+fourthShiftedM31 C v)%31 != 0)) = true at hh
  have h3' : (A.c+thirdShiftedM31 B u+thirdShiftedM31 C v)%31=0 := by
    have hh : ((A.c+thirdShiftedM31 B u+thirdShiftedM31 C v:Nat):F)=0 := by
      simp only [Nat.cast_add,cast_third_poly,hu,hv,h3]
    have hz := congrArg ZMod.val hh
    simpa only [ZMod.val_natCast,ZMod.val_zero] using hz
  have h4' : (A.d+fourthShiftedM31 B u+fourthShiftedM31 C v)%31=0 := by
    have hh : ((A.d+fourthShiftedM31 B u+fourthShiftedM31 C v:Nat):F)=0 := by
      simp only [Nat.cast_add,cast_fourth_poly,hu,hv,h4]
    have hz := congrArg ZMod.val hh
    simpa only [ZMod.val_natCast,ZMod.val_zero] using hz
  simp [h3',h4'] at hh

end Symconf93

#print axioms Symconf93.phaseMomentVeto31_excludes
