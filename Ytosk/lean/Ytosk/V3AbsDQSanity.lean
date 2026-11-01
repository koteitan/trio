/- Positive local DQ witnesses on both absorption counterexamples.
These are sanity checks at the actual failing columns, not a global engine. -/
import Ytosk.V3T0AbsFalse
import Ytosk.V3T2AbsXFalse
namespace Ytosk.AbsDQSanity
open T
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def t0 : T := psi z z z
private def t1 : T := psi z t0 z
private def t2 : T := psi t1 t0 z
private def t3 : T := psi t0 z z
private def t4 : T := psi t1 z t3
private def t5 : T := psi t1 t2 z
private def t6 : T := psi t1 t4 z
private def t7 : T := psi t1 t5 z
private def t8 : T := psi t1 t6 z
private def t9 : T := psi t1 t7 z
private def t10 : T := psi t1 t8 z
private def t11 : T := psi z z t0
private def t12 : T := psi z z t11
private def t13 : T := psi z t12 z
private def t14 : T := psi t13 z z
private def t15 : T := psi z t14 z
private def t16 : T := psi t1 z t15
private def t17 : T := psi t1 z t16
private def t18 : T := psi t1 t17 z
private def t19 : T := psi t1 t18 z
private def t20 : T := psi t1 t19 z
private def t21 : T := psi t1 t19 t10
private def t22 : T := psi t9 z z
private def t23 : T := psi t21 z z
private def t24 : T := psi z t0 t1
private def t25 : T := psi t24 z z
private def t26 : T := psi z t0 t0
private def t27 : T := psi t26 z z
private def t28 : T := psi t1 t25 z
private def t29 : T := psi t1 t27 z
private def t30 : T := psi z t11 z
private def t31 : T := psi t30 z z
private def t32 : T := psi z t31 z
private def t33 : T := psi t26 z t32
private def t34 : T := psi t1 t33 z
private def t35 : T := psi t26 z t34
private def t36 : T := psi t1 t35 z
private def t37 : T := psi t26 z t36
private def t38 : T := psi t1 t37 z
private def t39 : T := psi t1 t37 t29
private def t40 : T := psi t28 z z
private def t41 : T := psi t39 z z
theorem t0_v : DQ z true (T0AbsFalse.ρ.v 34) (T0AbsFalse.σ.v 34) := by
  change DQ z true t9 t21
  exact (DQ.mk (B := z) (l := t9) (lN := t10) (Q := t20) rfl (DQ.arg (DQ.mk (B := z) (l := t7) (lN := t8) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t5) (lN := t6) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t2) (lN := z) (Q := t4) rfl (by have h := DQ.base (η := z) (l := t2) (by decide); have he : fsD t2 z = z := (by decide); simpa only [he] using h) (by decide))) (by decide))) (by decide))) (by decide))

theorem t0_o : DQ z false (T0AbsFalse.ρ.o 34) (T0AbsFalse.σ.o 34) := by
  change DQ z false t22 t23
  exact (DQ.sub (DQ.mk (B := z) (l := t9) (lN := t10) (Q := t20) rfl (DQ.arg (DQ.mk (B := z) (l := t7) (lN := t8) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t5) (lN := t6) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t2) (lN := z) (Q := t4) rfl (by have h := DQ.base (η := z) (l := t2) (by decide); have he : fsD t2 z = z := (by decide); simpa only [he] using h) (by decide))) (by decide))) (by decide))) (by decide)))

theorem t0_W : DQ z false (bumpW T0AbsFalse.M T0AbsFalse.ρ 34) (bumpW T0AbsFalse.N T0AbsFalse.σ 34) := by
  change DQ z false t9 t10
  exact (DQ.arg (DQ.mk (B := z) (l := t7) (lN := t8) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t5) (lN := t6) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t2) (lN := z) (Q := t4) rfl (by have h := DQ.base (η := z) (l := t2) (by decide); have he : fsD t2 z = z := (by decide); simpa only [he] using h) (by decide))) (by decide))) (by decide)))

theorem t2_v : DQ z true (T2AbsXFalse.ρ.v 37) (T2AbsXFalse.σ.v 37) := by
  change DQ z true t28 t39
  exact (DQ.mk (B := z) (l := t28) (lN := t29) (Q := t38) rfl (DQ.arg (DQ.mk (B := z) (l := t25) (lN := t27) (Q := z) rfl (DQ.sub (DQ.mk (B := t1) (l := t1) (lN := t0) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t0) (lN := z) (Q := z) rfl (by have h := DQ.base (η := z) (l := t0) (by decide); have he : fsD t0 z = z := (by decide); simpa only [he] using h) (by decide))) (by decide))) (by decide))) (by decide))

theorem t2_o : DQ z false (T2AbsXFalse.ρ.o 37) (T2AbsXFalse.σ.o 37) := by
  change DQ z false t40 t41
  exact (DQ.sub (DQ.mk (B := z) (l := t28) (lN := t29) (Q := t38) rfl (DQ.arg (DQ.mk (B := z) (l := t25) (lN := t27) (Q := z) rfl (DQ.sub (DQ.mk (B := t1) (l := t1) (lN := t0) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t0) (lN := z) (Q := z) rfl (by have h := DQ.base (η := z) (l := t0) (by decide); have he : fsD t0 z = z := (by decide); simpa only [he] using h) (by decide))) (by decide))) (by decide))) (by decide)))

theorem t2_W : DQ z false (bumpW T2AbsXFalse.M T2AbsXFalse.ρ 37) (bumpW T2AbsXFalse.N T2AbsXFalse.σ 37) := by
  change DQ z false t28 t29
  exact (DQ.arg (DQ.mk (B := z) (l := t25) (lN := t27) (Q := z) rfl (DQ.sub (DQ.mk (B := t1) (l := t1) (lN := t0) (Q := z) rfl (DQ.arg (DQ.mk (B := z) (l := t0) (lN := z) (Q := z) rfl (by have h := DQ.base (η := z) (l := t0) (by decide); have he : fsD t0 z = z := (by decide); simpa only [he] using h) (by decide))) (by decide))) (by decide)))

end Ytosk.AbsDQSanity
