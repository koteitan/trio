/-
**WfQrH4 (2026-11-01): the `ω` layer step reduced to the single-summand case.**
An `ω` layer `Y → Y_N` (`DQ η true Y Y_N`) needs no shape hypothesis when both are below `ε₀` (`omega_DQ_small`)
or when both are `≥ ε₀` and `Y` has more than one summand (`omega_DQ_rest`).  `LayerF` adds these two cases to
`LayerOK`; `layer_step` and `bumpW_DQ3` are `layer_DQ` / `bumpW_DQ2` (WfQrL16) with `LayerF`.
-/
import Ytosk.WfQrL17

namespace Ytosk.WfQrH4
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL2 Ytosk.WfQrL13 Ytosk.WfQrL16 Ytosk.WfQrL17

/-- The layer fields: small, multi-summand, or one of the three shapes of `LayerOK`. -/
def LayerF (Y YN : T) : Prop :=
  (Y < E0 ∧ YN < E0) ∨
  (isOT Y = true ∧ isOT YN = true ∧ ¬ Y < E0 ∧ ¬ YN < E0 ∧ ∃ a b c, Y = psi a b c ∧ c ≠ z) ∨
  LayerOK Y YN

/-- **An `ω` layer step from `LayerF`.** -/
theorem layer_step {Y YN : T} (hd : ∃ η, DQ η true Y YN) (h : LayerF Y YN) :
    ∃ η', DQ η' false (omega Y) (omega YN) := by
  obtain ⟨η, hη⟩ := hd
  rcases h with ⟨h1, h2⟩ | ⟨hY, hYN, h1, h2, a, b, c, rfl, hc⟩ | h
  · exact ⟨η, omega_DQ_small h1 h2 hη⟩
  · exact ⟨η, omega_DQ_rest hc hY hYN h1 h2 hη⟩
  · exact layer_DQ ⟨η, hη⟩ h

/-- **The bump term, two `ω` layers, each with `LayerF`.** -/
theorem bumpW_DQ3 {P0 K0 ok oN : T} (hok : ∃ s y, ok = psi s y z) (hd : ∃ η, DQ η false ok oN)
    (hG : isOT (app K0 ok) = true)
    (L1 : LayerF (app K0 ok) (app K0 oN))
    (L2 : LayerF (app P0 (omega (app K0 ok))) (app P0 (omega (app K0 oN)))) :
    ∃ η', DQ η' false (omega (app P0 (omega (app K0 ok)))) (omega (app P0 (omega (app K0 oN)))) := by
  obtain ⟨η, hη⟩ := hd
  obtain ⟨η1, d2⟩ := layer_step ⟨η, DQ.snoc K0 hok hη⟩ L1
  have hs : ∃ s y, omega (app K0 ok) = psi s y z := (single_omega hG).2
  exact layer_step ⟨η1, DQ.snoc P0 hs d2⟩ L2

/-- **The bump step of the engine from the two layer shapes** (`hBW2` of `qr_engineDQ2`). -/
theorem bump_step3 {M : Mat} {ρ : Valn} {i j k : Nat} {L K : List Nat} {oN : T}
    (hch : children M i = L ++ [j]) (hjb : col M j = bump M i) (hchj : children M j = K ++ [k])
    (hok : ∃ s y, ρ.o k = psi s y z)
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
    (hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t) (hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a))
    (hsK' : ∀ t ∈ K.map ρ.o ++ [oN], Single t) (hpK' : (K.map ρ.o ++ [oN]).Pairwise (fun a b => b ≤ a))
    (hpp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise (fun a b => b ≤ a))
    (hgt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t)
    (hpp' : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [oN]))]).Pairwise (fun a b => b ≤ a))
    (hgt' : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [oN]))], one < t)
    (L1 : LayerF (app (sumN (K.map ρ.o)) (ρ.o k)) (app (sumN (K.map ρ.o)) oN))
    (L2 : LayerF (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (app (sumN (K.map ρ.o)) (ρ.o k))))
      (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (app (sumN (K.map ρ.o)) oN))))
    (hd : ∃ η, DQ η false (ρ.o k) oN) :
    ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L K oN) := by
  rw [bumpW_eq_bumpWQ hch hjb hchj, bumpWQ_app hsL hsK hpK hpp hgt, bumpWQ_app hsL hsK' hpK' hpp' hgt']
  have hG : isOT (app (sumN (K.map ρ.o)) (ρ.o k)) = true := by
    rw [← sumN_snoc_dec hsK hpK]; exact (sumN_dec _ hsK hpK).1
  exact bumpW_DQ3 hok hd hG L1 L2

end Ytosk.WfQrH4
