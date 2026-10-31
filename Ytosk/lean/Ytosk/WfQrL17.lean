/-
**WfQrL17 (2026-11-01): the bump term in sum form, and the bump step of the DQ engine from its shapes.**

`bumpW M ρ i = bumpWQ M ρ i L K (o(k))` (`bumpW_eq_bumpWQ`); under the list conditions of `VLocZ` (singles,
decreasing, `> 1`) `bumpWQ M ρ i L K oK = ω^{P + ω^{K + oK}}` (`bumpWQ_app`).  With `WfQrL16.bumpW_DQ2` this gives
the hypothesis `hBW2` of `qr_engineDQ2` from the two `ω`-layer shapes (`bump_step`).
-/
import Ytosk.WfQrL16
import Ytosk.V3Bump

namespace Ytosk.WfQrL17
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL2 Ytosk.WfQrL16

theorem bumpW_eq_bumpWQ {M : Mat} {ρ : Valn} {i j k : Nat} {L K : List Nat}
    (hch : children M i = L ++ [j]) (hjb : col M j = bump M i) (hchj : children M j = K ++ [k]) :
    bumpW M ρ i = bumpWQ M ρ i L K (ρ.o k) := by
  unfold bumpW bumpWQ
  rw [hch, List.map_append, List.map_singleton]
  have : bumpTerm M ρ i j = omega (sumN (K.map ρ.o ++ [ρ.o k])) := by
    unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
  rw [this]

/-- **The bump term in sum form.** -/
theorem bumpWQ_app {M : Mat} {ρ : Valn} {i : Nat} {L K : List Nat} {oK : T}
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
    (hsK : ∀ t ∈ K.map ρ.o ++ [oK], Single t) (hpK : (K.map ρ.o ++ [oK]).Pairwise (fun a b => b ≤ a))
    (hpp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [oK]))]).Pairwise (fun a b => b ≤ a))
    (hgt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [oK]))], one < t) :
    bumpWQ M ρ i L K oK =
      omega (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (app (sumN (K.map ρ.o)) oK))) := by
  set G := sumN (K.map ρ.o ++ [oK]) with hGdef
  have hGot : isOT G = true := (sumN_dec _ hsK hpK).1
  have hGapp : G = app (sumN (K.map ρ.o)) oK := sumN_snoc_dec hsK hpK
  have hsG := single_omega hGot
  have hsl : ∀ t ∈ L.map (bumpTerm M ρ i) ++ [omega G], t = z ∨ Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsL t ht
    · rw [List.mem_singleton] at ht; subst ht; exact Or.inr hsG
  have hnz : nzs (L.map (bumpTerm M ρ i) ++ [omega G]) = nzs (L.map (bumpTerm M ρ i)) ++ [omega G] := by
    rw [nzs_append, nzs_single (single_ne_z hsG)]
  have hsP : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega G], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · simp only [nzs, List.mem_filter] at ht
      rcases hsL t ht.1 with h | h
      · exact absurd h (by simpa using ht.2)
      · exact h
    · rw [List.mem_singleton] at ht; subst ht; exact hsG
  unfold bumpWQ
  rw [← hGdef, sumN_one_cons hsl (by rw [hnz]; exact hpp) (by rw [hnz]; exact hgt) (by rw [hnz]; simp), hnz,
    sumN_snoc_dec hsP hpp, ← hGapp]

/-- **The bump step of the engine from the two layer shapes** (`hBW2` of `qr_engineDQ2`). -/
theorem bump_step {M : Mat} {ρ : Valn} {i j k : Nat} {L K : List Nat} {oN : T}
    (hch : children M i = L ++ [j]) (hjb : col M j = bump M i) (hchj : children M j = K ++ [k])
    (hok : ∃ s y, ρ.o k = psi s y z)
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
    (hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t) (hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a))
    (hsK' : ∀ t ∈ K.map ρ.o ++ [oN], Single t) (hpK' : (K.map ρ.o ++ [oN]).Pairwise (fun a b => b ≤ a))
    (hpp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise (fun a b => b ≤ a))
    (hgt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t)
    (hpp' : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [oN]))]).Pairwise (fun a b => b ≤ a))
    (hgt' : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [oN]))], one < t)
    (L1 : LayerOK (app (sumN (K.map ρ.o)) (ρ.o k)) (app (sumN (K.map ρ.o)) oN))
    (L2 : LayerOK (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (app (sumN (K.map ρ.o)) (ρ.o k))))
      (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (app (sumN (K.map ρ.o)) oN))))
    (hd : ∃ η, DQ η false (ρ.o k) oN) :
    ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L K oN) := by
  rw [bumpW_eq_bumpWQ hch hjb hchj, bumpWQ_app hsL hsK hpK hpp hgt, bumpWQ_app hsL hsK' hpK' hpp' hgt']
  have hG : isOT (app (sumN (K.map ρ.o)) (ρ.o k)) = true := by
    rw [← sumN_snoc_dec hsK hpK]; exact (sumN_dec _ hsK hpK).1
  exact bumpW_DQ2 hok hd hG L1 L2

end Ytosk.WfQrL17
