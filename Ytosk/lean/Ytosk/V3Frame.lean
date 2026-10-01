/-
**3 行: D の呼び出しの枠の補題（項の側）。**

D の列の局所的な形は 4 つ（`desc.md`）。ここではそのうち項の言葉だけで書ける 3 つ:
- `frame_last`: 引数の最後の加数だけが fsD で変わる（2 行の `FrameD` をそのまま使う）。
- `frame_sub`: 引数が 0 で添字だけが fsD で変わる（Ω_v → Ω_{fsD v}）。
- `frame_upg`: v = 0 + last(V)、V は項 1 つ（v = V）。
和の中の 0（数えない子）は飛ばしてよい（`sumN_skip_z`）。
-/
import Ytosk.V3Dep
import Ytosk.TwoRowT
import Ytosk.SPFSD

namespace Ytosk

open T

/-! ## 和の中の 0 -/

/-- Drop the zero entries. -/
def nzs (l : List T) : List T := l.filter (fun t => decide (t ≠ z))

theorem foldl_skip_z : ∀ (l : List T) (acc : T), isOT acc = true → (∀ t ∈ l, t = z ∨ Single t) →
    (summands acc ++ nzs l).Pairwise (fun a b => b ≤ a) →
    l.foldl (fun a b => sf (add a b)) acc = (nzs l).foldl (fun a b => sf (add a b)) acc
  | [], _, _, _, _ => rfl
  | t :: l, acc, hacc, hs, hp => by
    rcases hs t List.mem_cons_self with rfl | ht
    · have hn : nzs (z :: l) = nzs l := by simp [nzs]
      rw [hn] at hp ⊢
      simp only [List.foldl_cons, add_z_right, sf_ot hacc]
      exact foldl_skip_z l acc hacc (fun t' h' => hs t' (List.mem_cons_of_mem _ h')) hp
    · have htz : t ≠ z := by obtain ⟨_, s, y, rfl⟩ := ht; simp
      have hn : nzs (t :: l) = t :: nzs l := by simp [nzs, htz]
      rw [hn] at hp ⊢
      simp only [List.foldl_cons]
      have h1 := foldl_dec [t] acc hacc (fun t' h' => by
        rw [List.mem_singleton] at h'; subst h'; exact ht)
        (by
          have := List.pairwise_append.mp hp
          rw [List.pairwise_append]
          refine ⟨this.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb; subst hb
          exact this.2.2 a ha _ List.mem_cons_self)
      simp only [List.foldl_cons, List.foldl_nil] at h1
      apply foldl_skip_z l _ h1.1 (fun t' h' => hs t' (List.mem_cons_of_mem _ h'))
      rw [h1.2, List.append_assoc]; exact hp

/-- **Zeros in a sum can be skipped**, when the rest is a non-increasing list of single summands. -/
theorem sumN_skip_z {l : List T} (hs : ∀ t ∈ l, t = z ∨ Single t)
    (hp : (nzs l).Pairwise (fun a b => b ≤ a)) : sumN l = sumN (nzs l) := by
  unfold sumN
  exact foldl_skip_z l z rfl hs (by simpa [summands] using hp)

/-! ## 正規化した ψ -/

theorem sf_psi_spArg {v S : T} (hv : isOT v = true) (hS : isOT S = true) :
    sf (psi v S z) = psi v (spArg v z S) z := by
  show add (sp (sf v) z (sf S)) (sf z) = _
  rw [sf_ot hv, sf_ot hS, sp_eq_spArg]
  rfl

/-- **The last summand changes.** -/
theorem frame_last {v ζ c c' : T} {l : List T} (hv : isOT v = true)
    (hs : ∀ t ∈ l ++ [c], Single t) (hp : (l ++ [c]).Pairwise (fun a b => b ≤ a))
    (hs' : Single c') (hp' : (l ++ [c']).Pairwise (fun a b => b ≤ a))
    (hc' : c' = fsD c ζ) (hF : FrameD v (spArg v z (sumN l)) c ζ) :
    fsD (sf (psi v (sumN (l ++ [c])) z)) ζ = sf (psi v (sumN (l ++ [c'])) z) := by
  have hs2 : ∀ t ∈ l ++ [c'], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hs t (List.mem_append_left _ ht)
    · rw [List.mem_singleton] at ht; subst ht; exact hs'
  have hS := sumN_dec _ hs hp
  have hS' := sumN_dec _ hs2 hp'
  rw [sf_psi_spArg hv hS.1, sf_psi_spArg hv hS'.1, sumN_snoc_dec hs hp, sumN_snoc_dec hs2 hp',
    spArg_app, spArg_app, node_fsD hF, hc']

/-- **Only the subscript changes**: `Ω_v → Ω_{fsD v}`. -/
theorem frame_sub {v ζ : T} (hv : isOT v = true) (hv' : isOT (fsD v ζ) = true) (hz : v ≠ z)
    (hsu : isSucc v = false) :
    fsD (sf (psi v z z)) ζ = sf (psi (fsD v ζ) z z) := by
  have h1 : isOT (psi v z z) = true := by
    rw [isOT_psi_iff]; exact ⟨hv, rfl, rfl, z_le _, by simp [comps]⟩
  have h2 : isOT (psi (fsD v ζ) z z) = true := by
    rw [isOT_psi_iff]; exact ⟨hv', rfl, rfl, z_le _, by simp [comps]⟩
  rw [sf_ot h1, sf_ot h2]
  conv => lhs; unfold fsD
  rw [if_pos rfl, if_neg hz, if_neg (by rw [hsu]; simp)]

/-- **The upgrade case**: `v = 0 + last(V)` with `V` a single summand. -/
theorem frame_upg {V ζ : T} (hV : Single V) (hV' : Single (fsD V ζ)) :
    fsD (sf (add z (last V))) ζ = sf (add z (last (fsD V ζ))) := by
  obtain ⟨h1, s, y, rfl⟩ := hV
  obtain ⟨h2, s', y', h'⟩ := hV'
  rw [h'] at h2 ⊢
  simp only [add_z_left, last]
  rw [sf_ot h1, sf_ot h2, h']

end Ytosk
