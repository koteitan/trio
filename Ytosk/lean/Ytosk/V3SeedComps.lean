/-
**始点の成分の条件は ◁ から出る（2026-10-21、lead）。**

t = 1・q = r の始点 seed = ψ_s(σ) ◁ o(r) = ψ_μ(b + Ω_{μ+1})（s < μ）で、段 a ≤ μ の成分はどれも b + seed より小さい
（ψ_a(b + Ω_{μ+1}) が標準形のとき）。行列の事実は使わない。HSeedV2（SeedR）が使う側に渡していた条件 hcs そのもの。

証明: 悪い成分 w（b + seed ≤ w）のうち大きさが最小のものを取る。
- ◁ を c = Ω_μ で使うと w ≤ (μ の成分) < b + Ω_{μ+1}（標準形の条件）。よって w = b + w₀、seed ≤ w₀ < Ω_{μ+1}（`app_between`）。
- w₀ の先頭の添字 k は s ≤ k ≤ μ。◁ を c = Ω_k（k > s）か Ω_{s+1}（k = s）で使うと、w ≤ y となる y が
  comps_a k（⊆ comps_a w）にある。y は w より小さい悪い成分で、最小性に反する。
-/
import Ytosk.V3SeedLhd

namespace Ytosk

open T

namespace SeedComps

/-- **Between two extensions of the same prefix**: `b + X ≤ w < b + Y` gives `w = b + w₀` with `X ≤ w₀ < Y`. -/
theorem app_between {X Y : T} : ∀ {b w : T}, app b X ≤ w → w < app b Y →
    ∃ w0, w = app b w0 ∧ X ≤ w0 ∧ w0 < Y
  | z, w, h1, h2 => ⟨w, by rw [app_z], by rwa [app_z] at h1, by rwa [app_z] at h2⟩
  | psi v x c, w, h1, h2 => by
    cases w with
    | z =>
      rw [app_psi] at h1
      rcases (le_iff _ _).mp h1 with h | h
      · exact absurd h (T.not_lt_z _)
      · exact absurd h (by simp)
    | psi v' x' c' =>
      rw [app_psi] at h1 h2
      rw [T.psi_lt_psi] at h2
      rcases (le_iff _ _).mp h1 with hl1 | he1
      · rw [T.psi_lt_psi] at hl1
        rcases hl1 with ha1 | ⟨rfl, hb1⟩ | ⟨rfl, rfl, hc1⟩
        · rcases h2 with ha2 | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
          · exact absurd (lt_trans ha1 ha2) (T.lt_irrefl' _)
          · exact absurd ha1 (T.lt_irrefl' _)
          · exact absurd ha1 (T.lt_irrefl' _)
        · rcases h2 with ha2 | ⟨_, hb2⟩ | ⟨_, rfl, _⟩
          · exact absurd ha2 (T.lt_irrefl' _)
          · exact absurd (lt_trans hb1 hb2) (T.lt_irrefl' _)
          · exact absurd hb1 (T.lt_irrefl' _)
        · rcases h2 with ha2 | ⟨_, hb2⟩ | ⟨_, _, hc2⟩
          · exact absurd ha2 (T.lt_irrefl' _)
          · exact absurd hb2 (T.lt_irrefl' _)
          · obtain ⟨w0, e, hX, hY⟩ := app_between (Or.inl hc1) hc2
            exact ⟨w0, by rw [e, app_psi], hX, hY⟩
      · simp only [psi.injEq] at he1
        obtain ⟨rfl, rfl, e⟩ := he1
        rcases h2 with ha2 | ⟨_, hb2⟩ | ⟨_, _, hc2⟩
        · exact absurd ha2 (T.lt_irrefl' _)
        · exact absurd hb2 (T.lt_irrefl' _)
        · obtain ⟨w0, e', hX, hY⟩ := app_between (Or.inr e) hc2
          exact ⟨w0, by rw [e', app_psi], hX, hY⟩

theorem z_lt_app_psi (b s σ : T) : z < app b (psi s σ z) := by
  cases b with
  | z => rw [app_z]; exact T.z_lt_psi _ _ _
  | psi => rw [app_psi]; exact T.z_lt_psi _ _ _

/-- The components of `Ω_k` at a level `a ≤ k`. -/
theorem comps_om {a k : T} (h : ¬ k < a) {y : T} (hy : y ∈ comps a (psi k z z) ++ Gc a z) :
    y = z ∨ y ∈ comps a k := by
  rw [comps_psi_z_of_ge h] at hy
  simp only [Gc, comps, List.mem_append, List.mem_cons, List.nil_append,
    List.not_mem_nil, or_false] at hy
  rcases hy with (rfl | hy) | rfl
  · exact Or.inl rfl
  · exact Or.inr hy
  · exact Or.inl rfl

theorem comps_succ {u t g : T} (h : g ∈ comps u (succ t)) : g = z ∨ g ∈ comps u t := by
  rw [succ, comps_app] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inr h
  · left
    simp only [one, comps] at h
    split at h <;> simp_all

theorem mem_comps_succ {u t g : T} (h : g ∈ comps u t) : g ∈ comps u (succ t) := by
  rw [succ, comps_app]; exact List.mem_append_left _ h

/-- The head subscript of a term in `[ψ_s(σ), Ω_{μ+1})` is between `s` and `μ`. -/
theorem head_sub_between {s σ μ k y c : T} (h1 : psi s σ z ≤ psi k y c) (h2 : psi k y c < psi (succ μ) z z) :
    s ≤ k ∧ k ≤ μ := by
  constructor
  · rcases (le_iff _ _).mp h1 with h | h
    · rw [T.psi_lt_psi] at h
      rcases h with h | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
      · exact le_of_lt h
      · exact le_refl _
      · exact le_refl _
    · simp only [psi.injEq] at h; rw [h.1]
  · rw [psi_lt_psi_z_iff] at h2
    rcases h2 with h | ⟨rfl, h⟩
    · exact lt_succ_iff.mp h
    · exact absurd h (T.not_lt_z _)

/-- **The seed condition from `◁`** (the `hcs` of `qr_final3`, without `SeedR`). -/
theorem seed_comps_lt {μ b s σ a : T}
    (hl : Lhd z (psi s σ z) (psi μ (app b (psi (succ μ) z z)) z))
    (hsμ : s < μ) (ha : ¬ μ < a)
    (hot : isOT (psi a (app b (psi (succ μ) z z)) z) = true) :
    ∀ g ∈ comps a (psi s σ z), g < app b (psi s σ z) := by
  set seed := psi s σ z with hseed
  set B1 := app b (psi (succ μ) z z) with hB1
  -- the components of `B1` are below `B1`
  have hB1c : ∀ g ∈ comps a B1, g < B1 := by
    intro g hg
    simp only [isOT, Bool.and_eq_true, List.all_eq_true] at hot
    exact hot.2 g hg
  have haμ : ¬ succ μ < a := fun h => ha (lt_trans (lt_succ_self μ) h)
  have hμB1 : ∀ y ∈ comps a μ, y ∈ comps a B1 := by
    intro y hy
    rw [hB1, comps_app]
    apply List.mem_append_right
    rw [comps_psi_z_of_ge haμ]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (mem_comps_succ hy))
  have hz : z < app b seed := z_lt_app_psi b s σ
  intro g hg
  -- an empty list when `s < a`
  by_cases hsa : s < a
  · have he : comps a seed = [] := by
      simp [hseed, comps, (lt_iff_lt s a).mp hsa]
    rw [he] at hg; simp at hg
  -- the minimal bad component
  have key : ∀ n, ∀ w, size w = n → w ∈ comps a seed → w < app b seed := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro w hwn hw
      by_contra hbad
      have hbw : app b seed ≤ w := not_lt.mp hbad
      -- `w` is below a component of `μ`, hence below `B1`
      have hseedμ : seed < psi μ z z := psi_lt_psi_z_iff.mpr (Or.inl hsμ)
      have hμle : psi μ z z ≤ psi μ B1 z := psi_le_psi_z (le_refl μ)
      obtain ⟨y0, hy0, hwy0⟩ := hl.2 a _ hseedμ hμle w hw
      rcases comps_om ha hy0 with rfl | hy0
      · exact absurd (lt_of_lt_of_le hz (le_trans hbw hwy0)) (T.lt_irrefl' _)
      have hwB : w < B1 := lt_of_le_of_lt hwy0 (hB1c y0 (hμB1 y0 hy0))
      obtain ⟨w0, rfl, hX, hY⟩ := app_between hbw hwB
      cases w0 with
      | z => exact absurd (lt_of_lt_of_le (T.z_lt_psi s σ z) hX) (T.lt_irrefl' _)
      | psi k y c =>
        obtain ⟨hsk, hkμ⟩ := head_sub_between hX hY
        have hka : ¬ k < a := fun h => hsa (lt_of_le_of_lt hsk h)
        -- the components of `k` are components of `w`
        have hkw : ∀ e ∈ comps a k, e ∈ comps a (app b (psi k y c)) := by
          intro e he
          rw [comps_app]
          apply List.mem_append_right
          simp only [comps, show lt k a = false by simpa [lt_iff_lt] using hka]
          simp only [Bool.false_eq_true, if_false, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr (Or.inr he))
        -- a larger component of `w` below `k`
        have hstep : ∃ e ∈ comps a k, app b (psi k y c) ≤ e := by
          rcases (le_iff _ _).mp hsk with hsk | rfl
          · have h1 : seed < psi k z z := psi_lt_psi_z_iff.mpr (Or.inl hsk)
            have h2 : psi k z z ≤ psi μ B1 z := psi_le_psi_z hkμ
            obtain ⟨e, he, hwe⟩ := hl.2 a _ h1 h2 _ hw
            rcases comps_om hka he with rfl | he
            · exact absurd (lt_of_lt_of_le hz (le_trans hbw hwe)) (T.lt_irrefl' _)
            · exact ⟨e, he, hwe⟩
          · have h1 : seed < psi (succ s) z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s))
            have h2 : psi (succ s) z z ≤ psi μ B1 z := psi_le_psi_z (succ_le_of_lt hsμ)
            have hsa' : ¬ succ s < a := fun h => hsa (lt_trans (lt_succ_self s) h)
            obtain ⟨e, he, hwe⟩ := hl.2 a _ h1 h2 _ hw
            rcases comps_om hsa' he with rfl | he
            · exact absurd (lt_of_lt_of_le hz (le_trans hbw hwe)) (T.lt_irrefl' _)
            rcases comps_succ he with rfl | he
            · exact absurd (lt_of_lt_of_le hz (le_trans hbw hwe)) (T.lt_irrefl' _)
            · exact ⟨e, he, hwe⟩
        obtain ⟨e, he, hwe⟩ := hstep
        have hew := hkw e he
        have hes : size e < n := by rw [← hwn]; exact size_comps hew
        have h := ih _ hes e rfl (comps_trans hw e hew)
        exact absurd (lt_of_lt_of_le h (le_trans hbw hwe)) (T.lt_irrefl' _)
  exact key _ g rfl hg

end SeedComps

end Ytosk
