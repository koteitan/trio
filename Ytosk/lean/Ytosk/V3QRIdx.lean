/-
**3 行・t = 1・q = r: 列ごとの添字（引き上げの数）。**

D の各呼び出しに「葉 x からの引き上げの数 d」を付けた帰納的な述語 `DepL`（引き上げの量は o の枠で lo i c、
のりしろの枠で lb i j k、どちらも抽象）。D の各呼び出しは D の中の直前の呼び出しが 1 つだけ（`OShape`・
v の形）なので d は一意（`depL_unique`）。列ごとの d を `dOf` とおく（o と v で同じ: o が v に依存するのは
添字だけ変わる枠で、引き上げはない）。
-/
import Ytosk.V3QRPath

namespace Ytosk

open T

/-- `D` with the number of lifts from the leaf. -/
inductive DepL (M : Mat) (x : Nat) (lo : Nat → Nat → Nat) (lb : Nat → Nat → Nat → Nat) :
    Bool → Nat → Nat → Prop
  | leaf : DepL M x lo lb true x 0
  | ochild {i c d : Nat} : c ∈ children M i → col M c ≠ bump M i →
      ¬ (isUpg M c = true ∧ topped M c = true) → DepL M x lo lb true c d →
      DepL M x lo lb true i (d + lo i c)
  | ov {i d : Nat} : DepL M x lo lb false i d → DepL M x lo lb true i d
  | vpar {i m d : Nat} : entry M 1 i ≠ 0 → par M 1 i = some m → DepL M x lo lb false m d →
      DepL M x lo lb false i d
  | vupg {i k d : Nat} : entry M 1 i ≠ 0 → entry M 2 i = 0 → upg M i = some k →
      DepL M x lo lb false k d → DepL M x lo lb false i d
  | vbump {i j k d : Nat} : entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i →
      col M j = bump M i → k ∈ children M j → DepL M x lo lb true k d →
      DepL M x lo lb false i (d + lb i j k)

/-- The shape of a `v` call in `D` (`dv_shape`). -/
def VShape (M : Mat) (x i : Nat) : Prop :=
  entry M 1 i ≠ 0 ∧ (∀ m, par M 1 i = some m → ¬ DepX M x false m) ∧
    ((entry M 2 i = 0 ∧ upg M i = some (i + 1) ∧ i + 1 < x ∧ DepX M x false (i + 1)) ∨
     (entry M 2 i ≠ 0 ∧ ∃ L K j k, children M i = L ++ [j] ∧ col M j = bump M i ∧
        children M j = K ++ [k] ∧ DepX M x true k ∧ (∀ d ∈ K, ¬ DepX M x true d) ∧
        (∀ d ∈ L, ∀ e ∈ children M d, e < x ∧ ¬ DepX M x true e)))

section
variable {M : Mat} {x : Nat} {lo : Nat → Nat → Nat} {lb : Nat → Nat → Nat → Nat}

theorem depX_of_depL {b : Bool} {i d : Nat} (h : DepL M x lo lb b i d) : DepX M x b i := by
  induction h with
  | leaf => exact DepX.leaf
  | ochild hc hcb hcu _ ih => exact DepX.ochild hc hcb hcu ih
  | ov _ ih => exact DepX.ov ih
  | vpar h1 hp _ ih => exact DepX.vpar h1 hp ih
  | vupg h1 h2 hu _ ih => exact DepX.vupg h1 h2 hu ih
  | vbump h1 h2 hj hjb hk _ ih => exact DepX.vbump h1 h2 hj hjb hk ih

theorem depL_of_depX {b : Bool} {i : Nat} (h : DepX M x b i) : ∃ d, DepL M x lo lb b i d := by
  induction h with
  | leaf => exact ⟨0, DepL.leaf⟩
  | ochild hc hcb hcu _ ih => obtain ⟨d, hd⟩ := ih; exact ⟨_, DepL.ochild hc hcb hcu hd⟩
  | ov _ ih => obtain ⟨d, hd⟩ := ih; exact ⟨_, DepL.ov hd⟩
  | vpar h1 hp _ ih => obtain ⟨d, hd⟩ := ih; exact ⟨_, DepL.vpar h1 hp hd⟩
  | vupg h1 h2 hu _ ih => obtain ⟨d, hd⟩ := ih; exact ⟨_, DepL.vupg h1 h2 hu hd⟩
  | vbump h1 h2 hj hjb hk _ ih => obtain ⟨d, hd⟩ := ih; exact ⟨_, DepL.vbump h1 h2 hj hjb hk hd⟩

variable (hx : x + 1 = M.length) (hxv : ¬ DepX M x false x)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
include hx hxv hOS hVS

omit hx hxv hVS in
/-- The `D` counted child of an `o` call in the last-child shape is the last counted child. -/
theorem ochild_unique {i c c' : Nat} (hi : i < x) (hD : DepX M x true i)
    (hc : c ∈ children M i) (hcb : col M c ≠ bump M i) (hcu : ¬ (isUpg M c = true ∧ topped M c = true))
    (hdc : DepX M x true c)
    (hc' : c' ∈ children M i) (hcb' : col M c' ≠ bump M i)
    (hcu' : ¬ (isUpg M c' = true ∧ topped M c' = true)) (hdc' : DepX M x true c') : c = c' := by
  rcases hOS i hi hD with ⟨_, hnc⟩ | ⟨_, L, e, R, hch, _, _, hR, hLnd⟩
  · exact absurd (hnc c hc) (by rintro (h | h); exact hcb h; exact hcu h)
  · have key : ∀ d, d ∈ children M i → col M d ≠ bump M i →
        ¬ (isUpg M d = true ∧ topped M d = true) → DepX M x true d → d = e := by
      intro d hd hdb hdu hdd
      rw [hch] at hd
      rcases List.mem_append.mp hd with h | h
      · exact absurd hdd (hLnd d h ⟨hdb, hdu⟩)
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · rcases hR d h with h' | h'
          · exact absurd h' hdb
          · exact absurd h' hdu
    rw [key c hc hcb hcu hdc, key c' hc' hcb' hcu' hdc']

omit hx hxv hOS in
/-- The bump child and its `D` child are unique. -/
theorem vbump_unique {i j k j' k' : Nat} (hi : i < x) (hD : DepX M x false i) (h2 : entry M 2 i ≠ 0)
    (hj : j ∈ children M i) (_hjb : col M j = bump M i) (hk : k ∈ children M j) (hdk : DepX M x true k)
    (hj' : j' ∈ children M i) (_hjb' : col M j' = bump M i) (hk' : k' ∈ children M j')
    (hdk' : DepX M x true k') : j = j' ∧ k = k' := by
  obtain ⟨_, _, hcase⟩ := hVS i hi hD
  rcases hcase with ⟨h2', _⟩ | ⟨_, L, K, j0, k0, hch, _, hchj, _, hKnd, hLnd⟩
  · exact absurd h2' h2
  · have keyj : ∀ a b, a ∈ children M i → b ∈ children M a → DepX M x true b → a = j0 := by
      intro a b ha hb hdb
      rw [hch] at ha
      rcases List.mem_append.mp ha with h | h
      · exact absurd hdb (hLnd a h b hb).2
      · exact List.mem_singleton.mp h
    have hjj := keyj j k hj hk hdk
    have hjj' := keyj j' k' hj' hk' hdk'
    have keyk : ∀ b, b ∈ children M j0 → DepX M x true b → b = k0 := by
      intro b hb hdb
      rw [hchj] at hb
      rcases List.mem_append.mp hb with h | h
      · exact absurd hdb (hKnd b h)
      · exact List.mem_singleton.mp h
    rw [hjj] at hk; rw [hjj'] at hk'
    exact ⟨by rw [hjj, hjj'], by rw [keyk k hk hdk, keyk k' hk' hdk']⟩

/-- **The number of lifts is unique.** -/
theorem depL_unique {b : Bool} {i d₁ : Nat} (h₁ : DepL M x lo lb b i d₁) :
    i ≤ x → ∀ d₂, DepL M x lo lb b i d₂ → d₁ = d₂ := by
  induction h₁ with
  | leaf =>
    intro _ d₂ h₂
    cases h₂ with
    | leaf => rfl
    | ochild hc _ _ _ =>
      have := mem_children hc; omega
    | ov hv => exact absurd (depX_of_depL hv) hxv
  | @ochild i c d hc hcb hcu hd ih =>
    intro hix d₂ h₂
    have hcm := mem_children hc
    have hi : i < x := by omega
    have hDi : DepX M x true i := DepX.ochild hc hcb hcu (depX_of_depL hd)
    cases h₂ with
    | leaf => omega
    | ochild hc' hcb' hcu' hd' =>
      have hcc := ochild_unique hOS hi hDi hc hcb hcu (depX_of_depL hd) hc' hcb' hcu' (depX_of_depL hd')
      subst hcc
      rw [ih (by omega) _ hd']
    | ov hv =>
      rcases hOS i hi hDi with ⟨_, hnc⟩ | ⟨hnv, _⟩
      · exact absurd (hnc c hc) (by rintro (h | h); exact hcb h; exact hcu h)
      · exact absurd (depX_of_depL hv) hnv
  | @ov i d hv ih =>
    intro hix d₂ h₂
    cases h₂ with
    | leaf => exact absurd (depX_of_depL hv) hxv
    | ov hv' => exact ih hix _ hv'
    | ochild hc hcb hcu hd =>
      have hcm := mem_children hc
      have hi : i < x := by omega
      rcases hOS i hi (DepX.ov (depX_of_depL hv)) with ⟨_, hnc⟩ | ⟨hnv, _⟩
      · exact absurd (hnc _ hc) (by rintro (h | h); exact hcb h; exact hcu h)
      · exact absurd (depX_of_depL hv) hnv
  | @vpar i m d h1 hp hd ih =>
    intro hix d₂ h₂
    have hDi : DepX M x false i := DepX.vpar h1 hp (depX_of_depL hd)
    have hi : i < x := by
      rcases Nat.lt_or_ge i x with h | h
      · exact h
      · exact absurd (by rw [show i = x by omega] at hDi; exact hDi) hxv
    exact absurd (depX_of_depL hd) ((hVS i hi hDi).2.1 m hp)
  | @vupg i k d h1 h2 hu hd ih =>
    intro hix d₂ h₂
    have hDi : DepX M x false i := DepX.vupg h1 h2 hu (depX_of_depL hd)
    have hi : i < x := by
      rcases Nat.lt_or_ge i x with h | h
      · exact h
      · exact absurd (by rw [show i = x by omega] at hDi; exact hDi) hxv
    obtain ⟨_, hpd, hcase⟩ := hVS i hi hDi
    have hk : k ≤ x := by
      rcases hcase with ⟨_, hu', hlt, _⟩ | ⟨h2', _⟩
      · rw [hu] at hu'; cases hu'; omega
      · exact absurd h2 h2'
    cases h₂ with
    | vpar _ hp hd' => exact absurd (depX_of_depL hd') (hpd _ hp)
    | vupg _ _ hu' hd' =>
      rw [hu] at hu'; cases hu'
      exact ih hk _ hd'
    | vbump _ h2' _ _ _ _ => exact absurd h2 h2'
  | @vbump i j k d h1 h2 hj hjb hk hd ih =>
    intro hix d₂ h₂
    have hDi : DepX M x false i := DepX.vbump h1 h2 hj hjb hk (depX_of_depL hd)
    have hi : i < x := by
      rcases Nat.lt_or_ge i x with h | h
      · exact h
      · exact absurd (by rw [show i = x by omega] at hDi; exact hDi) hxv
    have hkx : k ≤ x := by have := mem_children hk; omega
    cases h₂ with
    | vpar _ hp hd' => exact absurd (depX_of_depL hd') ((hVS i hi hDi).2.1 _ hp)
    | vupg _ h2' _ _ => exact absurd h2' h2
    | vbump _ _ hj' hjb' hk' hd' =>
      obtain ⟨hjj, hkk⟩ := vbump_unique hVS hi hDi h2 hj hjb hk (depX_of_depL hd) hj' hjb' hk'
        (depX_of_depL hd')
      subst hjj; subst hkk
      rw [ih hkx _ hd']

end

open Classical in
/-- The number of lifts of a column (that of its `v` call if it is in `D`, else that of its `o` call). -/
noncomputable def dOf (M : Mat) (x : Nat) (lo : Nat → Nat → Nat) (lb : Nat → Nat → Nat → Nat)
    (i : Nat) : Nat :=
  if h : ∃ d, DepL M x lo lb false i d then Nat.find h
  else if h' : ∃ d, DepL M x lo lb true i d then Nat.find h' else 0

section
variable {M : Mat} {x : Nat} {lo : Nat → Nat → Nat} {lb : Nat → Nat → Nat → Nat}
  (hx : x + 1 = M.length) (hxv : ¬ DepX M x false x)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
include hx hxv hOS hVS

theorem dOf_v {i d : Nat} (hi : i ≤ x) (h : DepL M x lo lb false i d) : dOf M x lo lb i = d := by
  classical
  have he : ∃ d, DepL M x lo lb false i d := ⟨d, h⟩
  unfold dOf
  rw [dif_pos he]
  exact depL_unique hx hxv hOS hVS (Nat.find_spec he) hi d h

theorem dOf_o {i d : Nat} (hi : i ≤ x) (h : DepL M x lo lb true i d) : dOf M x lo lb i = d := by
  classical
  by_cases he : ∃ d, DepL M x lo lb false i d
  · obtain ⟨d', hd'⟩ := he
    rw [dOf_v hx hxv hOS hVS hi hd']
    exact depL_unique hx hxv hOS hVS (DepL.ov hd') hi d h
  · have he' : ∃ d, DepL M x lo lb true i d := ⟨d, h⟩
    unfold dOf
    rw [dif_neg he, dif_pos he']
    exact depL_unique hx hxv hOS hVS (Nat.find_spec he') hi d h

theorem dOf_x : dOf M x lo lb x = 0 := dOf_o hx hxv hOS hVS (le_refl _) DepL.leaf

/-- The `o` frame: the child's lifts plus the frame's. -/
theorem dOf_ochild {i c : Nat} (hc : c ∈ children M i) (hcb : col M c ≠ bump M i)
    (hcu : ¬ (isUpg M c = true ∧ topped M c = true)) (hdc : DepX M x true c) :
    dOf M x lo lb i = dOf M x lo lb c + lo i c := by
  have hcm := mem_children hc
  obtain ⟨d, hd⟩ := depL_of_depX (lo := lo) (lb := lb) hdc
  rw [dOf_o hx hxv hOS hVS (by omega) (DepL.ochild hc hcb hcu hd), dOf_o hx hxv hOS hVS (by omega) hd]

/-- The upgrade frame: the same lifts. -/
theorem dOf_upg {i k : Nat} (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i = 0)
    (hu : upg M i = some k) (hk : k ≤ x) (hdk : DepX M x false k) :
    dOf M x lo lb i = dOf M x lo lb k := by
  obtain ⟨d, hd⟩ := depL_of_depX (lo := lo) (lb := lb) hdk
  rw [dOf_v hx hxv hOS hVS (by omega) (DepL.vupg h1 h2 hu hd), dOf_v hx hxv hOS hVS hk hd]

/-- The bump frame: the child's lifts plus the frame's. -/
theorem dOf_bump {i j k : Nat} (hi : i < x) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hj : j ∈ children M i) (hjb : col M j = bump M i) (hk : k ∈ children M j)
    (hdk : DepX M x true k) :
    dOf M x lo lb i = dOf M x lo lb k + lb i j k := by
  have hkm := mem_children hk
  obtain ⟨d, hd⟩ := depL_of_depX (lo := lo) (lb := lb) hdk
  rw [dOf_v hx hxv hOS hVS (by omega) (DepL.vbump h1 h2 hj hjb hk hd),
    dOf_o hx hxv hOS hVS (by omega) hd]

end

end Ytosk
