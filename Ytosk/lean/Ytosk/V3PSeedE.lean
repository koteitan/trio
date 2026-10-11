/-
**種の状態の形から Fix を出す（closure、2026-10-11）。**

σ = σ_{V,V′}（t = 2 の置き換え）。種の状態 B（M.take x での r の引数）は、実測（deepA・d3s・deep3、例外 0）で
σ で動かないか、右端の 1 か所の「目印」Ω_{V′} だけで σ に動かされる。その位置への道は cutsNS の文法に沿う:
- `SpotC`: 添字の鎖 Ω_{V′}、Ω_{Ω_{V′}}、…（純粋な Ω の鎖）。
- `SpotH`: 引数の中（cutsH の文法）。目印そのもの、または σ で動かない前の項 ＋ 後ろ、または添字が V′ 以上で
  f で動かない項の引数の中。
- `SpotN`: 状態の段（cutsNS の文法）。前の項 ＋ 後ろ、先頭の項 Ω_a（a は添字の鎖）、または引数の中。
`fix_of_spotN`: SpotN B なら B ∈ cutsNS V′ (σ B)（V3PSeedO の Fix の後半）。
-/
import Ytosk.V3PSeedO

namespace Ytosk

open T

section
variable (V V' : T)

/-- The subscript chain ending at the mark `Ω_{V′}`. -/
inductive SpotC : T → Prop
  | mark : SpotC (psi V' z z)
  | up {u : T} : SpotC u → SpotC (psi u z z)

/-- The mark at the right end, inside an argument (`cutsH` grammar). -/
inductive SpotH : T → Prop
  | mark : SpotH (psi V' z z)
  | rest {a x c : T} : c ≠ z → sh V V' (psi a x z) = psi a x z → SpotH c → SpotH (psi a x c)
  | arg {a x : T} : x ≠ z → le V' a = true → V < a → shf V V' a = a → SpotH x → SpotH (psi a x z)

/-- The mark at the right end of a state (`cutsNS` grammar). -/
inductive SpotN : T → Prop
  | rest {a x c : T} : c ≠ z → sh V V' (psi a x z) = psi a x z → SpotN c → SpotN (psi a x c)
  | sub {a : T} : SpotC V' a → SpotN (psi a z z)
  | arg {a x : T} : x ≠ z → V < a → shf V V' a = a → SpotH V V' x → SpotN (psi a x z)

end

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

theorem V'_lt_shf : V' < shf V V' V' := by
  have := shf_lt_shf hV hV' (le_of_lt hVV) hV hV' (le_refl V) hVV
  rwa [shf_self] at this

theorem le_V'_shf : le V' (shf V V' V') = true := by
  simp [le, show lt V' (shf V V' V') = true from V'_lt_shf hV hV' hVV]

/-- Elements of the chain are standard and above `V`. -/
theorem spotC_ot : ∀ {a : T}, SpotC V' a → isOT a = true ∧ V < a
  | _, .mark => ⟨isOT_om.mpr hV', lt_trans hVV (lt_Om_self V')⟩
  | _, .up h => by
    obtain ⟨h1, h2⟩ := spotC_ot h
    exact ⟨isOT_om.mpr h1, lt_trans h2 (lt_Om_self _)⟩

/-- **The chain is a subscript cut of its image.** -/
theorem spotC_scuts : ∀ {a : T}, SpotC V' a → a ∈ scuts V' (shf V V' a)
  | _, .mark => by
    rw [shf_psi hV hV' hVV hV' hVV]
    simp only [scuts, List.mem_append, List.mem_map]
    left; rw [if_pos (le_V'_shf hV hV' hVV)]; simp
  | _, .up (u := u) h => by
    obtain ⟨hu, hVu⟩ := spotC_ot hV hV' hVV h
    rw [shf_psi hV hV' hVV hu hVu]
    simp only [scuts, List.mem_append, List.mem_map]
    right; exact ⟨u, spotC_scuts h, rfl⟩

/-- **The argument part is a high-path cut of its image.** -/
theorem spotH_cutsH : ∀ {x : T}, SpotH V V' x → x ∈ cutsH V' (sh V V' x)
  | _, .mark => by
    rw [sh_psi_gt hVV]
    simp only [sh_z]
    exact mem_cutsH_psi.mpr (Or.inl ⟨le_V'_shf hV hV' hVV, rfl⟩)
  | _, .rest (a := a) (x := x) (c := c) _ hfix h => by
    rw [sh_psi_app, hfix]
    simp only [app_psi, app_z]
    exact mem_cutsH_psi.mpr (Or.inr (Or.inr ⟨c, spotH_cutsH h, rfl⟩))
  | _, .arg (a := a) (x := x) _ hle hVa hfa h => by
    rw [sh_psi_gt hVa, hfa]
    simp only [sh_z]
    exact mem_cutsH_psi.mpr (Or.inr (Or.inl ⟨hle, x, spotH_cutsH h, rfl⟩))

/-- **The state is a `PH3c` cut of its image** at level `V′`. -/
theorem fix_of_spotN : ∀ {B : T}, SpotN V V' B → B ∈ cutsNS V' (sh V V' B)
  | _, .rest (a := a) (x := x) (c := c) _ hfix h => by
    rw [sh_psi_app, hfix]
    simp only [app_psi, app_z, cutsNS, List.mem_append, List.mem_map]
    exact Or.inr ⟨c, fix_of_spotN h, rfl⟩
  | _, .sub (a := a) h => by
    obtain ⟨ha, hVa⟩ := spotC_ot hV hV' hVV h
    rw [sh_psi_gt hVa]
    simp only [sh_z, cutsNS, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl ⟨a, spotC_scuts hV hV' hVV h, rfl⟩)
  | _, .arg (a := a) (x := x) _ hVa hfa h => by
    rw [sh_psi_gt hVa, hfa]
    simp only [sh_z, cutsNS, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨x, spotH_cutsH hV hV' hVV h, rfl⟩)

end

end Ytosk
