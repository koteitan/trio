/-
HdL.lean: 遠い段の入れ子の F の位置のタイの子の並びの良さ（高さの跳びの階層）。

    plugQ [] T = T、plugQ (us :: q) T = us ++ [tie (plugQ q T)]（道 Q の下に T を置く）
    imgT A H G c u x = relTs A H G u (mlTs c (u - c) x)（埋め込みと段の像）
    BotT C o f u Lds Q T := 全ての段 b ≥ u と良い接頭辞 ws で、最後の語の F のタイの子の並び Lds ++ [plugQ Q T] が GpT
    GT t A k H c x := 全ての埋め込み (G, S, o, f)、段 u ≥ c、良い Lds（GoodChtX）、高さ t の良い道 Q（PG t）で BotT
    PG 0 Q := Q = []、PG (t+1) Q := Q = Q' ++ [us0] ∧ PG t Q' ∧ GT t us0（全て最後の級で）

- GT_emb / GT_lift / PG_emb / PG_lift: 埋め込みと段の持ち上げで閉じる（定義の合成）。
- GT_jump / GT_of_jump: GT (t+1) cs ↔ 全ての埋め込みと段で、GT t us0 → GT t (us0 ++ [tie (cs の像)])。
- GT_good: GT から GoodChtX。farWt_plugQ: 最後の語は接頭辞 botQ のあとに T の語を高さ |Q| + 2 だけずらしたもの。
-/
import HdJ

namespace TRIO
namespace HdL

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ

/-! ## 道と像 -/

def plugQ : List (List UT) → List UT → List UT
  | [], T => T
  | us :: q, T => us ++ [UT.tie 0 (plugQ q T)]

theorem plugQ_snoc : ∀ (Q : List (List UT)) (us T : List UT),
    plugQ (Q ++ [us]) T = plugQ Q (us ++ [UT.tie 0 T])
  | [], us, T => by simp [plugQ]
  | q :: Q, us, T => by simp only [List.cons_append, plugQ, plugQ_snoc Q us T]

noncomputable def imgT (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (x : List UT) : List UT :=
  relTs A H G u (mlTs c (u - c) x)

theorem imgT_zero (A : List ℕ) (H : ℕ → ℕ) (c : ℕ) (x : List UT) :
    imgT A H (fun _ => 0) c c x = x := by
  unfold imgT; rw [Nat.sub_self, mlTs_zero, relTs_zero]

theorem imgT_append (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (x y : List UT) :
    imgT A H G c u (x ++ y) = imgT A H G c u x ++ imgT A H G c u y := by
  unfold imgT; rw [mlTs_append, relTs_append]

theorem imgT_tie (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (x : List UT) :
    imgT A H G c u [UT.tie 0 x] = [UT.tie 0 (imgT A H G c u x)] := by
  simp [imgT, mlTs, mlT, relTs, relT]

theorem imgT_ch (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (X : TrioSeq) :
    imgT A H G c u [UT.ch X] = [UT.ch (reliftX u H G A (mlift X c (u - c)))] := by
  simp [imgT, mlTs, mlT, relTs, relT]

theorem imgT_nil (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) : imgT A H G c u [] = [] := by
  simp [imgT, mlTs, relTs]

mutual
theorem relT_plugQ_aux (A : List ℕ) (H G : ℕ → ℕ) (u : ℕ) :
    ∀ (Q : List (List UT)) (T : List UT),
      relTs A H G u (plugQ Q T) = plugQ (Q.map (relTs A H G u)) (relTs A H G u T)
  | [], T => by simp [plugQ]
  | q :: Q, T => by
      simp only [plugQ, List.map_cons, relTs_append]
      rw [show relTs A H G u [UT.tie 0 (plugQ Q T)] = [UT.tie 0 (relTs A H G u (plugQ Q T))] by
        simp [relTs, relT], relT_plugQ_aux A H G u Q T]
end

theorem relTs_plugQ (A : List ℕ) (H G : ℕ → ℕ) (u : ℕ) (Q : List (List UT)) (T : List UT) :
    relTs A H G u (plugQ Q T) = plugQ (Q.map (relTs A H G u)) (relTs A H G u T) :=
  relT_plugQ_aux A H G u Q T

theorem mlTs_plugQ (c t : ℕ) : ∀ (Q : List (List UT)) (T : List UT),
    mlTs c t (plugQ Q T) = plugQ (Q.map (mlTs c t)) (mlTs c t T)
  | [], T => by simp [plugQ]
  | q :: Q, T => by
      simp only [plugQ, List.map_cons, mlTs_append]
      rw [show mlTs c t [UT.tie 0 (plugQ Q T)] = [UT.tie 0 (mlTs c t (plugQ Q T))] by
        simp [mlTs, mlT], mlTs_plugQ c t Q T]

theorem RawTs_plugQ {K : ℕ} : ∀ (Q : List (List UT)) (T : List UT), (∀ us ∈ Q, RawTs K us) →
    RawTs K T → RawTs K (plugQ Q T)
  | [], T, _, hT => hT
  | q :: Q, T, hQ, hT => by
      simp only [plugQ]
      exact RawTs_snoc.mpr ⟨hQ q (by simp), RawT_tie.mpr
        (RawTs_plugQ Q T (fun us h => hQ us (by simp [h])) hT)⟩

theorem RawTs_imgT {A : List ℕ} {k : ℕ} {H G : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H G S o f) {c u : ℕ} (hcu : c ≤ u) {x : List UT}
    (hx : RawTs (c + reOff (fun _ => 0) H A k) x) :
    RawTs (u + reOff (fun _ => 0) f (S ++ A) o) (imgT A H G c u x) := by
  have hKo := hE.2.2.2.2.2.2
  rw [liftOff_eq_reOff0] at hKo
  have h1 : RawTs (u + reOff (fun _ => 0) H A k) (mlTs c (u - c) x) := RawTs_lift hcu hx
  exact RawTs_mono' (Nat.add_le_add_left hKo _) (RawTs_relift h1 G)

/-- 像の合成。 -/
theorem imgT_comp {A : List ℕ} {k : ℕ} {H G : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H G S o f) (G2 : ℕ → ℕ) {c u u' : ℕ} (hcu : c ≤ u) (huu : u ≤ u') {x : List UT}
    (hx : RawTs (c + reOff (fun _ => 0) H A k) x) :
    imgT (S ++ A) f G2 u u' (imgT A H G c u x) = imgT A H (addF G G2) c u' x := by
  unfold imgT
  rw [← relTs_mlTs A H G huu, mlTs_comp hcu huu]
  exact EmbU_relTs hE u' G2 _ (RawTs_lift (le_trans hcu huu) hx)

/-! ## 定義 -/

/-- 最終の級 (C, o, f) の段 u で、F のタイの子の並び Lds のあとに道 Q の下の T を置いた最後の語が GpT。 -/
def BotT (C : List ℕ) (o : ℕ) (f : ℕ → ℕ) (u : ℕ) (Lds Q : List (List UT)) (T : List UT) : Prop :=
  ∀ b, u ≤ b → ∀ ws, FarCAt C o f b ws → RawWsAt C o f b ws →
    GpT C o f b (farWt b (b + liftOff f C o + 1) (ws ++ [(Lds ++ [plugQ Q T], u, [])]))

theorem BotT_snoc_eq (C : List ℕ) (o : ℕ) (f : ℕ → ℕ) (u : ℕ) (Lds Q : List (List UT)) (us T : List UT) :
    BotT C o f u Lds (Q ++ [us]) T = BotT C o f u Lds Q (us ++ [UT.tie 0 T]) := by
  unfold BotT; rw [plugQ_snoc]

def GTdef (P : List ℕ → ℕ → (ℕ → ℕ) → ℕ → List (List UT) → Prop)
    (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (c : ℕ) (x : List UT) : Prop :=
  RawTs (c + reOff (fun _ => 0) H A k) x ∧
    ∀ (G : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ), EmbU A k H G S o f → ∀ u, c ≤ u →
      ∀ Lds, GoodChtX (S ++ A) o f u Lds → ∀ Q, P (S ++ A) o f u Q →
        BotT (S ++ A) o f u Lds Q (imgT A H G c u x)

/-- 高さ t の良い道（外側から内側へ）。 -/
def PG : ℕ → List ℕ → ℕ → (ℕ → ℕ) → ℕ → List (List UT) → Prop
  | 0, _, _, _, _, Q => Q = []
  | t + 1, C, o, f, u, Q => ∃ Q' us0, Q = Q' ++ [us0] ∧ PG t C o f u Q' ∧ GTdef (PG t) C o f u us0

/-- ★ 高さ t の子の並びの良さ。 -/
def GT (t : ℕ) : List ℕ → ℕ → (ℕ → ℕ) → ℕ → List UT → Prop := GTdef (PG t)

theorem GT_raw {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : GT t A k H c x) :
    RawTs (c + reOff (fun _ => 0) H A k) x := h.1

theorem PG_zero {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} : PG 0 C o f u [] := rfl

theorem PG_succ {t : ℕ} {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} {Q : List (List UT)} {us0 : List UT}
    (hQ : PG t C o f u Q) (hus : GT t C o f u us0) : PG (t + 1) C o f u (Q ++ [us0]) :=
  ⟨Q, us0, rfl, hQ, hus⟩

theorem PG_raw : ∀ {t : ℕ} {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} {Q : List (List UT)},
    PG t C o f u Q → ∀ us ∈ Q, RawTs (u + reOff (fun _ => 0) f C o) us
  | 0, _, _, _, _, _, h => by intro us hus; simp only [PG] at h; subst h; simp at hus
  | t + 1, _, _, _, _, _, h => by
      obtain ⟨Q', us0, rfl, hQ', hus0⟩ := h
      intro us hus
      rcases List.mem_append.mp hus with hus | hus
      · exact PG_raw hQ' us hus
      · simp at hus; subst hus; exact hus0.1

theorem PG_length : ∀ {t : ℕ} {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} {Q : List (List UT)},
    PG t C o f u Q → Q.length = t
  | 0, _, _, _, _, _, h => by simp only [PG] at h; subst h; rfl
  | t + 1, _, _, _, _, _, h => by
      obtain ⟨Q', us0, rfl, hQ', -⟩ := h
      simp [PG_length hQ']

/-! ## 埋め込みと持ち上げ -/

theorem GT_emb {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : GT t A k H c x)
    {G1 : ℕ → ℕ} {S1 : List ℕ} {o1 : ℕ} {f1 : ℕ → ℕ} (hE1 : EmbU A k H G1 S1 o1 f1) :
    GT t (S1 ++ A) o1 f1 c (relTs A H G1 c x) := by
  have hKo := hE1.2.2.2.2.2.2
  rw [liftOff_eq_reOff0] at hKo
  refine ⟨RawTs_mono' (Nat.add_le_add_left hKo _) (RawTs_relift h.1 G1),
    fun G2 S2 o2 f2 hE2 u hcu Lds hL Q hQ => ?_⟩
  have e : imgT (S1 ++ A) f1 G2 c u (relTs A H G1 c x) = imgT A H (addF G1 G2) c u x := by
    have := imgT_comp hE1 G2 le_rfl hcu h.1
    rwa [show imgT A H G1 c c x = relTs A H G1 c x by
      unfold imgT; rw [Nat.sub_self, mlTs_zero]] at this
  rw [e]
  have := h.2 (addF G1 G2) (S2 ++ S1) o2 f2 (EmbU_comp hE1 hE2) u hcu Lds
    (by rw [List.append_assoc]; exact hL) Q (by rw [List.append_assoc]; exact hQ)
  rwa [List.append_assoc] at this

theorem GT_lift {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : GT t A k H c x)
    {c' : ℕ} (hcc : c ≤ c') : GT t A k H c' (mlTs c (c' - c) x) := by
  refine ⟨RawTs_lift hcc h.1, fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  have e : imgT A H G c' u (mlTs c (c' - c) x) = imgT A H G c u x := by
    unfold imgT; rw [mlTs_comp hcc hcu]
  rw [e]
  exact h.2 G S o f hE u (le_trans hcc hcu) Lds hL Q hQ

theorem GT_congr {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x y : List UT} (h : GT t A k H c x)
    (e : x = y) : GT t A k H c y := e ▸ h

theorem PG_emb : ∀ {t : ℕ} {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} {Q : List (List UT)},
    PG t C o f u Q → ∀ {G : ℕ → ℕ} {S : List ℕ} {o2 : ℕ} {f2 : ℕ → ℕ}, EmbU C o f G S o2 f2 →
      PG t (S ++ C) o2 f2 u (Q.map (relTs C f G u))
  | 0, _, _, _, _, _, h => by intro _; simp only [PG] at h ⊢; subst h; rfl
  | t + 1, _, _, _, _, _, h => by
      intro hE
      obtain ⟨Q', us0, rfl, hQ', hus0⟩ := h
      rw [List.map_append, List.map_singleton]
      exact PG_succ (PG_emb hQ' hE) (GT_emb (t := t) hus0 hE)

theorem PG_lift : ∀ {t : ℕ} {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} {Q : List (List UT)},
    PG t C o f u Q → ∀ {u' : ℕ}, u ≤ u' → PG t C o f u' (Q.map (mlTs u (u' - u)))
  | 0, _, _, _, _, _, h => by intro _; simp only [PG] at h ⊢; subst h; rfl
  | t + 1, _, _, _, _, _, h => by
      intro hu
      obtain ⟨Q', us0, rfl, hQ', hus0⟩ := h
      rw [List.map_append, List.map_singleton]
      exact PG_succ (PG_lift hQ' hu) (GT_lift (t := t) hus0 hu)

/-! ## 跳び -/

/-- ★ 高さ t+1 の並びの良さから、高さ t の並びにタイとして足せる。 -/
theorem GT_jump {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {cs : List UT}
    (h : GT (t + 1) A k H c cs) {G1 : ℕ → ℕ} {S1 : List ℕ} {o1 : ℕ} {f1 : ℕ → ℕ}
    (hE1 : EmbU A k H G1 S1 o1 f1) {u : ℕ} (hcu : c ≤ u) {us0 : List UT}
    (hus : GT t (S1 ++ A) o1 f1 u us0) :
    GT t (S1 ++ A) o1 f1 u (us0 ++ [UT.tie 0 (imgT A H G1 c u cs)]) := by
  refine ⟨RawTs_snoc.mpr ⟨hus.1, RawT_tie.mpr (RawTs_imgT hE1 hcu h.1)⟩,
    fun G2 S2 o2 f2 hE2 u' huu Lds hL Q hQ => ?_⟩
  rw [imgT_append, imgT_tie, imgT_comp hE1 G2 hcu huu h.1, ← BotT_snoc_eq]
  have hus' : GT t (S2 ++ (S1 ++ A)) o2 f2 u' (imgT (S1 ++ A) f1 G2 u u' us0) := by
    have := GT_lift (GT_emb hus hE2) huu
    unfold imgT
    rwa [relTs_mlTs _ _ _ huu]
  have := h.2 (addF G1 G2) (S2 ++ S1) o2 f2 (EmbU_comp hE1 hE2) u' (le_trans hcu huu) Lds
    (by rw [List.append_assoc]; exact hL) (Q ++ [imgT (S1 ++ A) f1 G2 u u' us0])
    (by rw [List.append_assoc]; exact PG_succ hQ hus')
  rwa [List.append_assoc] at this

theorem GT_of_jump {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {cs : List UT}
    (hraw : RawTs (c + reOff (fun _ => 0) H A k) cs)
    (hJ : ∀ (G1 : ℕ → ℕ) (S1 : List ℕ) (o1 : ℕ) (f1 : ℕ → ℕ), EmbU A k H G1 S1 o1 f1 →
      ∀ u, c ≤ u → ∀ us0, GT t (S1 ++ A) o1 f1 u us0 →
        GT t (S1 ++ A) o1 f1 u (us0 ++ [UT.tie 0 (imgT A H G1 c u cs)])) :
    GT (t + 1) A k H c cs := by
  refine ⟨hraw, fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  obtain ⟨Q', us0, rfl, hQ', hus0⟩ := hQ
  have h1 := hJ G S o f hE u hcu us0 hus0
  have := h1.2 (fun _ => 0) [] o f (EmbU_triv hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 f) u le_rfl Lds hL Q' hQ'
  rw [BotT_snoc_eq]
  rwa [imgT_zero] at this

/-- ★ 高さ t の並びに、子の並び cs（高さ t+1 で良い）を持つタイを足す。 -/
theorem GT_tie {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k)
    (hAk : ∀ a ∈ A, a < k) {c : ℕ} {us cs : List UT}
    (hus : GT t A k H c us) (hcs : GT (t + 1) A k H c cs) : GT t A k H c (us ++ [UT.tie 0 cs]) := by
  have := GT_jump hcs (EmbU_triv hAk hA01 hk H) le_rfl (S1 := []) hus
  rwa [imgT_zero] at this

/-! ## 最後の語 -/

noncomputable def chTQ (b r u : ℕ) : List (List UT) → TrioSeq
  | [] => []
  | us :: q => chT b r u us ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chTQ b r u q)

theorem chT_plugQ (b r u : ℕ) : ∀ (Q : List (List UT)) (T : List UT),
    chT b r u (plugQ Q T) = chTQ b r u Q ++ shiftr01 Q.length 0 (chT b r u T)
  | [], T => by simp [plugQ, chTQ, shiftr01]
  | q :: Q, T => by
      simp only [plugQ, chTQ, chT_append, List.length_cons]
      rw [show chT b r u [UT.tie 0 (plugQ Q T)]
          = ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u (plugQ Q T)) by simp [chT, unitT],
        chT_plugQ b r u Q T, shiftr01_append0, shiftr01_add0]
      simp

theorem Fr_chTQ {b r u K : ℕ} : ∀ (Q : List (List UT)), (∀ us ∈ Q, RawTs K us) → Fr (chTQ b r u Q)
  | [], _ => Fr_nil
  | q :: Q, hQ => by
      simp only [chTQ]
      exact Fr_append (Fr_chT _ (hQ q (by simp)))
        (Fr_node _ _)

noncomputable def botQ (b r u : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds Q : List (List UT)) : TrioSeq :=
  farWt b r ws ++ fwH b r (FTLt b r u Lds) b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chTQ b r u Q))

theorem farWt_plugQ (b r u : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds Q : List (List UT)) (T : List UT) :
    farWt b r (ws ++ [(Lds ++ [plugQ Q T], u, [])])
      = botQ b r u ws Lds Q ++ shiftr01 (Q.length + 2) 0 (chT b r u T) := by
  rw [farWt_snoc]
  dsimp only
  have e1 : ∀ (H0 K : TrioSeq), fwH b r (H0 ++ K) u [] = fwH b r H0 b K := by
    intro H0 K; simp only [fwH, mlift_nil, Nat.sub_self, mlift_zero, List.append_nil]
  rw [FTLt_snoc, chT_plugQ, botQ, List.append_assoc, e1, fwH_child_app1, shiftr01_add0]

theorem Fr_botQ (b r u : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) (Lds Q : List (List UT)) :
    Fr (botQ b r u ws Lds Q) := Fr_append (Fr_farWt _ _ _) (Fr_fwH _ _ _ _ _)

/-! ## GoodChtX との行き来 -/

theorem GoodChtX_bot {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} {L : List (List UT)}
    (hG : GoodChtX C o f u L) (hC : ∀ a ∈ C, a < o) (hC1 : ∀ a ∈ C, 1 ≤ a) (ho : 1 ≤ o)
    {b : ℕ} (hub : u ≤ b) {ws : List (List (List UT) × ℕ × TrioSeq)} (hFC : FarCAt C o f b ws)
    (hR : RawWsAt C o f b ws) :
    GpT C o f b (farWt b (b + liftOff f C o + 1) (ws ++ [(L, u, [])])) := by
  have := hG.2 (fun _ => 0) [] o f b (EmbU_triv hC hC1 ho f) hub ws hFC hR
  rwa [mapt_zero] at this

/-- ★ GT から GoodChtX。 -/
theorem GT_good {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : GT t A k H c x)
    {G : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} (hE : EmbU A k H G S o f) {u : ℕ} (hcu : c ≤ u)
    {Lds : List (List UT)} (hL : GoodChtX (S ++ A) o f u Lds) {Q : List (List UT)}
    (hQ : PG t (S ++ A) o f u Q) :
    GoodChtX (S ++ A) o f u (Lds ++ [plugQ Q (imgT A H G c u x)]) := by
  refine ⟨fun us hus => ?_, fun g2 S2 o2 f2 b hE2 hub ws hC hR => ?_⟩
  · rcases List.mem_append.mp hus with hus | hus
    · exact hL.1 us hus
    · simp at hus; subst hus
      exact RawTs_plugQ Q _ (PG_raw hQ) (RawTs_imgT hE hcu h.1)
  · rw [List.map_append, List.map_singleton, relTs_plugQ,
      show relTs (S ++ A) f g2 u (imgT A H G c u x) = imgT A H (addF G g2) c u x by
        have := imgT_comp hE g2 hcu le_rfl h.1
        rwa [show imgT (S ++ A) f g2 u u (imgT A H G c u x) = relTs (S ++ A) f g2 u (imgT A H G c u x) by
          unfold imgT; rw [Nat.sub_self, mlTs_zero]] at this]
    have := h.2 (addF G g2) (S2 ++ S) o2 f2 (EmbU_comp hE hE2) u hcu (Lds.map (relTs (S ++ A) f g2 u))
      (by rw [List.append_assoc]; exact GoodChtX_emb hL hE2) (Q.map (relTs (S ++ A) f g2 u))
      (by rw [List.append_assoc]; exact PG_emb hQ hE2) b hub ws
      (by rw [List.append_assoc]; exact hC) (by rw [List.append_assoc]; exact hR)
    rwa [List.append_assoc] at this

/-- 高さ 0 の空の並び。 -/
theorem GT_nil0 {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} : GT 0 A k H c [] := by
  refine ⟨by simp [RawTs], fun G S o f hE u _ Lds hL Q hQ => ?_⟩
  simp only [GT, PG] at hQ
  subst hQ
  intro b hub ws hC hR
  rw [imgT_nil]
  exact GoodChtX_bot (GoodChtX_Fsucc hL) hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 hub hC hR

end HdL
end TRIO
