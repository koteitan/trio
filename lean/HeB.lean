/-
HeB.lean: 段つきの道と、道の集合で定義する子の並びの良さ（HdL の一般化、追記577）。

    Path := List (List UT × ℕ)（成分 (us, l) は、兄弟の並び us のあとの段 l の節点）
    plugQ [] T = T、plugQ ((us, l) :: q) T = us ++ [tie l (plugQ q T)]
    BotT C o f u Lds Q T := 全ての段 b ≥ u と良い接頭辞 ws で、最後の語の F のタイの子の並び Lds ++ [plugQ Q T] が GpT
    Gd P A k H c x := 全ての埋め込み (G, S, o, f)、段 u ≥ c、良い Lds、集合 P の道 Q で BotT（HdL の GTdef の P を道の集合にした形）

- Gd_emb / Gd_lift: 定義の合成。Gd_mono: 集合が大きいほど弱い。
- Ext P l Pc := P の道に P で良い成分を段 l で足した道は Pc に入る。Gd_jump: Ext P l Pc なら Gd Pc cs → Gd P us0 → Gd P (us0 ++ [tie l cs])。
- PSOK: 道の成分の生の条件、埋め込みと段の持ち上げで閉じる。Gd_good: Gd から GoodChtX。
-/
import HdP

namespace TRIO
namespace HeB

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ

/-! ## 道 -/

abbrev Path := List (List UT × ℕ)

def plugQ : Path → List UT → List UT
  | [], T => T
  | (us, l) :: q, T => us ++ [UT.tie l (plugQ q T)]

theorem plugQ_snoc : ∀ (Q : Path) (us T : List UT) (l : ℕ),
    plugQ (Q ++ [(us, l)]) T = plugQ Q (us ++ [UT.tie l T])
  | [], us, T, l => by simp [plugQ]
  | (v, m) :: Q, us, T, l => by simp only [List.cons_append, plugQ, plugQ_snoc Q us T l]

def mapQ (φ : List UT → List UT) : Path → Path
  | [] => []
  | (us, l) :: q => (φ us, l) :: mapQ φ q

theorem mapQ_append (φ : List UT → List UT) : ∀ (Q Q' : Path), mapQ φ (Q ++ Q') = mapQ φ Q ++ mapQ φ Q'
  | [], Q' => by simp [mapQ]
  | (us, l) :: Q, Q' => by simp only [List.cons_append, mapQ, mapQ_append φ Q Q']

theorem mapQ_snoc (φ : List UT → List UT) (Q : Path) (us : List UT) (l : ℕ) :
    mapQ φ (Q ++ [(us, l)]) = mapQ φ Q ++ [(φ us, l)] := by
  rw [mapQ_append]; rfl

theorem mapQ_length (φ : List UT → List UT) : ∀ Q : Path, (mapQ φ Q).length = Q.length
  | [] => rfl
  | (us, l) :: Q => by simp [mapQ, mapQ_length φ Q]

theorem mapQ_comp (φ ψ : List UT → List UT) : ∀ Q : Path, mapQ φ (mapQ ψ Q) = mapQ (fun x => φ (ψ x)) Q
  | [] => rfl
  | (us, l) :: Q => by simp [mapQ, mapQ_comp φ ψ Q]

theorem mapQ_id : ∀ Q : Path, mapQ (fun x => x) Q = Q
  | [] => rfl
  | (us, l) :: Q => by simp [mapQ, mapQ_id Q]

theorem mapQ_congr {φ ψ : List UT → List UT} : ∀ (Q : Path), (∀ p ∈ Q, φ p.1 = ψ p.1) → mapQ φ Q = mapQ ψ Q
  | [], _ => rfl
  | (us, l) :: Q, h => by
      simp only [mapQ]
      rw [h (us, l) (by simp), mapQ_congr Q (fun p hp => h p (by simp [hp]))]

/-! ## 像 -/

noncomputable def imgT (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (x : List UT) : List UT :=
  relTs A H G u (mlTs c (u - c) x)

theorem imgT_zero (A : List ℕ) (H : ℕ → ℕ) (c : ℕ) (x : List UT) :
    imgT A H (fun _ => 0) c c x = x := by
  unfold imgT; rw [Nat.sub_self, mlTs_zero, relTs_zero]

theorem imgT_append (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (x y : List UT) :
    imgT A H G c u (x ++ y) = imgT A H G c u x ++ imgT A H G c u y := by
  unfold imgT; rw [mlTs_append, relTs_append]

theorem imgT_tie (A : List ℕ) (H G : ℕ → ℕ) (c u l : ℕ) (x : List UT) :
    imgT A H G c u [UT.tie l x] = [UT.tie l (imgT A H G c u x)] := by
  simp [imgT, mlTs, mlT, relTs, relT]

theorem imgT_ch (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (X : TrioSeq) :
    imgT A H G c u [UT.ch X] = [UT.ch (reliftX u H G A (mlift X c (u - c)))] := by
  simp [imgT, mlTs, mlT, relTs, relT]

theorem imgT_nil (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) : imgT A H G c u [] = [] := by
  simp [imgT, mlTs, relTs]

theorem relTs_plugQ (A : List ℕ) (H G : ℕ → ℕ) (u : ℕ) :
    ∀ (Q : Path) (T : List UT),
      relTs A H G u (plugQ Q T) = plugQ (mapQ (relTs A H G u) Q) (relTs A H G u T)
  | [], T => by simp [plugQ, mapQ]
  | (v, l) :: Q, T => by
      simp only [plugQ, mapQ, relTs_append]
      rw [show relTs A H G u [UT.tie l (plugQ Q T)] = [UT.tie l (relTs A H G u (plugQ Q T))] by
        simp [relTs, relT], relTs_plugQ A H G u Q T]

theorem mlTs_plugQ (c t : ℕ) : ∀ (Q : Path) (T : List UT),
    mlTs c t (plugQ Q T) = plugQ (mapQ (mlTs c t) Q) (mlTs c t T)
  | [], T => by simp [plugQ, mapQ]
  | (v, l) :: Q, T => by
      simp only [plugQ, mapQ, mlTs_append]
      rw [show mlTs c t [UT.tie l (plugQ Q T)] = [UT.tie l (mlTs c t (plugQ Q T))] by
        simp [mlTs, mlT], mlTs_plugQ c t Q T]

theorem RawTs_plugQ {K : ℕ} : ∀ (Q : Path) (T : List UT), (∀ p ∈ Q, RawTs K p.1) →
    RawTs K T → RawTs K (plugQ Q T)
  | [], T, _, hT => hT
  | (v, l) :: Q, T, hQ, hT => by
      simp only [plugQ]
      exact RawTs_snoc.mpr ⟨hQ (v, l) (by simp), RawT_tie.mpr
        (RawTs_plugQ Q T (fun p h => hQ p (by simp [h])) hT)⟩

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
def BotT (C : List ℕ) (o : ℕ) (f : ℕ → ℕ) (u : ℕ) (Lds : List (List UT)) (Q : Path) (T : List UT) : Prop :=
  ∀ b, u ≤ b → ∀ ws, FarCAt C o f b ws → RawWsAt C o f b ws →
    GpT C o f b (farWt b (b + liftOff f C o + 1) (ws ++ [(Lds ++ [plugQ Q T], u, [])]))

theorem BotT_snoc_eq (C : List ℕ) (o : ℕ) (f : ℕ → ℕ) (u : ℕ) (Lds : List (List UT)) (Q : Path)
    (us T : List UT) (l : ℕ) :
    BotT C o f u Lds (Q ++ [(us, l)]) T = BotT C o f u Lds Q (us ++ [UT.tie l T]) := by
  unfold BotT; rw [plugQ_snoc]

/-- 道の集合（級と段ごとの道の述語）。 -/
abbrev PS := List ℕ → ℕ → (ℕ → ℕ) → ℕ → Path → Prop

/-- ★ 道の集合 P の全ての道の下で良い子の並び。 -/
def Gd (P : PS) (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (c : ℕ) (x : List UT) : Prop :=
  RawTs (c + reOff (fun _ => 0) H A k) x ∧
    ∀ (G : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ), EmbU A k H G S o f → ∀ u, c ≤ u →
      ∀ Lds, GoodChtX (S ++ A) o f u Lds → ∀ Q, P (S ++ A) o f u Q →
        BotT (S ++ A) o f u Lds Q (imgT A H G c u x)

theorem Gd_raw {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : Gd P A k H c x) :
    RawTs (c + reOff (fun _ => 0) H A k) x := h.1

theorem Gd_mono {P P' : PS} (hPP : ∀ C o f u Q, P' C o f u Q → P C o f u Q) {A : List ℕ} {k : ℕ}
    {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : Gd P A k H c x) : Gd P' A k H c x :=
  ⟨h.1, fun G S o f hE u hcu Lds hL Q hQ => h.2 G S o f hE u hcu Lds hL Q (hPP _ _ _ _ _ hQ)⟩

theorem Gd_emb {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : Gd P A k H c x)
    {G1 : ℕ → ℕ} {S1 : List ℕ} {o1 : ℕ} {f1 : ℕ → ℕ} (hE1 : EmbU A k H G1 S1 o1 f1) :
    Gd P (S1 ++ A) o1 f1 c (relTs A H G1 c x) := by
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

theorem Gd_lift {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT} (h : Gd P A k H c x)
    {c' : ℕ} (hcc : c ≤ c') : Gd P A k H c' (mlTs c (c' - c) x) := by
  refine ⟨RawTs_lift hcc h.1, fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  have e : imgT A H G c' u (mlTs c (c' - c) x) = imgT A H G c u x := by
    unfold imgT; rw [mlTs_comp hcc hcu]
  rw [e]
  exact h.2 G S o f hE u (le_trans hcc hcu) Lds hL Q hQ

theorem Gd_congr {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x y : List UT} (h : Gd P A k H c x)
    (e : x = y) : Gd P A k H c y := e ▸ h

/-! ## 集合の性質 -/

/-- 道の成分の生の条件、埋め込みと段の持ち上げで閉じる。 -/
structure PSOK (P : PS) : Prop where
  raw : ∀ C o f u Q, P C o f u Q → ∀ p ∈ Q, RawTs (u + reOff (fun _ => 0) f C o) p.1
  emb : ∀ C o f u Q, P C o f u Q → ∀ G S o2 f2, EmbU C o f G S o2 f2 →
    P (S ++ C) o2 f2 u (mapQ (relTs C f G u) Q)
  lift : ∀ C o f u Q, P C o f u Q → ∀ u', u ≤ u' → P C o f u' (mapQ (mlTs u (u' - u)) Q)

/-- 延長: P の道に、P で良い成分を段 l で足した道は Pc に入る。 -/
def Ext (P : PS) (l : ℕ) (Pc : PS) : Prop :=
  ∀ C o f u Q us, P C o f u Q → Gd P C o f u us → Pc C o f u (Q ++ [(us, l)])

/-! ## 跳び -/

/-- ★ 延長の集合で良い子の並び cs を、段 l の節点の子として足す。 -/
theorem Gd_jump {P Pc : PS} {l : ℕ} (hX : Ext P l Pc) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ}
    {cs : List UT} (h : Gd Pc A k H c cs) {G1 : ℕ → ℕ} {S1 : List ℕ} {o1 : ℕ} {f1 : ℕ → ℕ}
    (hE1 : EmbU A k H G1 S1 o1 f1) {u : ℕ} (hcu : c ≤ u) {us0 : List UT}
    (hus : Gd P (S1 ++ A) o1 f1 u us0) :
    Gd P (S1 ++ A) o1 f1 u (us0 ++ [UT.tie l (imgT A H G1 c u cs)]) := by
  refine ⟨RawTs_snoc.mpr ⟨hus.1, RawT_tie.mpr (RawTs_imgT hE1 hcu h.1)⟩,
    fun G2 S2 o2 f2 hE2 u' huu Lds hL Q hQ => ?_⟩
  rw [imgT_append, imgT_tie, imgT_comp hE1 G2 hcu huu h.1, ← BotT_snoc_eq]
  have hus' : Gd P (S2 ++ (S1 ++ A)) o2 f2 u' (imgT (S1 ++ A) f1 G2 u u' us0) := by
    have := Gd_lift (Gd_emb hus hE2) huu
    unfold imgT
    rwa [relTs_mlTs _ _ _ huu]
  have := h.2 (addF G1 G2) (S2 ++ S1) o2 f2 (EmbU_comp hE1 hE2) u' (le_trans hcu huu) Lds
    (by rw [List.append_assoc]; exact hL) (Q ++ [(imgT (S1 ++ A) f1 G2 u u' us0, l)])
    (by rw [List.append_assoc]; exact hX _ _ _ _ _ _ hQ hus')
  rwa [List.append_assoc] at this

/-- ★ 埋め込みなしの跳び。 -/
theorem Gd_tie {P Pc : PS} {l : ℕ} (hX : Ext P l Pc) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ}
    (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) {c : ℕ} {us cs : List UT}
    (hus : Gd P A k H c us) (hcs : Gd Pc A k H c cs) : Gd P A k H c (us ++ [UT.tie l cs]) := by
  have := Gd_jump hX hcs (EmbU_triv hAk hA01 hk H) le_rfl (S1 := []) hus
  rwa [imgT_zero] at this

/-! ## 最後の語 -/

noncomputable def chTQ (b r u : ℕ) : Path → TrioSeq
  | [] => []
  | (us, l) :: q => chT b r u us ++ ((1, r + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chTQ b r u q)

theorem chT_plugQ (b r u : ℕ) : ∀ (Q : Path) (T : List UT),
    chT b r u (plugQ Q T) = chTQ b r u Q ++ shiftr01 Q.length 0 (chT b r u T)
  | [], T => by simp [plugQ, chTQ, shiftr01]
  | (v, l) :: Q, T => by
      simp only [plugQ, chTQ, chT_append, List.length_cons]
      rw [show chT b r u [UT.tie l (plugQ Q T)]
          = ((1, r + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u (plugQ Q T)) by simp [chT, unitT],
        chT_plugQ b r u Q T, shiftr01_append0, shiftr01_add0]
      simp

theorem Fr_chTQ {b r u K : ℕ} : ∀ (Q : Path), (∀ p ∈ Q, RawTs K p.1) → Fr (chTQ b r u Q)
  | [], _ => Fr_nil
  | (v, l) :: Q, hQ => by
      simp only [chTQ]
      exact Fr_append (Fr_chT _ (hQ (v, l) (by simp))) (Fr_node _ _)

noncomputable def botQ (b r u : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds : List (List UT)) (Q : Path) : TrioSeq :=
  farWt b r ws ++ fwH b r (FTLt b r u Lds) b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chTQ b r u Q))

theorem farWt_plugQ (b r u : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds : List (List UT)) (Q : Path) (T : List UT) :
    farWt b r (ws ++ [(Lds ++ [plugQ Q T], u, [])])
      = botQ b r u ws Lds Q ++ shiftr01 (Q.length + 2) 0 (chT b r u T) := by
  rw [farWt_snoc]
  dsimp only
  have e1 : ∀ (H0 K : TrioSeq), fwH b r (H0 ++ K) u [] = fwH b r H0 b K := by
    intro H0 K; simp only [fwH, mlift_nil, Nat.sub_self, mlift_zero, List.append_nil]
  rw [FTLt_snoc, chT_plugQ, botQ, List.append_assoc, e1, fwH_child_app1, shiftr01_add0]

theorem Fr_botQ (b r u : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) (Lds : List (List UT)) (Q : Path) :
    Fr (botQ b r u ws Lds Q) := Fr_append (Fr_farWt _ _ _) (Fr_fwH _ _ _ _ _)

/-! ## GoodChtX との行き来 -/

theorem GoodChtX_bot {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} {L : List (List UT)}
    (hG : GoodChtX C o f u L) (hC : ∀ a ∈ C, a < o) (hC1 : ∀ a ∈ C, 1 ≤ a) (ho : 1 ≤ o)
    {b : ℕ} (hub : u ≤ b) {ws : List (List (List UT) × ℕ × TrioSeq)} (hFC : FarCAt C o f b ws)
    (hR : RawWsAt C o f b ws) :
    GpT C o f b (farWt b (b + liftOff f C o + 1) (ws ++ [(L, u, [])])) := by
  have := hG.2 (fun _ => 0) [] o f b (EmbU_triv hC hC1 ho f) hub ws hFC hR
  rwa [mapt_zero] at this

/-- ★ Gd から GoodChtX。 -/
theorem Gd_good {P : PS} (hP : PSOK P) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {x : List UT}
    (h : Gd P A k H c x) {G : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} (hE : EmbU A k H G S o f)
    {u : ℕ} (hcu : c ≤ u) {Lds : List (List UT)} (hL : GoodChtX (S ++ A) o f u Lds) {Q : Path}
    (hQ : P (S ++ A) o f u Q) :
    GoodChtX (S ++ A) o f u (Lds ++ [plugQ Q (imgT A H G c u x)]) := by
  refine ⟨fun us hus => ?_, fun g2 S2 o2 f2 b hE2 hub ws hC hR => ?_⟩
  · rcases List.mem_append.mp hus with hus | hus
    · exact hL.1 us hus
    · simp at hus; subst hus
      exact RawTs_plugQ Q _ (hP.raw _ _ _ _ _ hQ) (RawTs_imgT hE hcu h.1)
  · rw [List.map_append, List.map_singleton, relTs_plugQ,
      show relTs (S ++ A) f g2 u (imgT A H G c u x) = imgT A H (addF G g2) c u x by
        have := imgT_comp hE g2 hcu le_rfl h.1
        rwa [show imgT (S ++ A) f g2 u u (imgT A H G c u x) = relTs (S ++ A) f g2 u (imgT A H G c u x) by
          unfold imgT; rw [Nat.sub_self, mlTs_zero]] at this]
    have := h.2 (addF G g2) (S2 ++ S) o2 f2 (EmbU_comp hE hE2) u hcu (Lds.map (relTs (S ++ A) f g2 u))
      (by rw [List.append_assoc]; exact GoodChtX_emb hL hE2) (mapQ (relTs (S ++ A) f g2 u) Q)
      (by rw [List.append_assoc]; exact hP.emb _ _ _ _ _ hQ _ _ _ _ hE2) b hub ws
      (by rw [List.append_assoc]; exact hC) (by rw [List.append_assoc]; exact hR)
    rwa [List.append_assoc] at this

/-- 空の道だけの集合での空の並び（新しい F のタイ）。 -/
theorem Gd_nilF {P : PS} (hP : ∀ C o f u Q, P C o f u Q → Q = []) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ}
    {c : ℕ} : Gd P A k H c [] := by
  refine ⟨by simp [RawTs], fun G S o f hE u _ Lds hL Q hQ => ?_⟩
  have := hP _ _ _ _ _ hQ
  subst this
  intro b hub ws hC hR
  rw [imgT_nil]
  exact GoodChtX_bot (GoodChtX_Fsucc hL) hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 hub hC hR

end HeB
end TRIO
