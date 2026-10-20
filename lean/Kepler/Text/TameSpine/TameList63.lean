/-
  Kepler.Text.TameSpine.TameList63 — B3 D 链第四批：EXISTS_PATH_COMPLEMENT
  收口（AUQTZYZ.hl :574-:1850 大件独批第二落，§3-§5 照批 62 处方照方
  抓药）。接续批 62 = TameList62.lean（cc9da66a，§0 私桥 12 件 + §1
  证人支 + §2 互斥/双闭包 6 件入库）；本批收口 = 合取 8-12（card 支
  epcFInj/epcAtomInj/epcCard + 双射桥 epcFaceAtomSingleton/epcConj9-12）
  + §5 总装 EXISTS_PATH_COMPLEMENT 十二合取全闭；批 63 终点 = 章
  只剩压尾段（AUQTZYZ_concl :1851-:1858 + AUQTZYZ :1859-:2624）。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ EXISTS_PATH_COMPLEMENT 收口：§3 card 支（epcFInj / epcAtomInj /
  │ epcCard）+ §4 双射桥（epcFaceAtomSingleton / epcConj9 / epcConj10 /
  │ epcConj11 / epcConj12）+ §5 总装 EXISTS_PATH_COMPLEMENT（十二合取
  │ 全闭，AUQTZYZ.hl :574-:586 语句逐字承载）。全件零 sorry；公理面
  │ propext/Classical.choice/Quot.sound 三标准内。构建纯 lake build
  │ 单发串行零旗标零 -K。
  └──────────────────────────────────────────────────────────────

  拆分裁定（本批特殊点，批 64 起沿用）：

  - **§0' 本地私桥副本（19 件）**：TameList62 的 §0-§2 桥件全部
    `private`（模块私有，Lean 4 跨模块不可见），而红线「零既有文件
    触碰」禁止回头把 TameList62 改公开——故本批以 §0' 段把 §3-§5
    依赖的 19 件桥件（pow_succ'_apply / isInjContourIsInjList /
    epcFaceMapNodeMap / epcMapStep / epcInvMapStep / epcGoingTrans /
    epcGoingChain / epcGoingWrap / epcSymmPredNodeMap /
    epcNodeSymmEqOfTwo / epcNodePos / epcMemSupport / epcNodeSplit /
    epcMemPath / epcDisjoint / epcStepSeg / epcStepWrapN3 /
    epcClosureIn / epcClosureFace）**逐字复制**为本地 private 件
    （文本取自已构建绿的 TameList62 §0-§2 实库文本，非草稿）。
    同 namespace 下与 TameList62 的 private 名不冲突。后续批若再
    遇私桥依赖段同法处理，或等清理批统一上收公开化。
  - **批 62 草稿五点处方的落地形**（批 63 实测记档）：① zNe 三假设
    `1 ≤ i → i < j → j ≤ cf` 的调用方三发 (by omega)，且 epcFInj /
    epcAtomInj 的 intro 须保留 hi hj（第三发 omega 的下料）；②
    conj10 合取④两支的 atom 归属方向：`atom L u = {y | going L u y ∨
    going L y u}`（Hypermap :6566），going u→z 走 Or.inl（草稿误
    Or.inr），且 ci (i+1) = n+1 支须先把 p (ci x cf) 经
    hmod (Nat.mod_self) 换算回 p 0 才能消费 epcGoingWrap；③ conj10/
    conj11 的 N_x = 2 支 L.invMap 链：h1（invMap (nodeMap x) = p n）
    与目标（nodeMap.symm x 面）的换算在**目标侧** rw
    epcNodeSymmEqOfTwo（勿在 h1 侧），链中 complementPt_compIndex_eval
    走正向（p (ci j) = nodeMap (symm^j x)），链尾补
    (epcNodeSymmEqOfTwo ..).symm；④ hinvSeg/hfinSeg 二连 rw 即闭合
    （hfinSeg 的假设位直喂 succ_eval 等式，conclusion 的 y 被实例化
    成 p (ci j'+1) 本形，rw 尾 rfl 自闭合，勿多补 exact）；⑤ 总装
    13 孔 + complementMod H hr hx n hn.symm + epcDisjoint … hn.symm，
    合取 5 孔内 epcMemSupport 换算后 rw [hym]（正向，p m → u）。

  新雷区（本批实测记档，编号承批 62 的 #128-#136）：
  - **#137 private 桥件跨模块不可消费**：TameList62 §0-§2 全 private，
    批 63 只能本地复制（§0' 段）；复制源取实库构建绿文本而非快照
    草稿（本例两者逐字同，但纪律上以实库为准）。同名件在同一
    namespace 下不冲突。
  - **#138 atom 归属方向 + 尾段 p (ci cf) → p 0 换算**：合取④的
    `z ∈ atom L u` 展开是 `going L u z ∨ going L z u`（u→z 在左），
    going 正向证据一律 Or.inl；ci (i+1) = n+1 时目标里的
    `p (ci x (i+1))` 先 rw [hicf] 变 `p (n+1)`，再经
    `hmod (n+1) : p 0 = p (n+1)` 的 symm 换回 `p 0`（epcCard 的
    hpnp1 形内联），否则 epcGoingWrap 的 p 0 端点对不上。
  - **#139 N_x = 2 的 invMap 链换算面**：h1 只到 nodeMap x 面
    （hp0 正向 rw 而来），目标的 nodeMap.symm x 面在【目标侧】用
    epcNodeSymmEqOfTwo 换算（rw 于目标、勿 rw at h1）；链尾
    `nodeMap x = nodeMap.symm x` 由 (epcNodeSymmEqOfTwo ..).symm
    收口。complementPt_compIndex_eval 的语句方向是
    `p (ci x i) = nodeMap (symm^i x)`（pivot 在左），消费时按此定向。
  - **#140 段首 witness 等式的闭合面**：hfinSeg 假设位直喂
    succ_eval 等式时 conclusion 的 y 实例化为 `p (ci j'+1)`，二连
    rw 后 rfl 自闭合——多补 exact 反而零命中报错。res 的展开用
    `simp only [res]`（rw [res] 对 def 无效）。
  - **#141 setOf 合取的解构序**：conj9 的 hA 双合取先
    `rw [Set.mem_inter_iff]` 拆半，两个 setOf 成员各补
    `rw [Set.mem_setOf_eq]` 再 obtain（rcases 对假设侧 setOf 的
    whnf 穿透不作依赖）；atomsOfLoopRep 给的 ∃ 形是
    `y = atom L x`（A 在前），bind 序 ⟨u, hAu, huL⟩ 勿倒；
    hAx1 是 Eq 无 .1 投影，原子单点化走
    `rw [← hAu, hAx1] + epcFaceAtomSingleton` 三发拼装。
  - **#142 complementIndex 指标链的「两步空降」**：lt_of_lt 每发只
    承载 +1——`n ≥ ci (i-1) + 1` 型目标（conj11 段首 hm₀）须两发
    链 `lt_of_lt (i-1<i)` + `lt_of_lt (i<cf)` 配 hn（ci cf - 1 = n）
    三件 omega（一发 lt_of_lt (i-1<cf) 只给 ≤ n，omega 实测拒证；
    HOL 同点走 lemma_increasing_index :1845，两步形同源）。
  - **#143 obtain 清名**：`obtain ⟨k, hkw, hag⟩ := hgoing` 之后
    hgoing 即清名，后续消费（如 Or.inr hgoing 走 atom_subset_node）
    须在 obtain 前落 ascription have（本批 hAtom）。
  - **#144 Iff 件消费面三坑**：mem_node_iff 是 Iff，消食用
    `(H.mem_node_iff w y).mp h1`（直取报 Function expected），
    解构 ⟨t, hyt⟩ 两元（多写 `-` 位反使 eq 落空名）；_
    orbitMap_singleton_iff 的 mpr 参是 `f x = x` 形，hagree1 经
    mapFix 换算后方向倒置，补 .symm。

  批 64 接续点（AUQTZYZ 章压尾）：
  - `AUQTZYZ_concl`（:1851-:1858）：is_normal 拼装件——is_normal
    {loop_of_face x, L} 双件族验证；直接消费本件
    EXISTS_PATH_COMPLEMENT 与在册 IsNormalFamily/quotient 面。
  - `AUQTZYZ`（:1859-:2624，765 行压尾）：is_normal 分支 + dih2k
    (quotient H {L1,L2}) 卡段；:1864 起以 MRESAL
    EXISTS_PATH_COMPLEMENT[atoms_of_loop_rep] 消费本件，同面化直投。
    其后章毕接 RXOKSKC.hl（1,105 行；**:523 RXOKSKC 是 A9 接口件，
    到达时单独标注**）。
-/
import Kepler.Text.TameSpine.TameList62

/-! # AUQTZYZ 主峰收口：EXISTS_PATH_COMPLEMENT §3-§5（AUQTZYZ.hl :574-:1850） -/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

/-! ### §0' 本地私桥（TameList62 §0-§2 同名件逐字副本；private 跨模块
不可见 + 零触碰红线，见头注拆分裁定 #137） -/

/-! ### §0 私桥件副本 -/

/- `inverseAddExponents`（INVERSE_ADD_EXPONENTS 重推导）已在 TameList62
落公开件，本模块经 import 直接消费，不再本地副本。 -/

/-- `(p^(k+1)) x = p ((p^k) x)`（pow_succ' 的应用形；雷区 #132：
裸 pow_succ' 在多幂项目标上会错咬 face 侧幂，一律用本件）。 -/
private theorem pow_succ'_apply (f : Equiv.Perm α) (k : ℕ) (x : α) :
    (f ^ (k + 1)) x = f ((f ^ k) x) := by
  rw [pow_succ']; rfl

/-- `is_inj_contour`（嵌套成对定义）到 `Loop.IsInjList`（成对全称形）
的展开桥：第 `n+1` 层的第三分量（对末点的成对排除）逐层可用。 -/
private theorem isInjContourIsInjList (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (h : H.isInjContour p n) : Loop.IsInjList p n := by
  induction n with
  | zero => intro i j hi hj _; omega
  | succ k ih =>
    obtain ⟨h', -, hnew⟩ := (H.isInjContour_succ p k).mp h
    intro i j hi hj heq
    rcases Nat.eq_or_lt_of_le hj with rfl | hjlt
    · rcases Nat.eq_or_lt_of_le hi with rfl | hilt
      · rfl
      · exact absurd heq (hnew i (by omega))
    · rcases Nat.eq_or_lt_of_le hi with rfl | hilt
      · exact ((hnew j (Nat.lt_succ_iff.mp hjlt)) heq.symm).elim
      · exact ih h' i j (by omega) (by omega) heq

/-- **Plain 组合面（Lvducxu.HYP_MAPS_INVS 的 face/node 对在本章消费形，
HOL :975-:986）**：`faceMap ∘ nodeMap = nodeMap.symm ∘ faceMap.symm`。
在册 `edgeMap_mul_nodeMap`（雷区 #129）+ inv_inv 两发拼出。 -/
private theorem epcFaceMapNodeMap (H : Hypermap α) (hp : H.Plain) (w : α) :
    H.faceMap (H.nodeMap w) = H.nodeMap.symm (H.faceMap.symm w) := by
  have h9 : H.nodeMap = H.edgeMap * H.faceMap.symm :=
    H.nodeMap_eq_edgeMap_mul_faceMap_symm hp
  have hE2 : H.edgeMap.symm = H.edgeMap := by
    show H.edgeMap⁻¹ = H.edgeMap
    exact (eq_inv_of_mul_eq_one_right hp).symm
  have hnf : ∀ v, H.nodeMap (H.faceMap v) = H.edgeMap v := by
    intro v
    have h1 : H.edgeMap (H.nodeMap (H.faceMap v)) = v := by
      have h := congrArg (fun q : Equiv.Perm α => q v) H.comp_eq_one
      simpa using h
    have h2 : H.edgeMap (H.edgeMap (H.nodeMap (H.faceMap v)))
        = H.nodeMap (H.faceMap v) := by
      have h := congrArg (fun q : Equiv.Perm α => q (H.nodeMap (H.faceMap v))) hp
      simpa using h
    rw [h1] at h2
    exact h2.symm
  have hns : H.nodeMap.symm = H.faceMap * H.edgeMap := by
    apply Equiv.Perm.ext
    intro u
    apply Eq.symm
    apply Equiv.injective H.nodeMap
    show H.nodeMap ((H.faceMap * H.edgeMap) u) = H.nodeMap (H.nodeMap.symm u)
    rw [Equiv.Perm.mul_apply, hnf (H.edgeMap u), Equiv.apply_symm_apply H.nodeMap u]
    have hee : H.edgeMap (H.edgeMap u) = u := by
      have h := congrArg (fun q : Equiv.Perm α => q u) hp
      simpa using h
    exact hee
  rw [hns, Equiv.Perm.mul_apply, h9, Equiv.Perm.mul_apply]

/-- **L.map 在补路径上的任意下标求值式**（雷区 #128：p 下标先 hmod
归位，再 samsara_apply，尾段 Nat.mod_add_mod）。 -/
private theorem epcMapStep (H : Hypermap α) {L : Loop α} {p : ℕ → α} {n : ℕ}
    (hinj : Loop.IsInjList p n) (hLm : (L.map : α → α) = Loop.samsara p n)
    (hmod : ∀ m, p (m % (n + 1)) = p m) (j : ℕ) :
    (L.map : α → α) (p j) = p ((j + 1) % (n + 1)) := by
  rw [hLm, ← hmod j, Loop.samsara_apply p n hinj
    (Nat.lt_succ_iff.mp (Nat.mod_lt j (Nat.succ_pos n))), Nat.mod_add_mod]

/-- **L.invMap 在补路径上的任意下标求值式**（雷区 #128：Equiv.Perm.ext
升面 + samsaraPerm 的 invFun 定义面 = samsaraInv）。 -/
private theorem epcInvMapStep (H : Hypermap α) {L : Loop α} {p : ℕ → α} {n : ℕ}
    (hinj : Loop.IsInjList p n) (hLm : (L.map : α → α) = Loop.samsara p n)
    (hmod : ∀ m, p (m % (n + 1)) = p m) (j : ℕ) :
    (L.invMap : α → α) (p j) = p ((j + n) % (n + 1)) := by
  have hE : L.map = Loop.samsaraPerm hinj := Equiv.Perm.ext (fun y => by
    rw [hLm]
    rfl)
  have him : L.invMap = (Loop.samsaraPerm hinj).symm := by
    show L.map.symm = (Loop.samsaraPerm hinj).symm
    rw [hE]
  rw [him, ← hmod j]
  have h1 : (Loop.samsaraPerm hinj).symm (p (j % (n + 1)))
      = Loop.samsaraInv p n (p (j % (n + 1))) := rfl
  rw [h1, Loop.samsaraInv_apply p n hinj
    (Nat.lt_succ_iff.mp (Nat.mod_lt j (Nat.succ_pos n))), Nat.mod_add_mod]

/-- going 传递（雷区 #132：k1+k2 幂加法 + 分段 agree 拼装）。 -/
private theorem epcGoingTrans (H : Hypermap α) {L : Loop α} {a b c : α}
    (h1 : H.IsNodeGoing L a b) (h2 : H.IsNodeGoing L b c) :
    H.IsNodeGoing L a c := by
  obtain ⟨k1, hb, ag1⟩ := h1
  obtain ⟨k2, hc, ag2⟩ := h2
  refine ⟨k1 + k2, ?_, ?_⟩
  · rw [show k1 + k2 = k2 + k1 from Nat.add_comm k1 k2, pow_add,
      Equiv.Perm.mul_apply, ← hb, hc]
  · intro t ht
    rcases Nat.lt_or_ge t k1 with hlt | hge
    · exact ag1 t (by omega)
    · have hs : t - k1 ≤ k2 := by omega
      have e1 : (L.map ^ t) a = (L.map ^ (t - k1)) b := by
        conv_lhs => rw [show t = t - k1 + k1 from by omega, pow_add,
          Equiv.Perm.mul_apply, ← hb]
      conv_rhs => rw [show t = t - k1 + k1 from by omega, pow_add,
        Equiv.Perm.mul_apply]
      rw [e1, ag2 _ hs, hb, ag1 k1 le_rfl]

/-- 段内链：`p m₀ → p m`（m₀ ≤ m ≤ n）且每步 `nodeMap.symm (p t) =
p (t+1)` 时 going 成立（对步数 k 归纳，雷区 #132）。 -/
private theorem epcGoingChain (H : Hypermap α) {L : Loop α} {p : ℕ → α} {n : ℕ}
    (hinj : Loop.IsInjList p n) (hLm : (L.map : α → α) = Loop.samsara p n)
    (m₀ : ℕ) :
    ∀ k m : ℕ, m = m₀ + k → m ≤ n →
      (∀ t, m₀ ≤ t → t < m → H.nodeMap.symm (p t) = p (t + 1)) →
      H.IsNodeGoing L (p m₀) (p m) := by
  intro k
  induction k with
  | zero =>
    intro m hm _ _
    have h0m : m₀ = m := by omega
    subst h0m
    have hbase : H.IsNodeGoing L (p m₀) (p m₀) :=
      ⟨0, rfl, fun i hi => by rw [Nat.le_zero.mp hi, pow_zero, pow_zero]⟩
    exact hbase
  | succ l ih =>
    intro m hm hmn hstep
    have hprev : H.IsNodeGoing L (p m₀) (p (m - 1)) :=
      ih (m - 1) (by omega) (by omega) (fun t ht1 ht2 => hstep t ht1 (by omega))
    have hstepLm : (L.map : α → α) (p (m - 1)) = p m := by
      rw [hLm, Loop.samsara_apply p n hinj (by omega),
        Nat.mod_eq_of_lt (by omega : m - 1 + 1 < n + 1)]
      exact congrArg p (by omega)
    have hlast : H.IsNodeGoing L (p (m - 1)) (p m) := ⟨1, hstepLm.symm, by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [pow_zero, pow_zero]
      · have hi1 : i = 1 := by omega
        subst hi1
        rw [pow_one, pow_one, hstepLm,
          hstep (m - 1) (by omega) (by omega)]
        exact congrArg p (by omega)⟩
    exact epcGoingTrans H hprev hlast

/-- 收口链：`p m₀ → p 0`（m₀ ≤ n）：段内链到 `p n`，再走收口步
（L.map (p n) = p 0 与 nodeMap.symm (p n) = p 0 由 hstep n 给出）。
hstep 的下标到 n 含端点（以 `(t+1) % (n+1)` 形承载，雷区 #128）。 -/
private theorem epcGoingWrap (H : Hypermap α) {L : Loop α} {p : ℕ → α} {n : ℕ}
    (hinj : Loop.IsInjList p n) (hLm : (L.map : α → α) = Loop.samsara p n)
    (m₀ : ℕ) (hm₀ : m₀ ≤ n)
    (hstep : ∀ t, m₀ ≤ t → t ≤ n → H.nodeMap.symm (p t) = p ((t + 1) % (n + 1))) :
    H.IsNodeGoing L (p m₀) (p 0) := by
  have hseg : H.IsNodeGoing L (p m₀) (p n) :=
    epcGoingChain H hinj hLm m₀ (n - m₀) n (by omega) (Nat.le_refl n)
      (fun t ht1 ht2 => by
        rw [hstep t ht1 (by omega), Nat.mod_eq_of_lt (by omega : t + 1 < n + 1)])
  have hlast : H.IsNodeGoing L (p n) (p 0) := ⟨1, by
    rw [pow_one, hLm, Loop.samsara_apply p n hinj (Nat.le_refl n), Nat.mod_self], by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pow_zero, pow_zero]
    · have hi1 : i = 1 := by omega
      subst hi1
      rw [pow_one, pow_one, hLm, Loop.samsara_apply p n hinj (Nat.le_refl n),
        Nat.mod_self]
      rw [hstep n hm₀ (Nat.le_refl n), Nat.mod_self]⟩
  exact epcGoingTrans H hseg hlast

/-- `nodeMap.symm^(N-1) z = nodeMap z`（N = |node z|；segment-cf
修正式的载体件）：两侧同施 nodeMap^(N-1)，左 = z
（perm_pow_symm_pow_apply_ge + sub_self + pow_zero），右 =
z（pow_card_node_apply_self 的 pow_succ 拆分）。 -/
private theorem epcSymmPredNodeMap (H : Hypermap α) (z : α) :
    (H.nodeMap.symm ^ ((H.node z).ncard - 1)) z = H.nodeMap z := by
  have hcancel : (H.nodeMap ^ ((H.node z).ncard - 1))
      ((H.nodeMap.symm ^ ((H.node z).ncard - 1)) z) = z := by
    have h := perm_pow_symm_pow_apply_ge (p := H.nodeMap)
      (s := (H.node z).ncard - 1) (t := (H.node z).ncard - 1) (Nat.le_refl _) z
    rwa [Nat.sub_self, pow_zero] at h
  have hN1 : (H.node z).ncard - 1 + 1 = (H.node z).ncard := by
    have hzpos : 0 < (H.node z).ncard := by
      show 0 < (orbitMap H.nodeMap z).ncard
      rw [Set.ncard_pos (orbitMap_finite H.nodeMap_permutes z)]
      exact ⟨z, H.mem_node_self z⟩
    omega
  have hR : (H.nodeMap ^ ((H.node z).ncard - 1)) (H.nodeMap z) = z := by
    have e : (H.nodeMap ^ ((H.node z).ncard - 1 + 1)) z
        = (H.nodeMap ^ ((H.node z).ncard - 1)) (H.nodeMap z) := by
      rw [pow_succ, Equiv.Perm.mul_apply]
    rw [← e, hN1]
    exact H.pow_card_node_apply_self z
  refine Equiv.injective (H.nodeMap ^ ((H.node z).ncard - 1)) ?_
  rw [hcancel, hR]

/-- N = 2 时 nodeMap.symm x = nodeMap x（nodeMap² x = x 的等价形；
合取 10/11 的 N_x = 2 支用）。 -/
private theorem epcNodeSymmEqOfTwo (H : Hypermap α) (x : α)
    (hN2 : (H.node x).ncard = 2) : H.nodeMap.symm x = H.nodeMap x := by
  have h2 : (H.nodeMap ^ 2) x = x := by
    have h := H.pow_card_node_apply_self x
    rwa [show H.nodeMap ^ (H.node x).ncard = H.nodeMap ^ 2 from by rw [hN2]] at h
  exact Equiv.injective H.nodeMap (by
    rw [Equiv.apply_symm_apply]
    exact h2.symm)

/-- node 基数正性（任意 dart；供 mod_lt/omega 门楽）。 -/
private theorem epcNodePos (H : Hypermap α) (hnn : H.NodeNondegenerate) {u : α}
    (hu : u ∈ H.darts) : 0 < (H.node u).ncard := by
  show 0 < (orbitMap H.nodeMap u).ncard
  rw [Set.ncard_pos (orbitMap_finite H.nodeMap_permutes u)]
  exact ⟨u, H.mem_node_self u⟩

/-- **hLd 换算桥（雷区 #136）**：y ∈ L.darts ⟹ ∃ m ≤ n，p m = y
（hLd 的 coe 实例面经 show-defeq 统一）。 -/
private theorem epcMemSupport (H : Hypermap α) {x : α} (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    {y : α} (hy : y ∈ L.darts) :
    ∃ m ≤ n, H.complementPt x m = y := by
  have h1 : y ∈ (Loop.pathSupport (H.complementPt x) n : Set α) := by
    rw [← hLd]
    exact Finset.mem_coe.mpr hy
  have h2 : y ∈ Loop.pathSupport (H.complementPt x) n := h1
  rw [Loop.mem_pathSupport] at h2
  exact h2

/-! ### §1 段①证人 L 支：node 分裂（AUQTZYZ.hl :666-:686） -/

/-- 补路径首两点异 node：`node (p 0) = node (p 1)` 导出
`faceMap.symm x = x`，与面轨道窗口单射（j = 1 < CARD face）矛盾。
（HOL :666-:686 走 lemma_different_nodes + CARD_FACE_LE3；Lean 面
塌缩到 orbitMap_pow_inj 一发，终点同——雷区 #122 体例。） -/
private theorem epcNodeSplit (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) :
    H.node (H.complementPt x 0) ≠ H.node (H.complementPt x 1) := by
  intro hcon
  have hnn := hr.nodeNondegenerate
  have hs := hr.simple
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  -- 雷区 #134：字面下标 1 先经 ascription have 塌缩
  have h01 : H.complementPt x 1 = H.nodeMap.symm ((H.faceMap.symm ^ 1) x) :=
    H.complementPt_compIndex_succ_eval hnn hx 0
  rw [h01, show H.complementPt x 0 = H.nodeMap x from rfl] at hcon
  have h1 : H.node (H.nodeMap x) = H.node x :=
    (H.node_eq_of_mem (H.pow_nodeMap_mem_node x 1)).symm
  have h2 : H.node (H.nodeMap.symm ((H.faceMap.symm ^ 1) x))
      = H.node ((H.faceMap.symm ^ 1) x) :=
    (H.node_eq_of_mem
      (H.nodeMap_symm_mem_node (H.mem_node_self ((H.faceMap.symm ^ 1) x)))).symm
  rw [h1, h2] at hcon
  have hmem : (H.faceMap.symm ^ 1) x ∈ H.node x := by
    rw [hcon]
    exact H.mem_node_self _
  have hfin : (H.faceMap.symm ^ 1) x ∈ H.face x :=
    H.faceMap_symm_pow_mem_face_self x 1
  have hmem2 : (H.faceMap.symm ^ 1) x ∈ H.node x ∩ H.face x := ⟨hmem, hfin⟩
  rw [hs x hx] at hmem2
  have heq : (H.faceMap.symm ^ 1) x = x := Set.mem_singleton_iff.mp hmem2
  have hz0 : (H.faceMap.symm ^ 0) x = (H.faceMap.symm ^ 1) x := by
    show x = H.faceMap.symm x
    exact heq.symm
  refine orbitMap_pow_inj (p := H.faceMap.symm) H.faceMap_permutes.symm
    (a := 0) (b := 1) (by omega) ?_ hz0
  rw [PermutesOn.orbitMap_symm H.faceMap_permutes x]
  show 1 < (H.face x).ncard
  omega

/-! ### §2 段⑤：互斥与双闭包（AUQTZYZ.hl :698-:1000，合取 5-7） -/

/-- **均匀成员件（本批主方法论）**：任意下标 m 的补路径点都在
L.darts（p m = p (m % (n+1))，hmod 一发；压平 HOL 全部 support 下标
±1 边界 case）。 -/
private theorem epcMemPath (H : Hypermap α) {x : α} (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m) (m : ℕ) :
    H.complementPt x m ∈ L.darts := by
  have h1 : H.complementPt x m ∈ (Loop.pathSupport (H.complementPt x) n : Set α) := by
    show H.complementPt x m ∈ Loop.pathSupport (H.complementPt x) n
    rw [Loop.mem_pathSupport]
    exact ⟨m % (n + 1), Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos n)),
      hmod m⟩
  rw [← hLd] at h1
  exact Finset.mem_coe.mpr h1

/-- **合取 5 核**：补路径前 n+1 点无一在 face x 内。
i = 0 支：nodeMap x = x ⟹ 轨道单点 ⟹ |node x| ≤ 1（HOL :708-:713）；
1 ≤ i 支：strictInc_partition₂ 分解 + Simple 单点塌出
nodeMap.symm^j z = z，orbitMap_pow_inj 灭（HOL :715-:733）。 -/
private theorem epcDisjoint (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) (hn : H.complementIndex x (H.face x).ncard - 1 = n) :
    ∀ m ≤ n, H.complementPt x m ∉ H.face x := by
  have hnn := hr.nodeNondegenerate
  have hs := hr.simple
  have hn2x : 2 ≤ (H.node x).ncard := H.nodeNondegenerate_two_le.mp hnn x hx
  intro m hm hmem
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hmem2 : H.nodeMap x ∈ H.node x ∩ H.face x :=
      ⟨H.pow_nodeMap_mem_node x 1, hmem⟩
    rw [hs x hx] at hmem2
    have hfix : H.nodeMap x = x := Set.mem_singleton_iff.mp hmem2
    have hsingle : H.node x = {x} := (orbitMap_singleton_iff H.nodeMap x).mpr hfix
    rw [hsingle] at hn2x
    simp at hn2x
  · obtain hzero | ⟨i, j, hj1, hj2, hrep⟩ := strictInc_partition₂
      (f := H.complementIndex x) (H.complementIndex_zero_eq x)
      (H.complementIndex_lt_succ hnn hx) m
    · exact absurd hzero (by omega)
    have hjN : j < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard := by
      have hs2 := H.complementIndex_succ_eq_sub hnn hx i
      omega
    have hev : H.complementPt x m
        = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ (i + 1)) x) := by
      rw [hrep]
      exact H.complementPt_add_eval hnn hx i j hj1 hjN
    have hz : (H.faceMap.symm ^ (i + 1)) x ∈ H.darts :=
      H.faceMap_symm_pow_mem_darts hx (i + 1)
    have hmemn : H.complementPt x m ∈ H.node ((H.faceMap.symm ^ (i + 1)) x) := by
      rw [hev]
      exact H.nodeMap_symm_pow_mem_node_self _ j
    have hfacez : H.face x = H.face ((H.faceMap.symm ^ (i + 1)) x) :=
      H.face_eq_of_mem (H.faceMap_symm_pow_mem_face_self x (i + 1))
    have hmem2 : H.complementPt x m ∈ H.node ((H.faceMap.symm ^ (i + 1)) x) ∩
        H.face ((H.faceMap.symm ^ (i + 1)) x) := ⟨hmemn, by rw [← hfacez]; exact hmem⟩
    rw [hs _ hz] at hmem2
    have hfixz : (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ (i + 1)) x)
        = (H.faceMap.symm ^ (i + 1)) x :=
      hev.symm.trans (Set.mem_singleton_iff.mp hmem2)
    have hbm : j < (orbitMap H.nodeMap.symm ((H.faceMap.symm ^ (i + 1)) x)).ncard := by
      rw [PermutesOn.orbitMap_symm H.nodeMap_permutes]
      show j < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard
      exact hjN
    exact orbitMap_pow_inj (p := H.nodeMap.symm) H.nodeMap_permutes.symm
      (a := 0) (b := j) hj1 hbm (by rw [pow_zero, Equiv.Perm.one_apply, hfixz])

/-- 段内 nodeMap.symm 步：`ci x i + 1 ≤ t ≤ ci x (i+1) - 1` 时
`nodeMap.symm (p t) = p (t+1)`（segEval 双发）。 -/
private theorem epcStepSeg (H : Hypermap α) {x : α} (hnn : H.NodeNondegenerate)
    (hx : x ∈ H.darts) (i t : ℕ)
    (h1 : H.complementIndex x i + 1 ≤ t)
    (h2 : t + 1 ≤ H.complementIndex x (i + 1)) :
    H.nodeMap.symm (H.complementPt x t) = H.complementPt x (t + 1) := by
  have hciS : H.complementIndex x (i + 1)
      = H.complementIndex x i + ((H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard - 1) :=
    H.complementIndex_succ_eq_sub hnn hx i
  have hj1 : 1 ≤ t - H.complementIndex x i := by omega
  have hjN : t - H.complementIndex x i + 1
      < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard := by omega
  have hev1 : H.complementPt x t
      = (H.nodeMap.symm ^ (t - H.complementIndex x i))
        ((H.faceMap.symm ^ (i + 1)) x) := by
    conv_lhs => rw [show t = H.complementIndex x i + (t - H.complementIndex x i) from by omega]
    exact H.complementPt_add_eval hnn hx i _ hj1 (by omega)
  have hev2 : H.complementPt x (t + 1)
      = (H.nodeMap.symm ^ (t - H.complementIndex x i + 1))
        ((H.faceMap.symm ^ (i + 1)) x) := by
    have h3 : H.complementPt x (t + 1)
        = H.complementPt x (H.complementIndex x i
          + (t - H.complementIndex x i + 1)) := by
      rw [show t + 1 = H.complementIndex x i
        + (t - H.complementIndex x i + 1) from by omega]
    rw [h3, H.complementPt_add_eval hnn hx i _ (by omega) (by omega)]
  rw [hev1, hev2, pow_succ'_apply H.nodeMap.symm (t - H.complementIndex x i) _]

/-- 收口步（N_x ≥ 3）：`nodeMap.symm (p n) = p 0`。
p n = symm^(N_x-2) z_cf（尾段末点），symm 后 = symm^(N_x-1) z_cf =
nodeMap z_cf（epcSymmPredNodeMap）= nodeMap x（cycle）= p 0。 -/
private theorem epcStepWrapN3 (H : Hypermap α) {x : α} (hnn : H.NodeNondegenerate)
    (hx : x ∈ H.darts) (n : ℕ) (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    (hcf3 : 3 ≤ (H.face x).ncard) (hN3 : 3 ≤ (H.node x).ncard) :
    H.nodeMap.symm (H.complementPt x n) = H.complementPt x 0 := by
  have hp0 : H.complementPt x 0 = H.nodeMap x := rfl
  have h1cf : 1 ≤ H.complementIndex x (H.face x).ncard :=
    complementIndexFaceLe1 H hnn hx
  have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
      = (H.node x).ncard := by
    refine congrArg (fun v => (H.node v).ncard) ?_
    exact inverseFaceCycle H x
  have hci1 : H.complementIndex x (H.face x).ncard
      = H.complementIndex x ((H.face x).ncard - 1) + ((H.node x).ncard - 1) := by
    have h2 := H.complementIndex_succ_eq_sub hnn hx ((H.face x).ncard - 1)
    rw [show (H.face x).ncard - 1 + 1 = (H.face x).ncard from by omega] at h2
    rwa [hNcf] at h2
  have hk1 : 1 ≤ n - H.complementIndex x ((H.face x).ncard - 1) := by omega
  have hk2 : n - H.complementIndex x ((H.face x).ncard - 1) < (H.node x).ncard := by
    omega
  have hev : H.complementPt x n
      = (H.nodeMap.symm ^ (n - H.complementIndex x ((H.face x).ncard - 1)))
        ((H.faceMap.symm ^ (H.face x).ncard) x) := by
    conv_lhs => rw [show n = H.complementIndex x ((H.face x).ncard - 1)
      + (n - H.complementIndex x ((H.face x).ncard - 1)) from by omega]
    have hcfN2 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
    have hlt : n - H.complementIndex x ((H.face x).ncard - 1)
        < (H.node ((H.faceMap.symm ^ ((H.face x).ncard - 1 + 1)) x)).ncard := by
      rw [hcfN2, hNcf]
      omega
    have h5 := H.complementPt_add_eval hnn hx ((H.face x).ncard - 1)
      (n - H.complementIndex x ((H.face x).ncard - 1)) hk1 hlt
    rwa [hcfN2] at h5
  have step1 : H.nodeMap.symm
      ((H.nodeMap.symm ^ (n - H.complementIndex x ((H.face x).ncard - 1)))
        ((H.faceMap.symm ^ (H.face x).ncard) x))
      = (H.nodeMap.symm ^ ((H.node x).ncard - 1))
        ((H.faceMap.symm ^ (H.face x).ncard) x) := by
    rw [← pow_succ'_apply H.nodeMap.symm
      (n - H.complementIndex x ((H.face x).ncard - 1))
      ((H.faceMap.symm ^ (H.face x).ncard) x),
      show n - H.complementIndex x ((H.face x).ncard - 1) + 1
        = (H.node x).ncard - 1 by omega]
  rw [hev, step1, ← hNcf, epcSymmPredNodeMap, inverseFaceCycle, hp0]

/-- **合取 6**：y ∈ L ⟹ z ∈ node y ⟹ z ∈ L ∨ z ∈ face x。
（HOL :735-:885 的全线 case 分析；hmod 均匀成员件压平 witness。） -/
private theorem epcClosureIn (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m)
    (y : α) (hy : y ∈ L.darts) (z : α) (hz : z ∈ H.node y) :
    z ∈ L.darts ∨ z ∈ H.face x := by
  have hnn := hr.nodeNondegenerate
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hmem : ∀ m, H.complementPt x m ∈ L.darts := fun m => epcMemPath H n hLd hmod m
  obtain ⟨m, hm, hym⟩ := epcMemSupport H n hLd hy
  obtain ⟨j, hjN, hzj⟩ := H.exists_pow_nodeMap_symm_apply_of_mem_node hz
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact Or.inl (by rw [hzj, pow_zero]; exact hy)
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · -- y = p 0 = nodeMap x：j = 1 给 x ∈ face x；j ≥ 2 走尾段 witness
    have hyn : y = H.nodeMap x := by rw [← hym]; rfl
    have hny : (H.node y).ncard = (H.node x).ncard := by
      rw [hyn, nodeNodeMapEq H x]
    rw [hny] at hjN
    have hzm : z = (H.nodeMap.symm ^ j) (H.nodeMap x) := by rw [hzj, hyn]
    have hjm : j = j - 1 + 1 := by omega
    have hz1 : z = (H.nodeMap.symm ^ (j - 1)) x := by
      rw [hzm]
      conv_lhs => rw [hjm, pow_succ, Equiv.Perm.mul_apply]
      rw [Equiv.symm_apply_apply]
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hje : j = 1 := by omega
      rw [hje] at hz1
      refine Or.inr ?_
      rw [hz1, show (1:ℕ) - 1 = 0 from by omega, pow_zero]
      exact mem_orbitMap_self H.faceMap x
    · have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
          = (H.node x).ncard := by
        refine congrArg (fun v => (H.node v).ncard) ?_
        exact inverseFaceCycle H x
      have hcf1 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
      have hkN : j - 1 < (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard := by
        omega
      have hev : H.complementPt x (H.complementIndex x ((H.face x).ncard - 1)
            + (j - 1))
            = (H.nodeMap.symm ^ (j - 1))
              ((H.faceMap.symm ^ ((H.face x).ncard - 1 + 1)) x) :=
        H.complementPt_add_eval hnn hx _ _ (by omega)
          (by rw [show (H.face x).ncard = (H.face x).ncard - 1 + 1 from by omega] at hkN
              exact hkN)
      rw [hcf1] at hev
      refine Or.inl ?_
      rw [hz1, show x = (H.faceMap.symm ^ (H.face x).ncard) x from (inverseFaceCycle H x).symm,
        ← hev]
      exact hmem _
  · -- m ≥ 1：strictInc 分解，j+j₀ 取模 N_{i+1} 后段内 witness
    obtain hzero | ⟨i, j₀, hj1₀, hj2₀, hrep⟩ := strictInc_partition₂
      (f := H.complementIndex x) (H.complementIndex_zero_eq x)
      (H.complementIndex_lt_succ hnn hx) m
    · exact absurd hzero (by omega)
    have hjN₀ : j₀ < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard := by
      have hs2 := H.complementIndex_succ_eq_sub hnn hx i
      omega
    have hevy : y = (H.nodeMap.symm ^ j₀) ((H.faceMap.symm ^ (i + 1)) x) := by
      rw [← hym, hrep]
      exact H.complementPt_add_eval hnn hx i j₀ hj1₀ hjN₀
    have hzK : z = (H.nodeMap.symm ^
        ((j + j₀) % (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard))
        ((H.faceMap.symm ^ (i + 1)) x) := by
      rw [hzj, hevy, ← Equiv.Perm.mul_apply, ← pow_add,
        inverseNodeMod H ((H.faceMap.symm ^ (i + 1)) x) (j + j₀)]
    rcases Nat.eq_zero_or_pos
      ((j + j₀) % (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard) with hK0 | hK1
    · refine Or.inr ?_
      rw [hzK, hK0, pow_zero]
      exact H.faceMap_symm_pow_mem_face_self x (i + 1)
    · refine Or.inl ?_
      rw [hzK, ← H.complementPt_add_eval hnn hx i _ hK1
        (Nat.mod_lt _ (epcNodePos H hnn
          (H.faceMap_symm_pow_mem_darts hx (i + 1))))]
      exact hmem _

/-- **合取 7**：y ∈ face x ⟹ z ∈ node y ⟹ z ∈ L ∨ z ∈ face x。
（HOL :917-:1000；i = 0 支的 j = N-1 端点经 epcSymmPredNodeMap 落
p 0。） -/
private theorem epcClosureFace (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m)
    (y : α) (hy : y ∈ H.face x) (z : α) (hz : z ∈ H.node y) :
    z ∈ L.darts ∨ z ∈ H.face x := by
  have hnn := hr.nodeNondegenerate
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hn2x : 2 ≤ (H.node x).ncard := H.nodeNondegenerate_two_le.mp hnn x hx
  have hmem : ∀ m, H.complementPt x m ∈ L.darts := fun m => epcMemPath H n hLd hmod m
  obtain ⟨i, hi, hyi⟩ := lemmaViaInverseFaceMap H hy
  obtain ⟨j, hjN, hzj⟩ := H.exists_pow_nodeMap_symm_apply_of_mem_node hz
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact Or.inr (by rw [hzj, pow_zero]; exact hy)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- y = x：j = N-1 端点给 nodeMap x = p 0 ∈ L；j ≤ N-2 走尾段
    have hz1 : z = (H.nodeMap.symm ^ j) x := by
      rw [hzj, hyi, pow_zero, Equiv.Perm.one_apply]
    rw [hyi, pow_zero, Equiv.Perm.one_apply] at hjN
    rcases Nat.lt_or_ge j ((H.node x).ncard - 1) with hj2 | hj2
    · have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
          = (H.node x).ncard := by
        refine congrArg (fun v => (H.node v).ncard) ?_
        exact inverseFaceCycle H x
      have hcf1 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
      have hkN : j < (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard := by
        omega
      have hev : H.complementPt x (H.complementIndex x ((H.face x).ncard - 1) + j)
          = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ ((H.face x).ncard - 1 + 1)) x) :=
        H.complementPt_add_eval hnn hx _ _ hj0
          (by rw [show (H.face x).ncard = (H.face x).ncard - 1 + 1 from by omega] at hkN
              exact hkN)
      rw [hcf1] at hev
      refine Or.inl ?_
      rw [hz1, show x = (H.faceMap.symm ^ (H.face x).ncard) x from
        (inverseFaceCycle H x).symm, ← hev]
      exact hmem _
    · have hje : j = (H.node x).ncard - 1 := by omega
      refine Or.inl ?_
      rw [hz1, hje, epcSymmPredNodeMap]
      exact hmem 0
  · -- y = z_i（1 ≤ i < cf）：z = symm^j z_i，段 i 内 witness ci (i-1) + j
    have hz1 : z = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ i) x) := by
      rw [hzj, hyi]
    have hjN2 : j < (H.node ((H.faceMap.symm ^ i) x)).ncard := by
      rw [hyi] at hjN
      exact hjN
    have hcf1 : i - 1 + 1 = i := by omega
    have hev : H.complementPt x (H.complementIndex x (i - 1) + j)
        = (H.nodeMap.symm ^ j) ((H.faceMap.symm ^ (i - 1 + 1)) x) := by
      rw [← hcf1] at hjN2
      exact H.complementPt_add_eval hnn hx _ _ hj0 hjN2
    rw [hcf1] at hev
    refine Or.inl ?_
    rw [hz1, ← hev]
    exact hmem _

/-! ### §3 段③：card 支（AUQTZYZ.hl :916-:1418，合取 8） -/

/-- f = `fun i => p (ci x i + 1)` 在 i < cf 上单射（HOL :925-:979 的
f-单射段；Lean 路线：succEval 直评 + nodeMap.symm 单射 + 面轨道窗口
单射，INVERSE_ADD_EXPONENTS/ORBIT_MAP_INJ 消费点塌缩，缺口件裁定见
文件头）。 -/
private theorem epcFInj (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) :
    ∀ i j : ℕ, i < (H.face x).ncard → j < (H.face x).ncard →
      H.complementPt x (H.complementIndex x i + 1)
        = H.complementPt x (H.complementIndex x j + 1) → i = j := by
  have hzNe : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ (H.face x).ncard →
      (H.faceMap.symm ^ i) x ≠ (H.faceMap.symm ^ j) x := by
    intro i j hi1 hij hjle hcon
    rcases Nat.lt_or_ge j (H.face x).ncard with hlt | hge
    · refine orbitMap_pow_inj (p := H.faceMap.symm) H.faceMap_permutes.symm
        (a := i) (b := j) hij ?_ hcon
      rw [PermutesOn.orbitMap_symm H.faceMap_permutes x]
      show j < (H.face x).ncard
      exact hlt
    · have hjcf : j = (H.face x).ncard := by omega
      have hiz0 : (H.faceMap.symm ^ i) x = x := by
        rw [hcon, hjcf]
        exact inverseFaceCycle H x
      refine orbitMap_pow_inj (p := H.faceMap.symm) H.faceMap_permutes.symm
        (a := 0) (b := i) (by omega) ?_ (by rw [pow_zero, Equiv.Perm.one_apply, hiz0])
      rw [PermutesOn.orbitMap_symm H.faceMap_permutes x]
      show i < (H.face x).ncard
      omega
  intro i j hi hj hcon
  have hz : (H.faceMap.symm ^ (i + 1)) x = (H.faceMap.symm ^ (j + 1)) x := by
    rw [H.complementPt_compIndex_succ_eval (hr.nodeNondegenerate) hx i,
      H.complementPt_compIndex_succ_eval (hr.nodeNondegenerate) hx j] at hcon
    have h2 := congrArg H.nodeMap hcon
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hz (hzNe (i + 1) (j + 1) (by omega) (by omega) (by omega))
  · exact h
  · exact absurd hz.symm (hzNe (j + 1) (i + 1) (by omega) (by omega) (by omega))

/-- atom ∘ f 在 i < cf 上单射（HOL :1285-:1400 的 g-单射段；雷区
#130 node 交塌缩 + Simple 单点 + 面窗口单射）。 -/
private theorem epcAtomInj (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) {L : Loop α} :
    ∀ i j : ℕ, i < (H.face x).ncard → j < (H.face x).ncard →
      H.atom L (H.complementPt x (H.complementIndex x i + 1))
        = H.atom L (H.complementPt x (H.complementIndex x j + 1)) → i = j := by
  have hnn := hr.nodeNondegenerate
  have hs := hr.simple
  have hf : ∀ k : ℕ, H.complementPt x (H.complementIndex x k + 1)
      = H.nodeMap.symm ((H.faceMap.symm ^ (k + 1)) x) :=
    fun k => H.complementPt_compIndex_succ_eval hnn hx k
  have hfin : ∀ k : ℕ,
      H.complementPt x (H.complementIndex x k + 1)
        ∈ H.node ((H.faceMap.symm ^ (k + 1)) x) := by
    intro k
    rw [hf k]
    exact H.nodeMap_symm_mem_node (H.mem_node_self _)
  have hnode : ∀ k : ℕ, H.node (H.complementPt x (H.complementIndex x k + 1))
      = H.node ((H.faceMap.symm ^ (k + 1)) x) :=
    fun k => (H.node_eq_of_mem (hfin k)).symm
  intro i j hi hj hcon
  -- f j ∈ atom L (f i) ⊆ node (f i) = node z_{i+1} ⟹ node (f j) = node z_{i+1}
  have hmemj : H.complementPt x (H.complementIndex x j + 1)
      ∈ H.node ((H.faceMap.symm ^ (i + 1)) x) := by
    have h1 : H.complementPt x (H.complementIndex x j + 1)
        ∈ H.atom L (H.complementPt x (H.complementIndex x i + 1)) := by
      rw [hcon]
      exact H.atom_reflect _ _
    have h2 := H.atom_subset_node (L := L)
      (x := H.complementPt x (H.complementIndex x i + 1)) h1
    rw [hnode i] at h2
    exact h2
  have hnodej : H.node (H.complementPt x (H.complementIndex x j + 1))
      = H.node ((H.faceMap.symm ^ (i + 1)) x) :=
    (H.node_eq_of_mem hmemj).symm
  -- z_{i+1} = nodeMap (f i) ∈ node (f i) = node (f j) = node z_{j+1}
  have hzi : (H.faceMap.symm ^ (i + 1)) x
      ∈ H.node (H.complementPt x (H.complementIndex x j + 1)) := by
    have h1 : (H.faceMap.symm ^ (i + 1)) x
        = H.nodeMap (H.complementPt x (H.complementIndex x i + 1)) := by
      rw [hf i, Equiv.apply_symm_apply]
    rw [h1, hnodej]
    exact H.nodeMap_mem_node_of_mem_node (hfin i)
  -- Simple 塌出 z_{i+1} = z_{j+1}
  have hzjD : (H.faceMap.symm ^ (j + 1)) x ∈ H.darts :=
    H.faceMap_symm_pow_mem_darts hx (j + 1)
  have hfacez : H.face x = H.face ((H.faceMap.symm ^ (j + 1)) x) :=
    H.face_eq_of_mem (H.faceMap_symm_pow_mem_face_self x (j + 1))
  have hmem2 : (H.faceMap.symm ^ (i + 1)) x
      ∈ H.node ((H.faceMap.symm ^ (j + 1)) x)
        ∩ H.face ((H.faceMap.symm ^ (j + 1)) x) :=
    ⟨by rw [← hnode j]; exact hzi,
      by rw [← hfacez]; exact H.faceMap_symm_pow_mem_face_self x (i + 1)⟩
  rw [hs _ hzjD] at hmem2
  have heqz : (H.faceMap.symm ^ (i + 1)) x = (H.faceMap.symm ^ (j + 1)) x :=
    Set.mem_singleton_iff.mp hmem2
  have hzNe : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ (H.face x).ncard →
      (H.faceMap.symm ^ a) x ≠ (H.faceMap.symm ^ b) x := by
    intro a b ha1 hab hble hcon
    rcases Nat.lt_or_ge b (H.face x).ncard with hlt | hge
    · refine orbitMap_pow_inj (p := H.faceMap.symm) H.faceMap_permutes.symm
        (a := a) (b := b) hab ?_ hcon
      rw [PermutesOn.orbitMap_symm H.faceMap_permutes x]
      show b < (H.face x).ncard
      exact hlt
    · have hbcf : b = (H.face x).ncard := by omega
      have hiz0 : (H.faceMap.symm ^ a) x = x := by
        rw [hcon, hbcf]
        exact inverseFaceCycle H x
      refine orbitMap_pow_inj (p := H.faceMap.symm) H.faceMap_permutes.symm
        (a := 0) (b := a) (by omega) ?_ (by rw [pow_zero, Equiv.Perm.one_apply, hiz0])
      rw [PermutesOn.orbitMap_symm H.faceMap_permutes x]
      show a < (H.face x).ncard
      omega
  rcases lt_trichotomy i j with h | h | h
  · exact absurd heqz (hzNe (i + 1) (j + 1) (by omega) (by omega) (by omega))
  · exact h
  · exact absurd heqz.symm (hzNe (j + 1) (i + 1) (by omega) (by omega) (by omega))

/-- **合取 8**：CARD (atoms_of_loop H L) = CARD (face H x)。
（HOL :916-:1418 主链：f 单射给 |s| = cf；逐 dart 原子归位到 s
（m = 0 支：N_x = 2 时同点、N_x ≥ 3 时 going 收口链；m ≥ 1 支：
段内 going 链）；atom ∘ f 单射；ncard 计数。） -/
private theorem epcCard (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ)
    (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hLm : (L.map : α → α) = Loop.samsara (H.complementPt x) n)
    (hinj : Loop.IsInjList (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m) :
    (H.atomsOfLoop L).ncard = (H.face x).ncard := by
  have hnn := hr.nodeNondegenerate
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hn2x : 2 ≤ (H.node x).ncard := H.nodeNondegenerate_two_le.mp hnn x hx
  have h1cf : 1 ≤ H.complementIndex x (H.face x).ncard :=
    complementIndexFaceLe1 H hnn hx
  have hcfN : n + 1 = H.complementIndex x (H.face x).ncard := by omega
  have hmem : ∀ m, H.complementPt x m ∈ L.darts := fun m => epcMemPath H n hLd hmod m
  have hcf1 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
  have hp0 : H.complementPt x 0 = H.nodeMap x := rfl
  have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
      = (H.node x).ncard := by
    refine congrArg (fun v => (H.node v).ncard) ?_
    exact inverseFaceCycle H x
  have hci1 : H.complementIndex x (H.face x).ncard
      = H.complementIndex x ((H.face x).ncard - 1) + ((H.node x).ncard - 1) := by
    have h2 := H.complementIndex_succ_eq_sub hnn hx ((H.face x).ncard - 1)
    rw [hcf1] at h2
    rwa [hNcf] at h2
  -- 原子族 = atom L ∘ f 在 {i | i < cf} 上的像
  have hAE : H.atomsOfLoop L
      = (fun i => H.atom L (H.complementPt x (H.complementIndex x i + 1)))
        '' {i : ℕ | i < (H.face x).ncard} := by
    ext A
    simp only [Hypermap.atomsOfLoop, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m, hm, hym⟩ := epcMemSupport H n hLd hu
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · -- u = p 0：归位到尾段首点 f (cf-1)
        rw [← hym]
        refine ⟨(H.face x).ncard - 1, by omega, ?_⟩
        have key : H.complementPt x 0 ∈ H.atom L
            (H.complementPt x (H.complementIndex x ((H.face x).ncard - 1) + 1)) := by
          rcases Nat.lt_or_ge (H.node x).ncard 3 with hN2' | hN3
          · -- N_x = 2：f (cf-1) = nodeMap.symm x = nodeMap x = p 0，同点
            have hN2 : (H.node x).ncard = 2 := by omega
            have hevy : H.complementPt x
                (H.complementIndex x ((H.face x).ncard - 1) + 1)
                = H.complementPt x 0 := by
              rw [H.complementPt_compIndex_succ_eval hnn hx _, hcf1, inverseFaceCycle,
                epcNodeSymmEqOfTwo H x hN2, hp0]
            rw [hevy]
            exact H.atom_reflect _ _
          · -- N_x ≥ 3：going 收口链 p (ci (cf-1)+1) → p 0
            have hm₀ : H.complementIndex x ((H.face x).ncard - 1) + 1 ≤ n := by omega
            have hstep : ∀ t, H.complementIndex x ((H.face x).ncard - 1) + 1 ≤ t →
                t ≤ n → H.nodeMap.symm (H.complementPt x t)
                  = H.complementPt x ((t + 1) % (n + 1)) := by
              intro t ht1 ht2
              rcases Nat.lt_or_ge t n with hlt | hle
              · rw [epcStepSeg H hnn hx ((H.face x).ncard - 1) t ht1
                  (by rw [hcf1, ← hcfN]; omega), Nat.mod_eq_of_lt (by omega)]
              · rw [show t = n from by omega, epcStepWrapN3 H hnn hx n hn hcf3
                  (by omega), Nat.mod_self]
            exact Or.inl (epcGoingWrap H hinj hLm _ hm₀ hstep)
        rw [H.atom_eq_of_mem key]
      · -- u = p m（m ≥ 1）：段内 going 链归位到段首 f i
        rw [← hym]
        obtain hzero | ⟨i, j₀, hj1₀, hj2₀, hrep⟩ := strictInc_partition₂
          (f := H.complementIndex x) (H.complementIndex_zero_eq x)
          (H.complementIndex_lt_succ hnn hx) m
        · exact absurd hzero (by omega)
        have hjN₀ : j₀ < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard := by
          have hs2 := H.complementIndex_succ_eq_sub hnn hx i
          omega
        have hilt : i < (H.face x).ncard := by
          by_contra hge
          have hge' : (H.face x).ncard ≤ i := by omega
          have hle := H.complementIndex_le_of_le hnn hx hge'
          omega
        refine ⟨i, hilt, ?_⟩
        have hm₀ : H.complementIndex x i + 1 ≤ m := by omega
        have hgoing := epcGoingChain H hinj hLm
          (H.complementIndex x i + 1) (m - (H.complementIndex x i + 1)) m
          (by omega) hm
          (fun t ht1 ht2 => epcStepSeg H hnn hx i t ht1 (by omega))
        have hmemm : H.complementPt x m ∈ H.atom L
            (H.complementPt x (H.complementIndex x i + 1)) := Or.inl hgoing
        rw [← H.atom_eq_of_mem hmemm]
    · rintro ⟨i, hi, rfl⟩
      exact ⟨H.complementPt x (H.complementIndex x i + 1), hmem _, rfl⟩
  have hset : {i : ℕ | i < (H.face x).ncard}
      = ((Finset.range (H.face x).ncard : Finset ℕ) : Set ℕ) := by
    ext i; simp
  rw [hAE, hset]
  -- 计数：injOn + ncard_image + coe 基数
  have hInjOn : Set.InjOn
      (fun i => H.atom L (H.complementPt x (H.complementIndex x i + 1)))
      ((Finset.range (H.face x).ncard : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hab
    exact epcAtomInj H hr hx a b (by simpa using ha) (by simpa using hb) hab
  have hfin2 : ((Finset.range (H.face x).ncard : Finset ℕ) : Set ℕ).Finite :=
    (Finset.range _).finite_toSet
  rw [hInjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]

/-! ### §4 段④：双射桥（AUQTZYZ.hl :1421-:1850，合取 9-12） -/

/-- **face-atom 单点件**：w ∈ face x 时 `atom (loop_of_face x) w = {w}`。
going 正向支：k ≥ 1 时 faceMap w = nodeMap.symm w，Simple 单点塌出
faceMap w = w，面轨道单点与 CARD face ≥ 3 矛盾；going 反向支：y ∉
face x 时 (loopOfFace x).map y = y（res 恒等支，雷区 #131），y ∈
face x 时同正向矛盾。 -/
private theorem epcFaceAtomSingleton (H : Hypermap α) (hr : H.IsRestricted)
    {x : α} (hx : x ∈ H.darts) (w : α) (hw : w ∈ H.face x) :
    H.atom (H.loopOfFace x) w = {w} := by
  have hnn := hr.nodeNondegenerate
  have hs := hr.simple
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hwD : w ∈ H.darts := H.face_subset_darts hx hw
  have mapEval : ∀ y : α, y ∈ H.face x → (H.loopOfFace x).map y = H.faceMap y := by
    intro y hy
    have h := H.loopOfFace_map_pow_apply hy 1
    rwa [pow_one, pow_one] at h
  have mapFix : ∀ y : α, y ∉ H.face x → (H.loopOfFace x).map y = y := by
    intro y hy
    show res H.faceMap (H.faceFinset x) y = y
    simp only [res]
    exact if_neg (by rw [H.mem_faceFinset]; exact hy)
  ext y
  constructor
  · rintro (hgoing | hgoing)
    · obtain ⟨k, hky, hag⟩ := hgoing
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [pow_zero] at hky
        exact hky
      · have hagree1 : (H.loopOfFace x).map w = H.nodeMap.symm w := hag 1 hk0
        rw [mapEval w hw] at hagree1
        have hmem2 : H.faceMap w ∈ H.node w ∩ H.face w :=
          ⟨by rw [hagree1]; exact H.nodeMap_symm_mem_node (H.mem_node_self w),
            H.pow_faceMap_mem_face w 1⟩
        rw [hs w hwD] at hmem2
        have hfixw : H.faceMap w = w := Set.mem_singleton_iff.mp hmem2
        have hcf1 : H.face x = {w} := by
          rw [H.face_eq_of_mem hw]
          exact (orbitMap_singleton_iff H.faceMap w).mpr hfixw
        rw [hcf1] at hcf3
        simp at hcf3
    · have hAtom : y ∈ H.atom (H.loopOfFace x) w := Or.inr hgoing
      obtain ⟨k, hkw, hag⟩ := hgoing
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [pow_zero] at hkw
        exact hkw.symm
      · have hagree1 : (H.loopOfFace x).map y = H.nodeMap.symm y := hag 1 hk0
        by_cases hyF : y ∈ H.face x
        · have hyD : y ∈ H.darts := H.face_subset_darts hx hyF
          rw [mapEval y hyF] at hagree1
          have hmem2 : H.faceMap y ∈ H.node y ∩ H.face y :=
            ⟨by rw [hagree1]; exact H.nodeMap_symm_mem_node (H.mem_node_self y),
              H.pow_faceMap_mem_face y 1⟩
          rw [hs y hyD] at hmem2
          have hfixy : H.faceMap y = y := Set.mem_singleton_iff.mp hmem2
          have hcf1 : H.face x = {y} := by
            rw [H.face_eq_of_mem hyF]
            exact (orbitMap_singleton_iff H.faceMap y).mpr hfixy
          rw [hcf1] at hcf3
          simp at hcf3
        · rw [mapFix y hyF] at hagree1
          have hyD : y ∈ H.darts := by
            have h1 : y ∈ H.node w :=
              H.atom_subset_node (L := H.loopOfFace x) (x := w) hAtom
            obtain ⟨t, hyt⟩ := (H.mem_node_iff w y).mp h1
            rw [hyt]
            exact H.nodeMap_permutes.pow_apply_mem t hwD
          have hsingle : H.node y = {y} := by
            rw [show H.node y = orbitMap H.nodeMap.symm y from
              (PermutesOn.orbitMap_symm H.nodeMap_permutes y).symm]
            exact (orbitMap_singleton_iff H.nodeMap.symm y).mpr hagree1.symm
          have h2le : 2 ≤ (H.node y).ncard := H.nodeNondegenerate_two_le.mp hnn y hyD
          rw [hsingle] at h2le
          simp at h2le
  · rintro hyy
    rw [Set.mem_singleton_iff.mp hyy]
    exact H.atom_reflect (H.loopOfFace x) w

/-- **合取 9**：atoms_of_loop L 与 loop_of_face x 的原子族不相交
（face-atom 单点 + 合取 5 互斥）。 -/
private theorem epcConj9 (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ)
    (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m) :
    H.atomsOfLoop L ∩ {y | ∃ x1, y = H.atom (H.loopOfFace x) x1 ∧
      x1 ∈ (H.loopOfFace x).darts} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  rw [Set.mem_inter_iff] at hA
  obtain ⟨hA1, hA2⟩ := hA
  rw [atomsOfLoopRep, Set.mem_setOf_eq] at hA1
  obtain ⟨u, hAu, huL⟩ := hA1
  rw [Set.mem_setOf_eq] at hA2
  obtain ⟨x1, hAx1, hx1d⟩ := hA2
  have hx1f : x1 ∈ H.face x := by
    rw [← H.loopOfFace_darts]
    exact Finset.mem_coe.mpr hx1d
  have hAu2 : H.atom L u = {x1} := by
    rw [← hAu, hAx1]
    exact epcFaceAtomSingleton H hr hx x1 hx1f
  have hu1 : u = x1 := by
    have h3 : u ∈ ({x1} : Set α) := by rw [← hAu2]; exact H.atom_reflect L u
    exact Set.mem_singleton_iff.mp h3
  obtain ⟨m, hm, hym⟩ := epcMemSupport H n hLd huL
  refine epcDisjoint H hr hx n hn m hm ?_
  rw [hym, hu1]
  exact hx1f

/-- **合取 10**：每环点 x1 有 y（段首点）：y ∈ atom L x1、
y = faceMap (L.invMap y)、nodeMap y ∈ face x、nodeMap² y ∈ atom L x1。
（HOL :1421-:1813「EXISTS Y FROM L」全线。） -/
private theorem epcConj10 (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ)
    (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hLm : (L.map : α → α) = Loop.samsara (H.complementPt x) n)
    (hinj : Loop.IsInjList (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m) :
    ∀ x1 : α, x1 ∈ L.darts → ∃ y, y ∈ H.atom L x1 ∧ y = H.faceMap (L.invMap y) ∧
      H.nodeMap y ∈ H.face x ∧ H.nodeMap (H.nodeMap y) ∈ H.atom L x1 := by
  have hnn := hr.nodeNondegenerate
  have hplain := hr.plain
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hn2x : 2 ≤ (H.node x).ncard := H.nodeNondegenerate_two_le.mp hnn x hx
  have h1cf : 1 ≤ H.complementIndex x (H.face x).ncard :=
    complementIndexFaceLe1 H hnn hx
  have hcfN : n + 1 = H.complementIndex x (H.face x).ncard := by omega
  have hmem : ∀ m, H.complementPt x m ∈ L.darts := fun m => epcMemPath H n hLd hmod m
  have hcf1 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
  have hp0 : H.complementPt x 0 = H.nodeMap x := rfl
  have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
      = (H.node x).ncard := by
    refine congrArg (fun v => (H.node v).ncard) ?_
    exact inverseFaceCycle H x
  have hci1 : H.complementIndex x (H.face x).ncard
      = H.complementIndex x ((H.face x).ncard - 1) + ((H.node x).ncard - 1) := by
    have h2 := H.complementIndex_succ_eq_sub hnn hx ((H.face x).ncard - 1)
    rw [hcf1] at h2
    rwa [hNcf] at h2
  -- 段首 y 的 L.invMap 求值（ci j' + 1 ≤ n 时回退到 pivot）
  have hinvSeg : ∀ j' : ℕ, H.complementIndex x j' + 1 ≤ n →
      (L.invMap : α → α) (H.complementPt x (H.complementIndex x j' + 1))
        = H.nodeMap ((H.faceMap.symm ^ j') x) := by
    intro j' hj
    have h1 := epcInvMapStep H hinj hLm hmod (H.complementIndex x j' + 1)
    rw [show H.complementIndex x j' + 1 + n
        = H.complementIndex x j' + (n + 1) from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at h1
    rw [h1, H.complementPt_compIndex_eval hnn hx j']
  -- faceMap ∘ nodeMap 拼装收口：faceMap (nodeMap z_{j'}) = nodeMap.symm z_{j'+1}
  have hfinSeg : ∀ (j' : ℕ) (y : α),
      y = H.nodeMap.symm ((H.faceMap.symm ^ (j' + 1)) x) →
      H.faceMap (H.nodeMap ((H.faceMap.symm ^ j') x)) = y := by
    intro j' y hy
    rw [hy, epcFaceMapNodeMap H hplain, pow_succ'_apply]
  intro x1 hx1
  obtain ⟨m, hm, hym⟩ := epcMemSupport H n hLd hx1
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · -- x1 = p 0：y := 尾段首点 p (ci (cf-1) + 1) = nodeMap.symm x
    have hm₀ : H.complementIndex x ((H.face x).ncard - 1) + 1 ≤ n ∨
        H.complementIndex x ((H.face x).ncard - 1) = n := by
      rcases Nat.lt_or_ge (H.node x).ncard 3 with h | h
      · right; omega
      · left; omega
    rw [← hym]
    refine ⟨H.complementPt x (H.complementIndex x ((H.face x).ncard - 1) + 1),
      ?_, ?_, ?_, ?_⟩
    · -- ① y ∈ atom L p 0
      rcases hm₀ with h3 | hcN
      · -- N_x ≥ 3：going 收口链 p (ci (cf-1)+1) → p 0
        have hstep : ∀ t, H.complementIndex x ((H.face x).ncard - 1) + 1 ≤ t →
            t ≤ n → H.nodeMap.symm (H.complementPt x t)
              = H.complementPt x ((t + 1) % (n + 1)) := by
          intro t ht1 ht2
          rcases Nat.lt_or_ge t n with hlt | hle
          · rw [epcStepSeg H hnn hx ((H.face x).ncard - 1) t ht1
              (by rw [hcf1, ← hcfN]; omega), Nat.mod_eq_of_lt (by omega)]
          · rw [show t = n from by omega, epcStepWrapN3 H hnn hx n hn hcf3
              (by omega), Nat.mod_self]
        have hmem0 : H.complementPt x 0 ∈ H.atom L
            (H.complementPt x (H.complementIndex x ((H.face x).ncard - 1) + 1)) :=
          Or.inl (epcGoingWrap H hinj hLm _ h3 hstep)
        rw [← H.atom_eq_of_mem hmem0]
        exact H.atom_reflect _ _
      · -- N_x = 2：y = nodeMap x = p 0，同点 reflect
        have hN2 : (H.node x).ncard = 2 := by omega
        have hevy : H.complementPt x (H.complementIndex x ((H.face x).ncard - 1) + 1)
            = H.complementPt x 0 := by
          rw [H.complementPt_compIndex_succ_eval hnn hx _, hcf1, inverseFaceCycle,
            epcNodeSymmEqOfTwo H x hN2, hp0]
        rw [hevy]
        exact H.atom_reflect _ _
    · -- ② y = faceMap (L.invMap y)
      rcases hm₀ with h3 | hcN
      · rw [hinvSeg _ h3, hfinSeg _ _ (H.complementPt_compIndex_succ_eval hnn hx _)]
      · -- N_x = 2：L.invMap y = p n = nodeMap z_{cf-1}
        have hN2 : (H.node x).ncard = 2 := by omega
        have hciN : H.complementIndex x ((H.face x).ncard - 1) = n := by omega
        have h1 := epcInvMapStep H hinj hLm hmod 0
        rw [show (0 + n) % (n + 1) = n from by
          rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)] at h1
        rw [hp0] at h1
        -- h1 : (L.invMap) (nodeMap x) = complementPt x n（勿再于 h1 侧换 symm 面）
        rw [H.complementPt_compIndex_succ_eval hnn hx _, hcf1, inverseFaceCycle,
          epcNodeSymmEqOfTwo H x hN2, h1,
          show n = H.complementIndex x ((H.face x).ncard - 1) from hciN.symm,
          H.complementPt_compIndex_eval hnn hx _, epcFaceMapNodeMap H hplain,
          ← pow_succ'_apply H.faceMap.symm _, hcf1, inverseFaceCycle,
          (epcNodeSymmEqOfTwo H x hN2).symm]
    · -- ③ nodeMap y = x ∈ face x
      rw [H.complementPt_compIndex_succ_eval hnn hx _, hcf1, inverseFaceCycle,
        Equiv.apply_symm_apply]
      exact mem_orbitMap_self H.faceMap x
    · -- ④ nodeMap² y = p 0 = x1 ∈ atom L x1
      rw [H.complementPt_compIndex_succ_eval hnn hx _, hcf1, inverseFaceCycle,
        Equiv.apply_symm_apply, hp0]
      exact H.atom_reflect _ _
  · -- x1 = p m（m ≥ 1）：y := 段首 p (ci i + 1)
    obtain hzero | ⟨i, j₀, hj1₀, hj2₀, hrep⟩ := strictInc_partition₂
      (f := H.complementIndex x) (H.complementIndex_zero_eq x)
      (H.complementIndex_lt_succ hnn hx) m
    · exact absurd hzero (by omega)
    have hjN₀ : j₀ < (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard := by
      have hs2 := H.complementIndex_succ_eq_sub hnn hx i
      omega
    have hm₀ : H.complementIndex x i + 1 ≤ m := by omega
    have hilt : i < (H.face x).ncard := by
      by_contra hge
      have hge' : (H.face x).ncard ≤ i := by omega
      have hle := H.complementIndex_le_of_le hnn hx hge'
      omega
    rw [← hym]
    have hgoing := epcGoingChain H hinj hLm
      (H.complementIndex x i + 1) (m - (H.complementIndex x i + 1)) m
      (by omega) hm
      (fun t ht1 ht2 => epcStepSeg H hnn hx i t ht1 (by omega))
    have hmemm : H.complementPt x m ∈ H.atom L
        (H.complementPt x (H.complementIndex x i + 1)) := Or.inl hgoing
    refine ⟨H.complementPt x (H.complementIndex x i + 1), ?_, ?_, ?_, ?_⟩
    · -- ① y ∈ atom L p m
      rw [← H.atom_eq_of_mem hmemm]
      exact H.atom_reflect _ _
    · -- ② y = faceMap (L.invMap y)
      have hci : H.complementIndex x i + 1 ≤ n := by omega
      rw [hinvSeg i hci, hfinSeg i _ (H.complementPt_compIndex_succ_eval hnn hx i)]
    · -- ③ nodeMap y = z_{i+1} ∈ face x
      rw [H.complementPt_compIndex_succ_eval hnn hx i, Equiv.apply_symm_apply]
      exact H.faceMap_symm_pow_mem_face_self x (i + 1)
    · -- ④ nodeMap² y = nodeMap z_{i+1} = p (ci (i+1)) ∈ atom L x1
      have hnodez : H.nodeMap ((H.faceMap.symm ^ (i + 1)) x)
          = H.complementPt x (H.complementIndex x (i + 1)) :=
        (H.complementPt_compIndex_eval hnn hx (i + 1)).symm
      rw [H.complementPt_compIndex_succ_eval hnn hx i, Equiv.apply_symm_apply, hnodez,
        ← H.atom_eq_of_mem hmemm]
      rcases Nat.lt_or_ge (H.complementIndex x (i + 1)) (n + 1) with hlt | heq
      · -- ci (i+1) ≤ n：段内链
        exact Or.inl (epcGoingChain H hinj hLm (H.complementIndex x i + 1)
          (H.complementIndex x (i + 1) - (H.complementIndex x i + 1))
          (H.complementIndex x (i + 1)) (by omega) (by omega)
          (fun t ht1 ht2 => epcStepSeg H hnn hx i t ht1 (by omega)))
      · -- ci (i+1) = n+1：nodeMap z_{i+1} = p (n+1) = p 0，收口链到 p 0
        have hicf : H.complementIndex x (i + 1) = n + 1 := by
          have hle1 : H.complementIndex x (i + 1)
              ≤ H.complementIndex x (H.face x).ncard :=
            H.complementIndex_le_of_le hnn hx (by omega)
          omega
        have hi1cf : i + 1 = (H.face x).ncard := by
          have hle1 : H.complementIndex x (i + 1)
              ≤ H.complementIndex x (H.face x).ncard :=
            H.complementIndex_le_of_le hnn hx (by omega)
          by_contra hne
          have hlt : i + 1 < (H.face x).ncard := by omega
          have hlt2 : H.complementIndex x (i + 1)
              < H.complementIndex x (H.face x).ncard :=
            H.complementIndex_lt_of_lt hnn hx hlt
          omega
        have hN3 : 3 ≤ (H.node x).ncard := by
          have hs2 := H.complementIndex_succ_eq_sub hnn hx i
          have hNcf' : (H.node ((H.faceMap.symm ^ (i + 1)) x)).ncard
              = (H.node x).ncard := by
            rw [hi1cf]
            exact hNcf
          omega
        have hstep : ∀ t, H.complementIndex x i + 1 ≤ t → t ≤ n →
            H.nodeMap.symm (H.complementPt x t)
              = H.complementPt x ((t + 1) % (n + 1)) := by
          intro t ht1 ht2
          rcases Nat.lt_or_ge t n with hlt | hle
          · rw [epcStepSeg H hnn hx i t ht1 (by rw [hicf]; omega),
              Nat.mod_eq_of_lt (by omega)]
          · rw [show t = n from by omega, epcStepWrapN3 H hnn hx n hn hcf3
              (by omega), Nat.mod_self]
        have hgoing := epcGoingWrap H hinj hLm (H.complementIndex x i + 1)
          (by omega) hstep
        rw [hicf, show H.complementPt x (n + 1) = H.complementPt x 0 from by
          have h := hmod (n + 1)
          rw [Nat.mod_self] at h
          exact h.symm]
        exact Or.inl hgoing

/-- **合取 11**：每面点 x1 有 y := nodeMap.symm x1：y ∈ atom L y、
y = faceMap (L.invMap y)、x1 = nodeMap y、y ∈ L。 -/
private theorem epcConj11 (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ)
    (hn : H.complementIndex x (H.face x).ncard - 1 = n)
    {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hLm : (L.map : α → α) = Loop.samsara (H.complementPt x) n)
    (hinj : Loop.IsInjList (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m) :
    ∀ x1 : α, x1 ∈ H.face x → ∃ y, y ∈ H.atom L (H.nodeMap.symm x1) ∧
      y = H.faceMap (L.invMap y) ∧ x1 = H.nodeMap y ∧
      H.nodeMap.symm x1 ∈ L.darts := by
  have hnn := hr.nodeNondegenerate
  have hplain := hr.plain
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hn2x : 2 ≤ (H.node x).ncard := H.nodeNondegenerate_two_le.mp hnn x hx
  have h1cf : 1 ≤ H.complementIndex x (H.face x).ncard :=
    complementIndexFaceLe1 H hnn hx
  have hcfN : n + 1 = H.complementIndex x (H.face x).ncard := by omega
  have hmem : ∀ m, H.complementPt x m ∈ L.darts := fun m => epcMemPath H n hLd hmod m
  have hcf1 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
  have hp0 : H.complementPt x 0 = H.nodeMap x := rfl
  have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
      = (H.node x).ncard := by
    refine congrArg (fun v => (H.node v).ncard) ?_
    exact inverseFaceCycle H x
  have hci1 : H.complementIndex x (H.face x).ncard
      = H.complementIndex x ((H.face x).ncard - 1) + ((H.node x).ncard - 1) := by
    have h2 := H.complementIndex_succ_eq_sub hnn hx ((H.face x).ncard - 1)
    rw [hcf1] at h2
    rwa [hNcf] at h2
  have hinvSeg : ∀ j' : ℕ, H.complementIndex x j' + 1 ≤ n →
      (L.invMap : α → α) (H.complementPt x (H.complementIndex x j' + 1))
        = H.nodeMap ((H.faceMap.symm ^ j') x) := by
    intro j' hj
    have h1 := epcInvMapStep H hinj hLm hmod (H.complementIndex x j' + 1)
    rw [show H.complementIndex x j' + 1 + n
        = H.complementIndex x j' + (n + 1) from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at h1
    rw [h1, H.complementPt_compIndex_eval hnn hx j']
  have hfinSeg : ∀ (j' : ℕ) (y : α),
      y = H.nodeMap.symm ((H.faceMap.symm ^ (j' + 1)) x) →
      H.faceMap (H.nodeMap ((H.faceMap.symm ^ j') x)) = y := by
    intro j' y hy
    rw [hy, epcFaceMapNodeMap H hplain, pow_succ'_apply]
  intro x1 hx1
  obtain ⟨i, hi, hx1z⟩ := lemmaViaInverseFaceMap H hx1
  refine ⟨H.nodeMap.symm x1, H.atom_reflect _ _, ?_,
    (Equiv.apply_symm_apply H.nodeMap x1).symm, ?_⟩
  · -- ② y = faceMap (L.invMap y)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · -- x1 = x：y = nodeMap.symm x，j' = cf - 1
      have hy : H.nodeMap.symm x1 = H.nodeMap.symm x := by
        rw [hx1z, pow_zero, Equiv.Perm.one_apply]
      rw [hy]
      rcases Nat.lt_or_ge (H.node x).ncard 3 with hN2' | hN3
      · -- N_x = 2：y = p 0；L.invMap y = p n = nodeMap z_{cf-1}
        have hN2 : (H.node x).ncard = 2 := by omega
        have hciN : H.complementIndex x ((H.face x).ncard - 1) = n := by omega
        have h1 := epcInvMapStep H hinj hLm hmod 0
        rw [show (0 + n) % (n + 1) = n from by
          rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)] at h1
        rw [hp0] at h1
        -- h1 : (L.invMap) (nodeMap x) = complementPt x n（勿再于 h1 侧换 symm 面）
        rw [epcNodeSymmEqOfTwo H x hN2, h1,
          show n = H.complementIndex x ((H.face x).ncard - 1) from hciN.symm,
          H.complementPt_compIndex_eval hnn hx _, epcFaceMapNodeMap H hplain,
          ← pow_succ'_apply H.faceMap.symm _, hcf1, inverseFaceCycle,
          (epcNodeSymmEqOfTwo H x hN2).symm]
      · -- N_x ≥ 3：y = p (ci (cf-1)+1)，hinvSeg 直接
        have hm₀ : H.complementIndex x ((H.face x).ncard - 1) + 1 ≤ n := by omega
        have hevy : H.nodeMap.symm x = H.complementPt x
            (H.complementIndex x ((H.face x).ncard - 1) + 1) := by
          rw [H.complementPt_compIndex_succ_eval hnn hx _, hcf1, inverseFaceCycle]
        rw [hevy, hinvSeg _ hm₀,
          hfinSeg _ _ (H.complementPt_compIndex_succ_eval hnn hx _)]
    · -- x1 = z_i（1 ≤ i < cf）：y = p (ci (i-1) + 1) = symm z_i
      have hm₀ : H.complementIndex x (i - 1) + 1 ≤ n := by
        have hA : H.complementIndex x (i - 1) < H.complementIndex x i :=
          H.complementIndex_lt_of_lt hnn hx (by omega)
        have hB : H.complementIndex x i < H.complementIndex x (H.face x).ncard :=
          H.complementIndex_lt_of_lt hnn hx (by omega)
        omega
      have hcf1i : i - 1 + 1 = i := by omega
      have hevy : H.nodeMap.symm x1 = H.complementPt x
          (H.complementIndex x (i - 1) + 1) := by
        rw [hx1z, show i = i - 1 + 1 from by omega]
        exact (H.complementPt_compIndex_succ_eval hnn hx _).symm
      rw [hevy, hinvSeg _ hm₀,
        hfinSeg _ _ (H.complementPt_compIndex_succ_eval hnn hx _)]
  · -- ④ y ∈ L
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hy : H.nodeMap.symm x1 = H.nodeMap.symm x := by
        rw [hx1z, pow_zero, Equiv.Perm.one_apply]
      rw [hy]
      rcases Nat.lt_or_ge (H.node x).ncard 3 with hN2' | hN3
      · have hN2 : (H.node x).ncard = 2 := by omega
        rw [epcNodeSymmEqOfTwo H x hN2, ← hp0]
        exact hmem 0
      · have hm₀ : H.complementIndex x ((H.face x).ncard - 1) + 1 ≤ n := by omega
        have hevy : H.nodeMap.symm x = H.complementPt x
            (H.complementIndex x ((H.face x).ncard - 1) + 1) := by
          rw [H.complementPt_compIndex_succ_eval hnn hx _, hcf1, inverseFaceCycle]
        rw [hevy]
        exact hmem _
    · have hm₀ : H.complementIndex x (i - 1) + 1 ≤ n := by
        have hA : H.complementIndex x (i - 1) < H.complementIndex x i :=
          H.complementIndex_lt_of_lt hnn hx (by omega)
        have hB : H.complementIndex x i < H.complementIndex x (H.face x).ncard :=
          H.complementIndex_lt_of_lt hnn hx (by omega)
        omega
      have hcf1i : i - 1 + 1 = i := by omega
      have hevy : H.nodeMap.symm x1 = H.complementPt x
          (H.complementIndex x (i - 1) + 1) := by
        rw [hx1z, show i = i - 1 + 1 from by omega]
        exact (H.complementPt_compIndex_succ_eval hnn hx _).symm
      rw [hevy]
      exact hmem _

/-- **合取 12**：每面点的 nodeMap 像在 L 内（pivotEval + 均匀成员件
一发；HOL :1846-:1850）。 -/
private theorem epcConj12 (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) (n : ℕ) {L : Loop α}
    (hLd : (L.darts : Set α) = Loop.pathSupport (H.complementPt x) n)
    (hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m) :
    ∀ x1 : α, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts := by
  have hnn := hr.nodeNondegenerate
  have hmem : ∀ m, H.complementPt x m ∈ L.darts := fun m => epcMemPath H n hLd hmod m
  intro x1 hx1
  obtain ⟨i, hi, hx1z⟩ := lemmaViaInverseFaceMap H hx1
  have h1 : H.nodeMap x1 = H.complementPt x (H.complementIndex x i) := by
    rw [hx1z, ← H.complementPt_compIndex_eval hnn hx i]
  rw [h1]
  exact hmem _

/-! ### §5 总装：EXISTS_PATH_COMPLEMENT（AUQTZYZ.hl :574-:586 语句） -/

/-- **HOL `EXISTS_PATH_COMPLEMENT`**（AUQTZYZ.hl:574-:586 语句，
证明体 :587-:1850）：受限 hypermap 中每个 dart 的补路径自成一个环，
十二合取——① is_loop；② path_of_loop L (complement x 0) =
complement x（函数等式）；③ complement x 0 在环内；④ node 分裂
（环含两个异 node 点）；⑤ 环与 face x 不交；⑥⑦ 两条
in_dart-or-in_face 闭包；⑧ CARD (atoms_of_loop L) = CARD (face x)；
⑨ atoms_of_loop L 与 loop_of_face x 的原子族不交；⑩⑪ 两条
atom↔face 双射桥；⑫ 面点的 nodeMap 像在环内。 -/
theorem EXISTS_PATH_COMPLEMENT (H : Hypermap α) (hr : H.IsRestricted) {x : α}
    (hx : x ∈ H.darts) :
    ∃ L : Loop α, Loop.IsLoopOf H L ∧ L.pathOf (H.complementPt x 0) = H.complementPt x ∧
      H.complementPt x 0 ∈ L.darts ∧
      (∃ y z, y ∈ L.darts ∧ z ∈ L.darts ∧ H.node y ≠ H.node z) ∧
      (L.darts : Set α) ∩ H.face x = ∅ ∧
      (∀ y, y ∈ L.darts → ∀ z, z ∈ H.node y → z ∈ L.darts ∨ z ∈ H.face x) ∧
      (∀ y, y ∈ H.face x → ∀ z, z ∈ H.node y → z ∈ L.darts ∨ z ∈ H.face x) ∧
      (H.atomsOfLoop L).ncard = (H.face x).ncard ∧
      H.atomsOfLoop L ∩ {y | ∃ x1, y = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅ ∧
      (∀ x1, x1 ∈ L.darts → ∃ y, y ∈ H.atom L x1 ∧ y = H.faceMap (L.invMap y) ∧
        H.nodeMap y ∈ H.face x ∧ H.nodeMap (H.nodeMap y) ∈ H.atom L x1) ∧
      (∀ x1, x1 ∈ H.face x → ∃ y, y ∈ H.atom L (H.nodeMap.symm x1) ∧
        y = H.faceMap (L.invMap y) ∧ x1 = H.nodeMap y ∧
        H.nodeMap.symm x1 ∈ L.darts) ∧
      (∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts) := by
  have hnn := hr.nodeNondegenerate
  have hplain := hr.plain
  have hcf3 : 3 ≤ (H.face x).ncard := hr.three_le_ncard_face hx
  have hn2x : 2 ≤ (H.node x).ncard := H.nodeNondegenerate_two_le.mp hnn x hx
  have h1cf : 1 ≤ H.complementIndex x (H.face x).ncard :=
    complementIndexFaceLe1 H hnn hx
  have hcf1 : (H.face x).ncard - 1 + 1 = (H.face x).ncard := by omega
  have hNcf : (H.node ((H.faceMap.symm ^ (H.face x).ncard) x)).ncard
      = (H.node x).ncard := by
    refine congrArg (fun v => (H.node v).ncard) ?_
    exact inverseFaceCycle H x
  have hci1 : H.complementIndex x (H.face x).ncard
      = H.complementIndex x ((H.face x).ncard - 1) + ((H.node x).ncard - 1) := by
    have h2 := H.complementIndex_succ_eq_sub hnn hx ((H.face x).ncard - 1)
    rw [hcf1] at h2
    rwa [hNcf] at h2
  obtain ⟨n, hn⟩ : ∃ n, n = H.complementIndex x (H.face x).ncard - 1 :=
    ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by
    have h0 : H.complementIndex x 0 = 0 := H.complementIndex_zero_eq x
    have h01 : H.complementIndex x 0 < H.complementIndex x 1 :=
      H.complementIndex_lt_succ hnn hx 0
    have h12 : H.complementIndex x 1 < H.complementIndex x 2 :=
      H.complementIndex_lt_succ hnn hx 1
    have h2le : H.complementIndex x 2
        ≤ H.complementIndex x ((H.face x).ncard - 1) :=
      H.complementIndex_le_of_le hnn hx (by omega)
    omega
  have hcont : H.isContour (H.complementPt x) (n + 1) :=
    H.isContour_complementPt hplain hnn hx _
  have hic := H.isInjContour_complementPt hplain hr.simple hnn hx
  rw [show Nat.pred (H.complementIndex x (H.face x).ncard) = n from hn.symm,
    show (fun t => H.complementPt x t) = H.complementPt x from rfl] at hic
  have hinj : Loop.IsInjList (H.complementPt x) n := isInjContourIsInjList H hic
  have hmod : ∀ m, H.complementPt x (m % (n + 1)) = H.complementPt x m :=
    complementMod H hr hx n hn.symm
  obtain ⟨L, hL1, hL2, hL3, hL4, hLd, hLm⟩ :=
    EXTRA_COMP_LOOP H (H.complementPt x) n 0 1 (epcNodeSplit H hr hx)
      (Nat.zero_le _) hn1 hcont hinj hmod
  refine ⟨L, hL1, hL2, hL3, hL4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 合取 5
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyL, hyF⟩
    obtain ⟨m, hm, hym⟩ := epcMemSupport H n hLd hyL
    refine epcDisjoint H hr hx n hn.symm m hm ?_
    rw [hym]
    exact hyF
  · exact fun y hy z hz => epcClosureIn H hr hx n hLd hmod y hy z hz
  · exact fun y hy z hz => epcClosureFace H hr hx n hLd hmod y hy z hz
  · exact epcCard H hr hx n hn.symm hLd hLm hinj hmod
  · exact epcConj9 H hr hx n hn.symm hLd hmod
  · exact epcConj10 H hr hx n hn.symm hLd hLm hinj hmod
  · exact epcConj11 H hr hx n hn.symm hLd hLm hinj hmod
  · exact epcConj12 H hr hx n hLd hmod

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针已执行，快照 t63_axiom_audit.log 全文）：
本件公开件 1（EXISTS_PATH_COMPLEMENT）+ private 段件 8（epcFInj /
epcAtomInj / epcCard / epcFaceAtomSingleton / epcConj9-12，含不消费
的记档件 epcFInj）已于本批在文件语境逐一 #print axioms 探针——9 发
全部 [propext, Classical.choice, Quot.sound] 标准三内，零 sorryAx。
注意 §0' 本地私桥副本全部经 epcCard/epcConj9-12/总装传递喂入主件
（epcMapStep 经 epcInvMapStep、epcNodePos 经 epcClosureIn），主件
公理面即全链公理面；§0' 副本与 TameList62 §0-§2 件互不引用。
#print axioms Kepler.Text.TameSpine.EXISTS_PATH_COMPLEMENT
-/
