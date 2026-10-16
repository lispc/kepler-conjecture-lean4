/-
  Kepler.Text.TameSpine.TameList20 — B1 Tame_list 地基批 20：e_list_pairs_rev
  + rotate 位移算术（tamespine-port-plan §4 批次表 B1 行；接续批 19 =
  TameList18→TameList19.lean，批 19 终点 = HOL :10554（e_list_image 已落，
  :10556 起留本批）；本批起点 = HOL :10556）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10556-:10592）——主件 1 枚 +
  §0 位移算术私件 5 枚，共 6 枚全量：

  主件：`e_list_pairs_rev` :10556-:10592
  `!f r. uniq f /\ ~(f = []) /\ sizel f = sizel r /\
    (!d. MEM d (list_pairs f) ==> MEM (e_list d) (list_pairs r)) /\
    HD f = LAST r ==> r = rev f`
  （证明体 :10561-:10591；:10584 COND_CASES 后半 = rotate 位移算术）。
  :10595 `fgraph_seed` 起自然边界收批（留批 21）。

  层级侦察定论（全量形记档，本批新核）：
  · `Seq.rot`（jHOLLight seq-compiled.hl:1113 定义）`rot n s = dropl n s ++
    take n s`——HOL rot 无 mod 语义，oversize 时恒等；Lean `List.rotate`
    为 mod 语义。`Seq.rot_oversize`（seq-compiled.hl:1124）
    `sizel s <= n ==> rot n s = s` 在 Lean 侧折算为位移归约
    k ↦ k % length（`List.rotate_mod`），两支合一。
  · `Seq2.index_rot`（ssreflect seq2-compiled.hl:1647 全量形）
    `uniq s /\ n < sizel s /\ MEM x s ==> indexl x (rot n s) =
    if n <= indexl x s then (indexl x s - n) else (indexl x s + sizel s - n)`
    ——:10584 COND_CASES 的来源；x = HD f 支（indexl (HD f) f = 0，
    index_hd0 tame_list.hl:4950）真支给 k = 0（Seq.rot0），假支
    `indexl (HD f) (rot k f) = sizel f - k > 0` 与 HD (rot k f) = HD f
    （LAST_rev :5938 换形 + index_hd0）算术矛盾（NAT 减法）。
  · `Seq.revK`（seq-compiled.hl:1375）`rev (rev s) = s` ↦
    `List.reverse_reverse`；`Seq.size_rev/size_rot/size_eq0` 全部由
    List.length_* simp 面吸收，零新增侦察件。
  · Lean 侧同构替代：位移算术内核取 `head?_rotate` + `head!_of_head?`
    + nodup-idxOf 单射（TameLp idxOf_getElem，批 19 在案）——
    (rotate k l).head! = l[k] 与 l.head! = l[0] 经 Nodup 逼 k = 0，
    与 index_rot/index_hd0 的 indexl 算术语义同构（层级 List ℕ 面，
    批 19 已定论）。

  依赖面（全为在案真件，零新增债）：批 19 `eListImage`（:10534）+
  TameLp `idxOf_getElem` + Mathlib List.rotate 群
  （rotate_mod/rotate_zero/rotate_eq_nil_iff/length_rotate/head?_rotate）+
  core head!_of_head?/getLast!_of_getLast?/getLast?_reverse。

  载体折算（沿批 1-19 约定）：`rot k` ↦ `List.rotate k`；`rev` ↦
  `List.reverse`；`HD` ↦ `head!`；`LAST` ↦ `getLast!`；`indexl` ↦
  `idxOf`；`uniq` ↦ `List.Nodup`；`sizel` ↦ `List.length`。

  诚实记账：本批六件全部真证，零新增记账债（零止损件）。
  e_list_pairs_rev 的 HOL 前提 `~(f = [])` 在 eListImage 路线中不被
  消费，按批 18 `_hgn` 惯例以 `_hne` 显式保留（实际参与位移归约的
  0 < length 与 rotate 非空支，非摆设）。位移归约 obtain 的 k' =
  k % f.length 为显式 witness（∃-提取两面包夹惯例），非 set（雷区：
  set 变量禁 rw）。§0 两处 `some (l[i]'h)` 按括号隔离写法（Kepler
  导入链下 getElem-证明参后缀在 `some` 实参位会被自定义记号遮蔽，
  括号隔离后核心语法直收）。公理审计实测（#print axioms，2026-10-16，
  隔离 clone /tmp/tl20-clone）：六件均仅依赖标准三
  [propext, Classical.choice, Quot.sound]（headQueryEqD 零公理，
  headGetZeroD/getLastReverseD 仅 propext 面），零 sorryAx、零记账传入。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 21 接续点：HOL :10595 `fgraph_seed`（`!p. fgraph (Seed p) =
  [iota 0 (maxGon p); rev (iota 0 (maxGon p))]`，fgraph/SEED/faces/graphl
  展开面 + lower_case/upt0；后随 `uniq_list_of_darts_seed` :10604、
  `all_nonempty_seed` :10638——Seed 章三连，iota/range' 面批 2/19
  el_iota/hdIota/iota_uniq 在案可资）。
-/

import Kepler.Text.TameSpine.TameList19

namespace Kepler.Text.TameSpine

open Kepler.Assembly (eList listPairs)
open Kepler.Text.TameLp (idxOf_getElem)

/-! ### §0 rotate 位移算术私件（:10584 COND_CASES 后半的 getElem 同构替代） -/

/-- 非空表的 `head?`-`head!` 对接桥。 -/
private theorem headQueryEqD {t : List ℕ} (h : t ≠ []) :
    t.head? = some t.head! := by
  rcases t with _ | ⟨a, s⟩
  · exact absurd rfl h
  · rfl

/-- 首元的 getElem 式：非空表 `head!` = 第 0 项（HOL `index_hd0`
（tame_list.hl:4950 `~(s = []) ==> indexl (HD s) s = 0`）的 getElem 面）。 -/
private theorem headGetZeroD {l : List ℕ} (h0 : 0 < l.length) :
    l.head! = l[0]'h0 := by
  have hq : l.head? = some (l[0]'h0) := by
    rcases l with _ | ⟨a, t⟩
    · exact absurd h0 (by simp)
    · rfl
  exact List.head!_of_head? hq

/-- rotate 后首元的 getElem 式（HOL `Seq2.index_rot`
（seq2-compiled.hl:1647）的 getElem 同构替代；`head?_rotate` 桥）。 -/
private theorem rotateHeadGetD {l : List ℕ} {k : ℕ} (hk : k < l.length) :
    (l.rotate k).head! = l[k]'hk := by
  have hq : (l.rotate k).head? = l[k]? := List.head?_rotate hk
  rw [List.getElem?_eq_getElem hk] at hq
  exact List.head!_of_head? hq

/-- **HOL `LAST_rev`**（tame_list.hl:5938-:5939
`!t. ~(t = []) ==> LAST (rev t) = HD t`）的 List ℕ 面。 -/
private theorem getLastReverseD {t : List ℕ} (h : t ≠ []) :
    t.reverse.getLast! = t.head! := by
  have hq : t.reverse.getLast? = some t.head! := by
    rw [List.getLast?_reverse]
    exact headQueryEqD h
  exact List.getLast!_of_getLast? hq

/-- rotate 位移算术（HOL `e_list_pairs_rev` 证明体 :10579-:10585：
`Seq2.index_rot` 假支 + `index_hd0` + NAT 减法的算术矛盾，加
`Seq.rot_oversize`（seq-compiled.hl:1124）oversize 支的 mod 归约前身）：
nodup 非空表被 `0 < k < sizel` 位移的 rotate 保持首元则假。 -/
private theorem rotateShiftHeadContradiction {l : List ℕ} (hnd : l.Nodup)
    (_hne : l ≠ []) {k : ℕ} (hk : k < l.length) (hk0 : 0 < k)
    (h : (l.rotate k).head! = l.head!) : False := by
  have hshift := rotateHeadGetD hk
  have hzero := headGetZeroD (hk0.trans hk)
  have hidx : l.idxOf l.head! = k := by
    rw [← h, hshift]
    exact idxOf_getElem hnd hk
  have hidx0 : l.idxOf l.head! = 0 := by
    rw [hzero]
    exact idxOf_getElem hnd (hk0.trans hk)
  omega

/-! ### §1 e_list_pairs_rev（tame_list.hl:10556-:10592） -/

/-- **HOL `e_list_pairs_rev`**（tame_list.hl:10556-:10560）
`!f r. uniq f /\ ~(f = []) /\ sizel f = sizel r /\
  (!d. MEM d (list_pairs f) ==> MEM (e_list d) (list_pairs r)) /\
  HD f = LAST r ==> r = rev f`
——HOL 同构：e_list_image（批 19 `eListImage`）给 `?k. rot k f = rev r`，
revK（`List.reverse_reverse`）翻出 `r = (rot k f).reverse`；
ENOUGH_TO_SHOW `rot k f = f` 后由 HD f = LAST r 经 LAST_rev
（`getLastReverseD`）换形为 HD f = HD (rot k f)。oversize 支
（Seq.rot_oversize）在 Lean `List.rotate` mod 语义下折算为位移归约
k ↦ k % length（`List.rotate_mod`，显式 witness obtain）；余下
COND_CASES 后半的位移算术由 `rotateShiftHeadContradiction`
（nodup-idxOf 单射逼 k = 0）收口，k = 0 支 `List.rotate_zero` 直收。 -/
theorem eListPairsRev {f r : List ℕ} (hu : f.Nodup) (hne : f ≠ [])
    (hlen : f.length = r.length)
    (h : ∀ d ∈ listPairs f, eList d ∈ listPairs r)
    (hhd : f.head! = r.getLast!) : r = f.reverse := by
  obtain ⟨k, hk⟩ := eListImage hu hne hlen h
  have hf0 : 0 < f.length := List.length_pos_of_mem (List.head!_mem_self hne)
  -- 位移归约（Seq.rot_oversize 支的 mod 规范化）
  obtain ⟨k', hk'l, hk'⟩ :
      ∃ k', k' < f.length ∧ f.rotate k' = r.reverse :=
    ⟨k % f.length, Nat.mod_lt k hf0, by rw [List.rotate_mod]; exact hk⟩
  -- LAST_rev 面：HD f = LAST r 换形为 HD f = HD (rot k' f)
  have hrf : f.rotate k' ≠ [] :=
    List.rotate_eq_nil_iff.not.mpr hne
  have h1 : f.head! = (f.rotate k').head! := by
    have e1 : (f.rotate k').reverse.getLast! = r.getLast! := by
      rw [hk', List.reverse_reverse]
    rw [← getLastReverseD hrf, e1]
    exact hhd
  rcases Nat.eq_zero_or_pos k' with h0 | hk'0
  · subst h0
    have hr2 := congrArg List.reverse hk'
    rw [List.reverse_reverse, List.rotate_zero] at hr2
    exact hr2.symm
  · exact (rotateShiftHeadContradiction hu hne hk'l hk'0 h1.symm).elim

end Kepler.Text.TameSpine
