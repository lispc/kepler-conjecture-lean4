/-
  Kepler.Text.TameSpine.TameList52 — B1 Tame_list 地基批 52：
  aad 新章开章（tamespine-port-plan §4 批次表 B1 行；接续批 51 =
  TameList51.lean，批 51 终点 = HOL :13192（XWCNBMA 别名记档跳过）；
  本批起点 = HOL :13196 `mem_minimalFace_nonFinals`。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测；批 51 头注预记
  「:13203 COMPLETE_INDUCT」经实测修正为 :13208（:13203 实为前件
  mem_minimalFace_nonFinals 的 `]);;` 收尾行，MESON 槽在 :13202
  ——预记行号偏移记档）。

  槽面侦察裁定（批 51 头注预记面的对拍结论）：

  - **定义层三件全部在册，零新 def 面**（批 51 未侦察，本批全核）：
    - `nonFinals`（tame_defs.hl:413 `FILTER (\f. ~SND f) (faces g)`）
      ↦ `Kepler.Graphs.nonFinals`（Graph.lean:120
      `g.faces.filter (fun f => !f.final)`，`~SND` ↦ `!final`，
      批 6 finalGraphSpine 已消费）；
    - `minimalFace`（tame_defs2.hl:249
      `minimal_el (LENGTH o FST)`）↦ `Kepler.Graphs.minimalFace`
      （Plane1.lean:12 `minimal (fun f => f.vertices.length) fs`，
      LENGTH o FST ↦ vertices.length，Face 载体批 6 既档；
      Inhabited Face Graph.lean:33）；
    - `minimal_el`（tame_defs.hl:308；`[] ↦ CHOICE UNIV` 的 junk
      吸收 = `default`）↦ `Kepler.Graphs.minimal`（ListAux.lean:40）；
      `mem_minimal_el`（tame_list.hl:803）槽 ↦
      `Kepler.Graphs.minimal_in_set`（ListAuxLemmas.lean:606），桥件
      memMinimalEl（TameList2.lean:270）批 2 已落，本批直投。
  - **COMPLETE_INDUCT**（tame_list.hl:13208，自记「same as
    num_WF」）：mathlib `Nat.strong_induction_on`
    （Mathlib/Data/Nat/Init.lean:260 `{p} (n)
    (h : ∀ n, ∀ m < n, p m → p n) : p n`）点状形逐字同内容；HOL
    语句为 ∀∀ 打包形，零镜像差一层打包 → 桥形 completeInduct
    一行落地（本批 §1，非止损件）。
  - **hd_cat**（tame_list.hl:13285 `~(a=[]) ==> HD (cat a b) =
    HD a`）：mathlib `List.head!_append`（Mathlib/Data/List/Basic.lean
    :425 `head! (s ++ t) = head! s`，`h : s ≠ []`）逐字同语句零镜像
    记档（批 48 fst_zip 体例）；HD/cat ↦ head!/++ 既档（批 11/12）。
  - **last_cat**（tame_list.hl:13293 `~(b=[]) ==> LAST (cat a b) =
    LAST b`）：本仓 `Kepler.Graphs.getLast!_append_of_ne_nil`
    （FaceDivisionProps4.lean:1454）逐字同语句零镜像零重落记档。
  - **EL 家族约定**：EL ↦ `List.getD` getD 形（越界 junk 按默认元
    吸收，批 2 §2 nth_EL/EL_REPLICATE 既档），前提内域经
    `List.getD_eq_getElem`（Mathlib/Data/List/GetD.lean:33）转
    getElem 消费 core 件（`getElem_append_left`
    Init/Data/List/BasicAux.lean:211、`getElem_dropLast`
    Init/Data/List/Lemmas.lean:3150）。
  - **rcons/TL/BUTLAST/sizel 约定既档**：`rcons t h` ↦ `t ++ [h]`
    （批 2 rconsNonnil）、`TL` ↦ `List.tail`、`BUTLAST` ↦
    `List.dropLast`、`sizel` ↦ `List.length`、`LAST`/`HD` ↦
    `getLast!`/`head!`（批 11/12）、`upt` ↦ 批 2 `Upt`、
    `set_of_list` ↦ `List.toFinset`（批 2 cardUpt 记档）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13196-:13407）：

  §1 章首件：`mem_minimalFace_nonFinals` :13196 `!g. ~(nonFinals g
  = []) ==> MEM (minimalFace (nonFinals g)) (nonFinals g)` ↦
  `memMinimalFaceNonFinals`（真证）。HOL 证体两行（minimalFace 定义
  展开 + MESON[mem_minimal_el]）↦ minimal_in_set 直投——minimalFace
  定义性 defeq（GeneratorProps.lean:947 同款消费先例）；
  COMPLETE_INDUCT :13208 ↦ completeInduct 桥形如上。

  §2 算术对：`f_mono_pair` :13216 / `f_mono_lt_pair` :13241（num
  单调性：步内递增/严增 ⇒ 有界段内全程单调，j 归纳 + LE_TRANS/
  LT_TRANS）↦ fMonoPair / fMonoLtPair（真证；归纳分流 eq_or_lt/
  lt_succ_iff，算术槽 omega 收口，trans 槽 core
  Nat.le_trans/Nat.lt_trans 直投）。

  §3 枚举件：`mem_enumAppend` :13266 `!iss nmax a u. MEM a iss /\
  LAST a <= u /\ u <= nmax ==> MEM (cat a [u]) (enumAppend nmax
  iss)` ↦ memEnumAppend（真证）；消费定义 `enumAppend`
  （tame_defs2.hl:211 `flatten (MAP (\is. MAP (\n. APPEND is [n])
  (upt (LAST is) (SUC nmax))) iss)`）批 51 前未落地 → 定义层首落
  `enumAppendSpine`（本批唯一新 def）。证体逐槽：Seq2.mem_flatten/
  MEM_MAP ↦ core `List.mem_flatten`/`List.mem_map`；Seq.mem_iota ↦
  Upt 展开 + `List.mem_range`（泛化形显式证人 `u - a.getLast!`，
  mem_range' 泛化形须 ∃ 证人雷区既档）+ omega 收算术槽。

  §4 Seq append/rcons/butlast 家族（tame_list.hl:13304-:13407；
  hd_cat/last_cat 零镜像记档如上，落地八件全真证）：
  - `hd_rcons` :13304 ↦ hdRcons（head!_append 零镜像件就地消费 +
    cases 两支；`if t = []` 经 Classical 求决保持泛型 α，
    TameList17 transformListSpine `open Classical in` 同款）；
  - `el_rcons` :13314 ↦ elRcons（getD 双向转 + core
    getElem_append_left）；
  - `el_rcons_size` :13327 ↦ elRconsSize（getD 转 + 尾元槽）；
  - `LAST_TL` :13345 ↦ lastTL（getLast!_eq_getLast 私桥批 37 同证
    重落——private 不跨文件雷区既档 + core getLast_cons；
    getLast! junk 面经非空前提封死）；
  - `BUTLAST_NIL` :13356 ↦ butlastNil（core length_dropLast +
    length_nil + omega）；
  - `size_tail` :13368 ↦ sizeTail（core length_tail 直投；HOL
    非空前提在 Lean 无条件 length_tail 下保真闲置，
    unusedVariables 记档批 50 体例）；
  - `rcons_butlast` :13377 ↦ rconsButlast（mathlib
    dropLast_append_getLast + getLast!_eq_getLast 私桥换装）；
  - `EL_BUTLAST` :13395 ↦ elButlast（getD 双向转 + core
    getElem_dropLast）。

  本批范围边界：:13409 `next_el_list_pairs_eq` 起为 next_el/
  list_pairs/zip/rot/index 机制章（Seq.next_el、list_pairs 泛型
  载体与 zip/rot/index 槽在册性未侦察），自然边界判批 53；
  :13436 card_le_size/:13449 betwn_nil 随后同批。

  新落地载体：enumAppendSpine（§3 定义层首落，tame_defs2.hl:211
  逐字折算）。

  诚实记账：十三件全真证（memMinimalFaceNonFinals/completeInduct/
  fMonoPair/fMonoLtPair/memEnumAppend/hdRcons/elRcons/elRconsSize/
  lastTL/butlastNil/sizeTail/rconsButlast/elButlast）+ 一 def
  （enumAppendSpine），零 sorry、零止损件、零记账债；hd_cat/last_cat
  零镜像记档如上（非止损件）。范围决策：批 52 射程收口至 :13407
  （aad 开章判件 + 算术对 + 枚举件 + Seq append/rcons/butlast 家族，
  自然边界）。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 53 接续点：HOL :13409 `next_el_list_pairs_eq`（`!x s. uniq s /\
  MEM x s ==> MEM (x, next_el s x) (list_pairs s)`——HOL 证体
  zip/rot/index 机制：Seq.nth_index/index_mem/index_el/nth_zip/
  next_el_alt 五槽；开工先核 Seq.next_el、List_hypermap.list_pairs
  泛型载体与 rot/index 家族在册性）；其后 :13436 card_le_size
  （`CARD (set_of_list s) <= sizel s`——mathlib List.toFinset_card_le
  Mathlib/Data/Finset/Card.lean:209 逐字同语句，预记或零镜像）、
  :13449 betwn_nil。
-/

import Kepler.Text.TameSpine.TameList51

namespace Kepler.Text.TameSpine

open Kepler.Graphs (nonFinals minimalFace minimal_in_set)

/-! ### §1 aad 新章首件（tame_list.hl:13196-:13213） -/

/-- **HOL `mem_minimalFace_nonFinals`**（tame_list.hl:13196
`!g. ~(nonFinals g = []) ==> MEM (minimalFace (nonFinals g))
(nonFinals g)`，aad 新章首件）。证体两行（minimalFace 定义展开 +
MESON[mem_minimal_el]）↦ `Kepler.Graphs.minimal_in_set` 直投：
minimalFace = minimal vertices.length 定义性 defeq
（GeneratorProps.lean:947 同款消费先例）。 -/
theorem memMinimalFaceNonFinals (g : Kepler.Graphs.Graph)
    (h : nonFinals g ≠ []) :
    minimalFace (nonFinals g) ∈ nonFinals g :=
  minimal_in_set _ h

/-- **HOL `COMPLETE_INDUCT`**（tame_list.hl:13208 `!P. (!j. (!i.
i < j ==> P i) ==> P j) ==> (!i. P i)`，自记「same as num_WF」）——
mathlib `Nat.strong_induction_on` 点状形零内容差，HOL ∀∀ 打包形
桥面一行落地。 -/
theorem completeInduct {p : ℕ → Prop} (h : ∀ j, (∀ i, i < j → p i) → p j) :
    ∀ i, p i := fun i => Nat.strong_induction_on i h

/-! ### §2 f_mono 算术对（tame_list.hl:13216-:13264） -/

/-- **HOL `f_mono_pair`**（tame_list.hl:13216 `!(f:num->num) n.
(!i. SUC i < n ==> f i <= f (SUC i)) ==> (!j i. i <= j /\ j < n ==>
f i <= f j)`）。证体：j 归纳 + LE_TRANS 槽 ↦ core `Nat.le_trans`，
分流/算术槽 omega。 -/
theorem fMonoPair (f : ℕ → ℕ) (n : ℕ) (h : ∀ i, i + 1 < n → f i ≤ f (i + 1))
    (j i : ℕ) (hij : i ≤ j) (hjn : j < n) : f i ≤ f j := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with hi | hi
    · subst hi
      exact Nat.le_refl _
    · exact Nat.le_trans (ih (Nat.le_of_lt_succ hi) (by omega)) (h j hjn)

/-- **HOL `f_mono_lt_pair`**（tame_list.hl:13241 `!(f:num->num) n.
(!i. SUC i < n ==> f i < f (SUC i)) ==> (!j i. i < j /\ j < n ==>
f i < f j)`）。证体：j 归纳 + LT_TRANS 槽 ↦ core `Nat.lt_trans`；
`i = j` 分流即步内前提直投（subst 后走 `h _ hjn`——subst 方向吞
变元走 `_` 槽，雷区新记）。 -/
theorem fMonoLtPair (f : ℕ → ℕ) (n : ℕ) (h : ∀ i, i + 1 < n → f i < f (i + 1))
    (j i : ℕ) (hij : i < j) (hjn : j < n) : f i < f j := by
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero i)
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hi | hi
    · exact Nat.lt_trans (ih hi (by omega)) (h j hjn)
    · subst hi
      exact h _ hjn

/-! ### §3 enumAppend 定义层首落 + mem_enumAppend（tame_defs2.hl:211
/ tame_list.hl:13266-:13283） -/

/-- HOL `enumAppend`（tame_defs2.hl:211 `flatten (MAP (\is. MAP
(\n. APPEND is [n]) (upt (LAST is) (SUC nmax))) iss)`）↦
`enumAppendSpine`（定义层首落：upt ↦ 批 2 `Upt`、`LAST` ↦
`getLast!`、`APPEND` ↦ `++`、`FLAT` ↦ `List.flatten`）。 -/
def enumAppendSpine (nmax : ℕ) (iss : List (List ℕ)) : List (List ℕ) :=
  (iss.map fun is => (Upt is.getLast! (nmax + 1)).map fun n => is ++ [n]).flatten

/-- **HOL `mem_enumAppend`**（tame_list.hl:13266 `!iss nmax a u.
MEM a iss /\ LAST a <= u /\ u <= nmax ==> MEM (cat a [u])
(enumAppend nmax iss)`）。证体：Seq2.mem_flatten/MEM_MAP 槽 ↦ core
`List.mem_flatten`/`List.mem_map`；Seq.mem_iota 槽 ↦ Upt 展开 +
`List.mem_range`（显式证人 `u - a.getLast!`）+ omega。 -/
theorem memEnumAppend {nmax : ℕ} {iss : List (List ℕ)} {a : List ℕ} {u : ℕ}
    (ha : a ∈ iss) (hla : a.getLast! ≤ u) (hu : u ≤ nmax) :
    a ++ [u] ∈ enumAppendSpine nmax iss := by
  unfold enumAppendSpine
  rw [List.mem_flatten]
  refine ⟨(Upt a.getLast! (nmax + 1)).map fun n => a ++ [n],
    List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
  rw [List.mem_map]
  have hupt : u ∈ Upt a.getLast! (nmax + 1) := by
    unfold Upt
    rw [if_pos (by omega)]
    exact List.mem_map.mpr ⟨u - a.getLast!,
      List.mem_range.mpr (by omega), by omega⟩
  exact ⟨u, hupt, rfl⟩

/-! ### §4 Seq append/rcons/butlast 家族（tame_list.hl:13304-:13407；
hd_cat/last_cat 零镜像记档见头注） -/

/-- 非空表 `getLast!` 即 `getLast`（批 37 私件同证重落，private
不跨文件雷区既档）。 -/
private theorem getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp

open Classical in
/-- **HOL `hd_rcons`**（tame_list.hl:13304 `HD (rcons t h) =
if (t=[]) then h else HD t`）。证体：Seq.rcons/HD 展开 + hd_cat 槽
↦ mathlib `List.head!_append`（零镜像既档件就地消费）+ cases 两支；
`if t = []` 经 Classical 求决保持泛型 α（批 17 transformListSpine
`open Classical in` 前置同款——docstring 置于 open 后雷区新记）。 -/
theorem hdRcons {α : Type*} [Inhabited α] (t : List α) (h : α) :
    (t ++ [h]).head! = if t = [] then h else t.head! := by
  cases t with
  | nil => simp
  | cons a t' =>
    rw [List.head!_append [h] (List.cons_ne_nil a t')]
    simp

/-- **HOL `el_rcons`**（tame_list.hl:13314 `i < sizel t ==>
EL i (rcons t h) = EL i t`；EL getD 形既档）。证体：getD 双向转 +
core `List.getElem_append_left`（BasicAux.lean:211 逐字同语句）。 -/
theorem elRcons {α : Type*} {t : List α} {h : α} {d : α} {i : ℕ}
    (hi : i < t.length) :
    (t ++ [h]).getD i d = t.getD i d := by
  have h1 : i < (t ++ [h]).length := by
    rw [List.length_append, List.length_singleton]
    omega
  rw [List.getD_eq_getElem (t ++ [h]) d h1, List.getD_eq_getElem t d hi,
    List.getElem_append_left hi]

/-- **HOL `el_rcons_size`**（tame_list.hl:13327 `EL (sizel t)
(rcons t h) = h`；无前提件，尾元自动内域）。 -/
theorem elRconsSize {α : Type*} (t : List α) (h : α) (d : α) :
    (t ++ [h]).getD t.length d = h := by
  rw [List.getD_eq_getElem (t ++ [h]) d (by simp)]
  simp

/-- **HOL `LAST_TL`**（tame_list.hl:13345 `2 <= sizel xs ==>
LAST xs = LAST (TL xs)`）。证体：cons 剥壳 + getLast!_eq_getLast
私桥换装 + core `getLast_cons`；两处空表支 omega/simp 封死。 -/
theorem lastTL {α : Type*} [Inhabited α] {xs : List α} (h : 2 ≤ xs.length) :
    xs.tail.getLast! = xs.getLast! := by
  cases xs with
  | nil => simp at h
  | cons a t =>
    have ht : t ≠ [] := by
      cases t with
      | nil => simp at h
      | cons b t' => exact List.cons_ne_nil b t'
    show t.getLast! = (a :: t).getLast!
    rw [getLast!_eq_getLast ht, getLast!_eq_getLast (List.cons_ne_nil a t)]
    exact (List.getLast_cons ht).symm

/-- **HOL `BUTLAST_NIL`**（tame_list.hl:13356 `1 < sizel xs ==>
~(BUTLAST xs = [])`）。证体：core `length_dropLast` + `length_nil`
+ omega。 -/
theorem butlastNil {α : Type*} {xs : List α} (h : 1 < xs.length) :
    xs.dropLast ≠ [] := by
  intro hc
  have h2 : xs.dropLast.length = xs.length - 1 := List.length_dropLast
  rw [hc, List.length_nil] at h2
  omega

/-- **HOL `size_tail`**（tame_list.hl:13368 `~(sizel xs = 0) ==>
sizel (TL xs) = sizel xs - 1`）——core `List.length_tail` 直投；HOL
非空前提保真闲置（unusedVariables 记档批 50 体例）。 -/
theorem sizeTail {α : Type*} {xs : List α} (h : xs ≠ []) :
    xs.tail.length = xs.length - 1 :=
  List.length_tail

/-- **HOL `rcons_butlast`**（tame_list.hl:13377 `~(xs = []) ==>
xs = rcons (butlast xs) (LAST xs)`）。证体：mathlib
`dropLast_append_getLast`（Mathlib/Data/List/Basic.lean:315）+
getLast!_eq_getLast 私桥换装。 -/
theorem rconsButlast {α : Type*} [Inhabited α] {xs : List α} (h : xs ≠ []) :
    xs = xs.dropLast ++ [xs.getLast!] := by
  rw [getLast!_eq_getLast h]
  exact (List.dropLast_append_getLast h).symm

/-- **HOL `EL_BUTLAST`**（tame_list.hl:13395 `SUC i < sizel xs ==>
EL i (BUTLAST xs) = EL i xs`；EL getD 形既档）。证体：getD 双向转 +
core `getElem_dropLast`（Lemmas.lean:3150 逐字同语句）。 -/
theorem elButlast {α : Type*} {xs : List α} {d : α} {i : ℕ}
    (h : i + 1 < xs.length) :
    xs.dropLast.getD i d = xs.getD i d := by
  have hd : i < xs.dropLast.length := by rw [List.length_dropLast]; omega
  have hd2 : i < xs.length := by omega
  rw [List.getD_eq_getElem xs.dropLast d hd, List.getD_eq_getElem xs d hd2,
    List.getElem_dropLast hd]

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；十三件正文 + 消费链槽全绿零 sorryAx——
#print axioms Kepler.Text.TameSpine.memMinimalFaceNonFinals
#print axioms Kepler.Text.TameSpine.completeInduct
#print axioms Kepler.Text.TameSpine.fMonoPair
#print axioms Kepler.Text.TameSpine.fMonoLtPair
#print axioms Kepler.Text.TameSpine.memEnumAppend
#print axioms Kepler.Text.TameSpine.hdRcons
#print axioms Kepler.Text.TameSpine.elRcons
#print axioms Kepler.Text.TameSpine.elRconsSize
#print axioms Kepler.Text.TameSpine.lastTL
#print axioms Kepler.Text.TameSpine.butlastNil
#print axioms Kepler.Text.TameSpine.sizeTail
#print axioms Kepler.Text.TameSpine.rconsButlast
#print axioms Kepler.Text.TameSpine.elButlast
-/
