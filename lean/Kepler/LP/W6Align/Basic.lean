/-
  Kepler.LP.W6Align.Basic — W6-A 逐图 archive 对齐的内核件（车道 hlp-w6a）。

  机器生成：`pipeline/lp/gen_w6a_align.py`；不要手改。

  语义锚：
  * `decodeHypermap` = HOL `convert_to_list`
    （list_hypermap_computations.hl:134-146）的 Lean 直译：去 `_`、按空格
    run 分词、丢 id 与 count 两 token、(len, face…) 配对。**字节级单遍
    实现**（本工具链 String 为 UTF-8 ByteArray 承载，`String.toList` 走
    按索引解码 = 内核 O(n²)；数据侧全 ASCII——生成器门槛 (a) 逐字节
    断言——故直接在 `toByteArray.data.toList` 上单遍扫描：字节 95 (`_`)
    跳过 = 严格 global-replace 语义，32 = 分隔，48..57 = 数字）。全结构
    递归，内核可归约；计数核对由生成器承担（生成侧零违例为停批门槛）。
  * `CertOf g L` = 证书 g 的 hypermap 串解码恰为 archive 条目 L
    （`fgraph ℕ` 定义性展开为 `List (List Nat)`；逐元素精确相等，
    不做同构/重编号）。
  * `listAt` = 内核友好的取元（越界给 `Inhabited` 默认；本模块所有
    用点都在 19,715 范围内，越界支不触发）。

  import 闭包只含 `Kepler.Assembly.GoodListDefs`（tameArchiveLists）与
  `Kepler.Text.LP.W6Data`（dataAll）；本模块不被任何既有文件 import。
-/
import Kepler.Assembly.GoodListDefs
import Kepler.Text.LP.W6Data

set_option maxRecDepth 4000000

namespace Kepler.LP.W6Align
open Kepler.Assembly Kepler.Text.LP Kepler.Text.LP.W6Data

deriving instance Inhabited for LpPrecision, LpSplitType, LpSplitNode,
  LpTerminalCase, LpCaseTree, LpGraphCert

/-- 单遍字节级分词：UTF-8 字节表 → Nat token（数据侧 ASCII：32 = 空格、
48..57 = 数字、95 = `_` 跳过）。`seen` 区分「尾随分隔符」与「token 0」；
token 以 `cur :: acc` 压入、尾部一次 `reverse`（整体 O(n)，无中间
String、无逐 token toList/reverse）。 -/
def natToksGo (cur : Nat) (seen : Bool) (acc : List Nat) : List UInt8 → List Nat
  | [] => if seen then (cur :: acc).reverse else acc.reverse
  | b :: cs =>
      if b = 32 then
        (if seen then natToksGo 0 false (cur :: acc) cs
                  else natToksGo 0 false acc cs)
      else if b = 95 then natToksGo cur seen acc cs
      else natToksGo (cur * 10 + (b.toNat - 48)) true acc cs

/-- (len, face…) 配对（fuel = token 数上界；越界/截断给短表，
由对齐定理的精确相等排除）。 -/
def decodeFacesF : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, len :: rest => rest.take len :: decodeFacesF n (rest.drop len)

/-- HOL `convert_to_list`：`id :: count :: (len, face…) 串联` → 面表。
id 与 count 两 token 丢弃（与 HOL 逐字一致；count 核对 = 生成侧门槛）。 -/
def decodeHypermap (hs : String) : List (List Nat) :=
  match natToksGo 0 false [] hs.toByteArray.data.toList with
  | _ :: _ :: toks => decodeFacesF (toks.length + 1) toks
  | _ => []

/-- **CertOf**：证书 g 与 archive 条目 L 的对齐关系——hypermap 串解码
恰为该条目（逐元素精确相等）。W6-B 可由逐图 `align_*` + 表事实升级为
`∀ L ∈ tameArchiveLists, ∃ g ∈ dataAll, CertOf g L`。 -/
abbrev CertOf (g : LpGraphCert) (L : List (List Nat)) : Prop :=
  decodeHypermap g.hypermapString = L

/-- 内核友好取元（越界给默认值；对齐用点均在范围内）。 -/
def listAt [Inhabited α] : Nat → List α → α
  | _, [] => default
  | 0, a :: _ => a
  | k + 1, _ :: t => listAt k t

end Kepler.LP.W6Align
