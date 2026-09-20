/-
  Kepler/Assembly/IdLists — `nonlinearInequalities` 接口六 ID 清单数据
  （P6-E 接口侧收尾件，2026-09-20）。

  **本文件由 `lean/scripts/gen_idlists.py` 生成，请勿手改。**
  数据源与规则版本见脚本 docstring；再生成命令：

    python3 lean/scripts/gen_idlists.py \
        --flyspeck reference/flyspeck/text_formalization \
        --ineqs-json <g4e>/pipeline/interval/out/ineqs.json \
        --out lean/Kepler/Assembly/IdLists.lean

  镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353）：
  `the_nonlinear_inequalities`（the_main_statement.hl:55-59）的六分量，
  每分量 = 生成式合取的 ID 清单（Assembly.lean:146-161 §2a 的已批准折算：
  ID 清单（数据）+ `AllCertified` 量化命题）。

  清单口径（HOL 构造规则逐条翻译，折算登记 docs/statement-fidelity.md 附录）：
  - `packNonlinearNonOx3q1hIds`：merge_ineq.hl:98-116，
    Flypaper ∩ {UKBRPFE,BIEFJHU,OXLZLEZ,TSKAJXY} ≠ ∅ 且 idv 不带
    "OXLZLEZ 6346351218" 前缀（81 条）；
  - `ox3q1hIds`：merge_ineq.hl:78-92，ineqdata3q1h.hl 的 46 条 record
    × 5 支 = 230 条（"OXLZLEZ 6346351218 i n"，i ∈ 0..4，n ∈ 0..45）；
  - `mainNonlinearTerminalV11Ids`：terminal.hl:24-44，Main_estimate 标签
    （109 条；含 main_estimate_ineq.hl:957-963 hex_ear 循环 35 条）；
  - `lpIneqsIds`：the_main_statement.hl:29-45，Lp/Tablelp/Lp_aux 标签或
    idv = "6170936724"，剔除 Tame_lemmas.deprecated_quads 6 条（127 条）；
  - `packIneqDefAIds`：YSSKQOY.hl:24-28，Flypaper ∩ {UKBRPFE,WAZLDCD,BIEFJHU}
    ≠ ∅（5 条）；
  - `kcblrqcIneqDefIds`：tame_lemmas-compiled.hl:34-46，Flypaper ∩ {KCBLRQC}
    ≠ ∅ 或 idv ∈ extra_ids（3 + quad_idv 17），剔除 deprecated_quads（28 条）。

  顺序说明：除 ox3q1h 外五清单按 HOL 注册表内存序（`Ineq.add` 前插，
  ineq.hl:39-42；载入序 build/build.hl:86-87）——与 HOL `filter (!Ineq.ineqs)`
  的合取顺序逐项对应；ox3q1h 按其定义 `ox3q1h_term()` 的 n 主序
  （merge_ineq.hl:89-91）。顺序无语义影响（合取/全称量化对排列封闭），
  保留它只为逐项对照可审计。
-/

namespace Kepler.Assembly

/-- HOL `pack_nonlinear_non_ox3q1h`（merge_ineq.hl:118-134）分量清单。 对应 Assembly.lean 占位 `idsPackNonlinearNonOx3q1h`（:171）。 -/
def packNonlinearNonOx3q1hIds : List String :=
  ["6096597438 b",
  "6096597438 a",
  "1965189142 a",
  "1965189142 34",
  "GRKIBMP B V2",
  "GRKIBMP A V2",
  "JSPEVYT",
  "CJFZZDW",
  "CIHTIUM",
  "QZECFIC wt2 A",
  "QZECFIC wt1",
  "QZECFIC wt0 sqrt8",
  "QZECFIC wt0 corner",
  "QZECFIC wt0",
  "GCKBQEA",
  "RQWUDDU",
  "QITNPEA 4003532128 a",
  "IXPOTPA",
  "TXQTPVC",
  "QITNPEA 3725403817",
  "QITNPEAv2 4003532128",
  "PEMKWKU",
  "TEWNSCJ",
  "QITNPEA  5400790175 b",
  "QITNPEA  5400790175 a",
  "QITNPEA 3848804089",
  "QITNPEA 5814748276",
  "QITNPEA 6206775865",
  "QITNPEA 5653753305",
  "BIXPCGW 9455898160",
  "FWGKMBZ",
  "FHBVYXZ b",
  "FHBVYXZ a",
  "FHBVYXZv2 a",
  "QITNPEA 2134082733",
  "QITNPEA1 2 2 9063653052 A",
  "QITNPEA1 2 1 9063653052 A",
  "QITNPEA1 2 0 9063653052 A",
  "QITNPEA1 1 2 9063653052 A",
  "QITNPEA1 1 1 9063653052 A",
  "QITNPEA1 1 0 9063653052 A",
  "QITNPEA 9939613598",
  "BIXPCGW 7274157868 a",
  "BIXPCGW b",
  "BIXPCGW 1738910218 a2",
  "BIXPCGW 7080972881 a2",
  "BIXPCGW 6652007036 a2",
  "GLFVCVK4 2477216213 y4subcrit",
  "GLFVCVK4 2477216213 y4supercrit",
  "GLFVCVK4 2477216213 y4crit",
  "GLFVCVK4a 8328676778",
  "GLFVCVK4 2477216213",
  "MKFKQWU halfwt",
  "MKFKQWU",
  "ZTGIJCF4 1 1 1 1 1821661595",
  "ZTGIJCF4 1 1 1 0 1821661595",
  "ZTGIJCF4 1 1 0 1 1821661595",
  "ZTGIJCF4 1 1 0 0 1821661595",
  "ZTGIJCF4 1 0 1 1 1821661595",
  "ZTGIJCF4 1 0 1 0 1821661595",
  "ZTGIJCF4 1 0 0 1 1821661595",
  "ZTGIJCF4 1 0 0 0 1821661595",
  "ZTGIJCF4 0 1 1 1 1821661595",
  "ZTGIJCF4 0 1 1 0 1821661595",
  "ZTGIJCF4 0 1 0 1 1821661595",
  "ZTGIJCF4 0 1 0 0 1821661595",
  "ZTGIJCF4 0 0 1 1 1821661595",
  "ZTGIJCF4 0 0 1 0 1821661595",
  "ZTGIJCF4 0 0 0 1 1821661595",
  "ZTGIJCF4 0 0 0 0 1821661595",
  "ZTGIJCF0",
  "TSKAJXY-GXSABWC DIV",
  "TSKAJXY-delta_x4",
  "TSKAJXY-eulerA",
  "TSKAJXY-XLLIPLS",
  "TSKAJXY-WKGUESB sym",
  "TSKAJXY-IYOUOBF sharp v2",
  "TSKAJXY-IYOUOBF sym",
  "TSKAJXY-RIBCYXU sym",
  "TSKAJXY-RIBCYXU sharp",
  "TSKAJXY-TADIAMB"]

-- 生成期条数钉死（内核 `rfl` 可判）。
set_option maxRecDepth 2048 in
theorem packNonlinearNonOx3q1hIds_length : packNonlinearNonOx3q1hIds.length = 81 := rfl

/-- HOL `ox3q1h`（merge_ineq.hl:90-92）分量清单（定义序，n 主 i 次）。 对应 Assembly.lean 占位 `idsOx3q1h`（:173）。 -/
def ox3q1hIds : List String :=
  ["OXLZLEZ 6346351218 0 0",
  "OXLZLEZ 6346351218 1 0",
  "OXLZLEZ 6346351218 2 0",
  "OXLZLEZ 6346351218 3 0",
  "OXLZLEZ 6346351218 4 0",
  "OXLZLEZ 6346351218 0 1",
  "OXLZLEZ 6346351218 1 1",
  "OXLZLEZ 6346351218 2 1",
  "OXLZLEZ 6346351218 3 1",
  "OXLZLEZ 6346351218 4 1",
  "OXLZLEZ 6346351218 0 2",
  "OXLZLEZ 6346351218 1 2",
  "OXLZLEZ 6346351218 2 2",
  "OXLZLEZ 6346351218 3 2",
  "OXLZLEZ 6346351218 4 2",
  "OXLZLEZ 6346351218 0 3",
  "OXLZLEZ 6346351218 1 3",
  "OXLZLEZ 6346351218 2 3",
  "OXLZLEZ 6346351218 3 3",
  "OXLZLEZ 6346351218 4 3",
  "OXLZLEZ 6346351218 0 4",
  "OXLZLEZ 6346351218 1 4",
  "OXLZLEZ 6346351218 2 4",
  "OXLZLEZ 6346351218 3 4",
  "OXLZLEZ 6346351218 4 4",
  "OXLZLEZ 6346351218 0 5",
  "OXLZLEZ 6346351218 1 5",
  "OXLZLEZ 6346351218 2 5",
  "OXLZLEZ 6346351218 3 5",
  "OXLZLEZ 6346351218 4 5",
  "OXLZLEZ 6346351218 0 6",
  "OXLZLEZ 6346351218 1 6",
  "OXLZLEZ 6346351218 2 6",
  "OXLZLEZ 6346351218 3 6",
  "OXLZLEZ 6346351218 4 6",
  "OXLZLEZ 6346351218 0 7",
  "OXLZLEZ 6346351218 1 7",
  "OXLZLEZ 6346351218 2 7",
  "OXLZLEZ 6346351218 3 7",
  "OXLZLEZ 6346351218 4 7",
  "OXLZLEZ 6346351218 0 8",
  "OXLZLEZ 6346351218 1 8",
  "OXLZLEZ 6346351218 2 8",
  "OXLZLEZ 6346351218 3 8",
  "OXLZLEZ 6346351218 4 8",
  "OXLZLEZ 6346351218 0 9",
  "OXLZLEZ 6346351218 1 9",
  "OXLZLEZ 6346351218 2 9",
  "OXLZLEZ 6346351218 3 9",
  "OXLZLEZ 6346351218 4 9",
  "OXLZLEZ 6346351218 0 10",
  "OXLZLEZ 6346351218 1 10",
  "OXLZLEZ 6346351218 2 10",
  "OXLZLEZ 6346351218 3 10",
  "OXLZLEZ 6346351218 4 10",
  "OXLZLEZ 6346351218 0 11",
  "OXLZLEZ 6346351218 1 11",
  "OXLZLEZ 6346351218 2 11",
  "OXLZLEZ 6346351218 3 11",
  "OXLZLEZ 6346351218 4 11",
  "OXLZLEZ 6346351218 0 12",
  "OXLZLEZ 6346351218 1 12",
  "OXLZLEZ 6346351218 2 12",
  "OXLZLEZ 6346351218 3 12",
  "OXLZLEZ 6346351218 4 12",
  "OXLZLEZ 6346351218 0 13",
  "OXLZLEZ 6346351218 1 13",
  "OXLZLEZ 6346351218 2 13",
  "OXLZLEZ 6346351218 3 13",
  "OXLZLEZ 6346351218 4 13",
  "OXLZLEZ 6346351218 0 14",
  "OXLZLEZ 6346351218 1 14",
  "OXLZLEZ 6346351218 2 14",
  "OXLZLEZ 6346351218 3 14",
  "OXLZLEZ 6346351218 4 14",
  "OXLZLEZ 6346351218 0 15",
  "OXLZLEZ 6346351218 1 15",
  "OXLZLEZ 6346351218 2 15",
  "OXLZLEZ 6346351218 3 15",
  "OXLZLEZ 6346351218 4 15",
  "OXLZLEZ 6346351218 0 16",
  "OXLZLEZ 6346351218 1 16",
  "OXLZLEZ 6346351218 2 16",
  "OXLZLEZ 6346351218 3 16",
  "OXLZLEZ 6346351218 4 16",
  "OXLZLEZ 6346351218 0 17",
  "OXLZLEZ 6346351218 1 17",
  "OXLZLEZ 6346351218 2 17",
  "OXLZLEZ 6346351218 3 17",
  "OXLZLEZ 6346351218 4 17",
  "OXLZLEZ 6346351218 0 18",
  "OXLZLEZ 6346351218 1 18",
  "OXLZLEZ 6346351218 2 18",
  "OXLZLEZ 6346351218 3 18",
  "OXLZLEZ 6346351218 4 18",
  "OXLZLEZ 6346351218 0 19",
  "OXLZLEZ 6346351218 1 19",
  "OXLZLEZ 6346351218 2 19",
  "OXLZLEZ 6346351218 3 19",
  "OXLZLEZ 6346351218 4 19",
  "OXLZLEZ 6346351218 0 20",
  "OXLZLEZ 6346351218 1 20",
  "OXLZLEZ 6346351218 2 20",
  "OXLZLEZ 6346351218 3 20",
  "OXLZLEZ 6346351218 4 20",
  "OXLZLEZ 6346351218 0 21",
  "OXLZLEZ 6346351218 1 21",
  "OXLZLEZ 6346351218 2 21",
  "OXLZLEZ 6346351218 3 21",
  "OXLZLEZ 6346351218 4 21",
  "OXLZLEZ 6346351218 0 22",
  "OXLZLEZ 6346351218 1 22",
  "OXLZLEZ 6346351218 2 22",
  "OXLZLEZ 6346351218 3 22",
  "OXLZLEZ 6346351218 4 22",
  "OXLZLEZ 6346351218 0 23",
  "OXLZLEZ 6346351218 1 23",
  "OXLZLEZ 6346351218 2 23",
  "OXLZLEZ 6346351218 3 23",
  "OXLZLEZ 6346351218 4 23",
  "OXLZLEZ 6346351218 0 24",
  "OXLZLEZ 6346351218 1 24",
  "OXLZLEZ 6346351218 2 24",
  "OXLZLEZ 6346351218 3 24",
  "OXLZLEZ 6346351218 4 24",
  "OXLZLEZ 6346351218 0 25",
  "OXLZLEZ 6346351218 1 25",
  "OXLZLEZ 6346351218 2 25",
  "OXLZLEZ 6346351218 3 25",
  "OXLZLEZ 6346351218 4 25",
  "OXLZLEZ 6346351218 0 26",
  "OXLZLEZ 6346351218 1 26",
  "OXLZLEZ 6346351218 2 26",
  "OXLZLEZ 6346351218 3 26",
  "OXLZLEZ 6346351218 4 26",
  "OXLZLEZ 6346351218 0 27",
  "OXLZLEZ 6346351218 1 27",
  "OXLZLEZ 6346351218 2 27",
  "OXLZLEZ 6346351218 3 27",
  "OXLZLEZ 6346351218 4 27",
  "OXLZLEZ 6346351218 0 28",
  "OXLZLEZ 6346351218 1 28",
  "OXLZLEZ 6346351218 2 28",
  "OXLZLEZ 6346351218 3 28",
  "OXLZLEZ 6346351218 4 28",
  "OXLZLEZ 6346351218 0 29",
  "OXLZLEZ 6346351218 1 29",
  "OXLZLEZ 6346351218 2 29",
  "OXLZLEZ 6346351218 3 29",
  "OXLZLEZ 6346351218 4 29",
  "OXLZLEZ 6346351218 0 30",
  "OXLZLEZ 6346351218 1 30",
  "OXLZLEZ 6346351218 2 30",
  "OXLZLEZ 6346351218 3 30",
  "OXLZLEZ 6346351218 4 30",
  "OXLZLEZ 6346351218 0 31",
  "OXLZLEZ 6346351218 1 31",
  "OXLZLEZ 6346351218 2 31",
  "OXLZLEZ 6346351218 3 31",
  "OXLZLEZ 6346351218 4 31",
  "OXLZLEZ 6346351218 0 32",
  "OXLZLEZ 6346351218 1 32",
  "OXLZLEZ 6346351218 2 32",
  "OXLZLEZ 6346351218 3 32",
  "OXLZLEZ 6346351218 4 32",
  "OXLZLEZ 6346351218 0 33",
  "OXLZLEZ 6346351218 1 33",
  "OXLZLEZ 6346351218 2 33",
  "OXLZLEZ 6346351218 3 33",
  "OXLZLEZ 6346351218 4 33",
  "OXLZLEZ 6346351218 0 34",
  "OXLZLEZ 6346351218 1 34",
  "OXLZLEZ 6346351218 2 34",
  "OXLZLEZ 6346351218 3 34",
  "OXLZLEZ 6346351218 4 34",
  "OXLZLEZ 6346351218 0 35",
  "OXLZLEZ 6346351218 1 35",
  "OXLZLEZ 6346351218 2 35",
  "OXLZLEZ 6346351218 3 35",
  "OXLZLEZ 6346351218 4 35",
  "OXLZLEZ 6346351218 0 36",
  "OXLZLEZ 6346351218 1 36",
  "OXLZLEZ 6346351218 2 36",
  "OXLZLEZ 6346351218 3 36",
  "OXLZLEZ 6346351218 4 36",
  "OXLZLEZ 6346351218 0 37",
  "OXLZLEZ 6346351218 1 37",
  "OXLZLEZ 6346351218 2 37",
  "OXLZLEZ 6346351218 3 37",
  "OXLZLEZ 6346351218 4 37",
  "OXLZLEZ 6346351218 0 38",
  "OXLZLEZ 6346351218 1 38",
  "OXLZLEZ 6346351218 2 38",
  "OXLZLEZ 6346351218 3 38",
  "OXLZLEZ 6346351218 4 38",
  "OXLZLEZ 6346351218 0 39",
  "OXLZLEZ 6346351218 1 39",
  "OXLZLEZ 6346351218 2 39",
  "OXLZLEZ 6346351218 3 39",
  "OXLZLEZ 6346351218 4 39",
  "OXLZLEZ 6346351218 0 40",
  "OXLZLEZ 6346351218 1 40",
  "OXLZLEZ 6346351218 2 40",
  "OXLZLEZ 6346351218 3 40",
  "OXLZLEZ 6346351218 4 40",
  "OXLZLEZ 6346351218 0 41",
  "OXLZLEZ 6346351218 1 41",
  "OXLZLEZ 6346351218 2 41",
  "OXLZLEZ 6346351218 3 41",
  "OXLZLEZ 6346351218 4 41",
  "OXLZLEZ 6346351218 0 42",
  "OXLZLEZ 6346351218 1 42",
  "OXLZLEZ 6346351218 2 42",
  "OXLZLEZ 6346351218 3 42",
  "OXLZLEZ 6346351218 4 42",
  "OXLZLEZ 6346351218 0 43",
  "OXLZLEZ 6346351218 1 43",
  "OXLZLEZ 6346351218 2 43",
  "OXLZLEZ 6346351218 3 43",
  "OXLZLEZ 6346351218 4 43",
  "OXLZLEZ 6346351218 0 44",
  "OXLZLEZ 6346351218 1 44",
  "OXLZLEZ 6346351218 2 44",
  "OXLZLEZ 6346351218 3 44",
  "OXLZLEZ 6346351218 4 44",
  "OXLZLEZ 6346351218 0 45",
  "OXLZLEZ 6346351218 1 45",
  "OXLZLEZ 6346351218 2 45",
  "OXLZLEZ 6346351218 3 45",
  "OXLZLEZ 6346351218 4 45"]

-- 生成期条数钉死（内核 `rfl` 可判）。
set_option maxRecDepth 2048 in
theorem ox3q1hIds_length : ox3q1hIds.length = 230 := rfl

/-- HOL `main_nonlinear_terminal_v11`（terminal.hl:37）分量清单。 对应 Assembly.lean 占位 `idsMainNonlinearTerminalV11`（:175）。 -/
def mainNonlinearTerminalV11Ids : List String :=
  ["2125338128",
  "2445657182",
  "9096461391",
  "8495326405",
  "OMKYNLT 3336871894",
  "5541487347",
  "6833979866",
  "4010906068",
  "7881254908",
  "5026777310a",
  "5405130650",
  "3603097872",
  "2468307358",
  "2171548893",
  "4680581274 delta top issue",
  "4680581274 delta issue-cayleyR",
  "4680581274 delta issue-cayleytr",
  "4680581274 delta issue-cayleytr0",
  "4680581274 2x",
  "4680581274 1x",
  "5550839403 delta",
  "5550839403",
  "8405387449",
  "9368433105",
  "5557288534 delta",
  "5557288534",
  "1348932091 delta",
  "1348932091",
  "2073661826",
  "6184614449",
  "5202826650 a",
  "4821120729",
  "8631418063",
  "8346775862",
  "6762190381",
  "7550003505 4 4 4",
  "7550003505 3 4 4",
  "7550003505 3 3 4",
  "7550003505 3 3 3",
  "7550003505 2 4 4",
  "7550003505 2 3 4",
  "7550003505 2 3 3",
  "7550003505 2 2 4",
  "7550003505 2 2 3",
  "7550003505 2 2 2",
  "7550003505 1 4 4",
  "7550003505 1 3 4",
  "7550003505 1 3 3",
  "7550003505 1 2 4",
  "7550003505 1 2 3",
  "7550003505 1 2 2",
  "7550003505 1 1 4",
  "7550003505 1 1 3",
  "7550003505 1 1 2",
  "7550003505 1 1 1",
  "7550003505 0 4 4",
  "7550003505 0 3 4",
  "7550003505 0 3 3",
  "7550003505 0 2 4",
  "7550003505 0 2 3",
  "7550003505 0 2 2",
  "7550003505 0 1 4",
  "7550003505 0 1 3",
  "7550003505 0 1 2",
  "7550003505 0 1 1",
  "7550003505 0 0 4",
  "7550003505 0 0 3",
  "7550003505 0 0 2",
  "7550003505 0 0 1",
  "7550003505 0 0 0",
  "5744538693",
  "7823243247",
  "9692636487",
  "6877738680",
  "7439076204",
  "6459846571",
  "1008824382",
  "8875146520",
  "1586903463",
  "1948775510",
  "5708641738",
  "2565248885",
  "5429238960",
  "2320951108",
  "7997589055",
  "5546286427",
  "7903347843",
  "3665919985",
  "6601228004",
  "3078028960",
  "1347067436",
  "2314572187",
  "7796879304",
  "6789182745",
  "4887115291",
  "7175074394",
  "2485876245b",
  "2485876245a",
  "4559601669b",
  "4559601669",
  "1117202051",
  "6843920790",
  "4828966562",
  "1834976363",
  "9563139965 f",
  "9563139965 e",
  "9563139965 d",
  "5691615370",
  "4717061266"]

-- 生成期条数钉死（内核 `rfl` 可判）。
set_option maxRecDepth 2048 in
theorem mainNonlinearTerminalV11Ids_length : mainNonlinearTerminalV11Ids.length = 109 := rfl

/-- HOL `lp_ineqs`（the_main_statement.hl:29-45）分量清单。 对应 Assembly.lean 占位 `idsLpIneqs`（:177）。 -/
def lpIneqsIds : List String :=
  ["6184614449",
  "4821120729",
  "8631418063",
  "8346775862",
  "6762190381",
  "3137600529",
  "6284721194",
  "9185711902",
  "6725783616",
  "1248932983",
  "1836408787",
  "5943578801",
  "2763799127",
  "4306175952",
  "2923748598",
  "6410081357",
  "7316455966",
  "3425739813",
  "5756588587",
  "4222324842",
  "9641946727",
  "2390583444",
  "7291663656",
  "6987934000",
  "7819193535",
  "8384511215",
  "4750199435",
  "1894886027",
  "5835568093",
  "4002562507",
  "7409690040",
  "9925287433",
  "4841020453",
  "3139693500",
  "3872614111",
  "4041673283",
  "1284543870",
  "6619134733",
  "8657368829",
  "7743522046",
  "5298513205",
  "3636849632",
  "6836427086",
  "2151506422",
  "181212899 5",
  "181212899 4",
  "181212899 3",
  "181212899 2",
  "181212899 1",
  "181212899 0",
  "8611785756",
  "8282573160",
  "4491491732",
  "1550635295",
  "9229542852",
  "1085358243",
  "3566713650",
  "7718591733",
  "7863247282",
  "1642527039",
  "4840774900",
  "5451229371",
  "6224332984",
  "7761782916",
  "9291937879",
  "9225295803",
  "7931207804",
  "2563100177",
  "5760733457",
  "8082208587",
  "9756015945",
  "9251360200",
  "5000076558",
  "9922699028",
  "3318775219",
  "8248508703",
  "6988401556",
  "9995621667",
  "9414951439",
  "3020140039",
  "5957966880",
  "3526497018",
  "4047599236",
  "7726998381",
  "7394240696",
  "1395142356",
  "4667071578",
  "8519146937",
  "3296257235",
  "5490182221",
  "5735387903",
  "9563139965 f",
  "9563139965 e",
  "9563139965 d",
  "5584033259",
  "5691615370",
  "3862621143 back",
  "3862621143 front",
  "3862621143 side",
  "8293089898",
  "2513405547",
  "6404645741",
  "1968758929",
  "6723997360",
  "3253650737",
  "8425800388",
  "4092227918",
  "4240815464 a reduced",
  "2608321088x",
  "1611600345x",
  "2327525027",
  "3508342905",
  "5429228381",
  "9893763499",
  "8384429938",
  "6078657299",
  "6944699408 a reduced",
  "7043724150 a reduced v2",
  "6170936724",
  "8673686234 c",
  "8673686234 b",
  "8673686234 a",
  "3287695934",
  "2570626711",
  "4652969746 2",
  "4652969746 1",
  "JNTEFVP 1"]

-- 生成期条数钉死（内核 `rfl` 可判）。
set_option maxRecDepth 2048 in
theorem lpIneqsIds_length : lpIneqsIds.length = 127 := rfl

/-- HOL `pack_ineq_def_a`（YSSKQOY.hl:30-31）分量清单。 对应 Assembly.lean 占位 `idsPackIneqDefA`（:179）。 -/
def packIneqDefAIds : List String :=
  ["6096597438 b",
  "6096597438 a",
  "8055810915",
  "1965189142 a",
  "1965189142 34"]

-- 生成期条数钉死（内核 `rfl` 可判）。
set_option maxRecDepth 2048 in
theorem packIneqDefAIds_length : packIneqDefAIds.length = 5 := rfl

/-- HOL `kcblrqc_ineq_def`（tame_lemmas-compiled.hl:45-46）分量清单。 对应 Assembly.lean 占位 `idsKcblrqcIneqDef`（:181）。 -/
def kcblrqcIneqDefIds : List String :=
  ["6184614449",
  "6988401556",
  "4667071578",
  "8519146937",
  "3296257235",
  "5490182221",
  "5735387903",
  "3862621143 side",
  "8293089898",
  "2513405547",
  "6404645741",
  "1968758929",
  "6723997360",
  "3253650737",
  "8425800388",
  "2608321088x",
  "1611600345x",
  "2327525027",
  "3508342905",
  "5429228381",
  "9893763499",
  "8384429938",
  "6078657299",
  "3287695934",
  "2570626711",
  "4652969746 2",
  "4652969746 1",
  "JNTEFVP 1"]

-- 生成期条数钉死（内核 `rfl` 可判）。
set_option maxRecDepth 2048 in
theorem kcblrqcIneqDefIds_length : kcblrqcIneqDefIds.length = 28 := rfl

/-! ## 接线示范（P6-E 接口侧；**不改 Assembly.lean 本体**）

`TheNonlinearInequalities`（Assembly.lean:190-193）填入六清单后的展开形态。
按 IneqPilot.lean 先例，本数据文件不 import `Kepler.Assembly`
（避免为纯数据拉起整条装配链构建）；下面两个定义是 Assembly.lean:165-168
`CertifiedIneqHolds` / `AllCertified` 的逐字镜像，仅用于展示展开形态。
接线时（G4 粘合量产）把六个清单常量代入 Assembly.lean:171-183 的对应
PLACEHOLDER 字段，并将 `CertifiedIneqHolds` 填实为按 id 查表展开
（量产样板 = IneqPilot.lean `certifiedIneqHolds_pilot`）。 -/

/-- Assembly.lean:165 占位语义的本地镜像（填实后按 id 查表展开为字面量化
不等式命题，由 G4 内核证书闭合）。 -/
def CertifiedIneqHoldsMirror (_id : String) : Prop := True

/-- Assembly.lean:168 注册表量化的本地镜像。 -/
def AllCertifiedMirror (ids : List String) : Prop :=
  ∀ id ∈ ids, CertifiedIneqHoldsMirror id

/-- **填入后展开形态**：`TheNonlinearInequalities` = 六分量 `AllCertified` 合取
（Assembly.lean:190-193；`LpIneqs` = 第四分量，Assembly.lean:186）。 -/
def TheNonlinearInequalitiesFilled : Prop :=
  AllCertifiedMirror packNonlinearNonOx3q1hIds ∧ AllCertifiedMirror ox3q1hIds ∧
    AllCertifiedMirror mainNonlinearTerminalV11Ids ∧ AllCertifiedMirror lpIneqsIds ∧
    AllCertifiedMirror packIneqDefAIds ∧ AllCertifiedMirror kcblrqcIneqDefIds

/-- 清单上的量化逐点展开（注册表量化的定义等价值）。 -/
example : AllCertifiedMirror lpIneqsIds ↔
    ∀ id ∈ lpIneqsIds, CertifiedIneqHoldsMirror id := Iff.rfl

/-- 占位语义下填入形态可闭合（`True` 占位逐点平凡）；`CertifiedIneqHolds`
填实后此定理由 G4 证书逐条替换。 -/
theorem theNonlinearInequalitiesFilled_placeholder :
    TheNonlinearInequalitiesFilled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro _ _ <;> exact True.intro

/-- **清单 = 查表定义域** 不变量（IneqPilot.lean:72-76 警告的 else-True 静默
退化防线）：查表定义域 = 六清单并集；`CertifiedIneqHolds` 填实时其查表分支
必须覆盖此定义域的每个键（分量间有重叠——lp_ineqs 与 main/kcblrqc 共享若干
id——查表按键覆盖即可，重复键无语义影响；无 import 的纯数据文件不提供
`List.eraseDup`，去重留给接线方）。 -/
def certLookupDomain : List String :=
  packNonlinearNonOx3q1hIds ++ ox3q1hIds ++ mainNonlinearTerminalV11Ids ++ lpIneqsIds ++ packIneqDefAIds ++ kcblrqcIneqDefIds

-- 生成期特例钉子（位置式成员证明，内核可判、零新增公理——String 的 BEq
-- 内核归约不走 `decide`，故成员证明按位置构造）：`"6170936724"` 特例进
-- lp_ineqs；ox3q1h 首支 / kcblrqc 末支在列。
-- 负向钉子（deprecated_quads 六条不进 lp_ineqs / kcblrqc_ineq_def、ox3q1h
-- 230 条与 pack_nonlinear_non_ox3q1h 的前缀不交性）由生成期 assert 钉死
-- （gen_idlists.py `validate`），不写成 Lean example。
example : "6170936724" ∈ lpIneqsIds := by
  unfold lpIneqsIds
  repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
example : "OXLZLEZ 6346351218 0 0" ∈ ox3q1hIds := by
  unfold ox3q1hIds
  repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
example : "JNTEFVP 1" ∈ kcblrqcIneqDefIds := by
  unfold kcblrqcIneqDefIds
  repeat (first | exact List.Mem.head _ | apply List.Mem.tail)

end Kepler.Assembly
