# EVIDENCE.md — `hf-proof-map` 的 grep 台账

> 配套 `PROOF-MAP.md`。只读、零编译。每条给：命令 → 命中（截断到关键行）。
> 工作目录若未注明，`HOL` = `reference/flyspeck`，`LEAN` = `lean`。
> 行号口径见 `PROOF-MAP.md` 顶部（`Assembly.lean` 用工作树行号，含未提交的 `lp-registry` 改动）。

---

## A. 工作树状态（先确认，否则行号对不上）

```sh
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
git log -1 --format='%h %ci %s'
# 26b4f702 2026-11-06 19:36:41 +0800 docs 基线 S 写档（K_AXIOM 587 / 根面 591 / SORRIED 78 且这 −1 是去重）
git status --porcelain | head -5
#  M lean/Kepler/Assembly.lean
# ?? lean/Kepler/Assembly/LpIneqProps.lean
git diff --stat lean/Kepler/Assembly.lean
#  lean/Kepler/Assembly.lean | 91 +++++++++++++++++++++++++++++++----------------
#  1 file changed, 61 insertions(+), 30 deletions(-)
wc -l lean/Kepler/Assembly.lean
# 7341 Kepler/Assembly.lean      （HEAD 版是 7310）
```

`git diff` 的实质内容（决定 §7 的写法）：

```
+  2026-11-06 lp-registry 车道：LP 分量真化——`idsLpIneqs := lpIneqsIds`
+  （127 条），`CertifiedIneqHolds := lpIneqProp`（`LpIneqProps.lean`
+  机械转写的 127 条字面命题）；`LpIneqs` 从空量化恒真变为 127 条真债。
...
-/-- ... 表外键回落 `True` ... -/
-def CertifiedIneqHolds (_id : String) : Prop := certifiedIneqHolds_pilot _id
+/-- ... LP 清单内 id 查表命中即得该命题（真实但未证 = 127 条债务）... -/
+def CertifiedIneqHolds (id : String) : Prop := lpIneqProp id
```

`Kepler/Assembly/LpIneqProps.lean` 文件头（1714 行，生成件）：

```
**本文件由 /tmp/lp-registry/scripts/emit_lean.py 生成，请勿手改。**
  - id 清单 = the_main_statement.hl:29-45 的 `lp_ineqs` 过滤 ... 127 条，
    `lpIneqsIds_length = 127` 是 rfl 钉子；
  - 命题正文 = nonlinear/ineq.hl 与 nonlinear/main_estimate_ineq.hl 的 `ineq` 字面项；
...
  注意：127 条命题本身是本轮**未证债务**（`nliLpIneqs` 仍是 sorry）；
  本文件只把它们从"空量化恒真"换成"真实但未证"。
```

关键定义（工作树）：

```
1632:def lpIneqProp (id : String) : Prop :=
1633-  if id ∈ lpIneqIds then (lpIneqLookup id).getD False
1634-  else if id = "3397113841" then ineqProp_3397113841
1635-  else if id ∈ certLookupDomain then True
1636-  else False
```

---

## B. §4 的 `pt` / `decomposition_star`（MISSING/UNRESOLVED 的证据）

```sh
cd HOL && grep -rn --include='*.hl' "decomposition_star\|decomposition star" .
#   （零输出）
cd LEAN && grep -rn --include='*.lean' -i "decomposition" Kepler/
# Kepler/Geom/SolidAngle.lean:512:/-- ## `MEASURE_LUNE_DECOMPOSITION`（flyspeck.ml:5833） -/
# Kepler/Text/PackingAuto6.lean:876: ... union decomposition ...
# Kepler/Text/LocalAuto35.lean:5678:/-- (pm13) **The explicit projection decomposition** ...
# Kepler/LP/ColMajor.lean:828: ... the two-decide decomposition ...
cd HOL && grep -rn --include='*.hl' "FULLY_SURROUNDED_NODE_DECOMPOSITION\|decomposition_planar_by_angle_fan" text_formalization/ | head
# text_formalization/tame/CDTETAT.hl:198
# text_formalization/tame/tame_general.hl:514
# text_formalization/local/WJSCPRO.hl:699  （+ 800/1603/1727/1878/2021 …）
```

```sh
cd HOL && grep -rn --include='*.hl' 'atn (sqrt' . | head
# text_formalization/local/OCBICBY.hl:3236: atn (sqrt (#0.110186)) < #0.3205
# text_formalization/general/sphere.hl:730: atn (sqrt x) / (sqrt x)
# text_formalization/local/lp_details.hl:1304/1368/1376/1384/... （全是数值证书）
cd HOL && grep -rn --include='*.hl' '&4 \* atn\|4\*atn' .
# text_formalization/jordan/float.hl:926:  `pi = &4 * atn (&1)`
# formal_ineqs/taylor/theory/multivariate_taylor-compiled.hl:2599  (&3/&4 * atn ...)
cd LEAN && grep -rn --include='*.lean' '4 \* atn\|4\*atn\|arctan (Real.sqrt\|0\.0553' Kepler/
#   （零输出）
cd LEAN && grep -rn --include='*.lean' '\bpt\b' Kepler/ | grep -v pts | head
# Kepler/Interval/MonoCorner.lean:712:  set pt : ℕ → (Fin n → ℝ) :=   ← 局部变量，非常数
# Kepler/Interval/CertTM.lean:5534: obtain ⟨pt, _hpt, hfinal⟩ := h
```

**结论**：`pt` 从未作为常数出现；`8pt` 零命中；`decomposition_star` 两类树都没有。

---

## C. §4 的 σ 上界（真实对应物是 `sum_tauVEF_upper_bound`）

```sh
cd HOL && grep -n "let sum_tauVEF_upper_bound" -A 4 text_formalization/tame/ssreflect/tame_lemmas-compiled.hl
# 529:let sum_tauVEF_upper_bound = Sections.section_proof []
# 530-`&12 <= scriptL V ==>
# 531-	 sum (face_set (hypermap_of_fan (V,E))) (\f. tauVEF (V,E,f))
# 532-		<= &4 * pi - &20 * sol0`
cd LEAN && grep -n "^theorem sum_tauVEF_upper_bound" -A 5 Kepler/Text/TameLp.lean
# 1467:theorem sum_tauVEF_upper_bound (V : Set V3) (E : Set (Set V3))
# 1468-    (hfan : FAN 0 V E) (hsurr : FullySurrounded V E)
# 1469-    (hscript : 12 ≤ scriptL V) :
# 1470-    setSum (hypermapOfFanTl V E hfan).faceSet (fun f => tauVEF_p2 V E f)
# 1471-      ≤ 4 * Real.pi - 20 * sol0 := by
cd LEAN && sed -n '4,8p' Kepler/Text/TameLp.lean
#   填实状态：JGTDEBU 全组 + CDTETAT/SZIPOAS + KCBLRQC/BDJYFFB1/BDJYFFB2
#   已真证明；sum_tauVEF_upper_bound 已于 2026-10-23 真证明（§3b kit：…
```

数值核对（我只做算术，不重算指标）：

```
sol0 = 3*acs(1/3) - pi = 3*1.2309594 - 3.14159265 = 0.5512856
4*pi - 20*sol0        = 12.5663706 - 11.025712 = 1.540659
8*(4*atan(sqrt2/5) - pi/3) = 8*(4*0.275643 - 1.047198) = 8*0.055374 = 0.442992
⇒ 两者不等（差 3.5 倍）。tgt = 1.541 = squanderTarget/10000 = 15410/10000。
```

```sh
cd HOL && grep -n "squanderTarget\|tgt =" text_formalization/tame/import_tame_classification.hl text_formalization/local/appendix.hl | head
# tame/import_tame_classification.hl:50:let squanderTarget = new_definition' `squanderTarget = 15410`;;
# local/appendix.hl:106:  let tgt = new_definition' `tgt = #1.541`;;
cd HOL && sed -n '105,112p' text_formalization/tame/OXAXUCS.hl
# let tgt_squanderTarget = prove_by_refinement(
#   `tgt = &squanderTarget / &10000`, ...
```

---

## D. §2/§3 链路（PROVED 的证据）

```sh
cd LEAN && grep -n "def fccCompatible" -A 2 Kepler/Text/PackingAuto2.lean
# 298:def fccCompatible (f : V3 → ℝ) (S : Set V3) : Prop :=
# 299-  ∀ v ∈ S, Real.sqrt 32 ≤ volume.real (voronoiOpen S v) + f v
cd LEAN && grep -n "^theorem FCC_COMPATABILITY_FUNC\|^theorem NEGLIGIBLE_FUNC\|^theorem UPFZBZM\|^theorem JGXZYGW_KY" Kepler/Text/PackingAuto19.lean
# 590 / 754 / 915 / 947
cd LEAN && grep -n "private theorem JGXZYGW_p19" Kepler/Text/PackingAuto19.lean
# 934
cd LEAN && grep -n "^theorem jgxzygw_p" Kepler/Text/PackingJGXZYGW.lean
# 610
cd LEAN && sed -n '1345,1352p' Kepler/Text/PackingConcl.lean
#   obtain ⟨G, hG0, hGf⟩ := UPFZBZM V hs hP (hcc V hP hs) hT hlm
#   exact hden (JGXZYGW_KY V hP hs ⟨G, hGf, hG0⟩)
```

HOL 侧：

```sh
cd HOL && grep -n "fcc_compatible=\|negligible_fun_p =\|negligible_fun_0 =\|kepler_conjecture =" text_formalization/packing/pack_defs.hl
# 18 / 20 / 22 / 24
cd HOL && grep -n "FCC_COMPATABILITY_FUNC_concl\|NEGLIGIBLE_FUNC_concl\|let UPFZBZM" text_formalization/packing/UPFZBZM.hl
# 58 / 66 / 227
cd HOL && grep -n "let JGXZYGW\|JGXZYGW_concl" text_formalization/packing/pack1.hl
# 519
```

---

## E. §5 的 contravening → tame 链（SORRY 的两根）

```sh
cd LEAN && grep -n "^theorem contraveningFan\|^theorem mqmsmabWired\|^theorem mqmsmab\b\|^theorem tamePlanarHypermapRestricted\|^theorem jcajydu\|^theorem tameCorrespondenceIso\|^theorem hypermapOfFanNeg\|^theorem contraveningNegative\|^theorem elllnyz\|^theorem fcdjdot" Kepler/Assembly.lean
# 2320 / 2446 / 2469 / 2484 / 2509 / 2521 / 4090 / 4223 / 3025 / 6746
cd LEAN && sed -n '2509,2515p' Kepler/Assembly.lean
# theorem jcajydu … := by
#   sorry
cd LEAN && grep -n "theorem fully_surrounded_perimeter_bound" -A 9 Kepler/Text/TameLp.lean
# 925 … 933:  sorry
cd LEAN && grep -n "sorry" Kepler/Text/TameLp.lean
# 7:（注释）  33:（注释）  311:（注释）  836/842/929:（注释）  933:  sorry
#   ⇒ 现存唯一真 sorry = :933
cd LEAN && sed -n '7185,7198p' Kepler/Assembly.lean
# 7185:  obtain ⟨W, hWp, hWsub, hWlai⟩ := PACKING_CHAPTER_MAIN_CONCLUSION_discharged hneg hpnn hox3
# 7189:  obtain ⟨V, hcV⟩ := fcdjdot hpacka ⟨W, hWp, hWsub, hW12⟩
# 7192:  have htpH : TamePlanarHypermap (hypermapOfFan 0 V (ESTD V) hfanV) :=
# 7197:  obtain ⟨g, hgPlane, hgg4, Hg, hHgIs, hIsoFanHg⟩ := jcajydu _ hresH
```

HOL 侧：

```sh
cd HOL && grep -n "let ESTD\|let ECTC\|let surrounded_node\|let scriptL\|let contravening\|let tauVEF\|let restricted_hypermap\|let hypermap_of_fan\|let face_set_of_fan" text_formalization/tame/tame_defs.hl
# 191 / 194 / 241 / 245 / 248 / 274 / 278 / 230 / 235
cd HOL && grep -n "FCDJDOT_concl\|HRXEFDM_concl\|JGTDEBU1_concl\|MQMSMAB_concl\|WTEMDTA" text_formalization/tame/tame_concl.hl
# 26 (WTEMDTA skipped) / 40 (FCDJDOT) / 43 (HRXEFDM) / 46 (JGTDEBU1) / 105 (MQMSMAB)
```

---

## F. §6 的枚举（AXIOM 的证据）

```sh
cd LEAN && grep -n "theorem tame_classification" -A 3 Kepler/Graphs/TameClassification.lean
# 23:theorem tame_classification {g : Graph} (hpg : PlaneGraphs g) (ht : tame g) :
# 24-    inIso g.fgraph Archive :=
# 25-  completeness same_0 same_1 same_2 same_3 hpg ht
cd LEAN && grep -n "^theorem completeness\|^def Archive" Kepler/Graphs/RelativeCompleteness.lean
# 110 (Archive) / 170 (completeness)
cd LEAN && grep -n "^theorem same_0\|^theorem same_1\|^theorem same_2\|^theorem same_3" Kepler/Graphs/Cert*.lean
# CertTri.lean:113 / CertQuad.lean:142 / CertPent.lean:248 / CertHex.lean:340
cd LEAN && grep -n "native_decide" Kepler/Graphs/CertTri.lean
# 90/94/98/102/106  (tri_shard_0..4)
cd LEAN && find Kepler/Graphs -name '*Shard*.lean' | wc -l
# 218
cd LEAN && grep -n "tameArchiveLists" Kepler/Assembly/GoodListDefs.lean
# 82:def tameArchiveLists : List (fgraph ℕ) := TriData ++ QuadData ++ PentData ++ HexData
```

HOL 侧（原版跳过 + Isabelle 的 `by eval`）：

```sh
cd HOL && sed -n '24,28p' text_formalization/tame/tame_concl.hl
#   (* WTEMDTA_concl skipped. Tame hypermap classification theorem. *)
cd HOL && grep -n "let tame = new_definition" text_formalization/tame/import_tame_classification.hl
# 116
ls reference/afp-flyspeck-tame/Computation/ArchComp.thy
# （35 行，8 条 by eval；见 docs/handoff-2026-11-06.md §0.1）
```

---

## G. §7 的六分量与 LP 层

```sh
cd LEAN && grep -n "^def CertifiedIneqHolds\|^def AllCertified\|^def idsLpIneqs\|^def LpIneqs\|^def PackIneqDefA\|^def KcblrqcIneqDef\|^def TheNonlinearInequalities" Kepler/Assembly.lean
# 286 / 289 / 294 / 299 / 305 / 309 / 317
cd LEAN && sed -n '286,300p' Kepler/Assembly.lean
# def CertifiedIneqHolds (id : String) : Prop := lpIneqProp id
# def AllCertified … := ∀ id ∈ ids, CertifiedIneqHolds id
# def idsLpIneqs : List String := lpIneqsIds
# def LpIneqs : Prop := AllCertified idsLpIneqs
cd LEAN && grep -n "^theorem nliOx3q1h\b\|^theorem nliMainNonlinearTerminalV11\b\|^theorem nliLpIneqs\b\|^theorem nliPackIneqDefA\b\|^theorem nliKcblrqcIneqDef\b" Kepler/Assembly.lean
# 1885 / 1907 / 1925 / 1958 / 1973   （全部 := sorry）
cd LEAN && grep -n "^def ox3q1hP25" Kepler/Text/PackingAuto25.lean
# 94
cd LEAN && grep -n "^def main_nonlinear_terminal_v11\|^def mainNonlinearTerminalV11Ids_t11" -A 2 Kepler/Text/LocalAuto1.lean
# 2139 / 1902；长度钉子 2015: theorem mainNonlinearTerminalV11Ids_t11_length : … = 109 := rfl
cd LEAN && grep -n "^def pack_nonlinear_non_ox3q1h" Kepler/Text/PackingAuto21.lean
# 968
cd LEAN && grep -n "^def packIneqDefAP22" Kepler/Text/PackingAuto22.lean
# 406
cd LEAN && grep -n "^def KcblrqcIneqDef" -A 3 Kepler/Text/TameLp.lean
# 516
cd LEAN && grep -n "^def lp_main_estimate\|^theorem lp_main_estimate_JEJTVGB" Kepler/Text/LocalAuto16.lean
# 519 / 522
cd LEAN && grep -n "^theorem nonlinear_imp_lp_main_estimate_p16_discharged" -A 3 Kepler/Text/LocalConcl.lean
# 5427
```

LP 内核：

```sh
cd LEAN && grep -n "^def checkDualCMTF\|^theorem checkDualCMTF_sound" Kepler/LP/ColMajor.lean
# 773 / 809
cd LEAN && grep -n "^def farkasCheck\|^theorem farkasCheck_sound" Kepler/Text/LP/LPFarkas.lean
# 67 / 198
cd LEAN && sed -n '1,20p' Kepler/LP/PilotCM204880136538/Assembly.lean
#   AUTO-GENERATED certificate (column-major mode) …
#   LP: max cᵀx s.t. A·x ≤ b, x ≥ 0 — 915 vars, 3882 rows.
cd LEAN && grep -n "def LpTerminalCertified" -A 6 Kepler/Text/LP/LPCert.lean
# 60 起
cd LEAN && sed -n '28,35p' Kepler/Text/LP/LPCert.lean
#   终端记录总数 43,078（root 19,237 + easy 4,403 + hard 19,438）… infeasible 189
cd LEAN && grep -n "^theorem lpTerminalBoundAll\|^theorem lpAllInfeas" Kepler/Text/LP/LPAll.lean
# 553 / 190
cd LEAN && sed -n '1,14p' Kepler/Text/LP/LPPilot.lean
#   §1 试点 A：114084514923_t0000 …（唯一真跑的 root 记录）
```

HOL 侧：

```sh
cd HOL && grep -n "Open_type\|type tag" text_formalization/nonlinear/types.hl | head
# 20 起：tag 构造子表；36: | Quad_cluster of float
cd HOL && sed -n '136,142p' text_formalization/nonlinear/types.hl
#   Quad_cluster is an ineq on a coupled pair of simplices. The float
#   is the margin value for "breaksapart".
cd HOL && grep -n "let lp_main_estimate\|let lp_main_estimate_JEJTVGB\|let nonlinear_imp_lp_main_estimate" text_formalization/local/JEJTVGB.hl
# 232 / 236 / 244
cd HOL && grep -n "let tame_result_lemma\|let linear_programming_results_th" text_formalization/tame/linear_programming_results.hl
# 24 / 40
cd HOL && grep -n "let the_nonlinear_inequalities" text_formalization/general/the_main_statement.hl
# 55
cd HOL && grep -n "ineq_ids\|check_lp_tags" text_formalization/general/the_main_statement.hl
# 29-45（lp_ineqs 的过滤定义，id "6170936724"）
```

Lean 侧确实没有 `tag`/`Ineq` 记录：

```sh
cd LEAN && grep -rn --include='*.lean' "Dim_red\|Set_rad2\|Delta126\|Delta135\|Quad_cluster\|QuadCluster" Kepler/
#   （零输出）
cd LEAN && grep -rn --include='*.lean' "structure Ineq\|inductive Ineq\|ineqDatum" Kepler/
#   （零输出）
```

---

## H. §1 / §8 / §9（取等与总装）

```sh
cd LEAN && grep -n "^theorem kcImpTheKc\|^private theorem cpnknxn\|^private theorem flyspeckDevolution\|^theorem assembly\|^theorem the_kepler_conjecture_from_interfaces\|^theorem goodListArchive\|^theorem linearProgrammingResults\b\|^theorem textCapstone\|^theorem nonlinearInequalities" Kepler/Assembly.lean
# 7021 / 6810 / 6875 / 7319 / 7327 / 7301 / 7119 / 7128 / 7110
cd LEAN && sed -n '7319,7325p' Kepler/Assembly.lean
# theorem assembly (hNL) (hLP) (hTC) : TheKeplerConjecture := by
#   refine hTC tameArchiveLists ⟨?_, ⟨goodListArchive, hLP⟩, hNL⟩
#   intro g hpg ht
#   exact Kepler.Graphs.tame_classification hpg ht
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4 && grep -rn -i "fcc\|hcp" lean/Kepler/ docs/ | head
#   （只命中 DAKEFCC 注释与哈希串；无 fcc/hcp 图）
cd LEAN && grep -rn "8 \* pt\|8\*pt\|quad_cluster" Kepler/ ; grep -rn "8pt" /Users/zhangzhuo/repos/kepler-conjecture-lean4/docs
#   （零输出）
```

HOL 侧总装：

```sh
cd HOL && grep -n "let kepler_conjecture_with_assumptions_and_archive" text_formalization/general/the_kepler_conjecture.hl
# 69
cd HOL && grep -n "let the_kepler_conjecture_def\|let tame_classification\|let reduction_to_local_annulus_inequality\|let kepler_conjecture_with_assumptions" text_formalization/general/the_main_statement.hl
# 19 / 63 / 111 / 170
cd HOL && grep -n "let PACKING_CHAPTER_MAIN_CONCLUSION\|let OXLZLEZ \|let CELL_CLUSTER_ESTIMATE_PROPS" text_formalization/packing/OXLZLEZ3.hl
# 9019 / 8988 / 8963
cd HOL && grep -n "let OXLZLEZ_concl\|let TSKAJXY_statement\|let UPFZBZM_concl\|let RDWKARC_concl" text_formalization/packing/pack_concl.hl
# 222 / 224 / 240 / 247
```

---

## I. 文档数字的出处（本文只引用，不重算）

```sh
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4 && sed -n '1,25p' docs/priority-queue.md
# 基线 S @2ef062e8（2026-11-06 19:27）：K_REACH 2,088,636 / SORRIED 78 / K_AXIOM 587
# / MODULES 4,657 / UNIVERSE 2,100,847 / COVERAGE 99.4183%
# 根面 #print axioms the_kepler_conjecture_e2e = 591 = 587 native + 标准三 + sorryAx
sed -n '8,34p' docs/handoff-2026-11-06.md        # §0 在 :8
# 78 的构成：57 Assembly + 21 Text；587 的构成：585 shard + 2 {hex,pent}_top_replay
sed -n '35,67p' docs/handoff-2026-11-06.md        # §0.1 在 :35
# §0.1：HOL tame_concl.hl:26 skipped；ALL good_list 零公理真证；Isabelle ArchComp.thy 8 条 by eval
sed -n '27,45p' docs/trust-base.md                # §2 在 :27
# §2 逐类对照表；"`else True` 回落 / 索引盲谓词 / 空量化注册表 … 我们更差 → 必须修"
```

---

## J. 复核提示

1. **想复核「某节是不是真的 PROVED」**：不要信本文，直接跑（编排者才允许）
   `cd lean && lake env lean Kepler/<File>.lean` 看 `#print axioms`；本文的证据一律是
   **源码静态事实**（声明存在/body 里有没有 `sorry`/结论的字面形状），不是编译结果。
2. **`Assembly.lean` 行号**：本文用工作树行号（含未提交改动）。若 `lp-registry` 落库，
   行号会再漂一次；按声明名 grep 最稳。
3. **`TameLp.lean` 的文件头已 stale**（仍写 7 处 sorry，实际 1 处）。复核时以
   `grep -n "sorry" Kepler/Text/TameLp.lean` 为准。
4. **`docs/main-theorem-trust-audit.md` 的行号也 stale**（写成 Assembly:6235/6243/6040，
   且停在 624 公理时代）。该文档的结论仍可用，行号别用。
