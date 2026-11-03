/-
`Kepler.Text.HypermapConcl` — hypermap 章结论出口层（章根 capstone）。

HOL `more_tame_concl.hl`（tame 章结论层）对 `hypermap.hl` 定理层的章外分名
恰好五条（:276 / :286 / :423 / :425 / :428）；本文件把这条别名层以 Lean 正名
verbatim 落地：每条陈述逐字取 `Kepler/Text/Hypermap.lean` 原定理签名（含
implicit/instance 绑定与绑定名），体 = 原常数按绑定名应用。零新数学、零
未证占位、零陈述重铸（HOL 别名层本身零内容，Lean 直译）。

本文件是 `lean/scripts/global_reach_map.lean` 与 `lean/scripts/orphan_histogram.lean`
manual capstone 根清单的注册对象（hypermap 章根；lane `hypermap-root-w1`，
工单 = `hypermap-mat-scout` §3 候选 1 + §5 落库工单）。
-/
import Kepler.Text.Hypermap

namespace Kepler.Text

/-- HOL `more_tame_concl.hl:276  let QRDYXYJ = Hypermap.lemmaParameters;;`。
正本：`Kepler.Text.Hypermap.parameters`（Hypermap.lean:10858；
HOL `hypermap.hl`:12217 `lemmaParameters`）。 -/
theorem QRDYXYJ {α : Type*} [DecidableEq α] (H : Hypermap α) {NF : Set (Loop α)}
    {hnf : H.IsNormalFamily NF} {L : Loop α} {x : α}
    (hmark : H.IsMarked NF hnf L x) (hLnot : L ∉ H.finalLoops NF) :
    H.hypM NF L x < H.hypQ hmark hLnot ∧
      H.hypQ hmark hLnot < (H.atomsOfLoop L).ncard ∧
      H.hypM NF L x + 1 < H.hypP NF L x + H.hypQ hmark hLnot ∧
      H.node (H.hypY NF L x) ≠ H.node x ∧
      H.node (H.hypY NF L x) ≠ H.node (H.hypZ NF L x) :=
  H.parameters hmark hLnot

/-- HOL `more_tame_concl.hl:286  let AQIUNPP1 = Hypermap.lemma_normal_family_transform;;`
（章主定理；HOL 下游 `reduction2.hl:1070 MATCH_MP_TAC Tame_list.AQIUNPP1`）。
正本：`Kepler.Text.Hypermap.normal_family_transform`（Hypermap.lean:12096；
HOL `hypermap.hl`:13152 `lemma_normal_family_transform`）。 -/
theorem AQIUNPP1 {α : Type*} [DecidableEq α] (H : Hypermap α) {NF : Set (Loop α)}
    {hnf : H.IsNormalFamily NF} {L : Loop α} {x : α}
    (hmark : H.IsMarked NF hnf L x) (hLnot : L ∉ H.finalLoops NF) :
    H.IsNormalFamily (H.familyTransform hmark hLnot) :=
  H.normal_family_transform hmark hLnot

/-- HOL `more_tame_concl.hl:423  let ZBHENEI_hypermap = Hypermap.lemma_finite_normal_loops;;`。
正本：`Kepler.Text.Hypermap.isNormalFamily_finite_and_card_le`（Hypermap.lean:6937；
HOL `hypermap.hl`:8342 `lemma_finite_normal_loops`）。 -/
theorem ZBHENEI_hypermap {α : Type*} [DecidableEq α] (H : Hypermap α)
    {NF : Set (Loop α)} (hnf : H.IsNormalFamily NF) :
    NF.Finite ∧ NF.ncard ≤ H.darts.card :=
  H.isNormalFamily_finite_and_card_le hnf

/-- HOL `more_tame_concl.hl:425  let XWCNBMA_hypermap = Hypermap.face_quotient_lemma;;`。
正本：`Kepler.Text.Hypermap.iso_quotientHypermap_faceCollection`（Hypermap.lean:8604；
HOL `hypermap.hl`:10278 `face_quotient_lemma`）。 -/
theorem XWCNBMA_hypermap {α : Type*} [DecidableEq α] (H : Hypermap α)
    (hne : H.EdgeNondegenerate)
    (h2 : ∀ x ∈ H.darts, ∃ y ∈ H.darts, y ∈ H.face x ∧ H.node x ≠ H.node y) :
    (∀ x : α, H.atomChoice (H.faceCollection) x = {x}) ∧
    H.Iso (H.quotientHypermap (H.isNormalFamily_faceCollection h2)) :=
  H.iso_quotientHypermap_faceCollection hne h2

/-- HOL `more_tame_concl.hl:428  let STKBEPH_hypermap = Hypermap.lemmaSTKBEPH;;`。
正本：`Kepler.Text.Hypermap.faceCollection_eq_and_iso_of_card_le`（Hypermap.lean:8808；
HOL `hypermap.hl`:10498 `lemmaSTKBEPH`）。 -/
theorem STKBEPH_hypermap {α : Type*} [DecidableEq α] (H : Hypermap α)
    {NF : Set (Loop α)} (hnf : H.IsNormalFamily NF)
    (hcard : H.numberOfFaces ≤ (H.finalQuotientFaces hnf).ncard) :
    NF = H.faceCollection ∧ H.Iso (H.quotientHypermap hnf) :=
  H.faceCollection_eq_and_iso_of_card_le hnf hcard

end Kepler.Text
