/-
  Kepler/Graphs/ArchivePreTri — `archivePre` / Tri 全类闭合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  单片：全类 9 项一次 `decide +kernel`（纯内核，无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.ArchiveData.Tri
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Tri `archivePre` 全类闭合：9 项，单片。 -/
theorem archivePreTriAll : (TriData).all (fun a => preIsoTestB a) = true := by
  decide +kernel

#print axioms archivePreTriAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
