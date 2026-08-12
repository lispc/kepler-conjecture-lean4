#!/usr/bin/env python3
"""Generate per-seed shard files + wiring file for the enumeration certificates.

Reads the top certificate data (must already be generated into
lean/Kepler/Graphs/CertData/<Name>Top.lean by certgen.py) and writes:

  lean/Kepler/Graphs/CertShards/<Name>/kNNN.lean   -- G shards per file
  lean/Kepler/Graphs/Cert<Name>.lean               -- wiring (same_p assembly)

Usage: shardgen.py <p> <Name> <group_size> <fuel>
"""
import math
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean" / "Kepler" / "Graphs"

# position of <Name>Data in TriData ++ QuadData ++ PentData ++ HexData
MEMPATH = {
    "Tri": "List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha))",
    "Quad": "List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha))",
    "Pent": "List.mem_append_left _ (List.mem_append_right _ ha)",
    "Hex": "List.mem_append_right _ ha",
}


def frontier_length(name):
    txt = (LEAN / "CertData" / f"{name}Top.lean").read_text()
    m = re.search(r"\|frontier\| = (\d+)", txt)
    return int(m.group(1))


def shard_theorem(p, name, fuel, start, count, prefix=None):
    prefix = prefix or name.lower()
    return f"""/-- Shards [{start}, {start + count}): worklist closure from each
frontier root certifies `checkFinal` (`loop_some_true`). -/
theorem {prefix}_shard_{start} : (List.range' {start} {count}).all (fun j =>
    decide (loop (next_tame {p}) (checkFinal (buildBuckets {name}Data)) {fuel}
      [{name}Frontier[j]!] = some true)) = true := by
  native_decide
"""


def shard_file(p, name, fuel, start, count, prefix=None):
    return f"""/- Shard group [{start}, {start + count}) for seed {name} (p = {p}).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.{name}Top
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

{shard_theorem(p, name, fuel, start, count, prefix)}
/-- Fuel-existential form: the certificate is valid regardless of the fuel
each shard file happened to use. -/
theorem {prefix}_shardE_{start} : ∀ j ∈ List.range' {start} {count},
    ∃ fuel, loop (next_tame {p}) (checkFinal (buildBuckets {name}Data)) fuel
      [{name}Frontier[j]!] = some true := fun j hj =>
  ⟨{fuel}, of_decide_eq_true ((List.all_eq_true.mp {prefix}_shard_{start}) j hj)⟩

end Kepler.Graphs
"""


def dispatch(name, fuel, gsize, nfiles, length, prefix=None):
    prefix = prefix or name.lower()
    """Nested dite-chain selecting the shard-group theorem for index j."""
    lines = []
    for k in range(nfiles):
        start = k * gsize
        cnt = min(gsize, length - start)
        kw = "if" if k == 0 else "else if"
        lines.append(f"      {kw} h{k} : j < {start + cnt} then")
        lo = "Nat.zero_le j" if k == 0 else f"le_of_not_gt h{k - 1}"
        lines.append(f"        {prefix}_shardE_{start} j")
        lines.append(f"          (List.mem_range'_1.mpr ⟨{lo}, h{k}⟩)")
    lines.append("      else")
    lines.append(f"        absurd hj h{nfiles - 1}")
    return "\n".join(lines)


def wiring_file(p, name, fuel, gsize, length, suffix=""):
    prefix = (name.lower() + suffix.lower())
    nfiles = math.ceil(length / gsize)
    imports = "\n".join(
        f"import Kepler.Graphs.CertShards.{name}{suffix}.K{k:03d}" for k in range(nfiles))
    mem = MEMPATH[name]
    lower = name.lower()
    return f"""/-
{name} seed (p = {p}) enumeration certificate wiring.{suffix and " (GENERATOR SMOKE TEST)" or ""}
Evaluation-side file: `native_decide` allowed (DECISIONS.md 2026-08-10);
every assembly proof is a pure kernel proof.  Mirrors CertTri.lean.
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.{name}Top
import Kepler.Graphs.Worklist
{imports}

set_option maxRecDepth 100000

namespace Kepler.Graphs

/-- Replay: every top node's `next_tame {p}` children are exactly its tagged
children table entries. -/
theorem {lower}_top_replay : (List.range {name}Top.length).all (fun i =>
    decide (next_tame {p} {name}Top[i]! =
      ({name}TopChildren[i]!).map (resolveChild {name}Top {name}Frontier))) = true := by
  native_decide

/-- Bounds: every tagged child index is in range of its target list. -/
theorem {lower}_top_bounds : (List.range {name}TopChildren.length).all (fun i =>
    ({name}TopChildren[i]!).all (fun t =>
      (t.1 && decide (t.2 < {name}Frontier.length)) ||
        (!t.1 && decide (t.2 < {name}Top.length)))) = true := by
  native_decide

/-- `{name}Top` is closed under `next_tame {p}` up to `{name}Frontier`. -/
theorem {lower}_top_closed : ∀ x ∈ {name}Top, ∀ c ∈ next_tame {p} x,
    c ∈ {name}Top ∨ c ∈ {name}Frontier :=
  closed_of_replay rfl {lower}_top_replay {lower}_top_bounds

/-- No final graphs in the {name} top. -/
theorem {lower}_top_no_finals : ({name}Top.all (fun g => !g.final)) = true := by
  native_decide

theorem {lower}_top_final_archive :
    ∀ g ∈ {name}Top, g.final = true → inIso g.fgraph Archive :=
  top_final_archive_of_no_finals {lower}_top_no_finals

/-- Every `{name}Data` entry satisfies `pre_iso_test`. -/
theorem {lower}_archive_pre : ({name}Data.all (fun a => preIsoTestB a)) = true := by
  native_decide

theorem {lower}_archive_pre_iso : ∀ a ∈ {name}Data, pre_iso_test a := fun a ha =>
  preIsoTestB_correct ((List.all_eq_true.mp {lower}_archive_pre) a ha)

/-- The seed-{p} (`{name}`) case of the enumeration-completeness certificate. -/
theorem same_{p}{suffix} : ∀ g, TameEnumP {p} g → inIso g.fgraph Archive := by
  intro g htep
  obtain ⟨hr, hfin⟩ := htep
  have h0 : {name}Top[0]'(by decide) = Seed {p} := by decide
  have hseed : Seed {p} ∈ {name}Top := h0 ▸ List.getElem_mem _
  rcases frontier_cut {name}Top {name}Frontier hseed {lower}_top_closed hr
    with hS | ⟨h, hF, hrh⟩
  · exact {lower}_top_final_archive g hS hfin
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hF
    have hlenN : {name}Frontier.length = {length} := rfl
    rw [hlenN] at hj
    have hloopE : ∃ fuel, loop (next_tame {p}) (checkFinal (buildBuckets {name}Data))
        fuel [{name}Frontier[j]!] = some true :=
{dispatch(name, fuel, gsize, nfiles, length, prefix)}
    obtain ⟨fuel, hloop⟩ := hloopE
    rw [getElem!_pos {name}Frontier j hj] at hloop
    have hcheck := loop_some_true hloop g
      ⟨{name}Frontier[j]'hj, List.mem_singleton_self _, hrh⟩
    obtain ⟨a, ha, hiso⟩ := checkFinal_correct {lower}_archive_pre_iso hcheck hfin
    refine ⟨a, ?_, hiso⟩
    show a ∈ TriData ++ QuadData ++ PentData ++ HexData
    exact {mem}

end Kepler.Graphs
"""


def main():
    p = int(sys.argv[1])
    name = sys.argv[2]
    gsize = int(sys.argv[3])
    fuel = int(sys.argv[4])
    length = frontier_length(name)
    nfiles = math.ceil(length / gsize)
    suffix = sys.argv[5] if len(sys.argv) > 5 else ""
    shard_dir = LEAN / "CertShards" / (name + suffix)
    shard_dir.mkdir(parents=True, exist_ok=True)
    for k in range(nfiles):
        start = k * gsize
        cnt = min(gsize, length - start)
        (shard_dir / f"K{k:03d}.lean").write_text(
            shard_file(p, name, fuel, start, cnt, (name.lower() + suffix.lower())))
    (LEAN / f"Cert{name}{suffix}.lean").write_text(
        wiring_file(p, name, fuel, gsize, length, suffix))
    print(f"{name}: frontier={length}, {nfiles} shard files "
          f"(group {gsize}), fuel {fuel}")


if __name__ == "__main__":
    main()
