import pathlib

def fix(path, name):
    lines = pathlib.Path(path).read_text().splitlines(keepends=True)
    i_rw = next(i for i, l in enumerate(lines) if "getElem" in l and "rw" in l)
    i_end = next(i for i, l in enumerate(lines) if "absurd hiN" in l)
    body = ["  interval_cases i\n"]
    for i in range(100):
        body.append(f"  · exact {name(i)}\n")
    new = lines[:i_rw + 1] + body + lines[i_end + 1:]
    pathlib.Path(path).write_text("".join(new))
    print(f"fixed {path}")

fix("lean/Kepler/Graphs/CertShards/PentR4/Root.lean", lambda i: f"pentr4_shardE_{i}")
fix("lean/probes/TestRoot.lean", lambda i: f"pentr4_shardE_test {i}")
